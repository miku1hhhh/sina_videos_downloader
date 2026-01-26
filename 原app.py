# app.py (修复GIF和视频播放的完整代码)
import os
import sys
import threading
import time
import json
from flask import Flask, render_template, request, jsonify, send_file, send_from_directory
import requests
import concurrent.futures
from tqdm import tqdm
import urllib3
from queue import Queue
import hashlib
import random
import datetime
import re
from enum import Enum
import configparser
import asyncio
import aiohttp
import cv2
import numpy as np
from PIL import Image
import io
import base64
import shutil

# 尝试导入moviepy用于生成GIF
try:
    from moviepy.editor import VideoFileClip
    MOVIEPY_AVAILABLE = True
except ImportError:
    MOVIEPY_AVAILABLE = False
    print("警告: 未安装 moviepy 库，将无法生成GIF预览")

# 禁用SSL警告
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# 使用 fake_useragent 替代手动维护的 User-Agent 列表
try:
    from fake_useragent import UserAgent
    FAKE_UA_AVAILABLE = True
except ImportError:
    FAKE_UA_AVAILABLE = False
    print("警告: 未安装 fake_useragent 库，将使用备用 User-Agent 列表")

# 视频类型枚举
class VideoType(Enum):
    NORMAL = "正常视频"
    DELETED = "已删除视频"
    REVIEW_FAILED = "审核未通过视频"
    OTHER = "分段视频"

# 运行模式枚举
class RunMode(Enum):
    THREADING = "多线程"
    ASYNC = "异步"

# 其他异常视频检测API枚举
class OtherCheckAPI(Enum):
    MAIN = "主API (基于错误消息匹配)"
    BACKUP = "备用API (基于getvideoidbyvid接口)"

class VideoInfo:
    """视频信息类，存储视频元数据和用户标记"""
    def __init__(self, vid, format, file_path, file_size):
        self.vid = vid
        self.format = format
        self.file_path = file_path
        self.file_size = file_size
        self.previews = {
            'thumbnail': None,
            'gif': None,
            'snapshots': []
        }
        self.tags = []
        self.rating = 0
        self.notes = ""
        self.added_time = datetime.datetime.now().isoformat()
        
    def to_dict(self):
        """转换为字典，用于JSON序列化"""
        return {
            "vid": self.vid,
            "format": self.format,
            "file_size": self.file_size,
            "previews": self.previews,
            "tags": self.tags,
            "rating": self.rating,
            "notes": self.notes,
            "added_time": self.added_time
        }

class SinaVideoDownloader:
    def __init__(self):
        self.base_api_url = "http://api.ivideo.sina.com.cn/public/video/play/url"
        self.base_flv_url = "http://cdn.sinacloud.net/edge.v.iask.com/"
        self.other_check_url = "https://s.video.sina.com.cn/video/getvideoidbyvid"
        self.valid_vids = []
        self.output_dir = "sina_videos"
        self.thumbnails_dir = "thumbnails"
        self.previews_dir = "previews"
        self.default_test_vid = 28545847
        self.supported_formats = ["flv", "hlv", "mp4"]
        self.selected_formats = ["flv", "hlv", "mp4"]  # 默认选择所有格式
        self.download_queue = Queue()
        self.connection_pool = {}
        self.max_download_threads = 0
        self.downloaded_bytes = 0
        self.start_time = 0
        self.download_errors = {}
        self.scan_errors = {}
        
        # 中断标志
        self.stop_scan = False
        self.stop_download = False
        
        # 配置文件路径
        self.config_file = "sina_downloader_config.ini"
        self.metadata_file = "video_metadata.json"
        
        # 运行模式设置 - 先设置默认值，然后从配置文件加载
        self.run_mode = RunMode.THREADING
        
        # 其他异常视频检测API选择 - 默认使用主API
        self.other_check_api = OtherCheckAPI.MAIN
        
        # 视频类型过滤策略 - 先设置默认值，然后从配置文件加载
        self.video_type_filter = {
            VideoType.NORMAL: True,
            VideoType.DELETED: False,
            VideoType.REVIEW_FAILED: False,
            VideoType.OTHER: False
        }
        
        # 预览设置
        self.preview_settings = {
            'gif_duration': 3,  # GIF时长（秒）
            'gif_fps': 5,       # GIF帧率
            'snapshot_count': 9, # 快照数量
            'preview_quality': 80, # 预览质量（0-100）
            'thumbnail_check_enabled': True, # 是否检查缩略图质量
            'min_thumbnail_quality': 30,      # 缩略图质量阈值
            'gif_max_size': 300,  # GIF最大尺寸
            'gif_use_opencv': True  # 使用OpenCV生成GIF作为备选方案
        }
        
        # 初始化 UserAgent
        if FAKE_UA_AVAILABLE:
            try:
                self.ua = UserAgent(fallback="Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36")
            except Exception as e:
                print(f"fake_useragent 初始化失败: {e}, 使用备用 User-Agent")
                self._init_fallback_ua()
        else:
            self._init_fallback_ua()
        
        self.retry_attempts = 3  # 固定重试次数
        
        # 创建输出目录
        if not os.path.exists(self.output_dir):
            os.makedirs(self.output_dir)
        
        # 创建缩略图目录
        if not os.path.exists(self.thumbnails_dir):
            os.makedirs(self.thumbnails_dir)
            
        # 创建预览目录
        if not os.path.exists(self.previews_dir):
            os.makedirs(self.previews_dir)
        
        # 加载配置文件和元数据
        self.load_config()
        self.load_video_metadata()
        
        # GUI状态
        self.current_task = None
        self.task_progress = 0
        self.task_status = "空闲"
        self.task_message = ""
        self.scan_results = []
        self.download_results = []
        self.video_thumbnails = []  # 存储VideoInfo对象
    
    def _init_fallback_ua(self):
        """初始化备用 User-Agent 列表"""
        self.user_agents = [
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36",
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:89.0) Gecko/20100101 Firefox/89.0",
            "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/14.1.1 Safari/605.1.15",
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/92.0.4515.107 Safari/537.36 Edg/92.0.902.62"
        ]
    
    def get_random_ua(self):
        """获取随机 User-Agent"""
        if FAKE_UA_AVAILABLE and hasattr(self, 'ua'):
            try:
                return self.ua.random
            except Exception as e:
                return random.choice(self.user_agents)
        else:
            return random.choice(self.user_agents)
    
    def load_config(self):
        """加载配置文件"""
        config = configparser.ConfigParser()
        
        if os.path.exists(self.config_file):
            try:
                config.read(self.config_file, encoding='utf-8')
                
                # 加载运行模式
                if config.has_option('SETTINGS', 'run_mode'):
                    mode_str = config.get('SETTINGS', 'run_mode')
                    if mode_str == 'ASYNC':
                        self.run_mode = RunMode.ASYNC
                    else:
                        self.run_mode = RunMode.THREADING
                
                # 加载其他异常视频检测API选择
                if config.has_option('SETTINGS', 'other_check_api'):
                    api_str = config.get('SETTINGS', 'other_check_api')
                    if api_str == 'BACKUP':
                        self.other_check_api = OtherCheckAPI.BACKUP
                    else:
                        self.other_check_api = OtherCheckAPI.MAIN
                
                # 加载视频类型过滤策略
                if config.has_section('VIDEO_TYPE_FILTER'):
                    for video_type in VideoType:
                        key = video_type.name
                        if config.has_option('VIDEO_TYPE_FILTER', key):
                            self.video_type_filter[video_type] = config.getboolean('VIDEO_TYPE_FILTER', key)
                
                # 加载选择的文件格式
                if config.has_option('SETTINGS', 'selected_formats'):
                    formats_str = config.get('SETTINGS', 'selected_formats')
                    self.selected_formats = formats_str.split(',')
                
                # 加载预览设置
                if config.has_section('PREVIEW_SETTINGS'):
                    if config.has_option('PREVIEW_SETTINGS', 'gif_duration'):
                        self.preview_settings['gif_duration'] = config.getint('PREVIEW_SETTINGS', 'gif_duration')
                    if config.has_option('PREVIEW_SETTINGS', 'gif_fps'):
                        self.preview_settings['gif_fps'] = config.getint('PREVIEW_SETTINGS', 'gif_fps')
                    if config.has_option('PREVIEW_SETTINGS', 'snapshot_count'):
                        self.preview_settings['snapshot_count'] = config.getint('PREVIEW_SETTINGS', 'snapshot_count')
                    if config.has_option('PREVIEW_SETTINGS', 'preview_quality'):
                        self.preview_settings['preview_quality'] = config.getint('PREVIEW_SETTINGS', 'preview_quality')
                    if config.has_option('PREVIEW_SETTINGS', 'thumbnail_check_enabled'):
                        self.preview_settings['thumbnail_check_enabled'] = config.getboolean('PREVIEW_SETTINGS', 'thumbnail_check_enabled')
                    if config.has_option('PREVIEW_SETTINGS', 'min_thumbnail_quality'):
                        self.preview_settings['min_thumbnail_quality'] = config.getint('PREVIEW_SETTINGS', 'min_thumbnail_quality')
                    if config.has_option('PREVIEW_SETTINGS', 'gif_max_size'):
                        self.preview_settings['gif_max_size'] = config.getint('PREVIEW_SETTINGS', 'gif_max_size')
                    if config.has_option('PREVIEW_SETTINGS', 'gif_use_opencv'):
                        self.preview_settings['gif_use_opencv'] = config.getboolean('PREVIEW_SETTINGS', 'gif_use_opencv')
                
            except Exception as e:
                print(f"加载配置文件失败: {e}, 使用默认设置")
    
    def save_config(self):
        """保存配置文件"""
        try:
            config = configparser.ConfigParser()
            
            # 设置区域
            config['SETTINGS'] = {
                'run_mode': self.run_mode.name,
                'output_dir': self.output_dir,
                'other_check_api': self.other_check_api.name,
                'selected_formats': ','.join(self.selected_formats)
            }
            
            # 视频类型过滤策略
            config['VIDEO_TYPE_FILTER'] = {}
            for video_type, enabled in self.video_type_filter.items():
                config['VIDEO_TYPE_FILTER'][video_type.name] = str(enabled)
            
            # 预览设置
            config['PREVIEW_SETTINGS'] = {}
            for key, value in self.preview_settings.items():
                config['PREVIEW_SETTINGS'][key] = str(value)
            
            # 写入文件
            with open(self.config_file, 'w', encoding='utf-8') as configfile:
                config.write(configfile)
            
            return True
            
        except Exception as e:
            print(f"保存配置文件失败: {e}")
            return False
    
    def load_video_metadata(self):
        """从文件加载视频元数据"""
        try:
            if os.path.exists(self.metadata_file):
                with open(self.metadata_file, "r", encoding="utf-8") as f:
                    metadata = json.load(f)
                    
                for video_data in metadata.get("videos", []):
                    # 检查视频文件是否存在
                    if os.path.exists(video_data.get("file_path", "")):
                        video_info = VideoInfo(
                            vid=video_data["vid"],
                            format=video_data["format"],
                            file_path=video_data["file_path"],
                            file_size=video_data["file_size"]
                        )
                        video_info.previews = video_data.get("previews", {})
                        video_info.tags = video_data.get("tags", [])
                        video_info.rating = video_data.get("rating", 0)
                        video_info.notes = video_data.get("notes", "")
                        video_info.added_time = video_data.get("added_time", "")
                        self.video_thumbnails.append(video_info)
                    else:
                        print(f"视频文件不存在，跳过加载: {video_data.get('file_path')}")
                        
        except Exception as e:
            print(f"加载视频元数据失败: {e}")
    
    def save_video_metadata(self):
        """保存视频元数据到文件"""
        try:
            metadata = {
                "videos": [video.to_dict() for video in self.video_thumbnails 
                          if isinstance(video, VideoInfo)]
            }
            
            with open(self.metadata_file, "w", encoding="utf-8") as f:
                json.dump(metadata, f, ensure_ascii=False, indent=2)
                
            return True
        except Exception as e:
            print(f"保存视频元数据失败: {e}")
            return False
    
    def set_run_mode(self, mode):
        """设置运行模式并保存配置"""
        if mode in [RunMode.THREADING, RunMode.ASYNC]:
            self.run_mode = mode
            self.save_config()
            return True
        return False

    def set_other_check_api(self, api):
        """设置其他异常视频检测API并保存配置"""
        if api in [OtherCheckAPI.MAIN, OtherCheckAPI.BACKUP]:
            self.other_check_api = api
            self.save_config()
            return True
        return False

    def set_video_type_filter(self, video_type, enabled):
        """设置视频类型过滤策略并保存配置"""
        if video_type in self.video_type_filter:
            self.video_type_filter[video_type] = enabled
            self.save_config()
            return True
        return False

    def set_selected_formats(self, formats):
        """设置选择的文件格式并保存配置"""
        if all(fmt in self.supported_formats for fmt in formats):
            self.selected_formats = formats
            self.save_config()
            return True
        return False

    def set_preview_settings(self, settings):
        """设置预览设置并保存配置"""
        for key, value in settings.items():
            if key in self.preview_settings:
                self.preview_settings[key] = value
        self.save_config()
        return True

    def stop_scanning(self):
        """停止扫描"""
        self.stop_scan = True
        self.task_status = "扫描已中断"
        self.task_message = "扫描任务已被用户中断"

    def stop_downloading(self):
        """停止下载"""
        self.stop_download = True
        self.task_status = "下载已中断"
        self.task_message = "下载任务已被用户中断"

    def clear_cache(self):
        """清除缓存（视频文件和缩略图）"""
        try:
            # 删除视频文件
            if os.path.exists(self.output_dir):
                shutil.rmtree(self.output_dir)
                os.makedirs(self.output_dir)
            
            # 删除缩略图和预览
            if os.path.exists(self.thumbnails_dir):
                shutil.rmtree(self.thumbnails_dir)
                os.makedirs(self.thumbnails_dir)
                
            if os.path.exists(self.previews_dir):
                shutil.rmtree(self.previews_dir)
                os.makedirs(self.previews_dir)
            
            # 重置相关状态
            self.video_thumbnails = []
            self.save_video_metadata()
            
            return True, "缓存清除成功"
        except Exception as e:
            return False, f"缓存清除失败: {str(e)}"

    # 同步检查VID方法
    def check_vid(self, vid):
        """同步检查VID有效性并分类视频类型"""
        # 检查是否应该停止
        if self.stop_scan:
            return False, VideoType.OTHER
        
        params = {
            "appname": "web",
            "appver": "web",
            "applt": "web",
            "tags": "popview",
            "direct": 0,
            "vid": vid
        }
        
        try:
            response = requests.get(
                self.base_api_url, 
                params=params, 
                timeout=5, 
                verify=False,
                headers={"User-Agent": self.get_random_ua()}
            )
            
            if response.status_code == 200:
                response_text = response.text.lower()
                video_type = self.classify_video(response_text, vid)
                
                if self.video_type_filter.get(video_type, False):
                    return True, video_type
                else:
                    return False, video_type
                    
            elif response.status_code == 400:
                try:
                    data = response.json()
                    if isinstance(data, dict):
                        error_message = (data.get("Message", "") + data.get("errorMessage", "")).lower()
                        video_type = self.classify_video(error_message, vid)
                        
                        if self.video_type_filter.get(video_type, False):
                            return True, video_type
                        else:
                            return False, video_type
                except:
                    return False, VideoType.OTHER
                    
        except Exception as e:
            return False, VideoType.OTHER
            
        return False, VideoType.OTHER

    def classify_video(self, response_text, vid):
        """根据响应文本分类视频类型"""
        response_text = response_text.lower()
        
        if "url" in response_text and "size" in response_text:
            return VideoType.NORMAL
        
        if "视频已删除" in response_text or "deleted" in response_text:
            return VideoType.DELETED
        
        if "视频审核不通过" in response_text or "failed to pass the review" in response_text:
            return VideoType.REVIEW_FAILED
        
        if "get video info exception" in response_text or "code==0 with getvideoidbyvid" in response_text:
            return VideoType.OTHER
        
        # 根据设置的API检查其他异常视频
        if self.other_check_api == OtherCheckAPI.BACKUP:
            if self.check_other_video_type(vid):
                return VideoType.OTHER
        else:
            # 使用主API的默认检测逻辑
            if "exception" in response_text or "error" in response_text:
                return VideoType.OTHER
        
        return VideoType.OTHER

    def check_other_video_type(self, vid):
        """使用备用API检查是否为其他异常视频"""
        try:
            params = {"vid": vid}
            response = requests.get(
                self.other_check_url,
                params=params,
                timeout=3,
                verify=False,
                headers={"User-Agent": self.get_random_ua()}
            )
            
            if response.status_code == 200:
                data = response.json()
                # 如果返回 {"code": 0, "message": "获取对应的video_id失败", "data": []}，则是其他异常视频
                if (data.get("code") == 0 and 
                    data.get("message") == "获取对应的video_id失败" and 
                    data.get("data") == []):
                    return True
            return False
        except:
            return False

    # 同步扫描方法
    def scan_vids(self, start_vid, end_vid, max_threads=50, progress_callback=None):
        """同步扫描指定范围内的有效VID"""
        self.task_status = "扫描中"
        self.task_message = f"开始扫描VID范围: {start_vid} 到 {end_vid}"
        self.scan_results = []
        self.stop_scan = False
        
        total = end_vid - start_vid + 1
        
        if total < 100:
            max_threads = min(10, max_threads)
        elif total < 1000:
            max_threads = min(30, max_threads)
        else:
            max_threads = min(100, max_threads)
        
        self.task_message = f"使用 {max_threads} 个线程进行扫描..."
        
        completed = 0
        
        with concurrent.futures.ThreadPoolExecutor(max_workers=max_threads) as executor:
            futures = {executor.submit(self.check_vid, vid): vid for vid in range(start_vid, end_vid+1)}
            
            for future in concurrent.futures.as_completed(futures):
                # 检查是否应该停止
                if self.stop_scan:
                    self.task_message = "正在停止扫描..."
                    # 取消所有未完成的任务
                    for f in futures:
                        f.cancel()
                    break
                
                vid = futures[future]
                completed += 1
                self.task_progress = int((completed / total) * 100)
                
                try:
                    result = future.result()
                    if result[0]:
                        self.valid_vids.append(vid)
                        self.scan_results.append({
                            "vid": vid,
                            "type": result[1].value,
                            "status": "有效"
                        })
                        self.task_message = f"发现有效VID: {vid} ({result[1].value})"
                except Exception as e:
                    self.scan_results.append({
                        "vid": vid,
                        "type": "未知",
                        "status": f"错误: {str(e)}"
                    })
                
                if progress_callback:
                    progress_callback(self.task_progress, self.task_message)
        
        if self.stop_scan:
            self.task_status = "扫描已中断"
            self.task_message = f"扫描已中断! 已完成 {completed}/{total}，找到 {len(self.valid_vids)} 个有效VID"
        else:
            self.task_status = "扫描完成"
            self.task_message = f"扫描完成! 找到 {len(self.valid_vids)} 个有效VID"
        
        if not self.valid_vids and not self.stop_scan:
            self.valid_vids.append(self.default_test_vid)
            self.task_message += f"，添加测试VID: {self.default_test_vid}"
            
        return self.valid_vids

    # 检测视频格式
    def detect_video_format(self, vid):
        """同步检测视频的实际格式"""
        headers = {
            "User-Agent": self.get_random_ua(),
            "Connection": "keep-alive"
        }
        
        # 只检测选择的格式
        for fmt in self.selected_formats:
            url = f"{self.base_flv_url}{vid}.{fmt}"
            try:
                response = requests.head(url, headers=headers, timeout=3, verify=False)
                if response.status_code == 200:
                    content_type = response.headers.get("Content-Type", "").lower()
                    if "video" in content_type or "octet-stream" in content_type:
                        return fmt
            except:
                continue
        
        for fmt in self.selected_formats:
            url = f"{self.base_flv_url}{vid}.{fmt}"
            try:
                response = requests.get(url, headers=headers, stream=True, timeout=5, verify=False)
                if response.status_code == 200:
                    content_length = int(response.headers.get('Content-Length', 0))
                    if content_length > 1024:
                        return fmt
            except:
                continue
        
        return None

    def analyze_frame_quality(self, frame):
        """分析帧质量，检测黑屏或单色屏"""
        try:
            # 转换为灰度图
            gray = cv2.cvtColor(frame, cv2.COLOR_BGR2GRAY)
            
            # 计算图像方差 - 方差小表示颜色单一（可能是黑屏或单色屏）
            variance = np.var(gray)
            
            # 计算平均亮度
            mean_brightness = np.mean(gray)
            
            # 检查是否为极端情况（全黑或全白）
            if variance < 100:  # 方差阈值
                if mean_brightness < 30:  # 全黑
                    return 0, "black_screen"
                elif mean_brightness > 220:  # 全白
                    return 0, "white_screen"
                else:
                    return 0, "solid_color"
            
            # 质量评分基于方差（0-100）
            quality_score = min(100, int(variance / 10))
            
            return quality_score, "normal"
            
        except Exception as e:
            print(f"分析帧质量失败: {str(e)}")
            return 0, "error"

    def extract_better_frame(self, video_path, max_attempts=10):
        """尝试从视频中提取质量更好的帧"""
        try:
            cap = cv2.VideoCapture(video_path)
            total_frames = int(cap.get(cv2.CAP_PROP_FRAME_COUNT))
            
            if total_frames <= 0:
                return None, 0, "no_frames"
            
            best_frame = None
            best_score = 0
            best_frame_info = "first_frame"
            
            # 检查多个帧
            check_points = [0]  # 第一帧
            if total_frames > 1:
                # 添加一些中间点
                check_points.extend([int(total_frames * 0.1), int(total_frames * 0.3), 
                                   int(total_frames * 0.5), int(total_frames * 0.7)])
            
            for frame_pos in check_points:
                if frame_pos >= total_frames:
                    continue
                    
                cap.set(cv2.CAP_PROP_POS_FRAMES, frame_pos)
                success, frame = cap.read()
                
                if success:
                    score, frame_type = self.analyze_frame_quality(frame)
                    
                    if score > best_score:
                        best_score = score
                        best_frame = frame.copy()
                        best_frame_info = f"frame_{frame_pos}_{frame_type}"
            
            cap.release()
            
            # 如果所有帧质量都很差，返回第一帧
            if best_frame is None:
                cap = cv2.VideoCapture(video_path)
                success, best_frame = cap.read()
                cap.release()
                if success:
                    best_score, best_frame_info = self.analyze_frame_quality(best_frame)
            
            return best_frame, best_score, best_frame_info
            
        except Exception as e:
            print(f"提取更好帧失败: {str(e)}")
            return None, 0, "error"

    # 截取视频第一帧（改进版本）
    def extract_first_frame(self, video_path, thumbnail_path):
        """截取视频质量最好的帧作为缩略图"""
        try:
            # 检查缩略图质量设置
            check_quality = self.preview_settings.get('thumbnail_check_enabled', True)
            min_quality = self.preview_settings.get('min_thumbnail_quality', 30)
            
            if check_quality:
                # 尝试提取质量更好的帧
                best_frame, quality_score, frame_info = self.extract_better_frame(video_path)
                
                if best_frame is not None:
                    # 调整缩略图大小
                    height, width = best_frame.shape[:2]
                    max_size = 300
                    if width > height:
                        new_width = max_size
                        new_height = int(height * max_size / width)
                    else:
                        new_height = max_size
                        new_width = int(width * max_size / height)
                    
                    frame_resized = cv2.resize(best_frame, (new_width, new_height))
                    
                    # 保存缩略图
                    cv2.imwrite(thumbnail_path, frame_resized)
                    
                    print(f"缩略图质量: {quality_score}, 来源: {frame_info}")
                    
                    # 如果质量太差，标记为低质量
                    if quality_score < min_quality:
                        return True, quality_score, frame_info
                    else:
                        return True, quality_score, "good_quality"
                else:
                    return False, 0, "no_frame_extracted"
            else:
                # 使用原始方法
                cap = cv2.VideoCapture(video_path)
                success, frame = cap.read()
                
                if success:
                    # 调整缩略图大小
                    height, width = frame.shape[:2]
                    max_size = 300
                    if width > height:
                        new_width = max_size
                        new_height = int(height * max_size / width)
                    else:
                        new_height = max_size
                        new_width = int(width * max_size / height)
                    
                    frame_resized = cv2.resize(frame, (new_width, new_height))
                    
                    # 保存缩略图
                    cv2.imwrite(thumbnail_path, frame_resized)
                    
                    cap.release()
                    return True, 50, "first_frame"  # 默认质量分数
                else:
                    cap.release()
                    return False, 0, "read_failed"
                    
        except Exception as e:
            print(f"截取视频帧失败: {str(e)}")
            return False, 0, f"error: {str(e)}"

    def generate_gif_with_opencv(self, video_path, gif_path, duration=3, fps=5, max_size=300):
        """使用OpenCV生成GIF（备选方案）"""
        try:
            cap = cv2.VideoCapture(video_path)
            video_fps = cap.get(cv2.CAP_PROP_FPS)
            total_frames = int(cap.get(cv2.CAP_PROP_FRAME_COUNT))
            
            if total_frames <= 0 or video_fps <= 0:
                return False
            
            # 计算需要提取的帧数
            frames_to_extract = min(int(duration * fps), total_frames)
            frame_interval = max(1, int(total_frames / frames_to_extract))
            
            frames = []
            frame_count = 0
            
            while frame_count < total_frames and len(frames) < frames_to_extract:
                success, frame = cap.read()
                if not success:
                    break
                
                # 每隔一定帧数提取一帧
                if frame_count % frame_interval == 0:
                    # 调整大小
                    height, width = frame.shape[:2]
                    if height > max_size or width > max_size:
                        if width > height:
                            new_width = max_size
                            new_height = int(height * max_size / width)
                        else:
                            new_height = max_size
                            new_width = int(width * max_size / height)
                        frame = cv2.resize(frame, (new_width, new_height))
                    
                    # 转换为RGB（OpenCV使用BGR）
                    frame_rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
                    frames.append(frame_rgb)
                
                frame_count += 1
            
            cap.release()
            
            if not frames:
                return False
            
            # 使用PIL创建GIF
            pil_images = []
            for frame in frames:
                pil_img = Image.fromarray(frame)
                pil_images.append(pil_img)
            
            # 保存GIF
            if len(pil_images) > 1:
                pil_images[0].save(
                    gif_path,
                    save_all=True,
                    append_images=pil_images[1:],
                    duration=int(1000 / fps),  # 每帧持续时间（毫秒）
                    loop=0  # 无限循环
                )
                return True
            else:
                return False
                
        except Exception as e:
            print(f"使用OpenCV生成GIF失败: {str(e)}")
            return False

    # 生成视频预览
    def generate_video_previews(self, video_path, vid):
        """生成多种预览：第一帧、GIF、多张快照"""
        previews = {}
        
        try:
            # 1. 第一帧缩略图（改进版本）
            thumbnail_path = os.path.join(self.thumbnails_dir, f"{vid}_thumb.jpg")
            success, quality_score, quality_info = self.extract_first_frame(video_path, thumbnail_path)
            if success:
                previews['thumbnail'] = thumbnail_path
                previews['thumbnail_quality'] = {
                    'score': quality_score,
                    'info': quality_info
                }
            
            # 2. 生成GIF预览
            gif_path = os.path.join(self.previews_dir, f"{vid}_preview.gif")
            gif_success = False
            
            # 首先尝试使用moviepy
            if MOVIEPY_AVAILABLE:
                try:
                    clip = VideoFileClip(video_path)
                    gif_duration = min(self.preview_settings['gif_duration'], clip.duration)
                    
                    # 取前几秒
                    subclip = clip.subclip(0, gif_duration)
                    
                    # 调整大小以减小文件
                    max_size = self.preview_settings.get('gif_max_size', 300)
                    subclip = subclip.resize(height=max_size)
                    
                    # 生成GIF - 使用imageio作为后端，更可靠
                    subclip.write_gif(
                        gif_path, 
                        fps=self.preview_settings['gif_fps'],
                        program='imageio'  # 使用imageio提高兼容性
                    )
                    
                    # 检查GIF文件是否有效
                    if os.path.exists(gif_path) and os.path.getsize(gif_path) > 100:
                        gif_success = True
                        previews['gif'] = gif_path
                    else:
                        print(f"moviepy生成的GIF文件无效: {gif_path}")
                    
                    clip.close()
                    
                except Exception as e:
                    print(f"使用moviepy生成GIF失败: {str(e)}")
            
            # 如果moviepy失败或不可用，尝试使用OpenCV
            if not gif_success and self.preview_settings.get('gif_use_opencv', True):
                try:
                    gif_success = self.generate_gif_with_opencv(
                        video_path, 
                        gif_path,
                        duration=self.preview_settings['gif_duration'],
                        fps=self.preview_settings['gif_fps'],
                        max_size=self.preview_settings.get('gif_max_size', 300)
                    )
                    
                    if gif_success:
                        previews['gif'] = gif_path
                        print(f"使用OpenCV成功生成GIF: {gif_path}")
                    else:
                        print(f"使用OpenCV生成GIF失败: {gif_path}")
                        
                except Exception as e:
                    print(f"使用OpenCV生成GIF异常: {str(e)}")
            
            # 3. 生成多张快照（九宫格概念）
            snapshots = []
            try:
                cap = cv2.VideoCapture(video_path)
                total_frames = int(cap.get(cv2.CAP_PROP_FRAME_COUNT))
                fps = cap.get(cv2.CAP_PROP_FPS)
                
                if total_frames > 0 and fps > 0:
                    duration = total_frames / fps
                    snapshot_count = min(self.preview_settings['snapshot_count'], int(duration))
                    
                    if snapshot_count > 0:
                        for i in range(snapshot_count):
                            # 在视频的不同时间点截取快照，避开开始和结束
                            time_point = (duration * 0.1) + (duration * 0.8 / (snapshot_count)) * i
                            cap.set(cv2.CAP_PROP_POS_MSEC, time_point * 1000)
                            success, frame = cap.read()
                            
                            if success:
                                snapshot_path = os.path.join(self.previews_dir, f"{vid}_snap_{i}.jpg")
                                
                                # 调整大小
                                height, width = frame.shape[:2]
                                max_size = 200
                                if width > height:
                                    new_width = max_size
                                    new_height = int(height * max_size / width)
                                else:
                                    new_height = max_size
                                    new_width = int(width * max_size / height)
                                
                                frame_resized = cv2.resize(frame, (new_width, new_height))
                                cv2.imwrite(snapshot_path, frame_resized, 
                                           [int(cv2.IMWRITE_JPEG_QUALITY), self.preview_settings['preview_quality']])
                                snapshots.append(snapshot_path)
                
                cap.release()
                previews['snapshots'] = snapshots
                
            except Exception as e:
                print(f"生成快照失败: {str(e)}")
            
            return previews
            
        except Exception as e:
            print(f"生成视频预览失败: {str(e)}")
            return None

    # 下载单个视频
    def download_video(self, vid):
        """同步下载单个视频文件"""
        # 检查是否应该停止
        if self.stop_download:
            return False, "下载已中断"
            
        video_format = self.detect_video_format(vid)
        if video_format is None:
            return False, f"无法确定视频 {vid} 的格式"
            
        url = f"{self.base_flv_url}{vid}.{video_format}"
        filename = os.path.join(self.output_dir, f"{vid}.{video_format}")
        
        for attempt in range(self.retry_attempts):
            try:
                # 再次检查是否应该停止
                if self.stop_download:
                    return False, "下载已中断"
                    
                if os.path.exists(filename):
                    if self.verify_file_integrity(filename):
                        # 如果文件存在且完整，检查是否有视频信息
                        existing_video = next((v for v in self.video_thumbnails 
                                             if isinstance(v, VideoInfo) and v.vid == vid), None)
                        if not existing_video:
                            # 创建视频信息并生成预览
                            file_size = os.path.getsize(filename)
                            video_info = VideoInfo(vid, video_format, filename, file_size)
                            
                            # 生成预览
                            previews = self.generate_video_previews(filename, vid)
                            if previews:
                                video_info.previews = previews
                            
                            self.video_thumbnails.append(video_info)
                            self.save_video_metadata()
                        
                        return True, f"文件已存在且完整: {filename}"
                    else:
                        os.remove(filename)
                
                session = self.get_session()
                
                headers = {
                    "User-Agent": self.get_random_ua(),
                    "Accept": "*/*",
                    "Connection": "keep-alive",
                    "Accept-Encoding": "gzip, deflate"
                }
                
                with session.get(url, headers=headers, stream=True, timeout=30, verify=False) as response:
                    if response.status_code == 200:
                        total_size = int(response.headers.get('content-length', 0))
                        
                        if total_size == 0:
                            return False, f"文件大小为零，可能无效: {url}"
                        
                        with open(filename, 'wb') as f:
                            for chunk in response.iter_content(chunk_size=512*1024):
                                # 检查是否应该停止
                                if self.stop_download:
                                    f.close()
                                    if os.path.exists(filename):
                                        os.remove(filename)
                                    return False, "下载已中断"
                                    
                                if chunk:
                                    f.write(chunk)
                                    f.flush()
                        
                        file_size = os.path.getsize(filename)
                        if file_size > 1024 and self.verify_file_integrity(filename, total_size):
                            # 下载成功后创建视频信息并生成预览
                            video_info = VideoInfo(vid, video_format, filename, file_size)
                            
                            # 生成预览
                            previews = self.generate_video_previews(filename, vid)
                            if previews:
                                video_info.previews = previews
                            
                            self.video_thumbnails.append(video_info)
                            self.save_video_metadata()
                            
                            return True, f"下载完成: {filename}"
                        else:
                            os.remove(filename)
                            return False, f"文件不完整: {filename}"
                    else:
                        return False, f"下载失败: HTTP {response.status_code} - {url}"
                        
            except Exception as e:
                if attempt == self.retry_attempts - 1:
                    return False, f"下载异常: {str(e)} - {url}"
        
        return False, f"下载失败: 超过最大重试次数 - {url}"

    # 下载所有视频
    def download_all(self, max_threads=10, progress_callback=None):
        """同步下载所有有效的VID"""
        if not self.valid_vids:
            return False, "没有可下载的VID! 请先扫描VID范围"
            
        total = len(self.valid_vids)
        
        self.task_status = "下载中"
        self.task_message = f"开始下载 {total} 个视频文件..."
        self.download_results = []
        self.stop_download = False
        
        if total < 10:
            max_threads = min(10, max_threads)
        elif total < 50:
            max_threads = min(30, max_threads)
        else:
            max_threads = min(100, max_threads)
        
        self.task_message = f"使用 {max_threads} 个线程进行下载..."
        
        completed = 0
        successful = 0
        
        with concurrent.futures.ThreadPoolExecutor(max_workers=max_threads) as executor:
            futures = {executor.submit(self.download_video, vid): vid for vid in self.valid_vids}
            
            for future in concurrent.futures.as_completed(futures):
                # 检查是否应该停止
                if self.stop_download:
                    self.task_message = "正在停止下载..."
                    # 取消所有未完成的任务
                    for f in futures:
                        f.cancel()
                    break
                
                vid = futures[future]
                completed += 1
                self.task_progress = int((completed / total) * 100)
                
                try:
                    success, message = future.result()
                    if success:
                        successful += 1
                        status = "成功"
                    else:
                        status = "失败"
                    
                    self.download_results.append({
                        "vid": vid,
                        "status": status,
                        "message": message
                    })
                    
                    self.task_message = f"下载进度: {successful}/{completed}/{total} - {message}"
                except Exception as e:
                    self.download_results.append({
                        "vid": vid,
                        "status": "错误",
                        "message": str(e)
                    })
                
                if progress_callback:
                    progress_callback(self.task_progress, self.task_message)
        
        if self.stop_download:
            self.task_status = "下载已中断"
            self.task_message = f"下载已中断! 已完成 {completed}/{total}，成功 {successful} 个"
        else:
            self.task_status = "下载完成"
            self.task_message = f"下载完成! 成功: {successful}/{total}"
        
        return True, self.task_message

    # 辅助方法
    def verify_file_integrity(self, filename, expected_size=None):
        """验证文件完整性"""
        try:
            if not os.path.exists(filename):
                return False
                
            file_size = os.path.getsize(filename)
            if file_size < 1024:
                return False
                
            if expected_size and file_size != expected_size:
                return False
                
            return True
            
        except Exception as e:
            return False

    def get_session(self):
        """获取或创建连接会话"""
        thread_id = threading.get_ident()
        if thread_id not in self.connection_pool:
            session = requests.Session()
            
            adapter = requests.adapters.HTTPAdapter(
                pool_connections=10,
                pool_maxsize=100,
                max_retries=3,
                pool_block=False
            )
            
            session.mount('http://', adapter)
            session.mount('https://', adapter)
            
            self.connection_pool[thread_id] = session
        
        return self.connection_pool[thread_id]

    def export_results(self, filename="valid_vids.txt"):
        """导出有效VID列表"""
        with open(filename, "w") as f:
            for vid in self.valid_vids:
                f.write(f"{vid}\n")
        return filename

    def get_thumbnail_base64(self, thumbnail_path):
        """获取缩略图的Base64编码"""
        try:
            if os.path.exists(thumbnail_path):
                with open(thumbnail_path, "rb") as img_file:
                    return base64.b64encode(img_file.read()).decode('utf-8')
            return None
        except:
            return None

    def get_preview_base64(self, preview_path):
        """获取预览文件的Base64编码"""
        try:
            if os.path.exists(preview_path):
                with open(preview_path, "rb") as file:
                    return base64.b64encode(file.read()).decode('utf-8')
            return None
        except:
            return None

    def get_video_base64(self, video_path):
        """获取视频文件的Base64编码（用于小视频预览）"""
        try:
            if os.path.exists(video_path):
                file_size = os.path.getsize(video_path)
                # 只对小文件进行Base64编码（小于10MB）
                if file_size < 10 * 1024 * 1024:
                    with open(video_path, "rb") as video_file:
                        return base64.b64encode(video_file.read()).decode('utf-8')
            return None
        except:
            return None

    def mark_video(self, vid, action, value=None):
        """标记视频（收藏、评分、备注等）"""
        for video_info in self.video_thumbnails:
            if isinstance(video_info, VideoInfo) and video_info.vid == vid:
                if action == 'favorite':
                    if 'favorite' in video_info.tags:
                        video_info.tags.remove('favorite')
                    else:
                        video_info.tags.append('favorite')
                elif action == 'watch_later':
                    if 'watch_later' in video_info.tags:
                        video_info.tags.remove('watch_later')
                    else:
                        video_info.tags.append('watch_later')
                elif action == 'rate':
                    video_info.rating = value
                elif action == 'add_note':
                    video_info.notes = value
                
                # 保存元数据
                self.save_video_metadata()
                return True
        
        return False

    def get_video_info_dict(self, video_info):
        """将VideoInfo对象转换为字典，包含Base64编码的预览"""
        previews_base64 = {}
        
        # 转换缩略图
        if video_info.previews.get('thumbnail'):
            previews_base64['thumbnail'] = self.get_thumbnail_base64(video_info.previews['thumbnail'])
        
        # 转换GIF
        if video_info.previews.get('gif'):
            previews_base64['gif'] = self.get_preview_base64(video_info.previews['gif'])
        
        # 转换快照
        previews_base64['snapshots'] = []
        for snapshot_path in video_info.previews.get('snapshots', []):
            snapshot_base64 = self.get_preview_base64(snapshot_path)
            if snapshot_base64:
                previews_base64['snapshots'].append(snapshot_base64)
        
        # 添加视频文件（小文件）
        if video_info.file_size < 5 * 1024 * 1024:  # 小于5MB的视频
            video_base64 = self.get_video_base64(video_info.file_path)
            if video_base64:
                previews_base64['video_preview'] = video_base64
        
        # 添加缩略图质量信息
        if 'thumbnail_quality' in video_info.previews:
            previews_base64['thumbnail_quality'] = video_info.previews['thumbnail_quality']
        
        return {
            "vid": video_info.vid,
            "format": video_info.format,
            "file_size": video_info.file_size,
            "file_path": video_info.file_path,
            "previews": previews_base64,
            "tags": video_info.tags,
            "rating": video_info.rating,
            "notes": video_info.notes,
            "added_time": video_info.added_time
        }

    def get_videos_paginated(self, page=1, per_page=12, view_type='grid'):
        """获取分页视频数据"""
        start_idx = (page - 1) * per_page
        end_idx = start_idx + per_page
        
        videos_info = []
        for item in self.video_thumbnails[start_idx:end_idx]:
            if isinstance(item, VideoInfo):
                videos_info.append(self.get_video_info_dict(item))
        
        total = len([v for v in self.video_thumbnails if isinstance(v, VideoInfo)])
        pages = (total + per_page - 1) // per_page
        
        return {
            "videos": videos_info,
            "pagination": {
                "page": page,
                "per_page": per_page,
                "total": total,
                "pages": pages
            }
        }

    def get_status(self):
        """获取当前状态"""
        # 获取视频信息（只返回基本信息，不包含分页数据）
        videos_count = len([v for v in self.video_thumbnails if isinstance(v, VideoInfo)])
        
        return {
            "task": self.current_task,
            "progress": self.task_progress,
            "status": self.task_status,
            "message": self.task_message,
            "valid_vids_count": len(self.valid_vids),
            "videos_count": videos_count,
            "scan_results": self.scan_results[-10:] if self.scan_results else [],
            "download_results": self.download_results[-10:] if self.download_results else [],
            "selected_formats": self.selected_formats,
            "moviepy_available": MOVIEPY_AVAILABLE
        }

    def reset_task(self):
        """重置任务状态"""
        self.current_task = None
        self.task_progress = 0
        self.task_status = "空闲"
        self.task_message = ""
        self.stop_scan = False
        self.stop_download = False

# 创建Flask应用
app = Flask(__name__)
downloader = SinaVideoDownloader()

# 存储任务线程的引用
current_scan_thread = None
current_download_thread = None

def scan_thread(start_vid, end_vid, max_threads):
    """扫描线程函数"""
    global downloader
    downloader.scan_vids(start_vid, end_vid, max_threads)

def download_thread(max_threads):
    """下载线程函数"""
    global downloader
    downloader.download_all(max_threads)

@app.route('/')
def index():
    """主页面"""
    return render_template('index.html')

@app.route('/api/status')
def api_status():
    """获取状态API"""
    return jsonify(downloader.get_status())

@app.route('/api/videos')
def api_videos():
    """获取分页视频数据API"""
    page = request.args.get('page', 1, type=int)
    per_page = request.args.get('per_page', 12, type=int)
    view_type = request.args.get('view_type', 'grid', type=str)
    
    videos_data = downloader.get_videos_paginated(page, per_page, view_type)
    return jsonify(videos_data)

@app.route('/api/scan', methods=['POST'])
def api_scan():
    """开始扫描API"""
    global current_scan_thread
    
    # 如果已有扫描任务在运行，返回错误
    if current_scan_thread and current_scan_thread.is_alive():
        return jsonify({"success": False, "message": "已有扫描任务在运行"})
    
    data = request.json
    start_vid = int(data.get('start_vid', 1))
    end_vid = int(data.get('end_vid', 100))
    max_threads = int(data.get('max_threads', 50))
    
    # 启动扫描线程
    current_scan_thread = threading.Thread(
        target=scan_thread, 
        args=(start_vid, end_vid, max_threads)
    )
    current_scan_thread.daemon = True
    current_scan_thread.start()
    
    return jsonify({"success": True, "message": "扫描任务已启动"})

@app.route('/api/stop_scan', methods=['POST'])
def api_stop_scan():
    """停止扫描API"""
    downloader.stop_scanning()
    return jsonify({"success": True, "message": "扫描停止命令已发送"})

@app.route('/api/download', methods=['POST'])
def api_download():
    """开始下载API"""
    global current_download_thread
    
    # 如果已有下载任务在运行，返回错误
    if current_download_thread and current_download_thread.is_alive():
        return jsonify({"success": False, "message": "已有下载任务在运行"})
    
    data = request.json
    max_threads = int(data.get('max_threads', 10))
    
    # 启动下载线程
    current_download_thread = threading.Thread(
        target=download_thread, 
        args=(max_threads,)
    )
    current_download_thread.daemon = True
    current_download_thread.start()
    
    return jsonify({"success": True, "message": "下载任务已启动"})

@app.route('/api/stop_download', methods=['POST'])
def api_stop_download():
    """停止下载API"""
    downloader.stop_downloading()
    return jsonify({"success": True, "message": "下载停止命令已发送"})

@app.route('/api/clear_cache', methods=['POST'])
def api_clear_cache():
    """清除缓存API"""
    success, message = downloader.clear_cache()
    return jsonify({"success": success, "message": message})

@app.route('/api/settings', methods=['GET', 'POST'])
def api_settings():
    """设置API"""
    if request.method == 'GET':
        # 返回当前设置
        settings = {
            "run_mode": downloader.run_mode.name,
            "other_check_api": downloader.other_check_api.name,
            "video_type_filter": {k.name: v for k, v in downloader.video_type_filter.items()},
            "selected_formats": downloader.selected_formats,
            "supported_formats": downloader.supported_formats,
            "preview_settings": downloader.preview_settings,
            "moviepy_available": MOVIEPY_AVAILABLE
        }
        return jsonify(settings)
    
    else:  # POST
        data = request.json
        
        if 'run_mode' in data:
            mode = RunMode[data['run_mode']]
            downloader.set_run_mode(mode)
        
        if 'other_check_api' in data:
            api = OtherCheckAPI[data['other_check_api']]
            downloader.set_other_check_api(api)
        
        if 'video_type_filter' in data:
            for type_name, enabled in data['video_type_filter'].items():
                video_type = VideoType[type_name]
                downloader.set_video_type_filter(video_type, enabled)
        
        if 'selected_formats' in data:
            downloader.set_selected_formats(data['selected_formats'])
        
        if 'preview_settings' in data:
            downloader.set_preview_settings(data['preview_settings'])
        
        return jsonify({"success": True, "message": "设置已更新"})

@app.route('/api/video/mark', methods=['POST'])
def api_mark_video():
    """标记视频API"""
    data = request.json
    vid = data.get('vid')
    action = data.get('action')
    value = data.get('value')
    
    success = downloader.mark_video(vid, action, value)
    if success:
        return jsonify({"success": True, "message": "标记成功"})
    else:
        return jsonify({"success": False, "message": "视频未找到"})

@app.route('/api/export')
def api_export():
    """导出有效VID列表"""
    filename = downloader.export_results()
    return send_file(filename, as_attachment=True)

@app.route('/api/reset')
def api_reset():
    """重置任务状态"""
    downloader.reset_task()
    return jsonify({"success": True, "message": "状态已重置"})

@app.route('/thumbnails/<path:filename>')
def serve_thumbnail(filename):
    """提供缩略图文件"""
    return send_from_directory(downloader.thumbnails_dir, filename)

@app.route('/previews/<path:filename>')
def serve_preview(filename):
    """提供预览文件"""
    return send_from_directory(downloader.previews_dir, filename)

@app.route('/videos/<path:filename>')
def serve_video(filename):
    """提供视频文件"""
    return send_from_directory(downloader.output_dir, filename)

if __name__ == '__main__':
    # 创建模板目录
    if not os.path.exists('templates'):
        os.makedirs('templates')
    
    # 生成HTML模板（修复GIF和视频播放问题）
    with open('templates/index.html', 'w', encoding='utf-8') as f:
        f.write('''<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>新浪视频下载工具 - 增强版</title>
    <!-- 引入flv.js -->
    <script src="https://cdn.jsdelivr.net/npm/flv.js@latest/dist/flv.min.js"></script>
    <style>
        * {
            margin: 0;
            padding: 0;
            box-sizing: border-box;
        }
        
        body {
            font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
            line-height: 1.6;
            color: #333;
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            min-height: 100vh;
            padding: 20px;
        }
        
        .container {
            max-width: 1600px;
            margin: 0 auto;
            background: white;
            border-radius: 15px;
            box-shadow: 0 10px 30px rgba(0, 0, 0, 0.3);
            overflow: hidden;
        }
        
        header {
            background: linear-gradient(135deg, #2c3e50, #34495e);
            color: white;
            padding: 25px;
            text-align: center;
            position: relative;
            border-bottom: 1px solid rgba(255, 255, 255, 0.1);
        }
        
        header h1 {
            margin-bottom: 10px;
            font-size: 2.5rem;
            text-shadow: 2px 2px 4px rgba(0, 0, 0, 0.3);
        }
        
        header .subtitle {
            opacity: 0.9;
            font-size: 1.1rem;
            margin-bottom: 15px;
        }
        
        .main-content {
            display: flex;
            flex-wrap: wrap;
            padding: 25px;
        }
        
        .panel {
            flex: 1;
            min-width: 300px;
            margin: 15px;
            padding: 25px;
            background: #f8f9fa;
            border-radius: 12px;
            box-shadow: 0 4px 15px rgba(0, 0, 0, 0.1);
            transition: transform 0.3s, box-shadow 0.3s;
        }
        
        .panel:hover {
            transform: translateY(-5px);
            box-shadow: 0 8px 25px rgba(0, 0, 0, 0.15);
        }
        
        .panel h2 {
            margin-bottom: 20px;
            padding-bottom: 15px;
            border-bottom: 2px solid #e9ecef;
            color: #2c3e50;
            font-size: 1.5rem;
        }
        
        .form-group {
            margin-bottom: 20px;
        }
        
        label {
            display: block;
            margin-bottom: 8px;
            font-weight: 600;
            color: #495057;
        }
        
        input, select {
            width: 100%;
            padding: 12px;
            border: 1px solid #ced4da;
            border-radius: 6px;
            font-size: 14px;
            background: white;
            transition: border-color 0.3s, box-shadow 0.3s;
        }
        
        input:focus, select:focus {
            outline: none;
            border-color: #3498db;
            box-shadow: 0 0 0 3px rgba(52, 152, 219, 0.2);
        }
        
        button {
            background: #3498db;
            color: white;
            border: none;
            padding: 14px 20px;
            border-radius: 6px;
            cursor: pointer;
            font-size: 16px;
            font-weight: 600;
            transition: all 0.3s;
            width: 100%;
            margin-top: 10px;
            box-shadow: 0 4px 6px rgba(52, 152, 219, 0.3);
        }
        
        button:hover {
            background: #2980b9;
            transform: translateY(-2px);
            box-shadow: 0 6px 8px rgba(52, 152, 219, 0.4);
        }
        
        button:active {
            transform: translateY(0);
            box-shadow: 0 2px 4px rgba(52, 152, 219, 0.3);
        }
        
        button:disabled {
            background: #95a5a6;
            cursor: not-allowed;
            transform: none;
            box-shadow: none;
        }
        
        .btn-success {
            background: #27ae60;
            box-shadow: 0 4px 6px rgba(39, 174, 96, 0.3);
        }
        
        .btn-success:hover {
            background: #219653;
            box-shadow: 0 6px 8px rgba(39, 174, 96, 0.4);
        }
        
        .btn-warning {
            background: #e67e22;
            box-shadow: 0 4px 6px rgba(230, 126, 34, 0.3);
        }
        
        .btn-warning:hover {
            background: #d35400;
            box-shadow: 0 6px 8px rgba(230, 126, 34, 0.4);
        }
        
        .btn-danger {
            background: #e74c3c;
            box-shadow: 0 4px 6px rgba(231, 76, 60, 0.3);
        }
        
        .btn-danger:hover {
            background: #c0392b;
            box-shadow: 0 6px 8px rgba(231, 76, 60, 0.4);
        }
        
        .btn-secondary {
            background: #7f8c8d;
            box-shadow: 0 4px 6px rgba(127, 140, 141, 0.3);
        }
        
        .btn-secondary:hover {
            background: #636e72;
            box-shadow: 0 6px 8px rgba(127, 140, 141, 0.4);
        }
        
        .status-panel {
            background: white;
        }
        
        .progress-container {
            margin: 20px 0;
        }
        
        .progress-bar {
            height: 25px;
            background: #ecf0f1;
            border-radius: 12px;
            overflow: hidden;
            box-shadow: inset 0 2px 4px rgba(0, 0, 0, 0.1);
        }
        
        .progress-fill {
            height: 100%;
            background: linear-gradient(90deg, #3498db, #2ecc71);
            width: 0%;
            transition: width 0.5s;
            position: relative;
            overflow: hidden;
        }
        
        .progress-fill::after {
            content: '';
            position: absolute;
            top: 0;
            left: 0;
            bottom: 0;
            right: 0;
            background-image: linear-gradient(
                -45deg,
                rgba(255, 255, 255, 0.2) 25%,
                transparent 25%,
                transparent 50%,
                rgba(255, 255, 255, 0.2) 50%,
                rgba(255, 255, 255, 0.2) 75%,
                transparent 75%,
                transparent
            );
            background-size: 50px 50px;
            animation: move 2s linear infinite;
        }
        
        @keyframes move {
            0% {
                background-position: 0 0;
            }
            100% {
                background-position: 50px 50px;
            }
        }
        
        .status-info {
            margin: 15px 0;
            padding: 15px;
            background: #f8f9fa;
            border-radius: 8px;
            border-left: 4px solid #3498db;
            box-shadow: 0 2px 5px rgba(0, 0, 0, 0.05);
        }
        
        .results {
            max-height: 300px;
            overflow-y: auto;
            margin-top: 15px;
            border-radius: 8px;
            background: rgba(255, 255, 255, 0.8);
            padding: 10px;
        }
        
        .result-item {
            padding: 10px 15px;
            margin-bottom: 8px;
            border-radius: 6px;
            background: white;
            border-left: 4px solid #3498db;
            box-shadow: 0 2px 4px rgba(0, 0, 0, 0.05);
            transition: transform 0.2s;
        }
        
        .result-item:hover {
            transform: translateX(5px);
        }
        
        .result-item.success {
            border-left-color: #27ae60;
        }
        
        .result-item.error {
            border-left-color: #e74c3c;
        }
        
        .result-item.warning {
            border-left-color: #f39c12;
        }
        
        .checkbox-group {
            display: flex;
            flex-wrap: wrap;
            gap: 12px;
            margin-top: 10px;
        }
        
        .checkbox-item {
            display: flex;
            align-items: center;
            gap: 8px;
            padding: 8px 12px;
            background: white;
            border-radius: 6px;
            transition: background 0.3s;
        }
        
        .checkbox-item:hover {
            background: #f8f9fa;
        }
        
        .checkbox-item input {
            width: auto;
        }
        
        .view-controls {
            display: flex;
            gap: 10px;
            margin-bottom: 20px;
            flex-wrap: wrap;
        }
        
        .view-btn {
            padding: 8px 16px;
            border: 1px solid #3498db;
            background: white;
            color: #3498db;
            border-radius: 6px;
            cursor: pointer;
            transition: all 0.3s;
        }
        
        .view-btn.active {
            background: #3498db;
            color: white;
        }
        
        .view-btn:hover {
            background: #2980b9;
            color: white;
        }
        
        .view-container {
            display: none;
        }
        
        .view-container.active {
            display: block;
        }
        
        /* 九宫格视图 */
        .video-grid {
            display: grid;
            grid-template-columns: repeat(auto-fill, minmax(250px, 1fr));
            gap: 20px;
            margin-top: 20px;
        }
        
        .video-card {
            border: 1px solid #ddd;
            border-radius: 10px;
            overflow: hidden;
            background: white;
            box-shadow: 0 4px 8px rgba(0,0,0,0.1);
            transition: transform 0.3s, box-shadow 0.3s;
            position: relative;
        }
        
        .video-card:hover {
            transform: translateY(-8px);
            box-shadow: 0 8px 16px rgba(0,0,0,0.2);
        }
        
        .video-preview {
            width: 100%;
            height: 150px;
            object-fit: cover;
            background: #f8f9fa;
            cursor: pointer;
        }
        
        .video-info {
            padding: 12px;
        }
        
        .video-vid {
            font-weight: bold;
            margin-bottom: 5px;
            color: #2c3e50;
            font-size: 1.1rem;
        }
        
        .video-details {
            color: #6c757d;
            font-size: 0.9rem;
            margin-bottom: 10px;
        }
        
        .video-tags {
            display: flex;
            flex-wrap: wrap;
            gap: 5px;
            margin-bottom: 10px;
        }
        
        .tag {
            padding: 2px 8px;
            background: #e9ecef;
            border-radius: 12px;
            font-size: 0.8rem;
            color: #495057;
        }
        
        .tag.favorite {
            background: #ffeaa7;
            color: #e17055;
        }
        
        .tag.watch-later {
            background: #a29bfe;
            color: white;
        }
        
        .tag.low-quality {
            background: #fab1a0;
            color: #d63031;
        }
        
        .video-actions {
            display: flex;
            gap: 5px;
            flex-wrap: wrap;
        }
        
        .action-btn {
            flex: 1;
            padding: 5px 10px;
            background: #f8f9fa;
            border: 1px solid #dee2e6;
            border-radius: 4px;
            cursor: pointer;
            font-size: 0.8rem;
            transition: all 0.2s;
        }
        
        .action-btn:hover {
            background: #e9ecef;
        }
        
        .action-btn.active {
            background: #3498db;
            color: white;
            border-color: #3498db;
        }
        
        .play-btn {
            position: absolute;
            top: 10px;
            right: 10px;
            background: rgba(0, 0, 0, 0.7);
            color: white;
            border: none;
            border-radius: 50%;
            width: 40px;
            height: 40px;
            display: flex;
            align-items: center;
            justify-content: center;
            cursor: pointer;
            opacity: 0;
            transition: opacity 0.3s;
            z-index: 2;
        }
        
        .video-card:hover .play-btn {
            opacity: 1;
        }
        
        .play-btn:hover {
            background: rgba(0, 0, 0, 0.9);
        }
        
        .rating-stars {
            display: flex;
            gap: 2px;
            margin-bottom: 10px;
        }
        
        .star {
            color: #ddd;
            cursor: pointer;
            font-size: 1.2rem;
        }
        
        .star.active {
            color: #f39c12;
        }
        
        /* 列表视图 */
        .video-list {
            margin-top: 20px;
        }
        
        .list-item {
            display: flex;
            align-items: center;
            padding: 15px;
            border-bottom: 1px solid #e9ecef;
            transition: background 0.2s;
            position: relative;
        }
        
        .list-item:hover {
            background: #f8f9fa;
        }
        
        .list-preview {
            width: 120px;
            height: 80px;
            object-fit: cover;
            border-radius: 6px;
            margin-right: 15px;
        }
        
        .list-info {
            flex: 1;
        }
        
        .list-actions {
            display: flex;
            gap: 10px;
        }
        
        /* 分页控件 */
        .pagination {
            display: flex;
            justify-content: center;
            align-items: center;
            margin: 20px 0;
            gap: 10px;
        }
        
        .page-btn {
            padding: 8px 16px;
            border: 1px solid #dee2e6;
            background: white;
            color: #3498db;
            border-radius: 6px;
            cursor: pointer;
            transition: all 0.3s;
        }
        
        .page-btn:hover {
            background: #3498db;
            color: white;
        }
        
        .page-btn.active {
            background: #3498db;
            color: white;
            border-color: #3498db;
        }
        
        .page-btn:disabled {
            background: #f8f9fa;
            color: #6c757d;
            cursor: not-allowed;
        }
        
        .page-info {
            margin: 0 15px;
            color: #6c757d;
        }
        
        /* 模态框 */
        .modal {
            display: none;
            position: fixed;
            top: 0;
            left: 0;
            width: 100%;
            height: 100%;
            background: rgba(0, 0, 0, 0.8);
            z-index: 1000;
            justify-content: center;
            align-items: center;
        }
        
        .modal-content {
            background: white;
            border-radius: 10px;
            padding: 20px;
            max-width: 90%;
            max-height: 90%;
            overflow: auto;
            position: relative;
        }
        
        .snapshots-grid {
            display: grid;
            grid-template-columns: repeat(3, 1fr);
            gap: 10px;
        }
        
        .snapshot-img {
            width: 100%;
            border-radius: 6px;
        }
        
        .close-modal {
            position: absolute;
            top: 15px;
            right: 15px;
            background: #e74c3c;
            color: white;
            border: none;
            border-radius: 50%;
            width: 40px;
            height: 40px;
            font-size: 1.5rem;
            cursor: pointer;
            display: flex;
            justify-content: center;
            align-items: center;
            z-index: 1001;
        }
        
        /* 视频播放器模态框 */
        .video-modal {
            display: none;
            position: fixed;
            top: 0;
            left: 0;
            width: 100%;
            height: 100%;
            background: rgba(0, 0, 0, 0.9);
            z-index: 1000;
            justify-content: center;
            align-items: center;
        }
        
        .video-player-container {
            max-width: 90%;
            max-height: 90%;
            background: black;
            border-radius: 10px;
            overflow: hidden;
            position: relative;
        }
        
        .video-player {
            width: 100%;
            height: auto;
            max-height: 80vh;
        }
        
        .video-info-panel {
            padding: 15px;
            background: #2c3e50;
            color: white;
        }
        
        .video-info-panel h3 {
            margin-bottom: 10px;
            color: #3498db;
        }
        
        .video-info-panel p {
            margin-bottom: 5px;
            font-size: 0.9rem;
        }
        
        .action-buttons {
            display: flex;
            gap: 10px;
            margin-top: 10px;
        }
        
        .action-buttons button {
            flex: 1;
            margin-top: 0;
        }
        
        .footer {
            text-align: center;
            padding: 20px;
            background: #f8f9fa;
            color: #6c757d;
            border-top: 1px solid #e9ecef;
        }
        
        .preview-settings {
            background: white;
            padding: 15px;
            border-radius: 8px;
            margin-top: 15px;
        }
        
        .preview-setting-item {
            display: flex;
            justify-content: space-between;
            align-items: center;
            margin-bottom: 10px;
        }
        
        .preview-setting-item label {
            margin-bottom: 0;
            flex: 1;
        }
        
        .preview-setting-item input {
            width: 80px;
            margin-left: 10px;
        }
        
        .quality-badge {
            position: absolute;
            top: 10px;
            left: 10px;
            background: rgba(231, 76, 60, 0.8);
            color: white;
            padding: 2px 8px;
            border-radius: 10px;
            font-size: 0.7rem;
            z-index: 1;
        }
        
        .gif-generating {
            position: absolute;
            top: 50%;
            left: 50%;
            transform: translate(-50%, -50%);
            background: rgba(0, 0, 0, 0.7);
            color: white;
            padding: 5px 10px;
            border-radius: 5px;
            font-size: 0.8rem;
        }
        
        @media (max-width: 768px) {
            .main-content {
                flex-direction: column;
            }
            
            .panel {
                min-width: 100%;
            }
            
            .video-grid {
                grid-template-columns: repeat(auto-fill, minmax(200px, 1fr));
            }
            
            .action-buttons {
                flex-direction: column;
            }
            
            .snapshots-grid {
                grid-template-columns: repeat(2, 1fr);
            }
            
            .list-item {
                flex-direction: column;
                align-items: flex-start;
            }
            
            .list-preview {
                width: 100%;
                height: 150px;
                margin-right: 0;
                margin-bottom: 10px;
            }
            
            .pagination {
                flex-wrap: wrap;
            }
            
            .video-player-container {
                max-width: 95%;
            }
        }
    </style>
</head>
<body>
    <div class="container">
        <header>
            <h1>新浪视频下载工具 - 增强版</h1>
            <div class="subtitle">支持视频预览、九宫格展示、分页浏览和视频播放</div>
        </header>
        
        <div class="main-content">
            <div class="panel">
                <h2>扫描设置</h2>
                <div class="form-group">
                    <label for="start_vid">起始VID:</label>
                    <input type="number" id="start_vid" value="1" min="1">
                </div>
                
                <div class="form-group">
                    <label for="end_vid">结束VID:</label>
                    <input type="number" id="end_vid" value="100" min="1">
                </div>
                
                <div class="form-group">
                    <label for="scan_threads">扫描线程数:</label>
                    <input type="number" id="scan_threads" value="50" min="1" max="200">
                </div>
                
                <div class="action-buttons">
                    <button id="scan-btn" class="btn-success">开始扫描</button>
                    <button id="stop-scan-btn" class="btn-danger" disabled>停止扫描</button>
                </div>
            </div>
            
            <div class="panel">
                <h2>下载设置</h2>
                <div class="form-group">
                    <label for="download_threads">下载线程数:</label>
                    <input type="number" id="download_threads" value="10" min="1" max="50">
                </div>
                
                <div class="action-buttons">
                    <button id="download-btn" class="btn-warning">开始下载</button>
                    <button id="stop-download-btn" class="btn-danger" disabled>停止下载</button>
                </div>
                
                <button id="export-btn" class="btn-secondary">导出VID列表</button>
                <button id="clear-cache-btn" class="btn-danger">清除缓存</button>
            </div>
            
            <div class="panel">
                <h2>程序设置</h2>
                <div class="form-group">
                    <label for="run_mode">运行模式:</label>
                    <select id="run_mode">
                        <option value="THREADING">多线程模式</option>
                        <option value="ASYNC">异步模式</option>
                    </select>
                </div>
                
                <div class="form-group">
                    <label for="other_check_api">异常视频检测API:</label>
                    <select id="other_check_api">
                        <option value="MAIN">主API</option>
                        <option value="BACKUP">备用API</option>
                    </select>
                </div>
                
                <div class="form-group">
                    <label>文件格式筛选:</label>
                    <div class="checkbox-group" id="format_filter">
                        <!-- 动态生成 -->
                    </div>
                </div>
                
                <div class="form-group">
                    <label>视频类型过滤:</label>
                    <div class="checkbox-group" id="video_type_filter">
                        <!-- 动态生成 -->
                    </div>
                </div>
                
                <div class="preview-settings">
                    <h3>预览设置</h3>
                    <div class="preview-setting-item">
                        <label for="gif_duration">GIF时长 (秒):</label>
                        <input type="number" id="gif_duration" min="1" max="10">
                    </div>
                    <div class="preview-setting-item">
                        <label for="gif_fps">GIF帧率:</label>
                        <input type="number" id="gif_fps" min="1" max="15">
                    </div>
                    <div class="preview-setting-item">
                        <label for="gif_max_size">GIF最大尺寸:</label>
                        <input type="number" id="gif_max_size" min="100" max="500">
                    </div>
                    <div class="preview-setting-item">
                        <label for="snapshot_count">快照数量:</label>
                        <input type="number" id="snapshot_count" min="1" max="12">
                    </div>
                    <div class="preview-setting-item">
                        <label for="preview_quality">预览质量 (1-100):</label>
                        <input type="number" id="preview_quality" min="1" max="100">
                    </div>
                    <div class="checkbox-item">
                        <input type="checkbox" id="thumbnail_check_enabled" checked>
                        <label for="thumbnail_check_enabled">检查缩略图质量</label>
                    </div>
                    <div class="preview-setting-item">
                        <label for="min_thumbnail_quality">最低缩略图质量:</label>
                        <input type="number" id="min_thumbnail_quality" min="1" max="100">
                    </div>
                    <div class="checkbox-item">
                        <input type="checkbox" id="gif_use_opencv" checked>
                        <label for="gif_use_opencv">使用OpenCV生成GIF（备选）</label>
                    </div>
                </div>
                
                <button id="save-settings">保存设置</button>
                <button id="reset-btn" class="btn-secondary">重置状态</button>
            </div>
        </div>
        
        <div class="panel status-panel">
            <h2>任务状态</h2>
            <div class="status-info">
                <div id="status-text">状态: 空闲</div>
                <div id="message-text">消息: 等待任务开始</div>
                <div id="valid-vids-text">有效VID数: 0</div>
                <div id="downloaded-videos-text">已下载视频: 0</div>
                <div id="moviepy-status"></div>
            </div>
            
            <div class="progress-container">
                <label>进度:</label>
                <div class="progress-bar">
                    <div class="progress-fill" id="progress-fill"></div>
                </div>
                <div id="progress-text">0%</div>
            </div>
            
            <div class="results" id="scan-results">
                <h3>扫描结果</h3>
                <div id="scan-results-list"></div>
            </div>
            
            <div class="results" id="download-results">
                <h3>下载结果</h3>
                <div id="download-results-list"></div>
            </div>
            
            <div id="videos-section">
                <h3>视频库</h3>
                
                <div class="view-controls">
                    <button class="view-btn active" data-view="grid">九宫格视图</button>
                    <button class="view-btn" data-view="list">列表视图</button>
                    <button class="view-btn" data-view="gif">GIF预览</button>
                    <div style="flex: 1;"></div>
                    <div>
                        <label for="per_page">每页显示:</label>
                        <select id="per_page">
                            <option value="12">12</option>
                            <option value="24">24</option>
                            <option value="48">48</option>
                            <option value="96">96</option>
                        </select>
                    </div>
                </div>
                
                <!-- 分页控件 -->
                <div class="pagination" id="pagination-controls">
                    <button class="page-btn" id="first-page">首页</button>
                    <button class="page-btn" id="prev-page">上一页</button>
                    <span class="page-info" id="page-info">第 1 页，共 1 页</span>
                    <button class="page-btn" id="next-page">下一页</button>
                    <button class="page-btn" id="last-page">末页</button>
                </div>
                
                <!-- 九宫格视图 -->
                <div id="grid-view" class="view-container active">
                    <div class="video-grid" id="video-grid">
                        <!-- 动态生成视频卡片 -->
                    </div>
                </div>
                
                <!-- 列表视图 -->
                <div id="list-view" class="view-container">
                    <div class="video-list" id="video-list">
                        <!-- 动态生成列表项 -->
                    </div>
                </div>
                
                <!-- GIF预览视图 -->
                <div id="gif-view" class="view-container">
                    <div class="video-grid" id="gif-grid">
                        <!-- 动态生成GIF卡片 -->
                    </div>
                </div>
                
                <!-- 分页控件底部 -->
                <div class="pagination" id="pagination-controls-bottom">
                    <button class="page-btn" id="first-page-bottom">首页</button>
                    <button class="page-btn" id="prev-page-bottom">上一页</button>
                    <span class="page-info" id="page-info-bottom">第 1 页，共 1 页</span>
                    <button class="page-btn" id="next-page-bottom">下一页</button>
                    <button class="page-btn" id="last-page-bottom">末页</button>
                </div>
            </div>
            
            <!-- 快照查看器模态框 -->
            <div id="snapshot-modal" class="modal">
                <button class="close-modal" onclick="closeSnapshotModal()">×</button>
                <div class="modal-content">
                    <h3>视频快照</h3>
                    <div class="snapshots-grid" id="snapshots-grid">
                        <!-- 动态生成快照 -->
                    </div>
                </div>
            </div>
            
            <!-- 视频播放器模态框 -->
            <div id="video-modal" class="video-modal">
                <button class="close-modal" onclick="closeVideoModal()">×</button>
                <div class="video-player-container">
                    <video id="video-player" controls style="display: none;">
                        您的浏览器不支持视频播放
                    </video>
                    <div id="flv-player"></div>
                    <div class="video-info-panel">
                        <h3 id="video-modal-title">视频信息</h3>
                        <p id="video-modal-details"></p>
                        <p id="video-modal-path"></p>
                    </div>
                </div>
            </div>
        </div>
        
        <div class="footer">
            <p>新浪视频下载工具 - 增强版 &copy; 2023 - 基于Python Flask开发</p>
        </div>
    </div>
    
    <script>
        // 全局变量
        let statusInterval;
        let videosInterval;
        let currentView = 'grid';
        let currentPage = 1;
        let perPage = 12;
        let totalPages = 1;
        let currentSnapshots = [];
        let flvPlayer = null;
        
        // DOM元素
        const scanBtn = document.getElementById('scan-btn');
        const stopScanBtn = document.getElementById('stop-scan-btn');
        const downloadBtn = document.getElementById('download-btn');
        const stopDownloadBtn = document.getElementById('stop-download-btn');
        const exportBtn = document.getElementById('export-btn');
        const clearCacheBtn = document.getElementById('clear-cache-btn');
        const saveSettingsBtn = document.getElementById('save-settings');
        const resetBtn = document.getElementById('reset-btn');
        
        const statusText = document.getElementById('status-text');
        const messageText = document.getElementById('message-text');
        const validVidsText = document.getElementById('valid-vids-text');
        const downloadedVideosText = document.getElementById('downloaded-videos-text');
        const moviepyStatus = document.getElementById('moviepy-status');
        const progressFill = document.getElementById('progress-fill');
        const progressText = document.getElementById('progress-text');
        
        const scanResultsList = document.getElementById('scan-results-list');
        const downloadResultsList = document.getElementById('download-results-list');
        const videoGrid = document.getElementById('video-grid');
        const videoList = document.getElementById('video-list');
        const gifGrid = document.getElementById('gif-grid');
        
        const perPageSelect = document.getElementById('per_page');
        
        // 分页控件
        const firstPageBtn = document.getElementById('first-page');
        const prevPageBtn = document.getElementById('prev-page');
        const pageInfo = document.getElementById('page-info');
        const nextPageBtn = document.getElementById('next-page');
        const lastPageBtn = document.getElementById('last-page');
        
        const firstPageBottomBtn = document.getElementById('first-page-bottom');
        const prevPageBottomBtn = document.getElementById('prev-page-bottom');
        const pageInfoBottom = document.getElementById('page-info-bottom');
        const nextPageBottomBtn = document.getElementById('next-page-bottom');
        const lastPageBottomBtn = document.getElementById('last-page-bottom');
        
        const snapshotModal = document.getElementById('snapshot-modal');
        const snapshotsGrid = document.getElementById('snapshots-grid');
        
        const videoModal = document.getElementById('video-modal');
        const videoPlayer = document.getElementById('video-player');
        const flvPlayerContainer = document.getElementById('flv-player');
        const videoModalTitle = document.getElementById('video-modal-title');
        const videoModalDetails = document.getElementById('video-modal-details');
        const videoModalPath = document.getElementById('video-modal-path');
        
        // 初始化
        document.addEventListener('DOMContentLoaded', function() {
            loadSettings();
            startStatusPolling();
            startVideosPolling();
            setupViewControls();
            setupPagination();
        });
        
        // 设置视图控制
        function setupViewControls() {
            const viewBtns = document.querySelectorAll('.view-btn');
            viewBtns.forEach(btn => {
                btn.addEventListener('click', function() {
                    // 移除所有active类
                    viewBtns.forEach(b => b.classList.remove('active'));
                    // 隐藏所有视图
                    document.querySelectorAll('.view-container').forEach(container => {
                        container.classList.remove('active');
                    });
                    
                    // 激活当前按钮和视图
                    this.classList.add('active');
                    currentView = this.dataset.view;
                    document.getElementById(`${currentView}-view`).classList.add('active');
                    
                    // 重新加载视频数据
                    loadVideosData();
                });
            });
        }
        
        // 设置分页
        function setupPagination() {
            // 每页显示数量变化
            perPageSelect.addEventListener('change', function() {
                perPage = parseInt(this.value);
                currentPage = 1;
                loadVideosData();
            });
            
            // 分页按钮事件
            const pageButtons = [
                {btn: firstPageBtn, action: () => goToPage(1)},
                {btn: prevPageBtn, action: () => goToPage(currentPage - 1)},
                {btn: nextPageBtn, action: () => goToPage(currentPage + 1)},
                {btn: lastPageBtn, action: () => goToPage(totalPages)},
                {btn: firstPageBottomBtn, action: () => goToPage(1)},
                {btn: prevPageBottomBtn, action: () => goToPage(currentPage - 1)},
                {btn: nextPageBottomBtn, action: () => goToPage(currentPage + 1)},
                {btn: lastPageBottomBtn, action: () => goToPage(totalPages)}
            ];
            
            pageButtons.forEach(item => {
                item.btn.addEventListener('click', item.action);
            });
        }
        
        // 跳转到指定页
        function goToPage(page) {
            if (page < 1) page = 1;
            if (page > totalPages) page = totalPages;
            
            currentPage = page;
            loadVideosData();
        }
        
        // 更新分页控件状态
        function updatePaginationControls(pagination) {
            currentPage = pagination.page;
            totalPages = pagination.pages;
            
            // 更新页面信息
            pageInfo.textContent = `第 ${currentPage} 页，共 ${totalPages} 页`;
            pageInfoBottom.textContent = `第 ${currentPage} 页，共 ${totalPages} 页`;
            
            // 更新按钮状态
            const disableFirstPrev = currentPage === 1;
            const disableNextLast = currentPage === totalPages;
            
            firstPageBtn.disabled = disableFirstPrev;
            prevPageBtn.disabled = disableFirstPrev;
            firstPageBottomBtn.disabled = disableFirstPrev;
            prevPageBottomBtn.disabled = disableFirstPrev;
            
            nextPageBtn.disabled = disableNextLast;
            lastPageBtn.disabled = disableNextLast;
            nextPageBottomBtn.disabled = disableNextLast;
            lastPageBottomBtn.disabled = disableNextLast;
        }
        
        // 开始状态轮询
        function startStatusPolling() {
            statusInterval = setInterval(updateStatus, 1000);
        }
        
        // 开始视频数据轮询
        function startVideosPolling() {
            videosInterval = setInterval(loadVideosData, 3000);
        }
        
        // 更新状态
        function updateStatus() {
            fetch('/api/status')
                .then(response => response.json())
                .then(data => {
                    statusText.textContent = `状态: ${data.status}`;
                    messageText.textContent = `消息: ${data.message}`;
                    validVidsText.textContent = `有效VID数: ${data.valid_vids_count}`;
                    downloadedVideosText.textContent = `已下载视频: ${data.videos_count}`;
                    
                    // 显示moviepy状态
                    if (data.moviepy_available) {
                        moviepyStatus.textContent = 'GIF预览: 可用';
                        moviepyStatus.style.color = '#27ae60';
                    } else {
                        moviepyStatus.textContent = 'GIF预览: 不可用 (需要安装moviepy)';
                        moviepyStatus.style.color = '#e74c3c';
                    }
                    
                    progressFill.style.width = `${data.progress}%`;
                    progressText.textContent = `${data.progress}%`;
                    
                    // 更新按钮状态
                    updateButtonStates(data.status);
                    
                    // 更新扫描结果
                    updateResultsList(scanResultsList, data.scan_results, 'scan');
                    
                    // 更新下载结果
                    updateResultsList(downloadResultsList, data.download_results, 'download');
                })
                .catch(error => {
                    console.error('获取状态失败:', error);
                });
        }
        
        // 加载视频数据
        function loadVideosData() {
            const url = `/api/videos?page=${currentPage}&per_page=${perPage}&view_type=${currentView}`;
            
            fetch(url)
                .then(response => response.json())
                .then(data => {
                    // 更新分页信息
                    updatePaginationControls(data.pagination);
                    
                    // 更新视频视图
                    updateVideoViews(data.videos);
                })
                .catch(error => {
                    console.error('获取视频数据失败:', error);
                });
        }
        
        // 更新按钮状态
        function updateButtonStates(status) {
            const isScanning = status === '扫描中';
            const isDownloading = status === '下载中';
            
            // 扫描按钮
            scanBtn.disabled = isScanning || isDownloading;
            stopScanBtn.disabled = !isScanning;
            
            // 下载按钮
            downloadBtn.disabled = isScanning || isDownloading || status === '空闲';
            stopDownloadBtn.disabled = !isDownloading;
        }
        
        // 更新结果列表
        function updateResultsList(element, results, type) {
            if (!results || results.length === 0) {
                element.innerHTML = '<div class="result-item">暂无结果</div>';
                return;
            }
            
            element.innerHTML = '';
            results.forEach(result => {
                const item = document.createElement('div');
                let statusClass = '';
                
                if (type === 'scan') {
                    item.textContent = `VID: ${result.vid} - 类型: ${result.type} - 状态: ${result.status}`;
                    
                    if (result.status === '有效') {
                        statusClass = 'success';
                    } else if (result.status.includes('错误')) {
                        statusClass = 'error';
                    }
                } else if (type === 'download') {
                    item.textContent = `VID: ${result.vid} - 状态: ${result.status} - ${result.message}`;
                    
                    if (result.status === '成功') {
                        statusClass = 'success';
                    } else if (result.status === '失败' || result.status === '错误') {
                        statusClass = 'error';
                    } else if (result.status === '警告') {
                        statusClass = 'warning';
                    }
                }
                
                item.className = `result-item ${statusClass}`;
                element.appendChild(item);
            });
        }
        
        // 更新视频视图
        function updateVideoViews(videos) {
            if (!videos || videos.length === 0) {
                const emptyMsg = '<div class="video-card" style="grid-column: 1 / -1; text-align: center; padding: 40px;">暂无视频</div>';
                videoGrid.innerHTML = emptyMsg;
                videoList.innerHTML = '<div class="list-item" style="justify-content: center;">暂无视频</div>';
                gifGrid.innerHTML = emptyMsg;
                return;
            }
            
            // 更新九宫格视图
            updateGridView(videos);
            
            // 更新列表视图
            updateListView(videos);
            
            // 更新GIF视图
            updateGifView(videos);
        }
        
        // 更新九宫格视图
        function updateGridView(videos) {
            videoGrid.innerHTML = '';
            
            videos.forEach(video => {
                const card = document.createElement('div');
                card.className = 'video-card';
                
                // 检查缩略图质量
                const thumbnailQuality = video.previews.thumbnail_quality;
                const isLowQuality = thumbnailQuality && thumbnailQuality.score < 30;
                
                // 低质量标记
                if (isLowQuality) {
                    const qualityBadge = document.createElement('div');
                    qualityBadge.className = 'quality-badge';
                    qualityBadge.textContent = '低质量';
                    card.appendChild(qualityBadge);
                }
                
                // 播放按钮
                const playBtn = document.createElement('button');
                playBtn.className = 'play-btn';
                playBtn.innerHTML = '▶';
                playBtn.title = '播放视频';
                playBtn.onclick = (e) => {
                    e.stopPropagation();
                    playVideo(video);
                };
                card.appendChild(playBtn);
                
                // 预览图片
                const preview = document.createElement('img');
                preview.className = 'video-preview';
                if (video.previews.thumbnail) {
                    preview.src = `data:image/jpeg;base64,${video.previews.thumbnail}`;
                } else {
                    preview.src = 'data:image/svg+xml;base64,PHN2ZyB3aWR0aD0iMjAwIiBoZWlnaHQ9IjE1MCIgeG1sbnM9Imh0dHA6Ly93d3cudzMub3JnLzIwMDAvc3ZnIj48cmVjdCB3aWR0aD0iMTAwJSIgaGVpZ2h0PSIxMDAlIiBmaWxsPSIjZjh mOWZhIi8+PHRleHQgeD0iNTAlIiB5PSI1MCUiIGZvbnQtZmFtaWx5PSJBcmlhbCwgc2Fucy1zZXJpZiIgZm9udC1zaXplPSIxNCIgZmlsbD0iIzk5OSIgdGV4dC1hbmNob3I9Im1pZGRsZSIgZHk9Ii4zZW0iPuWbvueJh+WbvueJhzwvdGV4dD48L3N2Zz4=';
                }
                preview.alt = `VID ${video.vid}`;
                preview.onclick = () => showSnapshots(video);
                
                // 视频信息
                const info = document.createElement('div');
                info.className = 'video-info';
                
                const vid = document.createElement('div');
                vid.className = 'video-vid';
                vid.textContent = `VID: ${video.vid}`;
                
                const details = document.createElement('div');
                details.className = 'video-details';
                details.textContent = `格式: ${video.format}, 大小: ${(video.file_size / 1024 / 1024).toFixed(2)}MB`;
                
                // 标签
                const tags = document.createElement('div');
                tags.className = 'video-tags';
                
                if (video.tags.includes('favorite')) {
                    const favTag = document.createElement('span');
                    favTag.className = 'tag favorite';
                    favTag.textContent = '收藏';
                    tags.appendChild(favTag);
                }
                
                if (video.tags.includes('watch_later')) {
                    const watchTag = document.createElement('span');
                    watchTag.className = 'tag watch-later';
                    watchTag.textContent = '稍后观看';
                    tags.appendChild(watchTag);
                }
                
                if (isLowQuality) {
                    const qualityTag = document.createElement('span');
                    qualityTag.className = 'tag low-quality';
                    qualityTag.textContent = '低质量预览';
                    tags.appendChild(qualityTag);
                }
                
                // 评分
                const rating = document.createElement('div');
                rating.className = 'rating-stars';
                for (let i = 1; i <= 5; i++) {
                    const star = document.createElement('span');
                    star.className = `star ${i <= video.rating ? 'active' : ''}`;
                    star.textContent = '★';
                    star.onclick = () => rateVideo(video.vid, i);
                    rating.appendChild(star);
                }
                
                // 操作按钮
                const actions = document.createElement('div');
                actions.className = 'video-actions';
                
                const favBtn = document.createElement('button');
                favBtn.className = `action-btn ${video.tags.includes('favorite') ? 'active' : ''}`;
                favBtn.textContent = video.tags.includes('favorite') ? '取消收藏' : '收藏';
                favBtn.onclick = () => toggleFavorite(video.vid);
                
                const watchBtn = document.createElement('button');
                watchBtn.className = `action-btn ${video.tags.includes('watch_later') ? 'active' : ''}`;
                watchBtn.textContent = video.tags.includes('watch_later') ? '取消标记' : '稍后观看';
                watchBtn.onclick = () => toggleWatchLater(video.vid);
                
                const snapBtn = document.createElement('button');
                snapBtn.className = 'action-btn';
                snapBtn.textContent = '查看快照';
                snapBtn.onclick = () => showSnapshots(video);
                
                actions.appendChild(favBtn);
                actions.appendChild(watchBtn);
                actions.appendChild(snapBtn);
                
                // 组装卡片
                info.appendChild(vid);
                info.appendChild(details);
                info.appendChild(tags);
                info.appendChild(rating);
                info.appendChild(actions);
                
                card.appendChild(preview);
                card.appendChild(info);
                
                videoGrid.appendChild(card);
            });
        }
        
        // 更新列表视图
        function updateListView(videos) {
            videoList.innerHTML = '';
            
            videos.forEach(video => {
                const item = document.createElement('div');
                item.className = 'list-item';
                
                // 检查缩略图质量
                const thumbnailQuality = video.previews.thumbnail_quality;
                const isLowQuality = thumbnailQuality && thumbnailQuality.score < 30;
                
                // 低质量标记
                if (isLowQuality) {
                    const qualityBadge = document.createElement('div');
                    qualityBadge.className = 'quality-badge';
                    qualityBadge.textContent = '低质量';
                    item.appendChild(qualityBadge);
                }
                
                // 播放按钮
                const playBtn = document.createElement('button');
                playBtn.className = 'play-btn';
                playBtn.innerHTML = '▶';
                playBtn.title = '播放视频';
                playBtn.onclick = (e) => {
                    e.stopPropagation();
                    playVideo(video);
                };
                item.appendChild(playBtn);
                
                // 预览图片
                const preview = document.createElement('img');
                preview.className = 'list-preview';
                if (video.previews.thumbnail) {
                    preview.src = `data:image/jpeg;base64,${video.previews.thumbnail}`;
                } else {
                    preview.src = 'data:image/svg+xml;base64,PHN2ZyB3aWR0aD0iMjAwIiBoZWlnaHQ9IjE1MCIgeG1sbnM9Imh0dHA6Ly93d3cudzMub3JnLzIwMDAvc3ZnIj48cmVjdCB3aWR0aD0iMTAwJSIgaGVpZ2h0PSIxMDAlIiBmaWxsPSIjZjhmOWZhIi8+PHRleHQgeD0iNTAlIiB5PSI1MCUiIGZvbnQtZmFtaWx5PSJBcmlhbCwgc2Fucy1zZXJpZiIgZm9udC1zaXplPSIxNCIgZmlsbD0iIzk5OSIgdGV4dC1hbmNob3I9Im1pZGRsZSIgZHk9Ii4zZW0iPuWbvueJh+WbvueJhzwvdGV4dD48L3N2Zz4=';
                }
                preview.alt = `VID ${video.vid}`;
                
                // 信息区域
                const info = document.createElement('div');
                info.className = 'list-info';
                
                const vid = document.createElement('div');
                vid.className = 'video-vid';
                vid.textContent = `VID: ${video.vid}`;
                
                const details = document.createElement('div');
                details.className = 'video-details';
                details.textContent = `格式: ${video.format}, 大小: ${(video.file_size / 1024 / 1024).toFixed(2)}MB`;
                
                // 标签
                const tags = document.createElement('div');
                tags.className = 'video-tags';
                
                if (video.tags.includes('favorite')) {
                    const favTag = document.createElement('span');
                    favTag.className = 'tag favorite';
                    favTag.textContent = '收藏';
                    tags.appendChild(favTag);
                }
                
                if (video.tags.includes('watch_later')) {
                    const watchTag = document.createElement('span');
                    watchTag.className = 'tag watch-later';
                    watchTag.textContent = '稍后观看';
                    tags.appendChild(watchTag);
                }
                
                if (isLowQuality) {
                    const qualityTag = document.createElement('span');
                    qualityTag.className = 'tag low-quality';
                    qualityTag.textContent = '低质量预览';
                    tags.appendChild(qualityTag);
                }
                
                info.appendChild(vid);
                info.appendChild(details);
                info.appendChild(tags);
                
                // 操作按钮
                const actions = document.createElement('div');
                actions.className = 'list-actions';
                
                const favBtn = document.createElement('button');
                favBtn.className = `action-btn ${video.tags.includes('favorite') ? 'active' : ''}`;
                favBtn.textContent = video.tags.includes('favorite') ? '取消收藏' : '收藏';
                favBtn.onclick = () => toggleFavorite(video.vid);
                
                const watchBtn = document.createElement('button');
                watchBtn.className = `action-btn ${video.tags.includes('watch_later') ? 'active' : ''}`;
                watchBtn.textContent = video.tags.includes('watch_later') ? '取消标记' : '稍后观看';
                watchBtn.onclick = () => toggleWatchLater(video.vid);
                
                const snapBtn = document.createElement('button');
                snapBtn.className = 'action-btn';
                snapBtn.textContent = '查看快照';
                snapBtn.onclick = () => showSnapshots(video);
                
                const playListBtn = document.createElement('button');
                playListBtn.className = 'action-btn';
                playListBtn.textContent = '播放视频';
                playListBtn.onclick = () => playVideo(video);
                
                actions.appendChild(favBtn);
                actions.appendChild(watchBtn);
                actions.appendChild(snapBtn);
                actions.appendChild(playListBtn);
                
                item.appendChild(preview);
                item.appendChild(info);
                item.appendChild(actions);
                
                videoList.appendChild(item);
            });
        }
        
        // 更新GIF视图
        function updateGifView(videos) {
            gifGrid.innerHTML = '';
            
            videos.forEach(video => {
                if (video.previews.gif) {
                    const card = document.createElement('div');
                    card.className = 'video-card';
                    
                    // GIF预览
                    const gif = document.createElement('img');
                    gif.className = 'video-preview';
                    gif.src = `data:image/gif;base64,${video.previews.gif}`;
                    gif.alt = `VID ${video.vid} GIF`;
                    
                    // 视频信息
                    const info = document.createElement('div');
                    info.className = 'video-info';
                    
                    const vid = document.createElement('div');
                    vid.className = 'video-vid';
                    vid.textContent = `VID: ${video.vid}`;
                    
                    const details = document.createElement('div');
                    details.className = 'video-details';
                    details.textContent = `格式: ${video.format}, 大小: ${(video.file_size / 1024 / 1024).toFixed(2)}MB`;
                    
                    info.appendChild(vid);
                    info.appendChild(details);
                    
                    card.appendChild(gif);
                    card.appendChild(info);
                    
                    gifGrid.appendChild(card);
                }
            });
            
            if (gifGrid.children.length === 0) {
                gifGrid.innerHTML = '<div class="video-card" style="grid-column: 1 / -1; text-align: center; padding: 40px;">暂无GIF预览</div>';
            }
        }
        
        // 显示快照
        function showSnapshots(video) {
            currentSnapshots = video.previews.snapshots || [];
            snapshotsGrid.innerHTML = '';
            
            if (currentSnapshots.length === 0) {
                snapshotsGrid.innerHTML = '<div style="grid-column: 1 / -1; text-align: center; padding: 20px;">暂无快照</div>';
            } else {
                currentSnapshots.forEach(snapshot => {
                    const img = document.createElement('img');
                    img.className = 'snapshot-img';
                    img.src = `data:image/jpeg;base64,${snapshot}`;
                    snapshotsGrid.appendChild(img);
                });
            }
            
            snapshotModal.style.display = 'flex';
        }
        
        // 播放视频
        function playVideo(video) {
            // 清理之前的播放器
            if (flvPlayer) {
                flvPlayer.destroy();
                flvPlayer = null;
            }
            videoPlayer.style.display = 'none';
            flvPlayerContainer.innerHTML = '';
            
            const videoUrl = `/videos/${video.vid}.${video.format}`;
            
            // 设置视频信息
            videoModalTitle.textContent = `视频播放 - VID: ${video.vid}`;
            videoModalDetails.textContent = `格式: ${video.format} | 大小: ${(video.file_size / 1024 / 1024).toFixed(2)}MB`;
            videoModalPath.textContent = `路径: ${video.file_path}`;
            
            // 显示模态框
            videoModal.style.display = 'flex';
            
            // 根据格式选择播放器
            if (video.format === 'flv' && flvjs.isSupported()) {
                // 使用flv.js播放FLV格式
                const flvVideo = document.createElement('video');
                flvVideo.controls = true;
                flvVideo.style.width = '100%';
                flvVideo.style.height = 'auto';
                flvVideo.style.maxHeight = '80vh';
                flvPlayerContainer.appendChild(flvVideo);
                
                flvPlayer = flvjs.createPlayer({
                    type: 'flv',
                    url: videoUrl
                });
                flvPlayer.attachMediaElement(flvVideo);
                flvPlayer.load();
                flvPlayer.play().catch(e => {
                    console.error('flv.js播放失败:', e);
                    alert('FLV视频播放失败: ' + e.message);
                });
            } else {
                // 使用普通video标签播放其他格式
                videoPlayer.style.display = 'block';
                videoPlayer.src = videoUrl;
                videoPlayer.play().catch(e => {
                    console.error('视频播放失败:', e);
                    alert('视频播放失败: ' + e.message);
                });
            }
        }
        
        // 关闭快照模态框
        function closeSnapshotModal() {
            snapshotModal.style.display = 'none';
        }
        
        // 关闭视频模态框
        function closeVideoModal() {
            videoModal.style.display = 'none';
            if (flvPlayer) {
                flvPlayer.pause();
                flvPlayer.destroy();
                flvPlayer = null;
            }
            videoPlayer.pause();
            videoPlayer.src = '';
            flvPlayerContainer.innerHTML = '';
        }
        
        // 标记视频为收藏
        function toggleFavorite(vid) {
            fetch('/api/video/mark', {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/json'
                },
                body: JSON.stringify({
                    vid: vid,
                    action: 'favorite'
                })
            })
            .then(response => response.json())
            .then(data => {
                if (data.success) {
                    // 重新加载视频数据
                    loadVideosData();
                } else {
                    alert('操作失败: ' + data.message);
                }
            })
            .catch(error => {
                console.error('标记失败:', error);
                alert('标记失败');
            });
        }
        
        // 标记视频为稍后观看
        function toggleWatchLater(vid) {
            fetch('/api/video/mark', {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/json'
                },
                body: JSON.stringify({
                    vid: vid,
                    action: 'watch_later'
                })
            })
            .then(response => response.json())
            .then(data => {
                if (data.success) {
                    // 重新加载视频数据
                    loadVideosData();
                } else {
                    alert('操作失败: ' + data.message);
                }
            })
            .catch(error => {
                console.error('标记失败:', error);
                alert('标记失败');
            });
        }
        
        // 评分视频
        function rateVideo(vid, rating) {
            fetch('/api/video/mark', {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/json'
                },
                body: JSON.stringify({
                    vid: vid,
                    action: 'rate',
                    value: rating
                })
            })
            .then(response => response.json())
            .then(data => {
                if (!data.success) {
                    alert('评分失败: ' + data.message);
                }
            })
            .catch(error => {
                console.error('评分失败:', error);
                alert('评分失败');
            });
        }
        
        // 加载设置
        function loadSettings() {
            fetch('/api/settings')
                .then(response => response.json())
                .then(settings => {
                    // 运行模式
                    document.getElementById('run_mode').value = settings.run_mode;
                    
                    // 异常视频检测API
                    document.getElementById('other_check_api').value = settings.other_check_api;
                    
                    // 文件格式筛选
                    const formatContainer = document.getElementById('format_filter');
                    formatContainer.innerHTML = '';
                    
                    settings.supported_formats.forEach(format => {
                        const checkboxItem = document.createElement('div');
                        checkboxItem.className = 'checkbox-item';
                        
                        const checkbox = document.createElement('input');
                        checkbox.type = 'checkbox';
                        checkbox.id = `format_${format}`;
                        checkbox.checked = settings.selected_formats.includes(format);
                        checkbox.value = format;
                        
                        const label = document.createElement('label');
                        label.htmlFor = `format_${format}`;
                        label.textContent = format.toUpperCase();
                        
                        checkboxItem.appendChild(checkbox);
                        checkboxItem.appendChild(label);
                        formatContainer.appendChild(checkboxItem);
                    });
                    
                    // 视频类型过滤
                    const typeContainer = document.getElementById('video_type_filter');
                    typeContainer.innerHTML = '';
                    
                    for (const [type, enabled] of Object.entries(settings.video_type_filter)) {
                        const checkboxItem = document.createElement('div');
                        checkboxItem.className = 'checkbox-item';
                        
                        const checkbox = document.createElement('input');
                        checkbox.type = 'checkbox';
                        checkbox.id = `filter_${type}`;
                        checkbox.checked = enabled;
                        checkbox.value = type;
                        
                        const label = document.createElement('label');
                        label.htmlFor = `filter_${type}`;
                        label.textContent = type.replace('_', ' ');
                        
                        checkboxItem.appendChild(checkbox);
                        checkboxItem.appendChild(label);
                        typeContainer.appendChild(checkboxItem);
                    }
                    
                    // 预览设置
                    document.getElementById('gif_duration').value = settings.preview_settings.gif_duration;
                    document.getElementById('gif_fps').value = settings.preview_settings.gif_fps;
                    document.getElementById('gif_max_size').value = settings.preview_settings.gif_max_size;
                    document.getElementById('snapshot_count').value = settings.preview_settings.snapshot_count;
                    document.getElementById('preview_quality').value = settings.preview_settings.preview_quality;
                    document.getElementById('thumbnail_check_enabled').checked = settings.preview_settings.thumbnail_check_enabled;
                    document.getElementById('min_thumbnail_quality').value = settings.preview_settings.min_thumbnail_quality;
                    document.getElementById('gif_use_opencv').checked = settings.preview_settings.gif_use_opencv;
                })
                .catch(error => {
                    console.error('加载设置失败:', error);
                });
        }
        
        // 保存设置
        function saveSettings() {
            const runMode = document.getElementById('run_mode').value;
            const otherCheckApi = document.getElementById('other_check_api').value;
            
            const selectedFormats = [];
            document.querySelectorAll('#format_filter input[type="checkbox"]').forEach(checkbox => {
                if (checkbox.checked) {
                    selectedFormats.push(checkbox.value);
                }
            });
            
            const videoTypeFilter = {};
            document.querySelectorAll('#video_type_filter input[type="checkbox"]').forEach(checkbox => {
                videoTypeFilter[checkbox.value] = checkbox.checked;
            });
            
            const previewSettings = {
                gif_duration: parseInt(document.getElementById('gif_duration').value),
                gif_fps: parseInt(document.getElementById('gif_fps').value),
                gif_max_size: parseInt(document.getElementById('gif_max_size').value),
                snapshot_count: parseInt(document.getElementById('snapshot_count').value),
                preview_quality: parseInt(document.getElementById('preview_quality').value),
                thumbnail_check_enabled: document.getElementById('thumbnail_check_enabled').checked,
                min_thumbnail_quality: parseInt(document.getElementById('min_thumbnail_quality').value),
                gif_use_opencv: document.getElementById('gif_use_opencv').checked
            };
            
            const settings = {
                run_mode: runMode,
                other_check_api: otherCheckApi,
                selected_formats: selectedFormats,
                video_type_filter: videoTypeFilter,
                preview_settings: previewSettings
            };
            
            fetch('/api/settings', {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/json'
                },
                body: JSON.stringify(settings)
            })
            .then(response => response.json())
            .then(data => {
                alert(data.message || '设置已保存');
            })
            .catch(error => {
                console.error('保存设置失败:', error);
                alert('保存设置失败');
            });
        }
        
        // 开始扫描
        function startScan() {
            const startVid = parseInt(document.getElementById('start_vid').value);
            const endVid = parseInt(document.getElementById('end_vid').value);
            const scanThreads = parseInt(document.getElementById('scan_threads').value);
            
            if (startVid >= endVid) {
                alert('起始VID必须小于结束VID');
                return;
            }
            
            if (endVid - startVid > 10000) {
                if (!confirm(`警告: 范围包含 ${endVid - startVid + 1} 个VID，可能需要很长时间。继续?`)) {
                    return;
                }
            }
            
            scanBtn.disabled = true;
            scanBtn.textContent = '扫描中...';
            
            fetch('/api/scan', {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/json'
                },
                body: JSON.stringify({
                    start_vid: startVid,
                    end_vid: endVid,
                    max_threads: scanThreads
                })
            })
            .then(response => response.json())
            .then(data => {
                if (!data.success) {
                    alert(data.message);
                    scanBtn.disabled = false;
                    scanBtn.textContent = '开始扫描';
                }
            })
            .catch(error => {
                console.error('开始扫描失败:', error);
                alert('开始扫描失败');
                scanBtn.disabled = false;
                scanBtn.textContent = '开始扫描';
            });
        }
        
        // 停止扫描
        function stopScan() {
            fetch('/api/stop_scan', {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/json'
                }
            })
            .then(response => response.json())
            .then(data => {
                alert(data.message);
            })
            .catch(error => {
                console.error('停止扫描失败:', error);
                alert('停止扫描失败');
            });
        }
        
        // 开始下载
        function startDownload() {
            const downloadThreads = parseInt(document.getElementById('download_threads').value);
            
            downloadBtn.disabled = true;
            downloadBtn.textContent = '下载中...';
            
            fetch('/api/download', {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/json'
                },
                body: JSON.stringify({
                    max_threads: downloadThreads
                })
            })
            .then(response => response.json())
            .then(data => {
                if (!data.success) {
                    alert(data.message);
                    downloadBtn.disabled = false;
                    downloadBtn.textContent = '开始下载';
                }
            })
            .catch(error => {
                console.error('开始下载失败:', error);
                alert('开始下载失败');
                downloadBtn.disabled = false;
                downloadBtn.textContent = '开始下载';
            });
        }
        
        // 停止下载
        function stopDownload() {
            fetch('/api/stop_download', {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/json'
                }
            })
            .then(response => response.json())
            .then(data => {
                alert(data.message);
            })
            .catch(error => {
                console.error('停止下载失败:', error);
                alert('停止下载失败');
            });
        }
        
        // 导出VID列表
        function exportVids() {
            window.open('/api/export', '_blank');
        }
        
        // 清除缓存
        function clearCache() {
            if (!confirm('确定要清除所有下载的视频文件和预览吗？此操作不可逆！')) {
                return;
            }
            
            fetch('/api/clear_cache', {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/json'
                }
            })
            .then(response => response.json())
            .then(data => {
                alert(data.message);
                // 清除后重新加载视频数据
                loadVideosData();
            })
            .catch(error => {
                console.error('清除缓存失败:', error);
                alert('清除缓存失败');
            });
        }
        
        // 重置状态
        function resetStatus() {
            fetch('/api/reset')
                .then(response => response.json())
                .then(data => {
                    alert(data.message);
                })
                .catch(error => {
                    console.error('重置状态失败:', error);
                });
        }
        
        // 事件监听
        scanBtn.addEventListener('click', startScan);
        stopScanBtn.addEventListener('click', stopScan);
        downloadBtn.addEventListener('click', startDownload);
        stopDownloadBtn.addEventListener('click', stopDownload);
        exportBtn.addEventListener('click', exportVids);
        clearCacheBtn.addEventListener('click', clearCache);
        saveSettingsBtn.addEventListener('click', saveSettings);
        resetBtn.addEventListener('click', resetStatus);
        
        // 点击模态框外部关闭
        snapshotModal.addEventListener('click', function(e) {
            if (e.target === this) {
                closeSnapshotModal();
            }
        });
        
        videoModal.addEventListener('click', function(e) {
            if (e.target === this) {
                closeVideoModal();
            }
        });
        
        // ESC键关闭模态框
        document.addEventListener('keydown', function(e) {
            if (e.key === 'Escape') {
                closeSnapshotModal();
                closeVideoModal();
            }
        });
    </script>
</body>
</html>''')
    
    # 启动Flask应用
    app.run(debug=True, host='0.0.0.0', port=5000)
