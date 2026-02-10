import requests
import time
import os
import sqlite3
import aiohttp
import asyncio
import json
from flask import Flask, request, jsonify, render_template_string, send_file
from concurrent.futures import ThreadPoolExecutor, as_completed
from collections import defaultdict
import traceback
from urllib.parse import quote

app = Flask(__name__)
executor = ThreadPoolExecutor(max_workers=50)
scan_tasks = {}
download_tasks = {}
task_counter = 0
download_counter = 0

# ==================== 下载目录配置 ====================
DOWNLOAD_DIR = "./downloads"
if not os.path.exists(DOWNLOAD_DIR):
    os.makedirs(DOWNLOAD_DIR)

# ==================== 第一部分：原有扫描功能（保持不变）====================

def check_single_video(v_id):
    result = {
        'video_id': v_id,
        'cover_status': '未知',
        'cover_url': '',
        'video_status': '未知',
        'detail': ''
    }
    
    # 构造封面URL
    vid_str = str(v_id)
    if len(vid_str) >= 9:
        part1 = vid_str[:3]
        part2 = vid_str[3:6]
        part3 = vid_str[-3:]
        cover_url = f"https://p2.ivideo.sina.com.cn/video/{part1}/{part2}/{part3}/{v_id}.jpg"
    else:
        cover_url = f"https://p2.ivideo.sina.com.cn/video/vid/eo_/id/{v_id}.jpg"
    
    result['cover_url'] = cover_url
    
    # 检查封面图
    try:
        resp = requests.head(cover_url, timeout=3, allow_redirects=True)
        if resp.status_code == 200:
            content_type = resp.headers.get('Content-Type', '')
            if 'image' in content_type:
                result['cover_status'] = '有封面'
            else:
                result['cover_status'] = '有文件但非图片'
        elif resp.status_code == 404:
            result['cover_status'] = '无封面'
        else:
            result['cover_status'] = f'HTTP状态码 {resp.status_code}'
    except requests.exceptions.RequestException:
        result['cover_status'] = '封面请求失败'
    
    # 检查视频信息
    info_url = "http://api.ivideo.sina.com.cn/public/video/play"
    params = {
        'appname': 'sinaplayer_pc', 'tags': 'sinaplayer_pc', 'applt': 'web',
        'appver': 'V11220.210521.03', 'player': 'all', 'video_id': v_id
    }
    
    try:
        resp = requests.get(info_url, params=params, timeout=5)
        data = resp.json()
        
        if data.get('code') == 0:
            error_msg = data.get('Message', '') or data.get('errorMessage', '')
            if any(keyword in error_msg for keyword in ['视频已删除', 'deleted', 'exception']):
                result['video_status'] = '伪分段'
                result['detail'] = f'伪分段: {error_msg[:80]}'
            else:
                result['video_status'] = '其他错误'
                result['detail'] = f'其他错误: {error_msg[:80]}'
        else:
            result['video_status'] = '正常或未知状态'
            result['detail'] = '视频信息获取成功'
            
    except requests.exceptions.RequestException as e:
        result['video_status'] = '信息请求失败'
        result['detail'] = f'网络错误: {str(e)[:50]}'
    except Exception as e:
        result['video_status'] = '信息解析失败'
        result['detail'] = f'解析错误: {str(e)[:50]}'
    
    return result

# ==================== 第二部分：完全采用 d.py 的反查验证策略 ====================

DB_BASE_PATH = "./"

# d.py 中的数据库范围定义（保持一致）
DB_FILE_RANGES = {
    'sina_00.db': (1, 10_000_000),
    'sina_01.db': (10_000_000, 20_000_000),
    'sina_02.db': (20_000_000, 30_000_000),
    'sina_03.db': (30_000_000, 40_000_000),
    'sina_04.db': (40_000_000, 50_000_000),
    'sina_05.db': (50_000_000, 60_000_000),
    'sina_06.db': (60_000_000, 70_000_000),
    'sina_07.db': (70_000_000, 80_000_000),
    'sina_08.db': (80_000_000, 90_000_000),
    'sina_09.db': (90_000_000, 100_000_000),
    'sina_10.db': (100_000_000, 110_000_000),
    'sina_11.db': (110_000_000, 120_000_000),
    'sina_12.db': (120_000_000, 130_000_000),
    'sina_13.db': (130_000_000, 140_000_000),
}

def lookup_vid_in_db(video_id, db_filename):
    """
    完全按照 d.py 的实现：在单个数据库文件中查找 video_id 记录
    """
    db_path = os.path.join(DB_BASE_PATH, db_filename)
    if not os.path.exists(db_path):
        return None

    try:
        conn = sqlite3.connect(db_path)
        # 使用字典光标，方便通过列名访问
        conn.row_factory = sqlite3.Row
        cursor = conn.cursor()

        # 关键查询：根据 video_id 查找记录
        cursor.execute(
            "SELECT vid, video_id, title, length, description, create_time FROM videos WHERE video_id = ?",
            (video_id,)
        )
        row = cursor.fetchone()
        conn.close()

        if row:
            # 将 sqlite3.Row 对象转换为字典
            result = dict(row)
            result['found_in_db'] = db_filename
            return result
        else:
            return None
    except sqlite3.Error as e:
        print(f"查询数据库 {db_filename} 时出错: {e}")
        return None
    except Exception as e:
        print(f"其他错误在查询数据库 {db_filename}: {e}")
        return None

def find_video_record(video_id):
    """
    完全按照 d.py 的查找策略：在所有 db 文件中搜索给定的 video_id
    """
    # 首先，尝试根据 video_id 的值猜测一个最有可能的 db 文件
    possible_files = []
    for db_file, (low, high) in DB_FILE_RANGES.items():
        if low <= video_id <= high:
            possible_files.insert(0, db_file)  # 最有可能的放前面
        else:
            possible_files.append(db_file)      # 其他的放后面

    # 依次查询
    for db_file in possible_files:
        record = lookup_vid_in_db(video_id, db_file)
        if record:
            return record

    return None

def check_cdn_flv(vid):
    """检查CDN上对应的 .flv 文件是否存在"""
    url = f"https://cdn.sinacloud.net/edge.v.iask.com/{vid}.flv"
    try:
        # 使用 HEAD 方法快速检查，避免下载大文件
        resp = requests.head(url, timeout=10, allow_redirects=True)
        return {
            'exists': resp.status_code == 200,
            'url': url,
            'http_status': resp.status_code,
            'content_length': resp.headers.get('Content-Length')
        }
    except requests.exceptions.RequestException as e:
        return {
            'exists': False,
            'url': url,
            'error': str(e)
        }

# ==================== 异步下载功能 ====================

async def download_single_file_async(session, url, filename, task_id, file_index):
    """异步下载单个文件"""
    try:
        async with session.get(url) as response:
            if response.status == 200:
                # 获取文件大小
                total_size = int(response.headers.get('content-length', 0))
                downloaded = 0
                
                # 分块下载
                with open(filename, 'wb') as f:
                    async for chunk in response.content.iter_chunked(8192):
                        if chunk:
                            f.write(chunk)
                            downloaded += len(chunk)
                            
                            # 更新进度
                            if total_size > 0:
                                progress = (downloaded / total_size) * 100
                                download_tasks[task_id]['files'][file_index]['progress'] = round(progress, 1)
                                download_tasks[task_id]['files'][file_index]['downloaded'] = downloaded
                                download_tasks[task_id]['files'][file_index]['total_size'] = total_size
                
                download_tasks[task_id]['files'][file_index]['status'] = 'completed'
                download_tasks[task_id]['files'][file_index]['progress'] = 100
                return True
            else:
                download_tasks[task_id]['files'][file_index]['status'] = f'failed: HTTP {response.status}'
                return False
    except Exception as e:
        download_tasks[task_id]['files'][file_index]['status'] = f'failed: {str(e)[:50]}'
        return False

async def download_files_async(task_id, urls, filenames):
    """异步下载多个文件"""
    connector = aiohttp.TCPConnector(limit=10)  # 限制并发连接数
    async with aiohttp.ClientSession(connector=connector) as session:
        tasks = []
        for i, (url, filename) in enumerate(zip(urls, filenames)):
            task = asyncio.create_task(download_single_file_async(session, url, filename, task_id, i))
            tasks.append(task)
        
        results = await asyncio.gather(*tasks)
        return results

def run_async_download(task_id, urls, filenames):
    """运行异步下载任务"""
    loop = asyncio.new_event_loop()
    asyncio.set_event_loop(loop)
    try:
        results = loop.run_until_complete(download_files_async(task_id, urls, filenames))
        download_tasks[task_id]['status'] = 'completed'
        download_tasks[task_id]['completed_time'] = time.time()
        download_tasks[task_id]['success_count'] = sum(results)
        download_tasks[task_id]['failed_count'] = len(results) - sum(results)
    except Exception as e:
        download_tasks[task_id]['status'] = f'failed: {str(e)}'
    finally:
        loop.close()

# ==================== 第三部分：API 路由（整合所有功能）====================

# ---------- 原有扫描任务相关的API ----------
@app.route('/api/start_scan', methods=['POST'])
def start_scan():
    global task_counter
    
    data = request.get_json()
    if not data or 'start_video_id' not in data or 'radius' not in data:
        return jsonify({'code': 0, 'message': '缺少参数：请提供 start_video_id 和 radius'})
    
    try:
        start_id = int(data['start_video_id'])
        radius = int(data['radius'])
    except ValueError:
        return jsonify({'code': 0, 'message': '参数格式错误：start_video_id 和 radius 必须是整数'})
    
    min_id = start_id - radius
    max_id = start_id + radius
    video_ids_to_scan = list(range(min_id, max_id + 1))
    
    task_id = f'task_{task_counter}_{int(time.time())}'
    task_counter += 1
    
    scan_tasks[task_id] = {
        'task_id': task_id, 'start_video_id': start_id, 'radius': radius,
        'scan_range': (min_id, max_id), 'total_count': len(video_ids_to_scan),
        'scanned_count': 0, 'status': 'running', 'start_time': time.time(),
        'results': defaultdict(list), 'cover_stats': defaultdict(int),
        'pseudo_segments': []
    }
    
    def run_scan_task():
        task = scan_tasks[task_id]
        try:
            with ThreadPoolExecutor(max_workers=10) as pool:
                future_to_vid = {pool.submit(check_single_video, vid): vid for vid in video_ids_to_scan}
                
                for future in as_completed(future_to_vid):
                    video_result = future.result()
                    vid = video_result['video_id']
                    
                    task['scanned_count'] += 1
                    status = video_result['video_status']
                    task['results'][status].append(video_result)
                    task['cover_stats'][video_result['cover_status']] += 1
                    
                    if status == '伪分段':
                        task['pseudo_segments'].append(vid)
            
            task['status'] = 'completed'
            task['end_time'] = time.time()
            task['duration'] = round(task['end_time'] - task['start_time'], 2)
            
        except Exception as e:
            task['status'] = 'failed'
            task['error'] = str(e)
            print(f"扫描任务出错: {e}")
    
    import threading
    scan_thread = threading.Thread(target=run_scan_task)
    scan_thread.daemon = True
    scan_thread.start()
    
    return jsonify({
        'code': 1, 'message': '扫描任务已启动',
        'data': {
            'task_id': task_id, 'scan_range': f'{min_id} 到 {max_id}',
            'total_videos': len(video_ids_to_scan), 'start_video_id': start_id,
            'radius': radius, 'status_endpoint': f'/api/scan_status/{task_id}',
            'results_endpoint': f'/api/scan_results/{task_id}'
        }
    })

@app.route('/api/scan_status/<task_id>', methods=['GET'])
def get_scan_status(task_id):
    if task_id not in scan_tasks:
        return jsonify({'code': 0, 'message': '任务不存在'})
    
    task = scan_tasks[task_id]
    progress = 0
    if task['total_count'] > 0:
        progress = round(task['scanned_count'] / task['total_count'] * 100, 1)
    
    status_data = {
        'task_id': task_id, 'status': task['status'], 'progress': progress,
        'scanned': task['scanned_count'], 'total': task['total_count'],
        'scan_range': f"{task['scan_range'][0]} 到 {task['scan_range'][1]}",
        'pseudo_found': len(task['pseudo_segments']),
        'cover_stats': dict(task['cover_stats']),
        'start_time': time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(task['start_time']))
    }
    
    if task['status'] == 'completed':
        status_data['duration_seconds'] = task.get('duration')
    elif task['status'] == 'failed':
        status_data['error'] = task.get('error', '未知错误')
    
    return jsonify({'code': 1, 'message': '状态查询成功', 'data': status_data})

@app.route('/api/scan_results/<task_id>', methods=['GET'])
def get_scan_results(task_id):
    if task_id not in scan_tasks:
        return jsonify({'code': 0, 'message': '任务不存在'})
    
    task = scan_tasks[task_id]
    
    if task['status'] == 'running':
        return jsonify({
            'code': 1, 'message': '任务进行中，当前部分结果',
            'data': {
                'task_id': task_id, 'status': 'running',
                'progress': round(task['scanned_count'] / task['total_count'] * 100, 1),
                'pseudo_segments_so_far': task['pseudo_segments'][:50],
                'cover_stats_summary': dict(task['cover_stats']),
                'note': '任务完成后获取完整结果'
            }
        })
    
    return jsonify({
        'code': 1, 'message': '扫描任务完成',
        'data': {
            'task_id': task_id, 'status': 'completed',
            'scan_range': f"{task['scan_range'][0]} 到 {task['scan_range'][1]}",
            'total_scanned': task['total_count'], 'duration_seconds': task.get('duration'),
            'pseudo_segments': task['pseudo_segments'],
            'pseudo_count': len(task['pseudo_segments']),
            'cover_statistics': dict(task['cover_stats']),
            'results_summary': {status: len(items) for status, items in task['results'].items()},
            'sample_results': {
                status: [
                    {'video_id': item['video_id'], 'cover_status': item['cover_status'], 'detail': item['detail'][:60]}
                    for item in items[:3]
                ]
                for status, items in task['results'].items() if items
            }
        }
    })

# ---------- 新增的反查验证API（完全采用d.py策略）----------
@app.route('/api/reverse_check', methods=['POST'])
def reverse_check():
    """
    根据 video_id 查找完整信息并验证CDN
    """
    try:
        data = request.get_json()
        if not data or 'video_id' not in data:
            return jsonify({'code': 0, 'message': '缺少 video_id 参数'})
        
        try:
            video_id = int(data['video_id'])
        except ValueError:
            return jsonify({'code': 0, 'message': 'video_id 必须是整数'})
        
        # 使用 d.py 策略查找记录
        record = find_video_record(video_id)
        
        if not record:
            return jsonify({
                'code': 0,
                'message': f'未在任何数据库中找到 video_id: {video_id} 的记录',
                'suggestion': '请确认 video_id 是否正确，或检查数据库内容'
            })
        
        # 检查 CDN 上的 .flv 文件
        cdn_result = check_cdn_flv(record['vid'])
        
        # 整合结果
        result = {
            'code': 1,
            'message': '反查验证成功',
            'data': {
                'input_video_id': video_id,
                'found_vid': record['vid'],
                'database_record': {
                    'vid': record['vid'],
                    'video_id': record['video_id'],
                    'title': record.get('title'),
                    'length': record.get('length'),
                    'description': record.get('description'),
                    'create_time': record.get('create_time'),
                    'source_db': record.get('found_in_db', '未知')
                },
                'cdn_check': cdn_result,
                'verdict': '已确认的伪分段（CDN文件存在）' if cdn_result['exists'] else '信息伪分段（CDN文件缺失）'
            }
        }
        
        return jsonify(result)
    except Exception as e:
        print(f"reverse_check 错误: {e}")
        print(traceback.format_exc())
        return jsonify({'code': 0, 'message': f'服务器内部错误: {str(e)}'})

# ==================== 批量反查验证功能（无限制版本）====================

def batch_find_video_records(video_ids):
    """
    批量查找video_id记录，优化数据库查询
    """
    results = {}
    
    # 按数据库文件分组
    video_ids_by_db = defaultdict(list)
    
    for video_id in video_ids:
        # 找到可能的数据库文件
        for db_file, (low, high) in DB_FILE_RANGES.items():
            if low <= video_id <= high:
                video_ids_by_db[db_file].append(video_id)
                break
        else:
            # 如果没有找到匹配的数据库文件，添加到所有文件中查询
            for db_file in DB_FILE_RANGES:
                video_ids_by_db[db_file].append(video_id)
    
    # 并行查询每个数据库
    with ThreadPoolExecutor(max_workers=10) as db_executor:
        future_to_db = {
            db_executor.submit(batch_query_db, db_file, vids): db_file
            for db_file, vids in video_ids_by_db.items()
        }
        
        for future in as_completed(future_to_db):
            db_file = future_to_db[future]
            try:
                db_results = future.result(timeout=30)
                results.update(db_results)
            except Exception as e:
                print(f"批量查询数据库 {db_file} 失败: {e}")
    
    return results

def batch_query_db(db_filename, video_ids):
    """
    批量查询单个数据库
    """
    db_path = os.path.join(DB_BASE_PATH, db_filename)
    if not os.path.exists(db_path):
        return {}
    
    try:
        conn = sqlite3.connect(db_path)
        conn.row_factory = sqlite3.Row
        
        # 使用IN语句批量查询
        if not video_ids:
            return {}
        
        placeholders = ','.join(['?'] * len(video_ids))
        query = f"""
            SELECT vid, video_id, title, length, description, create_time 
            FROM videos 
            WHERE video_id IN ({placeholders})
        """
        
        cursor = conn.cursor()
        cursor.execute(query, video_ids)
        rows = cursor.fetchall()
        conn.close()
        
        results = {}
        for row in rows:
            record = dict(row)
            record['found_in_db'] = db_filename
            results[record['video_id']] = record
        
        return results
    except Exception as e:
        print(f"批量查询 {db_filename} 出错: {e}")
        return {}

def generate_summary(results):
    """生成摘要统计"""
    summary = {
        'total': len(results),
        'found_in_db': sum(1 for r in results if r.get('database_record')),
        'cdn_exists': sum(1 for r in results if r.get('cdn_check_result', {}).get('exists') == True),
        'cdn_missing': sum(1 for r in results if r.get('cdn_check_result', {}).get('exists') == False),
        'not_found': sum(1 for r in results if not r.get('database_record') and 'error' in r),
        'confirmed_pseudo': sum(1 for r in results if r.get('cdn_check_result', {}).get('exists') == True and r.get('database_record')),
        'info_pseudo': sum(1 for r in results if r.get('cdn_check_result', {}).get('exists') == False and r.get('database_record'))
    }
    return summary

@app.route('/api/batch_reverse_check', methods=['POST'])
def batch_reverse_check():
    """
    批量反查验证，无限制版本
    """
    try:
        data = request.get_json()
        if not data or 'video_ids' not in data or not isinstance(data['video_ids'], list):
            return jsonify({'code': 0, 'message': '缺少 video_ids 数组参数'})
        
        try:
            video_ids = [int(vid) for vid in data['video_ids']]
        except ValueError:
            return jsonify({'code': 0, 'message': 'video_ids 数组中的元素必须是整数'})
        
        # 性能警告，但不限制
        if len(video_ids) > 10000:
            print(f"警告：批量查询数量较大，共 {len(video_ids)} 个video_id")
        
        start_time = time.time()
        
        # 批量查询数据库记录
        print(f"开始批量查询数据库，共 {len(video_ids)} 条记录...")
        batch_records = batch_find_video_records(video_ids)
        print(f"数据库查询完成，找到 {len(batch_records)} 条记录")
        
        # 并行检查CDN
        cdn_results = {}
        cdn_check_vids = [record['vid'] for record in batch_records.values() if record and 'vid' in record]
        
        if cdn_check_vids:
            print(f"开始检查CDN，共 {len(cdn_check_vids)} 个vid需要检查...")
            with ThreadPoolExecutor(max_workers=30) as cdn_executor:
                future_to_vid = {
                    cdn_executor.submit(check_cdn_flv, vid): vid
                    for vid in cdn_check_vids
                }
                
                for future in as_completed(future_to_vid):
                    vid = future_to_vid[future]
                    try:
                        cdn_results[vid] = future.result(timeout=15)
                    except Exception as e:
                        cdn_results[vid] = {'exists': False, 'error': str(e)}
            print("CDN检查完成")
        
        # 整合结果
        processed_results = []
        for video_id in video_ids:
            record = batch_records.get(video_id)
            if record:
                cdn_result = cdn_results.get(record['vid'], {'exists': False})
                verdict = '已确认的伪分段（CDN文件存在）' if cdn_result.get('exists') else '信息伪分段（CDN文件缺失）'
                processed_results.append({
                    'input_video_id': video_id,
                    'database_record': record,
                    'cdn_check_result': cdn_result,
                    'verdict': verdict
                })
            else:
                processed_results.append({
                    'input_video_id': video_id,
                    'error': '数据库记录不存在',
                    'verdict': '未找到数据库记录'
                })
        
        # 生成摘要
        summary = generate_summary(processed_results)
        total_time = time.time() - start_time
        
        print(f"批量处理完成，共处理 {len(processed_results)} 条记录，耗时 {total_time:.2f} 秒")
        
        return jsonify({
            'code': 1,
            'message': f'批量处理完成，共 {len(processed_results)} 个结果',
            'data': {
                'summary': summary,
                'processing_time': round(total_time, 2),
                'results_count': len(processed_results),
                'detailed_results': processed_results[:1000],  # 只返回前1000个详细结果
                'note': '完整结果已处理完成，但前端只显示前1000条。如需完整数据，请导出。'
            }
        })
        
    except Exception as e:
        print(f"batch_reverse_check 错误: {e}")
        print(traceback.format_exc())
        return jsonify({'code': 0, 'message': f'服务器内部错误: {str(e)}'})

@app.route('/api/batch_reverse_check_fast', methods=['POST'])
def batch_reverse_check_fast():
    """
    快速批量反查验证，只检查数据库不检查CDN
    """
    try:
        data = request.get_json()
        if not data or 'video_ids' not in data or not isinstance(data['video_ids'], list):
            return jsonify({'code': 0, 'message': '缺少 video_ids 数组参数'})
        
        try:
            video_ids = [int(vid) for vid in data['video_ids']]
        except ValueError:
            return jsonify({'code': 0, 'message': 'video_ids 数组中的元素必须是整数'})
        
        start_time = time.time()
        
        # 批量查询数据库记录
        batch_records = batch_find_video_records(video_ids)
        
        # 生成结果
        processed_results = []
        for video_id in video_ids:
            record = batch_records.get(video_id)
            if record:
                processed_results.append({
                    'input_video_id': video_id,
                    'database_record': record,
                    'verdict': '数据库中找到记录'
                })
            else:
                processed_results.append({
                    'input_video_id': video_id,
                    'error': '数据库记录不存在',
                    'verdict': '未找到数据库记录'
                })
        
        total_time = time.time() - start_time
        
        return jsonify({
            'code': 1,
            'message': f'快速批量处理完成，共 {len(processed_results)} 个结果',
            'data': {
                'processing_time': round(total_time, 2),
                'found_count': len(batch_records),
                'not_found_count': len(video_ids) - len(batch_records),
                'detailed_results': processed_results[:500]  # 只返回前500个详细结果
            }
        })
        
    except Exception as e:
        print(f"batch_reverse_check_fast 错误: {e}")
        return jsonify({'code': 0, 'message': f'服务器内部错误: {str(e)}'})

# ==================== 修复的下载相关API ====================

@app.route('/api/start_download', methods=['POST'])
def start_download():
    """
    启动CDN文件下载任务
    """
    global download_counter
    
    try:
        data = request.get_json()
        if not data or 'items' not in data or not isinstance(data['items'], list):
            return jsonify({'code': 0, 'message': '缺少 items 数组参数'})
        
        items = data['items']
        if not items:
            return jsonify({'code': 0, 'message': 'items 数组为空'})
        
        print(f"接收到的items: {len(items)} 个")  # 调试信息
        
        # 过滤出CDN存在的项目
        valid_items = []
        for item in items:
            # 调试信息
            print(f"检查item: {item.get('input_video_id')}")
            
            # 安全地检查所有必需字段
            if not isinstance(item, dict):
                print(f"item 不是字典: {item}")
                continue
            
            # 检查数据库记录
            db_record = item.get('database_record')
            if not db_record:
                print(f"没有database_record: {item.get('input_video_id')}")
                continue
            
            # 检查vid
            vid = db_record.get('vid') if isinstance(db_record, dict) else None
            if not vid:
                print(f"没有vid: {item.get('input_video_id')}")
                continue
            
            # 检查CDN结果 - 兼容两种数据结构
            cdn_check = item.get('cdn_check') or item.get('cdn_check_result')
            if not cdn_check:
                print(f"没有cdn_check或cdn_check_result: {item.get('input_video_id')}")
                continue
            
            # 检查CDN是否存在
            if isinstance(cdn_check, dict) and cdn_check.get('exists'):
                # 检查URL
                url = cdn_check.get('url')
                if url:
                    # 确保数据结构统一
                    item['cdn_check_result'] = cdn_check
                    valid_items.append(item)
                    print(f"有效item: {item.get('input_video_id')}, vid: {vid}, url: {url}")
                else:
                    print(f"没有URL: {item.get('input_video_id')}")
            else:
                print(f"CDN不存在或格式错误: {item.get('input_video_id')}, cdn_check: {cdn_check}")
        
        if not valid_items:
            return jsonify({'code': 0, 'message': '没有找到CDN存在的文件'})
        
        print(f"有效items: {len(valid_items)} 个")  # 调试信息
        
        # 创建下载任务
        task_id = f'download_{download_counter}_{int(time.time())}'
        download_counter += 1
        
        # 准备下载文件信息
        files = []
        urls = []
        filenames = []
        
        for i, item in enumerate(valid_items):
            video_id = item.get('input_video_id')
            db_record = item.get('database_record', {})
            cdn_check = item.get('cdn_check') or item.get('cdn_check_result', {})
            
            # 安全地获取字段
            vid = db_record.get('vid') if isinstance(db_record, dict) else f'unknown_{video_id}'
            url = cdn_check.get('url') if isinstance(cdn_check, dict) else ''
            title = db_record.get('title', f'video_{video_id}') if isinstance(db_record, dict) else f'video_{video_id}'
            
            if not url:
                print(f"跳过无效URL: {video_id}")
                continue
            
            # 清理文件名
            try:
                # 移除非法字符
                safe_title = "".join([c for c in str(title) if c.isalnum() or c in (' ', '-', '_', '.')]).strip()
                if not safe_title:
                    safe_title = f'video_{video_id}'
                
                # 限制文件名长度
                if len(safe_title) > 100:
                    safe_title = safe_title[:100]
                
                # 创建文件名
                filename = os.path.join(DOWNLOAD_DIR, f"{safe_title}_{vid}.flv")
                
                # 避免重复文件名
                counter = 1
                original_filename = filename
                while os.path.exists(filename):
                    name, ext = os.path.splitext(original_filename)
                    filename = f"{name}_{counter}{ext}"
                    counter += 1
                
            except Exception as e:
                print(f"文件名处理错误 {video_id}: {e}")
                safe_title = f'video_{video_id}'
                filename = os.path.join(DOWNLOAD_DIR, f"{safe_title}_{vid}.flv")
            
            files.append({
                'index': i,
                'video_id': video_id,
                'vid': vid,
                'title': title,
                'url': url,
                'filename': filename,
                'status': 'pending',
                'progress': 0,
                'downloaded': 0,
                'total_size': 0
            })
            urls.append(url)
            filenames.append(filename)
            
            print(f"添加到下载列表: {video_id} -> {filename}")
        
        if not files:
            return jsonify({'code': 0, 'message': '没有有效的下载文件'})
        
        # 创建下载任务记录
        download_tasks[task_id] = {
            'task_id': task_id,
            'status': 'running',
            'start_time': time.time(),
            'total_files': len(files),
            'files': files,
            'urls': urls,
            'filenames': filenames
        }
        
        print(f"创建下载任务: {task_id}, 文件数: {len(files)}")  # 调试信息
        
        # 启动异步下载任务
        import threading
        download_thread = threading.Thread(target=run_async_download, args=(task_id, urls, filenames))
        download_thread.daemon = True
        download_thread.start()
        
        return jsonify({
            'code': 1,
            'message': f'下载任务已启动，共 {len(files)} 个文件',
            'data': {
                'task_id': task_id,
                'status_endpoint': f'/api/download_status/{task_id}',
                'list_endpoint': f'/api/list_downloads',
                'total_files': len(files)
            }
        })
        
    except Exception as e:
        print(f"start_download 错误: {e}")
        import traceback
        traceback.print_exc()  # 打印完整的错误栈
        return jsonify({'code': 0, 'message': f'启动下载失败: {str(e)}'})

@app.route('/api/download_status/<task_id>', methods=['GET'])
def get_download_status(task_id):
    """获取下载任务状态"""
    if task_id not in download_tasks:
        return jsonify({'code': 0, 'message': '下载任务不存在'})
    
    task = download_tasks[task_id]
    
    # 计算总体进度
    total_progress = 0
    completed = 0
    failed = 0
    downloading = 0
    
    for file_info in task['files']:
        if file_info['status'] == 'completed':
            completed += 1
            total_progress += 100
        elif file_info['status'] == 'pending':
            total_progress += 0
        elif 'failed' in file_info['status']:
            failed += 1
            total_progress += 0
        else:
            downloading += 1
            total_progress += file_info.get('progress', 0)
    
    if task['total_files'] > 0:
        overall_progress = round(total_progress / task['total_files'], 1)
    else:
        overall_progress = 0
    
    # 准备返回数据
    status_data = {
        'task_id': task_id,
        'status': task['status'],
        'overall_progress': overall_progress,
        'start_time': time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(task['start_time'])),
        'total_files': task['total_files'],
        'completed_files': completed,
        'failed_files': failed,
        'downloading_files': downloading,
        'files': task['files'][:20]  # 只返回前20个文件信息
    }
    
    if task.get('completed_time'):
        status_data['completed_time'] = time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(task['completed_time']))
        status_data['duration'] = round(task['completed_time'] - task['start_time'], 2)
        status_data['success_count'] = task.get('success_count', 0)
        status_data['failed_count'] = task.get('failed_count', 0)
    
    return jsonify({
        'code': 1,
        'message': '下载状态查询成功',
        'data': status_data
    })

@app.route('/api/list_downloads', methods=['GET'])
def list_downloads():
    """列出所有下载任务"""
    tasks_list = []
    for tid, t in sorted(download_tasks.items(), key=lambda x: x[1].get('start_time', 0), reverse=True):
        # 计算总体进度
        total_progress = 0
        completed = 0
        for file_info in t['files']:
            if file_info['status'] == 'completed':
                completed += 1
                total_progress += 100
            else:
                total_progress += file_info.get('progress', 0)
        
        if t['total_files'] > 0:
            overall_progress = round(total_progress / t['total_files'], 1)
        else:
            overall_progress = 0
        
        tasks_list.append({
            'task_id': tid,
            'status': t['status'],
            'overall_progress': overall_progress,
            'total_files': t['total_files'],
            'completed_files': completed,
            'start_time': time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(t['start_time'])) if t.get('start_time') else '未知'
        })
    
    return jsonify({
        'code': 1,
        'message': '下载任务列表获取成功',
        'data': {
            'total_tasks': len(tasks_list),
            'tasks': tasks_list
        }
    })

@app.route('/api/download_file/<path:filename>', methods=['GET'])
def download_file(filename):
    """下载文件"""
    try:
        # 安全检查
        safe_path = os.path.abspath(os.path.join(DOWNLOAD_DIR, os.path.basename(filename)))
        if not safe_path.startswith(os.path.abspath(DOWNLOAD_DIR)):
            return jsonify({'code': 0, 'message': '无效的文件路径'}), 403
        
        if not os.path.exists(safe_path):
            return jsonify({'code': 0, 'message': '文件不存在'}), 404
        
        return send_file(safe_path, as_attachment=True)
    except Exception as e:
        return jsonify({'code': 0, 'message': f'下载失败: {str(e)}'}), 500

@app.route('/api/clear_downloads', methods=['POST'])
def clear_downloads():
    """清理下载目录"""
    try:
        # 只清理超过7天的文件
        current_time = time.time()
        deleted_count = 0
        
        for filename in os.listdir(DOWNLOAD_DIR):
            file_path = os.path.join(DOWNLOAD_DIR, filename)
            if os.path.isfile(file_path):
                # 获取文件修改时间
                file_mtime = os.path.getmtime(file_path)
                # 如果文件超过7天，删除
                if current_time - file_mtime > 7 * 24 * 60 * 60:
                    os.remove(file_path)
                    deleted_count += 1
        
        return jsonify({
            'code': 1,
            'message': f'清理完成，删除了 {deleted_count} 个旧文件'
        })
    except Exception as e:
        return jsonify({'code': 0, 'message': f'清理失败: {str(e)}'})

@app.route('/api/db_status', methods=['GET'])
def db_status():
    """
    检查数据库文件状态和统计信息（从d.py复制）
    """
    try:
        db_files_status = []
        total_records = 0

        for db_file, (low, high) in DB_FILE_RANGES.items():
            db_path = os.path.join(DB_BASE_PATH, db_file)
            exists = os.path.exists(db_path)
            record_count = 0

            if exists:
                try:
                    conn = sqlite3.connect(db_path)
                    cursor = conn.cursor()
                    cursor.execute("SELECT COUNT(*) FROM videos")
                    record_count = cursor.fetchone()[0]
                    total_records += record_count
                    conn.close()
                except sqlite3.Error as e:
                    record_count = f'错误: {e}'

            db_files_status.append({
                'filename': db_file,
                'exists': exists,
                'records': record_count,
                'vid_range': (low, high)
            })

        return jsonify({
            'code': 1,
            'message': '数据库状态查询成功',
            'data': {
                'db_directory': os.path.abspath(DB_BASE_PATH),
                'files': db_files_status,
                'total_files_found': sum(1 for f in db_files_status if f['exists']),
                'total_records': total_records
            }
        })
    except Exception as e:
        print(f"db_status 错误: {e}")
        return jsonify({'code': 0, 'message': f'数据库状态查询失败: {str(e)}'})

@app.route('/api/list_tasks', methods=['GET'])
def list_tasks():
    tasks_list = []
    for tid, t in sorted(scan_tasks.items(), key=lambda x: x[1]['start_time'], reverse=True):
        tasks_list.append({
            'task_id': tid, 'status': t['status'], 'start_video_id': t['start_video_id'],
            'radius': t['radius'], 'progress': f"{t['scanned_count']}/{t['total_count']}",
            'pseudo_found': len(t['pseudo_segments']),
            'start_time': time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(t['start_time']))
        })
    
    return jsonify({
        'code': 1, 'message': '任务列表获取成功',
        'data': {'total_tasks': len(tasks_list), 'tasks': tasks_list}
    })

# ==================== 第四部分：前端界面（保持原有排版）====================

HTML_PAGE = '''
<!DOCTYPE html>
<html>
<head>
    <title>新浪视频伪分段分析工具</title>
    <meta charset="utf-8">
    <style>
        body { font-family: sans-serif; margin: 40px; background: #f5f5f5; }
        .container { max-width: 1400px; margin: auto; background: white; padding: 30px; border-radius: 10px; box-shadow: 0 2px 10px rgba(0,0,0,0.1); }
        h1 { color: #333; border-bottom: 2px solid #4CAF50; padding-bottom: 10px; }
        .tab { overflow: hidden; border-bottom: 1px solid #ccc; margin-bottom: 20px; }
        .tab button { background: none; color: #555; border: none; padding: 14px 20px; cursor: pointer; font-size: 16px; margin-right: 5px; border-radius: 5px 5px 0 0; }
        .tab button:hover { background-color: #f1f1f1; }
        .tab button.active { background-color: #e8f5e9; color: #2e7d32; font-weight: bold; border: 1px solid #ccc; border-bottom: none; }
        .tab-content { display: none; padding: 20px 0; }
        .tab-content.active { display: block; }
        .form-group { margin: 15px 0; }
        label { display: block; font-weight: bold; margin-bottom: 8px; color: #555; }
        input, textarea { padding: 10px; width: 300px; border: 1px solid #ddd; border-radius: 4px; font-size: 16px; }
        button { background: #4CAF50; color: white; border: none; padding: 12px 24px; border-radius: 4px; cursor: pointer; font-size: 16px; margin-right: 10px; }
        button:hover { background: #45a049; }
        button:disabled { background: #cccccc; }
        .task-status { background: #e8f5e9; padding: 15px; border-radius: 5px; margin: 20px 0; border-left: 4px solid #4CAF50; }
        pre { background: #f5f5f5; padding: 15px; border-radius: 5px; overflow: auto; }
        .small-btn { padding: 4px 8px; font-size: 12px; margin-left: 8px; }
        .result-table { width: 100%; border-collapse: collapse; margin: 20px 0; }
        .result-table th, .result-table td { border: 1px solid #ddd; padding: 8px; text-align: left; }
        .result-table th { background-color: #f2f2f2; }
        .result-table tr:hover { background-color: #f9f9f9; }
        .category-box { padding: 15px; margin: 15px 0; border-radius: 5px; }
        .confirmed { background-color: #ffe6e6; border-left: 4px solid #ff0000; }
        .info-pseudo { background-color: #fff3cd; border-left: 4px solid #ffc107; }
        .not-found { background-color: #e2e3e5; border-left: 4px solid #6c757d; }
        .error { background-color: #f8d7da; border-left: 4px solid #dc3545; }
        .summary-box { display: flex; justify-content: space-between; margin: 20px 0; }
        .summary-item { flex: 1; text-align: center; padding: 15px; background: #f8f9fa; border-radius: 5px; margin: 0 10px; }
        .summary-value { font-size: 24px; font-weight: bold; }
        .summary-label { color: #6c757d; margin-top: 5px; }
        .toggle-btn { background: #6c757d; color: white; border: none; padding: 5px 10px; border-radius: 3px; cursor: pointer; font-size: 12px; margin-left: 10px; }
        .warning { background-color: #fff3cd; border: 1px solid #ffc107; padding: 10px; border-radius: 5px; margin: 10px 0; }
        .progress-bar { width: 100%; background-color: #f1f1f1; border-radius: 5px; margin: 10px 0; }
        .progress { height: 20px; background-color: #4CAF50; border-radius: 5px; text-align: center; color: white; line-height: 20px; }
        .download-btn { background: #007bff; color: white; border: none; padding: 6px 12px; border-radius: 4px; cursor: pointer; font-size: 14px; margin: 2px; }
        .download-btn:hover { background: #0056b3; }
        .select-all { margin: 10px 0; }
        .checkbox-cell { width: 50px; text-align: center; }
        .download-section { background: #e8f5e9; padding: 15px; border-radius: 5px; margin: 15px 0; }
    </style>
</head>
<body>
    <div class="container">
        <h1>新浪视频伪分段分析工具</h1>
        <p>功能一：正向扫描发现伪分段视频 | 功能二：反向验证伪分段视频的CDN文件 | 功能三：异步下载CDN文件</p>
        
        <div class="tab">
            <button class="tab-link active" onclick="openTab(event, 'scan-tab')">正向扫描</button>
            <button class="tab-link" onclick="openTab(event, 'reverse-tab')">反向验证</button>
            <button class="tab-link" onclick="openTab(event, 'download-tab')">下载管理</button>
            <button class="tab-link" onclick="openTab(event, 'db-tab')">DB状态</button>
            <button class="tab-link" onclick="openTab(event, 'tasks-tab')">任务列表</button>
        </div>
        
        <div id="scan-tab" class="tab-content active">
            <h3>正向扫描发现伪分段视频</h3>
            <div class="form-group">
                <label for="startId">起始 video_id:</label>
                <input type="number" id="startId" value="214497920" min="1" required>
            </div>
            <div class="form-group">
                <label for="radius">扫描半径:</label>
                <input type="number" id="radius" value="10" min="1" max="1000" required>
                <small>例如：半径为10，将扫描从 (起始ID-10) 到 (起始ID+10) 的共21个视频。</small>
            </div>
            <button onclick="startScan()" id="scanBtn">启动扫描任务</button>
            <div id="taskResult"></div>
            <div id="statusContainer"></div>
            <div id="resultsContainer"></div>
        </div>
        
        <div id="reverse-tab" class="tab-content">
            <h3>反向验证伪分段视频</h3>
            <p><strong>采用 d.py 的数据库查找策略</strong></p>
            <p>支持无限制批量查询，但大量数据可能需要较长时间处理。</p>
            
            <div class="form-group">
                <label for="singleVideoId">单个 video_id 验证:</label>
                <input type="number" id="singleVideoId" placeholder="输入伪分段 video_id">
                <button onclick="reverseCheckSingle()">反查验证</button>
            </div>
            <div class="form-group">
                <label for="batchVideoIds">批量 video_id 验证 (无限制):</label>
                <textarea id="batchVideoIds" rows="10" placeholder="每行输入一个伪分段 video_id，例如：&#10;214497920&#10;214497921&#10;214497922&#10;&#10;支持数万甚至数十万条记录批量查询。"></textarea>
                <div>
                    <button onclick="reverseCheckBatch()" id="batchBtn">批量反查验证</button>
                    <button onclick="reverseCheckBatchFast()" id="fastBtn" style="background:#007bff;">快速批量验证(仅数据库)</button>
                    <button onclick="exportResults()" id="exportBtn" style="background:#6c757d; display:none;">导出结果</button>
                </div>
                <div id="batchProgress" style="display:none;">
                    <p id="batchStatus">处理中...</p>
                    <div class="progress-bar">
                        <div class="progress" id="batchProgressBar" style="width:0%">0%</div>
                    </div>
                </div>
            </div>
            <div id="reverseResult"></div>
        </div>
        
        <div id="download-tab" class="tab-content">
            <h3>下载管理</h3>
            <div class="download-section">
                <h4>📥 下载文件选择</h4>
                <p>在反向验证结果中，选择CDN存在的文件进行下载。</p>
                <div id="downloadSelection" style="display:none;">
                    <h4>已选择下载项</h4>
                    <div id="selectedItemsList"></div>
                    <div class="select-all">
                        <input type="checkbox" id="selectAllItems" onchange="toggleSelectAllItems()">
                        <label for="selectAllItems">全选/取消全选</label>
                    </div>
                    <button onclick="startSelectedDownload()" id="startDownloadBtn" style="background:#28a745;">开始下载选中项</button>
                    <button onclick="clearSelectedItems()" style="background:#6c757d;">清空选择</button>
                </div>
            </div>
            
            <div class="download-section">
                <h4>📋 下载任务管理</h4>
                <button onclick="loadDownloadTasks()">刷新下载任务列表</button>
                <button onclick="clearOldDownloads()" style="background:#ffc107;">清理7天前文件</button>
                <div id="downloadTasksList"></div>
            </div>
            
            <div class="download-section">
                <h4>📚 已下载文件</h4>
                <div id="downloadedFilesList"></div>
            </div>
        </div>
        
        <div id="db-tab" class="tab-content">
            <h3>数据库文件状态</h3>
            <button onclick="checkDbStatus()">检查DB状态</button>
            <div id="dbStatusResult"></div>
        </div>
        
        <div id="tasks-tab" class="tab-content">
            <h3>所有扫描任务</h3>
            <button onclick="loadAllTasks()">刷新任务列表</button>
            <div id="allTasksList"></div>
        </div>
    </div>

    <script>
        let currentBatchResults = null;
        let currentBatchMode = 'full'; // 'full' 或 'fast'
        let selectedDownloadItems = [];
        
        function openTab(evt, tabName) {
            const tabContents = document.getElementsByClassName("tab-content");
            const tabLinks = document.getElementsByClassName("tab-link");
            for (let content of tabContents) content.classList.remove("active");
            for (let link of tabLinks) link.classList.remove("active");
            document.getElementById(tabName).classList.add("active");
            evt.currentTarget.classList.add("active");
        }
        
        // 正向扫描相关函数
        function startScan() {
            const startId = document.getElementById('startId').value;
            const radius = document.getElementById('radius').value;
            const btn = document.getElementById('scanBtn');
            
            btn.disabled = true;
            btn.textContent = '扫描启动中...';
            
            fetch('/api/start_scan', {
                method: 'POST',
                headers: {'Content-Type': 'application/json'},
                body: JSON.stringify({start_video_id: parseInt(startId), radius: parseInt(radius)})
            })
            .then(r => r.json())
            .then(data => {
                const resultDiv = document.getElementById('taskResult');
                if (data.code === 1) {
                    resultDiv.innerHTML = `
                        <div class="task-status">
                            <h3>✅ 扫描任务已启动</h3>
                            <p><strong>任务ID:</strong> ${data.data.task_id}</p>
                            <p><strong>扫描范围:</strong> ${data.data.scan_range} (共${data.data.total_videos}个视频)</p>
                            <p><button onclick="checkStatus('${data.data.task_id}')">点击跟踪进度</button></p>
                        </div>
                    `;
                    checkStatus(data.data.task_id);
                } else {
                    resultDiv.innerHTML = `<div class="task-status" style="border-color: #f44336;"><h3>❌ 启动失败</h3><p>${data.message}</p></div>`;
                }
                btn.disabled = false;
                btn.textContent = '启动扫描任务';
            })
            .catch(err => {
                document.getElementById('taskResult').innerHTML = `<p style="color:red;">网络错误: ${err}</p>`;
                btn.disabled = false;
                btn.textContent = '启动扫描任务';
            });
        }
        
        function checkStatus(taskId) {
            fetch(`/api/scan_status/${taskId}`)
            .then(r => r.json())
            .then(data => {
                if (data.code !== 1) return;
                const statusDiv = document.getElementById('statusContainer');
                const d = data.data;
                let html = `<div class="task-status"><h3>📊 任务进度: ${d.progress}%</h3>`;
                html += `<p><strong>状态:</strong> ${d.status === 'running' ? '运行中' : d.status}</p>`;
                html += `<p><strong>进度:</strong> ${d.scanned} / ${d.total} (${d.progress}%)</p>`;
                html += `<p><strong>已发现伪分段:</strong> ${d.pseudo_found} 个</p>`;
                html += `<p><strong>封面统计:</strong> ${JSON.stringify(d.cover_stats)}</p>`;
                if (d.status === 'running') {
                    html += `<p>3秒后自动刷新... <button onclick="checkStatus('${taskId}')">立即刷新</button></p>`;
                    setTimeout(() => checkStatus(taskId), 3000);
                } else if (d.status === 'completed') {
                    html += `<p><button onclick="getFullResults('${taskId}')">查看完整结果</button></p>`;
                }
                html += `</div>`;
                statusDiv.innerHTML = html;
            });
        }
        
        function getFullResults(taskId) {
            fetch(`/api/scan_results/${taskId}`)
            .then(r => r.json())
            .then(data => {
                if (data.code !== 1) return;
                
                const d = data.data;
                const resultsDiv = document.getElementById('resultsContainer');
                
                let html = `<h3>📋 扫描结果详情</h3>
                            <p><strong>总结:</strong> 在 ${d.total_scanned} 个视频中，发现 ${d.pseudo_count} 个伪分段视频。</p>
                            <p><strong>封面统计:</strong> ${JSON.stringify(d.cover_statistics)}</p>`;
                
                if (d.pseudo_segments && d.pseudo_segments.length > 0) {
                    html += `<h4>伪分段 video_id 列表 (共 ${d.pseudo_count} 个):</h4>`;
                    html += `<div style="max-height: 300px; overflow-y: auto; border: 1px solid #ddd; padding: 10px; margin: 10px 0;">`;
                    html += `<ul>`;
                    d.pseudo_segments.forEach(id => {
                        html += `<li>${id} <button onclick="reverseCheckFromResult(${id})" class="small-btn">反向验证</button></li>`;
                    });
                    html += `</ul>`;
                    html += `</div>`;
                }
                
                resultsDiv.innerHTML = html;
            })
            .catch(err => {
                document.getElementById('resultsContainer').innerHTML = 
                    `<p style="color:red;">获取结果失败: ${err}</p>`;
            });
        }
        
        function reverseCheckFromResult(videoId) {
            document.querySelectorAll('.tab-link').forEach(btn => btn.classList.remove("active"));
            document.querySelectorAll('.tab-content').forEach(content => content.classList.remove("active"));
            
            document.querySelector('[onclick="openTab(event, \\'reverse-tab\\')"]').classList.add("active");
            document.getElementById('reverse-tab').classList.add("active");
            
            document.getElementById('singleVideoId').value = videoId;
            reverseCheckSingle();
        }
        
        // 反向验证相关函数
        function reverseCheckSingle() {
            const videoId = document.getElementById('singleVideoId').value;
            if (!videoId) {
                alert('请输入video_id');
                return;
            }
            
            const resultDiv = document.getElementById('reverseResult');
            resultDiv.innerHTML = '<p>查询中...</p>';
            
            fetch('/api/reverse_check', {
                method: 'POST',
                headers: {'Content-Type': 'application/json'},
                body: JSON.stringify({video_id: parseInt(videoId)})
            })
            .then(r => r.json())
            .then(data => {
                let html = '<h4>反查验证结果:</h4>';
                if (data.code === 1) {
                    html += `<div class="task-status">`;
                    html += `<h3>✅ ${data.data.verdict}</h3>`;
                    html += `<p><strong>输入 video_id:</strong> ${data.data.input_video_id}</p>`;
                    html += `<p><strong>找到的 vid:</strong> ${data.data.found_vid}</p>`;
                    html += `<p><strong>数据库来源:</strong> ${data.data.database_record.source_db || '未知'}</p>`;
                    html += `<p><strong>CDN文件状态:</strong> ${data.data.cdn_check.exists ? '存在' : '不存在'}</p>`;
                    if (data.data.cdn_check.exists) {
                        html += `<p><strong>CDN URL:</strong> <a href="${data.data.cdn_check.url}" target="_blank">${data.data.cdn_check.url}</a></p>`;
                        // 注意：单个反查验证返回的是 data.data，且CDN检查字段是 cdn_check
                        html += `<button onclick="addToDownloadListSingle(${JSON.stringify(data.data).replace(/"/g, '&quot;')})" class="download-btn">添加到下载列表</button>`;
                    }
                    html += `<p><button onclick="toggleDetails('single')" class="toggle-btn">显示详情</button></p>`;
                    html += `<div id="single-details" style="display:none;"><pre>${JSON.stringify(data.data, null, 2)}</pre></div>`;
                    html += `</div>`;
                } else {
                    html += `<div class="task-status" style="border-color: #f44336;"><h3>❌ 查询失败</h3><p>${data.message}</p></div>`;
                }
                resultDiv.innerHTML = html;
            })
            .catch(err => {
                resultDiv.innerHTML = 
                    '<p style="color:red;">请求失败: ' + err + '</p>';
            });
        }
        
        function toggleDetails(type) {
            const detailsDiv = document.getElementById(`${type}-details`);
            if (detailsDiv.style.display === 'none') {
                detailsDiv.style.display = 'block';
            } else {
                detailsDiv.style.display = 'none';
            }
        }
        
        function reverseCheckBatch() {
            const textarea = document.getElementById('batchVideoIds');
            const ids = textarea.value.split('\\n')
                .map(id => id.trim())
                .filter(id => id.length > 0)
                .map(id => parseInt(id));
            
            if (ids.length === 0) {
                alert('请输入至少一个video_id');
                return;
            }
            
            // 警告但不限制
            if (ids.length > 10000) {
                if (!confirm(`警告：您输入了 ${ids.length.toLocaleString()} 个视频ID，处理可能需要较长时间。是否继续？`)) {
                    return;
                }
            }
            
            const resultDiv = document.getElementById('reverseResult');
            const batchBtn = document.getElementById('batchBtn');
            const fastBtn = document.getElementById('fastBtn');
            const progressDiv = document.getElementById('batchProgress');
            const statusText = document.getElementById('batchStatus');
            const progressBar = document.getElementById('batchProgressBar');
            
            resultDiv.innerHTML = `<p>批量查询中 (共 ${ids.length.toLocaleString()} 个)...</p>`;
            document.getElementById('exportBtn').style.display = 'none';
            batchBtn.disabled = true;
            fastBtn.disabled = true;
            progressDiv.style.display = 'block';
            statusText.textContent = '正在处理中...';
            progressBar.style.width = '0%';
            progressBar.textContent = '0%';
            
            currentBatchMode = 'full';
            
            fetch('/api/batch_reverse_check', {
                method: 'POST',
                headers: {'Content-Type': 'application/json'},
                body: JSON.stringify({video_ids: ids})
            })
            .then(r => r.json())
            .then(data => {
                currentBatchResults = data;
                displayBatchResults(data);
                
                batchBtn.disabled = false;
                fastBtn.disabled = false;
                progressDiv.style.display = 'none';
            })
            .catch(err => {
                resultDiv.innerHTML = 
                    '<p style="color:red;">请求失败: ' + err + '</p>';
                batchBtn.disabled = false;
                fastBtn.disabled = false;
                progressDiv.style.display = 'none';
            });
        }
        
        function reverseCheckBatchFast() {
            const textarea = document.getElementById('batchVideoIds');
            const ids = textarea.value.split('\\n')
                .map(id => id.trim())
                .filter(id => id.length > 0)
                .map(id => parseInt(id));
            
            if (ids.length === 0) {
                alert('请输入至少一个video_id');
                return;
            }
            
            // 警告但不限制
            if (ids.length > 50000) {
                if (!confirm(`警告：您输入了 ${ids.length.toLocaleString()} 个视频ID，快速模式不检查CDN。是否继续？`)) {
                    return;
                }
            }
            
            const resultDiv = document.getElementById('reverseResult');
            const batchBtn = document.getElementById('batchBtn');
            const fastBtn = document.getElementById('fastBtn');
            const progressDiv = document.getElementById('batchProgress');
            const statusText = document.getElementById('batchStatus');
            const progressBar = document.getElementById('batchProgressBar');
            
            resultDiv.innerHTML = `<p>快速批量查询中 (共 ${ids.length.toLocaleString()} 个)...</p>`;
            document.getElementById('exportBtn').style.display = 'none';
            batchBtn.disabled = true;
            fastBtn.disabled = true;
            progressDiv.style.display = 'block';
            statusText.textContent = '正在快速处理中...';
            progressBar.style.width = '0%';
            progressBar.textContent = '0%';
            
            currentBatchMode = 'fast';
            
            fetch('/api/batch_reverse_check_fast', {
                method: 'POST',
                headers: {'Content-Type': 'application/json'},
                body: JSON.stringify({video_ids: ids})
            })
            .then(r => r.json())
            .then(data => {
                currentBatchResults = data;
                displayFastBatchResults(data);
                
                batchBtn.disabled = false;
                fastBtn.disabled = false;
                progressDiv.style.display = 'none';
            })
            .catch(err => {
                resultDiv.innerHTML = 
                    '<p style="color:red;">请求失败: ' + err + '</p>';
                batchBtn.disabled = false;
                fastBtn.disabled = false;
                progressDiv.style.display = 'none';
            });
        }
        
        function displayBatchResults(data) {
            let html = '<h4>批量反查验证结果:</h4>';
            
            if (data.code === 1) {
                const summary = data.data.summary;
                const processingTime = data.data.processing_time;
                const detailedResults = data.data.detailed_results || [];
                
                // 摘要统计
                html += `<div class="summary-box">
                    <div class="summary-item">
                        <div class="summary-value">${summary.total}</div>
                        <div class="summary-label">总计</div>
                    </div>
                    <div class="summary-item">
                        <div class="summary-value">${summary.found_in_db}</div>
                        <div class="summary-label">数据库找到</div>
                    </div>
                    <div class="summary-item">
                        <div class="summary-value">${summary.cdn_exists}</div>
                        <div class="summary-label">CDN存在</div>
                    </div>
                    <div class="summary-item">
                        <div class="summary-value">${summary.cdn_missing}</div>
                        <div class="summary-label">CDN缺失</div>
                    </div>
                </div>`;
                
                // 处理时间
                html += `<div class="task-status">
                    <p><strong>处理时间:</strong> ${processingTime} 秒</p>
                    <p><strong>已确认伪分段:</strong> ${summary.confirmed_pseudo} 个 (可下载)</p>
                    <p><strong>信息伪分段:</strong> ${summary.info_pseudo} 个</p>
                    <p><strong>未找到记录:</strong> ${summary.not_found} 个</p>
                    ${data.data.note ? `<p><em>${data.data.note}</em></p>` : ''}
                </div>`;
                
                // 选择下载按钮
                if (summary.cdn_exists > 0) {
                    html += `<div class="select-all">
                        <input type="checkbox" id="selectAllDownload" onchange="toggleSelectAllDownload()">
                        <label for="selectAllDownload">全选可下载项</label>
                        <button onclick="addAllDownloadableToSelection()" class="download-btn">全部添加到下载列表</button>
                    </div>`;
                }
                
                // 详细结果
                if (detailedResults.length > 0) {
                    html += `<h4>详细结果 (前 ${Math.min(detailedResults.length, 1000)} 条):</h4>`;
                    html += `<table class="result-table">
                        <thead>
                            <tr>
                                <th class="checkbox-cell">选择</th>
                                <th>序号</th>
                                <th>输入video_id</th>
                                <th>找到的vid</th>
                                <th>数据库来源</th>
                                <th>CDN文件</th>
                                <th>判定</th>
                                <th>操作</th>
                            </tr>
                        </thead>
                        <tbody>`;
                    
                    detailedResults.forEach((result, index) => {
                        const dbRecord = result.database_record;
                        const cdnCheck = result.cdn_check_result;
                        const isDownloadable = cdnCheck && cdnCheck.exists;
                        
                        html += `<tr>
                            <td class="checkbox-cell">
                                ${isDownloadable ? `<input type="checkbox" class="download-checkbox" data-index="${index}" onchange="toggleDownloadItem(${index}, ${isDownloadable})">` : ''}
                            </td>
                            <td>${index + 1}</td>
                            <td>${result.input_video_id}</td>
                            <td>${dbRecord ? dbRecord.vid : 'N/A'}</td>
                            <td>${dbRecord ? (dbRecord.source_db || dbRecord.found_in_db || '未知') : 'N/A'}</td>
                            <td>${cdnCheck ? (cdnCheck.exists ? '✅ 存在' : '❌ 缺失') : 'N/A'}</td>
                            <td>${result.verdict || '未知'}</td>
                            <td>
                                ${isDownloadable ? `<button onclick="addToDownloadListBatch(${JSON.stringify(result).replace(/"/g, '&quot;')})" class="small-btn">下载</button>` : ''}
                                <button onclick="showResultDetails(${result.input_video_id})" class="small-btn">详情</button>
                            </td>
                        </tr>`;
                    });
                    
                    html += `</tbody></table>`;
                }
                
                // 导出按钮
                document.getElementById('exportBtn').style.display = 'inline-block';
                
            } else {
                html += `<div class="task-status" style="border-color: #f44336;"><h3>❌ 批量查询失败</h3><p>${data.message}</p></div>`;
            }
            
            document.getElementById('reverseResult').innerHTML = html;
        }
        
        function displayFastBatchResults(data) {
            let html = '<h4>快速批量反查验证结果:</h4>';
            
            if (data.code === 1) {
                const processingTime = data.data.processing_time;
                const foundCount = data.data.found_count;
                const notFoundCount = data.data.not_found_count;
                const detailedResults = data.data.detailed_results || [];
                
                html += `<div class="summary-box">
                    <div class="summary-item">
                        <div class="summary-value">${foundCount + notFoundCount}</div>
                        <div class="summary-label">总计</div>
                    </div>
                    <div class="summary-item" style="background:#e8f5e9;">
                        <div class="summary-value">${foundCount}</div>
                        <div class="summary-label">数据库找到</div>
                    </div>
                    <div class="summary-item" style="background:#e2e3e5;">
                        <div class="summary-value">${notFoundCount}</div>
                        <div class="summary-label">未找到记录</div>
                    </div>
                </div>`;
                
                // 处理时间
                html += `<div class="task-status">
                    <p><strong>处理时间:</strong> ${processingTime} 秒 (快速模式，仅检查数据库)</p>
                    <p><strong>说明:</strong> 快速模式仅检查数据库记录，不验证CDN文件</p>
                </div>`;
                
                // 详细结果
                if (detailedResults.length > 0) {
                    html += `<h4>详细结果 (前 ${Math.min(detailedResults.length, 500)} 条):</h4>`;
                    html += `<table class="result-table">
                        <thead>
                            <tr>
                                <th>序号</th>
                                <th>输入video_id</th>
                                <th>找到的vid</th>
                                <th>数据库来源</th>
                                <th>判定</th>
                                <th>操作</th>
                            </tr>
                        </thead>
                        <tbody>`;
                    
                    detailedResults.forEach((result, index) => {
                        const dbRecord = result.database_record;
                        
                        html += `<tr>
                            <td>${index + 1}</td>
                            <td>${result.input_video_id}</td>
                            <td>${dbRecord ? dbRecord.vid : 'N/A'}</td>
                            <td>${dbRecord ? (dbRecord.source_db || dbRecord.found_in_db || '未知') : 'N/A'}</td>
                            <td>${result.verdict || '未知'}</td>
                            <td>
                                <button onclick="showResultDetails(${result.input_video_id})" class="small-btn">详情</button>
                            </td>
                        </tr>`;
                    });
                    
                    html += `</tbody></table>`;
                }
                
                // 导出按钮
                document.getElementById('exportBtn').style.display = 'inline-block';
                
            } else {
                html += `<div class="task-status" style="border-color: #f44336;"><h3>❌ 批量查询失败</h3><p>${data.message}</p></div>`;
            }
            
            document.getElementById('reverseResult').innerHTML = html;
        }
        
        // 下载相关函数 - 修复数据结构问题
        function addToDownloadListSingle(item) {
            // 单个反查验证的数据结构：item.cdn_check
            console.log('单个反查数据:', item);
            
            if (!item || !item.cdn_check || !item.cdn_check.exists) {
                alert('此文件CDN不存在，无法下载');
                return;
            }
            
            if (!item.database_record || !item.database_record.vid) {
                alert('缺少数据库记录信息，无法下载');
                return;
            }
            
            // 创建清洁的数据对象，统一为 cdn_check_result 格式
            const cleanedItem = {
                input_video_id: item.input_video_id,
                database_record: {
                    vid: item.database_record.vid,
                    video_id: item.database_record.video_id,
                    title: item.database_record.title || `video_${item.input_video_id}`,
                    length: item.database_record.length,
                    description: item.database_record.description,
                    create_time: item.database_record.create_time,
                    source_db: item.database_record.source_db || item.database_record.found_in_db || '未知'
                },
                cdn_check_result: {  // 统一使用 cdn_check_result
                    exists: item.cdn_check.exists,
                    url: item.cdn_check.url,
                    http_status: item.cdn_check.http_status,
                    content_length: item.cdn_check.content_length,
                    error: item.cdn_check.error
                },
                verdict: item.verdict
            };
            
            // 检查是否已存在
            const exists = selectedDownloadItems.some(i => 
                i.input_video_id === cleanedItem.input_video_id && 
                i.database_record.vid === cleanedItem.database_record.vid
            );
            
            if (!exists) {
                selectedDownloadItems.push(cleanedItem);
                updateDownloadSelectionDisplay();
                alert('已添加到下载列表');
            } else {
                alert('此项已在下载列表中');
            }
        }
        
        function addToDownloadListBatch(item) {
    // 批量反查验证的数据结构：item.cdn_check_result
    if (!item || !item.cdn_check_result || !item.cdn_check_result.exists) {
        alert('此文件CDN不存在，无法下载');
        return;
    }
    
    if (!item.database_record || !item.database_record.vid) {
        alert('缺少数据库记录信息，无法下载');
        return;
    }
    
    // 创建清洁的数据对象
    const cleanedItem = {
        input_video_id: item.input_video_id,
        database_record: {
            vid: item.database_record.vid,
            video_id: item.database_record.video_id,
            title: item.database_record.title || `video_${item.input_video_id}`,
            length: item.database_record.length,
            description: item.database_record.description,
            create_time: item.database_record.create_time,
            source_db: item.database_record.source_db || item.database_record.found_in_db || '未知'
        },
        cdn_check_result: item.cdn_check_result,
        verdict: item.verdict
    };
    
    // 检查是否已存在
    const exists = selectedDownloadItems.some(i => 
        i.input_video_id === cleanedItem.input_video_id && 
        i.database_record.vid === cleanedItem.database_record.vid
    );
    
    if (!exists) {
        selectedDownloadItems.push(cleanedItem);
        updateDownloadSelectionDisplay();
        // 不再显示单独的弹窗，通过更新显示来反馈
        // 可以在界面上显示一个短暂的状态提示
        showStatusMessage('已添加到下载列表');
    } else {
        showStatusMessage('此项已在下载列表中', 'warning');
    }
}

// 添加一个状态提示函数
function showStatusMessage(message, type = 'info') {
    // 移除已存在的状态消息
    const existingMessage = document.getElementById('statusMessage');
    if (existingMessage) {
        existingMessage.remove();
    }
    
    // 创建新的状态消息
    const statusDiv = document.createElement('div');
    statusDiv.id = 'statusMessage';
    statusDiv.style.cssText = `
        position: fixed;
        top: 20px;
        right: 20px;
        padding: 10px 20px;
        background-color: ${type === 'warning' ? '#ffc107' : '#28a745'};
        color: white;
        border-radius: 5px;
        z-index: 1000;
        box-shadow: 0 2px 10px rgba(0,0,0,0.1);
        transition: opacity 0.3s;
    `;
    statusDiv.textContent = message;
    
    document.body.appendChild(statusDiv);
    
    // 3秒后自动消失
    setTimeout(() => {
        statusDiv.style.opacity = '0';
        setTimeout(() => {
            if (statusDiv.parentNode) {
                statusDiv.remove();
            }
        }, 300);
    }, 3000);
}
        function toggleDownloadItem(index, isDownloadable) {
            if (!isDownloadable) return;
            
            if (currentBatchResults && currentBatchResults.data && currentBatchResults.data.detailed_results) {
                const item = currentBatchResults.data.detailed_results[index];
                const checkbox = document.querySelector(`.download-checkbox[data-index="${index}"]`);
                
                if (checkbox.checked) {
                    addToDownloadListBatch(item);
                } else {
                    removeFromDownloadList(item.input_video_id, item.database_record.vid);
                }
            }
        }
        
        function toggleSelectAllDownload() {
    const selectAll = document.getElementById('selectAllDownload');
    const checkboxes = document.querySelectorAll('.download-checkbox');
    
    if (!currentBatchResults || !currentBatchResults.data || !currentBatchResults.data.detailed_results) {
        return;
    }
    
    const items = currentBatchResults.data.detailed_results;
    let addedCount = 0;
    let alreadyExistsCount = 0;
    
    if (selectAll.checked) {
        // 全选：添加所有可下载项
        items.forEach((item, index) => {
            if (item.cdn_check_result && item.cdn_check_result.exists) {
                const exists = selectedDownloadItems.some(selected => 
                    selected.input_video_id === item.input_video_id && 
                    selected.database_record.vid === item.database_record.vid
                );
                
                if (!exists) {
                    selectedDownloadItems.push({
                        input_video_id: item.input_video_id,
                        database_record: item.database_record,
                        cdn_check_result: item.cdn_check_result,
                        verdict: item.verdict
                    });
                    addedCount++;
                } else {
                    alreadyExistsCount++;
                }
            }
            // 更新复选框状态
            if (checkboxes[index]) {
                checkboxes[index].checked = true;
            }
        });
        
        updateDownloadSelectionDisplay();
        
        // 只显示一个汇总弹窗
        if (addedCount > 0 || alreadyExistsCount > 0) {
            let message = `已添加 ${addedCount} 个新文件到下载列表。`;
            if (alreadyExistsCount > 0) {
                message += `\n${alreadyExistsCount} 个文件已在列表中。`;
            }
            alert(message);
        }
    } else {
        // 取消全选：移除所有对应的项
        const removedItems = [];
        
        // 收集要移除的项
        items.forEach(item => {
            if (item.cdn_check_result && item.cdn_check_result.exists) {
                removedItems.push({
                    videoId: item.input_video_id,
                    vid: item.database_record.vid
                });
            }
        });
        
        // 批量移除
        removedItems.forEach(item => {
            selectedDownloadItems = selectedDownloadItems.filter(selected => 
                !(selected.input_video_id === item.videoId && 
                  selected.database_record.vid === item.vid)
            );
        });
        
        // 更新复选框状态
        checkboxes.forEach(checkbox => {
            checkbox.checked = false;
        });
        
        updateDownloadSelectionDisplay();
        
        if (removedItems.length > 0) {
            alert(`已从下载列表中移除 ${removedItems.length} 个文件。`);
        }
    }
}
        
        function addAllDownloadableToSelection() {
            if (currentBatchResults && currentBatchResults.data && currentBatchResults.data.detailed_results) {
                const items = currentBatchResults.data.detailed_results;
                items.forEach(item => {
                    if (item.cdn_check_result && item.cdn_check_result.exists) {
                        addToDownloadListBatch(item);
                    }
                });
            }
        }
        
        function removeFromDownloadList(videoId, vid) {
            selectedDownloadItems = selectedDownloadItems.filter(item => 
                !(item.input_video_id === videoId && item.database_record.vid === vid)
            );
            updateDownloadSelectionDisplay();
        }
        
        function updateDownloadSelectionDisplay() {
            const selectionDiv = document.getElementById('downloadSelection');
            const listDiv = document.getElementById('selectedItemsList');
            
            if (selectedDownloadItems.length > 0) {
                selectionDiv.style.display = 'block';
                
                let html = `<p>已选择 ${selectedDownloadItems.length} 个文件:</p>`;
                html += `<ul>`;
                
                selectedDownloadItems.forEach((item, index) => {
                    const title = item.database_record.title || `video_${item.input_video_id}`;
                    const vid = item.database_record.vid;
                    const cdnExists = item.cdn_check_result && item.cdn_check_result.exists;
                    
                    html += `<li>
                        ${title} (vid: ${vid}, CDN: ${cdnExists ? '✅ 存在' : '❌ 缺失'})
                        <button onclick="removeFromDownloadList(${item.input_video_id}, '${vid}')" class="small-btn">移除</button>
                    </li>`;
                });
                
                html += `</ul>`;
                listDiv.innerHTML = html;
                
                // 切换到下载标签页
                document.querySelector('[onclick="openTab(event, \\'download-tab\\')"]').click();
            } else {
                selectionDiv.style.display = 'none';
            }
        }
        
        function toggleSelectAllItems() {
            const selectAll = document.getElementById('selectAllItems');
            // 这里可以添加更多逻辑，如果需要的话
        }
        
        function clearSelectedItems() {
            selectedDownloadItems = [];
            updateDownloadSelectionDisplay();
        }
        
        function startSelectedDownload() {
            if (selectedDownloadItems.length === 0) {
                alert('请先选择要下载的文件');
                return;
            }
            
            if (!confirm(`确定要下载 ${selectedDownloadItems.length} 个文件吗？`)) {
                return;
            }
            
            // 清理数据，确保只发送必需字段
            const cleanedItems = selectedDownloadItems.map(item => {
                return {
                    input_video_id: item.input_video_id,
                    database_record: item.database_record,
                    cdn_check_result: item.cdn_check_result,
                    verdict: item.verdict
                };
            }).filter(item => item.database_record && item.cdn_check_result && item.cdn_check_result.exists);
            
            if (cleanedItems.length === 0) {
                alert('没有有效的下载项目');
                return;
            }
            
            console.log('发送的items:', cleanedItems);  // 调试信息
            
            const btn = document.getElementById('startDownloadBtn');
            btn.disabled = true;
            btn.textContent = '下载启动中...';
            
            fetch('/api/start_download', {
                method: 'POST',
                headers: {'Content-Type': 'application/json'},
                body: JSON.stringify({items: cleanedItems})
            })
            .then(r => r.json())
            .then(data => {
                if (data.code === 1) {
                    alert(`下载任务已启动，任务ID: ${data.data.task_id}`);
                    selectedDownloadItems = [];
                    updateDownloadSelectionDisplay();
                    loadDownloadTasks();
                } else {
                    alert(`下载启动失败: ${data.message}`);
                }
                btn.disabled = false;
                btn.textContent = '开始下载选中项';
            })
            .catch(err => {
                alert('请求失败: ' + err);
                console.error('下载请求错误:', err);
                btn.disabled = false;
                btn.textContent = '开始下载选中项';
            });
        }
        
        function loadDownloadTasks() {
            fetch('/api/list_downloads')
            .then(r => r.json())
            .then(data => {
                if (data.code !== 1) return;
                const container = document.getElementById('downloadTasksList');
                
                if (data.data.total_tasks === 0) {
                    container.innerHTML = '<p>暂无下载任务。</p>';
                    return;
                }
                
                let html = `<table class="result-table">
                    <thead>
                        <tr>
                            <th>任务ID</th>
                            <th>状态</th>
                            <th>总体进度</th>
                            <th>文件数</th>
                            <th>完成数</th>
                            <th>开始时间</th>
                            <th>操作</th>
                        </tr>
                    </thead>
                    <tbody>`;
                
                data.data.tasks.forEach(task => {
                    html += `<tr>
                        <td>${task.task_id}</td>
                        <td>${task.status}</td>
                        <td>
                            <div class="progress-bar">
                                <div class="progress" style="width:${task.overall_progress}%">${task.overall_progress}%</div>
                            </div>
                        </td>
                        <td>${task.total_files}</td>
                        <td>${task.completed_files}</td>
                        <td>${task.start_time}</td>
                        <td>
                            <button onclick="checkDownloadStatus('${task.task_id}')" class="small-btn">查看</button>
                        </td>
                    </tr>`;
                });
                
                html += `</tbody></table>`;
                container.innerHTML = html;
            })
            .catch(err => {
                document.getElementById('downloadTasksList').innerHTML = 
                    `<p style="color:red;">加载失败: ${err}</p>`;
            });
        }
        
        function checkDownloadStatus(taskId) {
            fetch(`/api/download_status/${taskId}`)
            .then(r => r.json())
            .then(data => {
                if (data.code !== 1) return;
                
                const d = data.data;
                let html = `<h4>下载任务详情: ${taskId}</h4>`;
                html += `<div class="task-status">`;
                html += `<p><strong>状态:</strong> ${d.status}</p>`;
                html += `<p><strong>总体进度:</strong> ${d.overall_progress}%</p>`;
                html += `<p><strong>文件数:</strong> ${d.total_files} (完成: ${d.completed_files}, 失败: ${d.failed_files}, 下载中: ${d.downloading_files})</p>`;
                html += `<p><strong>开始时间:</strong> ${d.start_time}</p>`;
                
                if (d.completed_time) {
                    html += `<p><strong>完成时间:</strong> ${d.completed_time}</p>`;
                    html += `<p><strong>耗时:</strong> ${d.duration} 秒</p>`;
                    html += `<p><strong>成功:</strong> ${d.success_count} 个文件</p>`;
                    html += `<p><strong>失败:</strong> ${d.failed_count} 个文件</p>`;
                }
                
                html += `</div>`;
                
                // 文件列表
                if (d.files && d.files.length > 0) {
                    html += `<h5>文件详情:</h5>`;
                    html += `<table class="result-table">
                        <thead>
                            <tr>
                                <th>序号</th>
                                <th>视频ID</th>
                                <th>vid</th>
                                <th>标题</th>
                                <th>状态</th>
                                <th>进度</th>
                            </tr>
                        </thead>
                        <tbody>`;
                    
                    d.files.forEach(file => {
                        html += `<tr>
                            <td>${file.index + 1}</td>
                            <td>${file.video_id}</td>
                            <td>${file.vid}</td>
                            <td>${file.title || 'N/A'}</td>
                            <td>${file.status}</td>
                            <td>
                                <div class="progress-bar">
                                    <div class="progress" style="width:${file.progress}%">${file.progress}%</div>
                                </div>
                            </td>
                        </tr>`;
                    });
                    
                    html += `</tbody></table>`;
                }
                
                // 创建模态框显示详情
                const modal = document.createElement('div');
                modal.style.position = 'fixed';
                modal.style.top = '0';
                modal.style.left = '0';
                modal.style.width = '100%';
                modal.style.height = '100%';
                modal.style.backgroundColor = 'rgba(0,0,0,0.5)';
                modal.style.zIndex = '1000';
                modal.style.display = 'flex';
                modal.style.justifyContent = 'center';
                modal.style.alignItems = 'center';
                
                const modalContent = document.createElement('div');
                modalContent.style.backgroundColor = 'white';
                modalContent.style.padding = '20px';
                modalContent.style.borderRadius = '10px';
                modalContent.style.maxWidth = '800px';
                modalContent.style.maxHeight = '80%';
                modalContent.style.overflow = 'auto';
                modalContent.innerHTML = html;
                
                const closeButton = document.createElement('button');
                closeButton.textContent = '关闭';
                closeButton.style.marginTop = '10px';
                closeButton.onclick = function() {
                    document.body.removeChild(modal);
                };
                modalContent.appendChild(closeButton);
                
                modal.appendChild(modalContent);
                modal.onclick = function(e) {
                    if (e.target === modal) {
                        document.body.removeChild(modal);
                    }
                };
                
                document.body.appendChild(modal);
            })
            .catch(err => {
                alert('获取下载状态失败: ' + err);
            });
        }
        
        function clearOldDownloads() {
            if (!confirm('确定要清理7天前的下载文件吗？')) {
                return;
            }
            
            fetch('/api/clear_downloads', {
                method: 'POST',
                headers: {'Content-Type': 'application/json'}
            })
            .then(r => r.json())
            .then(data => {
                alert(data.message);
            })
            .catch(err => {
                alert('清理失败: ' + err);
            });
        }
        
        function showResultDetails(videoId) {
            if (!currentBatchResults || !currentBatchResults.data) {
                alert('没有可用的结果数据');
                return;
            }
            
            const results = currentBatchResults.data.results || currentBatchResults.data.detailed_results;
            const result = results.find(r => r.input_video_id === videoId);
            
            if (!result) {
                alert('未找到该video_id的详细结果');
                return;
            }
            
            let detailsHtml = `<h4>详细结果: ${videoId}</h4>`;
            detailsHtml += `<div style="max-height: 500px; overflow-y: auto;"><pre>${JSON.stringify(result, null, 2)}</pre></div>`;
            detailsHtml += `<button onclick="closeDetails()" style="margin-top: 10px;">关闭</button>`;
            
            // 创建一个模态框显示详情
            const modal = document.createElement('div');
            modal.style.position = 'fixed';
            modal.style.top = '0';
            modal.style.left = '0';
            modal.style.width = '100%';
            modal.style.height = '100%';
            modal.style.backgroundColor = 'rgba(0,0,0,0.5)';
            modal.style.zIndex = '1000';
            modal.style.display = 'flex';
            modal.style.justifyContent = 'center';
            modal.style.alignItems = 'center';
            
            const modalContent = document.createElement('div');
            modalContent.style.backgroundColor = 'white';
            modalContent.style.padding = '20px';
            modalContent.style.borderRadius = '10px';
            modalContent.style.maxWidth = '800px';
            modalContent.style.maxHeight = '80%';
            modalContent.style.overflow = 'auto';
            modalContent.innerHTML = detailsHtml;
            
            modal.appendChild(modalContent);
            modal.onclick = function(e) {
                if (e.target === modal) {
                    document.body.removeChild(modal);
                }
            };
            
            document.body.appendChild(modal);
        }
        
        function closeDetails() {
            const modals = document.querySelectorAll('div[style*="position: fixed"]');
            modals.forEach(modal => {
                if (modal.style.backgroundColor === 'rgba(0,0,0,0.5)') {
                    document.body.removeChild(modal);
                }
            });
        }
        
        function exportResults() {
            if (!currentBatchResults) {
                alert('没有可导出的结果');
                return;
            }
            
            const dataStr = JSON.stringify(currentBatchResults, null, 2);
            const dataBlob = new Blob([dataStr], {type: 'application/json'});
            const url = URL.createObjectURL(dataBlob);
            const link = document.createElement('a');
            link.href = url;
            
            if (currentBatchMode === 'full') {
                link.download = `reverse_check_full_${new Date().getTime()}.json`;
            } else {
                link.download = `reverse_check_fast_${new Date().getTime()}.json`;
            }
            
            document.body.appendChild(link);
            link.click();
            document.body.removeChild(link);
            URL.revokeObjectURL(url);
        }
        
        function checkDbStatus() {
            const resultDiv = document.getElementById('dbStatusResult');
            resultDiv.innerHTML = '<p>检查中...</p>';
            
            fetch('/api/db_status')
            .then(r => r.json())
            .then(data => {
                let html = '<h4>数据库文件状态</h4>';
                if (data.code === 1) {
                    html += `<p>目录: ${data.data.db_directory}</p>`;
                    html += `<p>共找到 ${data.data.total_files_found} 个数据库文件，总计约 ${data.data.total_records} 条记录</p>`;
                    
                    html += '<table class="result-table"><tr><th>文件名</th><th>是否存在</th><th>记录数</th><th>vid范围</th></tr>';
                    for (let file of data.data.files) {
                        html += `<tr>
                            <td>${file.filename}</td>
                            <td>${file.exists ? '✅' : '❌'}</td>
                            <td>${file.records}</td>
                            <td>${file.vid_range[0].toLocaleString()} - ${file.vid_range[1].toLocaleString()}</td>
                        </tr>`;
                    }
                    html += '</table>';
                } else {
                    html += `<p style="color:red;">${data.message}</p>`;
                }
                
                resultDiv.innerHTML = html;
            })
            .catch(err => {
                resultDiv.innerHTML = `<p style="color:red;">请求失败: ${err}</p>`;
            });
        }
        
        function loadAllTasks() {
            fetch('/api/list_tasks')
            .then(r => r.json())
            .then(data => {
                if (data.code !== 1) return;
                const container = document.getElementById('allTasksList');
                if (data.data.total_tasks === 0) {
                    container.innerHTML = '<p>暂无任务记录。</p>';
                    return;
                }
                let html = `<table class="result-table"><tr>
                    <th>任务ID</th>
                    <th>起始ID</th>
                    <th>半径</th>
                    <th>状态</th>
                    <th>进度</th>
                    <th>伪分段</th>
                    <th>操作</th>
                </tr>`;
                data.data.tasks.forEach(task => {
                    html += `<tr>
                        <td>${task.task_id}</td>
                        <td>${task.start_video_id}</td>
                        <td>${task.radius}</td>
                        <td>${task.status}</td>
                        <td>${task.progress}</td>
                        <td>${task.pseudo_found}</td>
                        <td>
                            <button onclick="checkStatus('${task.task_id}')" class="small-btn">查看</button>
                        </td>
                    </tr>`;
                });
                html += `</table>`;
                container.innerHTML = html;
            });
        }
        
        window.onload = function() {
            loadAllTasks();
            loadDownloadTasks();
        };
    </script>
</body>
</html>
'''

@app.route('/')
def index():
    return render_template_string(HTML_PAGE)

# ==================== 第五部分：启动时检查并创建索引（整合d.py功能）====================

def create_indices_on_startup():
    """
    启动时自动为所有数据库文件创建索引（d.py功能）
    """
    print("正在检查并创建数据库索引...")
    
    for i in range(0, 14):  # sina_00.db 到 sina_13.db
        db_file = f"sina_{i:02d}.db"
        db_path = os.path.join(DB_BASE_PATH, db_file)
        
        if os.path.exists(db_path):
            try:
                conn = sqlite3.connect(db_path)
                cursor = conn.cursor()
                
                # 创建索引
                cursor.execute("CREATE INDEX IF NOT EXISTS idx_video_id ON videos(video_id)")
                print(f"✅ 已为 {db_file} 创建 video_id 索引")
                
                # 验证索引
                cursor.execute("SELECT name FROM sqlite_master WHERE type='index' AND tbl_name='videos'")
                indexes = [row[0] for row in cursor.fetchall()]
                print(f"   现有索引: {indexes}")
                
                conn.commit()
                conn.close()
            except Exception as e:
                print(f"❌ {db_file} 索引创建失败: {e}")
        else:
            print(f"⚠️  {db_file} 不存在，跳过索引创建")

def check_database_schema():
    """
    检查数据库表结构
    """
    print("检查数据库表结构...")
    
    for i in range(0, 14):
        db_file = f"sina_{i:02d}.db"
        db_path = os.path.join(DB_BASE_PATH, db_file)
        
        if os.path.exists(db_path):
            try:
                conn = sqlite3.connect(db_path)
                cursor = conn.cursor()
                
                # 检查videos表是否存在
                cursor.execute("SELECT name FROM sqlite_master WHERE type='table' AND name='videos'")
                table_exists = cursor.fetchone()
                
                if table_exists:
                    # 获取表结构
                    cursor.execute("PRAGMA table_info(videos)")
                    columns = cursor.fetchall()
                    print(f"✅ {db_file} - videos表存在，包含{len(columns)}个列")
                    
                    # 检查是否有video_id列
                    video_id_exists = any(col[1] == 'video_id' for col in columns)
                    if not video_id_exists:
                        print(f"⚠️  {db_file} 中没有video_id列！")
                else:
                    print(f"❌ {db_file} 中没有videos表！")
                
                conn.close()
            except Exception as e:
                print(f"❌ 检查 {db_file} 表结构失败: {e}")

# ==================== 第六部分：配置和启动 ====================

def configure_app():
    """
    应用配置
    """
    # 设置请求超时
    requests.adapters.DEFAULT_RETRIES = 3
    
    # 设置线程池
    import concurrent.futures
    concurrent.futures.ThreadPoolExecutor._max_workers = 50
    
    print("应用配置完成")

if __name__ == '__main__':
    # 确保数据库目录存在
    if not os.path.exists(DB_BASE_PATH):
        print(f"重要：请创建目录 '{DB_BASE_PATH}'，并将 sina_xx.db 文件放入其中。")
        os.makedirs(DB_BASE_PATH, exist_ok=True)
    
    # 确保下载目录存在
    if not os.path.exists(DOWNLOAD_DIR):
        os.makedirs(DOWNLOAD_DIR, exist_ok=True)
    
    # 应用配置
    configure_app()
    
    # 检查数据库表结构
    check_database_schema()
    
    # 启动时创建索引
    create_indices_on_startup()

    print("新浪视频伪分段分析工具启动中...")
    print(f"数据库文件目录：{os.path.abspath(DB_BASE_PATH)}")
    print(f"下载文件目录：{os.path.abspath(DOWNLOAD_DIR)}")
    print("请确保已将 sina_00.db 至 sina_13.db 等文件放入数据库目录")
    print("访问 http://127.0.0.1:5000 使用完整功能")
    print("主要功能:")
    print("  1. 正向扫描 (起始ID + 半径) -> 发现伪分段视频")
    print("  2. 反向验证 (伪分段ID) -> 反查vid并验证CDN文件 (采用d.py策略)")
    print("  3. 异步下载 (CDN存在的文件) -> 支持多文件并发下载")
    print("  4. 数据库状态检查")
    print("  5. 自动创建数据库索引 (启动时执行)")
    print("  6. 批量反查验证 (无限制)")
    print("  7. 快速批量验证 (仅数据库)")
    
    # 启动服务器
    app.run(host='0.0.0.0', port=5000, debug=True, threaded=True)
