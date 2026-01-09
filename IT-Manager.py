#项目名称:局域网远程控制-IT管理控制端
#项目简介：主要用于公司局域网内部远程连接使用，IP地址直连
#时间:2025-01-08
#版本:v0.8
#作者:itzehao
#谢明:感谢豆包、小米
#---------------------------------------------------------------------------------------------

import socket
import json
import cv2
import numpy as np
import tkinter as tk
from tkinter import ttk, Entry, Button, Label, Frame, messagebox, Text, Scrollbar, END, Scale
import threading
import queue
from datetime import datetime
import platform
import time
import os

# ---------------------- 按需导入PIL（保留原有逻辑，增强异常处理） ----------------------
try:
    from PIL import Image, ImageTk
except ImportError as e:
    print(f"请安装PIL依赖：pip install pillow，错误详情：{e}")
    exit(1)

# ---------------------- 核心配置（优化版） ----------------------
MIN_WINDOW_WIDTH = 400
MIN_WINDOW_HEIGHT = 300
CHAT_AREA_WIDTH = 280
OPERATE_BAR_HEIGHT = 80
SCREEN_MARGIN = 50
ADJUST_THROTTLE = 0.3  # 进一步提高窗口调整节流
BUFFER_SIZE = 65536  # 增大缓冲区
FRAME_QUEUE_MAXSIZE = 3  # 增加队列缓冲，减少丢帧
DRAG_BASE_THROTTLE = 0.002  # 降低拖拽节流，提高响应速度
WINDOW_ADJUST_ONLY_ONCE = True
RENDER_FPS_LIMIT = 30  # 渲染帧率限制

# ---------------------- 跨平台屏幕可用尺寸获取 ----------------------
def get_screen_available_size(root):
    """获取用户主屏幕的可用尺寸"""
    try:
        screen_width = root.winfo_screenwidth()
        screen_height = root.winfo_screenheight()

        available_width = screen_width - SCREEN_MARGIN * 2
        available_height = screen_height - SCREEN_MARGIN * 2

        if platform.system() == "Windows":
            try:
                import ctypes
                class RECT(ctypes.Structure):
                    _fields_ = [("left", ctypes.c_long),
                                ("top", ctypes.c_long),
                                ("right", ctypes.c_long),
                                ("bottom", ctypes.c_long)]
                
                user32 = ctypes.windll.user32
                rect = RECT()
                user32.SystemParametersInfoW(0x0030, 0, ctypes.byref(rect), 0)
                available_width = rect.right - rect.left - SCREEN_MARGIN
                available_height = rect.bottom - rect.top - SCREEN_MARGIN
            except Exception as e:
                pass

        available_width = max(int(available_width), MIN_WINDOW_WIDTH)
        available_height = max(int(available_height), MIN_WINDOW_HEIGHT)
        return available_width, available_height
    except Exception as e:
        return 1280, 720

# ---------------------- 封装单个远程连接类（优化版） ----------------------
class RemoteClient:
    """单个被控端连接的封装类"""
    def __init__(self, target_ip, target_port=8888):
        self.TARGET_PORT = target_port
        self.BUFFER_SIZE = BUFFER_SIZE
        self.remote_scaling = 1.0
        self.remote_width = 0       
        self.remote_height = 0      
        self.canvas_ratio = 1.0
        self.is_connected = False
        self.remote_sys_info = None
        self.is_ratio_calculated = False
        self.HD_SCALE_FACTOR = 1.0

        # 连接核心资源
        self.client_socket = None
        self.frame_queue = queue.Queue(maxsize=FRAME_QUEUE_MAXSIZE)
        self.stop_event = threading.Event()
        self.cmd_lock = threading.Lock()

        # GUI组件绑定
        self.display_label = None
        self.chat_text = None
        self.chat_entry = None
        self.sys_info_panel = None
        self.hd_scale_slider = None
        self.hd_scale_entry = None
        self.main_window = None
        self.chat_send_btn = None

        # 线程对象
        self.recv_thread = None
        self.update_thread = None
        self.target_ip = target_ip

        # 窗口调整优化参数
        self.last_adjust_time = 0.0
        self.aspect_ratio = 16 / 9
        self.is_initial_adjust = False
        self.has_adjusted_window = False

        # 拖拽相关参数
        self.is_mouse_pressed = False
        self.pressed_mouse_button = 'left'
        self.last_drag_time = 0.0
        self.DRAG_THROTTLE = DRAG_BASE_THROTTLE

        # 渲染优化
        self.last_render_time = 0
        self.frame_count = 0
        self.last_stat_time = time.time()

        # 快捷键功能
        self.modifier_keys = {
            'ctrl': False,
            'shift': False,
            'alt': False,
            'win': False
        }
        
        # 符号按键优化
        self.keysym_to_char = {
            '0': '0', '1': '1', '2': '2', '3': '3', '4': '4',
            '5': '5', '6': '6', '7': '7', '8': '8', '9': '9',
            'a': 'a', 'b': 'b', 'c': 'c', 'd': 'd', 'e': 'e',
            'f': 'f', 'g': 'g', 'h': 'h', 'i': 'i', 'j': 'j',
            'k': 'k', 'l': 'l', 'm': 'm', 'n': 'n', 'o': 'o',
            'p': 'p', 'q': 'q', 'r': 'r', 's': 's', 't': 't',
            'u': 'u', 'v': 'v', 'w': 'w', 'x': 'x', 'y': 'y', 'z': 'z',
            'minus': '-', 'equal': '=', 'bracketleft': '[', 'bracketright': ']',
            'backslash': '\\', 'semicolon': ';', 'apostrophe': "'",
            'grave': '`', 'comma': ',', 'period': '.', 'slash': '/',
            'exclam': '!', 'at': '@', 'numbersign': '#', 'dollar': '$',
            'percent': '%', 'asciicircum': '^', 'ampersand': '&', 'asterisk': '*',
            'parenleft': '(', 'parenright': ')', 'underscore': '_', 'plus': '+',
            'braceleft': '{', 'braceright': '}', 'bar': '|', 'colon': ':',
            'quotedbl': '"', 'tilde': '~', 'less': '<', 'greater': '>', 'question': '?',
            'Meta_L': 'win', 'Meta_R': 'win'
        }
        
        self.shift_char_map = {
            '1': '!', '2': '@', '3': '#', '4': '$', '5': '%',
            '6': '^', '7': '&', '8': '*', '9': '(', '0': ')',
            '-': '_', '=': '+', '[': '{', ']': '}', '\\': '|',
            ';': ':', '\'': '"', '`': '~', ',': '<', '.': '>', '/': '?',
            'a': 'A', 'b': 'B', 'c': 'C', 'd': 'D', 'e': 'E',
            'f': 'F', 'g': 'G', 'h': 'H', 'i': 'I', 'j': 'J',
            'k': 'K', 'l': 'L', 'm': 'M', 'n': 'N', 'o': 'O',
            'p': 'P', 'q': 'Q', 'r': 'R', 's': 'S', 't': 'T',
            'u': 'U', 'v': 'V', 'w': 'W', 'x': 'X', 'y': 'Y', 'z': 'Z'
        }

    def auto_adjust_window_size(self):
        """窗口适配（优化版）"""
        if self.has_adjusted_window and WINDOW_ADJUST_ONLY_ONCE:
            return
        
        if not self.is_connected or not self.remote_sys_info:
            return
        
        try:
            self.remote_width = int(float(self.remote_sys_info.get('screen_width', 1280)))
            self.remote_height = int(float(self.remote_sys_info.get('screen_height', 720)))
        except (ValueError, TypeError):
            self.remote_width = 1280
            self.remote_height = 720
        
        if self.remote_width <= 0 or self.remote_height <= 0:
            self.remote_width = 1280
            self.remote_height = 720
        
        current_time = time.time()
        if current_time - self.last_adjust_time < ADJUST_THROTTLE:
            return
        self.last_adjust_time = current_time
        
        try:
            self.aspect_ratio = self.remote_width / self.remote_height
            if not (0.5 <= self.aspect_ratio <= 4.0):
                self.aspect_ratio = 16 / 9

            if not self.main_window or not self.main_window.winfo_exists():
                return
            available_screen_width, available_screen_height = get_screen_available_size(self.main_window)

            display_width = int(self.remote_width * self.HD_SCALE_FACTOR)
            display_height = int(self.remote_height * self.HD_SCALE_FACTOR)
            
            window_total_width = display_width + CHAT_AREA_WIDTH + 40
            window_total_height = display_height + OPERATE_BAR_HEIGHT + 40
            
            if window_total_width > available_screen_width:
                window_total_width = available_screen_width
                display_width = window_total_width - CHAT_AREA_WIDTH - 40
                display_height = int(display_width / self.aspect_ratio)
                window_total_height = display_height + OPERATE_BAR_HEIGHT + 40
            
            if window_total_height > available_screen_height:
                window_total_height = available_screen_height
                display_height = window_total_height - OPERATE_BAR_HEIGHT - 40
                display_width = int(display_height * self.aspect_ratio)
                window_total_width = display_width + CHAT_AREA_WIDTH + 40

            window_total_width = max(window_total_width, MIN_WINDOW_WIDTH)
            window_total_height = max(window_total_height, MIN_WINDOW_HEIGHT)

            if self.main_window.winfo_exists():
                self.main_window.after(0, lambda: self.main_window.geometry(f"{window_total_width}x{window_total_height}"))
                self.main_window.after(0, self.main_window.update_idletasks)

            if self.display_label and self.display_label.master.winfo_exists():
                self.display_label.master.after(0, lambda: self.display_label.master.config(
                    width=display_width, 
                    height=display_height
                ))
            
            self.is_initial_adjust = True
            self.is_ratio_calculated = True
            print(f"[{self.target_ip}] 已适配分辨率：{self.remote_width}x{self.remote_height} -> {window_total_width}x{window_total_height}")

        except Exception as e:
            print(f"[{self.target_ip}] 自动调整窗口大小失败：{e}")
            self.has_adjusted_window = True

    def adjust_hd_scale(self, value):
        """清晰度调节"""
        try:
            self.HD_SCALE_FACTOR = round(float(value), 1)
            if self.hd_scale_entry and self.hd_scale_entry.winfo_exists():
                self.hd_scale_entry.delete(0, END)
                self.hd_scale_entry.insert(0, str(self.HD_SCALE_FACTOR))
            if not self.has_adjusted_window:
                self.auto_adjust_window_size()
        except (ValueError, TypeError):
            pass

    def update_hd_scale_from_entry(self, event=None):
        """输入框调节清晰度"""
        try:
            if not self.hd_scale_entry or not self.hd_scale_entry.winfo_exists():
                return
            input_val = float(self.hd_scale_entry.get().strip())
            if 0.5 <= input_val <= 2.0:
                self.HD_SCALE_FACTOR = round(input_val, 1)
                if self.hd_scale_slider and self.hd_scale_slider.winfo_exists():
                    self.hd_scale_slider.set(self.HD_SCALE_FACTOR)
                if not self.has_adjusted_window:
                    self.auto_adjust_window_size()
            else:
                self.hd_scale_entry.delete(0, END)
                self.hd_scale_entry.insert(0, str(self.HD_SCALE_FACTOR))
                messagebox.showwarning("提示", "请输入0.5~2.0之间的数字！")
        except ValueError:
            if self.hd_scale_entry and self.hd_scale_entry.winfo_exists():
                self.hd_scale_entry.delete(0, END)
                self.hd_scale_entry.insert(0, str(self.HD_SCALE_FACTOR))
                messagebox.showwarning("提示", "请输入有效的数字！")

    def receive_frames(self):
        """帧接收线程（优化版）"""
        self.is_connected = True
        try:
            # 接收系统信息
            sys_info_len_data = self.client_socket.recv(4)
            if not sys_info_len_data:
                raise Exception("未获取到系统信息长度")
            sys_info_len = int.from_bytes(sys_info_len_data, 'big')
            sys_info_data = self.client_socket.recv(sys_info_len)
            if len(sys_info_data) != sys_info_len:
                raise Exception("系统信息数据不完整")
            sys_info_json = json.loads(sys_info_data.decode('utf-8', errors='ignore'))
            if sys_info_json.get('type') == 'sys_info':
                self.remote_sys_info = sys_info_json.get('data', {})
                if self.sys_info_panel and self.sys_info_panel.winfo_exists():
                    self.main_window.after(0, self.update_sys_info_panel)
                if self.main_window and self.main_window.winfo_exists():
                    self.main_window.after(0, self.auto_adjust_window_size)
            
            # 接收缩放比例
            scaling_len_data = self.client_socket.recv(4)
            if not scaling_len_data:
                raise Exception("未获取到缩放比例长度")
            scaling_len = int.from_bytes(scaling_len_data, 'big')
            scaling_data = self.client_socket.recv(scaling_len)
            if len(scaling_data) != scaling_len:
                raise Exception("缩放比例数据不完整")
            self.remote_scaling = json.loads(scaling_data.decode('utf-8', errors='ignore')).get('scaling', 1.0)
        except Exception as e:
            print(f"[{self.target_ip}] 初始化数据接收失败：{e}")
            self.remote_scaling = 1.0

        while not self.stop_event.is_set():
            try:
                self.client_socket.settimeout(0.5)
                data_len_data = self.client_socket.recv(4)
                if not data_len_data:
                    break
                data_len = int.from_bytes(data_len_data, 'big')
                
                # 分段接收数据
                data = b''
                remaining = data_len
                while remaining > 0 and not self.stop_event.is_set():
                    chunk = self.client_socket.recv(min(self.BUFFER_SIZE, remaining))
                    if not chunk:
                        break
                    data += chunk
                    remaining -= len(chunk)
                
                if len(data) != data_len or self.stop_event.is_set():
                    continue
                
                # 优先尝试解码为JSON（聊天消息）
                try:
                    json_data = json.loads(data.decode('utf-8', errors='strict'))
                    if json_data.get('type') == 'chat_msg' and self.chat_text and self.chat_text.winfo_exists():
                        self.chat_text.master.after(0, self.add_chat_msg, json_data)
                        continue
                except (json.JSONDecodeError, UnicodeDecodeError):
                    # 解码失败=二进制帧数据
                    try:
                        if self.frame_queue.full():
                            self.frame_queue.get_nowait()
                        self.frame_queue.put_nowait(data)
                    except queue.Full:
                        pass
            except socket.timeout:
                continue
            except Exception as e:
                print(f"[{self.target_ip}] 接收异常：{e}")
                break
        
        # 连接断开清理
        self.is_connected = False
        self.stop_event.set()
        self.is_mouse_pressed = False
        self.pressed_mouse_button = 'left'
        for key in self.modifier_keys:
            self.modifier_keys[key] = False
        while not self.frame_queue.empty():
            try:
                self.frame_queue.get_nowait()
            except queue.Empty:
                pass
        if self.display_label and self.display_label.winfo_exists():
            self.display_label.master.after(0, self.display_label.update_frame, None, self)

    def update_label_from_queue(self):
        """帧更新线程（优化版）"""
        if not self.display_label or not self.display_label.winfo_exists():
            return
        
        frame_interval = 1.0 / RENDER_FPS_LIMIT
        last_render_time = time.time()
        
        while not self.stop_event.is_set():
            try:
                # 优先从队列获取帧
                frame_data = self.frame_queue.get_nowait()
                
                # 渲染节流
                current_time = time.time()
                elapsed = current_time - last_render_time
                if elapsed < frame_interval:
                    # 跳过这一帧，直接处理下一帧
                    continue
                
                last_render_time = current_time
                self.display_label.update_frame(frame_data, self)
                
                # 性能统计
                self.frame_count += 1
                if current_time - self.last_stat_time >= 5.0:
                    fps = self.frame_count / (current_time - self.last_stat_time)
                    print(f"[{self.target_ip}] 渲染FPS: {fps:.1f}")
                    self.frame_count = 0
                    self.last_stat_time = current_time
                    
            except queue.Empty:
                time.sleep(0.001)
                continue
            except Exception as e:
                print(f"[{self.target_ip}] 帧更新异常：{e}")
                time.sleep(0.01)
                continue
        
        if self.display_label and self.display_label.winfo_exists():
            self.display_label.update_frame(None, self)

        

    def add_chat_msg(self, msg_data):
        """聊天消息更新"""
        if not self.chat_text or not self.chat_text.winfo_exists():
            return
        try:
            self.chat_text.config(state=tk.NORMAL)
            self.chat_text.insert(END, f"[{msg_data.get('time', '未知时间')}] {msg_data.get('sender', '未知发送者')}：{msg_data.get('content', '')}\n")
            self.chat_text.see(END)
            self.chat_text.config(state=tk.DISABLED)
        except Exception as e:
            print(f"[{self.target_ip}] 聊天消息更新失败：{e}")

    def send_chat_msg(self):
        """聊天消息发送"""
        if not self.is_connected:
            return
        if not self.chat_entry or not self.chat_entry.winfo_exists() or not self.chat_text or not self.chat_text.winfo_exists():
            return
        msg = self.chat_entry.get().strip()
        if not msg:
            return
        
        chat_data = {
            "type": "chat_msg",
            "sender": "IT同学",
            "content": msg,
            "time": datetime.now().strftime("%H:%M:%S")
        }
        
        try:
            self.send_cmd(chat_data)
            self.chat_text.config(state=tk.NORMAL)
            self.chat_text.insert(END, f"[{chat_data['time']}] 我：{msg}\n")
            self.chat_text.see(END)
            self.chat_text.config(state=tk.DISABLED)
            self.chat_entry.delete(0, END)
            if self.chat_entry.winfo_exists():
                self.chat_entry.focus_set()
        except Exception as e:
            messagebox.showerror("发送失败", f"[{self.target_ip}] 消息发送失败：{str(e)}")

    def update_sys_info_panel(self):
        """被控端信息更新"""
        if not self.sys_info_panel or not self.sys_info_panel.winfo_exists() or not self.remote_sys_info:
            return
        try:
            sys_text = f"📌 被控端信息（{self.target_ip}）\n"
            sys_text += f"IP：{self.remote_sys_info.get('local_ip', '未知')} | 主机：{self.remote_sys_info.get('hostname', '未知')}\n"
            sys_text += f"用户：{self.remote_sys_info.get('username', '未知')} | 系统：{self.remote_sys_info.get('system', '未知')}\n"
            sys_text += f"CPU：{self.remote_sys_info.get('cpu_count_physical', '未知')}核 | 内存：{self.remote_sys_info.get('mem_used', '未知')}/{self.remote_sys_info.get('mem_total', '未知')}GB\n"
            self.sys_info_panel.config(text=sys_text)
        except Exception as e:
            print(f"[{self.target_ip}] 系统信息面板更新失败：{e}")
            self.sys_info_panel.config(text=f"📌 被控端信息（{self.target_ip}）\n获取信息失败，请重新连接")

    def send_cmd(self, cmd):
        """发送指令（优化版）"""
        if not self.client_socket or not self.is_connected or self.stop_event.is_set():
            return
        try:
            with self.cmd_lock:
                cmd_data = json.dumps(cmd).encode('utf-8')
                self.client_socket.sendall(len(cmd_data).to_bytes(4, 'big'))
                self.client_socket.sendall(cmd_data)
        except Exception as e:
            print(f"[{self.target_ip}] 发送指令失败：{e}")
            self.disconnect()

    def on_mouse_press(self, event):
        """鼠标按下事件"""
        if not self.is_connected or not self.is_ratio_calculated:
            return
        if not self.display_label or not self.display_label.winfo_exists():
            return
        self.display_label.focus_set()
        self.is_mouse_pressed = True
        self.pressed_mouse_button = 'left' if event.num == 1 else 'right'
        
        try:
            rel_x = event.x - self.display_label.img_offset_x
            rel_y = event.y - self.display_label.img_offset_y
            scaled_w = int(self.remote_width * self.canvas_ratio * self.HD_SCALE_FACTOR)
            scaled_h = int(self.remote_height * self.canvas_ratio * self.HD_SCALE_FACTOR)
            if rel_x < 0 or rel_y < 0 or rel_x > scaled_w or rel_y > scaled_h:
                return
            remote_x = (rel_x / (self.canvas_ratio * self.HD_SCALE_FACTOR)) * self.remote_scaling
            remote_y = (rel_y / (self.canvas_ratio * self.HD_SCALE_FACTOR)) * self.remote_scaling
            
            self.send_cmd({
                'type': 'mouse_press',
                'x': int(remote_x),
                'y': int(remote_y),
                'button': self.pressed_mouse_button
            })
        except Exception as e:
            print(f"[{self.target_ip}] 鼠标按下事件处理失败：{e}")

    def on_mouse_release(self, event):
        """鼠标释放事件"""
        if not self.is_connected or not self.is_ratio_calculated or not self.is_mouse_pressed:
            return
        if not self.display_label or not self.display_label.winfo_exists():
            return
        self.is_mouse_pressed = False
        
        try:
            rel_x = event.x - self.display_label.img_offset_x
            rel_y = event.y - self.display_label.img_offset_y
            scaled_w = int(self.remote_width * self.canvas_ratio * self.HD_SCALE_FACTOR)
            scaled_h = int(self.remote_height * self.canvas_ratio * self.HD_SCALE_FACTOR)
            if rel_x < 0 or rel_y < 0 or rel_x > scaled_w or rel_y > scaled_h:
                return
            remote_x = (rel_x / (self.canvas_ratio * self.HD_SCALE_FACTOR)) * self.remote_scaling
            remote_y = (rel_y / (self.canvas_ratio * self.HD_SCALE_FACTOR)) * self.remote_scaling
            
            self.send_cmd({
                'type': 'mouse_release',
                'x': int(remote_x),
                'y': int(remote_y),
                'button': self.pressed_mouse_button
            })
        except Exception as e:
            print(f"[{self.target_ip}] 鼠标释放事件处理失败：{e}")

    def on_mouse_drag_move(self, event):
        """鼠标移动事件（优化版）"""
        if not self.is_connected or not self.is_ratio_calculated:
            return
        if not self.display_label or not self.display_label.winfo_exists():
            return
        
        current_time = time.time()
        if current_time - self.last_drag_time < self.DRAG_THROTTLE:
            return
        self.last_drag_time = current_time
        
        try:
            rel_x = event.x - self.display_label.img_offset_x
            rel_y = event.y - self.display_label.img_offset_y
            scaled_w = int(self.remote_width * self.canvas_ratio * self.HD_SCALE_FACTOR)
            scaled_h = int(self.remote_height * self.canvas_ratio * self.HD_SCALE_FACTOR)
            if rel_x < 0 or rel_y < 0 or rel_x > scaled_w or rel_y > scaled_h:
                return
            remote_x = (rel_x / (self.canvas_ratio * self.HD_SCALE_FACTOR)) * self.remote_scaling
            remote_y = (rel_y / (self.canvas_ratio * self.HD_SCALE_FACTOR)) * self.remote_scaling
            
            if not self.is_mouse_pressed:
                self.send_cmd({
                    'type': 'mouse_move',
                    'x': int(remote_x),
                    'y': int(remote_y)
                })
            else:
                self.send_cmd({
                    'type': 'mouse_drag',
                    'x': int(remote_x),
                    'y': int(remote_y),
                    'button': self.pressed_mouse_button
                })
        except Exception as e:
            print(f"[{self.target_ip}] 鼠标移动/拖拽事件处理失败：{e}")

    def map_tk_keysym_to_pyautogui(self, keysym):
        """按键映射"""
        key_map = {
            'Control_L': 'ctrl', 'Control_R': 'ctrl',
            'Shift_L': 'shift', 'Shift_R': 'shift',
            'Alt_L': 'alt', 'Alt_R': 'alt',
            'Win_L': 'win', 'Win_R': 'win',
            'Meta_L': 'win', 'Meta_R': 'win',
            'Delete': 'delete', 'Tab': 'tab', 'Escape': 'esc', 'Space': 'space',
            'Caps_Lock': 'capslock', 'Num_Lock': 'numlock', 'Scroll_Lock': 'scrolllock',
            'Insert': 'insert', 'Home': 'home', 'End': 'end',
            'Page_Up': 'pageup', 'Page_Down': 'pagedown',
            'Up': 'up', 'Down': 'down', 'Left': 'left', 'Right': 'right',
            'F1': 'f1', 'F2': 'f2', 'F3': 'f3', 'F4': 'f4', 'F5': 'f5',
            'F6': 'f6', 'F7': 'f7', 'F8': 'f8', 'F9': 'f9', 'F10': 'f10',
            'F11': 'f11', 'F12': 'f12'
        }
        return key_map.get(keysym, keysym.lower())

    def get_pressed_character(self, keysym):
        """根据Shift状态获取字符"""
        char = self.keysym_to_char.get(keysym, None)
        if char is None:
            char = keysym.lower() if len(keysym) == 1 else None
        if char is None:
            return None
        
        if self.modifier_keys.get('shift', False):
            char = self.shift_char_map.get(char, char)
        
        return char

    def on_key_press(self, event):
        """键盘按下事件"""
        if not self.display_label or self.display_label != self.main_window.focus_get():
            return
        if not self.is_connected or not self.is_ratio_calculated:
            return
        
        try:
            keysym = event.keysym
            key = self.map_tk_keysym_to_pyautogui(keysym)
            
            if key in self.modifier_keys:
                self.modifier_keys[key] = True
                self.send_cmd({'type': 'key_down', 'key': key})
                return
            
            char = self.get_pressed_character(keysym)
            if char is not None:
                self.send_cmd({
                    'type': 'key_input',
                    'key': char,
                    'is_character': True
                })
                return
            
            self.send_cmd({'type': 'key_input', 'key': key, 'is_character': False})
        except Exception as e:
            print(f"[{self.target_ip}] 键盘按下事件处理失败：{e}")

    def on_key_release(self, event):
        """键盘释放事件"""
        if not self.display_label or self.display_label != self.main_window.focus_get():
            return
        if not self.is_connected or not self.is_ratio_calculated:
            return
        
        try:
            keysym = event.keysym
            key = self.map_tk_keysym_to_pyautogui(keysym)
            
            if key in self.modifier_keys:
                self.modifier_keys[key] = False
                self.send_cmd({'type': 'key_up', 'key': key})
                return
        except Exception as e:
            print(f"[{self.target_ip}] 键盘释放事件处理失败：{e}")

    def bind_controls(self):
        """绑定键鼠控制"""
        if not self.display_label or not self.display_label.winfo_exists():
            return

        # 鼠标事件
        self.display_label.bind('<Motion>', self.on_mouse_drag_move)
        self.display_label.bind('<ButtonPress-1>', self.on_mouse_press)
        self.display_label.bind('<ButtonPress-3>', self.on_mouse_press)
        self.display_label.bind('<ButtonRelease-1>', self.on_mouse_release)
        self.display_label.bind('<ButtonRelease-3>', self.on_mouse_release)
        self.display_label.bind('<MouseWheel>', self.on_mouse_wheel)
        self.display_label.bind('<Button-4>', lambda e: self.on_mouse_wheel(tk.Event(e.widget, delta=120)))
        self.display_label.bind('<Button-5>', lambda e: self.on_mouse_wheel(tk.Event(e.widget, delta=-120)))

        # 键盘事件
        self.display_label.bind('<KeyPress>', self.on_key_press)
        self.display_label.bind('<KeyRelease>', self.on_key_release)

        self.display_label.focus_set()

    def on_mouse_wheel(self, event):
        """鼠标滚轮事件"""
        if not self.is_connected:
            return
        try:
            direction = 'up' if event.delta > 0 else 'down'
            distance = (abs(event.delta) // 120) * 6
            self.send_cmd({'type': 'mouse_wheel', 'direction': direction, 'distance': distance})
        except Exception as e:
            print(f"[{self.target_ip}] 鼠标滚轮事件处理失败：{e}")

    def connect(self):
        """建立连接"""
        self.stop_event.clear()
        self.remote_width = 0
        self.remote_height = 0
        self.is_ratio_calculated = False
        self.HD_SCALE_FACTOR = 1.0
        self.last_adjust_time = 0.0
        self.is_initial_adjust = False
        self.has_adjusted_window = False
        
        self.is_mouse_pressed = False
        self.pressed_mouse_button = 'left'
        for key in self.modifier_keys:
            self.modifier_keys[key] = False

        if self.display_label and self.display_label.winfo_exists():
            self.display_label.update_frame(None, self)
        if self.hd_scale_slider and self.hd_scale_slider.winfo_exists() and self.hd_scale_entry and self.hd_scale_entry.winfo_exists():
            self.hd_scale_slider.set(1.0)
            self.hd_scale_entry.delete(0, END)
            self.hd_scale_entry.insert(0, "1.0")

        try:
            self.client_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self.client_socket.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
            self.client_socket.setsockopt(socket.SOL_SOCKET, socket.SO_SNDBUF, self.BUFFER_SIZE * 2)
            self.client_socket.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, self.BUFFER_SIZE * 2)
            self.client_socket.setsockopt(socket.SOL_SOCKET, socket.SO_KEEPALIVE, 1)
            
            self.client_socket.settimeout(8.0)
            self.client_socket.connect((self.target_ip, self.TARGET_PORT))
            self.client_socket.settimeout(None)

            self.recv_thread = threading.Thread(target=self.receive_frames, args=(), daemon=True, name=f"RecvThread-{self.target_ip}")
            self.update_thread = threading.Thread(target=self.update_label_from_queue, args=(), daemon=True, name=f"UpdateThread-{self.target_ip}")
            self.recv_thread.start()
            self.update_thread.start()

            self.bind_controls()

            print(f"[{self.target_ip}] 已成功连接到 {self.target_ip}:{self.TARGET_PORT}")
            return True
        except socket.timeout:
            messagebox.showerror("连接超时", f"[{self.target_ip}] 连接超时：\n1. 检查被控端是否运行\n2. 检查IP地址是否正确\n3. 检查防火墙是否放行8888端口")
            self.client_socket = None
            return False
        except Exception as e:
            messagebox.showerror("连接失败", f"[{self.target_ip}] 连接失败：{str(e)}")
            self.client_socket = None
            return False

    def disconnect(self):
        """断开连接"""
        if not self.is_connected:
            return
        self.stop_event.set()
        
        try:
            if self.is_mouse_pressed and self.client_socket:
                self.send_cmd({
                    'type': 'mouse_release',
                    'x': 0,
                    'y': 0,
                    'button': self.pressed_mouse_button
                })
            for key, is_pressed in self.modifier_keys.items():
                if is_pressed and self.client_socket:
                    self.send_cmd({'type': 'key_up', 'key': key})
        except:
            pass

        if self.client_socket:
            try:
                self.client_socket.shutdown(socket.SHUT_RDWR)
                self.client_socket.close()
            except:
                pass
            self.client_socket = None

        if self.recv_thread and self.recv_thread.is_alive():
            try:
                self.recv_thread.join(timeout=1.0)
            except:
                pass
        if self.update_thread and self.update_thread.is_alive():
            try:
                self.update_thread.join(timeout=1.0)
            except:
                pass

        while not self.frame_queue.empty():
            try:
                self.frame_queue.get_nowait()
            except queue.Empty:
                pass

        self.is_connected = False
        self.remote_sys_info = None
        self.recv_thread = None
        self.update_thread = None

        print(f"[{self.target_ip}] 连接已断开，所有资源清理完成")

# ---------------------- 高清渲染Label（优化版） ----------------------
class HDNoFlickerLabel(Label):
    def __init__(self, master, **kwargs):
        super().__init__(master, **kwargs)
        self._img_tk = None
        self.img_offset_x = 0
        self.img_offset_y = 0
        self.focus_set()
        self.bind('<Visibility>', lambda e: self.focus_set())
        self.config(takefocus=True)
        self.bind('<Button-1>', lambda e: self.focus_set())

    def update_frame(self, frame_data, client: RemoteClient = None):
        """高清渲染（优化版）"""
        if frame_data is None:
            self.config(text="连接已断开", font=("Arial", 12), bg="black", fg="white")
            self.img_offset_x = 0
            self.img_offset_y = 0
            self._img_tk = None
            return
        
        if not client or not client.is_connected:
            return
        
        try:
            nparr = np.frombuffer(frame_data, np.uint8)
            frame = cv2.imdecode(nparr, cv2.IMREAD_COLOR | cv2.IMREAD_IGNORE_ORIENTATION)
            if frame is None:
                return
            
            if client.remote_width == 0 or client.remote_height == 0:
                try:
                    client.remote_height, client.remote_width = frame.shape[:2]
                    print(f"[{client.target_ip}] 从帧中提取分辨率：{client.remote_width}x{client.remote_height}")
                    if not client.has_adjusted_window and client.main_window and client.main_window.winfo_exists():
                        client.main_window.after(0, client.auto_adjust_window_size)
                except:
                    client.remote_width = 1280
                    client.remote_height = 720
            
            final_scale = client.canvas_ratio * client.HD_SCALE_FACTOR
            new_w = int(client.remote_width * final_scale)
            new_h = int(client.remote_height * final_scale)
            
            self.img_offset_x = max(0, (self.winfo_width() - new_w) // 2) if self.winfo_width() > 0 else 0
            self.img_offset_y = max(0, (self.winfo_height() - new_h) // 2) if self.winfo_height() > 0 else 0
            
            # 使用更快的缩放算法
            frame_resized = cv2.resize(
                frame, 
                (new_w, new_h), 
                interpolation=cv2.INTER_LINEAR  # 线性插值，速度较快
            )
            frame_rgb = cv2.cvtColor(frame_resized, cv2.COLOR_BGR2RGB)
            img = Image.fromarray(frame_rgb)
            
            self._img_tk = ImageTk.PhotoImage(image=img)
            self.config(image=self._img_tk, text="", bg="black")
            self.image = self._img_tk
        except Exception as e:
            print(f"[{client.target_ip}] 高清渲染失败：{e}")

# ---------------------- 独立连接窗口（优化版） ----------------------
class SingleRemoteWindow(tk.Toplevel):
    """单个被控端连接的独立窗口"""
    def __init__(self, parent, target_ip):
        super().__init__(parent)
        self.target_ip = target_ip
        self.title(f"局域网远程控制 - {target_ip}")
        self.geometry(f"{MIN_WINDOW_WIDTH}x{MIN_WINDOW_HEIGHT}")
        self.resizable(True, True)

        # 创建RemoteClient实例并绑定当前窗口
        self.remote_client = RemoteClient(target_ip)
        self.remote_client.main_window = self

        # 绑定窗口关闭事件
        self.protocol("WM_DELETE_WINDOW", self.on_window_close)

        # 初始化独立窗口的GUI布局
        self.init_window_gui()

        # 自动尝试连接
        self.connect_to_slave()

        # 跨平台高DPI适配
        if platform.system() == "Windows":
            try:
                import ctypes
                ctypes.windll.shcore.SetProcessDpiAwareness(2)
                ctypes.windll.user32.SetProcessDPIAware()
            except:
                pass
        else:
            try:
                self.tk.call('tk', 'scaling', 1.5)
            except:
                pass

    def init_window_gui(self):
        """初始化独立窗口的GUI布局"""
        # 窗口顶部：清晰度调节栏
        top_frame = Frame(self)
        top_frame.pack(pady=5, fill=tk.X, padx=10)

        Label(top_frame, text="清晰度：", font=("Arial", 10)).pack(side=tk.LEFT, padx=2)
        hd_scale_slider = Scale(top_frame, from_=0.5, to=2.0, resolution=0.1, orient=tk.HORIZONTAL,
                                command=self.remote_client.adjust_hd_scale, font=("Arial", 8), length=80, width=15)
        hd_scale_slider.set(1.0)
        hd_scale_slider.pack(side=tk.LEFT, padx=2)
        self.remote_client.hd_scale_slider = hd_scale_slider

        hd_scale_entry = Entry(top_frame, width=5, font=("Arial", 10))
        hd_scale_entry.insert(0, "1.0")
        hd_scale_entry.pack(side=tk.LEFT, padx=2)
        hd_scale_entry.bind('<Return>', self.remote_client.update_hd_scale_from_entry)
        hd_scale_entry.bind('<FocusOut>', self.remote_client.update_hd_scale_from_entry)
        self.remote_client.hd_scale_entry = hd_scale_entry

        # 窗口中间：核心显示+聊天区域
        main_frame = Frame(self)
        main_frame.pack(pady=5, fill=tk.BOTH, expand=True, padx=10)

        # 远程桌面显示区
        display_frame = Frame(main_frame, bg="black")
        display_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=2)
        display_label = HDNoFlickerLabel(display_frame, bg="black", text="等待连接...", font=("Arial", 12), fg="white")
        display_label.pack(fill=tk.BOTH, expand=True)
        self.remote_client.display_label = display_label

        # 聊天区域
        chat_frame = Frame(main_frame, width=CHAT_AREA_WIDTH, bd=1, relief=tk.GROOVE)
        chat_frame.pack(side=tk.RIGHT, fill=tk.BOTH, padx=2)
        chat_frame.pack_propagate(False)

        # 被控端信息面板
        sys_info_panel = Label(chat_frame, text="📌 被控端信息\n等待连接...", font=("Arial", 8),
                               justify=tk.LEFT, bg="#f0f0f0", bd=1, relief=tk.SUNKEN, wraplength=260)
        sys_info_panel.pack(pady=3, fill=tk.X, padx=3)
        self.remote_client.sys_info_panel = sys_info_panel

        # 聊天标题
        Label(chat_frame, text="聊天", font=("Arial", 9, "bold")).pack(anchor=tk.W, padx=3)
        
        # 聊天记录
        chat_scroll = Scrollbar(chat_frame)
        chat_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        chat_text = Text(chat_frame, height=10, state=tk.DISABLED, yscrollcommand=chat_scroll.set, font=("Arial", 8))
        chat_text.pack(pady=3, fill=tk.BOTH, expand=True, padx=3)
        chat_scroll.config(command=chat_text.yview)
        self.remote_client.chat_text = chat_text
        
        # 聊天输入
        chat_input_frame = Frame(chat_frame)
        chat_input_frame.pack(pady=3, fill=tk.X, padx=3)
        chat_entry = Entry(chat_input_frame, font=("Arial", 8), takefocus=True)
        chat_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=2)
        def send_chat_handler(event=None):
            self.remote_client.send_chat_msg()
        chat_entry.bind('<Return>', send_chat_handler)
        self.remote_client.chat_entry = chat_entry

        send_btn = Button(chat_input_frame, text="发送", font=("Arial", 8), width=4, 
                          command=self.remote_client.send_chat_msg)
        send_btn.pack(side=tk.RIGHT, padx=2)
        self.remote_client.chat_send_btn = send_btn

        # 初始聚焦显示区
        display_label.focus_set()

    def connect_to_slave(self):
        """尝试连接被控端"""
        self.remote_client.connect()

    def on_window_close(self):
        """窗口关闭事件 - 优化版：只清理子窗口资源"""
        print(f"[{self.target_ip}] 开始关闭子窗口...")
        
        # 1. 先断开远程连接，清理网络资源
        if hasattr(self, 'remote_client') and self.remote_client:
            try:
                self.remote_client.disconnect()
                print(f"[{self.target_ip}] 远程连接资源已清理")
            except Exception as e:
                print(f"[{self.target_ip}] 清理远程连接资源时出错: {e}")
        
        # 2. 销毁窗口（这会自动清理GUI组件）
        try:
            self.destroy()
            print(f"[{self.target_ip}] 窗口组件已销毁")
        except Exception as e:
            print(f"[{self.target_ip}] 销毁窗口时出错: {e}")
        
        print(f"[{self.target_ip}] 子窗口关闭完成，资源清理完毕")
        
        # 3. 重要：不再检查其他窗口或退出程序，让主窗口控制程序生命周期
        # 子窗口只负责清理自己的资源

# ---------------------- 控制端主窗口（优化版） ----------------------
class RemoteControlMainWindow:
    def __init__(self, root):
        self.root = root
        self.root.title("局域网远程控制")
        self.root.geometry("450x100")
        self.root.resizable(False, False)

        # 主窗口：仅保留IP输入和新建连接按钮
        main_frame = Frame(self.root, padx=20, pady=30)
        main_frame.pack(fill=tk.BOTH, expand=True)

        # IP输入区域
        ip_frame = Frame(main_frame)
        ip_frame.pack(side=tk.LEFT, padx=5)
        Label(ip_frame, text="被控端IP：", font=("Arial", 12)).pack(side=tk.LEFT, padx=5)
        self.ip_entry = Entry(ip_frame, width=20, font=("Arial", 12))
        self.ip_entry.pack(side=tk.LEFT, padx=5)
        self.ip_entry.insert(0, "")

        # 新建连接按钮
        Button(main_frame, text="新建连接窗口", font=("Arial", 12), width=20,
               command=self.create_new_remote_window).pack(pady=10)

        # 跨平台高DPI适配
        if platform.system() == "Windows":
            try:
                import ctypes
                ctypes.windll.shcore.SetProcessDpiAwareness(2)
                ctypes.windll.user32.SetProcessDPIAware()
            except:
                pass
        
        # 绑定主窗口关闭事件
        self.root.protocol("WM_DELETE_WINDOW", self.on_main_window_close)

    def on_main_window_close(self):
        """主窗口关闭事件 - 优化版：清理所有资源"""
        print("主窗口开始关闭，清理所有资源...")
        
        # 1. 先关闭所有子窗口，确保每个子窗口清理自己的资源
        try:
            # 获取所有子窗口
            child_windows = [w for w in self.root.winfo_children() if isinstance(w, tk.Toplevel)]
            print(f"发现 {len(child_windows)} 个子窗口，开始逐一关闭...")
            
            for i, child in enumerate(child_windows):
                try:
                    if hasattr(child, 'on_window_close'):
                        # 调用子窗口的关闭方法，确保资源清理
                        child.on_window_close()
                    else:
                        # 如果没有自定义关闭方法，直接销毁
                        child.destroy()
                    print(f"子窗口 {i+1}/{len(child_windows)} 已关闭")
                except Exception as e:
                    print(f"关闭子窗口时出错: {e}")
                    try:
                        child.destroy()
                    except:
                        pass
            
            # 等待一下确保所有资源清理完成
            time.sleep(0.2)
            print("所有子窗口已关闭，资源清理完成")
            
        except Exception as e:
            print(f"清理子窗口时出错: {e}")
        
        # 2. 清理主窗口自身资源（如果有）
        try:
            # 清理主窗口的GUI组件
            self.root.quit()
            self.root.destroy()
            print("主窗口GUI组件已销毁")
        except Exception as e:
            print(f"销毁主窗口时出错: {e}")
        
        # 3. 最终退出程序
        print("主窗口关闭完成，程序即将退出...")
        try:
            # 给系统一点时间完成清理
            time.sleep(0.1)
            # 使用更温和的退出方式
            os._exit(0)
        except:
            os._exit(0)

    def create_new_remote_window(self):
        """创建新的独立连接窗口"""
        target_ip = self.ip_entry.get().strip()
        if not target_ip:
            messagebox.showwarning("提示", "请输入被控端IP地址！")
            return
        ip_parts = target_ip.split('.')
        if len(ip_parts) != 4:
            messagebox.showwarning("提示", "请输入有效的IPv4地址！")
            return
        try:
            for part in ip_parts:
                int(part)
            SingleRemoteWindow(self.root, target_ip)
        except ValueError:
            messagebox.showwarning("提示", "请输入有效的IPv4地址！")

# ---------------------- 程序入口 ----------------------
if __name__ == "__main__":
    try:
        root = tk.Tk()
        app = RemoteControlMainWindow(root)
        root.mainloop()
    except Exception as e:
        print(f"程序运行异常：{e}")
        messagebox.showerror("致命错误", f"程序运行失败：{str(e)}\n请检查依赖是否安装完整")
