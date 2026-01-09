#项目名称:局域网远程控制-用户侧被控端（修复版）
#项目简介：主要用于公司局域网内部远程连接使用，IP地址直连
#时间:2025-01-08
#版本:v0.8
#作者:itzehao
#谢明:感谢豆包、小米
#------------------------------------------------------------------------------------------------

import socket
import json
import mss
import cv2
import numpy as np
import threading
import tkinter as tk
from tkinter import Label, Menu, messagebox, Frame, Button, Text, Entry, Scrollbar, END, Toplevel
import platform
import os
import ctypes
from datetime import datetime
import queue
import winreg
import pystray
from PIL import Image as PILImage, ImageDraw
import sys
import psutil
import getpass
import time
# ---------------------- 核心配置（优化版） ----------------------
LISTEN_PORT = 8888
JPEG_QUALITY = 55  # 降低质量以提高传输效率
BUFFER_SIZE = 32768  # 增大缓冲区
FPS_LIMIT = 25  # 降低FPS以减少CPU占用
FRAME_QUEUE_SIZE = 2  # 增加队列缓冲
MOUSE_THROTTLE = 0.03  # 降低节流延迟
SCROLL_SPEED_MULTIPLIER = 3
AUTO_START_KEY = winreg.HKEY_CURRENT_USER
AUTO_START_PATH = "Software\\Microsoft\\Windows\\CurrentVersion\\Run"
AUTO_START_NAME = "RemoteControlSlave"

# ---------------------- 全局变量 ----------------------
tray_icon = None
root = None
msg_notify_window = None
current_active_connection = None
USE_WIN32 = False
MODIFIER_STATE = {'ctrl': False, 'shift': False, 'alt': False, 'win': False}

# ---------------------- 连接隔离类（优化版） ----------------------
class SlaveConnection:
    """单个控制端连接的隔离类"""
    def __init__(self, conn, addr, chat_text, chat_entry):
        self.conn = conn
        self.addr = addr
        self.is_connected = True
        
        # 核心资源（优化队列大小）
        self.stop_event = threading.Event()
        self.frame_queue = queue.Queue(maxsize=FRAME_QUEUE_SIZE)
        self.last_frame = None
        self.last_frame_time = 0
        self.last_mouse_time = 0.0
        
        # 聊天组件
        self.chat_text = chat_text
        self.chat_entry = chat_entry
        
        # 拖拽状态
        self.is_mouse_dragging = False
        self.dragging_button = 'left'
        
        # 线程对象
        self.cmd_thread = None
        self.capture_thread = None
        self.send_thread = None
        
        # 性能统计
        self.frame_count = 0
        self.last_stat_time = time.time()

    def disconnect(self, graceful=True):
        """断开当前连接，清理资源（优化版）"""
        global current_active_connection
        if not self.is_connected:
            return
        
        print(f"[{self.addr}] 开始断开连接...")
        
        # 1. 设置停止事件，通知所有线程退出
        self.stop_event.set()
        
        # 2. 释放拖拽状态
        try:
            if self.is_mouse_dragging:
                import pyautogui
                pyautogui.mouseUp(button=self.dragging_button)
                self.is_mouse_dragging = False
        except:
            pass
        
        # 3. 释放所有按键状态
        try:
            import pyautogui
            for key, is_pressed in MODIFIER_STATE.items():
                if is_pressed:
                    pyautogui.keyUp(key)
                    MODIFIER_STATE[key] = False
        except:
            pass
        
        # 4. 关闭Socket（先shutdown确保立即中断阻塞操作）
        if self.conn:
            try:
                # 立即中断所有阻塞的recv/send操作
                self.conn.shutdown(socket.SHUT_RDWR)
            except:
                pass
            try:
                self.conn.close()
            except Exception as e:
                print(f"[{self.addr}] 关闭Socket失败：{e}")
            self.conn = None
        
        # 5. 等待线程退出（增加等待时间，确保彻底清理）
        threads = [
            (self.cmd_thread, "指令处理"),
            (self.capture_thread, "截图"),
            (self.send_thread, "发送")
        ]
        
        for thread, name in threads:
            if thread and thread.is_alive():
                try:
                    # 等待更长时间，确保线程完全退出
                    thread.join(timeout=2.0)
                    if thread.is_alive():
                        print(f"[{self.addr}] 警告：{name}线程未能正常退出")
                    else:
                        print(f"[{self.addr}] {name}线程已正常退出")
                except Exception as e:
                    print(f"[{self.addr}] 等待{name}线程退出异常：{e}")
        
        # 6. 清理队列
        while not self.frame_queue.empty():
            try:
                self.frame_queue.get_nowait()
            except queue.Empty:
                break
        
        # 7. 重置状态
        self.is_connected = False
        self.last_frame = None
        
        # 8. 更新全局状态
        if current_active_connection == self:
            current_active_connection = None
            if self.chat_text and self.chat_text.winfo_exists():
                root.after(0, lambda: self._clear_chat_ui())
        
        print(f"[{self.addr}] 连接已完全断开，资源清理完成")

    def _clear_chat_ui(self):
        """清空聊天UI（线程安全）"""
        if not self.chat_text.winfo_exists():
            return
        try:
            self.chat_text.config(state=tk.NORMAL)
            self.chat_text.insert(END, f"\n【提示】IT同学已完成操作断开连接，可以关闭软件\n后续若有其他需要可以在Athena.51talk.com提交工单或发送邮件到bjit@51talk.com获取IT同学的支持\n")
            self.chat_text.config(state=tk.DISABLED)
            if self.chat_entry.winfo_exists():
                self.chat_entry.delete(0, END)
                self.chat_entry.config(state=tk.NORMAL)
        except Exception as e:
            print(f"清空聊天UI失败：{e}")

# ---------------------- 键鼠API初始化 ----------------------
def init_mouse_keyboard_api():
    global USE_WIN32, MODIFIER_STATE
    USE_WIN32 = False
    import pyautogui
    pyautogui.FAILSAFE = False
    pyautogui.PAUSE = 0.001
    MODIFIER_STATE = {'ctrl': False, 'shift': False, 'alt': False, 'win': False}
    print("已加载pyautogui API（优化模式）")

# ---------------------- 开机自启 ----------------------
def get_script_path():
    try:
        if getattr(sys, 'frozen', False):
            return sys.executable
        else:
            return os.path.abspath(__file__)
    except Exception as e:
        print(f"获取脚本路径失败：{e}")
        return ""

def set_auto_start():
    try:
        script_path = get_script_path()
        if not script_path:
            return False
        key = winreg.OpenKey(AUTO_START_KEY, AUTO_START_PATH, 0, winreg.KEY_SET_VALUE)
        winreg.SetValueEx(key, AUTO_START_NAME, 0, winreg.REG_SZ, f'"{script_path}" --hidden')
        winreg.CloseKey(key)
        return True
    except Exception as e:
        print(f"设置开机自启失败：{e}")
        return False

def cancel_auto_start():
    try:
        key = winreg.OpenKey(AUTO_START_KEY, AUTO_START_PATH, 0, winreg.KEY_SET_VALUE)
        winreg.DeleteValue(key, AUTO_START_NAME)
        winreg.CloseKey(key)
        return True
    except Exception as e:
        print(f"取消开机自启失败：{e}")
        return False

def check_auto_start():
    try:
        key = winreg.OpenKey(AUTO_START_KEY, AUTO_START_PATH, 0, winreg.KEY_READ)
        winreg.QueryValueEx(key, AUTO_START_NAME)
        winreg.CloseKey(key)
        return True
    except FileNotFoundError:
        return False
    except Exception as e:
        print(f"检查开机自启状态失败：{e}")
        return False

# ---------------------- 系统托盘 ----------------------
def create_tray_icon():
    try:
        icon_size = 16
        image_normal = PILImage.new('RGB', (icon_size, icon_size), (64, 64, 64))
        draw_normal = ImageDraw.Draw(image_normal)
        draw_normal.text((2, 2), "RC", fill=(255, 255, 255))
        image_notify = PILImage.new('RGB', (icon_size, icon_size), (255, 0, 0))
        draw_notify = ImageDraw.Draw(image_notify)
        draw_notify.text((2, 2), "RC", fill=(255, 255, 255))
        
        auto_start_status = check_auto_start()
        menu = pystray.Menu(
            pystray.MenuItem("显示界面", show_main_window),
            pystray.MenuItem("开机自启" if not auto_start_status else "取消开机自启",
                             lambda: toggle_auto_start(menu)),
            pystray.MenuItem("退出", lambda: exit_app())
        )
        global tray_icon
        tray_icon = pystray.Icon("RemoteControlSlave", image_normal, "远程被控端", menu)
        tray_icon.normal_image = image_normal
        tray_icon.notify_image = image_notify
        return tray_icon
    except Exception as e:
        print(f"创建托盘图标失败：{e}")
        return None

def blink_tray_icon():
    if not tray_icon:
        return
    def blink():
        try:
            for i in range(4):  # 减少闪烁次数
                tray_icon.icon = tray_icon.notify_image if i % 2 == 0 else tray_icon.normal_image
                time.sleep(0.2)
            tray_icon.icon = tray_icon.normal_image
        except Exception as e:
            print(f"托盘闪烁失败：{e}")
    threading.Thread(target=blink, daemon=True).start()

def show_msg_notify(sender, content, time_str):
    global msg_notify_window
    try:
        if msg_notify_window and msg_notify_window.winfo_exists():
            msg_notify_window.destroy()
        
        def create_notify():
            global msg_notify_window
            msg_notify_window = Toplevel(root)
            msg_notify_window.title("新消息提醒")
            msg_notify_window.geometry("300x100")
            msg_notify_window.attributes('-topmost', True)
            msg_notify_window.attributes('-toolwindow', True)
            msg_notify_window.resizable(False, False)
            
            Label(msg_notify_window, text=f"来自 {sender} 的消息", font=("Arial", 10, "bold")).pack(pady=5)
            Label(msg_notify_window, text=content, wraplength=280).pack(pady=5)
            msg_notify_window.after(3000, lambda: msg_notify_window.destroy())
        root.after(0, create_notify)
    except Exception as e:
        print(f"显示消息提醒失败：{e}")

def toggle_auto_start(menu):
    try:
        current_status = check_auto_start()
        success = cancel_auto_start() if current_status else set_auto_start()
        if success:
            new_text = "开机自启" if not check_auto_start() else "取消开机自启"
            menu.items[1].text = new_text
            tray_icon.menu = menu
            messagebox.showinfo("提示", f"已{'开启' if not current_status else '关闭'}开机自启")
        else:
            messagebox.showwarning("提示", f"{'开启' if not current_status else '关闭'}开机自启失败")
    except Exception as e:
        print(f"切换自启状态失败：{e}")
        messagebox.showerror("错误", f"操作失败：{str(e)}")

def show_main_window():
    try:
        global root
        root.deiconify()
        root.lift()
        root.focus_force()
        if current_active_connection and current_active_connection.chat_entry:
            current_active_connection.chat_entry.focus_set()
    except Exception as e:
        print(f"显示窗口失败：{e}")

def hide_main_window():
    try:
        global root
        root.withdraw()
    except Exception as e:
        print(f"隐藏窗口失败：{e}")

def exit_app():
    """优化的退出函数"""
    try:
        global tray_icon, root, msg_notify_window, current_active_connection
        
        print("开始退出程序...")
        
        # 1. 断开当前连接
        if current_active_connection:
            try:
                current_active_connection.disconnect(graceful=True)
            except Exception as e:
                print(f"断开连接时出错：{e}")
        
        # 2. 关闭消息窗口
        if msg_notify_window and msg_notify_window.winfo_exists():
            try:
                msg_notify_window.destroy()
            except:
                pass
        
        # 3. 停止托盘图标
        if tray_icon:
            try:
                tray_icon.stop()
            except:
                pass
        
        # 4. 关闭主窗口
        if root:
            try:
                root.quit()
                root.destroy()
            except:
                pass
        
        # 5. 等待一下，确保资源清理
        time.sleep(0.1)
        
        # 6. 完全退出程序
        print("程序即将完全退出...")
        os._exit(0)
            
    except Exception as e:
        print(f"退出失败：{e}")
        # 无论如何都要强制退出，避免程序挂起
        os._exit(1)

# ---------------------- 系统信息 ----------------------
def get_screen_scaling():
    try:
        if platform.system() == "Windows":
            ctypes.windll.user32.SetProcessDPIAware()
            dpi = ctypes.windll.user32.GetDpiForSystem()
            return dpi / 96.0
        return 1.0
    except Exception as e:
        print(f"获取屏幕缩放失败：{e}")
        return 1.0

def get_local_ip():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        ip = s.getsockname()[0]
        s.close()
        return ip
    except Exception as e:
        print(f"获取IP失败：{e}")
        return "127.0.0.1"

def get_system_info():
    try:
        sys_info = {
            "hostname": platform.node(),
            "username": getpass.getuser(),
            "system": platform.system(),
            "system_version": platform.version(),
            "os_release": platform.release(),
            "machine": platform.machine(),
            "local_ip": get_local_ip(),
            "screen_scaling": get_screen_scaling(),
        }
        
        try:
            sys_info["cpu_count_physical"] = psutil.cpu_count(logical=False) or "未知"
            sys_info["cpu_count_logical"] = psutil.cpu_count(logical=True) or "未知"
            sys_info["cpu_percent"] = psutil.cpu_percent(interval=0.1)
            
            mem = psutil.virtual_memory()
            sys_info["mem_total"] = round(mem.total / (1024**3), 2)
            sys_info["mem_used"] = round(mem.used / (1024**3), 2)
            sys_info["mem_percent"] = mem.percent
            
            if platform.system() == "Windows":
                user32 = ctypes.windll.user32
                sys_info["screen_width"] = user32.GetSystemMetrics(0)
                sys_info["screen_height"] = user32.GetSystemMetrics(1)
            else:
                sys_info["screen_width"] = "未知"
                sys_info["screen_height"] = "未知"
                
        except Exception as e:
            print(f"补充系统信息失败：{e}")
            sys_info["cpu_count_physical"] = "未知"
            sys_info["cpu_count_logical"] = "未知"
            sys_info["mem_total"] = "未知"
            sys_info["mem_used"] = "未知"
        
        return sys_info
    except Exception as e:
        print(f"采集系统信息失败：{e}")
        return {"error": f"采集信息失败：{str(e)}", "local_ip": get_local_ip(), "hostname": platform.node()}

def set_thread_priority():
    if platform.system() != "Windows":
        return
    try:
        # 设置线程优先级为高（减少延迟）
        import win32api
        import win32process
        import win32con
        
        current_process = win32api.GetCurrentProcess()
        win32process.SetPriorityClass(current_process, win32process.HIGH_PRIORITY_CLASS)
        print("线程优先级已设置为高")
    except Exception as e:
        print(f"优先级设置跳过：{e}")

# ---------------------- 复制IP ----------------------
def copy_ip_to_clipboard():
    ip = get_local_ip()
    try:
        root.clipboard_clear()
        root.clipboard_append(ip)
        root.update()
        messagebox.showinfo("复制成功", f"本机IP {ip} 已复制到剪贴板！")
    except Exception as e:
        messagebox.showerror("复制失败", f"复制IP失败：{str(e)}")

# ---------------------- 聊天功能（优化版） ----------------------
def send_chat_msg():
    """发送聊天消息"""
    global current_active_connection
    if not current_active_connection or not current_active_connection.is_connected:
        messagebox.showwarning("提示", "当前无有效连接，无法发送消息！")
        return
    
    connection = current_active_connection
    if not connection.chat_entry or not connection.chat_text:
        messagebox.showerror("错误", "聊天组件未初始化！")
        return
    
    msg = connection.chat_entry.get().strip()
    if not msg:
        return
    
    try:
        chat_data = {
            "type": "chat_msg",
            "sender": "业务同学",
            "content": msg,
            "time": datetime.now().strftime("%H:%M:%S")
        }
        
        data = json.dumps(chat_data).encode()
        connection.conn.sendall(len(data).to_bytes(4, 'big'))
        connection.conn.sendall(data)
        
        def update_chat_ui():
            if not connection.chat_text.winfo_exists() or not connection.chat_entry.winfo_exists():
                return
            connection.chat_text.config(state=tk.NORMAL)
            connection.chat_text.insert(END, f"[{chat_data['time']}] 我：{msg}\n")
            connection.chat_text.see(END)
            connection.chat_text.config(state=tk.DISABLED)
            connection.chat_entry.delete(0, END)
            connection.chat_entry.focus_set()
        
        root.after(0, update_chat_ui)
        
    except Exception as e:
        messagebox.showerror("发送失败", f"消息发送失败：{str(e)}")
        connection.chat_entry.focus_set()

def add_chat_msg(msg_data, connection: SlaveConnection):
    """接收聊天消息"""
    try:
        if not connection or not connection.chat_text or not connection.chat_text.winfo_exists():
            return
        
        def update_chat_ui():
            connection.chat_text.config(state=tk.NORMAL)
            connection.chat_text.insert(END, f"[{msg_data.get('time', '未知时间')}] {msg_data.get('sender', '未知发送者')}：{msg_data.get('content', '')}\n")
            connection.chat_text.see(END)
            connection.chat_text.config(state=tk.DISABLED)
            blink_tray_icon()
            show_msg_notify(msg_data.get('sender', '未知'), msg_data.get('content', ''), msg_data.get('time', ''))
        
        root.after(0, update_chat_ui)
        
    except Exception as e:
        print(f"添加聊天消息失败：{e}")

# ---------------------- 键鼠操作（优化版） ----------------------
def press_mouse(x, y, button='left'):
    try:
        set_mouse_pos(x, y)
        import pyautogui
        pyautogui.mouseDown(int(x), int(y), button=button)
    except Exception as e:
        print(f"鼠标按下失败：{e}")

def release_mouse(x, y, button='left'):
    try:
        set_mouse_pos(x, y)
        import pyautogui
        pyautogui.mouseUp(int(x), int(y), button=button)
    except Exception as e:
        print(f"鼠标释放失败：{e}")

def drag_mouse(x, y, button='left'):
    try:
        import pyautogui
        pyautogui.moveTo(int(x), int(y), duration=0.0)
    except Exception as e:
        print(f"鼠标拖拽失败：{e}")

def click_mouse(x, y, button='left'):
    try:
        set_mouse_pos(x, y)
        import pyautogui
        pyautogui.click(int(x), int(y), button=button)
    except Exception as e:
        print(f"鼠标点击失败：{e}")

def set_mouse_pos(x, y):
    try:
        import pyautogui
        pyautogui.moveTo(int(x), int(y), duration=0.0)
    except Exception as e:
        print(f"设置鼠标位置失败：{e}")

def scroll_mouse(direction, distance):
    try:
        scaled_distance = distance * SCROLL_SPEED_MULTIPLIER
        import pyautogui
        pyautogui.scroll(scaled_distance * 2 if direction == 'up' else -scaled_distance * 2)
    except Exception as e:
        print(f"滚轮操作失败：{e}")

def key_down(key):
    try:
        import pyautogui
        pyautogui.keyDown(key)
        MODIFIER_STATE[key] = True
    except Exception as e:
        print(f"按键按下失败：{e}")

def key_up(key):
    try:
        import pyautogui
        pyautogui.keyUp(key)
        MODIFIER_STATE[key] = False
    except Exception as e:
        print(f"按键释放失败：{e}")

def key_input(key, is_character=False):
    try:
        import pyautogui
        if is_character:
            pyautogui.typewrite(key)
        else:
            if len(key) == 1:
                pyautogui.typewrite(key)
            else:
                pyautogui.press(key)
    except Exception as e:
        print(f"输入按键/符号失败：{e}（键值：{key}）")

# ---------------------- 截图功能（优化版） ----------------------
def capture_incremental_frame(connection: SlaveConnection):
    """优化的增量截图"""
    try:
        with mss.mss() as sct:
            monitor = sct.monitors[1]
            # 使用更快的截图方式
            img = sct.grab(monitor)
            frame = np.array(img, dtype=np.uint8)[:, :, :3]
            
            if connection.last_frame is None:
                connection.last_frame = frame
                return frame
            
            # 优化差异检测：使用更宽松的阈值
            diff = cv2.absdiff(frame, connection.last_frame)
            gray_diff = cv2.cvtColor(diff, cv2.COLOR_BGR2GRAY)
            
            # 动态阈值：根据画面变化程度调整
            non_zero = np.count_nonzero(gray_diff > 15)
            total_pixels = gray_diff.shape[0] * gray_diff.shape[1]
            
            # 如果变化小于0.1%则跳过
            if non_zero < total_pixels * 0.001:
                return None
            
            connection.last_frame = frame
            return frame
    except Exception as e:
        print(f"截图失败：{e}")
        connection.last_frame = None
        return None

def capture_to_queue(queue_obj, stop_event, connection: SlaveConnection):
    """优化的截图线程"""
    frame_interval = 1.0 / FPS_LIMIT
    last_time = time.time()
    
    while not stop_event.is_set() and connection.is_connected:
        try:
            current_time = time.time()
            elapsed = current_time - last_time
            
            if elapsed < frame_interval:
                # 使用更精确的睡眠
                sleep_time = frame_interval - elapsed
                if sleep_time > 0.001:
                    time.sleep(sleep_time)
                continue
            
            last_time = current_time
            
            frame = capture_incremental_frame(connection)
            if frame is None:
                continue
            
            # 使用更快的JPEG编码
            encode_param = [cv2.IMWRITE_JPEG_QUALITY, JPEG_QUALITY]
            _, encoded = cv2.imencode('.jpg', frame, encode_param)
            
            # 优化队列管理
            if queue_obj.qsize() >= FRAME_QUEUE_SIZE:
                try:
                    queue_obj.get_nowait()
                except queue.Empty:
                    pass
            
            queue_obj.put(encoded.tobytes())
            
            # 性能统计
            connection.frame_count += 1
            if current_time - connection.last_stat_time >= 5.0:
                fps = connection.frame_count / (current_time - connection.last_stat_time)
                print(f"[{connection.addr}] FPS: {fps:.1f}")
                connection.frame_count = 0
                connection.last_stat_time = current_time
                
        except Exception as e:
            print(f"[{connection.addr}] 截图线程异常：{e}")
            time.sleep(0.1)
            continue

def send_from_queue(conn, queue_obj, stop_event, connection: SlaveConnection):
    """优化的发送线程"""
    try:
        # 发送系统信息
        sys_info = get_system_info()
        sys_info_data = json.dumps({"type": "sys_info", "data": sys_info}).encode()
        conn.sendall(len(sys_info_data).to_bytes(4, 'big'))
        conn.sendall(sys_info_data)
        
        # 发送缩放信息
        scaling_data = json.dumps({"scaling": get_screen_scaling()}).encode()
        conn.sendall(len(scaling_data).to_bytes(4, 'big'))
        conn.sendall(scaling_data)
    except Exception as e:
        print(f"[{connection.addr}] 发送系统信息失败：{e}")
        stop_event.set()
        return
    
    while not stop_event.is_set() and connection.is_connected:
        try:
            encoded_data = queue_obj.get(timeout=0.05)
            data_len = len(encoded_data)
            conn.sendall(data_len.to_bytes(4, 'big'))
            conn.sendall(encoded_data)
        except queue.Empty:
            continue
        except Exception as e:
            print(f"[{connection.addr}] 发送帧失败：{e}")
            stop_event.set()
            break

# ---------------------- 指令处理（优化版） ----------------------
def handle_commands(conn, stop_event, connection: SlaveConnection):
    """处理控制指令"""
    screen_scaling = get_screen_scaling()
    set_thread_priority()
    
    # 连接成功提示
    def show_connect_tip():
        if not connection.chat_text.winfo_exists():
            return
        connection.chat_text.config(state=tk.NORMAL)
        connection.chat_text.insert(END, f"\n【提示】已连接到IT同学\n")
        connection.chat_text.config(state=tk.DISABLED)
        connection.chat_entry.focus_set()
    root.after(0, show_connect_tip)
    
    while not stop_event.is_set() and connection.is_connected:
        try:
            # 接收指令长度
            cmd_len_data = conn.recv(4)
            if not cmd_len_data:
                break
            cmd_len = int.from_bytes(cmd_len_data, 'big')
            
            # 接收指令内容（优化接收）
            cmd_data = b''
            remaining = cmd_len
            while remaining > 0 and not stop_event.is_set():
                chunk_size = min(BUFFER_SIZE, remaining)
                chunk = conn.recv(chunk_size)
                if not chunk:
                    break
                cmd_data += chunk
                remaining -= len(chunk)
            
            if len(cmd_data) != cmd_len:
                continue
            
            # 解析指令
            cmd = json.loads(cmd_data.decode())
            current_time = datetime.now().timestamp()

            # 处理聊天消息
            if cmd['type'] == 'chat_msg':
                add_chat_msg(cmd, connection)
                continue
            
            # 鼠标移动（优化节流）
            if cmd['type'] == 'mouse_move':
                if current_time - connection.last_mouse_time < MOUSE_THROTTLE:
                    continue
                connection.last_mouse_time = current_time
                set_mouse_pos(int(cmd['x']), int(cmd['y']))
            
            # 鼠标点击
            elif cmd['type'] == 'mouse_click':
                click_mouse(int(cmd['x']), int(cmd['y']), cmd.get('button', 'left'))
            
            # 鼠标滚轮
            elif cmd['type'] == 'mouse_wheel':
                scroll_mouse(cmd['direction'], cmd['distance'])
            
            # 鼠标按下（拖拽）
            elif cmd['type'] == 'mouse_press':
                connection.is_mouse_dragging = True
                connection.dragging_button = cmd.get('button', 'left')
                press_mouse(int(cmd['x']), int(cmd['y']), connection.dragging_button)
            
            # 鼠标释放（拖拽）
            elif cmd['type'] == 'mouse_release':
                connection.is_mouse_dragging = False
                release_mouse(int(cmd['x']), int(cmd['y']), cmd.get('button', 'left'))
            
            # 鼠标拖拽
            elif cmd['type'] == 'mouse_drag':
                if current_time - connection.last_mouse_time < MOUSE_THROTTLE:
                    continue
                connection.last_mouse_time = current_time
                drag_mouse(int(cmd['x']), int(cmd['y']), cmd.get('button', 'left'))
            
            # 按键输入
            elif cmd['type'] == 'key_input':
                is_character = cmd.get('is_character', False)
                key_input(cmd['key'], is_character)
            
            # 按键按下
            elif cmd['type'] == 'key_down':
                key_down(cmd['key'])
            
            # 按键释放
            elif cmd['type'] == 'key_up':
                key_up(cmd['key'])
                
        except Exception as e:
            print(f"[{connection.addr}] 指令处理异常：{e}")
            time.sleep(0.01)
            continue
    
    # 断开连接清理
    stop_event.set()
    connection.disconnect()

# ---------------------- 启动服务（优化版） ----------------------
def start_server(chat_text, chat_entry):
    """启动被控端服务"""
    try:
        server_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        server_socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        # 优化socket参数
        server_socket.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        server_socket.bind(('', LISTEN_PORT))
        server_socket.listen(5)
        
        # 打印启动信息
        sys_info = get_system_info()
        print(f"===== 被控端启动信息 =====")
        print(f"本机IP：{sys_info['local_ip']}")
        print(f"主机名：{sys_info['hostname']} | 用户名：{sys_info['username']}")
        print(f"系统：{sys_info['system']} {sys_info['os_release']}")
        print(f"CPU：{sys_info['cpu_count_physical']}物理/{sys_info['cpu_count_logical']}逻辑核心")
        print(f"内存：{sys_info['mem_used']}/{sys_info['mem_total']}GB")
        print(f"屏幕：{sys_info['screen_width']}x{sys_info['screen_height']} (缩放{sys_info['screen_scaling']}x)")
        print(f"优化配置：FPS={FPS_LIMIT}, JPEG质量={JPEG_QUALITY}, 队列大小={FRAME_QUEUE_SIZE}")
        print(f"开机自启状态：{'已开启' if check_auto_start() else '未开启'}")
        print(f"==========================")

        # 循环接收连接
        while True:
            try:
                conn, addr = server_socket.accept()
                print(f"[{addr}] 新连接建立")
                
                # 断开旧连接
                global current_active_connection
                if current_active_connection and current_active_connection.is_connected:
                    current_active_connection.disconnect()
                
                # 创建新连接实例
                slave_connection = SlaveConnection(conn, addr, chat_text, chat_entry)
                current_active_connection = slave_connection
                
                # 启动线程组
                stop_event = slave_connection.stop_event
                frame_queue = slave_connection.frame_queue

                # 指令处理线程
                slave_connection.cmd_thread = threading.Thread(
                    target=handle_commands, 
                    args=(conn, stop_event, slave_connection), 
                    daemon=True,
                    name=f"CmdThread-{addr}"
                )
                # 截图线程
                slave_connection.capture_thread = threading.Thread(
                    target=capture_to_queue, 
                    args=(frame_queue, stop_event, slave_connection), 
                    daemon=True,
                    name=f"CaptureThread-{addr}"
                )
                # 发送线程
                slave_connection.send_thread = threading.Thread(
                    target=send_from_queue, 
                    args=(conn, frame_queue, stop_event, slave_connection), 
                    daemon=True,
                    name=f"SendThread-{addr}"
                )
                
                # 启动线程
                slave_connection.cmd_thread.start()
                slave_connection.capture_thread.start()
                slave_connection.send_thread.start()

            except Exception as e:
                print(f"客户端连接异常：{e}")
                time.sleep(0.1)
                continue
    except Exception as e:
        print(f"启动服务失败：{e}")
        messagebox.showerror("致命错误", f"启动服务失败：{str(e)}\n请检查端口{LISTEN_PORT}是否被占用")
        exit_app()

# ---------------------- GUI（优化版） ----------------------
def create_gui():
    """创建图形界面"""
    global root
    root = tk.Tk()
    root.title("局域网被控端")
    root.geometry("450x550")
    root.resizable(True, True)
    root.attributes('-topmost', True)
    
    # 关闭窗口时隐藏到托盘
    def on_close():
        hide_main_window()
        return True
    root.protocol("WM_DELETE_WINDOW", on_close)

    # 顶部信息区
    top_frame = Frame(root)
    top_frame.pack(pady=10, fill=tk.X, padx=10)
    Label(top_frame, text="已启动远程协助服务，正在呼叫IT同学", font=("Arial", 12)).pack()
    
    # IP复制区
    ip_frame = Frame(top_frame)
    ip_frame.pack(pady=5)
    ip_label = Label(ip_frame, text=f"本机IP：{get_local_ip()}", font=("Arial", 10))
    ip_label.pack(side=tk.LEFT, padx=5)
    
    copy_btn = Button(ip_frame, text="复制IP", font=("Arial", 9), width=8, command=copy_ip_to_clipboard)
    copy_btn.pack(side=tk.LEFT, padx=5)

    # 系统信息区
    sys_frame = Frame(root, bd=1, relief=tk.GROOVE)
    sys_frame.pack(pady=5, fill=tk.X, padx=10)
    Label(sys_frame, text="📌 本机信息", font=("Arial", 10, "bold")).pack(anchor=tk.W, padx=5)
    sys_info = get_system_info()
    sys_text = (
        f"主机名：{sys_info.get('hostname', '未知')} | 用户名：{sys_info.get('username', '未知')}\n"
        f"系统：{sys_info.get('system', '未知')} {sys_info.get('os_release', '未知')} | IP：{sys_info.get('local_ip', '未知')}\n"
        f"CPU：{sys_info.get('cpu_count_physical', '未知')}物理核心 | 内存：{sys_info.get('mem_used', '未知')}/{sys_info.get('mem_total', '未知')}GB\n"
        f"优化：FPS={FPS_LIMIT} | 质量={JPEG_QUALITY}% | 队列={FRAME_QUEUE_SIZE}"
    )
    Label(sys_frame, text=sys_text, font=("Arial", 9), justify=tk.LEFT).pack(anchor=tk.W, padx=5, pady=2)

    # 聊天区域
    chat_frame = Frame(root, bd=1, relief=tk.GROOVE)
    chat_frame.pack(pady=5, fill=tk.BOTH, expand=True, padx=10)
    Label(chat_frame, text="💬 聊天（当前连接）", font=("Arial", 10, "bold")).pack(anchor=tk.W, padx=5)
    
    # 聊天记录框
    chat_scroll = Scrollbar(chat_frame)
    chat_scroll.pack(side=tk.RIGHT, fill=tk.Y)
    chat_text = Text(chat_frame, height=10, state=tk.DISABLED, yscrollcommand=chat_scroll.set, font=("Arial", 9))
    chat_text.pack(pady=3, fill=tk.BOTH, expand=True, padx=5)
    chat_scroll.config(command=chat_text.yview)
    
    # 聊天输入框
    chat_input_frame = Frame(chat_frame)
    chat_input_frame.pack(pady=5, fill=tk.X, padx=5)
    chat_entry = Entry(chat_input_frame, font=("Arial", 9), takefocus=True)
    chat_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=5)
    chat_entry.bind('<Return>', lambda e: send_chat_msg())
    
    send_btn = Button(chat_input_frame, text="发送", font=("Arial", 9), width=8, command=send_chat_msg)
    send_btn.pack(side=tk.RIGHT, padx=5)

    # 初始化键鼠API
    init_mouse_keyboard_api()

    # 启动服务
    threading.Thread(target=start_server, args=(chat_text, chat_entry), daemon=True).start()

    # 隐藏窗口参数
    if "--hidden" in sys.argv:
        hide_main_window()

    # 启动系统托盘
    def start_tray():
        global tray_icon
        tray_icon = create_tray_icon()
        if tray_icon:
            tray_icon.run()
    threading.Thread(target=start_tray, daemon=True).start()

    # 初始聚焦输入框
    chat_entry.focus_set()

    # 启动主循环
    root.mainloop()

# ---------------------- 主程序入口 ----------------------
if __name__ == "__main__":
    if platform.system() == "Windows":
        try:
            os.system("title 局域网被控端")
        except:
            pass
    
    # 检查Python版本
    if sys.version_info < (3, 7):
        messagebox.showerror("版本错误", "请使用Python 3.7及以上版本运行！")
        sys.exit(1)
    
    # 启动GUI
    create_gui()
