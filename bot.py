import os
import asyncio
import base64
import struct
import copy
import json
import io
import random
import re
import tempfile
from contextvars import ContextVar
from datetime import datetime, timedelta
from pyrogram import Client, filters, idle, raw, handlers, utils as pyrogram_utils
from pyrogram.types import ReplyKeyboardMarkup, KeyboardButton, Message, InlineKeyboardMarkup, InlineKeyboardButton
from pyrogram.errors import (
    SessionPasswordNeeded, PhoneCodeInvalid, PhoneCodeExpired, 
    FloodWait, AuthKeyUnregistered, PeerIdInvalid, UserBannedInChannel
)
from pyrogram.session import Session
from pyrogram.session.auth import Auth
try:
    from pyrogram.raw.functions.messages import CheckChatInvite
except ImportError:
    CheckChatInvite = None

# Telegram channel IDs can exceed the legacy 32-bit lower bound used by
# Pyrogram's peer classifier (for example, -1002404093511).
pyrogram_utils.MIN_CHANNEL_ID = -10**15

# --- Settings ---
def read_env(name):
    value = (os.environ.get(name) or "").strip()
    print(f"[config] {name}: {'present' if value else 'EMPTY'}")
    return value

BOT_TOKEN = read_env("BOT_TOKEN")
OWNER_ID_RAW = read_env("OWNER_ID")
API_ID_RAW = read_env("API_ID")
API_HASH = read_env("API_HASH")

ENABLE_USERBOT_MONITORING = (
    (os.environ.get("ENABLE_USERBOT_MONITORING") or "true").strip().lower()
    not in {"0", "false", "no", "off", "disabled"}
)

# Keep user accounts below Telegram's connection and send-rate limits.
# A lower value can easily trigger a transport flood when several accounts
# and groups are configured.
MIN_SEND_INTERVAL = 60
TRANSPORT_RETRY_DELAYS = (5, 15, 30, 60)

try:
    OWNER_ID = int(OWNER_ID_RAW or "0")
    API_ID = int(API_ID_RAW or "0")
except ValueError as exc:
    raise RuntimeError("OWNER_ID and API_ID must be numeric environment variables") from exc

missing_settings = []
if not BOT_TOKEN:
    missing_settings.append("BOT_TOKEN")
if OWNER_ID <= 0:
    missing_settings.append("OWNER_ID")
if API_ID <= 0:
    missing_settings.append("API_ID")
if not API_HASH:
    missing_settings.append("API_HASH")
if missing_settings:
    raise RuntimeError(f"Missing or invalid environment variables: {', '.join(missing_settings)}")

# --- Data file ---
DATA_FILE = os.path.abspath(
    os.environ.get("DATA_FILE")
    or os.path.join(os.path.dirname(os.path.abspath(__file__)), "data", "bot_data.json")
)
login_sessions = {}
profile_context = ContextVar("profile_context", default=None)
profile_posting_tasks = {}
profile_userbot_tasks = {}
profile_recent_scan_claims = set()
profile_auto_leave_tasks = {}
profile_account_caches = {}
profile_account_statuses = {}
profile_active_clients = {}
qr_login_sessions = {}
forwarded_incoming = set()
group_message_keys = set()
join_operations_in_progress = set()

# --- Load/Save Data ---
def default_profile_data():
    return {
        "accounts": [],
        "templates": [],
        "groups": [],
        "group_activity": {},
        "incoming_activity": {},
        "group_chat_ids": {},
        "timer": 60,
        "is_running": False,
        "stats": {"sent_count": 0, "failed_count": 0},
        "failed_messages": [],
        "user_state": {},
        "last_message": {},
        "outgoing_messages": {},
        "joined_channels": {},
        "channel_join_time": {},
        "account_joined_channels": {},
        "account_join_waits": {},
        "account_errors": {},
        "last_group_index": {},
        "last_sent_group_index": -1,
        "template_index": 0,
        "incoming_messages": {},
        "account_blocked_groups": {},
        "account_group_posts": {},
        "account_group_incoming": {},
        "account_group_last_sent": {},
        "group_unread_counts": {},
        "auto_join_groups": True
    }

def ensure_profile_data(data):
    defaults = default_profile_data()
    for key, value in defaults.items():
        if key not in data:
            data[key] = copy.deepcopy(value)
    data.setdefault("stats", {})
    data["stats"].setdefault("sent_count", 0)
    data["stats"].setdefault("failed_count", 0)
    return data

profile_store = {
    "active_profile_id": "profile_1",
    "profiles": []
}

def current_profile_id():
    return profile_context.get() or profile_store.get("active_profile_id", "profile_1")

def current_profile_record():
    profile_id = current_profile_id()
    profile = next((item for item in profile_store.get("profiles", []) if item.get("id") == profile_id), None)
    if profile is None:
        profile = profile_record(profile_id, "المجموعة 1", default_profile_data())
        profile_store.setdefault("profiles", []).append(profile)
    return profile

class ProfileDBProxy:
    def _data(self):
        return current_profile_record()["data"]

    def __getitem__(self, key):
        return self._data()[key]

    def __setitem__(self, key, value):
        self._data()[key] = value

    def __delitem__(self, key):
        del self._data()[key]

    def __contains__(self, key):
        return key in self._data()

    def __iter__(self):
        return iter(self._data())

    def __len__(self):
        return len(self._data())

    def get(self, key, default=None):
        return self._data().get(key, default)

    def setdefault(self, key, default=None):
        return self._data().setdefault(key, default)

    def pop(self, key, *args):
        return self._data().pop(key, *args)

    def clear(self):
        self._data().clear()

    def keys(self):
        return self._data().keys()

    def items(self):
        return self._data().items()

    def values(self):
        return self._data().values()

def get_account_cache():
    return profile_account_caches.setdefault(current_profile_id(), {})

def get_account_status_cache():
    return profile_account_statuses.setdefault(current_profile_id(), {})

def profile_record(profile_id, name, data):
    return {
        "id": profile_id,
        "name": name,
        "data": ensure_profile_data(copy.deepcopy(data))
    }

def reset_to_default_data():
    default_data = default_profile_data()
    profile_store["profiles"] = [
        profile_record("profile_1", "المجموعة 1", default_data)
    ]
    profile_store["active_profile_id"] = "profile_1"
    os.makedirs(os.path.dirname(DATA_FILE), exist_ok=True)
    return default_data

def load_data():
    if not os.path.exists(DATA_FILE):
        return reset_to_default_data()

    try:
        with open(DATA_FILE, "r", encoding="utf-8") as f:
            raw_data = json.load(f)
    except json.JSONDecodeError as exc:
        corrupt_path = f"{DATA_FILE}.corrupt-{datetime.now().strftime('%Y%m%d-%H%M%S')}"
        try:
            os.replace(DATA_FILE, corrupt_path)
        except OSError:
            corrupt_path = "unavailable"
        print(
            f"Warning: invalid JSON in {DATA_FILE}: {exc}. "
            f"Starting with default data; corrupt file: {corrupt_path}"
        )
        return reset_to_default_data()

    if not isinstance(raw_data, dict):
        print(f"Warning: {DATA_FILE} does not contain a JSON object. Starting with default data.")
        return reset_to_default_data()

    if isinstance(raw_data.get("profiles"), list):
        stored_profiles = []
        for index, stored in enumerate(raw_data["profiles"], 1):
            if not isinstance(stored, dict):
                continue
            profile_id = str(stored.get("id") or f"profile_{index}")
            name = str(stored.get("name") or f"المجموعة {index}").strip()
            data = stored.get("data") or {}
            stored_profiles.append(profile_record(profile_id, name, data))
        if stored_profiles:
            profile_store["profiles"] = stored_profiles
            active_id = str(raw_data.get("active_profile_id") or stored_profiles[0]["id"])
            if not any(item["id"] == active_id for item in stored_profiles):
                active_id = stored_profiles[0]["id"]
            profile_store["active_profile_id"] = active_id
            active = next(item for item in stored_profiles if item["id"] == active_id)
            return copy.deepcopy(active["data"])

    legacy_data = ensure_profile_data(raw_data)
    profile_store["profiles"] = [
        profile_record("profile_1", "المجموعة 1", legacy_data)
    ]
    profile_store["active_profile_id"] = "profile_1"
    return legacy_data

def save_data(data=None):
    if data is None or isinstance(data, ProfileDBProxy):
        data = current_profile_record()["data"]
    ensure_profile_data(data)
    active_id = current_profile_id()
    active_profile = next((item for item in profile_store.get("profiles", []) if item["id"] == active_id), None)
    if active_profile is None:
        active_profile = profile_record(active_id, "المجموعة 1", data)
        profile_store.setdefault("profiles", []).append(active_profile)
    active_profile["data"] = data
    payload = {
        "schema_version": 2,
        "active_profile_id": profile_store.get("active_profile_id", active_id),
        "profiles": profile_store.get("profiles", [])
    }
    os.makedirs(os.path.dirname(DATA_FILE), exist_ok=True)
    temp_fd, temp_path = tempfile.mkstemp(
        prefix=".bot_data-",
        suffix=".tmp",
        dir=os.path.dirname(DATA_FILE)
    )
    try:
        with os.fdopen(temp_fd, "w", encoding="utf-8") as f:
            json.dump(payload, f, ensure_ascii=False, indent=4)
            f.flush()
        os.replace(temp_path, DATA_FILE)
    except Exception:
        try:
            os.unlink(temp_path)
        except OSError:
            pass
        raise

load_data()
db = ProfileDBProxy()
ensure_profile_data(db._data())

# --- Bot profiles / groups ---
def get_active_profile():
    active_id = profile_store.get("active_profile_id")
    return next(
        (item for item in profile_store.get("profiles", []) if item["id"] == active_id),
        None
    )

def get_profile_index_by_name(name):
    normalized = normalize_button_text(name)
    for index, profile in enumerate(profile_store.get("profiles", [])):
        if normalize_button_text(profile.get("name", "")) == normalized:
            return index
    return None

def next_profile_id():
    used_ids = {str(item.get("id")) for item in profile_store.get("profiles", [])}
    number = 1
    while f"profile_{number}" in used_ids:
        number += 1
    return f"profile_{number}"

def profile_menu_keyboard():
    keyboard = []
    for profile in profile_store.get("profiles", []):
        keyboard.append([KeyboardButton(profile.get("name", "مجموعة"))])
    keyboard.append([
        KeyboardButton("➕ إضافة مجموعة"),
        KeyboardButton("🗑 حذف مجموعة")
    ])
    keyboard.append([KeyboardButton("📊 إحصائيات الكل")])
    return ReplyKeyboardMarkup(keyboard, resize_keyboard=True)

def profile_menu_text():
    active = get_active_profile()
    active_name = active.get("name", "المجموعة 1") if active else "المجموعة 1"
    lines = ["🤖 مجموعات البوت", "", f"📂 المجموعة الحالية: {active_name}", ""]
    for index, profile in enumerate(profile_store.get("profiles", []), 1):
        profile_data = profile.get("data", {})
        is_running = bool(profile_data.get("is_running"))
        marker = "🟢" if is_running else ("✅" if profile.get("id") == profile_store.get("active_profile_id") else "📁")
        status = "يعمل" if is_running else "متوقف"
        lines.append(f"{marker} {index}. {profile.get('name', f'المجموعة {index}')} — {status}")
    lines.append("")
    lines.append("اختر مجموعة لفتح إعداداتها.")
    return "\n".join(lines)

def all_profiles_stats_text():
    profiles = profile_store.get("profiles", [])
    totals = {
        "accounts": 0,
        "templates": 0,
        "groups": 0,
        "sent": 0,
        "failed": 0,
        "incoming": 0,
    }
    lines = ["📊 إحصائيات جميع المجموعات", ""]

    for index, profile in enumerate(profiles, 1):
        data = ensure_profile_data(profile.get("data") or {})
        stats = data.get("stats") or {}
        incoming_messages = data.get("incoming_messages") or {}
        incoming_count = sum(
            len(messages)
            for messages in incoming_messages.values()
            if isinstance(messages, dict)
        )
        sent_count = int(stats.get("sent_count", 0) or 0)
        failed_count = int(stats.get("failed_count", 0) or 0)
        account_count = len(data.get("accounts") or [])
        template_count = len(data.get("templates") or [])
        group_count = len(data.get("groups") or [])
        status = "🟢 يعمل" if data.get("is_running") else "🔴 متوقف"
        name = profile.get("name") or f"المجموعة {index}"

        lines.append(
            f"{index}. {name} — {status}\n"
            f"   حسابات: {account_count} | كروبات: {group_count} | "
            f"كليشات: {template_count} | إرسال: {sent_count} | "
            f"فشل: {failed_count} | ردود: {incoming_count}"
        )

        totals["accounts"] += account_count
        totals["templates"] += template_count
        totals["groups"] += group_count
        totals["sent"] += sent_count
        totals["failed"] += failed_count
        totals["incoming"] += incoming_count

    if not profiles:
        return "📊 لا توجد مجموعات منفصلة."

    lines.extend(
        [
            "",
            "📌 الإجمالي الكلي",
            f"الحسابات: {totals['accounts']} | الكروبات: {totals['groups']} | "
            f"الكليشات: {totals['templates']}",
            f"تم الإرسال: {totals['sent']} | فشل الإرسال: {totals['failed']} | "
            f"الردود الواردة: {totals['incoming']}",
        ]
    )
    return "\n".join(lines)

def failed_messages_text():
    failures = db.get("failed_messages") or []
    if not failures:
        return "✅ لا توجد رسائل فاشلة مسجلة حاليًا."

    recent = failures[-10:]
    grouped = {}
    for item in recent:
        group = str(item.get("group", "غير معروف"))[:100]
        grouped.setdefault(group, []).append(item)

    lines = [
        "❌ الرسائل الفاشلة حسب الكروبات",
        "",
        f"إجمالي سجل الفشل: {len(failures)} | "
        f"المحاولات المعروضة: {len(recent)}",
        "",
    ]
    for group, group_failures in grouped.items():
        lines.append(f"📢 الكروب: {group}")
        for item in reversed(group_failures):
            timestamp = str(item.get("time", "غير معروف")).replace("T", " ")[:19]
            account = item.get("account", "غير معروف")
            reason = str(item.get("reason", "خطأ غير مصنف"))[:260]
            solution = str(item.get("solution", "راجع التفاصيل التقنية وأعد المحاولة."))[:320]
            technical = str(item.get("technical", ""))[:240]
            lines.extend([
                f"  🔢 الحساب رقم: {account} | 🕒 {timestamp}",
                f"  🔎 السبب: {reason}",
                f"  🛠 الحل: {solution}",
            ])
            if technical and technical != reason:
                lines.append(f"  🧪 التفاصيل: {technical}")
        lines.append("")

    return "\n".join(lines)[:3900]

def empty_profile_data():
    new_data = default_profile_data()
    new_data["timer"] = int(db.get("timer", 60) or 60)
    new_data["auto_join_groups"] = bool(db.get("auto_join_groups", True))
    return new_data

async def show_profile_menu(message):
    await message.reply_text(
        profile_menu_text(),
        reply_markup=profile_menu_keyboard()
    )

async def stop_all_userbots(profile_id=None):
    profile_id = profile_id or current_profile_id()
    tasks = list(profile_userbot_tasks.get(profile_id, []))
    profile_userbot_tasks[profile_id] = []
    for task in tasks:
        task.cancel()
    if tasks:
        await asyncio.gather(*tasks, return_exceptions=True)

async def activate_profile(index):
    profiles = profile_store.get("profiles", [])
    if not 0 <= index < len(profiles):
        return False
    selected = profiles[index]
    profile_store["active_profile_id"] = selected["id"]
    profile_context.set(selected["id"])
    get_account_cache().clear()
    get_account_status_cache().clear()
    ensure_profile_data(selected["data"])
    save_data()
    return True

# --- Bot Client ---
app = Client(
    "auto_post_bot",
    api_id=API_ID,
    api_hash=API_HASH,
    bot_token=BOT_TOKEN,
    in_memory=True,
)

# --- Bot settings keyboard ---
BOT_KEYBOARD = ReplyKeyboardMarkup(
    [
        [
            KeyboardButton("➕ إضافة حساب"),
            KeyboardButton("📷 إضافة حساب QR"),
        ],
        [KeyboardButton("🔄 استرداد حساب")],
        [KeyboardButton("🗑 حذف حساب"), KeyboardButton("📋 قائمة الحسابات")],
        [KeyboardButton("📋 قائمة الكروبات")],
        [KeyboardButton("📝 إضافة كليشة"), KeyboardButton("🗑 حذف كليشة")],
        [KeyboardButton("📢 إضافة كروب"), KeyboardButton("❌ حذف كروب")],
        [KeyboardButton("▶️ تشغيل البوت"), KeyboardButton("⏹ إيقاف البوت")],
        [KeyboardButton("⏱ المؤقت"), KeyboardButton("📊 الإحصائيات")],
        [KeyboardButton("❌ الرسائل الفاشلة")],
        [KeyboardButton("🗑 حذف الكل")],
        [KeyboardButton("👥 الردود الواردة")],
        [KeyboardButton("🔄 حالة الردود"), KeyboardButton("⚙️ إعدادات الردود")],
        [KeyboardButton("⬅️ المجموعات")]
    ],
    resize_keyboard=True
)

MENU_ACTIONS = {
    "accounts": {"📋 قائمة الحسابات", "قائمة الحسابات", "📋 Accounts"},
    "groups": {"📋 قائمة الكروبات", "قائمة الكروبات", "📋 Groups"},
    "add_account": {"➕ إضافة حساب", "إضافة حساب", "➕ Add Acc"},
    "add_account_qr": {"📷 إضافة حساب QR", "إضافة حساب QR", "📷 QR Login"},
    "recover_account": {"🔄 استرداد حساب", "استرداد حساب", "🔄 Recover"},
    "delete_account": {"🗑 حذف حساب", "حذف حساب", "🗑 Delete Acc"},
    "add_text": {"📝 إضافة كليشة", "إضافة كليشة", "إضافة كليشه", "📝 Add Text"},
    "delete_text": {"🗑 حذف كليشة", "حذف كليشة", "حذف كليشه", "🗑 Del Text"},
    "add_group": {"📢 إضافة كروب", "إضافة كروب", "إضافة قروب", "📢 Add Group"},
    "delete_group": {"❌ حذف كروب", "حذف كروب", "حذف قروب", "❌ Del Group"},
    "start": {"▶️ تشغيل البوت", "تشغيل البوت", "▶️ Start"},
    "stop": {"⏹ إيقاف البوت", "إيقاف البوت", "⏹ Stop"},
    "timer": {"⏱ المؤقت", "المؤقت", "⏱ Timer"},
    "stats": {"📊 الإحصائيات", "الإحصائيات", "📊 Stats"},
    "failed_messages": {"❌ الرسائل الفاشلة", "الرسائل الفاشلة", "❌ Failed Messages"},
    "clear": {"🗑 حذف الكل", "حذف الكل", "🗑 Clear All"},
    "incoming_replies": {"👥 الردود الواردة", "الردود الواردة", "👥 Replies"},
    "reply_status": {"🔄 حالة الردود", "حالة الردود", "🔄 Status"},
    "reply_settings": {"⚙️ إعدادات الردود", "إعدادات الردود", "⚙️ Settings"},
    "profiles": {"⬅️ المجموعات", "المجموعات", "⬅️ Groups Menu"}
}

def normalize_button_text(value):
    return re.sub(r"\s+", " ", value.replace("\ufe0f", "").replace("\u200d", "").strip()).casefold()

NORMALIZED_MENU_ACTIONS = {
    action: {normalize_button_text(label) for label in labels}
    for action, labels in MENU_ACTIONS.items()
}

def get_menu_action(text):
    normalized_text = normalize_button_text(text)
    for action, labels in NORMALIZED_MENU_ACTIONS.items():
        if normalized_text in labels:
            return action
    return None

# --- 🛠️ دالة استخراج الروابط (محسّنة بقوة) ---
def extract_all_links(message: Message):
    links = []
    seen = set()

    def add_value(value):
        if not value:
            return
        value = str(value).strip().rstrip(".,;:!?)]}")
        value = re.sub(
            r"tg://join\?invite=([\w-]+)",
            r"https://t.me/+\1",
            value,
            flags=re.IGNORECASE,
        )
        value = re.sub(
            r"(?i)((?:https?://)?)(?:www\.)?telegram\.(?:me|dog)/",
            r"\1t.me/",
            value,
        )
        pattern = (
            r"(?:(?:https?://)?(?:www\.)?t\.me/(?:\+[\w-]+|joinchat/[\w-]+|"
            r"(?:s/)?[A-Za-z0-9_]{4,32}(?:/\d+)?|c/\d+(?:/\d+)?))"
            r"|(?<![\w])@[A-Za-z0-9_]{4,32}\b"
            r"|(?<!\d)-100\d{6,}(?!\d)"
        )
        for match in re.finditer(pattern, value, flags=re.IGNORECASE):
            candidate = match.group(0).rstrip(".,;:!?)]}")
            if candidate not in seen:
                links.append(candidate)
                seen.add(candidate)

    def add_chat(chat):
        if not chat:
            return
        username = getattr(chat, "username", None)
        if username:
            add_value(f"@{str(username).lstrip('@')}")
        chat_id = getattr(chat, "id", None)
        if chat_id is not None:
            add_value(str(chat_id))

    add_value(message.text or message.caption or "")
    for entity in (message.entities or message.caption_entities or []):
        add_value(getattr(entity, "url", None))

    markup = message.reply_markup
    rows = []
    if markup:
        rows = getattr(markup, "inline_keyboard", None) or getattr(markup, "keyboard", None) or []
    for row in rows:
        for button in row:
            add_value(getattr(button, "url", None))
            add_value(getattr(button, "text", None))
            add_value(getattr(button, "callback_data", None))
            web_app = getattr(button, "web_app", None)
            add_value(getattr(web_app, "url", None) if web_app else None)

    add_chat(getattr(message, "forward_from_chat", None))
    forward_origin = getattr(message, "forward_origin", None)
    add_chat(getattr(forward_origin, "chat", None))

    return links

JOIN_BUTTON_KEYWORDS = (
    "اشترك",
    "إشترك",
    "انضم",
    "القناة",
    "قناة",
    "الاشتراك",
    "اضغط",
    "تحقق",
    "subscribe",
    "join",
    "channel",
    "check",
    "verify",
    "member",
)

def message_requests_subscription(message):
    text = f"{message.text or ''}\n{message.caption or ''}".casefold()
    return any(
        keyword.casefold() in text
        for keyword in (
            "غير مشترك",
            "اشترك",
            "الاشتراك",
            "انضم",
            "join the channel",
            "subscribe",
            "not subscribed",
            "must join",
        )
    )

def get_join_button_positions(message):
    markup = getattr(message, "reply_markup", None)
    rows = (
        getattr(markup, "inline_keyboard", None)
        or getattr(markup, "keyboard", None)
        or []
    ) if markup else []
    subscription_context = message_requests_subscription(message)
    positions = []
    for row_index, row in enumerate(rows):
        for column_index, button in enumerate(row):
            callback_data = getattr(button, "callback_data", None)
            if not callback_data:
                continue
            button_text = " ".join(
                str(value or "")
                for value in (
                    getattr(button, "text", None),
                    callback_data,
                )
            ).casefold()
            is_join_button = any(
                keyword.casefold() in button_text
                for keyword in JOIN_BUTTON_KEYWORDS
            )
            if subscription_context or is_join_button:
                positions.append((row_index, column_index))
    return positions

async def click_join_buttons(client, message):
    discovered_links = set()
    positions = get_join_button_positions(message)
    if not positions:
        return discovered_links

    for row_index, column_index in positions[:8]:
        try:
            result = await message.click(row_index, column_index)
            await asyncio.sleep(0.6)

            updated_message = await client.get_messages(
                message.chat.id,
                message.id,
            )
            if updated_message:
                discovered_links.update(extract_all_links(updated_message))

            callback_message = getattr(result, "message", None)
            if callback_message:
                discovered_links.update(extract_all_links(callback_message))
            callback_answer = (
                getattr(result, "answer", None)
                or getattr(result, "text", None)
                or ""
            )
            callback_url = getattr(result, "url", None)
            if callback_url:
                discovered_links.update(
                    extract_all_links(
                        type(
                            "LinkProbe",
                            (),
                            {
                                "text": str(callback_url),
                                "caption": None,
                                "entities": None,
                                "caption_entities": None,
                                "reply_markup": None,
                                "forward_from_chat": None,
                                "forward_origin": None,
                            },
                        )()
                    )
                )
            if callback_answer:
                probe = type(
                    "LinkProbe",
                    (),
                    {
                        "text": str(callback_answer),
                        "caption": None,
                        "entities": None,
                        "caption_entities": None,
                        "reply_markup": None,
                        "forward_from_chat": None,
                        "forward_origin": None,
                    },
                )()
                discovered_links.update(extract_all_links(probe))
            print(
                f"🖱️ Userbot clicked subscription button "
                f"{row_index}:{column_index}"
            )
        except FloodWait as error:
            print(
                f"⏳ Userbot button click flood wait: {error.x}s; "
                "remaining buttons skipped"
            )
            break
        except Exception as error:
            print(
                f"⚠️ Userbot could not click subscription button "
                f"{row_index}:{column_index}: {str(error)[:120]}"
            )
    return discovered_links

# --- Clean group link ---
def clean_group_link(link):
    link = str(link or "").strip().rstrip(".,;:!?)]}")
    link = re.sub(r"(?i)^https?://telegram\.me/", "https://t.me/", link)
    link = re.sub(r"(?i)^telegram\.me/", "t.me/", link)
    link = re.sub(r"(?i)^https?://www\.t\.me/", "https://t.me/", link)
    link = re.sub(r"(?i)^www\.t\.me/", "t.me/", link)
    link = re.sub(r"(?i)^tg://join\?invite=([\w-]+)$", r"https://t.me/+\1", link)
    link = re.sub(r"[?#].*$", "", link)
    private_message_link = re.match(
        r"^(?:https?://)?t\.me/c/(\d+)(?:/\d+)?(?:[?#].*)?$",
        link,
        flags=re.IGNORECASE,
    )
    if private_message_link:
        return f"-100{private_message_link.group(1)}"
    if re.fullmatch(r"-?\d+", link):
        return link
    if link.startswith(("https://t.me/", "http://t.me/", "t.me/")):
        prefix = "https://t.me/" if link.startswith("https://t.me/") else (
            "http://t.me/" if link.startswith("http://t.me/") else "t.me/"
        )
        suffix = link[len(prefix):]
        if suffix.startswith(("+", "joinchat/")):
            return link
        if suffix.startswith("s/"):
            suffix = suffix[2:]
        suffix = suffix.split("/", 1)[0]
        return f"@{suffix}"
    if not link.startswith("@"):
        link = f"@{link}"
    return link

def get_group_chat_target(group):
    clean_group = clean_group_link(group)
    known_chat_id = db.get("group_chat_ids", {}).get(clean_group)
    if known_chat_id is not None:
        try:
            return int(known_chat_id)
        except (TypeError, ValueError):
            pass
    if re.fullmatch(r"-?\d+", clean_group):
        return int(clean_group)
    return clean_group

def is_private_invite_link(value):
    normalized = str(value or "").strip().rstrip(".,;:!?)]}")
    normalized = re.sub(r"(?i)^https?://telegram\.me/", "https://t.me/", normalized)
    normalized = re.sub(r"(?i)^telegram\.me/", "t.me/", normalized)
    normalized = re.sub(r"(?i)^https?://www\.t\.me/", "https://t.me/", normalized)
    normalized = re.sub(r"(?i)^www\.t\.me/", "t.me/", normalized)
    normalized = re.sub(r"[?#].*$", "", normalized)
    return bool(
        re.fullmatch(
            r"(?:https?://)?t\.me/(?:\+[\w-]+|joinchat/[\w-]+)",
            normalized,
            flags=re.IGNORECASE,
        )
    )

async def get_account_group_target(client, group):
    clean_group = clean_group_link(group)
    if not clean_group:
        return clean_group

    if clean_group.startswith("@"):
        return clean_group

    chat_info = None
    if is_private_invite_link(clean_group):
        try:
            chat_info = await client.get_chat(clean_group)
        except Exception:
            chat_info = await get_chat_from_private_invite(client, clean_group)
    elif re.fullmatch(r"-?\d+", clean_group):
        try:
            chat_info = await client.get_chat(int(clean_group))
        except Exception as error:
            db.setdefault("group_chat_ids", {}).pop(clean_group, None)
            save_data(db)
            raise ValueError(
                f"PEER_ID_INVALID: peer {clean_group} is not available in this account session; "
                "configure the group with its @username or invite link"
            ) from error
    else:
        try:
            chat_info = await client.get_chat(clean_group)
        except Exception as error:
            db.setdefault("group_chat_ids", {}).pop(clean_group, None)
            save_data(db)
            raise ValueError(f"PEER_ID_INVALID: could not resolve {clean_group}") from error

    resolved_id = getattr(chat_info, "id", None) if chat_info else None
    if resolved_id is not None:
        db.setdefault("group_chat_ids", {})[clean_group] = str(resolved_id)
        return int(resolved_id)

    db.setdefault("group_chat_ids", {}).pop(clean_group, None)
    save_data(db)
    raise ValueError(f"PEER_ID_INVALID: could not resolve configured group {clean_group}")

async def get_chat_from_private_invite(client, invite_link):
    if CheckChatInvite is None:
        return None
    match = re.fullmatch(
        r"(?:https?://)?t\.me/(?:\+|joinchat/)([\w-]+)",
        invite_link,
        flags=re.IGNORECASE,
    )
    if not match:
        return None
    try:
        invite_state = await client.invoke(CheckChatInvite(hash=match.group(1)))
        chat = getattr(invite_state, "chat", None)
        if chat is not None:
            try:
                await client.fetch_peers([chat])
            except Exception as error:
                print(f"⚠️ Could not cache private invite peer {invite_link}: {error}")
        return chat
    except Exception as error:
        print(f"⚠️ Could not resolve private invite {invite_link}: {error}")
        return None

GROUP_RETRY_MINUTES = 15
UNREAD_MESSAGES_THRESHOLD = 10

def get_account_group_blocks(account_number):
    all_blocks = db.setdefault("account_blocked_groups", {})
    key = str(account_number)
    blocks = all_blocks.setdefault(key, {})
    if isinstance(blocks, list):
        retry_until = (datetime.now() + timedelta(minutes=GROUP_RETRY_MINUTES)).isoformat()
        blocks = {group: retry_until for group in blocks}
        all_blocks[key] = blocks
    return blocks

def parse_activity_time(value):
    if isinstance(value, datetime):
        parsed = value
        return parsed.replace(tzinfo=None) if parsed.tzinfo else parsed
    if not value or isinstance(value, (int, float)):
        return None
    try:
        parsed = datetime.fromisoformat(str(value))
        if parsed.tzinfo:
            parsed = parsed.replace(tzinfo=None)
        return parsed
    except (TypeError, ValueError):
        return None

def get_account_group_post_state(account_number, group):
    account_key = str(account_number)
    posts = db.get("account_group_posts", {}).get(account_key, {})
    incoming = db.get("account_group_incoming", {}).get(account_key, {})
    return int(posts.get(group, 0) or 0), int(incoming.get(group, 0) or 0)

def can_account_post_to_group(account_number, group, latest_time=None):
    post_count, incoming_count = get_account_group_post_state(account_number, group)
    if post_count == 0 or incoming_count >= UNREAD_MESSAGES_THRESHOLD:
        return True
    if latest_time is None:
        return False

    account_key = str(account_number)
    last_sent_raw = (
        db.get("account_group_last_sent", {})
        .get(account_key, {})
        .get(group)
    )
    last_sent_time = parse_activity_time(last_sent_raw)
    if last_sent_time is None:
        return True
    return latest_time > last_sent_time + timedelta(seconds=2)

def mark_account_group_sent(account_number, group):
    account_key = str(account_number)
    db.setdefault("account_group_posts", {}).setdefault(account_key, {})
    db.setdefault("account_group_incoming", {}).setdefault(account_key, {})
    db.setdefault("account_group_last_sent", {}).setdefault(account_key, {})
    posts = db["account_group_posts"][account_key]
    incoming = db["account_group_incoming"][account_key]
    posts[group] = int(posts.get(group, 0) or 0) + 1
    incoming[group] = 0
    db["account_group_last_sent"][account_key][group] = datetime.now().isoformat()

async def get_group_dialog_states(client):
    states = {}
    try:
        known_chat_ids = db.setdefault("group_chat_ids", {})
        for configured_group in db.get("groups", []):
            clean_group = clean_group_link(configured_group)
            if clean_group in known_chat_ids:
                continue
            try:
                chat_info = await client.get_chat(clean_group)
                known_chat_ids[clean_group] = str(chat_info.id)
            except Exception:
                continue

        async for dialog in client.get_dialogs():
            group = get_configured_group_for_chat(getattr(dialog, "chat", None))
            if not group:
                continue

            unread_count = int(getattr(dialog, "unread_messages_count", 0) or 0)
            top_message = getattr(dialog, "top_message", None)
            latest_time = parse_activity_time(getattr(top_message, "date", None))
            if latest_time is None:
                latest_time = parse_activity_time(
                    db.get("incoming_activity", {}).get(group)
                )
            if latest_time is None:
                continue

            states[group] = {
                "unread_count": unread_count,
                "last_message_time": latest_time,
            }
            db.setdefault("group_unread_counts", {})[group] = unread_count

        missing_groups = [
            configured_group
            for configured_group in db.get("groups", [])
            if configured_group not in states
        ]
        for configured_group in missing_groups:
            latest_time = None
            try:
                chat_target = get_group_chat_target(configured_group)
                async for latest_message in client.get_chat_history(chat_target, limit=1):
                    latest_time = parse_activity_time(
                        getattr(latest_message, "date", None)
                    )
                    break
            except Exception as error:
                print(
                    f"⚠️ تعذر قراءة آخر رسالة من {configured_group}: "
                    f"{str(error)[:80]}"
                )

            if latest_time is None:
                latest_time = parse_activity_time(
                    db.get("incoming_activity", {}).get(configured_group)
                )
            if latest_time is not None:
                states[configured_group] = {
                    "unread_count": int(
                        db.get("group_unread_counts", {}).get(configured_group, 0) or 0
                    ),
                    "last_message_time": latest_time,
                }
    except Exception as error:
        print(f"❌ Could not read group dialogs: {error}")
    return states

def get_next_group(account_number=None, dialog_states=None):
    groups = db.get("groups", [])
    if not groups:
        return None

    account_key = str(account_number or 0)
    last_indices = db.setdefault("last_group_index", {})
    try:
        last_index = int(last_indices.get(account_key, -1))
    except (TypeError, ValueError):
        last_index = -1
    next_index = (last_index + 1) % len(groups)
    last_indices[account_key] = next_index
    return groups[next_index]

def advance_group_after_attempt(group):
    groups = db.get("groups", [])
    if group in groups:
        db["last_sent_group_index"] = groups.index(group)
        save_data(db)

PERMANENT_GROUP_ERRORS = (
    "CHAT_WRITE_FORBIDDEN",
    "CHAT_ADMIN_REQUIRED",
    "CHAT_RESTRICTED",
    "CHANNEL_PRIVATE",
    "USER_BANNED_IN_CHANNEL",
    "PEER_ID_INVALID",
    "USERNAME_INVALID",
    "ID NOT FOUND",
    "MESSAGE_SEND_FAILED"
)

def is_permanent_group_error(error_text):
    text = str(error_text).upper()
    return any(marker in text for marker in PERMANENT_GROUP_ERRORS)

def failure_guidance(error_text):
    text = str(error_text or "").strip()
    upper = text.upper()
    rules = [
        (("FLOODWAIT", "FLOOD_WAIT"), "Telegram طلب الانتظار بسبب كثرة الطلبات.", "انتظر المدة الظاهرة، وارفع قيمة المؤقت أو قلّل عدد الحسابات."),
        (("USER_NOT_ACCEPTED", "INVITE_REQUEST_SENT"), "Telegram لم يقبل الحساب في هذه الدعوة أو أرسل طلب انضمام بانتظار الموافقة.", "لا تعاود المحاولة بسرعة؛ وافق مشرف القناة على الطلب أو استخدم رابط دعوة صالحًا."),
        (("USERBANNEDINCHANNEL", "USER_BANNED_IN_CHANNEL"), "الحساب ممنوع من المجموعة أو القناة.", "أزل الحظر من Telegram أو استخدم حسابًا آخر ثم أعد المحاولة."),
        (("PEER_ID_INVALID", "ID NOT FOUND", "PEER INVALID"), "معرّف المجموعة غير متاح داخل جلسة هذا الحساب.", "أعد إضافة المجموعة باستخدام @username أو رابط دعوة، وتأكد أن الحساب عضو فيها."),
        (("CHAT_WRITE_FORBIDDEN", "CHAT_ADMIN_REQUIRED"), "الحساب لا يملك صلاحية الكتابة في المجموعة.", "امنح الحساب صلاحية إرسال الرسائل أو اختر مجموعة تسمح بالكتابة."),
        (("CHAT_RESTRICTED", "CHANNEL_PRIVATE", "USERNAME_INVALID"), "المجموعة خاصة أو أن الرابط/المستخدم غير صالح.", "تحقق من الرابط، واجعل الحساب عضوًا في المجموعة قبل التشغيل."),
        (("AUTH_KEY_UNREGISTERED", "SESSION REVOKED"), "جلسة الحساب غير صالحة أو تم تسجيل خروجها.", "احذف الحساب وأعد تسجيل الدخول أو أضف Session String جديدًا."),
        (("GROUP_JOIN_FAILED",), "تعذر الوصول إلى المجموعة أو الانضمام إليها.", "أرسل @username أو رابط الدعوة الصحيح، وتأكد من صلاحية الحساب."),
    ]
    for markers, reason, solution in rules:
        if any(marker in upper for marker in markers):
            return reason, solution
    return "حدث خطأ غير مصنف أثناء الإرسال.", "راجع التفاصيل التقنية، ثم تحقق من عضوية الحساب وصلاحية الكتابة وأعد المحاولة."

def record_failure(account_number, group, error_text, reason=None, solution=None):
    raw_text = str(error_text or "").strip()
    default_reason, default_solution = failure_guidance(raw_text)
    failures = db.setdefault("failed_messages", [])
    failures.append({
        "time": datetime.now().isoformat(),
        "account": account_number,
        "group": str(group),
        "reason": reason or default_reason,
        "solution": solution or default_solution,
        "technical": raw_text[:300],
    })
    del failures[:-50]

def block_account_from_group(account_number, group):
    blocked = get_account_group_blocks(account_number)
    retry_until = datetime.now() + timedelta(minutes=GROUP_RETRY_MINUTES)
    blocked[group] = retry_until.isoformat()
    print(f"⏸️ Account {account_number} will retry {group} after {retry_until.isoformat()}")
    save_data(db)

def mark_group_sent(group):
    groups = db.get("groups", [])
    if group in groups:
        db["last_sent_group_index"] = groups.index(group)
        save_data(db)

def get_next_template():
    templates = db.get("templates", [])
    if not templates:
        return None
    return random.choice(templates)

async def send_message_with_transport_backoff(client, chat_id, text):
    """Send without opening another client and back off on transport 429s."""
    for attempt in range(len(TRANSPORT_RETRY_DELAYS) + 1):
        try:
            return await client.send_message(chat_id, text)
        except FloodWait:
            raise
        except Exception as error:
            error_text = str(error).casefold()
            is_transport_flood = (
                isinstance(error, OSError)
                or "transport flood" in error_text
                or "socket.send" in error_text
                or "server sent transport error: 429" in error_text
            )
            if not is_transport_flood or attempt >= len(TRANSPORT_RETRY_DELAYS):
                raise

            delay = TRANSPORT_RETRY_DELAYS[attempt]
            print(
                f"⏳ Telegram transport flood؛ إعادة المحاولة بعد "
                f"{delay} ثانية"
            )
            await asyncio.sleep(delay)

# --- Get account info with caching ---
async def get_account_info(session_str, index):
    cache_key = f"{index}_{hash(session_str)}"
    cache = get_account_cache()
    if cache_key in cache:
        return cache[cache_key]
    try:
        temp_client = Client(
            f"info_session_{current_profile_id()}_{index}",
            api_id=API_ID,
            api_hash=API_HASH,
            session_string=_normalize_session_string(session_str),
            in_memory=True,
        )
        await temp_client.connect()
        me = await temp_client.get_me()
        info = {
            "phone": me.phone_number or "غير معروف", 
            "name": me.first_name or "غير معروف", 
            "connected": True,
            "id": me.id,
            "username": me.username or ""
        }
        await temp_client.disconnect()
        cache[cache_key] = info
        return info
    except:
        info = {"phone": "غير معروف", "name": "غير متصل", "connected": False, "id": None, "username": ""}
        cache[cache_key] = info
        return info

def normalize_phone_number(phone):
    return re.sub(r"\D+", "", str(phone or ""))

def find_account_owner_by_session(session_str):
    normalized_session = str(session_str or "").strip()
    if not normalized_session:
        return None
    for profile in profile_store.get("profiles", []):
        accounts = (profile.get("data") or {}).get("accounts", [])
        for index, existing_session in enumerate(accounts):
            if str(existing_session or "").strip() == normalized_session:
                return {
                    "profile_name": profile.get("name") or "مجموعة بدون اسم",
                    "profile_id": profile.get("id"),
                    "account_number": index + 1,
                }
    return None

async def find_account_owner_by_phone(phone):
    normalized_phone = normalize_phone_number(phone)
    if not normalized_phone:
        return None

    for profile in profile_store.get("profiles", []):
        profile_id = profile.get("id")
        accounts = (profile.get("data") or {}).get("accounts", [])
        token = profile_context.set(profile_id)
        try:
            for index, session_str in enumerate(accounts):
                info = await get_account_info(session_str, index)
                if (
                    info.get("connected")
                    and normalize_phone_number(info.get("phone")) == normalized_phone
                ):
                    return {
                        "profile_name": profile.get("name") or "مجموعة بدون اسم",
                        "profile_id": profile_id,
                        "account_number": index + 1,
                        "phone": info.get("phone"),
                    }
        finally:
            profile_context.reset(token)
    return None

def duplicate_account_warning(owner, phone):
    return (
        "⚠️ لا يمكن إضافة هذا الحساب.\n\n"
        f"📱 الرقم: {phone}\n"
        f"📂 مستخدم مسبقًا في: {owner.get('profile_name', 'مجموعة غير معروفة')}\n"
        f"🔢 رقم الحساب هناك: {owner.get('account_number', '?')}\n\n"
        "لا يمكن استخدام نفس الرقم في أكثر من مجموعة."
    )

# --- 🔥 Account Status Check ---
async def check_account_status(client, account_number):
    try:
        me = await client.get_me()
        return {"status": "active", "message": f"✅ الحساب {account_number} يعمل بشكل طبيعي"}
    except FloodWait as e:
        wait_time = e.x
        error_msg = f"⏳ الحساب {account_number} ممنوع مؤقتاً لمدة {wait_time} ثانية"
        print(f"⚠️ {error_msg}")
        await notify_owner(error_msg)
        return {"status": "flood", "message": error_msg, "wait": wait_time}
    except Exception as e:
        error_msg = f"❌ الحساب {account_number} عالق أو محظور: {str(e)[:50]}"
        print(f"⚠️ {error_msg}")
        await notify_owner(error_msg)
        return {"status": "error", "message": error_msg}

async def notify_owner(message):
    try:
        await app.send_message(OWNER_ID, f"⚠️ تنبيه البوت:\n{message}")
    except:
        print(f"⚠️ فشل إرسال إشعار للمالك: {message}")

# --- Auto Leave Channels (24 hours) ---
async def auto_leave_channels():
    global db
    while True:
        try:
            now = datetime.now()
            to_remove = []
            for channel, join_time in db.get("joined_channels", {}).items():
                try:
                    join_dt = datetime.fromisoformat(join_time)
                    if now - join_dt > timedelta(hours=24):
                        to_remove.append(channel)
                except:
                    to_remove.append(channel)
            for channel in to_remove:
                success = True
                for idx, session_str in enumerate(db["accounts"]):
                    user_app = None
                    try:
                        user_app = Client(
                            f"leave_session_{idx}",
                            api_id=API_ID,
                            api_hash=API_HASH,
                            session_string=_normalize_session_string(session_str),
                            in_memory=True,
                        )
                        await _start_user_client(user_app, start_updates=False)
                        await user_app.leave_chat(get_group_chat_target(channel))
                        print(f"🚪 Acc {idx+1} left {channel}")
                    except Exception as e:
                        success = False
                        print(f"❌ Leave {channel} failed: {e}")
                    finally:
                        if user_app:
                            try:
                                await user_app.stop()
                            except Exception:
                                pass
                if success:
                    db["joined_channels"].pop(channel, None)
                    db["channel_join_time"].pop(channel, None)
                    for account_channels in db.get("account_joined_channels", {}).values():
                        account_channels.pop(channel, None)
                    save_data(db)
            await asyncio.sleep(3600)
        except Exception as e:
            print(f"❌ Auto leave error: {e}")
            await asyncio.sleep(60)

def ensure_auto_leave_task():
    return

async def resolve_chat_for_join(client, channel):
    raw_value = str(channel or "").strip()
    clean_link = clean_group_link(raw_value)
    username_target = clean_link if clean_link.startswith("@") else None
    candidates = []
    for candidate in (
        username_target,
        raw_value,
        clean_link,
        clean_link[1:] if clean_link.startswith("@") else None,
    ):
        if candidate and candidate not in candidates:
            candidates.append(candidate)

    for candidate in candidates:
        try:
            chat_info = await client.get_chat(candidate)
            if chat_info and getattr(chat_info, "id", None) is not None:
                return chat_info, candidate
        except Exception:
            continue

    return None, clean_link

async def scan_recent_group_messages_for_mandatory_channels(client, account_index):
    profile_id = current_profile_id()
    if profile_id in profile_recent_scan_claims:
        return
    profile_recent_scan_claims.add(profile_id)

    discovered_links = set()
    history_limit = 50
    for group in list(db.get("groups", [])):
        try:
            chat_info, resolved_target = await resolve_chat_for_join(client, group)
            history_target = (
                getattr(chat_info, "id", None)
                if chat_info is not None
                else resolved_target
            )
            if history_target is None:
                continue

            resolved_chat_id = getattr(chat_info, "id", None)
            if resolved_chat_id is not None:
                db.setdefault("group_chat_ids", {})[
                    clean_group_link(group)
                ] = str(resolved_chat_id)

            async for message in client.get_chat_history(
                history_target,
                limit=history_limit,
            ):
                # Only bot-authored messages are allowed to trigger joins.
                # A normal user's link, forwarded post, or channel post must
                # never be treated as a mandatory-subscription instruction.
                if should_auto_join_from_message(message):
                    discovered_links.update(extract_all_links(message))
                    discovered_links.update(
                        await click_join_buttons(client, message)
                    )
        except Exception as error:
            print(
                f"⚠️ Userbot {account_index + 1} could not scan {group}: "
                f"{str(error)[:120]}"
            )

    if not discovered_links:
        return

    print(
        f"🔎 Userbot {account_index + 1} found "
        f"{len(discovered_links)} existing mandatory link(s)"
    )
    for link in discovered_links:
        try:
            await join_channel_for_all_accounts(link)
        except Exception as error:
            print(
                f"⚠️ Existing mandatory link {link} was skipped: "
                f"{str(error)[:120]}"
            )

# --- Join channel for all accounts ---
async def join_channel_for_account(session_str, account_index, channel, client=None):
    clean_link = clean_group_link(channel)
    if not clean_link:
        return False

    account_key = str(account_index)
    account_joined_channels = db.setdefault("account_joined_channels", {})
    already_confirmed = account_joined_channels.get(account_key, {}).get(clean_link) is True
    if already_confirmed:
        print(f"✅ Acc {account_index + 1} already joined {clean_link}; skipping")
        return True

    join_waits = db.setdefault("account_join_waits", {})
    wait_key = f"{account_key}:{clean_link}"
    wait_until = float(join_waits.get(wait_key, 0) or 0)
    now_ts = datetime.now().timestamp()
    if wait_until > now_ts:
        remaining = max(1, int(wait_until - now_ts))
        print(
            f"⏳ Acc {account_index + 1} skipping {clean_link}; "
            f"Telegram join wait {remaining}s remains"
        )
        return False
    join_waits.pop(wait_key, None)

    def remember_join_flood_wait(error):
        seconds = max(1, int(getattr(error, "x", 60) or 60))
        join_waits[wait_key] = datetime.now().timestamp() + seconds
        save_data(db)
        print(
            f"⏳ Acc {account_index + 1} must wait {seconds}s before "
            f"retrying join for {clean_link}"
        )

    user_app = client
    owns_client = user_app is None
    joined = False
    try:
        if owns_client:
            user_app = Client(
                f"join_session_{current_profile_id()}_{account_index}",
                api_id=API_ID,
                api_hash=API_HASH,
                session_string=_normalize_session_string(session_str),
                in_memory=True,
            )
            await _start_user_client(user_app, start_updates=False)
        chat_info, resolved_target = await resolve_chat_for_join(user_app, channel)
        if chat_info is None and is_private_invite_link(clean_link):
            chat_info = await get_chat_from_private_invite(user_app, clean_link)
        if chat_info and getattr(chat_info, "id", None) is not None:
            db.setdefault("group_chat_ids", {})[clean_link] = str(chat_info.id)

        join_targets = []
        if is_private_invite_link(clean_link):
            join_targets.append(clean_link)
        else:
            chat_username = getattr(chat_info, "username", None) if chat_info else None
            if chat_username:
                join_targets.append(f"@{str(chat_username).lstrip('@')}")
            if clean_link.startswith("@"):
                join_targets.append(clean_link)
            if resolved_target and not str(resolved_target).startswith("https://t.me/"):
                join_targets.append(resolved_target)
            if chat_info and getattr(chat_info, "id", None) is not None:
                join_targets.append(int(chat_info.id))
            join_targets.append(clean_link)

        unique_targets = []
        for target in join_targets:
            if target not in unique_targets:
                unique_targets.append(target)

        last_error = None
        skip_followup_lookup = False
        for join_target in unique_targets:
            try:
                print(
                    f"🔎 Acc {account_index + 1} trying join target "
                    f"{join_target!r} for {clean_link}"
                )
                joined_chat = await user_app.join_chat(join_target)
                joined = True
                print(f"✅ Acc {account_index + 1} joined {clean_link}")
                if getattr(joined_chat, "id", None) is not None:
                    db.setdefault("group_chat_ids", {})[clean_link] = str(joined_chat.id)
                break
            except Exception as error:
                last_error = error
                error_text = str(error).upper()
                if isinstance(error, FloodWait):
                    remember_join_flood_wait(error)
                    skip_followup_lookup = True
                    print(
                        f"⚠️ Acc {account_index + 1} join paused for "
                        f"{getattr(error, 'x', 60)}s"
                    )
                    break
                if "ALREADY_PARTICIPANT" in error_text or "USER_ALREADY_PARTICIPANT" in error_text:
                    joined = True
                    print(f"✅ Acc {account_index + 1} is already in {clean_link}")
                    break
                if any(
                    marker in error_text
                    for marker in (
                        "USER_NOT_ACCEPTED",
                        "INVITE_REQUEST_SENT",
                        "INVITE_HASH_EXPIRED",
                        "INVITE_HASH_INVALID",
                    )
                ):
                    skip_followup_lookup = True
                    print(
                        f"⚠️ Acc {account_index + 1} cannot join {clean_link}; "
                        "Telegram rejected the invite"
                    )
                    break
                print(
                    f"⚠️ Acc {account_index + 1} target {join_target!r} failed: {error}"
                )

        if not joined and last_error is not None:
            record_failure(account_index + 1, clean_link, last_error)
            print(f"❌ Acc {account_index + 1} failed to join {clean_link}: {last_error}")
        if joined:
            account_joined_channels.setdefault(account_key, {})[clean_link] = True
        if not joined and skip_followup_lookup:
            return False
        if clean_link not in db.get("group_chat_ids", {}):
            try:
                chat_info = await user_app.get_chat(resolved_target)
            except Exception:
                chat_info = await get_chat_from_private_invite(user_app, clean_link)
            if chat_info and getattr(chat_info, "id", None) is not None:
                db.setdefault("group_chat_ids", {})[clean_link] = str(chat_info.id)
    except FloodWait as error:
        remember_join_flood_wait(error)
        record_failure(account_index + 1, clean_link, error)
        print(
            f"⏳ Acc {account_index + 1} join paused for "
            f"{getattr(error, 'x', 60)}s: {clean_link}"
        )
    except Exception as error:
        record_failure(account_index + 1, clean_link, error)
        print(f"❌ Error opening acc {account_index + 1} for {clean_link}: {error}")
    finally:
        if user_app and owns_client:
            try:
                await user_app.stop()
            except Exception:
                pass
    return joined

async def join_account_to_configured_groups(session_str, account_index):
    groups = list(db.get("groups", []))
    mandatory_channels = list(db.get("joined_channels", {}).keys())
    joined_count = 0

    for channel in mandatory_channels:
        await join_channel_for_account(
            session_str,
            account_index,
            channel,
            client=profile_active_clients.get(current_profile_id(), {}).get(account_index),
        )

    for group in groups:
        if await join_channel_for_account(
            session_str,
            account_index,
            group,
            client=profile_active_clients.get(current_profile_id(), {}).get(account_index),
        ):
            joined_count += 1

    if groups or mandatory_channels:
        save_data(db)
    return joined_count, len(groups)

async def join_all_accounts_to_configured_groups():
    results = []
    for account_index, session_str in enumerate(list(db.get("accounts", []))):
        try:
            joined_count, total_groups = await join_account_to_configured_groups(
                session_str, account_index
            )
            results.append({
                "account": account_index + 1,
                "joined": joined_count,
                "total": total_groups,
            })
        except Exception as error:
            record_failure(
                account_index + 1,
                "كل الكروبات المسجلة",
                error,
                reason="تعذر فحص انضمام الحساب إلى الكروبات.",
                solution="تحقق من Session String ومن أن الحساب يستطيع دخول الكروبات، ثم أعد التشغيل.",
            )
            results.append({
                "account": account_index + 1,
                "joined": 0,
                "total": len(db.get("groups", [])),
            })
    if results:
        save_data(db)
    return results

async def _join_channel_for_all_accounts(channel, track_for_auto_leave=True):
    clean_link = clean_group_link(channel)
    if not clean_link:
        return

    if track_for_auto_leave:
        ensure_auto_leave_task()
        mandatory_channels = db.setdefault("joined_channels", {})
        if clean_link in mandatory_channels:
            print(f"🔁 Rechecking mandatory channel {clean_link} for every account")
        else:
            join_time = datetime.now().isoformat()
            mandatory_channels[clean_link] = join_time
            db.setdefault("channel_join_time", {})[clean_link] = join_time
            save_data(db)

    joined_any = False
    print(f"📢 Joining {clean_link} for all accounts...")
    active_clients = profile_active_clients.get(current_profile_id(), {})
    for idx, session_str in enumerate(db["accounts"]):
        try:
            if await join_channel_for_account(
                session_str,
                idx,
                clean_link,
                client=active_clients.get(idx),
            ):
                joined_any = True
        except Exception as error:
            print(
                f"⚠️ Acc {idx + 1} mandatory join skipped for "
                f"{clean_link}: {str(error)[:160]}"
            )

    if joined_any:
        save_data(db)
    if track_for_auto_leave:
        joined_count = sum(
            1
            for account_channels in db.get("account_joined_channels", {}).values()
            if isinstance(account_channels, dict)
            and account_channels.get(clean_link) is True
        )
        total_accounts = len(db.get("accounts", []))
        if joined_count == total_accounts and total_accounts:
            print(
                f"✅ Mandatory channel {clean_link} joined by "
                f"all {total_accounts} account(s)"
            )
        else:
            print(
                f"⚠️ Mandatory channel {clean_link}: "
                f"{joined_count}/{total_accounts} account(s) joined; "
                "it remains queued for the next retry/startup"
            )
    elif joined_any:
        print(f"✅ All accounts checked/joined posting group {clean_link}; it will remain in the list")

async def join_channel_for_all_accounts(channel, track_for_auto_leave=True):
    """Serialize auto-join operations so multiple updates cannot fan out clients."""
    clean_link = clean_group_link(channel)
    if not clean_link:
        return

    operation_key = (current_profile_id(), clean_link)
    if operation_key in join_operations_in_progress:
        print(f"⏭️ Join for {clean_link} is already in progress; skipping duplicate trigger")
        return

    join_operations_in_progress.add(operation_key)
    try:
        return await _join_channel_for_all_accounts(
            clean_link,
            track_for_auto_leave=track_for_auto_leave,
        )
    finally:
        join_operations_in_progress.discard(operation_key)

# --- 🚀 MAIN POSTING LOOP ---
async def ensure_account_in_group(client, group, account_number):
    clean_link = clean_group_link(group) or str(group)
    account_key = str(account_number - 1)
    wait_key = f"{account_key}:{clean_link}"
    waits = db.setdefault("account_group_waits", {})
    now_ts = datetime.now().timestamp()
    wait_until = float(waits.get(wait_key, 0) or 0)
    if wait_until > now_ts:
        remaining = max(1, int(wait_until - now_ts))
        print(f"⏳ Acc {account_number} skipping {clean_link}; Telegram wait {remaining}s remains")
        return False, False
    waits.pop(wait_key, None)

    def remember_flood_wait(error):
        seconds = max(1, int(getattr(error, "x", 60) or 60))
        waits[wait_key] = datetime.now().timestamp() + seconds
        save_data(db)
        print(f"⏳ Acc {account_number} must wait {seconds}s before retrying {clean_link}")

    def mark_member(chat_id=None):
        account_memberships.setdefault(account_key, {})[clean_link] = True
        if chat_id is not None:
            db.setdefault("group_chat_ids", {})[clean_link] = str(chat_id)
        save_data(db)

    account_memberships = db.setdefault("account_joined_channels", {})
    known_member = account_memberships.get(account_key, {}).get(clean_link) is True
    if known_member:
        # The membership was already verified for this session. Rechecking
        # get_chat/get_chat_member before every post creates unnecessary RPC
        # traffic and is a common trigger for Telegram transport flood 429s.
        return True, False

    chat_target = clean_link
    try:
        member = await client.get_chat_member(chat_target, "me")
        status = getattr(member, "status", "")
        status = getattr(status, "value", status)
        if str(status).lower() not in ("left", "kicked", "banned"):
            mark_member(getattr(member, "chat", None) and getattr(member.chat, "id", None))
            return True, False
    except FloodWait as error:
        remember_flood_wait(error)
        return False, False
    except Exception:
        pass

    try:
        resolved_chat = await client.get_chat(clean_link)
        resolved_id = getattr(resolved_chat, "id", None)
        if resolved_id is not None:
            db.setdefault("group_chat_ids", {})[clean_link] = str(resolved_id)
            member = await client.get_chat_member(resolved_id, "me")
            status = getattr(member, "status", "")
            status = getattr(status, "value", status)
            if str(status).lower() not in ("left", "kicked", "banned"):
                mark_member(resolved_id)
                return True, False
    except FloodWait as error:
        remember_flood_wait(error)
        return False, False
    except Exception:
        pass

    try:
        joined_chat = await client.join_chat(group)
        mark_member(getattr(joined_chat, "id", None))
        print(f"✅ Account {account_number} joined {group} before posting")
        return True, False
    except FloodWait as error:
        remember_flood_wait(error)
        return False, False
    except Exception as error:
        error_text = str(error).upper()
        if "ALREADY_PARTICIPANT" in error_text or "USER_ALREADY_PARTICIPANT" in error_text:
            try:
                resolved_chat = await client.get_chat(clean_link)
                resolved_id = getattr(resolved_chat, "id", None)
                if resolved_id is not None:
                    mark_member(resolved_id)
                    return True, False
            except Exception:
                pass
            account_memberships.get(account_key, {}).pop(clean_link, None)
            db.setdefault("group_chat_ids", {}).pop(clean_link, None)
            save_data(db)
            print(
                f"❌ Account {account_number} is already a member of {clean_link}, "
                "but Telegram did not expose its peer; use an @username or invite link"
            )
            return False, True
        permanent = is_permanent_group_error(error_text)
        print(f"❌ Account {account_number} could not join {group}: {error}")
        return False, permanent

async def auto_posting_loop():
    global db
    active_clients = []
    account_info = []
    try:
        for idx, session_str in enumerate(db["accounts"]):
            try:
                client = Client(
                    f"active_session_{current_profile_id()}_{idx}",
                    api_id=API_ID,
                    api_hash=API_HASH,
                    session_string=_normalize_session_string(session_str),
                    in_memory=True,
                )
                me = await _start_user_client(client)
                active_clients.append(client)
                account_info.append({
                    "index": idx,
                    "number": idx + 1,
                    "phone": me.phone_number,
                    "name": me.first_name,
                    "client": client
                })
                print(f"✅ Account {idx+1} connected: {me.phone_number}")
            except FloodWait as e:
                error_msg = f"⏳ الحساب {idx+1} ممنوع مؤقتاً لمدة {e.x} ثانية"
                print(f"⚠️ {error_msg}")
                await notify_owner(error_msg)
                active_clients.append(None)
                account_info.append({"index": idx, "number": idx+1, "status": "flood", "error": str(e)})
            except AuthKeyUnregistered:
                error_msg = f"❌ الحساب {idx+1} جلسته ملغاة (SESSION_REVOKED). يرجى حذفه وإعادة إضافته."
                print(f"⚠️ {error_msg}")
                await notify_owner(error_msg)
                active_clients.append(None)
                account_info.append({"index": idx, "number": idx+1, "status": "revoked", "error": "SESSION_REVOKED"})
            except Exception as e:
                error_msg = f"❌ فشل اتصال الحساب {idx+1}: {str(e)[:50]}"
                print(f"⚠️ {error_msg}")
                await notify_owner(error_msg)
                active_clients.append(None)
                account_info.append({"index": idx, "number": idx+1, "status": "error", "error": str(e)})

        timer_value = max(MIN_SEND_INTERVAL, int(db.get("timer", 60)))
        valid_accounts = [info for info in account_info if info.get("client") is not None]
        if not valid_accounts:
            error_msg = "❌ لا يوجد حسابات نشطة! إيقاف البوت."
            print(error_msg)
            await notify_owner(error_msg)
            db["is_running"] = False
            save_data(db)
            return

        profile_active_clients[current_profile_id()] = {
            info["index"]: info["client"] for info in valid_accounts
        }

        # Attach bot-message monitoring to these same live clients. This
        # preserves the feature without opening a duplicate session per user.
        await start_all_userbots(valid_accounts)

        print(f"🚀 Starting with {len(valid_accounts)} active accounts, interval: {timer_value}s")
        await notify_owner(f"🚀 بدء تشغيل البوت\n📊 {len(valid_accounts)} حساب نشط\n⏱ الفاصل بين كل إرسال: {timer_value} ثانية")

        consecutive_errors = {info["number"]: 0 for info in valid_accounts}
        max_errors = 5

        async def post_to_group(acc_info, group):
            """تشغيل إرسال مستقل لكل كروب مع منع التزامن."""
            if not db["is_running"]:
                return
            client = acc_info["client"]
            acc_number = acc_info["number"]
            
            # تخطي الحسابات الملغاة
            if acc_info.get("status") == "revoked":
                return
                
            try:
                # الانتظار قبل الإرسال لمنع الفلود
                await asyncio.sleep(timer_value)
                
                template = get_next_template()
                if template is None:
                    return

                joined, permanent_error = await ensure_account_in_group(client, group, acc_number)
                if not joined:
                    db["stats"]["failed_count"] += 1
                    record_failure(
                        acc_number,
                        group,
                        "GROUP_JOIN_FAILED",
                        reason="لم يتمكن الحساب من الوصول إلى المجموعة أو الانضمام إليها.",
                        solution="أعد إضافة المجموعة باستخدام @username أو رابط دعوة صحيح، وتأكد أن الحساب عضو فيها.",
                    )
                    advance_group_after_attempt(group)
                    if permanent_error:
                        block_account_from_group(acc_number, group)
                    save_data(db)
                    return

                send_target = await get_account_group_target(client, group)
                sent_msg = await send_message_with_transport_backoff(
                    client,
                    send_target,
                    template,
                )
                db["stats"]["sent_count"] += 1
                mark_account_group_sent(acc_number, group)
                db.setdefault("outgoing_messages", {})
                db["outgoing_messages"].setdefault(str(sent_msg.chat.id), {})[sent_msg.id] = {
                    "from_account": acc_number,
                    "time": datetime.now().isoformat(),
                    "template": template
                }
                mark_group_sent(group)
                save_data(db)
                consecutive_errors[acc_number] = 0
                print(f"✅ Acc {acc_number} sent message to {group}")
                
            except FloodWait as e:
                db["stats"]["failed_count"] += 1
                record_failure(acc_number, group, f"FLOOD_WAIT: {e.x}s")
                save_data(db)
                error_msg = f"⏳ Acc {acc_number} flood wait {e.x}s on {group}"
                print(f"⚠️ {error_msg}")
                await notify_owner(error_msg)
                await asyncio.sleep(e.x)
            except AuthKeyUnregistered:
                db["stats"]["failed_count"] += 1
                record_failure(acc_number, group, "SESSION_REVOKED: AuthKeyUnregistered")
                error_msg = f"🚫 الحساب {acc_number} تم إلغاء جلسته (SESSION_REVOKED). يرجى حذفه وإعادة إضافته."
                print(f"❌ {error_msg}")
                await notify_owner(error_msg)
                acc_info["status"] = "revoked"
            except UserBannedInChannel:
                db["stats"]["failed_count"] += 1
                record_failure(acc_number, group, "USER_BANNED_IN_CHANNEL")
                error_msg = f"🚫 الحساب {acc_number} ممنوع في {group}"
                print(f"❌ {error_msg}")
                await notify_owner(error_msg)
                advance_group_after_attempt(group)
                block_account_from_group(acc_number, group)
            except Exception as e:
                db["stats"]["failed_count"] += 1
                error_text = str(e)
                
                # التحقق من أخطاء الجلسة الملغاة
                if "SESSION_REVOKED" in error_text or "AUTH_KEY_UNREGISTERED" in error_text:
                    record_failure(acc_number, group, "SESSION_REVOKED")
                    error_msg = f"🚫 الحساب {acc_number} تم إلغاء جلسته. يرجى حذفه وإعادة إضافته."
                    print(f"❌ {error_msg}")
                    await notify_owner(error_msg)
                    acc_info["status"] = "revoked"
                else:
                    record_failure(acc_number, group, error_text)
                    print(f"❌ Acc {acc_number} failed to send to {group}: {error_text}")
                    consecutive_errors[acc_number] += 1
                    advance_group_after_attempt(group)
                    if is_permanent_group_error(error_text):
                        block_account_from_group(acc_number, group)
                        print(f"⏭️ Account {acc_number} will skip {group}: no send permission or invalid peer")

        while db["is_running"]:
            if not db["accounts"] or not db["templates"] or not db["groups"]:
                db["is_running"] = False
                save_data(db)
                break

            groups_this_round = list(db.get("groups", []))
            rotation_index = int(db.get("account_rotation_index", 0) or 0) % len(valid_accounts)
            
            # التنفيذ التسلسلي بدلاً من المتزامن لمنع الفلود
            for group_index, group in enumerate(groups_this_round):
                if not db["is_running"]:
                    break
                    
                acc_info = valid_accounts[(group_index + rotation_index) % len(valid_accounts)]
                
                # تخطي الحسابات الملغاة
                if acc_info.get("status") == "revoked":
                    continue
                    
                await post_to_group(acc_info, group)

            db["account_rotation_index"] = (rotation_index + 1) % len(valid_accounts)
            save_data(db)
    except Exception as e:
        error_msg = f"❌ خطأ رئيسي في حلقة النشر: {str(e)}"
        print(f"❌ {error_msg}")
        await notify_owner(error_msg)
    finally:
        await stop_all_userbots(current_profile_id())
        profile_active_clients.pop(current_profile_id(), None)
        for client in active_clients:
            if client:
                try:
                    await client.stop()
                except:
                    pass
        if db["is_running"]:
            db["is_running"] = False
            save_data(db)
            await notify_owner("🛑 تم إيقاف البوت تلقائياً بسبب خطأ")

# ===== ⭐ جديد: مراقبة الحسابات (Userbots) لاستقبال رسائل البوتات في الكروبات =====
def is_bot_generated_message(message):
    sender = getattr(message, "from_user", None)
    return bool(sender and getattr(sender, "is_bot", False))

def is_group_message(message):
    chat = getattr(message, "chat", None)
    chat_type = str(getattr(chat, "type", "") or "").casefold()
    return chat_type.rsplit(".", 1)[-1] in {"group", "supergroup"}

def is_channel_post(message):
    chat = getattr(message, "chat", None)
    chat_type = str(getattr(chat, "type", "") or "").lower()
    return chat_type.rsplit(".", 1)[-1] == "channel"

def has_forwarded_chat(message):
    if getattr(message, "forward_from_chat", None):
        return True
    forward_origin = getattr(message, "forward_origin", None)
    return bool(getattr(forward_origin, "chat", None))

def is_automated_or_channel_message(_, __, message):
    return bool(
        is_bot_generated_message(message)
        or is_channel_post(message)
        or getattr(message, "sender_chat", None)
        or has_forwarded_chat(message)
    )

def should_auto_join_from_message(message):
    # These are the only message-level gates for automatic joining:
    # the sender must be a real Telegram bot and the chat must be one of the
    # groups configured by the owner. Link parsing is handled separately.
    return bool(
        is_bot_generated_message(message)
        and get_configured_group_for_chat(getattr(message, "chat", None))
    )

AUTOMATED_OR_CHANNEL_FILTER = filters.create(
    is_automated_or_channel_message,
    name="automated_or_channel_message",
)

def get_message_context(chat_id, message_id):
    for collection in ("outgoing_messages", "incoming_messages"):
        chat_messages = db.get(collection, {}).get(str(chat_id), {})
        info = chat_messages.get(message_id) or chat_messages.get(str(message_id))
        if info:
            return info
    return None

def get_outgoing_message_context(chat_id, message_id):
    chat_messages = db.get("outgoing_messages", {}).get(str(chat_id), {})
    return chat_messages.get(message_id) or chat_messages.get(str(message_id))

def get_configured_group_for_chat(chat):
    if not chat:
        return None
    chat_id = str(getattr(chat, "id", ""))
    username = (getattr(chat, "username", None) or "").casefold()
    known_chat_ids = db.get("group_chat_ids", {})

    for group in db.get("groups", []):
        clean_group = clean_group_link(group)
        if clean_group == chat_id:
            return group
        if username and clean_group.casefold() == f"@{username}":
            return group
        if str(known_chat_ids.get(clean_group, "")) == chat_id:
            return group
    return None

def record_group_interaction(message):
    if not message.from_user or message.from_user.is_bot:
        return
    group = get_configured_group_for_chat(message.chat)
    if not group:
        return

    message_key = (str(message.chat.id), message.id)
    if message_key not in group_message_keys:
        group_message_keys.add(message_key)
        if len(group_message_keys) > 10000:
            group_message_keys.clear()
        db.setdefault("incoming_activity", {})[group] = datetime.now().isoformat()
        for account_key, posts_by_group in db.get("account_group_posts", {}).items():
            if int(posts_by_group.get(group, 0) or 0) <= 0:
                continue
            incoming_by_group = db.setdefault(
                "account_group_incoming", {}
            ).setdefault(account_key, {})
            incoming_by_group[group] = int(incoming_by_group.get(group, 0) or 0) + 1
        save_data(db)
        print(f"🔥 Latest group interaction: {group}")

async def forward_group_message_to_owner(message, source_account=None):
    if not message.from_user or message.from_user.is_bot:
        return

    record_group_interaction(message)
    chat_id = str(message.chat.id)
    replied = message.reply_to_message
    if not replied:
        return

    reply_info = get_outgoing_message_context(chat_id, replied.id)
    if not reply_info:
        return

    key = (chat_id, message.id)
    if key in forwarded_incoming:
        if source_account:
            saved_incoming = db.get("incoming_messages", {}).get(chat_id, {}).get(message.id)
            if saved_incoming is None:
                saved_incoming = db.get("incoming_messages", {}).get(chat_id, {}).get(str(message.id))
            if saved_incoming and not saved_incoming.get("from_account"):
                saved_incoming["from_account"] = reply_info.get("from_account") or source_account
                save_data(db)
        return
    forwarded_incoming.add(key)
    if len(forwarded_incoming) > 5000:
        forwarded_incoming.clear()

    account_number = reply_info.get("from_account") or source_account
    incoming = db.setdefault("incoming_messages", {}).setdefault(chat_id, {})
    incoming[message.id] = {
        "is_reply": True,
        "reply_to_message_id": replied.id,
        "from_account": account_number,
        "time": datetime.now().isoformat(),
        "text": message.text or message.caption or "[وسائط]",
        "from_user_id": message.from_user.id,
        "from_username": message.from_user.username or "",
        "from_name": f"{message.from_user.first_name} {message.from_user.last_name or ''}".strip(),
        "chat_title": message.chat.title or "بدون اسم"
    }
    save_data(db)
    print(f"📩 Saved reply from {message.from_user.id} in {chat_id} for account {account_number}")

async def start_userbot_monitor(client, index):
    """Monitor an already-connected posting client for bot join instructions."""
    handler_ref = None

    async def userbot_message_handler(ub_client, message):
        try:
            # Only the two gates in should_auto_join_from_message matter here:
            # configured chat and bot sender. Link parsing happens afterward.
            if not should_auto_join_from_message(message):
                return
            links = set(extract_all_links(message))
            clicked_links = await click_join_buttons(ub_client, message)
            links.update(clicked_links)
            if links:
                print(
                    f"🤖 Userbot {index+1} found "
                    f"{len(links)} link(s); all accounts will join"
                )
                for link in links:
                    await join_channel_for_all_accounts(link)
        except Exception as error:
            print(f"⚠️ Userbot {index+1} skipped an update: {error}")

    try:
        handler_ref = client.add_handler(
            handlers.MessageHandler(userbot_message_handler, filters.incoming)
        )
        await scan_recent_group_messages_for_mandatory_channels(client, index)
        print(f"✅ Userbot {index+1} started monitoring groups")
        while True:
            await asyncio.sleep(3600)
    except Exception as e:
        print(f"❌ Userbot {index+1} failed: {str(e)[:80]}")
    finally:
        if handler_ref:
            try:
                client.remove_handler(*handler_ref)
            except Exception:
                pass

async def start_all_userbots(account_info=None):
    profile_id = current_profile_id()
    # Calls from menu actions do not carry the live clients and must not
    # disturb the monitors already attached to the posting loop.
    if not account_info:
        print("ℹ️ Userbot monitoring is waiting for the posting clients")
        return

    if not ENABLE_USERBOT_MONITORING:
        await stop_all_userbots(profile_id)
        profile_userbot_tasks[profile_id] = []
        print(
            "ℹ️ Userbot monitoring disabled; "
            "posting uses one connection per account"
        )
        return

    await stop_all_userbots(profile_id)
    profile_recent_scan_claims.discard(profile_id)
    tasks = []
    profile_userbot_tasks[profile_id] = tasks
    for account in account_info:
        task = asyncio.create_task(
            start_userbot_monitor(account["client"], account["index"])
        )
        tasks.append(task)
    print(f"🚀 Started monitoring {len(tasks)} accounts for {profile_id}")

async def start_profile_services(profile_id):
    token = profile_context.set(profile_id)
    try:
        # Do not create a temporary client for every account/group at startup.
        # The posting loop verifies the target with the same persistent client
        # and joins only when that account actually reaches the group.
        if not db.get("is_running"):
            return

        posting_task = asyncio.create_task(auto_posting_loop())
        profile_posting_tasks[profile_id] = posting_task
        await app.send_message(
            OWNER_ID,
            "✅ بدأت حلقة النشر.\n"
            "سيتم فحص عضوية كل حساب عند أول إرسال باستخدام نفس الاتصال."
        )
    except asyncio.CancelledError:
        raise
    except Exception as error:
        db["is_running"] = False
        save_data(db)
        print(f"❌ فشل تجهيز خدمات المجموعة {profile_id}: {error}")
        try:
            await app.send_message(
                OWNER_ID,
                f"❌ تعذر تشغيل البوت بعد الضغط على بدء:\n{str(error)[:500]}"
            )
        except Exception:
            pass
    finally:
        profile_context.reset(token)

# --- ✅ المعالج الأهم والأول: أي رسالة من بوت تحتوي روابط (يعمل إذا كان البوت الرئيسي عضواً) ---
@app.on_message(
    filters.incoming,
    group=0,
)
async def handle_bot_messages_with_links(client: Client, message: Message):
    if not should_auto_join_from_message(message):
        return
    if not get_configured_group_for_chat(message.chat):
        return
    links = extract_all_links(message)
    if not links:
        return
    sender = getattr(message, "from_user", None)
    sender_chat = getattr(message, "sender_chat", None)
    sender_name = (
        getattr(sender, "username", None)
        or getattr(sender_chat, "username", None)
        or getattr(sender_chat, "title", None)
        or "anonymous sender"
    )
    print(f"🤖 Bot '{sender_name}' sent a message with {len(links)} channel link(s). Joining...")
    for link in links:
        try:
            await join_channel_for_all_accounts(link)
        except Exception as error:
            print(f"⚠️ Main bot skipped auto-join update: {error}")

# --- Handle incoming group messages and replies ---
@app.on_message(
    filters.incoming & AUTOMATED_OR_CHANNEL_FILTER,
    group=1,
)
async def handle_user_replies(client: Client, message: Message):
    try:
        await forward_group_message_to_owner(message)
    except Exception as error:
        print(f"⚠️ Main bot skipped group update: {error}")

# --- Handle private messages from users (non-owner) ---
@app.on_message(filters.private & filters.incoming & ~filters.user(OWNER_ID), group=2)
async def handle_private_messages(client: Client, message: Message):
    if not message.from_user:
        return
    user_info = f"""
📩 **رسالة خاصة جديدة**

👤 **المرسل:**
• الأيدي: `{message.from_user.id}`
• اليوزر: @{message.from_user.username or 'لا يوجد'}
• الاسم: {message.from_user.first_name} {message.from_user.last_name or ''}

📍 **المكان:**
• النوع: خاص

💬 **الرسالة:**
{message.text or message.caption or '[وسائط]'}

🔄 **للرد:** أرسل رسالة تحتوي على:
`/reply_private {message.from_user.id} {message.id} رسالتك`
"""
    await app.send_message(OWNER_ID, user_info)

# --- MAIN HANDLER FOR OWNER (UNIFIED) ---
@app.on_message(filters.private & filters.user(OWNER_ID) & filters.text, group=3)
async def handle_owner_commands(client: Client, message: Message):
    profile_context.set(profile_store.get("active_profile_id", "profile_1"))
    text = message.text.strip()
    user_id_str = str(OWNER_ID)

    if text.startswith("/reply_private"):
        parts = text.split(maxsplit=2)
        if len(parts) >= 3:
            try:
                user_id = int(parts[1])
                reply_text = parts[2]
                await app.send_message(user_id, f"💬 **رد من الإدارة:**\n\n{reply_text}")
                await message.reply_text("✅ تم إرسال الرد")
            except Exception as e:
                await message.reply_text(f"❌ خطأ: {e}")
        return

    if text.startswith("/reply"):
        parts = text.split(maxsplit=4)
        if len(parts) >= 5:
            try:
                user_id = int(parts[1])
                chat_id = int(parts[2])
                message_id = int(parts[3])
                reply_text = parts[4]
                msg_info = get_message_context(chat_id, message_id)
                account_number = (msg_info or {}).get("from_account")
                if account_number:
                    account_index = account_number - 1
                    if account_index < len(db["accounts"]):
                        session_str = db["accounts"][account_index]
                        user_client = Client(
                            f"reply_client_{current_profile_id()}_{account_index}",
                            api_id=API_ID,
                            api_hash=API_HASH,
                            session_string=_normalize_session_string(session_str),
                            in_memory=True,
                        )
                        await _start_user_client(user_client, start_updates=False)
                        await user_client.send_message(chat_id, reply_text, reply_to_message_id=message_id)
                        await user_client.stop()
                        await message.reply_text(f"✅ تم إرسال الرد من الحساب {account_number}")
                    else:
                        await message.reply_text("❌ الحساب غير موجود")
                else:
                    await message.reply_text("❌ لم يتم العثور على الحساب المرسل لهذه الرسالة")
            except Exception as e:
                await message.reply_text(f"❌ خطأ: {e}")
        else:
            await message.reply_text("❌ الصيغة الصحيحة: /reply user_id chat_id message_id نص الرد")
        return

    if text.lower().startswith("/start"):
        return

    state = db["user_state"].get(user_id_str)
    navigation_pressed = (
        get_menu_action(text) is not None
        or normalize_button_text(text) in {
            normalize_button_text("📊 إحصائيات الكل"),
            normalize_button_text("➕ إضافة مجموعة"),
            normalize_button_text("🗑 حذف مجموعة"),
        }
        or get_profile_index_by_name(text) is not None
    )
    if state and navigation_pressed:
        qr_session = qr_login_sessions.get(OWNER_ID)
        if qr_session:
            qr_session["cancel_event"].set()
        pending_login = login_sessions.pop(OWNER_ID, None)
        if pending_login:
            try:
                await pending_login["client"].disconnect()
            except Exception:
                pass
        db["user_state"].pop(user_id_str, None)
        save_data(db)
        state = None

    if state:
        if state == "WAITING_PROFILE_NAME":
            profile_name = text.strip()
            reserved_names = {
                "➕ إضافة مجموعة",
                "🗑 حذف مجموعة",
                "⬅️ المجموعات"
            }
            if not profile_name or len(profile_name) > 40:
                return await message.reply_text("❌ أرسل اسمًا بين 1 و40 حرفًا.")
            if profile_name in reserved_names:
                return await message.reply_text("❌ هذا الاسم محجوز. اختر اسمًا آخر.")
            if get_profile_index_by_name(profile_name) is not None:
                return await message.reply_text("⚠️ توجد مجموعة بهذا الاسم بالفعل. أرسل اسمًا مختلفًا.")

            new_profile = profile_record(
                next_profile_id(),
                profile_name,
                empty_profile_data()
            )
            profile_store.setdefault("profiles", []).append(new_profile)
            db["user_state"].pop(user_id_str, None)
            save_data(db)
            return await message.reply_text(
                f"✅ تمت إضافة {profile_name}.\n"
                "المجموعة الجديدة فارغة وجاهزة لإضافة إعداداتها.",
                reply_markup=profile_menu_keyboard()
            )

        elif state == "WAITING_PHONE":
            phone = re.sub(r"[\s()-]", "", text.strip())
            if not re.fullmatch(r"\+\d{7,15}", phone):
                return await message.reply_text(
                    "❌ رقم الهاتف غير صحيح.\n"
                    "أرسله بصيغة دولية مثل:\n"
                    "+9647800000000"
                )
            existing_owner = await find_account_owner_by_phone(phone)
            if existing_owner:
                return await message.reply_text(
                    duplicate_account_warning(existing_owner, phone)
                )

            session_name = f"temp_session_{OWNER_ID}"
            old_login = login_sessions.pop(OWNER_ID, None)
            if old_login:
                try:
                    await old_login["client"].disconnect()
                except Exception:
                    pass

            temp_client = None
            try:
                temp_client = Client(
                    session_name,
                    api_id=API_ID,
                    api_hash=API_HASH,
                    in_memory=True,
                )
                await temp_client.connect()
                sent_code = await temp_client.send_code(phone)
                login_sessions[OWNER_ID] = {
                    "client": temp_client,
                    "phone": phone,
                    "hash": sent_code.phone_code_hash,
                    "session_name": session_name,
                }
                db["user_state"][user_id_str] = "WAITING_OTP"
                save_data(db)
                return await message.reply_text("📩 أرسل رمز التحقق:")
            except Exception as e:
                if temp_client:
                    try:
                        await temp_client.disconnect()
                    except Exception:
                        pass
                if os.path.exists(f"{session_name}.session"):
                    os.remove(f"{session_name}.session")
                login_sessions.pop(OWNER_ID, None)
                return await message.reply_text(f"❌ حدث خطأ أثناء إرسال الكود:\n`{e}`")
        elif state == "WAITING_OTP":
            otp = text.strip()
            session_info = login_sessions.get(OWNER_ID)
            if not session_info:
                db["user_state"].pop(user_id_str, None)
                save_data(db)
                return await message.reply_text("❌ انتهت الجلسة. أعد المحاولة.")
            temp_client = session_info["client"]
            session_name = session_info["session_name"]
            try:
                await temp_client.sign_in(session_info["phone"], session_info["hash"], otp)
                session_string = await temp_client.export_session_string()
                existing_owner = await find_account_owner_by_phone(session_info["phone"])
                if existing_owner:
                    await temp_client.disconnect()
                    if os.path.exists(f"{session_name}.session"):
                        os.remove(f"{session_name}.session")
                    del login_sessions[OWNER_ID]
                    db["user_state"].pop(user_id_str, None)
                    save_data(db)
                    return await message.reply_text(
                        duplicate_account_warning(
                            existing_owner,
                            session_info["phone"],
                        )
                    )
                new_account_index = len(db["accounts"])
                db["accounts"].append(session_string)
                await temp_client.disconnect()
                if os.path.exists(f"{session_name}.session"):
                    os.remove(f"{session_name}.session")
                del login_sessions[OWNER_ID]
                db["user_state"].pop(user_id_str, None)
                save_data(db)
                joined_count, total_groups = await join_account_to_configured_groups(
                    session_string, new_account_index
                )
                if profile_userbot_tasks.get(current_profile_id()):
                    await start_all_userbots()
                return await message.reply_text(
                    f"✅ تمت إضافة الحساب بنجاح!\n"
                    f"📢 انضم إلى {joined_count} من {total_groups} كروب مسجل."
                )
            except SessionPasswordNeeded:
                db["user_state"][user_id_str] = "WAITING_PASSWORD"
                save_data(db)
                return await message.reply_text("🔐 أرسل كلمة مرور التحقق بخطوتين:")
            except (PhoneCodeInvalid, PhoneCodeExpired):
                return await message.reply_text("❌ رمز التحقق غير صحيح. حاول مرة أخرى:")
            except Exception as e:
                await temp_client.disconnect()
                if os.path.exists(f"{session_name}.session"):
                    os.remove(f"{session_name}.session")
                del login_sessions[OWNER_ID]
                db["user_state"].pop(user_id_str, None)
                save_data(db)
                return await message.reply_text(f"❌ حدث خطأ: `{e}`")

        elif state == "WAITING_PASSWORD":
            password = text.strip()
            session_info = login_sessions.get(OWNER_ID)
            if not session_info:
                db["user_state"].pop(user_id_str, None)
                save_data(db)
                return await message.reply_text("❌ انتهت الجلسة. أعد المحاولة.")
            temp_client = session_info["client"]
            session_name = session_info["session_name"]
            try:
                await temp_client.check_password(password)
                session_string = await temp_client.export_session_string()
                existing_owner = await find_account_owner_by_phone(session_info["phone"])
                if existing_owner:
                    await temp_client.disconnect()
                    if os.path.exists(f"{session_name}.session"):
                        os.remove(f"{session_name}.session")
                    del login_sessions[OWNER_ID]
                    db["user_state"].pop(user_id_str, None)
                    save_data(db)
                    return await message.reply_text(
                        duplicate_account_warning(
                            existing_owner,
                            session_info["phone"],
                        )
                    )
                new_account_index = len(db["accounts"])
                db["accounts"].append(session_string)
                await temp_client.disconnect()
                if os.path.exists(f"{session_name}.session"):
                    os.remove(f"{session_name}.session")
                del login_sessions[OWNER_ID]
                db["user_state"].pop(user_id_str, None)
                save_data(db)
                joined_count, total_groups = await join_account_to_configured_groups(
                    session_string, new_account_index
                )
                if profile_userbot_tasks.get(current_profile_id()):
                    await start_all_userbots()
                return await message.reply_text(
                    f"✅ تمت إضافة الحساب بنجاح!\n"
                    f"📢 انضم إلى {joined_count} من {total_groups} كروب مسجل."
                )
            except Exception as e:
                return await message.reply_text(f"❌ كلمة المرور غير صحيحة: `{e}`")

        elif state == "WAITING_RECOVER":
            session_str = text.strip()
            result = await _recover_session_string(session_str, db, user_id_str)
            return await message.reply_text(result)

        elif state == "WAITING_QR":
            return await message.reply_text(
                "📷 ما زال تسجيل الدخول عبر QR قيد الانتظار.\n"
                "امسح الرمز المرسل لك، أو اضغط «إلغاء» لإيقاف العملية."
            )

        elif state == "WAITING_QR_PASSWORD":
            qr_session = qr_login_sessions.get(OWNER_ID)
            password_future = (qr_session or {}).get("password_future")
            if not password_future or password_future.done():
                return await message.reply_text(
                    "❌ انتهت جلسة طلب كلمة المرور. أعد إصدار رمز QR جديدًا."
                )
            password = text.strip()
            if not password:
                return await message.reply_text("❌ أرسل كلمة المرور كما هي.")
            password_future.set_result(password)
            try:
                await message.delete()
            except Exception:
                pass
            return await app.send_message(OWNER_ID, "⏳ جارٍ التحقق من كلمة المرور...")

        elif state == "WAITING_TEMPLATE":
            lines = text.strip().split('\n')
            added_count = 0
            for line in lines:
                if line.strip():
                    db["templates"].append(line.strip())
                    added_count += 1
            db["user_state"].pop(user_id_str, None)
            save_data(db)
            return await message.reply_text(f"✅ تمت إضافة {added_count} كليشة!")

        elif state == "WAITING_GROUP":
            lines = text.strip().split('\n')
            added_count = 0
            new_groups = []
            for line in lines:
                if line.strip():
                    group = clean_group_link(line.strip())
                    if group not in db["groups"]:
                        db["groups"].append(group)
                        db.setdefault("group_activity", {}).setdefault(group, 0)
                        for blocked_groups in db.setdefault("account_blocked_groups", {}).values():
                            if isinstance(blocked_groups, dict):
                                blocked_groups.pop(group, None)
                            elif group in blocked_groups:
                                blocked_groups.remove(group)
                        new_groups.append(group)
                        added_count += 1
            db["user_state"].pop(user_id_str, None)
            save_data(db)
            if new_groups and profile_userbot_tasks.get(current_profile_id()):
                await start_all_userbots()
            return await message.reply_text(
                f"✅ تمت إضافة {added_count} كروب.\n"
                "سيتم فحص عضوية الحساب عند أول إرسال باستخدام اتصال واحد فقط."
            )

        elif state == "WAITING_TIMER":
            if text.isdigit() and MIN_SEND_INTERVAL <= int(text) <= 86400:
                db["timer"] = int(text)
                db["user_state"].pop(user_id_str, None)
                save_data(db)
                return await message.reply_text(f"✅ تم ضبط المؤقت على {text} ثانية")
            else:
                return await message.reply_text(
                    f"❌ أرسل رقمًا صحيحًا بين {MIN_SEND_INTERVAL} و86400 ثانية"
                )

    if text == "⬅️ المجموعات":
        db["user_state"].pop(user_id_str, None)
        save_data(db)
        return await show_profile_menu(message)

    if text == "📊 إحصائيات الكل":
        db["user_state"].pop(user_id_str, None)
        save_data(db)
        return await message.reply_text(all_profiles_stats_text())

    profile_index = get_profile_index_by_name(text)
    if profile_index is not None:
        selected_profile = profile_store["profiles"][profile_index]
        if selected_profile["id"] == profile_store.get("active_profile_id"):
            return await message.reply_text(
                f"📂 أنت داخل {selected_profile['name']} بالفعل.",
                reply_markup=BOT_KEYBOARD
            )
        db["user_state"].pop(user_id_str, None)
        await activate_profile(profile_index)
        return await message.reply_text(
            f"📂 تم فتح {selected_profile['name']}.\n\n"
            f"الحسابات: {len(db['accounts'])}\n"
            f"الكليشات: {len(db['templates'])}\n"
            f"الكروبات: {len(db['groups'])}\n"
            f"المؤقت: {db.get('timer', 60)} ثانية",
            reply_markup=BOT_KEYBOARD
        )

    if text == "➕ إضافة مجموعة":
        db["user_state"][user_id_str] = "WAITING_PROFILE_NAME"
        save_data(db)
        return await message.reply_text(
            "➕ أرسل اسم المجموعة الجديدة.\n"
            "سيتم إنشاء نسخة مستقلة من البوت بدون حسابات أو كليشات أو كروبات."
        )

    if text == "🗑 حذف مجموعة":
        profiles = profile_store.get("profiles", [])
        if len(profiles) <= 1:
            return await message.reply_text("⚠️ لا يمكن حذف المجموعة الوحيدة.")
        keyboard = create_selection_list(
            [profile.get("name", "مجموعة") for profile in profiles],
            "profile",
            "delete_profile"
        )
        return await message.reply_text("🗑 اختر المجموعة التي تريد حذفها:", reply_markup=keyboard)

    action = get_menu_action(text)
    if action:
        db["user_state"].pop(user_id_str, None)

        if action == "profiles":
            return await show_profile_menu(message)

        if action == "accounts":
            if not db["accounts"]:
                return await message.reply_text("❌ لا توجد حسابات مضافة.")
            msg = "📋 الحسابات المضافة:\n\n"
            for i, session_str in enumerate(db["accounts"]):
                info = await get_account_info(session_str, i)
                status = "✅" if info['connected'] else "❌"
                msg += f"{i+1}. {status} 📱 {info['phone']} - 👤 {info['name']}\n"
            await message.reply_text(msg)

        elif action == "groups":
            if not db["groups"]:
                return await message.reply_text("❌ لا توجد كروبات مضافة.")
            msg = "📋 الكروبات المضافة:\n\n"
            for i, g in enumerate(db["groups"], 1):
                msg += f"{i}. {g}\n"
            await message.reply_text(msg)

        elif action == "add_account":
            db["user_state"][user_id_str] = "WAITING_PHONE"
            save_data(db)
            await message.reply_text("📱 أرسل رقم الهاتف مع مفتاح الدولة:\nمثال: +9647800000000")

        elif action == "add_account_qr":
            if qr_login_sessions.get(OWNER_ID):
                return await message.reply_text(
                    "⚠️ توجد عملية QR قيد التشغيل. امسح الرمز الحالي أو ألغِها أولًا."
                )
            db["user_state"][user_id_str] = "WAITING_QR"
            save_data(db)
            await start_qr_login()

        elif action == "recover_account":
            db["user_state"][user_id_str] = "WAITING_RECOVER"
            save_data(db)
            await message.reply_text("🔄 أرسل جلسة الاسترداد (Session String):")

        elif action == "delete_account":
            if not db["accounts"]:
                return await message.reply_text("❌ لا توجد حسابات لحذفها.")
            if db["is_running"]:
                return await message.reply_text("⚠️ أوقف البوت أولًا.")
            account_labels = []
            for index, session_str in enumerate(db["accounts"]):
                info = await get_account_info(session_str, index)
                account_labels.append(f"{index+1}. {'✅' if info['connected'] else '❌'} 📱 {info['phone']}")
            keyboard = create_selection_list(
                account_labels,
                "account",
                "delete_account",
                current_profile_id(),
            )
            await message.reply_text("🗑 اختر الحساب لحذفه نهائياً:", reply_markup=keyboard)

        elif action == "add_text":
            db["user_state"][user_id_str] = "WAITING_TEMPLATE"
            save_data(db)
            await message.reply_text("📝 أرسل الكليشة الجديدة (يمكنك إرسال عدة كليشات، كل كليشة في سطر منفصل):")

        elif action == "delete_text":
            if not db["templates"]:
                return await message.reply_text("❌ لا توجد كليشات لحذفها.")
            keyboard = create_selection_list(db["templates"], "template", "delete_template")
            await message.reply_text("🗑 اختر الكليشة لحذفها:", reply_markup=keyboard)

        elif action == "add_group":
            db["user_state"][user_id_str] = "WAITING_GROUP"
            save_data(db)
            await message.reply_text("📢 أرسل الكروبات (كل كروب في سطر منفصل):\nمثال:\n@group1\n@group2\nhttps://t.me/+xxxxx")

        elif action == "delete_group":
            if not db["groups"]:
                return await message.reply_text("❌ لا توجد كروبات لحذفها.")
            keyboard = create_selection_list(db["groups"], "group", "delete_group")
            await message.reply_text("🗑 اختر الكروب لحذفه:", reply_markup=keyboard)

        elif action == "start":
            profile_id = current_profile_id()
            posting_task = profile_posting_tasks.get(profile_id)
            if db["is_running"]:
                if posting_task is not None and not posting_task.done():
                    return await message.reply_text("⚠️ البوت يعمل حاليًا.")
                db["is_running"] = False
                save_data()
            if not db["accounts"] or not db["templates"] or not db["groups"]:
                return await message.reply_text("❌ يجب إضافة حساب وكليشة وكروب أولًا.")

            db["is_running"] = True
            save_data()
            timer_value = db.get('timer', 60)
            startup_task = asyncio.create_task(start_profile_services(profile_id))
            profile_posting_tasks[profile_id] = startup_task
            await message.reply_text(
                f"🚀 تم بدء تشغيل البوت!\n"
                f"⏱ المؤقت: {timer_value} ثانية\n"
                f"📊 الحسابات: {len(db['accounts'])}\n"
                f"📢 الكروبات: {len(db['groups'])}\n"
                f"📝 الكليشات: {len(db['templates'])}\n"
                "🤝 جارٍ فحص انضمام الحسابات في الخلفية...\n"
                f"🔄 طابور حسابات متكرر بالترتيب\n"
                "🎯 إرسال بالتناوب إلى جميع الكروبات المسجلة دون شروط نشاط\n"
                f"📡 مراقبة الحظر والتجميد مفعلة\n"
                f"👥 نظام الردود الآلي مفعل"
            )

        elif action == "stop":
            profile_id = current_profile_id()
            posting_task = profile_posting_tasks.get(profile_id)
            if not db["is_running"]:
                return await message.reply_text("⚠️ البوت متوقف حاليًا.")
            db["is_running"] = False
            save_data()
            if posting_task and not posting_task.done():
                posting_task.cancel()
                try:
                    await posting_task
                except asyncio.CancelledError:
                    pass
            profile_posting_tasks[profile_id] = None
            await stop_all_userbots(profile_id)
            await message.reply_text("🛑 تم إيقاف البوت لهذه المجموعة.")

        elif action == "timer":
            db["user_state"][user_id_str] = "WAITING_TIMER"
            save_data(db)
            await message.reply_text(
                f"⏱ المؤقت الحالي: {max(MIN_SEND_INTERVAL, int(db.get('timer', 60) or 60))} ثانية\n"
                f"أرسل القيمة الجديدة (بالثواني، حد أدنى {MIN_SEND_INTERVAL}):"
            )

        elif action == "stats":
            status = "🟢 يعمل" if db["is_running"] else "🔴 متوقف"
            await message.reply_text(
                f"📊 الإحصائيات:\n\n"
                f"الحالة: {status}\n"
                f"الحسابات: {len(db['accounts'])}\n"
                f"الكليشات: {len(db['templates'])}\n"
                f"الكروبات: {len(db['groups'])}\n"
                f"✅ تم الإرسال: {db['stats']['sent_count']}\n"
                f"❌ فشل الإرسال: {db['stats']['failed_count']}\n"
                f"📡 قنوات إجبارية: {len(db.get('joined_channels', {}))}\n"
                f"👥 ردود واردة: {len(db.get('outgoing_messages', {}))}"
            )

        elif action == "failed_messages":
            await message.reply_text(failed_messages_text())

        elif action == "clear":
            db["accounts"] = []
            db["templates"] = []
            db["groups"] = []
            db["group_activity"] = {}
            db["stats"] = {"sent_count": 0, "failed_count": 0}
            db["failed_messages"] = []
            db["is_running"] = False
            db["joined_channels"] = {}
            db["channel_join_time"] = {}
            db["account_errors"] = {}
            db["last_group_index"] = {}
            db["last_sent_group_index"] = -1
            db["template_index"] = 0
            db["incoming_messages"] = {}
            db["account_blocked_groups"] = {}
            db["account_group_posts"] = {}
            db["account_group_incoming"] = {}
            db["account_group_last_sent"] = {}
            db["group_unread_counts"] = {}
            save_data(db)
            get_account_cache().clear()
            await message.reply_text("🗑 تم حذف جميع الحسابات والكليشات والكروبات والقنوات الإجبارية.")

        elif action == "incoming_replies":
            keyboard = build_incoming_replies_keyboard()
            if not keyboard:
                return await message.reply_text("❌ لا توجد ردود واردة على رسائل حساباتك.")
            await message.reply_text(
                "👥 اختر الرد الذي تريد عرضه ومعرفة الحساب الذي أرسل الرسالة:",
                reply_markup=keyboard
            )

        elif action == "reply_status":
            status = "🟢 يعمل" if db["is_running"] else "🔴 متوقف"
            await message.reply_text(
                f"🔄 حالة نظام الردود:\n\n"
                f"الحالة: {status}\n"
                f"الردود المستلمة: {len(db.get('outgoing_messages', {}))}\n"
                f"الانضمام التلقائي: {'مفعل' if db.get('auto_join_groups', True) else 'معطل'}\n"
                f"آخر تحديث: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
            )

        elif action == "reply_settings":
            current = db.get("auto_join_groups", True)
            await message.reply_text(
                f"⚙️ إعدادات الردود:\n\n"
                f"الانضمام التلقائي للكروبات: {'✅ مفعل' if current else '❌ معطل'}\n\n"
                f"لتبديل الحالة أرسل: /toggle_auto_join"
            )

        return

    await message.reply_text("لم أفهم الأمر. أرسل /start ثم اختر أحد أزرار القائمة.")

def build_incoming_replies_keyboard():
    keyboard = []
    for chat_id, messages in db.get("incoming_messages", {}).items():
        for msg_id, msg_info in messages.items():
            if not msg_info.get("is_reply", False):
                continue
            sender = msg_info.get("from_username") or msg_info.get("from_name") or "مستخدم"
            account = msg_info.get("from_account") or "؟"
            label = f"📩 {sender[:18]} | الحساب {account} | {str(chat_id)[-8:]}"
            callback_data = f"incoming_{chat_id}_{msg_id}"
            if len(callback_data.encode("utf-8")) <= 64:
                keyboard.append([InlineKeyboardButton(label[:60], callback_data=callback_data)])
    if keyboard:
        keyboard.append([InlineKeyboardButton("🔄 تحديث القائمة", callback_data="incoming_list")])
    return InlineKeyboardMarkup(keyboard) if keyboard else None

# --- Selection Helper ---
def create_selection_list(items, item_type, action, context_id=None):
    keyboard = []
    for i, item in enumerate(items):
        display_text = f"{i+1}. {item[:30]}..." if len(item) > 30 else f"{i+1}. {item}"
        callback_data = f"{action}_{i}"
        if context_id:
            callback_data = f"{callback_data}_{context_id}"
        keyboard.append([InlineKeyboardButton(display_text, callback_data=callback_data)])
    keyboard.append([InlineKeyboardButton("❌ إلغاء", callback_data="cancel")])
    return InlineKeyboardMarkup(keyboard)

def remove_indexed_account_state(state, removed_index, one_based=True):
    if not isinstance(state, dict):
        return {}

    removed_key = removed_index + (1 if one_based else 0)
    updated = {}
    for raw_key, value in state.items():
        try:
            key_number = int(raw_key)
        except (TypeError, ValueError):
            updated[raw_key] = value
            continue

        if key_number == removed_key:
            continue
        if key_number > removed_key:
            updated[str(key_number - 1)] = value
        else:
            updated[str(key_number)] = value
    return updated

def _qr_login_url(token):
    encoded_token = base64.urlsafe_b64encode(token).decode("ascii").rstrip("=")
    return f"tg://login?token={encoded_token}"

def _make_qr_image(qr_url):
    import qrcode

    qr = qrcode.QRCode(
        version=None,
        error_correction=qrcode.constants.ERROR_CORRECT_M,
        box_size=10,
        border=4,
    )
    qr.add_data(qr_url)
    qr.make(fit=True)
    image = qr.make_image(fill_color="black", back_color="white")
    photo = io.BytesIO()
    photo.name = "telegram-login-qr.png"
    image.save(photo, format="PNG")
    photo.seek(0)
    return photo

async def _stop_qr_client(client, handler_ref=None):
    if client is None:
        return
    if handler_ref:
        try:
            client.remove_handler(*handler_ref)
        except Exception:
            pass
    try:
        if client.is_initialized:
            await client.terminate()
    except Exception:
        pass
    try:
        if client.is_connected:
            await client.disconnect()
    except Exception:
        pass

async def _export_qr_login_token(client):
    return await client.invoke(
        raw.functions.auth.ExportLoginToken(
            api_id=API_ID,
            api_hash=API_HASH,
            except_ids=[],
        )
    )

async def _import_migrated_qr_token(client, token_result):
    # auth.exportLoginToken may ask us to continue on another DC.  The
    # previous implementation used get_dc_option/get_session, which are not
    # Pyrogram Client APIs and left the replacement session unstarted.  Build
    # and start a real Pyrogram Session instead, then persist its DC/auth key
    # so the exported session string belongs to the migrated session.
    dc_id = token_result.dc_id
    test_mode = await client.storage.test_mode()
    auth_key = await Auth(client, dc_id, test_mode).create()

    if client.session is not None:
        await client.session.stop()

    client.session = Session(client, dc_id, auth_key, test_mode)
    await client.session.start()
    await client.storage.dc_id(dc_id)
    await client.storage.auth_key(auth_key)
    return await client.invoke(
        raw.functions.auth.ImportLoginToken(token=token_result.token)
    )

async def _request_qr_password(session_info, cancel_event):
    """انتظار كلمة مرور 2FA دون حفظها في ملف البيانات."""
    password_future = asyncio.get_running_loop().create_future()
    session_info["password_future"] = password_future
    db["user_state"][str(OWNER_ID)] = "WAITING_QR_PASSWORD"
    save_data(db)

    try:
        try:
            hint = await session_info["client"].get_password_hint()
        except Exception:
            hint = ""

        hint_text = f"\n💡 التلميح: {hint}" if hint else ""
        await app.send_message(
            OWNER_ID,
            "🔐 الحساب محمي بالتحقق بخطوتين.\n"
            f"أرسل كلمة مرور Telegram لإكمال تسجيل الدخول عبر QR.{hint_text}\n"
            "⚠️ لا يتم حفظ كلمة المرور في البيانات.",
        )

        cancel_task = asyncio.create_task(cancel_event.wait())
        done, pending = await asyncio.wait(
            {password_future, cancel_task},
            timeout=180,
            return_when=asyncio.FIRST_COMPLETED,
        )
        for task in pending:
            task.cancel()
        await asyncio.gather(*pending, return_exceptions=True)

        if cancel_task in done:
            raise asyncio.CancelledError
        if password_future not in done:
            raise TimeoutError("انتهت مهلة انتظار كلمة مرور التحقق بخطوتين.")
        return str(password_future.result() or "").strip()
    finally:
        if session_info.get("password_future") is password_future:
            session_info.pop("password_future", None)

async def _qr_login_worker():
    client = None
    handler_ref = None
    qr_message = None
    session_info = qr_login_sessions.get(OWNER_ID)
    if not session_info:
        return

    scan_event = asyncio.Event()
    cancel_event = session_info["cancel_event"]

    async def on_raw_update(_, update, __, ___):
        if isinstance(update, raw.types.UpdateLoginToken):
            scan_event.set()

    try:
        try:
            import qrcode  # noqa: F401
        except ImportError as error:
            raise RuntimeError(
                "ميزة QR تحتاج الحزمة qrcode[pil]. أعد نشر التطبيق بعد تحديث requirements.txt."
            ) from error

        client = Client(
            f"qr_login_{current_profile_id()}_{OWNER_ID}",
            api_id=API_ID,
            api_hash=API_HASH,
            in_memory=True,
        )
        await client.connect()
        handler_ref = client.add_handler(
            handlers.RawUpdateHandler(on_raw_update)
        )
        await client.initialize()

        expires_at = asyncio.get_running_loop().time() + 180
        while asyncio.get_running_loop().time() < expires_at:
            token_result = await _export_qr_login_token(client)
            if isinstance(token_result, raw.types.auth.LoginTokenMigrateTo):
                token_result = await _import_migrated_qr_token(client, token_result)

            if not isinstance(token_result, raw.types.auth.LoginToken):
                raise RuntimeError(
                    f"Telegram أعاد استجابة QR غير متوقعة: {type(token_result).__name__}"
                )

            qr_url = _qr_login_url(token_result.token)
            photo = _make_qr_image(qr_url)
            if qr_message:
                try:
                    await qr_message.delete()
                except Exception:
                    pass
            qr_message = await app.send_photo(
                OWNER_ID,
                photo=photo,
                caption=(
                    "📷 امسح هذا الرمز من Telegram:\n\n"
                    "الإعدادات ← الأجهزة ← ربط جهاز سطح المكتب\n\n"
                    "⏳ الرمز يتجدد تلقائيًا عند انتهاء صلاحيته."
                ),
                reply_markup=InlineKeyboardMarkup(
                    [[InlineKeyboardButton("❌ إلغاء", callback_data="cancel_qr_login")]]
                ),
            )

            scan_event.clear()
            remaining = max(
                1,
                min(
                    int(getattr(token_result, "expires", 0))
                    - int(datetime.now().timestamp()),
                    30,
                ),
            )
            scan_wait = asyncio.create_task(scan_event.wait())
            cancel_wait = asyncio.create_task(cancel_event.wait())
            done, pending = await asyncio.wait(
                {scan_wait, cancel_wait},
                timeout=remaining,
                return_when=asyncio.FIRST_COMPLETED,
            )
            for task in pending:
                task.cancel()
            await asyncio.gather(*pending, return_exceptions=True)

            if cancel_wait in done:
                await app.send_message(OWNER_ID, "❌ تم إلغاء تسجيل الدخول عبر QR.")
                return
            if scan_wait not in done:
                continue

            raw_user = None
            try:
                result = await _export_qr_login_token(client)
                if isinstance(result, raw.types.auth.LoginTokenMigrateTo):
                    result = await _import_migrated_qr_token(client, result)
                if isinstance(result, raw.types.auth.LoginTokenSuccess):
                    raw_user = getattr(result.authorization, "user", None)
            except SessionPasswordNeeded:
                for attempt in range(3):
                    password = await _request_qr_password(
                        session_info,
                        cancel_event,
                    )
                    try:
                        raw_user = await client.check_password(password)
                        break
                    except Exception as password_error:
                        if attempt == 2:
                            raise RuntimeError(
                                "كلمة مرور التحقق بخطوتين غير صحيحة بعد 3 محاولات."
                            ) from password_error
                        await app.send_message(
                            OWNER_ID,
                            "❌ كلمة المرور غير صحيحة. أرسلها مرة أخرى:",
                        )

            if raw_user is None or not getattr(raw_user, "id", None):
                raise RuntimeError("تم مسح الرمز لكن Telegram لم يعِد بيانات الحساب.")

            await client.storage.user_id(raw_user.id)
            await client.storage.is_bot(False)
            me = await client.get_me()
            session_string = await client.export_session_string()

            existing_owner = find_account_owner_by_session(session_string)
            if not existing_owner and me.phone_number:
                existing_owner = await find_account_owner_by_phone(me.phone_number)
            if existing_owner:
                await app.send_message(
                    OWNER_ID,
                    duplicate_account_warning(
                        existing_owner,
                        me.phone_number or "غير معروف",
                    ),
                )
                return

            new_account_index = len(db["accounts"])
            db["accounts"].append(session_string)
            db["user_state"].pop(str(OWNER_ID), None)
            save_data(db)
            get_account_cache().clear()
            joined_count, total_groups = await join_account_to_configured_groups(
                session_string,
                new_account_index,
            )
            await app.send_message(
                OWNER_ID,
                "✅ تمت إضافة الحساب عبر QR بنجاح!\n"
                f"📱 الرقم: {me.phone_number or 'غير معروف'}\n"
                f"👤 الاسم: {me.first_name or 'غير معروف'}\n"
                f"📢 انضم إلى {joined_count} من {total_groups} كروب مسجل.",
            )
            return

        await app.send_message(
            OWNER_ID,
            "⌛ انتهت مهلة QR. اضغط «📷 إضافة حساب QR» لإصدار رمز جديد.",
        )
    except asyncio.CancelledError:
        raise
    except Exception as error:
        db["user_state"].pop(str(OWNER_ID), None)
        save_data(db)
        print(f"❌ QR login failed: {error}")
        try:
            await app.send_message(
                OWNER_ID,
                f"❌ فشل تسجيل الدخول عبر QR:\n{str(error)[:500]}",
            )
        except Exception:
            pass
    finally:
        if qr_message:
            try:
                await qr_message.delete()
            except Exception:
                pass
        await _stop_qr_client(client, handler_ref)
        qr_login_sessions.pop(OWNER_ID, None)
        if db.get("user_state", {}).get(str(OWNER_ID)) == "WAITING_QR":
            db["user_state"].pop(str(OWNER_ID), None)
            save_data(db)

async def start_qr_login():
    if qr_login_sessions.get(OWNER_ID):
        return
    cancel_event = asyncio.Event()
    task = asyncio.create_task(_qr_login_worker())
    qr_login_sessions[OWNER_ID] = {
        "task": task,
        "cancel_event": cancel_event,
    }

def _normalize_session_string(session_str):
    """تحويل Telethon StringSession إلى تنسيق Pyrogram عند استيراد جلسات Strat."""
    raw = str(session_str or "").strip()
    if not raw or not raw.startswith("1"):
        return raw

    try:
        encoded = raw[1:]
        payload = base64.urlsafe_b64decode(encoded + "=" * (-len(encoded) % 4))
        if len(payload) == 263:
            dc_id, _server_address, _port, auth_key = struct.unpack(">B4sH256s", payload)
        elif len(payload) == 275:
            dc_id, _server_address, _port, auth_key = struct.unpack(">B16sH256s", payload)
        else:
            return raw

        pyrogram_payload = struct.pack(
            ">BI?256sQ?",
            dc_id,
            API_ID,
            False,
            auth_key,
            0,
            False,
        )
        return base64.urlsafe_b64encode(pyrogram_payload).decode("ascii").rstrip("=")
    except Exception:
        return raw

async def _start_user_client(client, *, start_updates=True):
    try:
        is_authorized = await client.connect()
        if not is_authorized:
            try:
                me = await client.get_me()
            except Exception as error:
                raise RuntimeError(
                    "Session is not authorized or has expired; re-import the session"
                ) from error
            await client.storage.user_id(me.id)
            await client.storage.is_bot(bool(me.is_bot))

        await client.invoke(raw.functions.updates.GetState())
        client.me = await client.get_me()
        if start_updates:
            await client.initialize()
        return client.me
    except Exception:
        if client.is_connected:
            try:
                if client.is_initialized:
                    await client.terminate()
                await client.disconnect()
            except Exception:
                pass
        raise

async def _recover_session_string(session_str, db, user_id_str):
    session_str = _normalize_session_string(session_str)
    if not session_str:
        return "❌ ملف الجلسة لا يحتوي Session String صالحاً."
    try:
        temp_client = Client(
            f"recover_session_{current_profile_id()}_{OWNER_ID}",
            api_id=API_ID,
            api_hash=API_HASH,
            session_string=_normalize_session_string(session_str),
            in_memory=True,
        )
        await temp_client.connect()
        me = await temp_client.get_me()
        await temp_client.storage.user_id(me.id)
        await temp_client.storage.is_bot(bool(me.is_bot))
        session_str = await temp_client.export_session_string()
        await temp_client.disconnect()
        existing_owner = find_account_owner_by_session(session_str)
        if not existing_owner and me.phone_number:
            existing_owner = await find_account_owner_by_phone(me.phone_number)
        if existing_owner:
            return duplicate_account_warning(existing_owner, me.phone_number or "غير معروف")
        new_account_index = len(db["accounts"])
        db["accounts"].append(session_str)
        db["user_state"].pop(user_id_str, None)
        save_data(db)
        get_account_cache().clear()
        joined_count, total_groups = await join_account_to_configured_groups(
            session_str, new_account_index
        )
        return (
            f"✅ تم استرداد الحساب!\n"
            f"الرقم: {me.phone_number}\n"
            f"الاسم: {me.first_name}\n"
            f"📢 انضم إلى {joined_count} من {total_groups} كروب مسجل."
        )
    except Exception as e:
        return f"❌ فشل الاسترداد: {e}"

def _session_strings_from_payload(payload):
    result = []

    session_keys = {
        "session",
        "session_string",
        "sessionstring",
        "string_session",
        "stringsession",
    }

    def add(value):
        value = str(value or "").strip()
        if value and value not in result:
            result.append(value)

    def visit(value, key_hint=None):
        if isinstance(value, dict):
            for key, nested in value.items():
                normalized_key = re.sub(r"[^a-z0-9]", "", str(key).casefold())
                if normalized_key in session_keys and isinstance(nested, str):
                    add(nested)
                else:
                    visit(nested, normalized_key)
        elif isinstance(value, list):
            for item in value:
                visit(item, key_hint)
        elif isinstance(value, str) and key_hint in session_keys:
            add(value)

    visit(payload)
    return result

def _session_strings_from_text(text):
    result = []
    for raw_line in str(text or "").splitlines():
        line = raw_line.strip()
        if not line:
            continue
        match = re.search(
            r"(?:session(?:_string)?|string_session)\s*[:=]\s*[\"']?([A-Za-z0-9_=-]{80,})",
            line,
            flags=re.IGNORECASE,
        )
        candidate = match.group(1) if match else line
        if len(candidate) < 80 or not re.fullmatch(r"[A-Za-z0-9_=-]+", candidate):
            continue
        if candidate not in result:
            result.append(candidate)
    return result

def _session_strings_from_archive(raw_bytes, max_depth=2):
    import io
    import zipfile

    result = []

    def add_many(values):
        for value in values:
            if value and value not in result:
                result.append(value)

    def read_archive(blob, depth):
        if depth > max_depth or not zipfile.is_zipfile(io.BytesIO(blob)):
            return
        with zipfile.ZipFile(io.BytesIO(blob)) as archive:
            for entry in archive.infolist():
                if entry.is_dir() or entry.file_size > 2 * 1024 * 1024:
                    continue
                try:
                    content = archive.read(entry)
                except (OSError, RuntimeError, ValueError, zipfile.BadZipFile):
                    continue

                name = entry.filename.rsplit("/", 1)[-1].casefold()
                if name.endswith(".zip"):
                    read_archive(content, depth + 1)
                elif name.endswith((".json", ".jsonl")):
                    try:
                        if name.endswith(".jsonl"):
                            for line in content.decode("utf-8-sig").splitlines():
                                if line.strip():
                                    add_many(
                                        _session_strings_from_payload(
                                            json.loads(line)
                                        )
                                    )
                        else:
                            add_many(
                                _session_strings_from_payload(
                                    json.loads(content.decode("utf-8-sig"))
                                )
                            )
                    except (UnicodeDecodeError, json.JSONDecodeError):
                        add_many(_session_strings_from_text(content.decode("utf-8", errors="ignore")))
                elif name.endswith((".txt", ".csv", ".log")):
                    add_many(_session_strings_from_text(content.decode("utf-8", errors="ignore")))

    read_archive(raw_bytes, 0)
    return result

@app.on_message(filters.private & filters.user(OWNER_ID) & filters.document, group=3)
async def handle_owner_session_document(client: Client, message: Message):
    profile_context.set(profile_store.get("active_profile_id", "profile_1"))
    user_id_str = str(OWNER_ID)
    if db.get("user_state", {}).get(user_id_str) != "WAITING_RECOVER":
        return
    filename = (message.document.file_name or "").lower()
    try:
        import io
        import zipfile
        downloaded = await client.download_media(message, in_memory=True)
        raw_bytes = downloaded.getvalue() if hasattr(downloaded, "getvalue") else bytes(downloaded)
        is_archive = (
            filename.endswith((".zip", ".cbz"))
            or (message.document.mime_type or "").casefold() in {
                "application/zip",
                "application/x-zip-compressed",
            }
            or raw_bytes[:4] == b"PK\x03\x04"
        )
        if is_archive and zipfile.is_zipfile(io.BytesIO(raw_bytes)):
            sessions = _session_strings_from_archive(raw_bytes)
        elif filename.endswith((".json", ".jsonl")):
            try:
                if filename.endswith(".jsonl"):
                    sessions = []
                    for line in raw_bytes.decode("utf-8-sig").splitlines():
                        if line.strip():
                            sessions.extend(
                                _session_strings_from_payload(json.loads(line))
                            )
                else:
                    sessions = _session_strings_from_payload(
                        json.loads(raw_bytes.decode("utf-8-sig"))
                    )
            except (UnicodeDecodeError, json.JSONDecodeError):
                sessions = _session_strings_from_text(
                    raw_bytes.decode("utf-8", errors="ignore")
                )
        else:
            sessions = _session_strings_from_text(
                raw_bytes.decode("utf-8", errors="ignore")
            )
        sessions = list(dict.fromkeys(sessions))
        if not sessions:
            return await message.reply_text(
                "❌ لم أجد Session String داخل الملف. أرسل JSON أو ZIP يحتوي "
                "session_string، أو أرسل الجلسة كنص."
            )
        results = []
        for session_str in sessions[:50]:
            results.append(await _recover_session_string(session_str, db, user_id_str))
        summary = "\n\n".join(results)
        if len(sessions) > len(results):
            summary += f"\n\n⚠️ تم تجاهل {len(sessions) - len(results)} جلسة لتفادي معالجة دفعة كبيرة."
        return await message.reply_text(summary)
    except Exception as e:
        return await message.reply_text(f"❌ تعذر قراءة ملف الجلسة: {e}")

# --- Handle Callback Query ---
@app.on_callback_query()
async def handle_callback(client: Client, callback_query):
    global db
    if callback_query.from_user.id != OWNER_ID:
        return await callback_query.answer("غير مصرح")
    data = callback_query.data
    await callback_query.answer()
    if data == "cancel":
        await callback_query.message.delete()
        return
    if data == "cancel_qr_login":
        session_info = qr_login_sessions.get(OWNER_ID)
        if session_info:
            session_info["cancel_event"].set()
        await callback_query.message.delete()
        await callback_query.answer("تم إلغاء تسجيل الدخول")
        return
    if data == "incoming_list":
        keyboard = build_incoming_replies_keyboard()
        if not keyboard:
            return await callback_query.message.reply_text("❌ لا توجد ردود واردة على رسائل حساباتك.")
        return await callback_query.message.reply_text(
            "👥 اختر الرد الذي تريد عرضه:",
            reply_markup=keyboard
        )
    if data.startswith("incoming_"):
        try:
            _, chat_id_raw, message_id_raw = data.split("_", 2)
            chat_id = int(chat_id_raw)
            message_id = int(message_id_raw)
            msg_info = get_message_context(chat_id, message_id)
            if not msg_info:
                return await callback_query.message.reply_text("❌ انتهت بيانات هذه الرسالة أو لم تعد موجودة.")

            account_number = msg_info.get("from_account")
            account_label = f"الحساب رقم {account_number}" if account_number else "غير محدد"
            if account_number and 0 < int(account_number) <= len(db.get("accounts", [])):
                account_info = await get_account_info(db["accounts"][int(account_number) - 1], int(account_number) - 1)
                account_label += f"\n📱 الرقم: {account_info.get('phone', 'غير معروف')}\n👤 الاسم: {account_info.get('name', 'غير معروف')}"

            sender_name = msg_info.get("from_name") or "غير معروف"
            sender_username = msg_info.get("from_username") or "لا يوجد"
            reply_text = msg_info.get("text") or "[وسائط أو رسالة بدون نص]"
            details = f"""
📩 **تفاصيل الرد**

👤 المرسل: {sender_name}
🔹 اليوزر: @{sender_username}
📍 الكروب: {msg_info.get('chat_title', 'بدون اسم')}
🆔 أيدي الكروب: {chat_id}

💬 **نص الرد:**
{reply_text}

📱 **الحساب الذي أرسل الرسالة الأصلية:**
{account_label}

🔄 **للرد من نفس الحساب أرسل:**
/reply {msg_info.get('from_user_id', '')} {chat_id} {message_id} نص الرد
"""
            await callback_query.message.reply_text(
                details,
                reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ الرجوع للردود", callback_data="incoming_list")]])
            )
        except Exception as e:
            await callback_query.message.reply_text(f"❌ تعذر عرض الرد: {e}")
        return
    if data.startswith("delete_profile_"):
        try:
            index = int(data.split("_")[2])
        except (IndexError, ValueError):
            return await callback_query.message.reply_text("❌ المجموعة غير موجودة.")

        profiles = profile_store.get("profiles", [])
        if len(profiles) <= 1:
            return await callback_query.message.reply_text("⚠️ لا يمكن حذف المجموعة الوحيدة.")
        if not 0 <= index < len(profiles):
            return await callback_query.message.reply_text("❌ المجموعة غير موجودة.")
        if db.get("is_running"):
            return await callback_query.message.reply_text(
                "⚠️ أوقف البوت أولًا قبل حذف مجموعة."
            )

        deleted = profiles.pop(index)
        deleted_name = deleted.get("name", "المجموعة")
        if deleted.get("id") == profile_store.get("active_profile_id"):
            new_index = min(index, len(profiles) - 1)
            profile_store["active_profile_id"] = profiles[new_index]["id"]
            profile_context.set(profiles[new_index]["id"])
            get_account_cache().clear()
            get_account_status_cache().clear()
            save_data()
        else:
            save_data(db)

        await callback_query.message.delete()
        await callback_query.message.reply_text(
            f"🗑 تم حذف {deleted_name} نهائيًا.",
            reply_markup=profile_menu_keyboard()
        )
    elif data.startswith("delete_template_"):
        index = int(data.split("_")[2])
        if 0 <= index < len(db["templates"]):
            deleted = db["templates"].pop(index)
            save_data(db)
            await callback_query.message.delete()
            await callback_query.message.reply_text(f"🗑 تم حذف الكليشة: {deleted[:50]}...")
        else:
            await callback_query.message.reply_text("❌ العنصر غير موجود.")
    elif data.startswith("delete_group_"):
        index = int(data.split("_")[2])
        if 0 <= index < len(db["groups"]):
            deleted = db["groups"].pop(index)
            save_data(db)
            await callback_query.message.delete()
            await callback_query.message.reply_text(f"🗑 تم حذف الكروب: {deleted}")
        else:
            await callback_query.message.reply_text("❌ العنصر غير موجود.")
    elif data.startswith("delete_account_"):
        parts = data.split("_")
        try:
            index = int(parts[2])
        except (IndexError, ValueError):
            return await callback_query.message.reply_text("❌ الحساب غير موجود.")

        profile_id = "_".join(parts[3:]) if len(parts) > 3 else current_profile_id()
        profile = next(
            (
                item
                for item in profile_store.get("profiles", [])
                if item.get("id") == profile_id
            ),
            None,
        )
        if profile is None:
            return await callback_query.message.reply_text("❌ المجموعة غير موجودة.")

        token = profile_context.set(profile_id)
        logout_error = None
        had_userbot_tasks = bool(profile_userbot_tasks.get(profile_id))
        try:
            profile_data = ensure_profile_data(profile.get("data") or {})
            accounts = profile_data.get("accounts", [])
            if not 0 <= index < len(accounts):
                return await callback_query.message.reply_text("❌ الحساب غير موجود.")

            account_number = index + 1
            session_str = accounts[index]

            if had_userbot_tasks:
                await stop_all_userbots(profile_id)

            accounts.pop(index)
            for key in (
                "account_errors",
                "last_group_index",
                "account_blocked_groups",
                "account_group_posts",
                "account_group_incoming",
                "account_group_last_sent",
            ):
                profile_data[key] = remove_indexed_account_state(
                    profile_data.get(key, {}),
                    index,
                    one_based=True,
                )
            profile_data["account_joined_channels"] = remove_indexed_account_state(
                profile_data.get("account_joined_channels", {}),
                index,
                one_based=False,
            )
            profile["data"] = profile_data
            save_data(profile_data)

            persisted_profile = next(
                (
                    item
                    for item in profile_store.get("profiles", [])
                    if item.get("id") == profile_id
                ),
                None,
            )
            persisted_accounts = (
                (persisted_profile or {}).get("data", {}).get("accounts", [])
            )
            if session_str in persisted_accounts:
                raise RuntimeError("تعذر حفظ حذف الحساب في ملف البيانات")

            get_account_cache().clear()
            get_account_status_cache().clear()

            temp_client = None
            try:
                temp_client = Client(
                    f"logout_session_{profile_id}_{index}",
                    api_id=API_ID,
                    api_hash=API_HASH,
                    session_string=_normalize_session_string(session_str),
                    in_memory=True,
                )
                await _start_user_client(temp_client, start_updates=False)
                await temp_client.log_out()
            except Exception as error:
                logout_error = error
            finally:
                if temp_client:
                    try:
                        await temp_client.stop()
                    except Exception:
                        pass

            if had_userbot_tasks and profile_data.get("accounts"):
                await start_all_userbots()

            if logout_error:
                await callback_query.message.reply_text(
                    f"🗑 تم حذف الحساب رقم {account_number} من البوت.\n"
                    f"⚠️ تعذر تسجيل الخروج من Telegram: {logout_error}"
                )
            else:
                await callback_query.message.reply_text(
                    f"🗑 تم حذف الحساب رقم {account_number} وتسجيل الخروج بنجاح!"
                )
            await callback_query.message.delete()
        except Exception as error:
            print(f"❌ Account deletion failed for {profile_id}/{index}: {error}")
            await callback_query.message.reply_text(
                f"❌ لم يتم حذف الحساب: {str(error)[:180]}"
            )
        finally:
            profile_context.reset(token)

# --- /start command ---
@app.on_message(
    filters.private & filters.incoming & filters.command("start"),
    group=-1,
)
async def start_cmd(client: Client, message: Message):
    if not message.from_user:
        return
    if message.from_user.id != OWNER_ID:
        return await message.reply_text("⛔ هذا البوت مخصص لمالكه فقط.")
    if db.get("joined_channels"):
        ensure_auto_leave_task()
    db["user_state"].pop(str(OWNER_ID), None)
    save_data(db)
    await show_profile_menu(message)

# --- Toggle auto join ---
@app.on_message(filters.private & filters.user(OWNER_ID) & filters.command("toggle_auto_join"))
async def toggle_auto_join(client: Client, message: Message):
    db["auto_join_groups"] = not db.get("auto_join_groups", True)
    save_data(db)
    status = "مفعل" if db["auto_join_groups"] else "معطل"
    await message.reply_text(f"✅ الانضمام التلقائي للكروبات الآن: {status}")

# --- Main execution ---
if __name__ == "__main__":
    print("🤖 Bot running with advanced features...")
    print(f"👤 Owner: {OWNER_ID}")
    print(f"📊 Data: {DATA_FILE}")
    print("✨ Features:")
    print("  🔄 Sequential posting system")
    print("  🎯 Template rotation (1, 2, 3...)")
    print("  🔄 Group rotation for each account")
    print("  📡 Auto-join links from bot messages in groups only")
    print("  ⏰ Auto-leave after 24 hours")
    print("  👥 Reply forwarding to owner")
    print("  💬 Owner reply system")
    print("  📱 Private message handling")
    print("  🛡️ Account ban/freeze monitoring")
    
    async def startup_tasks():
        for profile in profile_store.get("profiles", []):
            profile_id = profile.get("id")
            token = profile_context.set(profile_id)
            try:
                await start_all_userbots()
                if db.get("is_running") and db.get("accounts") and db.get("templates") and db.get("groups"):
                    profile_posting_tasks[profile_id] = asyncio.create_task(auto_posting_loop())
                    print(f"🔄 Posting loop resumed for {profile_id}")
            finally:
                profile_context.reset(token)

    async def run_background_startup():
        try:
            await startup_tasks()
        except asyncio.CancelledError:
            raise
        except Exception as error:
            print(f"❌ Background startup failed: {error}")

    async def run_main_bot():
        startup_task = None
        try:
            await app.start()
            me = await app.get_me()
            print(
                f"✅ Main bot connected: @{me.username or 'no_username'} "
                f"(ID {me.id})"
            )
            startup_task = asyncio.create_task(run_background_startup())
            await idle()
        finally:
            if startup_task and not startup_task.done():
                startup_task.cancel()
                await asyncio.gather(startup_task, return_exceptions=True)
            if app.is_connected:
                await app.stop()

    asyncio.get_event_loop().run_until_complete(run_main_bot())
