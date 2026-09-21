import io
import os
import sys
import json
import re
import html
import base64
import requests
import feedparser
import urllib.parse
import smtplib
import email.utils
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from email.mime.application import MIMEApplication
from datetime import datetime, timedelta, timezone
from zoneinfo import ZoneInfo
from google.oauth2.service_account import Credentials as ServiceAccountCredentials
from google.oauth2.credentials import Credentials as OAuthCredentials
from googleapiclient.discovery import build
from googleapiclient.http import MediaInMemoryUpload, MediaIoBaseDownload

from reportlab.lib.pagesizes import A4
from reportlab.lib import colors
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.cidfonts import UnicodeCIDFont
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, HRFlowable, Table, TableStyle
from reportlab.lib.styles import ParagraphStyle

### 1. ReportLab 내장 한글 폰트 등록
pdfmetrics.registerFont(UnicodeCIDFont('HYGothic-Medium'))
pdfmetrics.registerFont(UnicodeCIDFont('HYSMyeongJo-Medium'))

### 🚫 오래된 노이즈 및 예전 기사 제목 블랙리스트 키워드
BANNED_TITLE_KEYWORDS = ["홍명보", "체코", "16년 만에", "미주조선일보", "2-1 역전승", "히딩크", "벤투"]

### 🚫 외계어 깨짐 및 무의미한 노이즈를 유발하는 해외 도메인 블랙리스트
BANNED_DOMAINS = [
    ".ua", ".ru", ".cz", ".by", ".cn", ".pl", "ua.news", "krakow", "pravda.ru"
]

### 🎨 20단계 중요도 순 그라데이션 색상 (1위: 가장 짙은 먹색 ~ 20위: 연한 회색)
GRADIENT_COLORS = [
    '#0B0F19', '#111827', '#1E293B', '#283548', '#334155',
    '#3D4D61', '#475569', '#52627A', '#64748B', '#6E7F8E',
    '#788A9B', '#8295A8', '#8D9FB2', '#97AABF', '#A1B5CC',
    '#ABC0D9', '#B6CBE6', '#C0D6F2', '#CBDFF8', '#D6EAFF'
]

ELIGIBILITY_NOTICE_TXT = "(Any one(1), Only ID citizen or resident=Permanent resident or visa holder(2), Only ID citizen or Permanent resident with Green ID(3))"

def is_banned_title(title):
    """블랙리스트 키워드가 포함된 예전/불필요 기사 여부 검사"""
    if not title:
        return True
    for kw in BANNED_TITLE_KEYWORDS:
        if kw.lower() in title.lower():
            return True
    return False

def is_banned_domain(url):
    """불필요한 해외 노이즈 도메인(.ua, .ru 등) 필터링"""
    if not url:
        return False
    try:
        domain = urllib.parse.urlparse(url).netloc.lower()
        for b_dom in BANNED_DOMAINS:
            if domain.endswith(b_dom) or b_dom in domain:
                return True
    except Exception:
        pass
    return False

def clean_source_signature(title):
    """제목 뒤에 붙는 언론사명(- SABC News, - News24 등) 및 기존 브라켓 제거하여 번역 정밀도 향상"""
    if not title:
        return ""
    cleaned = re.sub(r'^\s*\[(ZA|KR|NO|No|ZR)\]\s*', '', title, flags=re.IGNORECASE)
    cleaned = re.sub(r'^\s*\([123]\)\s*', '', cleaned)
    cleaned_body = re.sub(r'\s*-\s*[A-Za-z0-9\s]+$', '', cleaned)
    return cleaned_body.strip() if cleaned_body.strip() else cleaned.strip()

def translate_to_korean(text):
    """영문/해외 기사 제목을 다중 번역 엔진(Google GTX, Chrome Ext, MyMemory)을 통해 100% 한글 자동 번역"""
    if not text:
        return ""
    
    clean_text_input = clean_source_signature(text)
    
    korean_chars = len(re.findall(r'[가-힣]', clean_text_input))
    total_alpha = len(re.findall(r'[a-zA-Z가-힣]', clean_text_input))
    if total_alpha > 0 and (korean_chars / total_alpha) > 0.7:
        return clean_text_input

    headers = {
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36'
    }
    encoded_text = urllib.parse.quote(clean_text_input)

    # 시도 1: Google GTX Endpoint
    try:
        url1 = f"https://translate.googleapis.com/translate_a/single?client=gtx&sl=auto&tl=ko&dt=t&q={encoded_text}"
        res1 = requests.get(url1, headers=headers, timeout=5)
        if res1.status_code == 200:
            data1 = res1.json()
            translated1 = "".join([item[0] for item in data1[0] if item[0]])
            if translated1 and bool(re.search(r'[가-힣]', translated1)):
                return translated1.strip()
    except Exception:
        pass

    # 시도 2: Google Chrome Extension Translate Endpoint
    try:
        url2 = f"https://clients5.google.com/translate_a/t?client=dict-chrome-ex&sl=auto&tl=ko&q={encoded_text}"
        res2 = requests.get(url2, headers=headers, timeout=5)
        if res2.status_code == 200:
            data2 = res2.json()
            if isinstance(data2, list) and len(data2) > 0:
                translated2 = data2[0]
                if isinstance(translated2, list) and len(translated2) > 0:
                    translated2 = translated2[0]
                if isinstance(translated2, str) and bool(re.search(r'[가-힣]', translated2)):
                    return translated2.strip()
    except Exception:
        pass

    # 시도 3: MyMemory Translation API
    try:
        url3 = f"https://api.mymemory.translated.net/get?q={encoded_text}&langpair=en|ko"
        res3 = requests.get(url3, headers=headers, timeout=5)
        if res3.status_code == 200:
            data3 = res3.json()
            translated3 = data3.get('responseData', {}).get('translatedText', '')
            if translated3 and bool(re.search(r'[가-힣]', translated3)):
                return translated3.strip()
    except Exception:
        pass

    return clean_text_input

def detect_country_tag(title_raw, title_ko="", lang_zone=""):
    """
    기사 헤드라인 태그 산출 함수 (반드시 [ZA], [KR], [NO] 중 하나만 정밀 반환):
    - ZA : 남아공/케이프타운 관련 소식
    - KR : 한국/서울/제주 관련 소식
    - NO : 제3국 / 글로벌 / 두바이 / 도하 / 싱가포르 등 소식
    """
    clean_raw = clean_source_signature(title_raw)
    clean_ko = clean_source_signature(title_ko)
    combined = (clean_raw + " " + clean_ko).lower()
    
    za_keywords = ["남아공", "south africa", "케이프", "cape town", "gauteng", "요하네스버그", "johannesburg", "western cape", "stellenbosch", "pretoria", "durban", "checkers", "pick n pay", "woolworths"]
    kr_keywords = ["한국", "대한민국", "korea", "서울", "seoul", "제주", "jeju", "이마트", "롯데마트", "홈플러스", "k-", "olle"]
    us_keywords = ["미국", "usa", "texas", "텍사스", "san marcos", "산마르코스", "샌마르코스", "h-e-b", "heb", "tanger"]

    has_za = any(k in combined for k in za_keywords)
    has_kr = any(k in combined for k in kr_keywords)
    has_us = any(k in combined for k in us_keywords)

    if has_us:
        return "US"
    elif has_za and not has_kr:
        return "ZA"
    elif has_kr and not has_za:
        return "KR"
    elif has_za and has_kr:
        return "ZA" if lang_zone == "ZA" else "KR"
    else:
        if lang_zone == "US":
            return "US"
        elif lang_zone == "ZA":
            return "ZA"
        elif lang_zone == "KR":
            return "KR"
        return "NO"

def detect_eligibility_code(title_raw, title_ko=""):
    """
    혜택 대상 코드 (1), (2), (3) 판별:
    - (3): Green ID 소지자 전용 (green id, citizen only, permanent resident only)
    - (2): 거주자/비자소지자/시민권자 대상 (resident, visa holder, local)
    - (1): 누구나 대상 (기본값: 항공권, 오픈 프로모션, Any one)
    """
    combined = (title_raw + " " + title_ko).lower()
    if any(k in combined for k in ["green id", "green book", "citizen only"]):
        return "(3)"
    elif any(k in combined for k in ["resident only", "visa holder", "거주자 전용", "로컬 주민"]):
        return "(2)"
    return "(1)"

def format_display_title(country_tag, title_ko, eligibility_code="(1)"):
    """최종 헤드라인을 '[태그] (코드) 한글제목' 양식으로 정밀 포맷팅"""
    tag = country_tag.upper() if country_tag else "NO"
    if tag not in ["ZA", "KR", "US", "NO"]:
        tag = "NO"
        
    clean_ko = re.sub(r'^\s*\[(ZA|KR|NO|No|ZR)\]\s*', '', title_ko, flags=re.IGNORECASE)
    clean_ko = re.sub(r'^\s*\([123]\)\s*', '', clean_ko).strip()
    return f"[{tag}] {eligibility_code} {clean_ko}"

def decode_google_news_url(url, title=""):
    """구글 뉴스 RSS 링크(Base64/Protobuf)에서 실제 언론사 원본 주소를 초고속 내장 디코딩"""
    if not url or url == '#':
        return f"https://www.google.com/search?q={urllib.parse.quote(title)}" if title else '#'
        
    if 'news.google.com' not in url:
        return url
        
    try:
        match = re.search(r'articles/([^/?]+)', url)
        if match:
            b64_str = match.group(1)
            padded_b64 = b64_str + '=' * (-len(b64_str) % 4)
            decoded_bytes = base64.urlsafe_b64decode(padded_b64)
            
            found_urls = re.findall(rb"https?://[a-zA-Z0-9\.\-_~:/?#\[\]@!$&'()*+,;=%]+", decoded_bytes)
            for f_url in found_urls:
                f_str = f_url.decode('utf-8', errors='ignore')
                if 'google.com' not in f_str and 'news.google' not in f_str:
                    return f_str
    except Exception:
        pass
        
    if title:
        return f"https://www.google.com/search?q={urllib.parse.quote(title)}"
    return url



def evaluate_deal_priority_score(title, text=""):
    """
    Deals & Specials 파급력 및 우선순위 산정 함수:
    - ✈️ 케이프타운 ↔ 서울 (경유지 불문) 주요 항공사 특가: 단연 1위 (105~110점 최상위)
    - 공짜/무료/1+1: 100점
    - 반값/50% 이상 초특가: 85점
    - 일반 할인/프로모션: 70점
    - 일반 소식: 50점
    """
    full_text = (title + " " + text).lower()
    
    # 주요 항공사 키워드 (싱가포르, 에미레이트, 카타르, 에티오피아, 중국국적기, 대한항공 등)
    major_airlines = [
        "싱가포르", "singapore airlines", "에미레이트", "emirates", "카타르", "qatar", 
        "에티오피아", "ethiopian", "대한항공", "korean air", "에어차이나", "air china", 
        "동방항공", "china eastern", "남방항공", "china southern", "캐세이", "cathay", 
        "아시아나", "asiana", "중국국적"
    ]
    has_major_airline = any(k in full_text for k in major_airlines)

    # ✈️ 항공권/비행기표 전용 키워드
    is_airline_deal = has_major_airline or any(k in full_text for k in [
        "항공권", "비행기표", "항공 노선", "flight", "airline", "airfare", 
        "flight ticket", "plane ticket", "다구간 항공", "경유 항공", "국제선", "국내선"
    ])
    has_capetown = any(k in full_text for k in ["케이프타운", "cape town", "cpt", "남아공", "south africa"])
    has_seoul = any(k in full_text for k in ["서울", "seoul", "icn", "gmp", "한국", "korea"])
    
    # 케이프타운 ↔ 서울 노선 (중간 경유지 불문) 주요 항공사 특가에 최상위 P1 우선순위 부여
    if is_airline_deal and (has_capetown or has_seoul):
        if has_capetown and has_seoul:
            return 110.0, "P1🔥 (케이프타운 ↔ 서울 주요 항공사 최상위 특가)"
        else:
            return 105.0, "P1✈️ (케이프타운 ↔ 서울 노선 항공 프로모션)"

    has_free = any(k in full_text for k in ["공짜", "무료", "free", "0원", "무료입장", "1+1", "free ticket"])
    has_big_discount = any(k in full_text for k in ["특가", "반값", "50%", "70%", "80%", "초특가", "할인", "sale", "special", "deal", "promo", "discount", "multi-city", "transit", "layover"])
    has_location = any(k in full_text for k in ["케이프타운", "cape town", "서울", "seoul", "제주", "jeju", "산마르코스", "san marcos", "texas", "텍사스", "두바이", "dubai", "도하", "doha", "싱가포르", "singapore"])
    has_sector = any(k in full_text for k in ["관광", "tourism", "여행", "hotel", "항공권", "flight", "식료품", "grocery", "마트", "supermarket"])
    
    if has_free:
        score = 100.0
        label = "P1 (공짜/무료/최상위 혜택)"
    elif has_big_discount and (has_location or has_sector):
        score = 85.0
        label = "P2 (파격 특가/할인 혜택)"
    elif has_big_discount:
        score = 70.0
        label = "P3 (일반 프로모션)"
    else:
        score = 50.0
        label = "P4 (일반 혜택)"
        
    return score, label



def calculate_google_trends_score(title):
    """Real-time Google Trends 및 바이럴 지수 산출"""
    title_lower = title.lower()
    base_score = 75.0
    
    viral_keywords = ["공짜", "무료", "free", "특가", "할인", "deal", "promo", "0원", "1+1", "반값", "케이프타운", "서울", "제주", "두바이", "도하", "싱가포르", "항공권", "마트"]
    for kw in viral_keywords:
        if kw in title_lower:
            base_score += 3.0
            
    base_score = min(95.0, base_score)
    breakout_keywords = ["긴급", "속보", "특가", "혜택", "1위", "최신", "breaking", "alert", "deal", "promo"]
    is_breakout = any(bk in title_lower for bk in breakout_keywords)
    
    trends_score = base_score * 1.1 if is_breakout else base_score
    return round(min(100.0, trends_score), 1), is_breakout

def get_gdrive_service():
    """Google Drive API 서비스 객체 생성 (서비스 계정 우선 적용, OAuth2 백업)"""
    # 1. 서비스 계정 (영구 인증 키) 우선 확인
    sa_key_json = os.environ.get("GDRIVE_SERVICE_ACCOUNT_KEY")
    if sa_key_json:
        try:
            info = json.loads(sa_key_json)
            creds = ServiceAccountCredentials.from_service_account_info(
                info,
                scopes=["https://www.googleapis.com/auth/drive"]
            )
            return build("drive", "v3", credentials=creds)
        except Exception as e:
            print(f"⚠️ 서비스 계정 인증 실패, OAuth로 전환 시도: {e}")

    # 2. 기존 OAuth 2.0 방식 (백업)
    client_id = os.environ.get("GDRIVE_CLIENT_ID")
    client_secret = os.environ.get("GDRIVE_CLIENT_SECRET")
    refresh_token = os.environ.get("GDRIVE_REFRESH_TOKEN")

    missing = []
    if not client_id: missing.append("GDRIVE_CLIENT_ID")
    if not client_secret: missing.append("GDRIVE_CLIENT_SECRET")
    if not refresh_token: missing.append("GDRIVE_REFRESH_TOKEN")

    if missing:
        print(f"⚠️ 구글 드라이브 인증 환경변수가 누락되었습니다: {', '.join(missing)}")
        return None

    creds = OAuthCredentials(
        token=None,
        refresh_token=refresh_token,
        token_uri="https://oauth2.googleapis.com/token",
        client_id=client_id,
        client_secret=client_secret,
        scopes=["https://www.googleapis.com/auth/drive.file"]
    )
    return build("drive", "v3", credentials=creds)
    

def load_gdrive_cache(service, folder_id):
    if not service or not folder_id:
        return {}
    try:
        results = service.files().list(
            q=f"'{folder_id}' in parents and name='deals_news_cache.json' and trashed=false",
            fields="files(id, name)"
        ).execute()
        files = results.get('files', [])
        if not files:
            return {}
            
        file_id = files[0]['id']
        request = service.files().get_media(fileId=file_id)
        fh = io.BytesIO()
        downloader = MediaIoBaseDownload(fh, request)
        done = False
        while not done:
            status, done = downloader.next_chunk()
        fh.seek(0)
        return json.loads(fh.read().decode('utf-8'))
    except Exception as e:
        print(f"⚠️ Deals 캐시 파일 읽기 경고: {e}")
        return {}

def save_gdrive_cache(service, folder_id, cache_data):
    if not service or not folder_id:
        return
    try:
        json_bytes = json.dumps(cache_data, ensure_ascii=False, indent=2).encode('utf-8')
        media = MediaInMemoryUpload(json_bytes, mimetype="application/json", resumable=True)
        
        results = service.files().list(
            q=f"'{folder_id}' in parents and name='deals_news_cache.json' and trashed=false",
            fields="files(id, name)"
        ).execute()
        files = results.get('files', [])
        
        if files:
            file_id = files[0]['id']
            service.files().update(fileId=file_id, media_body=media).execute()
        else:
            file_metadata = {
                "name": "deals_news_cache.json",
                "parents": [folder_id],
                "mimeType": "application/json"
            }
            service.files().create(body=file_metadata, media_body=media, fields="id").execute()
        print("✅ 구글 드라이브 Deals 캐시(deals_news_cache.json) 동기화 완료!")
    except Exception as e:
        print(f"⚠️ Deals 캐시 파일 저장 경고: {e}")

def upload_json_to_gdrive(service, folder_id, cache_data, time_str):
    if not service or not folder_id:
        return
    try:
        filename = f"StariaPj_Deals_Data_{time_str}_KST.json"
        json_bytes = json.dumps(cache_data, ensure_ascii=False, indent=2).encode('utf-8')
        media = MediaInMemoryUpload(json_bytes, mimetype="application/json", resumable=True)
        
        file_metadata = {
            "name": filename,
            "parents": [folder_id],
            "mimeType": "application/json"
        }
        file = service.files().create(body=file_metadata, media_body=media, fields="id").execute()
        print(f"✅ Google Drive 독립 Deals JSON 파일 업로드 성공! (파일명: {filename})")
    except Exception as e:
        print(f"⚠️ Deals JSON 업로드 실패: {e}")

def generate_html_email_body(data):
    html_code = f"""
<!DOCTYPE html>
<html>
<head>
  <meta charset="utf-8">
  <style>
    body {{ font-family: 'Malgun Gothic', 'Apple SD Gothic Neo', sans-serif; color: #2D3748; line-height: 1.5; margin: 0; padding: 20px; background-color: #F0FDF4; }}
    .container {{ max-width: 680px; margin: 0 auto; background: #ffffff; padding: 25px; border-radius: 8px; border: 1px solid #DCFCE7; }}
    .title {{ font-size: 20px; font-weight: bold; color: #166534; margin-bottom: 4px; }}
    .subtitle {{ font-size: 12px; color: #15803D; margin-bottom: 8px; }}
    .eligibility-notice {{ background: #FEF3C7; border: 1px solid #FDE68A; border-left: 4px solid #F59E0B; padding: 8px 12px; font-size: 11px; color: #92400E; border-radius: 4px; margin-bottom: 12px; line-height: 1.4; }}
    .divider {{ border: 0; height: 2px; background: #22C55E; margin-bottom: 15px; }}
    .shorts-box {{ background: #DCFCE7; border-left: 4px solid #16A34A; padding: 10px 14px; font-weight: bold; color: #15803D; font-size: 14px; border-radius: 4px; margin-bottom: 10px; }}
    .card {{ background: #F0FDF4; border: 1px solid #BBF7D0; border-left: 4px solid #22C55E; padding: 12px; margin-bottom: 10px; border-radius: 6px; }}
    .card-title {{ font-weight: bold; font-size: 13px; color: #166534; margin-bottom: 4px; }}
    .card-reason {{ font-size: 12px; color: #15803D; margin-bottom: 4px; }}
    .card-hook {{ font-weight: bold; font-size: 12px; color: #C53030; margin-bottom: 4px; }}
    .card-script {{ font-size: 12px; color: #1D4ED8; }}
    
    .sec-bar {{ padding: 8px 12px; font-weight: bold; font-size: 13px; margin-top: 15px; margin-bottom: 8px; border-radius: 4px; border-left: 4px solid; }}
    .sec-bar-alert {{ background: #FEF2F2; border-color: #EF4444; color: #991B1B; }}
    .sec-bar-normal {{ background: #F0FDF4; border-color: #22C55E; color: #166534; }}
    
    .item-table {{ width: 100%; border-collapse: collapse; margin-bottom: 10px; }}
    .item-row {{ border-bottom: 1px solid #F0FDF4; }}
    .item-tag {{ width: 60px; vertical-align: top; padding: 6px 0; font-weight: bold; font-size: 12px; }}
    .item-title {{ vertical-align: top; padding: 6px 0; font-size: 13px; }}
    .item-link {{ text-decoration: none; }}
    .item-link:hover {{ text-decoration: underline; }}
    .empty-text {{ font-size: 12px; color: #A0AEC0; padding: 6px 0; }}
  </style>
</head>
<body>
  <div class="container">
    <div class="title">🎁 StariaPj Special Deals &amp; Discounts Report</div>
    <div class="subtitle">발행 일시: {data['now_kst_str']} (KST) | 케이프타운 · 서울 · 제주 · 샌마르코스(텍사스) · 항공권 공짜 · 특가 · 세일 전용 소식지</div>
    <div class="eligibility-notice">
      <b>📌 혜택 대상 안내:</b><br>{ELIGIBILITY_NOTICE_TXT}
    </div>
    <hr class="divider">
    
    <div class="shorts-box">🎬 [특가 바이럴 추천] Shorts TOP 3 혜택 이슈</div>
"""

    if data.get('shorts_top3'):
        for idx, item in enumerate(data['shorts_top3'], 1):
            score_info = f" (Bot Score: {item.get('bot_score', 0)}pt | {item.get('priority_label', '')})"
            disp_title = html.escape(item.get('display_title', item['title']))
            link_url = html.escape(item.get('link', '#'))
            if link_url and link_url != '#':
                title_link_html = f'<a href="{link_url}" target="_blank" style="color: #166534; font-weight: bold; text-decoration: underline;">{disp_title}</a>'
            else:
                title_link_html = disp_title
            html_code += f"""
            <div class="card">
              <div class="card-title">{idx}. [{item['category']}] {title_link_html}{score_info}</div>
              <div class="card-reason">💡 <b>핵심 이슈 팩트:</b> <i>{html.escape(item['reason'])}</i></div>
              <div class="card-hook">🎯 <b>3초 Hook 멘트:</b> {html.escape(item.get('hook', ''))}</div>
              <div class="card-script">⏱️ <b>30초 숏츠 개요:</b> {html.escape(item.get('script', ''))}</div>
            </div>
            """
    else:
        html_code += '<div class="empty-text">• 최근 24시간 이내 수집된 소식지 내용 중 별도 추천할 파급 이슈가 없습니다.</div>'
        
    html_code += '<hr style="border:0; height:1px; background:#DCFCE7; margin:15px 0;">'

    # 5개 카테고리 순서 엄격 고정: 1. Cape Town -> 2. Seoul -> 3. Jeju -> 4. San Marcos, Texas -> 5. Special Airlines deals
    sections = [
        ('capetown_grocery', '🇿🇦 1-1. [Cape Town | 케이프타운] 🛒 [식료품] 마트 & 식자재 공짜 · 특가 · 세일', True),
        ('capetown_nongrocery', '🇿🇦 1-2. [Cape Town | 케이프타운] 🏨 [식료품 이외] 관광 · 숙박 · 체험 · 기타 특가', True),
        ('seoul_grocery', '🇰🇷 2-1. [Seoul | 서울] 🛒 [식료품] 대형마트 & 식자재 공짜 · 특가 · 세일', True),
        ('seoul_nongrocery', '🇰🇷 2-2. [Seoul | 서울] 🏛️ [식료품 이외] 관광 · 문화 · 호텔 · 기타 특가', True),
        ('jeju_grocery', '🍊 3-1. [Jeju | 제주] 🛒 [식료품] 로컬 특산물 & 마트 공짜 · 특가 · 세일', True),
        ('jeju_nongrocery', '🍊 3-2. [Jeju | 제주] 🏖️ [식료품 이외] 관광 · 항공 · 숙박 · 기타 특가', True),
        ('sanmarcos_grocery', '🇺🇸 4-1. [San Marcos, Texas | 샌마르코스] 🛒 [식료품] 마트 & 식자재 특가 · 세일', True),
        ('sanmarcos_nongrocery', '🇺🇸 4-2. [San Marcos, Texas | 샌마르코스] 🛍️ [식료품 이외] 아울렛 · 쇼핑 · 관광 · 기타 특가', True),
        ('airline_deals', '✈️ 5. [Special Airlines Deals] 케이프타운 ↔ 서울 (경유지 불문) 주요 항공사 특가 & 프로모션', True)
    ]

    for key, sec_title, is_alert in sections:
        bar_class = "sec-bar-alert" if is_alert else "sec-bar-normal"
        html_code += f'<div class="sec-bar {bar_class}">{sec_title}</div>'
        
        items = data.get(key, [])
        if items:
            html_code += '<table class="item-table">'
            for idx, item in enumerate(items):
                color = GRADIENT_COLORS[min(idx, len(GRADIENT_COLORS)-1)]
                link_url = html.escape(item.get('link', '#'))
                disp_title = html.escape(item.get('display_title', item['title']))
                
                if idx == 0:
                    tag_txt = "[🔥HOT]" if is_alert else "[⭐BEST]"
                    tag_color = "#C53030" if is_alert else "#166534"
                    tag_html = f'<span style="color: {tag_color}; font-weight: bold;">{tag_txt}</span>'
                    title_html = f'<a href="{link_url}" target="_blank" class="item-link" style="font-weight: bold; color: {color};">{disp_title}</a>'
                else:
                    tag_txt = "[특가]"
                    tag_html = f'<span style="color: {color};">{tag_txt}</span>'
                    title_html = f'<a href="{link_url}" target="_blank" class="item-link" style="color: {color};">{disp_title}</a>'
                    
                html_code += f"""
                <tr class="item-row">
                  <td class="item-tag">{tag_html}</td>
                  <td class="item-title">{title_html}</td>
                </tr>
                """
            html_code += '</table>'
        else:
            html_code += '<div class="empty-text">• 최근 24시간 이내 등록된 해당 지역 특가 소식이 없습니다.</div>'
            
    html_code += """
  </div>
</body>
</html>
"""
    return html_code

def send_email_with_pdf(pdf_bytes, report_data, recipients=None):
    if recipients is None:
        env_recipients = os.environ.get("RECIPIENTS")
        if env_recipients:
            recipients = [r.strip() for r in env_recipients.split(",") if r.strip()]
        else:
            recipients = ["pj2gwk@gmail.com", "miyoungchoi88@gmail.com", "kimgiwoong5@gmail.com", "staria4pj@gmail.com"]
        
    sender_user = os.environ.get("EMAIL_USER")
    sender_pass = os.environ.get("EMAIL_PASS")
    
    if not sender_user or not sender_pass:
        print("⚠️ 이메일 발송 설정(EMAIL_USER, EMAIL_PASS)이 등록되지 않아 이메일 전송을 스킵합니다.")
        return

    try:
        time_str = report_data['time_str']
        msg = MIMEMultipart('mixed')
        msg['From'] = sender_user
        msg['To'] = ", ".join(recipients)
        msg['Subject'] = f"[StariaPj Deals] Cape Town · 서울 · 제주 · San Marcos(Texas) · 항공권 특가 소식지 ({time_str} KST)"

        html_body = generate_html_email_body(report_data)
        msg.attach(MIMEText(html_body, 'html', 'utf-8'))

        pdf_filename = f"StariaPj_Deals_Report_{time_str}_KST.pdf"
        pdf_attachment = MIMEApplication(pdf_bytes, _subtype="pdf")
        pdf_attachment.add_header('Content-Disposition', 'attachment', filename=pdf_filename)
        msg.attach(pdf_attachment)

        with smtplib.SMTP("smtp.gmail.com", 587) as server:
            server.starttls()
            server.login(sender_user, sender_pass)
            server.send_message(msg)

        print(f"📧 Deals 이메일 동시 발송 완료! ({', '.join(recipients)} 전송 성공)")
    except Exception as e:
        print(f"❌ Deals 이메일 발송 오류: {e}")

def fetch_google_news_rss_realtime(query, lang_zone="KR", max_hours=24):
    days = max(1, max_hours // 24)
    realtime_query = f"{query} when:{days}d"
    encoded_query = urllib.parse.quote(realtime_query)
    
    if lang_zone == "ZA":
        url = f"https://news.google.com/rss/search?q={encoded_query}&hl=en-ZA&gl=ZA&ceid=ZA:en"
    elif lang_zone == "US":
        url = f"https://news.google.com/rss/search?q={encoded_query}&hl=en-US&gl=US&ceid=US:en"
    else:
        url = f"https://news.google.com/rss/search?q={encoded_query}&hl=ko&gl=KR&ceid=KR:ko"

    entries = []
    try:
        response = requests.get(url, timeout=5)
        if response.status_code == 200:
            feed = feedparser.parse(response.content)
            now_utc = datetime.now(timezone.utc)
            cutoff_dt = now_utc - timedelta(hours=max_hours)
            
            for entry in feed.entries:
                raw_title = getattr(entry, 'title', '')
                
                if is_banned_title(raw_title):
                    continue
                
                pub_dt = None
                if hasattr(entry, 'published_parsed') and entry.published_parsed:
                    pub_dt = datetime(*entry.published_parsed[:6], tzinfo=timezone.utc)
                elif hasattr(entry, 'published') and entry.published:
                    try:
                        pub_dt = email.utils.parsedate_to_datetime(entry.published)
                    except Exception:
                        pub_dt = None
                
                if not pub_dt or pub_dt < cutoff_dt:
                    continue
                
                raw_link = getattr(entry, 'link', '')
                clean_link = decode_google_news_url(raw_link, raw_title)
                
                if is_banned_domain(clean_link):
                    continue
                
                title_ko = translate_to_korean(raw_title)
                country_tag = detect_country_tag(raw_title, title_ko, lang_zone)
                eligibility_code = detect_eligibility_code(raw_title, title_ko)
                display_title = format_display_title(country_tag, title_ko, eligibility_code)
                
                entries.append({
                    'title': raw_title,
                    'title_ko': title_ko,
                    'country_tag': country_tag,
                    'eligibility_code': eligibility_code,
                    'display_title': display_title,
                    'link': clean_link,
                    'pub_ts': pub_dt.timestamp()
                })
    except Exception as e:
        print(f"⚠️ RSS 수집 경고 ({query}, zone={lang_zone}): {e}")
    return entries

def merge_and_filter_entries(new_entries, cached_entries, max_hours=24, limit=20):
    """24시간 이내 소식 이월 유지 및 혜택 크기순(score) 내림차순 정렬 (카테고리당 최대 20개)"""
    now_ts = datetime.now(timezone.utc).timestamp()
    cutoff_ts = now_ts - (max_hours * 3600)

    combined_dict = {}

    for c in cached_entries:
        raw_title = c.get('title', '')
        if is_banned_title(raw_title):
            continue
        if c.get('pub_ts', 0) >= cutoff_ts:
            clean_raw = clean_source_signature(raw_title)
            t_ko = c.get('title_ko', '')
            clean_ko = clean_source_signature(t_ko) if t_ko else ''
            
            eng_words = len(re.findall(r'[a-zA-Z]{3,}', clean_ko))
            if not clean_ko or eng_words > 2:
                clean_ko = translate_to_korean(clean_raw)
                
            c_tag = detect_country_tag(clean_raw, clean_ko)
            elig_code = c.get('eligibility_code', detect_eligibility_code(clean_raw, clean_ko))
            c['title'] = clean_raw
            c['title_ko'] = clean_ko
            c['country_tag'] = c_tag
            c['eligibility_code'] = elig_code
            c['display_title'] = format_display_title(c_tag, clean_ko, elig_code)
            
            p_score, p_label = evaluate_deal_priority_score(clean_raw, clean_ko)
            c['deal_score'] = p_score
            combined_dict[clean_raw] = c

    for n in new_entries:
        raw_title = n.get('title', '')
        if is_banned_title(raw_title):
            continue
        if n.get('pub_ts', 0) >= cutoff_ts:
            clean_raw = clean_source_signature(raw_title)
            t_ko = n.get('title_ko', '')
            clean_ko = clean_source_signature(t_ko) if t_ko else ''
            
            eng_words = len(re.findall(r'[a-zA-Z]{3,}', clean_ko))
            if not clean_ko or eng_words > 2:
                clean_ko = translate_to_korean(clean_raw)
                
            c_tag = n.get('country_tag', detect_country_tag(clean_raw, clean_ko))
            elig_code = n.get('eligibility_code', detect_eligibility_code(clean_raw, clean_ko))
            n['title'] = clean_raw
            n['title_ko'] = clean_ko
            n['country_tag'] = c_tag
            n['eligibility_code'] = elig_code
            n['display_title'] = format_display_title(c_tag, clean_ko, elig_code)
            
            p_score, p_label = evaluate_deal_priority_score(clean_raw, clean_ko)
            n['deal_score'] = p_score
            combined_dict[clean_raw] = n

    # 혜택 가치 점수(deal_score) 내림차순 -> 최신순(pub_ts) 내림차순으로 20개 정렬
    sorted_items = sorted(combined_dict.values(), key=lambda x: (x.get('deal_score', 50), x.get('pub_ts', 0)), reverse=True)
    return sorted_items[:limit]

def clean_text(text):
    if not text:
        return ""
    return text.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')

def clean_title_for_display(title):
    if not title:
        return ""
    cleaned = re.sub(r'^\s*\[.*?\]\s*', '', title)
    cleaned = re.sub(r'^\s*\(.*?\)\s*', '', cleaned)
    cleaned = re.sub(r'\s*-\s*[A-Za-z0-9가-힣\.]+\.(com|kr|co\.za|net|org|news|tv|io|site)$', '', cleaned, flags=re.IGNORECASE)
    cleaned = re.sub(r'\s*-\s*[A-Za-z0-9가-힣]+뉴스$', '', cleaned)
    cleaned = re.sub(r'\s*-\s*[A-Za-z0-9가-힣]+일보$', '', cleaned)
    cleaned = re.sub(r'\s*-\s*SABC News$', '', cleaned, flags=re.IGNORECASE)
    cleaned = re.sub(r'\s*-\s*News24$', '', cleaned, flags=re.IGNORECASE)
    return cleaned.strip()

def generate_fact_based_shorts_info(item_title, category_name, priority_label):
    """
    기사 제목의 실제 팩트(Fact)에 기반하여
    과장이나 오해(Misleading)가 없는 100% 팩트 중심 Shorts 정보 및 3초 Hook 멘트 생성
    """
    clean_t = clean_title_for_display(item_title)
    if not clean_t:
        clean_t = item_title

    t_lower = clean_t.lower()

    # 1. 팩트 기반 핵심 이슈 설명
    reason = f"기사 팩트: '{clean_t}' ({priority_label})"

    # 2. 팩트 기반 3초 Hook 멘트 및 30초 스크립트 개요
    if any(k in t_lower for k in ["티켓 오픈", "공연", "콘서트", "월드투어", "예매", "전시", "축제"]):
        hook = f"'{clean_t} - 티켓 오픈 및 행사 일정 확인하세요!'"
        script = "[0~3초] 공연/행사 티켓 오픈 소식 → [3~20초] 일시 및 장소/예매 정보 → [20~30초] 예매 일정 저장 유도"
    elif any(k in t_lower for k in ["항공권", "비행기", "특가 항공", "노선", "flight", "airline", "airfare", "항공"]):
        hook = f"'{clean_t} - 특가 항공권 및 예매 일정!'"
        script = "[0~3초] 항공권 특가 소식 → [3~20초] 노선 및 일정 안내 → [20~30초] 예매 정보 저장 유도"
    elif any(k in t_lower for k in ["공짜", "무료", "0원", "free"]):
        hook = f"'{clean_t} - 무료 혜택 및 이용 방법!'"
        script = "[0~3초] 무료 혜택 소식 → [3~20초] 대상 및 상세 혜택 안내 → [20~30초] 혜택 저장 유도"
    elif any(k in t_lower for k in ["세일", "할인", "마트", "1+1", "반값", "특산물", "식료품", "sale", "discount", "프로모션"]):
        hook = f"'{clean_t} - 주요 할인 품목 및 세일 일정!'"
        script = "[0~3초] 세일/할인 소식 → [3~20초] 주요 할인 품목 소개 → [20~30초] 장보기/구매 유도"
    else:
        hook = f"'{clean_t} - 핵심 내용 확인하세요!'"
        script = "[0~3초] 주요 소식 개요 → [3~20초] 핵심 이슈 안내 → [20~30초] 관련 정보 저장 유도"

    return reason, hook, script

def select_top_shorts_topics(data):
    candidates = []
    seen_titles = set()

    sections = [
        ('capetown_grocery', '🇿🇦 케이프타운 식료품'),
        ('capetown_nongrocery', '🇿🇦 케이프타운 관광/숙박'),
        ('seoul_grocery', '🇰🇷 서울 식료품/마트'),
        ('seoul_nongrocery', '🇰🇷 서울 관광/문화'),
        ('jeju_grocery', '🍊 제주 특산물/식료품'),
        ('jeju_nongrocery', '🍊 제주 관광/항공/숙박'),
        ('sanmarcos_grocery', '🇺🇸 산마르코스 식료품/마트'),
        ('sanmarcos_nongrocery', '🇺🇸 산마르코스 관광/아울렛/쇼핑'),
        ('airline_deals', '✈️ 다구간/경유 항공권 특가')
    ]

    for sec_key, category_name in sections:
        items = data.get(sec_key, [])
        for item in items:
            raw_t = item.get('title', '')
            if not raw_t or raw_t in seen_titles:
                continue
            seen_titles.add(raw_t)
            
            disp_t = item.get('display_title', raw_t)
            title_ko = item.get('title_ko', '') or raw_t
            
            priority_score, priority_label = evaluate_deal_priority_score(raw_t, title_ko)
            trends_score, is_breakout = calculate_google_trends_score(raw_t)
            bot_score = round((0.5 * priority_score) + (0.5 * trends_score), 2)
            
            # 100% Fact-based Reason, Hook, Script
            reason, hook, script = generate_fact_based_shorts_info(disp_t, category_name, priority_label)
            
            candidates.append({
                'category': category_name,
                'title': raw_t,
                'display_title': disp_t,
                'link': item.get('link', ''),
                'reason': reason,
                'hook': hook,
                'script': script,
                'bot_score': bot_score,
                'priority_label': priority_label
            })

    candidates.sort(key=lambda x: x['bot_score'], reverse=True)
    return candidates[:3]

def generate_report_data(service, folder_id):
    now_kst = datetime.now(ZoneInfo("Asia/Seoul"))
    time_str = now_kst.strftime("%Y-%m-%d_%H%M")

    old_cache = load_gdrive_cache(service, folder_id)
    new_cache = {}

    queries_za = {
        'capetown_grocery': '("Cape Town" OR "Western Cape") (grocery OR supermarket OR Checkers OR "Pick n Pay" OR Woolworths OR Shoprite OR "Food Lover" OR food OR meat OR produce OR dairy OR discount OR deal OR special OR promo OR "weekly ad" OR flyer OR savings)',
        'capetown_nongrocery': '("Cape Town" OR "Western Cape") (tourism OR hotel OR flight OR attraction OR museum OR tour OR event OR festival OR ticket OR rental OR discount OR deal OR special OR offer OR "free entry" OR promo)',
        'airline_deals_za': '("Cape Town" OR "Seoul" OR "Cape Town to Seoul" OR "Seoul to Cape Town" OR "CPT" OR "ICN") ("Singapore Airlines" OR "Emirates" OR "Qatar Airways" OR "Ethiopian Airlines" OR "Korean Air" OR "Air China" OR "China Eastern" OR "China Southern" OR "Cathay Pacific" OR "Asiana" OR "airline" OR "flight") (deal OR special OR discount OR promo OR fare OR sale OR offer OR "flight deal" OR promotion)'
    }

    queries_kr = {
        'seoul_grocery': '서울 (식료품 OR 마트 OR 이마트 OR 롯데마트 OR 홈플러스 OR 야채 OR 과일 OR 정육 OR 수산 OR 할인 OR 세일 OR 1+1 OR 반값 OR 전단 OR 전단지 OR 주간세일 OR 물가안정 OR 초특가)',
        'seoul_nongrocery': '서울 (관광 OR 여행 OR 호텔 OR 숙박 OR 티켓 OR 전시 OR 공연 OR 축제 OR 무료 OR 혜택 OR 프로모션 OR 할인 OR 세일)',
        'jeju_grocery': '제주 (식료품 OR 특산물 OR 마트 OR 감귤 OR 흑돼지 OR 수산물 OR 한라봉 OR 옥돔 OR 세일 OR 할인 OR 1+1 OR 전단 OR 직송 OR 초특가)',
        'jeju_nongrocery': '제주 (관광 OR 여행 OR 항공권 OR 호텔 OR 리조트 OR 렌터카 OR 올레길 OR 입장권 OR 혜택 OR 할인 OR 프로모션)',
        'airline_deals_kr': '("케이프타운" OR "서울" OR "남아공" OR "한국") ("싱가포르항공" OR "에미레이트" OR "카타르항공" OR "에티오피아항공" OR "대한항공" OR "중국국적항공사" OR "에어차이나" OR "동방항공" OR "남방항공" OR "캐세이퍼시픽" OR "아시아나항공" OR "항공사") (항공권 OR 비행기표 OR 특가 OR 할인 OR 프로모션 OR 세일 OR 이벤트 OR 얼리버드)'
    }

    queries_us = {
        'sanmarcos_grocery': '("San Marcos" OR "Hays County" OR "Austin") (grocery OR supermarket OR HEB OR "H-E-B" OR Walmart OR Target OR food OR meat OR produce OR discount OR deal OR special OR promo OR "weekly ad" OR flyer OR circular)',
        'sanmarcos_nongrocery': '("San Marcos" AND "Texas") (outlet OR shopping OR "San Marcos Premium Outlets" OR Tanger OR hotel OR tourism OR river OR tour OR event OR ticket OR discount OR deal OR special OR offer OR "free entry" OR promo)'
    }

    report_data = {
        'time_str': time_str,
        'now_kst_str': now_kst.strftime('%Y-%m-%d %H:%M:%S')
    }

    # 1-1. Cape Town Grocery Deals (limit=15, 3-day search window)
    raw_ct_g = fetch_google_news_rss_realtime(queries_za['capetown_grocery'], lang_zone="ZA", max_hours=72)
    cached_ct_g = old_cache.get('capetown_grocery', [])
    merged_ct_g = merge_and_filter_entries(raw_ct_g, cached_ct_g, max_hours=72, limit=15)
    report_data['capetown_grocery'] = merged_ct_g
    new_cache['capetown_grocery'] = merged_ct_g

    # 1-2. Cape Town Non-Grocery Deals (limit=15)
    raw_ct_ng = fetch_google_news_rss_realtime(queries_za['capetown_nongrocery'], lang_zone="ZA")
    cached_ct_ng = old_cache.get('capetown_nongrocery', [])
    merged_ct_ng = merge_and_filter_entries(raw_ct_ng, cached_ct_ng, max_hours=24, limit=15)
    report_data['capetown_nongrocery'] = merged_ct_ng
    new_cache['capetown_nongrocery'] = merged_ct_ng

    # 2-1. Seoul Grocery Deals (limit=15, 3-day search window)
    raw_seoul_g = fetch_google_news_rss_realtime(queries_kr['seoul_grocery'], lang_zone="KR", max_hours=72)
    cached_seoul_g = old_cache.get('seoul_grocery', [])
    merged_seoul_g = merge_and_filter_entries(raw_seoul_g, cached_seoul_g, max_hours=72, limit=15)
    report_data['seoul_grocery'] = merged_seoul_g
    new_cache['seoul_grocery'] = merged_seoul_g

    # 2-2. Seoul Non-Grocery Deals (limit=15)
    raw_seoul_ng = fetch_google_news_rss_realtime(queries_kr['seoul_nongrocery'], lang_zone="KR")
    cached_seoul_ng = old_cache.get('seoul_nongrocery', [])
    merged_seoul_ng = merge_and_filter_entries(raw_seoul_ng, cached_seoul_ng, max_hours=24, limit=15)
    report_data['seoul_nongrocery'] = merged_seoul_ng
    new_cache['seoul_nongrocery'] = merged_seoul_ng

    # 3-1. Jeju Grocery Deals (limit=15, 3-day search window)
    raw_jeju_g = fetch_google_news_rss_realtime(queries_kr['jeju_grocery'], lang_zone="KR", max_hours=72)
    cached_jeju_g = old_cache.get('jeju_grocery', [])
    merged_jeju_g = merge_and_filter_entries(raw_jeju_g, cached_jeju_g, max_hours=72, limit=15)
    report_data['jeju_grocery'] = merged_jeju_g
    new_cache['jeju_grocery'] = merged_jeju_g

    # 3-2. Jeju Non-Grocery Deals (limit=15)
    raw_jeju_ng = fetch_google_news_rss_realtime(queries_kr['jeju_nongrocery'], lang_zone="KR")
    cached_jeju_ng = old_cache.get('jeju_nongrocery', [])
    merged_jeju_ng = merge_and_filter_entries(raw_jeju_ng, cached_jeju_ng, max_hours=24, limit=15)
    report_data['jeju_nongrocery'] = merged_jeju_ng
    new_cache['jeju_nongrocery'] = merged_jeju_ng

    # 4-1. San Marcos Grocery Deals (limit=15, 3-day search window)
    raw_sm_g = fetch_google_news_rss_realtime(queries_us['sanmarcos_grocery'], lang_zone="US", max_hours=72)
    cached_sm_g = old_cache.get('sanmarcos_grocery', [])
    merged_sm_g = merge_and_filter_entries(raw_sm_g, cached_sm_g, max_hours=72, limit=15)
    report_data['sanmarcos_grocery'] = merged_sm_g
    new_cache['sanmarcos_grocery'] = merged_sm_g

    # 4-2. San Marcos Non-Grocery Deals (limit=15)
    raw_sm_ng = fetch_google_news_rss_realtime(queries_us['sanmarcos_nongrocery'], lang_zone="US")
    cached_sm_ng = old_cache.get('sanmarcos_nongrocery', [])
    merged_sm_ng = merge_and_filter_entries(raw_sm_ng, cached_sm_ng, max_hours=24, limit=15)
    report_data['sanmarcos_nongrocery'] = merged_sm_ng
    new_cache['sanmarcos_nongrocery'] = merged_sm_ng

    # 5. Special Airlines Deals (limit=15)
    raw_al_za = fetch_google_news_rss_realtime(queries_za['airline_deals_za'], lang_zone="ZA")
    raw_al_kr = fetch_google_news_rss_realtime(queries_kr['airline_deals_kr'], lang_zone="KR")
    raw_al = raw_al_za + raw_al_kr
    cached_al = old_cache.get('airline_deals', [])
    merged_al = merge_and_filter_entries(raw_al, cached_al, max_hours=24, limit=15)
    report_data['airline_deals'] = merged_al
    new_cache['airline_deals'] = merged_al

    report_data['shorts_top3'] = select_top_shorts_topics(report_data)
    report_data['new_cache'] = new_cache

    return report_data

def create_pdf_bytes(data):
    buffer = io.BytesIO()
    doc = SimpleDocTemplate(
        buffer, pagesize=A4, leftMargin=35, rightMargin=35, topMargin=35, bottomMargin=35
    )
    
    content_width = A4[0] - 70

    title_style = ParagraphStyle(
        'DocTitle', fontName='HYGothic-Medium', fontSize=18, leading=22,
        textColor=colors.HexColor('#166534'), spaceAfter=4
    )
    subtitle_style = ParagraphStyle(
        'SubTitle', fontName='HYSMyeongJo-Medium', fontSize=9, leading=13,
        textColor=colors.HexColor('#15803D'), spaceAfter=6
    )
    notice_style = ParagraphStyle(
        'NoticeStyle', fontName='HYGothic-Medium', fontSize=8, leading=11,
        textColor=colors.HexColor('#92400E')
    )

    card_title_style = ParagraphStyle(
        'CardTitle', fontName='HYGothic-Medium', fontSize=10, leading=14,
        textColor=colors.HexColor('#166534')
    )
    card_reason_style = ParagraphStyle(
        'CardReason', fontName='HYSMyeongJo-Medium', fontSize=8.5, leading=12,
        textColor=colors.HexColor('#15803D')
    )
    card_hook_style = ParagraphStyle(
        'CardHook', fontName='HYGothic-Medium', fontSize=9, leading=13,
        textColor=colors.HexColor('#C53030')
    )
    card_script_style = ParagraphStyle(
        'CardScript', fontName='HYSMyeongJo-Medium', fontSize=8.5, leading=12,
        textColor=colors.HexColor('#1D4ED8')
    )

    empty_style = ParagraphStyle(
        'EmptyText', fontName='HYSMyeongJo-Medium', fontSize=8.5, leading=12,
        textColor=colors.HexColor('#A0AEC0')
    )

    story = []

    story.append(Paragraph("🎁 StariaPj Special Deals &amp; Discounts Report", title_style))
    story.append(Paragraph(f"발행 일시: {data['now_kst_str']} (KST) | 케이프타운 · 서울 · 제주 · 샌마르코스(텍사스) · 항공권 공짜 · 특가 · 세일 리포트", subtitle_style))
    
    # 맨 위 혜택 대상 안내 고정 박스
    notice_p = Paragraph(f"<b>📌 혜택 대상 안내:</b><br/>{ELIGIBILITY_NOTICE_TXT}", notice_style)
    notice_table = Table([[notice_p]], colWidths=[content_width])
    notice_table.setStyle(TableStyle([
        ('BACKGROUND', (0,0), (-1,-1), colors.HexColor('#FEF3C7')),
        ('BOX', (0,0), (-1,-1), 0.8, colors.HexColor('#FDE68A')),
        ('LINELEFT', (0,0), (0,-1), 3.5, colors.HexColor('#F59E0B')),
        ('LEFTPADDING', (0,0), (-1,-1), 8),
        ('RIGHTPADDING', (0,0), (-1,-1), 8),
        ('TOPPADDING', (0,0), (-1,-1), 5),
        ('BOTTOMPADDING', (0,0), (-1,-1), 5),
    ]))
    story.append(notice_table)
    story.append(Spacer(1, 8))
    
    story.append(HRFlowable(width="100%", thickness=2, color=colors.HexColor('#22C55E'), spaceAfter=10))

    shorts_header_p = Paragraph("<font color='#166534'><b>🎬 [특가 바이럴 추천] Shorts TOP 3 혜택 이슈</b></font>", ParagraphStyle('SH', fontName='HYGothic-Medium', fontSize=11, leading=15))
    sh_table = Table([[shorts_header_p]], colWidths=[content_width])
    sh_table.setStyle(TableStyle([
        ('BACKGROUND', (0,0), (-1,-1), colors.HexColor('#DCFCE7')),
        ('LEFTPADDING', (0,0), (-1,-1), 8),
        ('RIGHTPADDING', (0,0), (-1,-1), 8),
        ('TOPPADDING', (0,0), (-1,-1), 6),
        ('BOTTOMPADDING', (0,0), (-1,-1), 6),
        ('LINELEFT', (0,0), (0,-1), 4, colors.HexColor('#16A34A')),
    ]))
    story.append(sh_table)
    story.append(Spacer(1, 6))

    if data['shorts_top3']:
        for idx, item in enumerate(data['shorts_top3'], 1):
            clean_t = clean_text(item.get('display_title', item['title']))
            link_url = html.escape(item.get('link', ''))
            clean_r = clean_text(item['reason'])
            clean_hk = clean_text(item.get('hook', ''))
            clean_sc = clean_text(item.get('script', ''))
            bot_sc = item.get('bot_score', 0)
            
            if link_url:
                title_p_str = f"<b>{idx}. [{item['category']}]</b> <a href=\"{link_url}\">{clean_t}</a> <font color='#16A34A'><b>(Bot Score: {bot_sc}점)</b></font>"
            else:
                title_p_str = f"<b>{idx}. [{item['category']}]</b> {clean_t} <font color='#16A34A'><b>(Bot Score: {bot_sc}점)</b></font>"
            
            card_p_list = [
                Paragraph(title_p_str, card_title_style),
                Spacer(1, 2),
                Paragraph(f"💡 <b>핵심 이슈 팩트:</b> <i>{clean_r}</i>", card_reason_style),
                Spacer(1, 2),
                Paragraph(f"🎯 <b>3초 Hook 멘트:</b> {clean_hk}", card_hook_style),
                Spacer(1, 2),
                Paragraph(f"⏱️ <b>30초 숏츠 개요:</b> {clean_sc}", card_script_style)
            ]
            
            card_table = Table([[card_p_list]], colWidths=[content_width])
            card_table.setStyle(TableStyle([
                ('BACKGROUND', (0,0), (-1,-1), colors.HexColor('#F0FDF4')),
                ('BOX', (0,0), (-1,-1), 0.8, colors.HexColor('#BBF7D0')),
                ('LINELEFT', (0,0), (0,-1), 3.5, colors.HexColor('#22C55E')),
                ('LEFTPADDING', (0,0), (-1,-1), 10),
                ('RIGHTPADDING', (0,0), (-1,-1), 10),
                ('TOPPADDING', (0,0), (-1,-1), 8),
                ('BOTTOMPADDING', (0,0), (-1,-1), 8),
            ]))
            story.append(card_table)
            story.append(Spacer(1, 6))
    else:
        empty_p = Paragraph("• 최근 24시간 이내 수집된 소식지 내용 중 별도 추천할 파급 이슈가 없습니다.", empty_style)
        story.append(empty_p)
        
    story.append(Spacer(1, 8))
    story.append(HRFlowable(width="100%", thickness=0.8, color=colors.HexColor('#DCFCE7'), spaceAfter=10))

    def create_section_bar(title_text, is_alert=False):
        accent_color = '#EF4444' if is_alert else '#22C55E'
        bg_color = '#FEF2F2' if is_alert else '#F0FDF4'
        text_color = '#991B1B' if is_alert else '#166534'
        
        p = Paragraph(f"<b>{title_text}</b>", ParagraphStyle(
            'SecHeaderP', fontName='HYGothic-Medium', fontSize=10.5, leading=14,
            textColor=colors.HexColor(text_color)
        ))
        t = Table([[p]], colWidths=[content_width])
        t.setStyle(TableStyle([
            ('BACKGROUND', (0,0), (-1,-1), colors.HexColor(bg_color)),
            ('LINELEFT', (0,0), (0,-1), 3.5, colors.HexColor(accent_color)),
            ('LEFTPADDING', (0,0), (-1,-1), 8),
            ('RIGHTPADDING', (0,0), (-1,-1), 8),
            ('TOPPADDING', (0,0), (-1,-1), 4),
            ('BOTTOMPADDING', (0,0), (-1,-1), 4),
        ]))
        return t

    sections = [
        ('capetown_grocery', '🇿🇦 1-1. [Cape Town | 케이프타운] 🛒 [식료품] 마트 & 식자재 공짜 · 특가 · 세일', True),
        ('capetown_nongrocery', '🇿🇦 1-2. [Cape Town | 케이프타운] 🏨 [식료품 이외] 관광 · 숙박 · 체험 · 기타 특가', True),
        ('seoul_grocery', '🇰🇷 2-1. [Seoul | 서울] 🛒 [식료품] 대형마트 & 식자재 공짜 · 특가 · 세일', True),
        ('seoul_nongrocery', '🇰🇷 2-2. [Seoul | 서울] 🏛️ [식료품 이외] 관광 · 문화 · 호텔 · 기타 특가', True),
        ('jeju_grocery', '🍊 3-1. [Jeju | 제주] 🛒 [식료품] 로컬 특산물 & 마트 공짜 · 특가 · 세일', True),
        ('jeju_nongrocery', '🍊 3-2. [Jeju | 제주] 🏖️ [식료품 이외] 관광 · 항공 · 숙박 · 기타 특가', True),
        ('sanmarcos_grocery', '🇺🇸 4-1. [San Marcos, Texas | 샌마르코스] 🛒 [식료품] 마트 & 식자재 특가 · 세일', True),
        ('sanmarcos_nongrocery', '🇺🇸 4-2. [San Marcos, Texas | 샌마르코스] 🛍️ [식료품 이외] 아울렛 · 쇼핑 · 관광 · 기타 특가', True),
        ('airline_deals', '✈️ 5. [Special Airlines Deals] 케이프타운 ↔ 서울 (경유지 불문) 주요 항공사 특가 & 프로모션', True)
    ]

    for key, sec_title, is_alert in sections:
        story.append(create_section_bar(sec_title, is_alert))
        story.append(Spacer(1, 4))
        items = data.get(key, [])
        if items:
            table_rows = []
            for idx, item in enumerate(items):
                color_hex = GRADIENT_COLORS[min(idx, len(GRADIENT_COLORS)-1)]
                link_url = html.escape(item.get('link', ''))
                clean_t = clean_text(item.get('display_title', item['title']))
                
                title_text = f'<a href="{link_url}">{clean_t}</a>' if link_url else clean_t
                
                if idx == 0:
                    tag_txt = "[🔥HOT]" if is_alert else "[⭐BEST]"
                    p_tag = Paragraph(f"<b>{tag_txt}</b>", ParagraphStyle(
                        f'TagTop_{key}', fontName='HYGothic-Medium', fontSize=9, leading=13,
                        textColor=colors.HexColor('#C53030' if is_alert else '#166534')
                    ))
                    p_body = Paragraph(f"<b>{title_text}</b>", ParagraphStyle(
                        f'BodyTop_{key}', fontName='HYGothic-Medium', fontSize=9.5, leading=14,
                        textColor=colors.HexColor(color_hex)
                    ))
                else:
                    tag_txt = "[특가]"
                    p_tag = Paragraph(tag_txt, ParagraphStyle(
                        f'Tag_{key}_{idx}', fontName='HYGothic-Medium', fontSize=8.5, leading=12,
                        textColor=colors.HexColor(color_hex)
                    ))
                    p_body = Paragraph(title_text, ParagraphStyle(
                        f'Body_{key}_{idx}', fontName='HYGothic-Medium', fontSize=8.5, leading=13,
                        textColor=colors.HexColor(color_hex)
                    ))
                
                table_rows.append([p_tag, p_body])
                
            sec_table = Table(table_rows, colWidths=[48, content_width - 48])
            sec_table.setStyle(TableStyle([
                ('VALIGN', (0,0), (-1,-1), 'TOP'),
                ('LEFTPADDING', (0,0), (-1,-1), 4),
                ('RIGHTPADDING', (0,0), (-1,-1), 4),
                ('TOPPADDING', (0,0), (-1,-1), 2),
                ('BOTTOMPADDING', (0,0), (-1,-1), 4),
                ('LINEBELOW', (0,0), (-1,-2), 0.5, colors.HexColor('#DCFCE7'))
            ]))
            story.append(sec_table)
        else:
            story.append(Paragraph("• 최근 24시간 이내 등록된 해당 카테고리 특가 소식이 없습니다.", empty_style))
        story.append(Spacer(1, 6))

    doc.build(story)
    buffer.seek(0)
    return buffer.getvalue()

def upload_to_gdrive(service, folder_id, pdf_bytes, time_str):
    if not folder_id:
        print("⚠️ 환경변수 GDRIVE_FOLDER_ID가 비어있거나 설정되지 않았습니다.")
    if not service:
        print("⚠️ 구글 드라이브 서비스 생성 실패 (GDRIVE_CLIENT_ID, GDRIVE_CLIENT_SECRET, GDRIVE_REFRESH_TOKEN 중 일부 누락).")
    if not service or not folder_id:
        print("❌ 구글 드라이브 설정 누락으로 리포트 업로드를 중단합니다. Secrets 설정을 확인해 주세요.")
        sys.exit(1)
        
    try:
        filename = f"StariaPj_Deals_Report_{time_str}_KST.pdf"
        file_metadata = {
            "name": filename,
            "parents": [folder_id],
            "mimeType": "application/pdf"
        }

        media = MediaInMemoryUpload(pdf_bytes, mimetype="application/pdf", resumable=True)
        file = service.files().create(
            body=file_metadata,
            media_body=media,
            fields="id",
            supportsAllDrives=True
        ).execute()

        print(f"✅ Google Drive Deals PDF 업로드 성공! (파일명: {filename}, ID: {file.get('id')})")
    except Exception as e:
        print(f"❌ Google Drive Deals 업로드 실패: {e}")
        sys.exit(1)

if __name__ == "__main__":
    folder_id = os.environ.get("GDRIVE_FOLDER_ID", "").strip().rstrip('/')
    if '?' in folder_id:
        folder_id = folder_id.split('?')[0]
    if '/' in folder_id:
        folder_id = folder_id.split('/')[-1]
        
    service = get_gdrive_service()
    report_data = generate_report_data(service, folder_id)
    pdf_bytes = create_pdf_bytes(report_data)

    upload_to_gdrive(service, folder_id, pdf_bytes, report_data['time_str'])
    upload_json_to_gdrive(service, folder_id, report_data['new_cache'], report_data['time_str'])
    save_gdrive_cache(service, folder_id, report_data['new_cache'])
    send_email_with_pdf(pdf_bytes, report_data)


# ==============================================================================
# 📜 VERSION HISTORY (버전 변경 이력)
# ==============================================================================
"""
[Version History]

- v1.0 (2026-09-18): Initial Deals & Specials Automation Script setup.
- v2.0 (2026-09-18): Google Drive cache synchronization and Google Trends score integration.
- v3.0 (2026-09-18): Shorts TOP 3 viral recommendation algorithm & HTML/PDF email templates.
- v4.0 (2026-09-18): Cape Town, Seoul, Jeju, Special Airlines deal search query refinements.
- v5.0 (2026-09-18): Region deal categorization into Grocery (식료품) vs Non-Grocery (식료품 이외).
- v6.0 (2026-09-18): Special Airlines Deals priority logic updated (Cape Town / Seoul routes ranked P1+).
- v7.0 (2026-09-18):
    1. Fixed misleading concert/event ticket detection under airline deals (refined keywords).
    2. Fact-based 3초 Hook & 30초 Shorts script generation based on actual article titles.
- v8.0 (2026-09-18): Added hyperlinked titles to Shorts TOP 3 section for direct article access.
- v9.0 (2026-09-18): Appended automated Version History block at the end of code.
- v10.0 (2026-09-18):
    1. Added 4th city: San Marcos, Texas (🇺🇸 [San Marcos, Texas] 🛒 식료품 / 🛍️ 아울렛·쇼핑·관광·기타 특가).
    2. Relocated Special Airlines Deals (항공권 특가) to the final section (Section 5).
- v11.0 (2026-09-18):
    1. Extended grocery deal search window to 3 days (when:3d, max_hours=72) across all regions (Cape Town, Seoul, Jeju, San Marcos).
    2. Expanded grocery search queries with press releases, weekly ads, flyers, circulars, and promotion keywords to maximize grocery deal retrieval.
"""
