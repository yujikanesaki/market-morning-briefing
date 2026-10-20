#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Daily Market & Macro Briefing

完全無料構成を想定:
- GitHub Actionsで毎日実行
- Bloomberg Markets RSS / Google News Reuters RSSを取得
- 過去24時間の記事に限定
- ルールベースで重要度を採点
- deep-translatorで日本語化（失敗時は英語原文を保持）
- USD/JPY、米10年債、S&P 500、NASDAQ、日経平均、WTI、Brent、天然ガスを取得
- BESS、JEPX、EEX、LNG、石炭、再エネ、Banpu関連ニュースを優先
- HTMLメールをSMTP送信
- Teamsチャネルのメールアドレスを宛先に含めればTeamsにも配信

必要な環境変数:
  SMTP_HOST          例: smtp.gmail.com
  SMTP_PORT          例: 587
  SMTP_USER          送信用メールアドレス
  SMTP_PASSWORD      Gmailの場合はアプリパスワード
  MAIL_FROM          省略時はSMTP_USER
  MAIL_TO            カンマ区切りの送信先
  TEAMS_EMAIL        任意。Teamsチャネルのメールアドレス
  DRY_RUN            trueなら送信せず、report.htmlを保存

任意:
  REPORT_TIMEZONE    既定 Asia/Tokyo
  HOURS_BACK         既定 24
  MAX_NEWS           既定 10
"""

from __future__ import annotations

import html
import logging
import os
import re
import smtplib
import ssl
import sys
import time
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from email.message import EmailMessage
from email.utils import parsedate_to_datetime
from pathlib import Path
from typing import Iterable
from urllib.parse import urlparse
from zoneinfo import ZoneInfo

import feedparser
import requests
import yfinance as yf
from bs4 import BeautifulSoup
from deep_translator import GoogleTranslator


# -----------------------------------------------------------------------------
# 設定
# -----------------------------------------------------------------------------
RSS_FEEDS = {
    "Bloomberg": "https://www.bloomberg.com/feeds/markets/news.rss",
    "Reuters": (
        "https://news.google.com/rss/search?"
        "q=when:24h+site:reuters.com/business&ceid=US:en&hl=en-US&gl=US"
    ),
    "Energy & Power": (
        "https://news.google.com/rss/search?"
        "q=when:24h+(BESS+OR+battery+storage+OR+power+market+OR+JEPX+OR+EEX+OR+LNG+OR+coal+OR+renewables+OR+Banpu)&ceid=US:en&hl=en-US&gl=US"
    ),
}

USER_AGENT = (
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
    "AppleWebKit/537.36 Chrome/125 Safari/537.36 MarketBriefingBot/1.0"
)

TIMEZONE_NAME = os.getenv("REPORT_TIMEZONE", "Asia/Tokyo")
HOURS_BACK = int(os.getenv("HOURS_BACK", "24"))
MAX_NEWS = min(max(int(os.getenv("MAX_NEWS", "10")), 1), 10)
REQUEST_TIMEOUT = 25

# 関連性の低い記事を除外する語句
EXCLUDE_TERMS = {
    "sports", "football", "soccer", "tennis", "celebrity", "movie", "film",
    "fashion", "recipe", "travel guide", "crime", "weather forecast",
}

# 市場・マクロ関連語。該当がない記事は除外する。
MARKET_TERMS = {
    "market", "markets", "stock", "stocks", "equity", "equities", "shares",
    "bond", "bonds", "treasury", "yield", "yields", "rate", "rates",
    "interest rate", "currency", "currencies", "dollar", "yen", "euro",
    "inflation", "cpi", "pce", "gdp", "economy", "economic", "recession",
    "growth", "employment", "jobs", "payroll", "central bank", "fed",
    "federal reserve", "fomc", "boj", "bank of japan", "ecb", "boe",
    "oil", "crude", "brent", "wti", "gas", "lng", "gold", "commodity",
    "commodities", "china", "tariff", "trade", "debt", "deficit",
    "fiscal", "monetary", "forex", "fx", "usd", "jpy", "nikkei",
    "s&p", "nasdaq", "dow", "earnings", "credit", "default",
    "bess", "battery storage", "power market", "electricity", "jepx", "eex",
    "renewable", "renewables", "banpu", "coal",
}

# 重要度スコア
KEYWORD_WEIGHTS = {
    "fomc": 16, "federal reserve": 15, "fed": 12,
    "bank of japan": 16, "boj": 14,
    "ecb": 13, "bank of england": 12, "boe": 10,
    "interest rate": 12, "rate hike": 13, "rate cut": 13,
    "inflation": 12, "cpi": 12, "pce": 11,
    "payroll": 11, "employment": 9, "jobs": 7,
    "gdp": 11, "recession": 12, "economic growth": 9,
    "treasury": 10, "bond": 8, "yield": 9,
    "dollar": 9, "yen": 10, "usd/jpy": 14, "currency": 7,
    "tariff": 10, "trade war": 12, "sanction": 9,
    "china": 7, "japan": 7, "united states": 6, "euro zone": 7,
    "oil": 7, "crude": 7, "brent": 7, "wti": 7, "lng": 8,
    "debt": 8, "default": 12, "credit": 7, "banking crisis": 15,
    "stock": 6, "stocks": 6, "equity": 6, "s&p": 7, "nasdaq": 7,
    "volatility": 8, "selloff": 10, "rally": 7,
    "bess": 10, "battery storage": 10, "power market": 9, "electricity": 7,
    "jepx": 12, "eex": 10, "renewable": 7, "renewables": 7,
    "banpu": 12, "coal": 8,
}

THEME_RULES = [
    ("主要中央銀行と金利見通し", {"fed", "fomc", "boj", "ecb", "boe", "interest rate", "rate hike", "rate cut"}),
    ("インフレ・雇用・景気指標", {"inflation", "cpi", "pce", "employment", "jobs", "payroll", "gdp", "recession", "growth"}),
    ("為替市場とUSD/JPY", {"dollar", "yen", "usd/jpy", "currency", "forex", "fx"}),
    ("国債利回りと信用市場", {"treasury", "bond", "yield", "credit", "debt", "default"}),
    ("株式市場とリスク選好", {"stock", "stocks", "equity", "shares", "s&p", "nasdaq", "selloff", "rally"}),
    ("原油・エネルギー市場", {"oil", "crude", "brent", "wti", "lng", "gas"}),
    ("中国経済と世界貿易", {"china", "tariff", "trade", "trade war", "export", "import"}),
    ("地政学・制裁リスク", {"war", "geopolitical", "sanction", "conflict"}),
    ("電力・BESS・再生可能エネルギー", {"bess", "battery storage", "power market", "electricity", "jepx", "eex", "renewable", "renewables", "banpu"}),
]


@dataclass
class Article:
    source: str
    title: str
    summary: str
    link: str
    published: datetime
    score: int = 0
    matched_terms: list[str] = field(default_factory=list)
    title_ja: str = ""
    summary_ja: str = ""
    impacts: dict[str, str] = field(default_factory=dict)


# -----------------------------------------------------------------------------
# 共通関数
# -----------------------------------------------------------------------------
def env_bool(name: str, default: bool = False) -> bool:
    value = os.getenv(name)
    if value is None:
        return default
    return value.strip().lower() in {"1", "true", "yes", "on"}


def clean_text(value: str | None) -> str:
    if not value:
        return ""
    text = BeautifulSoup(value, "html.parser").get_text(" ", strip=True)
    text = html.unescape(text)
    return re.sub(r"\s+", " ", text).strip()


def parse_entry_date(entry: dict) -> datetime | None:
    for key in ("published_parsed", "updated_parsed", "created_parsed"):
        parsed = entry.get(key)
        if parsed:
            return datetime(*parsed[:6], tzinfo=timezone.utc)

    for key in ("published", "updated", "created"):
        value = entry.get(key)
        if value:
            try:
                dt = parsedate_to_datetime(value)
                if dt.tzinfo is None:
                    dt = dt.replace(tzinfo=timezone.utc)
                return dt.astimezone(timezone.utc)
            except (TypeError, ValueError, OverflowError):
                continue
    return None


def feeds_get(url: str) -> feedparser.FeedParserDict:
    response = requests.get(
        url,
        headers={"User-Agent": USER_AGENT, "Accept": "application/rss+xml, application/xml, text/xml"},
        timeout=REQUEST_TIMEOUT,
    )
    response.raise_for_status()
    return feedparser.parse(response.content)


def normalized_title(title: str) -> str:
    title = re.sub(r"\s+-\s+(Reuters|Bloomberg)$", "", title, flags=re.I)
    return re.sub(r"[^a-z0-9]+", " ", title.lower()).strip()


# -----------------------------------------------------------------------------
# RSS取得・選別
# -----------------------------------------------------------------------------
def fetch_articles(now_utc: datetime) -> list[Article]:
    cutoff = now_utc - timedelta(hours=HOURS_BACK)
    articles: list[Article] = []

    for source, url in RSS_FEEDS.items():
        try:
            feed = feeds_get(url)
            if getattr(feed, "bozo", False):
                logging.warning("RSS warning (%s): %s", source, getattr(feed, "bozo_exception", "unknown"))

            for entry in feed.entries:
                title = clean_text(entry.get("title"))
                summary = clean_text(entry.get("summary") or entry.get("description"))
                link = entry.get("link", "").strip()
                published = parse_entry_date(entry)

                # 日時が確認できない記事は「過去24時間」と断定できないため除外
                if not title or not published:
                    continue
                if not cutoff <= published <= now_utc + timedelta(minutes=10):
                    continue

                text = f"{title} {summary}".lower()
                if any(term in text for term in EXCLUDE_TERMS):
                    continue
                if not any(term in text for term in MARKET_TERMS):
                    continue

                articles.append(
                    Article(
                        source=source,
                        title=title,
                        summary=summary,
                        link=link,
                        published=published,
                    )
                )
        except Exception as exc:
            logging.exception("RSS取得失敗: %s (%s)", source, exc)

    # タイトル重複を排除
    unique: dict[str, Article] = {}
    for article in articles:
        key = normalized_title(article.title)
        if key and key not in unique:
            unique[key] = article
    return list(unique.values())


def rank_articles(articles: Iterable[Article], now_utc: datetime) -> list[Article]:
    ranked: list[Article] = []
    for article in articles:
        text = f"{article.title} {article.summary}".lower()
        matched: list[str] = []
        score = 0
        for keyword, weight in KEYWORD_WEIGHTS.items():
            if keyword in text:
                score += weight
                matched.append(keyword)

        # 新着性: 最大6点。古い記事ほど加点を減らす。
        age_hours = max((now_utc - article.published).total_seconds() / 3600, 0)
        score += max(0, 6 - int(age_hours / 4))

        # タイトル中の一致は追加加点
        title_lower = article.title.lower()
        score += sum(3 for keyword in matched if keyword in title_lower)

        article.score = score
        article.matched_terms = matched
        ranked.append(article)

    return sorted(ranked, key=lambda x: (x.score, x.published), reverse=True)[:MAX_NEWS]


# -----------------------------------------------------------------------------
# 翻訳・市場影響
# -----------------------------------------------------------------------------
def translate_ja(text: str, max_chars: int = 2500) -> str:
    text = clean_text(text)[:max_chars]
    if not text:
        return ""
    try:
        translated = GoogleTranslator(source="auto", target="ja").translate(text)
        return clean_text(translated) or text
    except Exception as exc:
        logging.warning("翻訳失敗。原文を使用します: %s", exc)
        return text


def sentence_limit(text: str, max_chars: int = 280) -> str:
    text = clean_text(text)
    if len(text) <= max_chars:
        return text
    shortened = text[:max_chars]
    cut = max(shortened.rfind("。"), shortened.rfind("."), shortened.rfind("！"), shortened.rfind("？"))
    if cut >= int(max_chars * 0.55):
        return shortened[: cut + 1]
    return shortened.rstrip() + "…"


def infer_impacts(article: Article) -> dict[str, str]:
    """見出し・RSS概要の語句だけを使う機械的な方向性評価。"""
    text = f"{article.title} {article.summary}".lower()

    hawkish = any(x in text for x in ["rate hike", "higher rates", "hawkish", "inflation rises", "inflation accelerates", "hot inflation"])
    dovish = any(x in text for x in ["rate cut", "lower rates", "dovish", "inflation cools", "inflation slows", "recession"])
    risk_off = any(x in text for x in ["selloff", "war", "conflict", "default", "crisis", "sanction", "recession", "slump"])
    risk_on = any(x in text for x in ["rally", "record high", "stimulus", "strong growth", "beats estimates"])
    oil_up = any(x in text for x in ["oil rises", "oil jumps", "crude rises", "supply cut", "supply disruption"])
    japan_hawkish = any(x in text for x in ["boj rate hike", "bank of japan rate hike", "boj hawkish", "yen intervention"])
    us_hawkish = hawkish and any(x in text for x in ["fed", "fomc", "u.s.", "us ", "united states"])
    us_dovish = dovish and any(x in text for x in ["fed", "fomc", "u.s.", "us ", "united states"])

    if risk_off:
        stocks = "弱含み。リスク回避により景気敏感株・高ベータ株に下押し圧力。"
    elif risk_on:
        stocks = "強含み。リスク選好の改善が株価を支えやすい。"
    elif hawkish:
        stocks = "上値が重くなりやすい。割引率上昇が高PER銘柄の逆風。"
    elif dovish:
        stocks = "支援材料。金利低下期待は高PER銘柄を支えやすい。"
    else:
        stocks = "方向は限定的。企業収益、政策金利、リスク選好への波及を確認。"

    if hawkish:
        rates = "金利上昇方向。短中期ゾーンを中心に利回り上昇圧力。"
        bonds = "債券価格には下押し圧力。デュレーションの長い債券ほど影響が大きい可能性。"
    elif dovish or risk_off:
        rates = "金利低下方向。利下げ観測または安全資産需要が利回りを押し下げる可能性。"
        bonds = "国債には支援材料。ただし信用不安の場合、低格付け債には逆風。"
    else:
        rates = "方向は限定的。中央銀行見通しと経済指標への影響を確認。"
        bonds = "国債は金利見通し、社債は信用スプレッドへの影響を確認。"

    if japan_hawkish:
        fx = "円高要因。日米金利差の縮小が意識されやすい。"
        usdjpy = "低下（ドル安・円高）方向。BOJの引き締め観測が円を支える可能性。"
    elif us_hawkish:
        fx = "ドル高要因。米金利上昇がドルを支えやすい。"
        usdjpy = "上昇（ドル高・円安）方向。米金利上昇による日米金利差拡大が主因。"
    elif us_dovish:
        fx = "ドル安要因。米金利低下がドルの上値を抑えやすい。"
        usdjpy = "低下（ドル安・円高）方向。米利下げ観測が強まる場合に影響。"
    elif risk_off:
        fx = "安全通貨が選好されやすい一方、ドルと円のどちらが優位かは米金利次第。"
        usdjpy = "方向は不安定。リスク回避の円買いと安全資産としてのドル買いが競合。"
    elif oil_up:
        fx = "資源国通貨を支えやすく、エネルギー輸入国通貨には逆風。"
        usdjpy = "上昇（ドル高・円安）要因。原油高による日本の輸入負担増が円の逆風。"
    else:
        fx = "方向は限定的。米金利、リスク選好、各国金融政策との組み合わせを確認。"
        usdjpy = "中立。米国金利とBOJ見通しへの波及が生じる場合に方向感が強まる。"

    return {"株式": stocks, "金利": rates, "債券": bonds, "為替": fx, "USD/JPY": usdjpy}


def enrich_articles(articles: list[Article]) -> None:
    for index, article in enumerate(articles):
        logging.info("翻訳中 %d/%d: %s", index + 1, len(articles), article.title)
        article.title_ja = sentence_limit(translate_ja(article.title), 160)
        base_summary = article.summary or article.title
        article.summary_ja = sentence_limit(translate_ja(base_summary), 320)
        article.impacts = infer_impacts(article)
        time.sleep(0.25)


# -----------------------------------------------------------------------------
# 市場データ（Yahoo Finance。無料・認証不要だが、配信遅延や欠損の可能性あり）
# -----------------------------------------------------------------------------
MARKET_TICKERS = {
    "USD/JPY": ("JPY=X", "円", 3, 1.0),
    "米国10年債利回り": ("^TNX", "%", 3, 0.1),  # Yahooの^TNX表示値を10分の1
    "S&P 500": ("^GSPC", "pt", 2, 1.0),
    "NASDAQ総合": ("^IXIC", "pt", 2, 1.0),
    "日経平均": ("^N225", "円", 2, 1.0),
    "WTI原油先物": ("CL=F", "USD/bbl", 2, 1.0),
    "Brent原油先物": ("BZ=F", "USD/bbl", 2, 1.0),
    "Henry Hub天然ガス先物": ("NG=F", "USD/MMBtu", 3, 1.0),
}


def fetch_market_snapshot() -> list[dict[str, object]]:
    """直近終値と前日比を取得。値が取れない銘柄はスキップする。"""
    rows: list[dict[str, object]] = []
    tickers = " ".join(spec[0] for spec in MARKET_TICKERS.values())
    try:
        data = yf.download(
            tickers=tickers,
            period="5d",
            interval="1d",
            group_by="ticker",
            auto_adjust=False,
            progress=False,
            threads=True,
        )
    except Exception as exc:
        logging.warning("市場データ一括取得失敗: %s", exc)
        return rows

    for name, (ticker, unit, decimals, multiplier) in MARKET_TICKERS.items():
        try:
            if len(MARKET_TICKERS) == 1:
                series = data["Close"].dropna()
            else:
                series = data[ticker]["Close"].dropna()
            if series.empty:
                continue
            latest = float(series.iloc[-1]) * multiplier
            previous = float(series.iloc[-2]) * multiplier if len(series) >= 2 else None
            change = latest - previous if previous is not None else None
            change_pct = (change / previous * 100) if previous not in (None, 0) else None
            rows.append({
                "name": name,
                "ticker": ticker,
                "value": latest,
                "unit": unit,
                "decimals": decimals,
                "change": change,
                "change_pct": change_pct,
            })
        except Exception as exc:
            logging.warning("市場データ取得失敗 %s (%s): %s", name, ticker, exc)
    return rows


def market_snapshot_html(rows: list[dict[str, object]]) -> str:
    if not rows:
        return "<p>市場データを取得できませんでした。</p>"
    body = []
    for row in rows:
        d = int(row["decimals"])
        value = f'{float(row["value"]):,.{d}f}'
        if row["change"] is None:
            change_text = "N/A"
        else:
            sign = "+" if float(row["change"]) >= 0 else ""
            change_text = f'{sign}{float(row["change"]):,.{d}f} ({sign}{float(row["change_pct"]):.2f}%)'
        body.append(
            "<tr>"
            f'<td>{html.escape(str(row["name"]))}</td>'
            f'<td>{value} {html.escape(str(row["unit"]))}</td>'
            f'<td>{change_text}</td>'
            f'<td>{html.escape(str(row["ticker"]))}</td>'
            "</tr>"
        )
    return (
        '<table class="market"><thead><tr><th>指標</th><th>直近値</th>'
        '<th>前日比</th><th>Yahoo Finance</th></tr></thead><tbody>'
        + "".join(body) + "</tbody></table>"
    )


# -----------------------------------------------------------------------------
# レポート生成
# -----------------------------------------------------------------------------
def select_themes(articles: list[Article]) -> list[tuple[str, str]]:
    scores: list[tuple[int, str, list[Article]]] = []
    for theme, terms in THEME_RULES:
        matched_articles = []
        score = 0
        for article in articles:
            text = f"{article.title} {article.summary}".lower()
            hits = sum(1 for term in terms if term in text)
            if hits:
                matched_articles.append(article)
                score += hits * 3 + article.score
        if matched_articles:
            scores.append((score, theme, matched_articles))

    selected = sorted(scores, reverse=True)[:3]
    output: list[tuple[str, str]] = []
    for _, theme, matched_articles in selected:
        titles = "、".join(a.title_ja for a in matched_articles[:2])
        output.append((theme, sentence_limit(titles, 220)))

    while len(output) < 3:
        article = articles[len(output)] if len(articles) > len(output) else None
        if not article:
            break
        output.append(("市場注目ニュース", article.title_ja))
    return output


def executive_summary(articles: list[Article], themes: list[tuple[str, str]]) -> list[str]:
    lines = [f"過去{HOURS_BACK}時間の市場・マクロ関連ニュースから、重要度上位{len(articles)}件を抽出しました。"]
    for theme, _ in themes[:3]:
        lines.append(f"注目テーマは「{theme}」です。")
    if articles:
        usd_impacts = [a.impacts.get("USD/JPY", "") for a in articles[:3]]
        if any("上昇" in x for x in usd_impacts) and any("低下" in x for x in usd_impacts):
            lines.append("USD/JPYは円安要因と円高要因が交錯しており、米金利とBOJ見通しの確認が重要です。")
        elif any("上昇" in x for x in usd_impacts):
            lines.append("USD/JPYは、主要ニュースの機械判定ではドル高・円安方向の材料が優勢です。")
        elif any("低下" in x for x in usd_impacts):
            lines.append("USD/JPYは、主要ニュースの機械判定ではドル安・円高方向の材料が優勢です。")
        else:
            lines.append("USD/JPYは、米金利とリスク選好の変化を確認する必要があります。")
    return lines[:5]


def safe_url(url: str) -> str:
    try:
        parsed = urlparse(url)
        if parsed.scheme in {"http", "https"}:
            return html.escape(url, quote=True)
    except Exception:
        pass
    return ""


def build_html(articles: list[Article], market_rows: list[dict[str, object]], report_time: datetime) -> str:
    themes = select_themes(articles)
    exec_lines = executive_summary(articles, themes)
    snapshot_html = market_snapshot_html(market_rows)

    theme_html = "".join(
        f"<li><strong>{html.escape(name)}</strong><br>{html.escape(detail)}</li>"
        for name, detail in themes
    ) or "<li>対象記事が不足しているため、3テーマを抽出できませんでした。</li>"

    news_blocks = []
    for i, article in enumerate(articles, 1):
        published_local = article.published.astimezone(ZoneInfo(TIMEZONE_NAME)).strftime("%Y/%m/%d %H:%M")
        link = safe_url(article.link)
        title_display = html.escape(article.title_ja or article.title)
        if link:
            title_html = f'<a href="{link}">{title_display}</a>'
        else:
            title_html = title_display

        impacts_html = "".join(
            f"<li><strong>{html.escape(asset)}:</strong> {html.escape(view)}</li>"
            for asset, view in article.impacts.items()
        )
        news_blocks.append(f"""
        <div class="news">
          <h3>{i}. {title_html}</h3>
          <p class="meta">出所: {html.escape(article.source)} | 公開: {published_local} JST | 重要度スコア: {article.score}</p>
          <p>{html.escape(article.summary_ja or article.summary or 'RSSに概要がありません。')}</p>
          <ul>{impacts_html}</ul>
        </div>
        """)

    if not news_blocks:
        news_blocks.append("<p>過去24時間で、公開日時を確認できる対象記事を取得できませんでした。</p>")

    insight_items = [
        "金利に関する記事では、政策金利の方向だけでなく、2年債・10年債のどの年限に影響するかを確認してください。",
        "株式では、高PER銘柄、金融、不動産、景気敏感株への影響を分けて確認してください。",
        "USD/JPYでは、米金利、BOJ見通し、リスク回避、原油価格の4要因を分けて判断してください。",
        "本レポートの市場影響は、RSSの見出し・概要を基にしたルールベースの機械判定です。売買判断には原記事と市場価格を確認してください。",
    ]

    return f"""<!doctype html>
<html lang="ja">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Daily Market & Macro Briefing</title>
<style>
body {{ font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif; color:#17202a; line-height:1.55; max-width:900px; margin:auto; padding:24px; }}
h1 {{ color:#123a63; border-bottom:3px solid #2b78c5; padding-bottom:10px; }}
h2 {{ color:#123a63; margin-top:32px; }}
h3 {{ margin-bottom:4px; }}
a {{ color:#1261a0; }}
.meta {{ color:#68737d; font-size:12px; }}
.news {{ border:1px solid #dfe6ec; border-radius:8px; padding:16px; margin:14px 0; background:#fff; }}
.notice {{ background:#fff8dd; border-left:4px solid #d5a400; padding:12px; }}
.market {{ border-collapse:collapse; width:100%; margin:12px 0; }}
.market th, .market td {{ border:1px solid #dfe6ec; padding:8px; text-align:right; }}
.market th:first-child, .market td:first-child {{ text-align:left; }}
.footer {{ color:#68737d; font-size:12px; margin-top:32px; border-top:1px solid #dfe6ec; padding-top:12px; }}
</style>
</head>
<body>
<h1>Daily Market &amp; Macro Briefing</h1>
<p>作成日時: {report_time.strftime('%Y/%m/%d %H:%M')} JST<br>対象期間: 過去{HOURS_BACK}時間</p>

<h2>0. 主要市場データ</h2>
{snapshot_html}
<p class="meta">直近取引日の終値ベース。リアルタイム値ではありません。</p>

<h2>1. 本日の注目テーマ（3件）</h2>
<ol>{theme_html}</ol>

<h2>2. 重要ニュース一覧</h2>
{''.join(news_blocks)}

<h2>3. 投資家向けインサイト</h2>
<ul>{''.join(f'<li>{html.escape(x)}</li>' for x in insight_items)}</ul>

<h2>4. エグゼクティブサマリー</h2>
<ol>{''.join(f'<li>{html.escape(x)}</li>' for x in exec_lines)}</ol>

<p class="notice"><strong>注意:</strong> 翻訳と市場影響は自動生成です。特にGoogle News経由のReutersリンク、翻訳結果、方向性評価は、原記事で確認してください。</p>
<p class="footer">Sources: Bloomberg Markets RSS / Google News RSS / Yahoo Finance</p>
</body>
</html>"""


def build_plain_text(articles: list[Article], report_time: datetime) -> str:
    themes = select_themes(articles)
    lines = [
        "Daily Market & Macro Briefing",
        f"作成日時: {report_time.strftime('%Y/%m/%d %H:%M')} JST",
        f"対象期間: 過去{HOURS_BACK}時間",
        "",
        "1. 本日の注目テーマ",
    ]
    lines.extend(f"- {name}: {detail}" for name, detail in themes)
    lines.extend(["", "2. 重要ニュース一覧"])
    for i, a in enumerate(articles, 1):
        lines.extend([
            f"{i}. {a.title_ja or a.title}",
            f"   出所: {a.source}",
            f"   {a.summary_ja or a.summary}",
            f"   USD/JPY: {a.impacts.get('USD/JPY', '')}",
            f"   {a.link}",
        ])
    lines.extend(["", "3. 投資家向けインサイト", "- 市場影響はRSS見出し・概要を基にした機械判定です。", "", "4. エグゼクティブサマリー"])
    lines.extend(f"- {x}" for x in executive_summary(articles, themes))
    return "\n".join(lines)


# -----------------------------------------------------------------------------
# メール
# -----------------------------------------------------------------------------
def recipients_from_env() -> list[str]:
    raw = os.getenv("MAIL_TO", "")
    recipients = [x.strip() for x in raw.split(",") if x.strip()]
    teams_email = os.getenv("TEAMS_EMAIL", "").strip()
    if teams_email:
        recipients.append(teams_email)
    # 順序を保って重複排除
    return list(dict.fromkeys(recipients))


def send_email(subject: str, html_body: str, plain_body: str) -> None:
    smtp_host = os.getenv("SMTP_HOST", "smtp.gmail.com").strip()
    smtp_port = int(os.getenv("SMTP_PORT", "587"))
    smtp_user = os.getenv("SMTP_USER", "").strip()
    smtp_password = os.getenv("SMTP_PASSWORD", "")
    mail_from = os.getenv("MAIL_FROM", smtp_user).strip()
    recipients = recipients_from_env()

    missing = [name for name, value in {
        "SMTP_USER": smtp_user,
        "SMTP_PASSWORD": smtp_password,
        "MAIL_FROM": mail_from,
        "MAIL_TO または TEAMS_EMAIL": recipients,
    }.items() if not value]
    if missing:
        raise RuntimeError("メール設定が不足しています: " + ", ".join(missing))

    message = EmailMessage()
    message["Subject"] = subject
    message["From"] = mail_from
    message["To"] = ", ".join(recipients)
    message.set_content(plain_body)
    message.add_alternative(html_body, subtype="html")

    context = ssl.create_default_context()
    if smtp_port == 465:
        with smtplib.SMTP_SSL(smtp_host, smtp_port, context=context, timeout=30) as smtp:
            smtp.login(smtp_user, smtp_password)
            smtp.send_message(message)
    else:
        with smtplib.SMTP(smtp_host, smtp_port, timeout=30) as smtp:
            smtp.ehlo()
            smtp.starttls(context=context)
            smtp.ehlo()
            smtp.login(smtp_user, smtp_password)
            smtp.send_message(message)


# -----------------------------------------------------------------------------
# メイン
# -----------------------------------------------------------------------------
def main() -> int:
    logging.basicConfig(
        level=os.getenv("LOG_LEVEL", "INFO").upper(),
        format="%(asctime)s %(levelname)s %(message)s",
    )

    tz = ZoneInfo(TIMEZONE_NAME)
    now_utc = datetime.now(timezone.utc)
    report_time = now_utc.astimezone(tz)

    logging.info("RSS取得開始。基準時刻=%s", report_time.isoformat())
    articles = fetch_articles(now_utc)
    logging.info("条件適合記事=%d", len(articles))

    selected = rank_articles(articles, now_utc)
    enrich_articles(selected)

    logging.info("主要市場データ取得開始")
    market_rows = fetch_market_snapshot()
    logging.info("取得した市場指標=%d", len(market_rows))

    html_report = build_html(selected, market_rows, report_time)
    plain_report = build_plain_text(selected, report_time)

    output = Path(os.getenv("REPORT_OUTPUT", "report.html"))
    output.write_text(html_report, encoding="utf-8")
    logging.info("レポート保存: %s", output.resolve())

    subject = f"Daily Market & Macro Briefing - {report_time:%Y/%m/%d}"

    if env_bool("DRY_RUN", False):
        logging.info("DRY_RUN=true のため、メール送信を省略しました。")
        print(plain_report)
        return 0

    send_email(subject, html_report, plain_report)
    logging.info("メール送信完了: %s", ", ".join(recipients_from_env()))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        raise SystemExit(130)
    except Exception as exc:
        logging.exception("処理に失敗しました: %s", exc)
        raise SystemExit(1)
