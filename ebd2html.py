#! /usr/bin/env python3
#
# ebd2html - EBDumpの出力からEBStudioへの入力HTMLファイルを再構成する試み
#       Written by Junn Ohta (ohta@sdg.mdd.ricoh.co.jp), Public Domain.
#

import sys
import os
import re
import configparser
import string
import pandas as pd
from pathlib import Path
from datetime import datetime

PROGNAME = "ebd2html-py"
__VERSION__ = "0.1.0"
__DATE__ = '2020-12-13'

LOG_FILE = "ebd2html.log" # ログファイル
MAX_WORD = 256            # 単語の最大長

# 2バイト記号→1バイト記号変換表(0x8140～0x8197)
ZEN2HAN = {
    '': ' ', '　': ' ', '，': ',',  '．': '.', '：': ':', '；': ';',
    '？': '?',  '！': '!', '＾': '^', '〜': '~', '￣': '~', '＿': '_',
    '／': '/',  '＼': '\\', '～': '~', '‖': '|', '｜': '|',
    '＇': "'", '‘': "'", '’': "'", '＂': '"', '“': '"', '”': '"',
    '（': '(', '）': ')', '［': '[', '］': ']',
    '「': '[', '」': ']', '｛': '{', '｝': '}',
    '＋': '+', '－': '-',  '＝': '=', '＜': '<',  '＞': '>',
    '￥': '\\', '＄': '$', '％': '%',
    '＃': '#', '＆': '&', '＊': '*', '＠': '@'
}

def tohan(s):
    '''2バイト英数字を1バイト英数字に変換する'''
    global ZEN2HAN
    result = ""
    for c in s:
        if ord('Ａ') <= ord(c) <= ord('Ｚ'):
            result += chr(ord(c) - ord('Ａ') + ord('A'))
        elif ord('ａ') <= ord(c) <= ord('ｚ'):
            result += chr(ord(c) - ord('ａ') + ord('a'))
        elif ord('０') <= ord(c) <= ord('９'):
            result += chr(ord(c) - ord('０') + ord('0'))
        else:
            result += ZEN2HAN.get(c, c)
    return result

def iskanastr(s):
    '''文字列がひらがな/カタカナ/長音のみで構成されているか?'''
    for c in s:
        if not (ord('ぁ') <= ord(c) <= ord('ん') or
                ord('ァ') <= ord(c) <= ord('ン') or c == 'ー'):
            return False
    return True

def write_log(s):
    '''メッセージをログファイルに書く'''
    with open(LOG_FILE, "a") as f:
        f.write(s)

def message(s):
    print(s, end='', flush=True)
    write_log(s)

# -------------------- メイン --------------------

MAX_HLINE = 256 # HTMLファイルのおよその最大長

FKINDEX_FILE = "fkindex.txt" # かなインデックスダンプデータ
FKTITLE_FILE = "fktitle.txt" # かな見出しダンプデータ

FHINDEX_FILE = "fhindex.txt" # 表記インデックスダンプデータ
FHTITLE_FILE = "fhtitle.txt" # 表記見出しダンプデータ

FAINDEX_FILE = "faindex.txt" # 英字インデックスダンプデータ
FATITLE_FILE = "fatitle.txt" # 英字見出しダンプデータ

ZGAIJI_FILE = "zgaiji.txt" # 全角16ドット外字ダンプデータ
HGAIJI_FILE = "hgaiji.txt" # 半角16ドット外字ダンプデータ
GFONT_FILE = "Gaiji.xml" # EBStudio用外字マップファイル
GMAP_FILE = "GaijiMap.xml" # EBStudio用外字フォント
HONMON_FILE = "honmon.txt" # 本文ダンプデータ
INI_FILE = "ebd2html.ini" # ebd2html設定ファイル

base_path = None   # EBStudio基準ディレクトリ
out_path = None    # EBStudio出力ディレクトリ
auto_kana = False  # 表記INDEXからかなINDEXを生成
eb_type = 0        # 0:EPWING, 1:電子ブック
book_title = ""    # 書籍タイトル
book_type = ""     # 書籍種別
book_dir = ""      # 書籍ディレクトリ名
html_file = ""     # 生成されるHTMLファイル名
ebs_file = ""      # 生成されるEBSファイル名

fktitle_data = None # かな見出しデータ
fhtitle_data = None # 表記見出しデータ
fatitle_data = None # 英字見出しデータ
fkindex_data = None # かなインデックスデータ
fhindex_data = None # 表記インデックスデータ
faindex_data = None # 英字インデックスデータ

gen_kana = False       # かなインデックスを作る
gen_hyoki = False      # 表記インデックスを作る
gen_alpha = False      # 英字インデックスを作る
have_auto_kana = False # auto_kana検索語がある

class Gaiji:
    FONTSET_START_RE = re.compile(
        r'^<fontSet\s.*start="([0-9A-Fa-f]{2})([0-9A-Fa-f]{2})"');
    GAIJI_UNICODE_FIRST = 0xe000
    
    def __init__(self, ebwin_map=None):
        self.zg_start_unicode = 0 # 全角外字開始Unicodeコード
        self.hg_start_unicode = 0 # 半角外字開始Unicodeコード

        self.zgaiji2uni = {}
        self.hgaiji2uni = {}
        self.zgaiji_data = []
        self.hgaiji_data = []
        if ebwin_map:
            with open(ebwin_map, 'r', encoding='cp932') as f:
                for line in f:
                    line = line.rstrip('\r\n')
                    if line == "" or line[0] == '#':
                        continue
                    s = re.split("[ \t]+", line)
                    if len(s) < 2:
                        continue
                    if s[1] == "-" or ',' in s[1]:
                        continue
                    ebcode = s[0].lower()
                    type_ = ebcode[0]
                    ebcode = int(ebcode[1:], 16)
                    unicode = int(s[1][1:], 16)
                    if unicode == 0x20:
                        continue
                    if type_ == "z":
                        self.zgaiji2uni[ebcode] = unicode
                    else:
                        self.hgaiji2uni[ebcode] = unicode

    def to_unicode(self, ebcode, halfwidth):
        if halfwidth:
            return self.hgaiji2uni.get(ebcode, 0)
        return self.zgaiji2uni.get(ebcode, 0)
        
    def load(self, zgaiji, hgaiji):
        first = True
        self.hg_start_unicode = self.GAIJI_UNICODE_FIRST
        with open(hgaiji, "r", encoding='cp932') as fp:
            unicode_ = self.hg_start_unicode
            ebhigh = 0xa1
            eblow = 0x21
            for line in fp:
                line = line.rstrip('\r\n')
                if line == '' or line[0] in (' ', '#', '.'):
                    self.hgaiji_data.append(line)
                    continue

                m = self.FONTSET_START_RE.match(line)
                if m:
                    ebhigh = int(m.group(1), 16)
                    eblow = int(m.group(2), 16)
                if not line.startswith("<fontData"):
                    continue
                
                ebcode = ebhigh*256 + eblow
                if first:
                    self.hgaiji_data.append(
                        '<fontSet size="8X16" start="{:04X}">'.format(ebcode))
                    first = False
                else:
                    self.hgaiji_data.append("</fontData>")
                if ebcode not in self.hgaiji2uni:
                    self.hgaiji2uni[ebcode] = unicode_
                    unicode_ += 1
                u = self.hgaiji2uni[ebcode]
                self.hgaiji_data.append(
                    '<fontData ebcode="{:04X}" unicode="#x{:04X}">'.format(
                        ebcode, u))
            
                if eblow < 0x7e:
                    eblow += 1
                else:
                    eblow = 0x21
                    ebhigh += 1
            if not first:
                self.hgaiji_data.append("</fontData>")
                self.hgaiji_data.append("</fontSet>")
        
        first = True
        self.zg_start_unicode = unicode_
        zg_start_ebhigh = ebhigh + 1
        with open(ZGAIJI_FILE, "r", encoding='cp932') as fp:
            ebhigh = zg_start_ebhigh
            eblow = 0x21
            for line in fp:
                if len(line) == 0 or line[0] in (" ", "#", "."):
                    self.zgaiji_data.append(line)
                    continue
                
                m = self.FONTSET_START_RE.match(line)
                if m:
                    ebhigh = int(m.group(1), 16)
                    eblow = int(m.group(2), 16)
                if not line.startswith("<fontData"):
                    continue
                
                ebcode = ebhigh*256 + eblow
                if first:
                    self.zgaiji_data.append(
                        '<fontSet size="16X16" start="{:04X}">'.format(ebcode))
                    first = False
                else:
                    self.zgaiji_data.append("</fontData>")
                if ebcode not in self.zgaiji2uni:
                    self.zgaiji2uni[ebcode] = unicode_
                    unicode_ += 1
                u = self.zgaiji2uni[ebcode]
                self.zgaiji_data.append(
                    '<fontData ebcode="{:04X}" unicode="#x{:04X}">'.format(
                        ebcode, u))
                if eblow < 0x7e:
                    eblow += 1
                else:
                    eblow = 0x21
                    ebhigh += 1
            if not first:
                self.zgaiji_data.append("</fontData>")
                self.zgaiji_data.append("</fontSet>")
    
    def create_file(self, gaiji_file, gaijimap_file):
        with open(gaiji_file, "w", encoding='cp932') as ffp:
            ffp.write('<?xml version="1.0" encoding="Shift_JIS"?>\n')
            ffp.write('<gaijiData xml:space="preserve">\n')
            ffp.write('\n'.join(self.hgaiji_data))
            ffp.write('\n')
            ffp.write('\n'.join(self.zgaiji_data))
            ffp.write("\n</gaijiData>\n")
        
        with open(gaijimap_file, "w", encoding="cp932") as mfp:
            mfp.write('<?xml version="1.0" encoding="Shift_JIS"?>\n')
            mfp.write("<gaijiSet>\n")
            for ebcode in sorted(self.hgaiji2uni.keys()):
                mfp.write(
                    '<gaijiMap unicode="#x{:04X}" ebcode="{:04X}"/>\n'.format(
                        self.hgaiji2uni[ebcode], ebcode))
            for ebcode in sorted(self.zgaiji2uni.keys()):
                mfp.write(
                    '<gaijiMap unicode="#x{:04X}" ebcode="{:04X}"/>\n'.format(
                        self.zgaiji2uni[ebcode], ebcode))
            mfp.write("</gaijiSet>\n")

gaiji = None
def generate_gaiji_file():
    '''外字ダンプファイルからGaiji.xmlとGaijiMap.xmlを作る'''
    global gaiji

    message("外字ファイルを生成しています... ")
    mapfile = base_path / (book_dir + ".map")
    if mapfile.exists():
        message("mapfile 読み込み... ")
        gaiji = Gaiji(mapfile.resolve())
    else:
        gaiji = Gaiji()
    gaiji.load(ZGAIJI_FILE, HGAIJI_FILE)
    gaiji.create_file(base_path / GFONT_FILE, base_path / GMAP_FILE)
    message("終了しました\n")

def gstr(s, halfwidth):
    '''文字列を外字のUnicode表記に変換する'''
    global gaiji
    
    if s[0] == '<':
        s = s[1:]
    high = int(s[:2], 16)
    low = int(s[2:4], 16)
    if high < 0xa1:
        return "&#x{:02X};&#x{:02X};".format(high, low)

    ebcode = high * 0x100 + low
    code = gaiji.to_unicode(ebcode, halfwidth)
    if code == 0:
        raise Exception()
    if 0xe000 <= code <= 0xf8ff:
        return "&#x{:04X};".format(code)
    return chr(code)

def conv_title(s):
    '''見出し文字列を変換する'''
    halfwidth = False
    result = ""
    while len(s):
        if s[0] == '<':
            if s[1] >= 'A':
                # 外字
                result += gstr(s, halfwidth)
            elif s[1:].startswith("1F04"):
                # 半角開始
                halfwidth = True
            elif s[1:].startswith("1F05"):
                # 半角終了
                halfwidth = False
            else:
                # その他のタグはとりあえず無視
                pass
            s = s[6:]
            continue
        
        if halfwidth:
            n = tohan(s[0])
            if n == '<':
                result += "&lt;"
            elif n == '>':
                result += "&gt;"
            elif n == '&':
                result += "&amp;"
            elif n == '"':
                result += "&quot;"
            elif n == "'":
                result += "&apos;"
            else:
                result += n
        else:
            result += s[0]
        s = s[1:]
    return result

def convert_index_data(ifp):
    '''インデックスデータを変換する'''
    firsterr = True
    complex = False
    INDEX_RE = re.compile(r"\[(\d+)\]\t" +
                          r"\[([\da-fA-F]+):([\da-fA-F]+)\]" +
                          r"\[([\da-fA-F]+):([\da-fA-F]+)\]")
    for line in ifp:
        if not line.startswith("ID="):
            continue
        if line[3:].startswith("C0"):
            break
        if line[3:].startswith("D0"):
            complex = True
            break
    else:
        raise Exception()
    
    result = []
    for line in ifp:
        line = line.rstrip("\r\n")
        if line == '' or line.startswith("block#") or line.startswith("ID="):
            continue
        if complex:
            if line.starswith("80:"):
                continue
            if line.startswith("C0:") or line.startswith("00:"):
                line = line[3:]
        if line[0] == '[':
            # 索引語が空っぽ。外字か?
            # (広辞苑第五版の表記インデックス末尾にある)
            continue

        m = INDEX_RE.search(line)
        if m is None:
            if firsterr:
                write_log("\n")
                firsterr = False
            write_log("不正なインデックス行: " + line)
            continue
        
        len = int(m.group(1))
        dblk = int(m.group(2), 16)
        dpos = int(m.group(3), 16)
        tblk = int(m.group(4), 16)
        tpos = int(m.group(5), 16)
        if dpos == 0x0800:
            dpos = 0
            dblk += 1
        if tpos == 0x0800:
            tpos = 0;
            tblk += 1
        line = line[:line.index('[')]
        result.append({
            "dblk": dblk, "dpos": dpos,
            "tblk": tblk, "tpos": tpos,
            "text": conv_title(line)
        })
    return pd.DataFrame(result)

def convert_title_data(fp):
    '''見出しデータを変換する'''
    firsterr = True
    result = {}
    TITLE_RE = re.compile(r'\[([\da-fA-F]+):( *[\da-fA-F]+)\]')
    
    for line in fp:
        line = line.rstrip('\r\n')
        if line == '' or line.startswith('[ID='):
            continue
        m = TITLE_RE.search(line)
        if m is None:
            if firsterr:
                write_log("\n")
                firsterr = False
            write_log("不正な見出し行: " + line + "\n")
            continue
        tblk = int(m.group(1), 16)
        tpos = int(m.group(2), 16)
        
        line = line[line.index(']')+1:]
        if (line == '' or
            line.startswith("<1F02>") or line.startswith("<1F03>")):
            continue
        if line.endswith("<1F0A>"):
            line = line[:-6]
        pos = tblk * 2048 + tpos
        result[pos] = conv_title(line)
    return result

def generate_work_file():
    '''インデックスおよび見出しの作業データファイルを生成する'''
    global fkindex_data, fhindex_data, faindex_data
    global fktitle_data, fhtitle_data, fatitle_data

    if Path(FKINDEX_FILE).exists():
        with open(FKINDEX_FILE, "r", encoding='cp932') as ifp:
            message("かなインデックスデータを変換しています...")
            fkindex_data = convert_index_data(ifp)
            message(" 終了しました\n")

        message("かなインデックスデータをソートしています...")
        fkindex_data.sort_values(
            by=["dblk", "dpos", "tblk", "tpos", "text"],
            inplace=True, ignore_index=True)
        message(" 終了しました\n")

    if Path(FKTITLE_FILE).exists():
        with open(FKTITLE_FILE, "r", encoding='cp932') as fp:
            message("かな見出しデータを生成しています...")
            fktitle_data = convert_title_data(fp)
            message(" 終了しました\n")

    if Path(FHINDEX_FILE).exists():
        with open(FHINDEX_FILE, "r", encoding='cp932') as ifp:
            message("表記インデックスデータを変換しています...")
            fhindex_data = convert_index_data(ifp)
            message(" 終了しました\n")
        
        message("表記インデックスデータをソートしています...");
        fhindex_data.sort_values(
            by=["dblk", "dpos", "tblk", "tpos", "text"],
            inplace=True, ignore_index=True)
        message(" 終了しました\n")

    if Path(FHTITLE_FILE).exists():
        with open(FHTITLE_FILE, "r", encoding='cp932') as fp:
            message("表記見出しデータを生成しています...")
            fhtitle_data = convert_title_data(fp)
            message(" 終了しました\n");

    if Path(FAINDEX_FILE).exists():
        with open(FAINDEX_FILE, "r", encoding='cp932') as ifp:
            message("英字インデックスデータを変換しています...")
            faindex_data = convert_index_data(ifp)
            message(" 終了しました\n")

        message("英字インデックスデータをソートしています...")
        faindex_data.sort_values(
            by=["dblk", "dpos", "tblk", "tpos", "text"],
            inplace=True, ignore_index=True)
        message(" 終了しました\n")

    if Path(FATITLE_FILE).exists():
        with open(FATITLE_FILE, "r", encoding='cp932') as fp:
            message("英字見出しデータを生成しています...")
            fatitle_data = convert_title_data(fp)
            message(" 終了しました\n");

def html_newfile():
    '''HTMLファイルを新規作成する'''

    filename = base_path / html_file
    fp = open(filename, 'w', encoding='utf-8')
    fp.write("""<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=utf-8">
<meta name="GENERATOR" content="{} {} {}">
<title>Dictionary</title>
</head>
<body>
<dl>
""".format(PROGNAME, __VERSION__, __DATE__))
    return fp

def html_close(fp):
    '''HTMLファイルをクローズする'''
    fp.write("</dl>\n")
    fp.write("</body>\n")
    fp.write("</html>\n")
    fp.close()

class IndexAndTitle:
    def __init__(self, index, title):
        self.pos = 0
        self.ind_dblk = index.dblk.values
        self.ind_dpos = index.dpos.values
        self.ind_tblk = index.tblk.values
        self.ind_tpos = index.tpos.values
        self.ind_text = index.text.values
        self.title = title

    def read_data(self):
        '''インデックスと見出しを1件読む'''
        pos = self.pos
        if pos >= len(self.ind_text):
            return None
        ip = {
            'dblk': self.ind_dblk[pos],
            'dpos': self.ind_dpos[pos],
            'tblk': self.ind_tblk[pos],
            'tpos': self.ind_tpos[pos],
            'text': self.ind_text[pos],
            'title': "",
        }
        self.pos += 1
        if ip['dblk'] == ip['tblk'] and ip['dpos'] == ip['tpos']:
            # 見出しデータは本文の見出し行を共用する(広辞苑第五版)
            pass
        else:
            pos = ip['tblk'] * 2048 + ip['tpos']
            ip['title'] = self.title[pos]
        return ip
        
def read_honmon_data(fp):
    '''本文を1行読む'''
    line = fp.readline()
    if line == '':
        return None
    line = line.rstrip('\r\n')
    m = re.search(r"^\[([\da-fA-F]+): *([\da-fA-F]+)\](.*)$", line)
    if m is None:
        return {
            'dblk': 0,
            'dpos': 0,
            'text': ""
        }
    hp = {
        'dblk': int(m.group(1), 16),
        'dpos': int(m.group(2), 16),
        'text': m.group(3)
    }
    if hp['dpos'] == 0x800:
        hp['dpos'] = 0
        hp['dblk'] += 1
    return hp

def compare_position(ip, dp):
    '''インデックスの参照先と本文データの位置関係を比較する'''
    ipos = ip['dblk'] * 2048 + ip['dpos']
    dpos = dp['dblk'] * 2048 + dp['dpos']

    # 本文の行頭から
    #   <1F09><xxxx>
    #   <1F41><xxxx>
    #   <1F61>
    # の並びが連続していて、
    # インデックスの参照先がその直後の場合は
    # インデックスがその行頭を参照しているとみなす
    # (ジーニアス英和辞典など)
    if ipos < dpos:
        return -1
    line = dp['text']
    while len(line) and ipos > dpos:
        if line.startswith("<1F09>"):
            line = line[12:]
            dpos += 4
            continue
        if line.startswith("<1F41>"):
            line = line[12:]
            dpos += 4
            continue
        if line.startswith("<1F61>"):
            line = line[6:]
            dpos += 2
            continue
        break
    if ipos > dpos:
        return 1
    return 0

def conv_honmon(s):
    '''本文データを変換する'''
    halfwidth = False
    linetop = 0
    result = ""
    
    while len(s):
        if s[0] == "<":
            tag = s[:6]
            if tag == '<1F04>':   # 1F04: 半角開始
                halfwidth = True
                s = s[6:]
            elif tag == '<1F05>': # 1F05: 半角終了 
                halfwidth = False
                s = s[6:]
            elif tag == '<1F06>': # 1F06: 下添え字開始
                result += "<sub>"
                s = s[6:]
            elif tag == '<1F07>': # 1F07: 下添え字終了
                result += "</sub>"
                s = s[6:]
            elif tag == '<1F0A>': # 1F0A: 改行
                result += "<br />"
                s = s[6:]
            elif tag == '<1F0E>': # 1F06: 上添え字開始
                result += "<sup>"
                s = s[6:]
            elif tag == '<1F0F>': # 1F07: 上添え字終了
                result += "</sup>"
                s = s[6:]
            elif tag == '<1F10>': # 1F10: 分割禁止開始
                result += "<nobr>"
                s = s[6:]
            elif tag == '<1F11>': # 1F11: 分割禁止終了
                result += "</nobr>"
                s = s[6:]
            elif tag == '<1F14>': # 1F14 ... 1F15: 色見本
                # "[色見本]"で置き換える
                result += "[色見本]"
                s = s[s.index("<1F15>")+6:]
            elif (tag == '<1F1A>' or # 1F1A xxxx: タブ位置指定 
                  tag == '<1F1B>' or # 1F1B xxxx: 字下げ・字上がり指定 
                  tag == '<1F1C>'):  # 1F1C xxxx: センタリング指定 
                s = s[12:]
            elif tag == "<1F39>": # 1F39 ... 1F59: カラー動画表示
                # "[動画]"で置き換える
                result += "[動画]"
                s = s[s.index("<1F59>")+6:]
            elif tag == "<1F3C>": # 1F3C ... 1F5C: インライン画像参照 
                # "[図版]"で置き換える
                result += "[図版]"
                s = s[s.index("<1F5C>")+6:]
            elif tag == "<1F41>": # 1F41 xxxx: 検索キー開始 
                s = s[12:]
            elif tag == "<1F42>": # 1F42 text 1F62[xx:yy]: 別項目参照 
                s = s[6:]
                if s.startswith("→"):
                    s = s[1:]
                r = s.index("<1F62>")
                text = s[:r]
                s = s[r+6:]
                m = re.search(r'^\[([\da-fA-f]+):([\da-fA-f]+)\](.*)$', s)
                dblk = int(m.group(1), 16)
                dpos = int(m.group(2), 16)
                result += '<a href="#{:08X}{:04X}">{}</a>'.format(
                    dblk, dpos, conv_honmon(text))
                s = m.group(3)
            elif tag == "<1F44>": # 1F44 ... 1F64[xx:yy]: 図版参照
                # "[図版]"で置き換える
                result += "[図版]"
                s = s[s.index("<1F64>"):]
                s = s[s.index("]")+1:]
            elif tag == "<1F4A>": # 1F4A ... 1F6A: 音声参照 
                # "[音声]"で置き換える
                result += "[音声]"
                s = s[s.index("<1F6A>")+6:]
            elif (tag == "<1F45>" or # 1F45 ... 1F65: 図版見出し 
                  tag == "<1F4B>" or # 1F4B ... 1F6B: カラー画像データ群参照 
                  tag == "<1F4C>" or # 1F4C ... 1F6C: カラー画面データ群参照 
                  tag == "<1F4D>" or # 1F4D ... 1F6D: カラー画面表示 
                  tag == "<1F4F>"):  # 1F4F ... 1F6F: カラー画面参照 
                # "[図版]"で置き換える
                endtag = "<1F6{}>".format(tag[4])
                result += "[図版]"
                s = s[s.index(endtag)+6:]
            elif tag == "<1F61>": # 1F61: 検索キー終了 
                s = s[6:]
            elif tag == "<1FE0>": # 1FE0 xxxx: 文字修飾開始
                s = s[12:]
            elif tag == "<1FE1>": # 1FE1: 文字修飾終了
                s = s[6:]
            elif tag[1] >= 'A':
                # 外字
                result += gstr(s, halfwidth)
                s = s[6:]
            else:
                # その他のタグは無視
                s = s[6:]
            continue
        
        if halfwidth:
            n = tohan(s[0])
            if n == '<':
                result += "&lt;"
            elif n == '>':
                result += "&gt;"
            elif n == '&':
                result += "&amp;"
            elif n == '"':
                result += "&quot;"
            elif n == "'":
                result += "&apos;"
            else:
                result += n
            if len(result) - linetop >= MAX_HLINE and n == '.':
                result += '\n'
                linetop = len(result)
            s = s[1:]
        else:
            result += s[0]
            if len(result) - linetop >= MAX_HLINE and s[0] == '。':
                result += '\n'
                linetop = len(result)
            s = s[1:]
            
    # 最後の<br />は捨てる
    if result.endswith('<br />'):
        result = result[:-6]
    return result

def get_title(s):
    '''「1F41 xxxx ～ 1F61」または「1F41 xxxx 1F61 1FE0 xxxx ～ 1FE1」で
    囲まれたタイトルを取り出し、直前の位置とタイトルを返す
    ただし囲まれた範囲の長さが128バイト以上か
    <1F61>が見つからない場合はタイトルとしない
    '''
 
    if not s.startswith("<1F41>"):
        return s, ""
    p = s[12:] # <1F41><xxxx>をスキップ 
    r = p.index("<1F61>")
    if r == -1 or r >= MAX_WORD:
        return s, ""

    title = p[:r]
    if len(title) >= MAX_WORD:
        return s, ""
    p = p[r+6:]
    if r == 0 and p.startswith("<1FE0>"):
        # <1F41><xxxx><1F61><1FE0><yyyy> ～ <1FE1>の形式
        p = p[12:]
        r = p.index("<1FE1>")
        if r < 0:
            return s, ""
        return p[r+6:], p[:r]
    return p, title

def skipindent(s):
    '''入力の字下げタグをスキップし、字下げ量を返す'''
    if not s.startswith("<1F09>"):
        return s, 0
    return s[12:], int(s[7:11], 16) - 1

def indentstr(indent):
    '''出力用字下げタグ文字列を作る'''
    return "<X4081>1F09 {:04X}</X4081>".format(indent+1)

def generate_html_file():
    '''honmon.txtと作業データファイルを突き合わせてHTMLファイルを生成する'''
    global fkindex_data, fhindex_data, faindex_data
    global fktitle_data, fhtitle_data, fatitle_data
    global gen_kana, gen_hyoki, gen_alpha
    fp = html_newfile()
    
    with open(HONMON_FILE, "r", encoding='cp932') as honfp: 
        kdata = None
        if fkindex_data is not None:
            gen_kana = True
            kdata = IndexAndTitle(fkindex_data, fktitle_data)

        hdata = None
        if fhindex_data is not None:
            gen_hyoki = True
            hdata = IndexAndTitle(fhindex_data, fhtitle_data)

        adata = None
        if faindex_data is not None:
            gen_alpha = True
            adata = IndexAndTitle(faindex_data, fatitle_data)

        if kdata is None and hdata is None and adata is None:
            message("かな/表記/英字いずれのインデックス/見出しもありません\n");
            message("HTMLファイルの生成を中止します\n");
            raise Exception()

        message("HTMLファイルを生成しています...\n");
        have_auto_kana = False
        have_preamble = False
        first_dt = True
        needbr = False
        new_content = False
        kp = None
        hp = None
        ap = None
        if kdata is not None:
            kp = kdata.read_data()
        if hdata is not None:
            hp = hdata.read_data()
        if adata is not None:
            ap = adata.read_data()

        while True:
            dp = read_honmon_data(honfp)
            if dp is None:
                break
            if dp['dblk'] == 0 or dp['text'] == "":
                continue
            p = dp['text']
            if p == "<1F02>" or p == "<1F03>":
                # これらはどこにあっても単独で出力する
                if needbr:
                    fp.write("<br />\n")
                    needbr = False
                if p == "<1F02>":
                    fp.write("<X4081>1F02</X4081>\n")
                    new_content = True
                else:
                    fp.write("<X4081>1F03</X4081>\n")
                needbr = False
                continue
            
            if new_content:
                # <1F02>の直後の行; 無条件にアンカーを作る
                # (研究社新英和中辞典など)
                fp.write('<a name="{:08X}{:04X}"></a>\n'.format(
                    dp['dblk'], dp['dpos']))
                new_content = False

            have_indent = False
            have_indent2 = False
            istr = ''
            istr2 = ''
            
            if p.startswith("<1F09>"):
                p, indent = skipindent(p)
                have_indent = True
                istr = indentstr(indent)
            if p.startswith("<1F41>"):
                p, tmp = get_title(p)
                if p.startswith("<1F09>"):
                    p, indent2 = skipindent(p)
                    have_indent2 = True
                    istr2 = indentstr(indent2)
                tbuf = conv_honmon(tmp)
                buf = conv_honmon(p)
                title = tbuf if len(tbuf) > 0 else buf
            else:
                tbuf = ""
                buf = conv_honmon(p)
                title = buf

            while kp and compare_position(kp, dp) < 0:
                message("使われないかなインデックスがあります\n");
                message(("  本文位置=[{:08X}:{:04X}], " +
                         "インデックス=[{:08X}:{:04X}]{}\n").format(
                             dp['dblk'], dp['dpos'],
                             kp['dblk'], kp['dpos'], kp['text']))
                kp = kdata.read_data()

            while hp and compare_position(hp, dp) < 0:
                message("使われない表記インデックスがあります\n");
                message(("  本文位置=[{:08X}:{:04X}], " +
                         "インデックス=[{:08X}:{:04X}]{}\n").format(
                             dp['dblk'], dp['dpos'],
                             hp['dblk'], hp['dpos'], hp['text']))
                hp = hdata.read_data()

            while ap and compare_position(ap, dp) < 0:
                message("使われない英字インデックスがあります\n");
                message(("  本文位置=[{:08X}:{:04X}], " +
                         "インデックス=[{:08X}:{:04X}]{}\n").format(
                             dp['dblk'], dp['dpos'],
                             ap['dblk'], ap['dpos'], ap['text']))
                ap = adata.read_data()
            
            if ((kp and compare_position(kp, dp) == 0) or
                (hp and compare_position(hp, dp) == 0) or
                (ap and compare_position(ap, dp) == 0)):
                # インデックスから参照されている
                if have_preamble:
                    fp.write("\n</p>\n")
                    have_preamble = False
                if have_indent and indent > 0 or len(title) > MAX_WORD:
                    # 字下げされた位置が参照されているか
                    # あるいはタイトルが128バイトを超えているので
                    # 見出しとしては採用しない
                    # <dd>～</dd>内に参照位置があったとみなし、
                    # あたらしい<p>を始める
                    yield_dt = False
                else:
                    # 行頭位置が参照されており
                    # タイトル長が128バイト以下なので
                    # 新しい<dt id=...>を始める
                    yield_dt = True
                if yield_dt:
                    if first_dt:
                        first_dt = False
                    else:
                        fp.write("\n</p></dd>\n")
                    fp.write('<dt id="{:08X}{:04X}">{}</dt>\n'.format(
                        dp['dblk'], dp['dpos'], title))
                else:
                    fp.write("\n</p>\n<p>\n")

                while kp and compare_position(kp, dp) == 0:
                    fp.write('<key title="{}" type="kana">{}</key>\n'.format(
                        kp['title'] if len(kp['title']) else title, kp['text']))
                    kp = kdata.read_data()

                while hp and compare_position(hp, dp) == 0:
                    fp.write('<key title="{}" type="hyoki">{}</key>\n'.format(
                        hp['title'] if len(hp['title']) else title, hp['text']))
                    if auto_kana and iskanastr(hp['text']):
                        fp.write(
                            '<key title="{}" type="kana">{}</key>\n'.format(
                                hp['title'] if len(hp['title']) else title,
                                hp['text']))
                        have_auto_kana = True
                    hp = hdata.read_data()

                while ap and compare_position(ap, dp) == 0:
                    fp.write('<key title="{}" type="hyoki">{}</key>\n'.format(
                        ap['title'] if len(ap['title']) else title, ap['str']))
                    ap = adata.read_data()

                if yield_dt:
                    fp.write("<dd><p>\n")
                    if tbuf == "" and buf == "":
                        fp.write("{}{}".format(istr2, buf))
                    else:
                        fp.write(" ")
                else:
                    fp.write("{}{}{}{}".format(istr, tbuf, istr2, buf))

                have_indent = False
                have_indent2 = False
                istr = ""
                istr2 = ""
                needbr = True
                continue

            if needbr:
                fp.write("<br />\n")
                needbr = False

            if first_dt and not have_preamble:
                # 最初の<dt ...>より前に内容があった
                fp.write("<p>\n")
                have_preamble = True

            fp.write("{}{}{}{}".format(istr, tbuf, istr2, buf))
            needbr = True
        fp.write("\n")
    html_close(fp)
    message("HTMLファイルの生成が終了しました\n")

def generate_ebs_file():
    '''EBStudio定義ファイルを生成する'''

    with open(base_path / ebs_file, "w", encoding='cp932') as f:
        message("EBSファイルを生成しています... ")
        f.write("InPath={}\n".format(base_path))
        f.write("OutPath={}\n".format(out_path))
        f.write("IndexFile=\n")
        f.write("Copyright=\n")
        f.write("GaijiFile=$(BASE)\\{}\n".format(GFONT_FILE))
        f.write("GaijiMapFile=$(BASE)\\{}\n".format(GMAP_FILE))
        f.write("EBType={}\n".format(eb_type))
        f.write("WordSearchHyoki={}\n".format(
            1 if (gen_hyoki or gen_alpha) else 0))
        f.write("WordSearchKana={}\n".format(
            1 if (gen_kana or have_auto_kana) else 0))
        f.write("EndWordSearchHyoki={}\n".format(
            1 if (gen_hyoki or gen_alpha) else 0))
        f.write("EndWordSearchKana={}\n".format(
            1 if (gen_kana or have_auto_kana) else 0))
        f.write("KeywordSearch=0\n")
        f.write("ComplexSearch=0\n")
        f.write("topMenu=0\n")
        f.write("singleLine=1\n")
        f.write("kanaSep1=【\n")
        f.write("kanaSep2=】\n")
        f.write("hyokiSep=0\n")
        f.write("makeFig=0\n")
        f.write("inlineImg=0\n")
        f.write("paraHdr=0\n")
        f.write("ruby=1\n")
        f.write("paraBr=0\n")
        f.write("subTitle=0\n")
        f.write("dfnStyle=0\n")
        f.write("srchUnit=1\n")
        f.write("linkChar=0\n")
        f.write("arrowCode=222A\n")
        f.write("eijiPronon=1\n")
        f.write("eijiPartOfSpeech=1\n")
        f.write("eijiBreak=1\n")
        f.write("eijiKana=0\n")
        f.write("leftMargin=0\n")
        f.write("indent=0\n")
        f.write("tableWidth=480\n")
        f.write("StopWord=\n")
        f.write("delBlank=1\n")
        f.write("delSym=1\n")
        f.write("delChars=\n")
        f.write("refAuto=0\n")
        f.write("titleWord=0\n")
        f.write("autoWord=0\n")
        f.write("autoEWord=0\n")
        f.write("HTagIndex=0\n")
        f.write("DTTagIndex=1\n")
        f.write("dispKeyInSelList=0\n")
        f.write("titleOrder=0\n")
        f.write("omitHeader=0\n")
        f.write("addKana=1\n")
        f.write("autoKana=0\n")
        f.write("withHeader=0\n")
        f.write("optMono=0\n")
        f.write("Size=20000;30000;100;3000000;20000;20000;"+
                "20000;1000;1000;1000;1000\n")
        f.write("Book={};{};{};_;".format(book_title, book_dir, book_type))
        f.write("_;GAI16H00;GAI16F00;_;_;_;_;_;_;\n")
        f.write("Source=$(BASE)\\{};本文;_;HTML;\n".format(html_file))
    message("終了しました\n")

def parse_ini_file():
    '''設定ファイルを読み込む'''
    global base_path, out_path, auto_kana
    global eb_type, book_title, book_type, book_dir
    global html_file, ebs_file

    config = configparser.ConfigParser()
    config.read(INI_FILE)
    base_path = Path(config['DEFAULT']['BASEPATH'])
    out_path = Path(config['DEFAULT']['OUTPATH'])
    auto_kana = config['DEFAULT'].getboolean('AUTOKANA')
    eb_type = int(config['DEFAULT']['EBTYPE'])
    book_title = config['DEFAULT']['BOOKTITLE']
    book_type =  config['DEFAULT']['BOOKTYPE']
    if book_type not in ("国語辞典", "漢和辞典", "英和辞典", "和英辞典",
                         "現代用語辞典", "一般書物", "類語辞典"):
        message("未知の書籍種別が指定されています\n")
    book_dir = config['DEFAULT']['BOOKDIR']
    if len(book_dir):
        message("書籍ディレクトリ名が8バイトを超えています\n")
        for c in book_dir:
            if c not in string.ascii_uppercase + string.digits + "_":
                message("書籍ディレクトリ名に不正な文字(A-Z0-9_以外)" +
                        "が含まれています\n")
    html_file = Path(book_dir + ".html")
    ebs_file = Path(book_dir + ".ebs")

    message("変換設定は以下のとおりです\n")
    message("  BASEPATH = {}\n".format(base_path))
    message("  OUTPATH = {}\n".format(out_path))
    message("  AUTOKANA = {}\n".format(auto_kana))
    message("  EBTYPE = {}\n".format(eb_type))
    message("  BOOKTITLE = {}\n".format(book_title))
    message("  BOOKTYPE = {}\n".format(book_type))
    message("  BOOKDIR = {}\n".format(book_dir))
    message("  生成されるHTMLファイル = {}\n".format(html_file))
    message("  生成されるEBSファイル = {}\n".format(ebs_file))

def work_directory():
    '''ファイル出力先ディレクトリを作る'''
    if not base_path.exists():
        base_path.mkdir()
    if not out_path.exists():
        out_path.mkdir()

def init(cmd_path):
    '''初期化'''
    global start_time
    path = Path(cmd_path).parent
    os.chdir(path)
    start_time = datetime.now()
    write_log("開始時刻: {}".format(start_time))
    message("作業ディレクトリ {} に移動しました\n".format(path))

def term():
    '''終了処理'''
    global stop_time
    message("変換処理が終了しました\n")
    stop_time = datetime.now()
    t = (stop_time - start_time).total_seconds()
    write_log("終了時刻: {}".format(stop_time))
    message("経過時間: {:d}:{:02d}\n".format(int(t // 60), int(t % 60)))
    message("※ {}{} を入力としてEBStudioを実行してください\n".format(
        base_path, ebs_file))
    write_log("\n")

def main():
    init(sys.argv[0])
    parse_ini_file()
    work_directory()
    generate_gaiji_file()
    generate_work_file()
    generate_html_file()
    generate_ebs_file()
    term()

if __name__ == "__main__":
    main()
