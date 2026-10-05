import base64
import datetime
import hashlib
import ipaddress
import random
import re
import string
import threading
import uuid
from zoneinfo import ZoneInfo


CURRENT_SMTP_FROMMAIL = ''
_placeholder_context = threading.local()


def set_current_smtp_frommail(value):
    _placeholder_context.smtp_frommail = str(value or '').strip()

def set_current_zip_key(value):
    _placeholder_context.zip_key = str(value or '')

def set_current_pdf_key(value):
    _placeholder_context.pdf_key = str(value or '')


def get_current_company_email():
    return str(getattr(_placeholder_context, 'company_email', '') or '').strip()


FIRST_NAMES = [
    'James', 'Mary', 'John', 'Patricia', 'Robert', 'Jennifer', 'Michael', 'Linda',
    'William', 'Elizabeth', 'David', 'Barbara', 'Richard', 'Susan', 'Joseph', 'Jessica',
    'Thomas', 'Sarah', 'Charles', 'Karen', 'Christopher', 'Nancy', 'Daniel', 'Lisa'
]
LAST_NAMES = [
    'Smith', 'Johnson', 'Williams', 'Brown', 'Jones', 'Garcia', 'Miller', 'Davis',
    'Rodriguez', 'Martinez', 'Hernandez', 'Lopez', 'Gonzalez', 'Wilson', 'Anderson',
    'Thomas', 'Taylor', 'Moore', 'Jackson', 'Martin', 'Lee', 'Perez', 'Thompson', 'White'
]
COUNTRIES = ['United States', 'Canada', 'United Kingdom', 'Australia', 'Germany', 'France', 'Japan']
USER_AGENTS = [
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/120 Safari/537.36',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 Safari/605.1.15',
]
OPERATING_SYSTEMS = ['Windows', 'macOS', 'Linux', 'Android', 'iOS']
BROWSERS = ['Chrome', 'Firefox', 'Safari', 'Edge']


def random_string(length=15):
    return ''.join(random.choice(string.ascii_letters + string.digits) for _ in range(int(length)))


def random_number(length=15):
    return ''.join(random.choice(string.digits) for _ in range(int(length)))


def random_hash(length=20):
    return random_string(length)


def _random_lower(length):
    return ''.join(random.choice(string.ascii_lowercase) for _ in range(int(length)))


def _random_upper(length):
    return ''.join(random.choice(string.ascii_uppercase) for _ in range(int(length)))


def _random_ip():
    return str(ipaddress.IPv4Address(random.getrandbits(32)))


def _timezone_now(timezone='UTC'):
    try:
        return datetime.datetime.now(ZoneInfo(timezone or 'UTC'))
    except Exception:
        return datetime.datetime.now(datetime.timezone.utc)


def _censor_email(email):
    local, separator, domain = email.partition('@')
    if not separator:
        return email
    visible = local[:1] if local else ''
    return f'{visible}***@{domain}'


def random_company_name():
    prefixes = ['Global', 'Premier', 'Prime', 'Silver', 'Golden', 'Summit', 'Pioneer', 'Dynamic', 'Elite', 'Fusion']
    suffixes = ['Solutions', 'Services', 'Systems', 'Holdings', 'Enterprises', 'Logistics', 'Consulting', 'Technologies', 'Partners', 'Ventures']
    return f'{random.choice(prefixes)} {random.choice(suffixes)}'


def random_company_email(company_name):
    slug = re.sub(r'[^a-z0-9]+', '-', company_name.lower()).strip('-')
    return f'contact@{slug}.com'


def random_iban():
    return 'GB' + ''.join(random.choice(string.digits) for _ in range(20))


STREET_NAMES = [
    'Park', 'Oak', 'Maple', 'Cedar', 'Elm', 'Pine', 'Main', 'Washington', 'Franklin', 'Lincoln',
    'Madison', 'Jefferson', 'Lake', 'Hill', 'River', 'Church', 'High', 'Union', 'Central', 'Walnut',
    'Chestnut', 'Spruce', 'Locust', 'Willow', 'Meadow', 'Brook', 'Sunset', 'Grand', 'Market', 'Court',
    'State', 'School', 'Liberty', 'Heritage', 'King', 'Queen', 'Columbia', 'Delaware'
]
STREET_SUFFIXES = ['AVE', 'ST', 'RD', 'BLVD', 'LN', 'DR', 'CT', 'WAY', 'PL', 'TER', 'PKWY', 'CIR']
BUILDING_NAMES = ['Plaza', 'Tower', 'Building', 'Centre', 'Center', 'Square', 'Suites', 'Place', 'Executive Center', 'Business Center']
CITY_STATES = [
    ('Corning', 'NY'), ('South Corning', 'NY'), ('Painted Post', 'NY'), ('Elmira', 'NY'),
    ('Rochester', 'NY'), ('Buffalo', 'NY'), ('Syracuse', 'NY'), ('Albany', 'NY'), ('Binghamton', 'NY'),
    ('Scranton', 'PA'), ('Erie', 'PA'), ('Pittsburgh', 'PA'), ('Allentown', 'PA'),
    ('Newark', 'NJ'), ('Trenton', 'NJ'), ('Hartford', 'CT'), ('Bridgeport', 'CT'),
    ('Springfield', 'MA'), ('Worcester', 'MA'), ('Burlington', 'VT'), ('Manchester', 'NH'),
    ('Portland', 'ME'), ('Providence', 'RI'), ('Baltimore', 'MD'), ('Wilmington', 'DE'),
    ('Richmond', 'VA'), ('Cleveland', 'OH'), ('Toledo', 'OH'), ('Columbus', 'OH'), ('Dayton', 'OH'),
    ('Canton', 'OH'), ('Detroit', 'MI'), ('Grand Rapids', 'MI'), ('Milwaukee', 'WI'),
    ('Tulsa', 'OK'), ('Omaha', 'NE'), ('Des Moines', 'IA'), ('Austin', 'TX'), ('Dallas', 'TX'),
    ('Phoenix', 'AZ'), ('Denver', 'CO'), ('Atlanta', 'GA'), ('Charlotte', 'NC')
]

def _random_phone_parts():
    return random.randint(200, 999), random.randint(200, 999), random.randint(1000, 9999)


def random_phone():
    area, exchange, subscriber = _random_phone_parts()
    return f'+1 {area}-{exchange}-{subscriber}'


def random_invoice(digits=6):
    digits = int(digits)
    if digits < 1:
        digits = 1
    return f'INVOICE {random.randint(10 ** (digits - 1), 10 ** digits - 1)}'


def random_amount(digits=None):
    if digits is not None and str(digits).strip() != '':
        digits = int(digits)
        if digits < 1:
            digits = 1
        value = random.randint(10 ** (digits - 1), 10 ** digits - 1)
    else:
        value = random.randint(100, 999999)
    return f'{value:,}.{random.randrange(100):02d}'


def _random_building():
    initials = ' '.join(random.choice(string.ascii_uppercase) + '.' for _ in range(random.randint(2, 4)))
    return f'{initials} {random.choice(BUILDING_NAMES).upper()}'


def _random_street_address():
    number = random.randint(1, 9999)
    return f'{number} {random.choice(STREET_NAMES).upper()} {random.choice(STREET_SUFFIXES)}'


def _random_city_line():
    city, state = random.choice(CITY_STATES)
    return f'{city.upper()}, {state} {random.randint(10000, 99999)}'


def random_fax_number():
    area, exchange, subscriber = _random_phone_parts()
    return f'{area}-{exchange}-{subscriber}'


def random_signature():
    greeting = random.choice(['Thank you,', 'Regards,', 'Best regards,', 'Sincerely,', 'Warm regards,'])
    person = f'{random.choice(FIRST_NAMES)} {random.choice(LAST_NAMES)}'
    title = random.choice([
        'General Manager', 'Operations Manager', 'Sales Director', 'Client Relations Manager',
        'Business Development Manager', 'Account Executive', 'Senior Consultant', 'Office Manager'
    ])
    company = random_company_name()
    building = _random_building()
    street = _random_street_address()
    city_line = _random_city_line()
    phone = random_phone().replace('+1 ', '').replace('-', ' ')
    fax = random_fax_number().replace('-', ' ')
    phone_line = f'Telephone {phone}'
    fax_line = f'Fax {fax}'
    website = f'www.{re.sub(r"[^a-z0-9]+", "-", company.lower()).strip("-")}.com'
    disclaimer = random.choice([
        'This email contains confidential information and is intended only for the addressee.',
        'Please treat this communication as confidential and do not distribute it without authorization.',
        'This message is intended solely for the named recipient and may contain privileged information.',
    ])
    wordmark = ''.join(ch for ch in company.upper() if ch.isalnum())[:18]
    if not wordmark:
        wordmark = 'KINETROL'
    return '\n'.join([
        greeting,
        f'{person} - {title}',
        phone_line,
        fax_line,
        wordmark,
        f'{company}, {building}, {street}',
        city_line,
        website,
        disclaimer,
    ])


def render_signature_html(signature_value=None):
    """Render the signature in a compact HTML layout matching the branded sample design."""
    if signature_value is None:
        signature_value = random_signature()

    value = str(signature_value).replace('\r\n', '\n').replace('\r', '\n')
    lines = [line.strip() for line in value.split('\n') if line.strip()]

    if len(lines) < 5:
        return '<br>'.join(lines)

    greeting = lines[0]
    person_title = lines[1]
    phone_line = lines[2]
    fax_line = lines[3]
    wordmark = lines[4]
    address_lines = lines[5:len(lines) - 2]
    website = lines[-2] if len(lines) >= 2 else ''
    disclaimer = lines[-1]

    phone_and_fax = f'{phone_line} &nbsp;&nbsp; {fax_line}'
    address_html = '<div style="font-size:16px; line-height:1.45; color:#1b1b1b; margin-top:8px;">' + '<br>'.join(address_lines) + '</div>' if address_lines else ''
    website_html = f'<div style="font-size:16px; color:#0b5ed7; margin-top:6px;">{website}</div>' if website else ''

    return (
        f'<div style="font-family:Arial,Helvetica,sans-serif; color:#111; line-height:1.35; letter-spacing:0.1px;">'
        f'<div style="font-size:18px; margin-bottom:6px;">{greeting}</div>'
        f'<div style="font-size:22px; font-weight:700; margin-bottom:8px;">{person_title}</div>'
        f'<div style="font-size:18px; font-weight:500; margin-bottom:8px;">{phone_and_fax}</div>'
        f'<div style="display:inline-block; background:#f3d400; border:3px solid #111; padding:10px 18px 8px; margin:10px 0 8px; box-sizing:border-box;">'
        f'<span style="display:block; font-size:52px; line-height:0.9; font-weight:900; letter-spacing:2px; color:#111; white-space:nowrap;">{wordmark}</span>'
        f'</div>'
        f'{address_html}'
        f'{website_html}'
        f'<div style="font-size:14px; color:#333; margin-top:12px; line-height:1.5;">{disclaimer}</div>'
        f'</div>'
    )


def _recipient_parts(email):
    email = str(email or '')
    username, separator, domain = email.partition('@')
    domain_name = domain.split(':', 1)[0].split('.', 1)[0] if separator else ''
    domain_name = domain_name.replace('-', ' ').replace('_', ' ')
    return email, username, domain, domain_name


def _duration_text(bucket):
    try:
        bucket = int(bucket)
    except (TypeError, ValueError):
        return 'under 1 minute'
    if bucket <= 1:
        return 'under 1 minute'
    return f'under {bucket} minutes'


def _duration_seconds_for_bucket(bucket):
    try:
        bucket = int(bucket)
    except (TypeError, ValueError):
        bucket = 1
    if bucket < 1:
        bucket = 1
    start_seconds = (bucket - 1) * 60
    end_seconds = bucket * 60 - 1
    seconds = random.randint(start_seconds, end_seconds)
    hours, remainder = divmod(seconds, 3600)
    minutes, secs = divmod(remainder, 60)
    return f'{hours:02d}:{minutes:02d}:{secs:02d}'


def _replace_dynamic(text):
    def number_match(match):
        return random_number(match.group(1) or 15)

    def random_match(match):
        return random_string(match.group(1) or 15)

    def hash_match(match):
        return random_hash(match.group(1) or 20)

    text = re.sub(r'\{number(\d*)\}', number_match, text, flags=re.IGNORECASE)
    text = re.sub(r'\{random(\d*)\}', random_match, text, flags=re.IGNORECASE)
    text = re.sub(r'\{hash(\d*)\}', hash_match, text, flags=re.IGNORECASE)
    text = re.sub(r'\{receipt(\d*)\}', lambda m: random_number(m.group(1) or 8), text, flags=re.IGNORECASE)
    text = re.sub(r'{amount(\d*)}', lambda m: random_amount(m.group(1) or None), text, flags=re.IGNORECASE)
    text = re.sub(r'{invoice(\d*)}', lambda m: random_invoice(m.group(1) or 6), text, flags=re.IGNORECASE)
    text = re.sub(r'\{duration(\d+)\}', lambda m: _duration_seconds_for_bucket(m.group(1)), text, flags=re.IGNORECASE)
    text = re.sub(r'base64\((.*?)\)', lambda m: base64.b64encode(m.group(1).encode()).decode(), text, flags=re.IGNORECASE)
    text = re.sub(r'hex\((.*?)\)', lambda m: m.group(1).encode().hex(), text, flags=re.IGNORECASE)
    text = re.sub(r'\{date([+-]?\d*)\}', lambda m: (datetime.datetime.now() + datetime.timedelta(days=int(m.group(1) or 0))).strftime('%d %B, %Y'), text, flags=re.IGNORECASE)
    return text


def replace_placeholders(email, text, skip_link=False, info=None, timezone='UTC'):
    if text is None:
        return ''
    smtp_frommail = getattr(_placeholder_context, 'smtp_frommail', CURRENT_SMTP_FROMMAIL)
    zip_key = getattr(_placeholder_context, 'zip_key', '')
    pdf_key = getattr(_placeholder_context, 'pdf_key', '')
    email, username, domain, domain_name = _recipient_parts(email)
    mename = username.capitalize()
    company_name = random_company_name()
    company_email = random_company_email(company_name)
    _placeholder_context.company_name = company_name
    _placeholder_context.company_email = company_email
    now = _timezone_now(timezone)
    info = list(info or [])
    tomorrow = now + datetime.timedelta(days=1)
    random_lower = lambda match: _random_lower(match.group(1))
    random_upper = lambda match: _random_upper(match.group(1))
    replacements = {
        '{email}': email, '{EMAIL}': email, '{Email}': email,
        '{EMAIL64}': base64.b64encode(email.encode()).decode(),
        '{smtpfrommail}': smtp_frommail, '{SMTPFROMMAIL}': smtp_frommail,
        '{ZIPKEY}': zip_key, '{zipkey}': zip_key,
        '{PDFKEY}': pdf_key, '{pdfkey}': pdf_key,
        '{frommail}': smtp_frommail, '{FROMMAIL}': smtp_frommail,
        '{Email64}': base64.b64encode(email.encode()).decode(),
        '{base64email}': base64.b64encode(email.encode()).decode(),
        '[base64email]': base64.b64encode(email.encode()).decode(),
        '{hexemail}': email.encode().hex(), '{year}': str(datetime.datetime.now().year),
        '{EMAILHEX}': email.encode().hex(), '{EMAILUTF8}': email,
        '[year]': str(datetime.datetime.now().year), '{mename}': mename,
        '{mename3}': mename[:3].upper(), '{equal}': '=', '{frmsite}': domain_name.capitalize(),
        '[frmsite]': domain_name.capitalize(), '{domain}': domain,
        '{tld}': domain.rsplit('.', 1)[-1] if '.' in domain else '',
        '[tld]': domain.rsplit('.', 1)[-1] if '.' in domain else '',
        '{time}': now.strftime('%H:%M:%S %p'), '{TIME}': now.strftime('%H:%M:%S %p'),
        '[sec]': now.strftime('%S'), '{sec}': now.strftime('%S'),
        '{date}': now.strftime('%d %B, %Y'), '{DATE}': now.strftime('%d %B, %Y'),
        '{TOMORROW}': tomorrow.strftime('%d %B, %Y'),
        '{DATETYPE1}': now.strftime('%Y-%m-%d'), '{DATETYPE2}': now.strftime('%d/%m/%Y'),
        '{TIMETYPE1}': now.strftime('%H:%M'), '{TIMETYPE2}': now.strftime('%I:%M %p'),
        '[Time_own_format]': now.strftime('%d %B, %Y%H:%M:%S %p'),
        '{random}': random_string(), '[random]': random_number(10),
        '{number}': random_number(), '[number]': random_number(10),
        '{receipt}': random_number(8), '{hash}': random_hash(), '{IBAN}': random_iban(),
        '{UUID}': str(uuid.uuid4()),
        '{company_name}': company_name, '{business_name}': company_name,
        '{phone}': random_phone(), '{invoice}': random_invoice(),
        '{signature}': render_signature_html(random_signature()),
        '{SIGNATURE}': render_signature_html(random_signature()),
        '{companyemail}': company_email,
        '{full_name}': f'{random.choice(FIRST_NAMES)} {random.choice(LAST_NAMES)}',
        '{firstname}': random.choice(FIRST_NAMES), '{first_name}': random.choice(FIRST_NAMES),
        '{lastname}': random.choice(LAST_NAMES), '{last_name}': random.choice(LAST_NAMES),
        '{FAKENAME}': f'{random.choice(FIRST_NAMES)} {random.choice(LAST_NAMES)}',
        '{FIRSTNAME}': random.choice(FIRST_NAMES), '{LASTNAME}': random.choice(LAST_NAMES),
        '{COUNTRY}': random.choice(COUNTRIES), '{IP}': _random_ip(),
        '{USERAGENT}': random.choice(USER_AGENTS), '{OS}': random.choice(OPERATING_SYSTEMS),
        '{BROWSER}': random.choice(BROWSERS), '{EMAILCENSORED}': _censor_email(email),
        '{USERNAME}': username, '{CAPSUSERNAME}': username.capitalize(), '{BLOCKUSERNAME}': username.upper(),
        '{DOMAINFULL}': domain, '{CAPSDOMAINFULL}': domain.capitalize(), '{BLOCKDOMAINFULL}': domain.upper(),
        '{DOMAINNAME}': domain_name.lower(), '{CAPSDOMAINNAME}': domain_name.capitalize(), '{BLOCKDOMAINNAME}': domain_name.upper(),
        '{COMPANYNAME}': domain_name.replace('-', ' ').replace('_', ' ').title() if domain_name else company_name,
    }
    for index, value in enumerate(info, 1):
        replacements[f'{{INFO{index}}}'] = str(value)
    # v9.5: normalise ${token} -> {token} BEFORE the replacement loop so
    # documented ${email}-style tokens are actually substituted. Previously
    # this ran after the loop and left ${...} literal.
    text = re.sub(r'\$\{([^}]+)\}', r'{\1}', text)
    for token, value in replacements.items():
        text = text.replace(token, value)
    text = re.sub(r'\{INFO(\d+)\}', lambda match: str(info[int(match.group(1)) - 1]) if int(match.group(1)) <= len(info) else '', text)
    text = re.sub(r'\$\{([^}]+)\}', r'{\1}', text)
    text = re.sub(r'\{NUMBER(\d+)\}', lambda m: random_number(m.group(1)), text)
    text = re.sub(r'\{char(\d+)\}', random_lower, text)
    text = re.sub(r'\{CHAR(\d+)\}', random_upper, text)
    text = text.replace('{randstring}', _random_lower(random.randint(8, 15)))
    text = text.replace('{RANDSTRING}', _random_upper(random.randint(8, 15)))
    text = text.replace('{RANDSTRING25}', _random_lower(25)).replace('{RANDSTRING100}', _random_lower(100))
    text = text.replace('{MD5RANDOM}', hashlib.md5(random_string(32).encode()).hexdigest())
    text = text.replace('{SHA256RANDOM}', hashlib.sha256(random_string(32).encode()).hexdigest())
    text = re.sub(r'\{PICK\(["\']([^"\']+)["\']\)\}', lambda m: random.choice(m.group(1).split('|')), text)
    text = re.sub(r'\{BASE64\("(.*?)"\)\}', lambda m: base64.b64encode(m.group(1).encode()).decode(), text)
    text = re.sub(r'\{HEX\("(.*?)"\)\}', lambda m: m.group(1).encode().hex(), text)
    text = re.sub(r'\{UTF8\("(.*?)"\)\}', lambda m: m.group(1), text)
    return _replace_dynamic(text)


SUPPORTED_PLACEHOLDERS = {
    '{EMAIL}': "Replaces with the lead email",
    '{EMAIL64}': "Replaces email with it's base64 string",
    '{EMAILHEX}': "Replaces email with it's hex string",
    '{EMAILUTF8}': "Replaces email with it's utf8 string",
    '{INFO1}': 'Information supplied in the csv file 1st option after email',
    '{INFO2}': 'Information supplied in the csv file 2nd option after email',
    '{INFOX}': 'Information supplied in the csv file Xth option after email (X => replace X with valid number)',
    '{NUMBER1}': 'Random Digit of length 1',
    '{NUMBER2}': 'Random Digit of length 2',
    '{NUMBER3}': 'Random Digit of length 3',
    '{NUMBER4}': 'Random Digit of length 4',
    '{NUMBER5}': 'Random Digit of length 5',
    '{NUMBER6}': 'Random Digit of length 6',
    '{NUMBER7}': 'Random Digit of length 7',
    '{NUMBER8}': 'Random Digit of length 8',
    '{NUMBER9}': 'Random Digit of length 9',
    '{NUMBER10}': 'Random Digit of length 10',
    '{char1}': 'Random Lowercase Character of length 1',
    '{char2}': 'Random Lowercase Character of length 2',
    '{char3}': 'Random Lowercase Character of length 3',
    '{char4}': 'Random Lowercase Character of length 4',
    '{char5}': 'Random Lowercase Character of length 5',
    '{char6}': 'Random Lowercase Character of length 6',
    '{char7}': 'Random Lowercase Character of length 7',
    '{char8}': 'Random Lowercase Character of length 8',
    '{char9}': 'Random Lowercase Character of length 9',
    '{char10}': 'Random Lowercase Character of length 10',
    '{CHAR1}': 'Random Uppercase Character of length 1',
    '{CHAR2}': 'Random Uppercase Character of length 2',
    '{CHAR3}': 'Random Uppercase Character of length 3',
    '{CHAR4}': 'Random Uppercase Character of length 4',
    '{CHAR5}': 'Random Uppercase Character of length 5',
    '{CHAR6}': 'Random Uppercase Character of length 6',
    '{CHAR7}': 'Random Uppercase Character of length 7',
    '{CHAR8}': 'Random Uppercase Character of length 8',
    '{CHAR9}': 'Random Uppercase Character of length 9',
    '{CHAR10}': 'Random Uppercase Character of length 10',
    '{randstring}': 'Random String Lowercase of length 8 to 15',
    '{RANDSTRING}': 'Random String Uppercase of length 8 to 15',
    '{RANDSTRING25}': 'Random String Lowercase of length 25',
    '{RANDSTRING100}': 'Random String Lowercase of length 100',
    '{MD5RANDOM}': 'Random md5 string',
    '{SHA256RANDOM}': 'Random sha256 string',
    '{FAKENAME}': 'Random Full Name',
    '{FIRSTNAME}': 'Random First Name',
    '{LASTNAME}': 'Random Last Name',
    '{COUNTRY}': 'Random Country',
    '{IP}': 'Random IP',
    '{USERAGENT}': 'Random Useragent',
    '{OS}': 'Random OS',
    '{BROWSER}': 'Random Browser',
    '{TIME}': 'Current Time Based on Timezone set in the sender',
    '{DATE}': 'Current Date Based on Timezone set in the sender',
    '{duration1}': 'Replaces with a random HH:MM:SS duration in the first minute bucket, e.g. 00:00:57',
    '{duration2}': 'Replaces with a random HH:MM:SS duration in the second minute bucket, e.g. 00:01:40',
    '{duration3}': 'Replaces with a random HH:MM:SS duration in the third minute bucket, e.g. 00:02:45',
    '{duration4}': 'Replaces with a random HH:MM:SS duration in the fourth minute bucket, e.g. 00:03:12',
    '{duration5}': 'Replaces with a random HH:MM:SS duration in the fifth minute bucket, e.g. 00:04:36',
    '{durationN}': 'Replaces with a random HH:MM:SS duration in the N-th minute bucket, where N is a positive integer',
    '{TOMORROW}': 'Next Day Date Based on Timezone set in the sender',
    '{DATETYPE1}': 'DateTime Format variant 1 based on Timezone set in the sender',
    '{DATETYPE2}': 'DateTime Format variant 2 based on Timezone set in the sender',
    '{TIMETYPE1}': 'Time Format variant 1 based on Timezone set in the sender',
    '{TIMETYPE2}': 'Time Format variant 2 based on Timezone set in the sender',
    '{EMAILCENSORED}': 'Censors the email applied using {EMAIL} current lead email',
    '{USERNAME}': 'Extracts username from email lowercase',
    '{CAPSUSERNAME}': 'Extracts username from email capitalized',
    '{BLOCKUSERNAME}': 'Extracts username from email uppercase',
    '{DOMAINFULL}': 'Extracts domain with extension in lowercase',
    '{CAPSDOMAINFULL}': 'Extracts domain with extension capitalized',
    '{BLOCKDOMAINFULL}': 'Extracts domain with extension in uppercase',
    '{DOMAINNAME}': 'Extracts domain without extension in lowercase',
    '{smtpfrommail}': 'Replaces with the exact SMTP from-mail selected for the current send',
    '{SMTPFROMMAIL}': 'Replaces with the exact SMTP from-mail selected for the current send',
    '{CAPSDOMAINNAME}': 'Extracts domain without extension capitalized',
    '{BLOCKDOMAINNAME}': 'Extracts domain without extension in uppercase',
    '{DISCLAIMER}': 'Replaces with disclaimer message selected in the sender',
    '{LINK}': 'Replaces with the URL determined in the sender',
    '<img src="{HTMLIMAGE}" />': 'HTML to be shown as an image in the email body',
    '<img src="{QRCODE}" width="128px"/>': 'QR image of the string supplied to it in the sender',
    '<img src="{LOGO}" />': "Logo image determined using the email's full domain",
    '{logos}': 'Replaces with a random logo picked from your local logo folders (LOGO_PICS, IMG, LOGO) or fallback logo location',
    'data:local/,local_image_name.extension': 'Adds a custom local image to the email body',
    '{PICK("alex|alice|bryan")}': 'Randomly picks one item from a pipe-separated list',
    '{BASE64("")}': 'Converts anything inside the Base64 brackets',
    '{HEX("")}': 'Converts anything inside the hex brackets',
    '{UTF8("")}': 'Converts anything inside the UTF-8 brackets',
    '{ZIPKEY}': 'Replaced with the zip password from zip_config when password_protection is enabled',
    '{PDFKEY}': 'Replaced with the pdf password from html_pdf_config when password_protection is enabled',
    '{COMPANYNAME}': 'Extracts a display-style company name from the email domain',
    '{amount}': 'Random money amount with comma grouping and two decimals; integer part has 3 to 6 digits (hundreds to hundreds of thousands)',
    '{amount3}': 'Random amount with a 3-digit integer part, e.g. 999.41',
    '{amount4}': 'Random amount with a 4-digit integer part, e.g. 7,485.41',
    '{amount5}': 'Random amount with a 5-digit integer part, e.g. 60,585.41',
    '{invoice}': 'Random invoice reference, e.g. INVOICE 173115',
    '{invoiceN}': 'Random invoice reference whose number has exactly N digits',
    '{phone}': 'Random US-format phone number, e.g. +1 888-559-2634',
    '{signature}': 'Random business letterhead signature with company name, street address and phone on separate lines',
}


def placeholder_list():
    email_tokens = [
        '{EMAIL}', '{EMAIL64}', '{EMAILHEX}', '{EMAILUTF8}', '{INFO1}', '{INFO2}', '{INFOX}',
    ]
    general_tokens = [
        '{NUMBER1}', '{NUMBER2}', '{NUMBER3}', '{NUMBER4}', '{NUMBER5}', '{NUMBER6}', '{NUMBER7}',
        '{NUMBER8}', '{NUMBER9}', '{NUMBER10}', '{char1}', '{char2}', '{char3}', '{char4}',
        '{char5}', '{char6}', '{char7}', '{char8}', '{char9}', '{char10}', '{CHAR1}', '{CHAR2}',
        '{CHAR3}', '{CHAR4}', '{CHAR5}', '{CHAR6}', '{CHAR7}', '{CHAR8}', '{CHAR9}', '{CHAR10}',
        '{randstring}', '{RANDSTRING}', '{RANDSTRING25}', '{RANDSTRING100}', '{MD5RANDOM}',
        '{SHA256RANDOM}', '{FAKENAME}', '{FIRSTNAME}', '{LASTNAME}', '{COUNTRY}', '{IP}',
        '{USERAGENT}', '{OS}', '{BROWSER}', '{TIME}', '{DATE}', '{duration1}', '{duration2}',
        '{duration3}', '{duration4}', '{duration5}', '{TOMORROW}', '{DATETYPE1}',
        '{DATETYPE2}', '{TIMETYPE1}', '{TIMETYPE2}', '{EMAILCENSORED}', '{USERNAME}',
        '{CAPSUSERNAME}', '{BLOCKUSERNAME}', '{DOMAINFULL}', '{CAPSDOMAINFULL}',
        '{BLOCKDOMAINFULL}', '{DOMAINNAME}', '{CAPSDOMAINNAME}', '{BLOCKDOMAINNAME}',
        '{amount}', '{amount3}', '{amount4}', '{amount5}', '{invoice}', '{phone}', '{signature}',
    ]
    functional_tokens = [
        '{DISCLAIMER}', '{LINK}', '<img src="{HTMLIMAGE}" />', '<img src="{QRCODE}" width="128px"/>',
        '<img src="{LOGO}" />', 'data:local/,local_image_name.extension', '{PICK("alex|alice|bryan")}',
        '{BASE64("")}', '{HEX("")}', '{UTF8("")}', '{ZIPKEY}', '{PDFKEY}', '{COMPANYNAME}', '{logos}',
    ]

    def render(tokens):
        return [f'{token} => {SUPPORTED_PLACEHOLDERS[token]}' for token in tokens]

    lines = [
        '=========', 'Email Tags', '=======', *render(email_tokens),
        '', '=====', 'General Tags', '=====', *render(general_tokens),
        '', '======', 'Functional tags', '=====', *render(functional_tokens),
    ]
    return '\n'.join(lines)
