import os
import re
import json
import sys
import time
import hashlib
import logging
import threading
from pathlib import Path
from datetime import datetime
from collections import defaultdict, deque
from itertools import cycle
from queue import Queue, Empty

import requests
from bs4 import BeautifulSoup
from urllib.parse import urljoin, urlparse
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

from playwright.sync_api import sync_playwright
from colorama import init, Fore, Style
from tqdm import tqdm
import html2text

from pdf2image import convert_from_path
import pytesseract
import numpy as np
import cv2
from PIL import Image
import pypdf

from rich.console import Console
from rich.logging import RichHandler
from rich.progress import Progress, SpinnerColumn, BarColumn, TextColumn, TimeElapsedColumn, TimeRemainingColumn
from rich.traceback import install
from dotenv import load_dotenv

# Initialize Rich modules for improved tracebacks
install()

# Initialize Colorama for colored terminal text
init(autoreset=True)


class ColoredFormatter(logging.Formatter):
    """
    A custom logging formatter that adds colors, symbols, and '#' characters to enhance log readability.

    This formatter enhances log messages by prefixing them with colored symbols based on the log level
    and appending '#' characters to indicate log structure. It aids in quickly discerning the severity
    and nature of log messages in the console.

    Attributes:
        COLORS (dict): Mapping of log levels to their corresponding color codes.
        SYMBOLS (dict): Mapping of log levels to their corresponding symbols.
    """

    # Define colors for different log levels
    COLORS = {
        'DEBUG': Fore.CYAN,
        'INFO': Fore.GREEN,
        'WARNING': Fore.YELLOW,
        'ERROR': Fore.RED,
        'CRITICAL': Fore.RED + Style.BRIGHT
    }

    # Define symbols for different log levels
    SYMBOLS = {
        'INFO': '✔',
        'WARNING': '⚠',
        'ERROR': '✘',
        'CRITICAL': '✘'
    }

    def format(self, record):
        """
        Format the specified record as text.

        This method overrides the default `format` method to inject colors and symbols into the log message.

        Args:
            record (logging.LogRecord): The log record to be formatted.

        Returns:
            str: The formatted log message with colors, symbols, and '#' characters.
        """
        color = self.COLORS.get(record.levelname, Fore.WHITE)
        symbol = self.SYMBOLS.get(record.levelname, '')
        # Initial format with symbol and timestamp, followed by '#'
        header = f"{color}{symbol} {self.formatTime(record, self.datefmt)}#"
        # Log level, followed by '#'
        level = f"- {record.levelname}#"
        # Log message, followed by '#'
        message = f"- {record.getMessage()}#"
        return f"{header}\n{level}\n{message}"


class MovingIndicator(threading.Thread):
    """
    A thread that displays a moving indicator in the terminal to signify ongoing processes.

    The indicator moves from right to left within a specified length, providing visual feedback
    to the user that a process is active. It appends '##' to enhance the dynamic feel.

    Attributes:
        delay (float): Time delay between indicator movements in seconds.
        length (int): The length of the indicator before it wraps around.
        running (bool): Flag indicating whether the indicator is active.
        position (int): Current position of the indicator in the line.
        direction (int): Direction of movement; -1 for left, 1 for right.
    """

    def __init__(self, delay=0.1, length=20):
        """
        Initialize the MovingIndicator thread.

        Args:
            delay (float, optional): Time delay between indicator movements in seconds. Defaults to 0.1.
            length (int, optional): The length of the indicator before it wraps around. Defaults to 20.
        """
        super().__init__()
        self.delay = delay
        self.length = length
        self.running = False
        self.position = self.length - 1  # Start from the right
        self.direction = -1  # Move left

    def run(self):
        """
        Start the moving indicator.

        This method runs in a separate thread, continuously updating the indicator's position
        and displaying it in the terminal until stopped.
        """
        self.running = True
        while self.running:
            # Create the representation of the indicator
            line = [' '] * self.length
            if 0 <= self.position < self.length:
                line[self.position] = '#'
            indicator = ''.join(line) + '##'  # Add '##' at the end for dynamism
            # Display the indicator
            sys.stdout.write(f"\r{indicator}")
            sys.stdout.flush()
            # Update the position
            self.position += self.direction
            if self.position == 0 or self.position == self.length - 1:
                self.direction *= -1  # Change direction
            time.sleep(self.delay)

    def stop(self):
        """
        Stop the moving indicator.

        This method halts the indicator thread and cleans up the terminal line space.
        """
        self.running = False
        self.join()
        # Clean the indicator line
        sys.stdout.write('\r' + ' ' * (self.length + 2) + '\r')  # +2 for the '##'
        sys.stdout.flush()


class WebCrawler:
    """
    A comprehensive web crawler for extracting content and downloadable files from websites.

    This crawler navigates through web pages starting from a given URL, respecting specified depth,
    language patterns, and exclusions. It can optionally use Playwright for dynamic content rendering.
    Downloaded content is organized into designated directories, and logging is implemented with
    color-coded messages for better visibility.

    Attributes:
        start_url (str): The initial URL from which the crawler begins.
        max_depth (int): Maximum depth for recursive crawling.
        use_playwright (bool): Flag to determine if Playwright should be used for rendering.
        visited_pages (set): Set of URLs that have already been visited.
        downloaded_files (set): Set of file URLs that have been downloaded.
        domain (str): The domain of the start_url.
        excluded_paths (list): List of URL segments to exclude from crawling.
        downloadable_extensions (dict): Mapping of file types to their respective extensions.
        language_pattern (re.Pattern or None): Regex pattern to match desired language URLs.
        base_dir (str): Base directory for storing crawled content and logs.
        session (requests.Session): Configured requests session with retries.
        html_converter (html2text.HTML2Text): Converter object to transform HTML to Markdown.
        playwright (Playwright): Playwright instance for browser automation (if used).
        browser (Browser): Playwright browser instance.
        page (Page): Playwright page instance.
        indicator (MovingIndicator): Threaded moving indicator for terminal feedback.
        stats (defaultdict): Dictionary to keep track of various statistics during crawling.
        all_downloadable_exts (set): Set of all downloadable file extensions.
        content_type_mapping (dict): Mapping of content types to file extensions.
    """

    def __init__(self, start_url, max_depth=2, use_playwright=False, excluded_paths=None, download_extensions=None, language_pattern=None, base_dir=None):
        """
        Initialize the WebCrawler with configuration parameters.

        Args:
            start_url (str): The initial URL from which the crawler begins.
            max_depth (int, optional): Maximum depth for recursive crawling. Defaults to 2.
            use_playwright (bool, optional): Flag to determine if Playwright should be used for rendering. Defaults to False.
            excluded_paths (list, optional): List of URL segments to exclude from crawling. Defaults to None.
            download_extensions (dict, optional): Mapping of file types to their respective extensions. Defaults to None.
            language_pattern (re.Pattern or None, optional): Regex pattern to match desired language URLs. Defaults to None.
            base_dir (str, optional): Base directory for storing crawled content and logs. Defaults to a timestamped directory.
        """
        self.start_url = start_url
        self.max_depth = max_depth
        self.use_playwright = use_playwright
        self.visited_pages = set()
        self.downloaded_files = set()
        self.domain = urlparse(start_url).netloc
        self.excluded_paths = excluded_paths or ['selecteur-de-produits']
        self.downloadable_extensions = download_extensions or {
            'PDF': ['.pdf'],
            'Image': ['.png', '.jpg', '.jpeg', '.gif', '.svg'],
            'Doc': ['.doc', '.docx', '.xls', '.xlsx', '.ppt', '.pptx']
        }
        self.language_pattern = language_pattern
        self.base_dir = base_dir or f"crawler_output_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
        self.create_directories()
        self.setup_logging()
        self.stats = defaultdict(int)
        self.all_downloadable_exts = set(ext for exts in self.downloadable_extensions.values() for ext in exts)
        self.content_type_mapping = {
            'PDF': {
                'application/pdf': '.pdf'
            },
            'Image': {
                'image/jpeg': '.jpg',
                'image/png': '.png',
                'image/gif': '.gif',
                'image/svg+xml': '.svg',
            },
            'Doc': {
                'application/msword': '.doc',
                'application/vnd.openxmlformats-officedocument.wordprocessingml.document': '.docx',
                'application/vnd.ms-excel': '.xls',
                'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet': '.xlsx',
                'application/vnd.ms-powerpoint': '.ppt',
                'application/vnd.openxmlformats-officedocument.presentationml.presentation': '.pptx',
            }
        }
        self.session = self.setup_session()
        self.html_converter = html2text.HTML2Text()
        self.html_converter.ignore_links = False
        self.html_converter.body_width = 0
        self.html_converter.ignore_images = True
        self.html_converter.single_line_break = False
        if self.use_playwright:
            self.playwright = sync_playwright().start()
            self.browser = self.playwright.chromium.launch(headless=True)
            self.page = self.browser.new_page()
        self.indicator = MovingIndicator(length=20)

    def setup_session(self):
        """
        Configure a requests session with retry logic and custom headers.

        This session is set up to handle retries on specific HTTP statuses and to include
        a user-agent header for mimicking a standard browser.

        Returns:
            requests.Session: Configured session object.
        """
        session = requests.Session()
        retry_strategy = Retry(
            total=5,
            backoff_factor=1,
            status_forcelist=[429, 500, 502, 503, 504],
            allowed_methods=["HEAD", "GET", "OPTIONS"]
        )
        adapter = HTTPAdapter(max_retries=retry_strategy)
        session.mount("http://", adapter)
        session.mount("https://", adapter)
        session.verify = False  # Disable SSL verification if necessary
        session.headers.update({
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) '
                          'AppleWebKit/537.36 (KHTML, like Gecko) '
                          'Chrome/91.0.4472.124 Safari/537.36'
        })
        return session

    def create_directories(self):
        """
        Create the necessary directory structure for storing crawled content and logs.

        Directories created include:
            - content: For storing extracted page content.
            - PDF: For storing downloaded PDF files.
            - Image: For storing downloaded image files.
            - Doc: For storing downloaded document files.
            - logs: For storing log files.
        """
        directories = ['content', 'PDF', 'Image', 'Doc', 'logs']
        for dir_name in directories:
            path = os.path.join(self.base_dir, dir_name)
            os.makedirs(path, exist_ok=True)

    def setup_logging(self):
        """
        Configure the logging system with colored console output and file logging.

        Logs are formatted with timestamps, log levels, and messages. The console handler uses
        the ColoredFormatter for enhanced readability, while the file handler logs messages
        without color codes.
        """
        log_format = '%(asctime)s - %(levelname)s - %(message)s'
        formatter = ColoredFormatter(log_format)

        logger = logging.getLogger()
        logger.setLevel(logging.INFO)

        # File handler for logging to a file without colors
        file_handler = logging.FileHandler(os.path.join(self.base_dir, 'logs', 'crawler.log'), encoding='utf-8')
        file_handler.setFormatter(logging.Formatter(log_format))
        logger.addHandler(file_handler)

        # Console handler for logging to the terminal with colors
        console_handler = logging.StreamHandler()
        console_handler.setFormatter(formatter)
        logger.addHandler(console_handler)

        # Log the start of the crawler
        logging.info(f"Crawler started with language pattern: {self.language_pattern}")

    def should_exclude(self, url):
        """
        Determine if a URL should be excluded based on predefined segments.

        The method checks if any of the excluded path segments are present in the URL.

        Args:
            url (str): The URL to be evaluated.

        Returns:
            bool: True if the URL contains any excluded segment, False otherwise.
        """
        for excluded in self.excluded_paths:
            if excluded in url:
                return True
        return False

    def is_same_language(self, url):
        """
        Check if a URL matches the desired language pattern.

        If no language pattern is set, the method defaults to True, allowing all URLs.

        Args:
            url (str): The URL to be checked.

        Returns:
            bool: True if the URL matches the language pattern or if no pattern is set.
        """
        if not self.language_pattern:
            return True
        return self.language_pattern.search(url) is not None

    def is_downloadable_file(self, url):
        """
        Determine if a URL points to a downloadable file based on its extension.

        The method uses regular expressions to identify file extensions, allowing for
        potential suffixes like `.aspx`.

        Args:
            url (str): The URL to be evaluated.

        Returns:
            bool: True if the URL is identified as a downloadable file, False otherwise.
        """
        parsed_url = urlparse(url)
        path = parsed_url.path.lower()
        # Create a regex pattern to detect extensions, allowing for suffixes like .pdf.aspx
        pattern = re.compile(r'\.(' + '|'.join([ext.strip('.') for exts in self.downloadable_extensions.values() for ext in exts]) + r')(\.[a-z0-9]+)?$', re.IGNORECASE)
        return bool(pattern.search(path))

    def get_file_type_and_extension(self, url, response):
        """
        Determine the file type and appropriate extension based on the URL and response headers.

        The method first attempts to deduce the file type from the URL's extension. If unsuccessful,
        it falls back to using the `Content-Type` header from the HTTP response.

        Args:
            url (str): The URL of the file.
            response (requests.Response): The HTTP response object containing headers.

        Returns:
            tuple: A tuple containing the file type (str) and the determined extension (str).
                   Returns (None, None) if the file type cannot be determined.
        """
        parsed_url = urlparse(url)
        path = parsed_url.path.lower()

        # First attempt: deduce file type based on the URL
        for file_type, extensions in self.downloadable_extensions.items():
            for ext in extensions:
                # Adapt the pattern to include suffixes like .aspx
                pattern = re.compile(re.escape(ext) + r'(\.[a-z0-9]+)?$', re.IGNORECASE)
                if pattern.search(path):
                    return file_type, self.content_type_mapping[file_type].get(response.headers.get('Content-Type', '').lower(), ext)

        # Second attempt: deduce file type based on the Content-Type
        content_type = response.headers.get('Content-Type', '').lower()
        for file_type, mapping in self.content_type_mapping.items():
            if content_type in mapping:
                return file_type, mapping[content_type]

        # If no type is determined, return None
        return None, None

    def sanitize_filename(self, url, file_type, extension, page_number=None):
        """
        Create a sanitized and unique filename based on the URL.

        The method removes unsafe characters, appends a short hash of the URL to ensure uniqueness,
        and adjusts the extension if necessary.

        Args:
            url (str): The URL from which to derive the filename.
            file_type (str): The type category of the file (e.g., 'PDF', 'Image', 'Doc').
            extension (str): The file extension to use.
            page_number (int, optional): If processing paginated content, the page number. Defaults to None.

        Returns:
            str: The sanitized filename.
        """
        # Create a short hash of the URL
        url_hash = hashlib.md5(url.encode()).hexdigest()[:8]

        # Extract the last segment of the URL
        filename = url.split('/')[-1]
        if not filename:
            filename = 'index'

        # Clean the filename by replacing unsafe characters
        filename = re.sub(r'[^\w\-_.]', '_', filename)

        # Remove existing extensions
        name, _ = os.path.splitext(filename)

        # Define the extension based on file type
        if not extension:
            extension = '.txt'  # Default extension if not determined

        if page_number is not None:
            sanitized = f"{name}_page_{page_number:03d}_{url_hash}{extension}"
        else:
            sanitized = f"{name}_{url_hash}{extension}"

        logging.debug(f"Sanitized filename: {sanitized}")
        return sanitized

    def download_file(self, url, file_type):
        """
        Download a file from a given URL and save it to the appropriate directory.

        The method handles HTTP requests with streaming, displays a progress bar during the download,
        and manages exceptions to ensure robust downloading.

        Args:
            url (str): The URL of the file to download.
            file_type (str): The type category of the file (e.g., 'PDF', 'Image', 'Doc').

        Returns:
            bool: True if the download was successful, False otherwise.
        """
        try:
            logging.info(f"Attempting to download {file_type} from: {url}")

            # Determine the file type and extension
            response = self.session.head(url, allow_redirects=True, timeout=10)
            file_type_detected, extension = self.get_file_type_and_extension(url, response)
            if not file_type_detected:
                logging.warning(f"⚠ Unable to determine file type for: {url}")
                return False

            # Properly rename the file
            filename = self.sanitize_filename(url, file_type_detected, extension)
            save_path = os.path.join(self.base_dir, file_type_detected, filename)

            # Check if the file already exists
            if os.path.exists(save_path):
                logging.info(f"📂 File already downloaded, skipping: {filename}")
                return False

            # Download the file with a progress bar
            response = self.session.get(url, stream=True, timeout=20)
            total_size = int(response.headers.get('content-length', 0))
            block_size = 1024  # 1 Kibibyte
            progress_bar = tqdm(total=total_size, unit='iB', unit_scale=True, desc=f"⏬ Downloading {filename}", leave=False)

            with open(save_path, 'wb') as f:
                for chunk in response.iter_content(chunk_size=block_size):
                    if chunk:
                        f.write(chunk)
                        progress_bar.update(len(chunk))
            progress_bar.close()

            if total_size != 0 and progress_bar.n != total_size:
                logging.warning(f"⚠ Incomplete download for {url}")
                return False

            self.stats[f'{file_type_detected}_downloaded'] += 1
            self.downloaded_files.add(url)
            logging.info(f"✅ Successfully downloaded {file_type_detected}: {filename}")
            return True

        except Exception as e:
            logging.error(f"✘ Error downloading {url}: {str(e)}")
            return False

    def convert_links_to_absolute(self, soup, base_url):
        """
        Convert all relative links within the BeautifulSoup object to absolute URLs.

        This ensures that all hyperlinks point to fully qualified URLs, which is essential
        for accurate crawling and resource linking.

        Additionally, it handles tags like <embed>, <iframe>, and <object> by updating their
        'src' attributes accordingly.

        Args:
            soup (BeautifulSoup): The BeautifulSoup object representing the HTML content.
            base_url (str): The base URL to resolve relative links against.

        Returns:
            BeautifulSoup: The modified BeautifulSoup object with absolute URLs.
        """
        # Include <embed>, <iframe>, and <object> tags in addition to <a> and <link>
        for tag in soup.find_all(['a', 'embed', 'iframe', 'object'], href=True):
            href = tag.get('href') or tag.get('src')
            if href:
                absolute_url = urljoin(base_url, href)
                if tag.name in ['embed', 'iframe', 'object']:
                    tag['src'] = absolute_url
                else:
                    tag['href'] = absolute_url
        return soup

    def clean_text(self, text):
        """
        Clean and format text by removing unnecessary spaces and ensuring clear separation.

        The method removes unwanted special characters, normalizes spaces, and manages line breaks
        to produce clean, readable text suitable for storage or further processing.

        Args:
            text (str): The raw text to be cleaned.

        Returns:
            str: The cleaned and formatted text.
        """
        if not text:
            return ""

        # Remove unwanted special characters
        text = re.sub(r'[\x00-\x08\x0B\x0C\x0E-\x1F\x7F-\x9F]', '', text)

        # Normalize spaces (replace multiple spaces/tabs with a single space)
        text = re.sub(r'[ \t]+', ' ', text)

        # Normalize newlines (replace multiple newlines with two newlines)
        text = re.sub(r'\n\s*\n', '\n\n', text)

        return text.strip()

    def fetch_page_content(self, url):
        """
        Retrieve the content of a web page using either Playwright or Requests.

        Depending on the `use_playwright` flag, this method fetches the page content using
        Playwright for dynamic rendering or the Requests library for static content.

        Args:
            url (str): The URL of the page to fetch.

        Returns:
            str or None: The HTML content of the page if successful, None otherwise.
        """
        if self.use_playwright:
            try:
                logging.info(f"🔍 Fetching with Playwright: {url}")
                self.page.goto(url, timeout=20000)
                time.sleep(2)  # Wait for the page to fully load
                content = self.page.content()
                return content
            except Exception as e:
                logging.error(f"✘ Playwright failed to fetch {url}: {str(e)}")
                return None
        else:
            try:
                response = self.session.get(url, timeout=20)
                if response.status_code == 200:
                    logging.info(f"✅ Successfully fetched content: {url}")
                    return response.text
                else:
                    logging.warning(f"⚠ Failed to fetch {url} with status code {response.status_code}")
                    return None
            except Exception as e:
                logging.error(f"✘ Requests failed to fetch {url}: {str(e)}")
                return None

    def extract_content(self, url):
        """
        Extract and save the main content of a web page in Markdown format.

        This method processes the HTML content by removing unwanted elements, converting
        links to absolute URLs, and saving the cleaned content. It also identifies and
        downloads any embedded downloadable files found within the page.

        Args:
            url (str): The URL of the page to extract content from.
        """
        logging.info(f"📄 Extracting content from: {url}")

        try:
            if self.is_downloadable_file(url):
                logging.info(f"🔗 Skipping content extraction for downloadable file: {url}")
                return

            page_content = self.fetch_page_content(url)
            if page_content is None:
                logging.warning(f"⚠ Unable to retrieve content for: {url}")
                return

            soup = BeautifulSoup(page_content, 'html.parser')

            # Remove unwanted elements
            for element in soup.find_all(['nav', 'header', 'footer', 'script', 'style', 'aside', 'iframe']):
                element.decompose()

            # Extract main content
            main_content = (
                soup.find('main') or
                soup.find('article') or
                soup.find('div', class_='content') or
                soup.find('div', id='content')
            )

            if main_content:
                # Convert relative links to absolute
                main_content = self.convert_links_to_absolute(main_content, url)

                # Convert main content to Markdown
                markdown_content = self.html_converter.handle(str(main_content))

                # Build the final content with title
                content_parts = []

                # Add the title if available
                title = soup.find('h1')
                if title:
                    content_parts.append(f"# {title.get_text().strip()}")

                # Add the source URL
                content_parts.append(f"**Source:** {url}")

                # Add the main Markdown content
                content_parts.append(markdown_content)

                # Clean the content
                content = self.clean_text('\n\n'.join(content_parts))

                if content:
                    # Create filename
                    filename = self.sanitize_filename(url, 'Doc', '.txt')  # Use 'Doc' with '.txt' extension for pages
                    save_path = os.path.join(self.base_dir, 'content', filename)
                    with open(save_path, 'w', encoding='utf-8') as f:
                        f.write(content)

                    self.stats['pages_processed'] += 1
                    logging.info(f"✅ Content successfully saved to: {filename}")
                else:
                    logging.warning(f"⚠ No significant content found for: {url}")

                # Process downloadable files found on the page
                downloadable_tags = main_content.find_all(['a', 'embed', 'iframe', 'object'], href=True)

                if downloadable_tags:
                    logging.info(f"🔄 Detected {len(downloadable_tags)} downloadable files on the page.")

                for tag in downloadable_tags:
                    href = tag.get('href') or tag.get('src')
                    if href:
                        file_url = urljoin(url, href)
                        if self.is_downloadable_file(file_url) and file_url not in self.downloaded_files:
                            # Use HEAD to get Content-Type without downloading the file
                            try:
                                response_head = self.session.head(file_url, allow_redirects=True, timeout=10)
                                file_type_detected, _ = self.get_file_type_and_extension(file_url, response_head)
                            except:
                                # Fallback to GET if HEAD fails
                                response_head = self.session.get(file_url, allow_redirects=True, timeout=10)
                                file_type_detected, _ = self.get_file_type_and_extension(file_url, response_head)

                            if file_type_detected:
                                # Properly rename the file
                                filename = self.sanitize_filename(file_url, file_type_detected, self.content_type_mapping[file_type_detected].get(response_head.headers.get('Content-Type', '').lower(), ''))
                                save_path = os.path.join(self.base_dir, file_type_detected, filename)

                                if os.path.exists(save_path):
                                    logging.info(f"📂 File already downloaded, skipping: {filename}")
                                    continue

                                self.download_file(file_url, file_type_detected)

            else:
                logging.warning(f"⚠ No main content found for: {url}")

        except Exception as e:
            logging.error(f"✘ Error processing {url}: {str(e)}")

    def extract_urls(self, start_url):
        """
        Recursively extract URLs from a page up to the specified maximum depth.

        This method navigates through pages, adhering to exclusion rules and language patterns,
        and identifies downloadable files for immediate download.

        Args:
            start_url (str): The starting URL for URL extraction.
        """
        queue = deque()
        queue.append((start_url, 0))
        self.visited_pages.add(start_url)

        pbar = tqdm(total=1, desc="🔍 Extracting URLs", unit="page", ncols=100)

        while queue:
            current_url, depth = queue.popleft()

            if depth > self.max_depth:
                pbar.update(1)
                continue

            # Check if the URL should be excluded
            if self.should_exclude(current_url):
                logging.info(f"🚫 URL excluded due to excluded segment: {current_url}")
                pbar.update(1)
                continue

            logging.info(f"🔎 Extracting URLs from: {current_url} (depth: {depth})")

            try:
                if self.is_downloadable_file(current_url):
                    # Use HEAD to get Content-Type without downloading the file
                    try:
                        response_head = self.session.head(current_url, allow_redirects=True, timeout=10)
                        file_type_detected, _ = self.get_file_type_and_extension(current_url, response_head)
                    except:
                        # Fallback to GET if HEAD fails
                        response_head = self.session.get(current_url, allow_redirects=True, timeout=10)
                        file_type_detected, _ = self.get_file_type_and_extension(current_url, response_head)

                    if file_type_detected:
                        # Rename the file to check existence
                        filename = self.sanitize_filename(current_url, file_type_detected, self.content_type_mapping[file_type_detected].get(response_head.headers.get('Content-Type', '').lower(), ''))
                        save_path = os.path.join(self.base_dir, file_type_detected, filename)

                        if os.path.exists(save_path):
                            logging.info(f"📂 File already downloaded, skipping: {filename}")
                            pbar.update(1)
                            continue

                        self.download_file(current_url, file_type_detected)
                        self.downloaded_files.add(current_url)
                    pbar.update(1)
                    continue

                # Fetch page content (with Playwright or Requests)
                page_content = self.fetch_page_content(current_url)
                if page_content is None:
                    logging.warning(f"⚠ Unable to retrieve content for: {current_url}")
                    pbar.update(1)
                    continue

                soup = BeautifulSoup(page_content, 'html.parser')

                # Search for downloadable files and links
                for tag in soup.find_all(['a', 'link', 'embed', 'iframe', 'object'], href=True):
                    href = tag.get('href') or tag.get('src')
                    if href:
                        absolute_url = urljoin(current_url, href)
                        parsed_url = urlparse(absolute_url)

                        # Check if it's a downloadable file
                        if self.is_downloadable_file(absolute_url):
                            # Use HEAD to get Content-Type without downloading the file
                            try:
                                response_head = self.session.head(absolute_url, allow_redirects=True, timeout=10)
                                file_type_detected, _ = self.get_file_type_and_extension(absolute_url, response_head)
                            except:
                                # Fallback to GET if HEAD fails
                                response_head = self.session.get(absolute_url, allow_redirects=True, timeout=10)
                                file_type_detected, _ = self.get_file_type_and_extension(absolute_url, response_head)

                            if file_type_detected:
                                # Rename the file to check existence
                                filename = self.sanitize_filename(absolute_url, file_type_detected, self.content_type_mapping[file_type_detected].get(response_head.headers.get('Content-Type', '').lower(), ''))
                                save_path = os.path.join(self.base_dir, file_type_detected, filename)

                                if os.path.exists(save_path):
                                    logging.info(f"📂 File already downloaded, skipping: {filename}")
                                    continue

                                self.download_file(absolute_url, file_type_detected)
                                self.downloaded_files.add(absolute_url)
                            continue

                        # Check for internal links
                        if (self.domain in parsed_url.netloc and
                            self.is_same_language(absolute_url) and
                            absolute_url not in self.visited_pages and
                            not absolute_url.endswith(('#', 'javascript:void(0)', 'javascript:;')) and
                            not self.should_exclude(absolute_url)):

                            # Add to queue with incremented depth
                            queue.append((absolute_url, depth + 1))
                            self.visited_pages.add(absolute_url)
                            pbar.total += 1  # Increase progress bar
                            pbar.refresh()

            except Exception as e:
                logging.error(f"✘ Error crawling {current_url}: {str(e)}")

            pbar.update(1)

        pbar.close()
        logging.info("🔍 URL extraction completed.")

    def crawl(self):
        """
        Execute the crawling process.

        This is the main method that orchestrates the crawling phases:
            1. URL Extraction: Gathers all relevant URLs up to the specified depth.
            2. Content Extraction: Processes each collected URL to extract and save content.
            3. Reporting: Generates a comprehensive report of the crawling session.

        Additionally, it handles the loading and saving of previously downloaded files to avoid redundancy.

        Raises:
            Exception: Propagates any critical exceptions encountered during crawling.
        """
        start_time = time.time()
        logging.info(f"🚀 Starting crawl of {self.start_url}")
        logging.info(f"🌐 Language pattern: {self.language_pattern}")
        logging.info(f"📏 Maximum depth: {self.max_depth}")

        # Load previously downloaded files
        self.load_downloaded_files()

        # Start the moving indicator
        self.indicator.start()

        try:
            # Phase 1: URL Extraction
            logging.info("🔍 Phase 1: Starting URL extraction")
            self.extract_urls(self.start_url)

            # Phase 2: Content Extraction
            logging.info("📄 Phase 2: Starting content extraction")
            visited_without_files = [url for url in self.visited_pages if not self.is_downloadable_file(url)]

            pbar_content = tqdm(total=len(visited_without_files), desc="📄 Extracting Content", unit="page", ncols=100)
            for i, url in enumerate(visited_without_files, 1):
                logging.info(f"📝 Processing URL {i}/{len(visited_without_files)}: {url}")
                self.extract_content(url)
                pbar_content.update(1)
            pbar_content.close()
            logging.info("📄 Content extraction completed.")

            # Generate the final report
            end_time = time.time()
            self.generate_report(end_time - start_time)

        except Exception as e:
            logging.error(f"⚠ Critical error during crawling: {str(e)}")
            self.generate_report(time.time() - start_time, error=str(e))

        finally:
            # Stop the moving indicator
            self.indicator.stop()

            # Save downloaded files
            self.save_downloaded_files()

            # Close Playwright if used
            if self.use_playwright:
                self.page.close()
                self.browser.close()
                self.playwright.stop()

    def load_downloaded_files(self):
        """
        Load URLs of previously downloaded files from the tracking file.

        This method reads from 'downloaded_files.txt' to populate the `downloaded_files` set,
        ensuring that the crawler does not redownload files.

        Notes:
            - If the tracking file does not exist, it initializes with an empty set.
        """
        downloaded_files_path = os.path.join(self.base_dir, 'logs', 'downloaded_files.txt')
        if os.path.exists(downloaded_files_path):
            with open(downloaded_files_path, 'r', encoding='utf-8') as f:
                for line in f:
                    self.downloaded_files.add(line.strip())
            logging.info(f"📥 Loaded {len(self.downloaded_files)} downloaded files from the tracking file.")
        else:
            logging.info("🆕 No download tracking file found, starting fresh.")

    def save_downloaded_files(self):
        """
        Save the URLs of downloaded files to a tracking file.

        This ensures that files are not redownloaded in future crawling sessions.
        """
        downloaded_files_path = os.path.join(self.base_dir, 'logs', 'downloaded_files.txt')
        try:
            with open(downloaded_files_path, 'w', encoding='utf-8') as f:
                for url in sorted(self.downloaded_files):
                    f.write(url + '\n')
            logging.info(f"💾 Saved {len(self.downloaded_files)} downloaded files to the tracking file.")
        except Exception as e:
            logging.error(f"✘ Error saving downloaded files tracking: {str(e)}")

    def generate_report(self, duration, error=None):
        """
        Generate a detailed report of the crawling process.

        The report includes configuration details, statistics, processed URLs,
        generated files, and any critical errors encountered.

        Args:
            duration (float): Total duration of the crawling process in seconds.
            error (str, optional): Description of any critical error that occurred. Defaults to None.
        """
        report_sections = []

        # Report header
        report_sections.append(f"""
Crawler Report
==============
Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}

Configuration
------------
Start URL: {self.start_url}
Language Pattern: {self.language_pattern}
Max Depth: {self.max_depth}
Duration: {duration:.2f} seconds

Statistics
---------
Total URLs found: {len(self.visited_pages)}
Pages processed: {self.stats['pages_processed']}
Files downloaded:
- PDFs: {self.stats['PDF_downloaded']}
- Images: {self.stats['Image_downloaded']}
- Documents: {self.stats['Doc_downloaded']}
""")

        # Error section if present
        if error:
            report_sections.append(f"""
Errors
------
Critical Error: {error}

""")

        # List of processed URLs
        report_sections.append("""
Processed URLs
-------------
""")
        for url in sorted(self.visited_pages):
            report_sections.append(url)

        # List of generated files
        report_sections.append("""
Generated Files
--------------
""")
        for directory in ['content', 'PDF', 'Image', 'Doc']:
            dir_path = os.path.join(self.base_dir, directory)
            if os.path.exists(dir_path):
                files = os.listdir(dir_path)
                report_sections.append(f"\n{directory} Files ({len(files)}):")
                for file in sorted(files):
                    report_sections.append(f"- {file}")

        # Save the report
        report_content = '\n'.join(report_sections)
        report_path = os.path.join(self.base_dir, 'crawler_report.txt')

        try:
            with open(report_path, 'w', encoding='utf-8') as f:
                f.write(report_content)
            logging.info(f"📄 Report successfully generated: {report_path}")
        except Exception as e:
            logging.error(f"✘ Error generating report: {str(e)}")

        # Create a summary file
        summary = f"""
Crawling Summary
---------------
Start URL: {self.start_url}
Total URLs: {len(self.visited_pages)}
Pages Processed: {self.stats['pages_processed']}
Total Files Downloaded: {sum(self.stats[k] for k in ['PDF_downloaded', 'Image_downloaded', 'Doc_downloaded'])}
Duration: {duration:.2f} seconds
Status: {'⚠ Completed with errors' if error else '✅ Completed successfully'}
"""
        try:
            with open(os.path.join(self.base_dir, 'summary.txt'), 'w', encoding='utf-8') as f:
                f.write(summary)
            logging.info(f"📄 Summary successfully generated: {os.path.join(self.base_dir, 'summary.txt')}")
        except Exception as e:
            logging.error(f"✘ Error generating summary: {str(e)}")


class PDFExtractor:
    """
    A utility class for extracting text from PDF and DOC files.

    This class handles the conversion of PDFs to images for OCR processing,
    extracts text using both OCR and direct extraction methods, and processes
    the text with GPT-4 for structuring and formatting. It supports
    multithreading for efficient processing of large documents.

    Attributes:
        input_dir (Path): Directory containing input files (PDFs).
        output_dir (Path): Directory where extracted and processed content is saved.
        api_keys (Queue): Queue of OpenAI API keys for handling rate limits.
        max_workers (int): Maximum number of worker threads for concurrent processing.
        initial_dpi (int): Initial DPI setting for PDF to image conversion.
        retry_dpi (int): DPI setting for retrying failed conversions.
        logger (logging.Logger): Logger for recording actions and errors.
    """

    def __init__(self, input_dir, output_dir, api_keys_file, max_workers=10, initial_dpi=300, retry_dpi=200, logger=None):
        """
        Initialize the PDFExtractor with necessary configurations.

        Args:
            input_dir (str or Path): Directory containing input PDF files.
            output_dir (str or Path): Directory to save extracted content.
            api_keys_file (str): Path to the file containing OpenAI API keys.
            max_workers (int, optional): Number of threads for parallel processing. Defaults to 10.
            initial_dpi (int, optional): DPI for initial PDF to image conversion. Defaults to 300.
            retry_dpi (int, optional): DPI for retry attempts if initial conversion fails. Defaults to 200.
            logger (logging.Logger, optional): Logger for logging information and errors. Defaults to None.
        """
        # Configure paths
        self.input_dir = Path(input_dir)
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)

        # Load OpenAI API keys from file
        self.api_keys = Queue()
        try:
            with open(api_keys_file, 'r') as f:
                for line in f:
                    key = line.strip()
                    if key:
                        self.api_keys.put(key)
            if self.api_keys.empty():
                raise ValueError("No API keys loaded.")
        except Exception as e:
            if logger:
                logger.error(f"🚫 Error loading API keys: {str(e)}")
            else:
                print(f"🚫 Error loading API keys: {str(e)}")
            raise

        self.max_workers = max_workers
        self.initial_dpi = initial_dpi
        self.retry_dpi = retry_dpi
        self.logger = logger or logging.getLogger(__name__)

    def preprocess_image(self, image):
        """
        Preprocess an image to enhance OCR accuracy.

        The preprocessing steps include converting to grayscale, denoising, applying CLAHE,
        and adaptive thresholding. These steps improve the quality of text recognition.

        Args:
            image (PIL.Image.Image or np.ndarray): The image to preprocess.

        Returns:
            np.ndarray: The preprocessed binary image ready for OCR.

        Raises:
            ValueError: If the image is empty or corrupted, or if preprocessing fails.
        """
        if isinstance(image, Image.Image):
            image = np.array(image)

        if image is None:
            raise ValueError("⚠ Empty or corrupted image.")

        try:
            if len(image.shape) == 3:
                gray = cv2.cvtColor(image, cv2.COLOR_BGR2GRAY)
            else:
                gray = image

            denoised = cv2.fastNlMeansDenoising(gray)
            clahe = cv2.createCLAHE(clipLimit=2.0, tileGridSize=(8, 8))
            enhanced = clahe.apply(denoised)
            binary = cv2.adaptiveThreshold(
                enhanced, 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C,
                cv2.THRESH_BINARY, 11, 2
            )
            return binary
        except Exception as e:
            raise ValueError(f"⚠ Error during image preprocessing: {str(e)}")

    def convert_pdf_to_images(self, pdf_path, dpi):
        """
        Convert a PDF file into a list of images at a specified DPI.

        Args:
            pdf_path (Path): Path to the PDF file to convert.
            dpi (int): Dots per inch for the conversion resolution.

        Returns:
            list or None: List of PIL.Image.Image objects if successful, None otherwise.
        """
        try:
            self.logger.info(f"📄 Converting {pdf_path.name} to images with DPI={dpi}")
            images = convert_from_path(pdf_path, dpi=dpi, fmt='jpeg', thread_count=1)
            self.logger.info(f"✅ Successfully converted {pdf_path.name} with DPI={dpi}")
            return images
        except Exception as e:
            self.logger.error(f"❌ Error converting {pdf_path.name} to images with DPI={dpi}: {str(e)}")
            return None

    def extract_text_with_ocr(self, pdf_path):
        """
        Extract text from a PDF using OCR with retry mechanisms for failed conversions.

        The method first attempts to convert the PDF to images at the initial DPI setting.
        If unsuccessful, it retries with a lower DPI. Subsequently, it performs OCR on each image,
        with fallback OCR configurations if initial attempts yield insufficient text.

        Args:
            pdf_path (Path): Path to the PDF file.

        Returns:
            list or None: List of extracted text strings per page if successful, None otherwise.
        """
        # First attempt with the initial DPI
        images = self.convert_pdf_to_images(pdf_path, self.initial_dpi)
        if images is None:
            # Second attempt with a reduced DPI
            images = self.convert_pdf_to_images(pdf_path, self.retry_dpi)
            if images is None:
                self.logger.error(f"❌ Failed to convert {pdf_path.name} to images with all attempted DPIs.")
                return None

        ocr_texts = []
        for i, image in enumerate(images, 1):
            self.logger.info(f"🔍 Performing OCR on page {i}/{len(images)} of {pdf_path.name}")
            try:
                processed_img = self.preprocess_image(image)
            except Exception as e:
                self.logger.error(f"⚠️ Image preprocessing failed for page {i} of {pdf_path.name}: {str(e)}")
                ocr_texts.append("")
                continue

            try:
                text = pytesseract.image_to_string(
                    processed_img,
                    lang='fra+eng',
                    config='--psm 1'
                )
                if len(text.strip()) < 100:
                    self.logger.info(f"🔄 Insufficient OCR output for page {i} of {pdf_path.name}, retrying with different config")
                    text = pytesseract.image_to_string(
                        processed_img,
                        lang='fra+eng',
                        config='--psm 3 --oem 1'
                    )
                ocr_texts.append(text)
            except Exception as e:
                self.logger.error(f"❌ OCR failed for page {i} of {pdf_path.name}: {str(e)}")
                ocr_texts.append("")

        return ocr_texts

    def extract_text_with_pypdf_per_page(self, pdf_path, page_num):
        """
        Extract text from a specific page of a PDF using PyPDF.

        Args:
            pdf_path (Path): Path to the PDF file.
            page_num (int): The page number from which to extract text.

        Returns:
            str: Extracted text if successful, empty string otherwise.
        """
        try:
            with open(pdf_path, 'rb') as file:
                reader = pypdf.PdfReader(file)
                if page_num < 1 or page_num > len(reader.pages):
                    self.logger.error(f"⚠️ Invalid page number: {page_num} in {pdf_path.name}")
                    return ''
                page = reader.pages[page_num - 1]
                text = page.extract_text() or ''
                self.logger.info(f"📝 Extracted PyPDF text from page {page_num} of {pdf_path.name}: {len(text)} characters")
                return text
        except Exception as e:
            self.logger.error(f"❌ PyPDF error on page {page_num} of {pdf_path.name}: {str(e)}")
            return ''

    def get_api_key(self):
        """
        Retrieve an API key from the queue.

        This method fetches an API key from the `api_keys` queue to handle
        API rate limiting by cycling through available keys.

        Returns:
            str or None: An API key if available, None otherwise.
        """
        try:
            api_key = self.api_keys.get(timeout=10)
            return api_key
        except Empty:
            self.logger.error("🚫 No API keys available.")
            return None

    def process_with_gpt(self, content):
        """
        Process the given text content using GPT-4 to structure it into Markdown.

        The method sends the content to the GPT-4 model with a system prompt guiding
        the formatting and structuring rules. It handles API responses and rate limiting.

        Args:
            content (str): The raw text content to be processed.

        Returns:
            str or None: The structured Markdown content if successful, None otherwise.
        """
        system_prompt = {
            "role": "system",
            "content": (
                "You are a document analysis expert. Your task is to: "
                "1. Extract and structure key information from the provided text following these rules:\n"
                "   - Create a clear hierarchy with titles (# ## ###)\n"
                "   - Separate sections with line breaks\n"
                "   - Ensure consistency in presentation\n\n"
                "2. For tables:\n"
                "   - Convert each row into list items\n"
                "   - Use the format '- **[Column Name]:** [Value]'\n"
                "   - Group related items with indentation\n"
                "   - Add '---' separators between groups\n\n"
                "3. Apply the following formatting:\n"
                "   - Use italics (*) for important terms\n"
                "   - Use bold (**) for column headers\n"
                "   - Create bullet lists (-) for enumerations\n"
                "   - Use blockquotes (>) for important notes\n\n"
                "4. Clean and improve the text:\n"
                "   - Correct OCR typos\n"
                "   - Unify punctuation\n"
                "   - Remove unwanted characters\n"
                "   - Check alignment and spacing\n\n"
                "Example transformation:\n"
                "Table: 'Product | Price | Stock\n"
                "         Apples | 2.50 | 100\n"
                "         Pears | 3.00 | 85'\n\n"
                "Becomes:\n"
                "### Product List\n\n"
                "- **Product:** Apples\n"
                "  - **Price:** 2.50€\n"
                "  - **Stock:** 100 units\n\n"
                "---\n\n"
                "- **Product:** Pears\n"
                "  - **Price:** 3.00€\n"
                "  - **Stock:** 85 units"
            )
        }

        api_key = self.get_api_key()
        if not api_key:
            return None

        headers = {
            "Authorization": f"Bearer {api_key}",
            "Content-Type": "application/json"
        }

        payload = {
            "model": "gpt-4",
            "messages": [
                system_prompt,
                {"role": "user", "content": content}
            ],
            "temperature": 0,
            "max_tokens": 16000,
            "top_p": 1,
            "frequency_penalty": 0,
            "presence_penalty": 0
        }

        try:
            response = requests.post(
                'https://api.openai.com/v1/chat/completions',
                headers=headers,
                json=payload,
                timeout=60
            )
            response.raise_for_status()
            processed_content = response.json()['choices'][0]['message']['content']
            time.sleep(1)  # Pause to respect rate limits
            return processed_content
        except Exception as e:
            self.logger.error(f"❌ GPT API error: {str(e)}")
            return None
        finally:
            # Return the API key back to the queue
            if api_key:
                self.api_keys.put(api_key)

    def split_content(self, content, max_length=4000):
        """
        Split the content into smaller chunks if it exceeds the maximum length.

        The method ensures that each chunk is within the specified `max_length` by splitting
        based on paragraph breaks and maintaining an overlap for context continuity.

        Args:
            content (str): The text content to split.
            max_length (int, optional): Maximum length of each chunk. Defaults to 4000.

        Returns:
            list: A list of text chunks.
        """
        try:
            paragraphs = content.split('\n\n')
            parts = []
            current_part = ""
            for para in paragraphs:
                if len(current_part) + len(para) + 2 > max_length:
                    if current_part:
                        parts.append(current_part.strip())
                    current_part = para + '\n\n'
                else:
                    current_part += para + '\n\n'
            if current_part.strip():
                parts.append(current_part.strip())
            return parts
        except Exception as e:
            self.logger.error(f"Error splitting text: {str(e)}")
            return [content]  # Return the full text in case of error

    def process_single_part(self, document_name, page_num, part_num, content):
        """
        Process a single part of the content with GPT-4.

        This method structures the content into Markdown and saves it to an output file.

        Args:
            document_name (str): Name of the document being processed.
            page_num (int): Page number of the document.
            part_num (int): Part number within the page.
            content (str): The text content to process.
        """
        self.logger.info(f"📝 Processing Document: {document_name}, Page: {page_num}, Part: {part_num}")
        processed_content = self.process_with_gpt(content)

        if processed_content:
            output_file_name = self.output_dir / f"{document_name}_page_{page_num}_part_{part_num}.txt"
            try:
                with open(output_file_name, 'a', encoding='utf-8') as f:
                    f.write(f"📄 Document ID: {document_name}\n\n{processed_content}\n\n")
                self.logger.info(f"✅ File created: {output_file_name.name}")
            except Exception as e:
                self.logger.error(f"❌ Error saving Document: {document_name}, Page: {page_num}, Part: {part_num}: {str(e)}")

    def process_pdf(self, pdf_path):
        """
        Process an individual PDF file by extracting text and structuring it.

        The method handles both OCR-based and direct text extraction, splits the content
        into manageable chunks, and processes each chunk with GPT-4.

        Args:
            pdf_path (Path): Path to the PDF file to process.

        Returns:
            bool: True if processing was successful, False otherwise.
        """
        document_name = pdf_path.stem
        self.logger.info(f"📂 Starting processing of {pdf_path.name}")

        # Extract text using OCR
        ocr_texts = self.extract_text_with_ocr(pdf_path)
        if ocr_texts is None:
            self.logger.error(f"❌ OCR extraction failed for {pdf_path.name}")
            return False

        with ThreadPoolExecutor(max_workers=self.max_workers) as executor:
            futures = []
            for page_num, ocr_text in enumerate(ocr_texts, 1):
                self.logger.info(f"🔄 Preparing page {page_num}/{len(ocr_texts)} of {pdf_path.name}")

                if ocr_text and len(ocr_text.strip()) >= 100:
                    page_text = ocr_text
                    self.logger.info(f"✅ OCR succeeded for page {page_num} of {pdf_path.name}")
                else:
                    self.logger.info(f"🔄 Insufficient OCR for page {page_num} of {pdf_path.name}, using PyPDF")
                    pypdf_text = self.extract_text_with_pypdf_per_page(pdf_path, page_num)
                    page_text = pypdf_text

                if not page_text.strip():
                    self.logger.warning(f"⚠️ No text extracted for page {page_num} of {pdf_path.name}")
                    continue  # Skip to next page if no text is extracted

                # Split text if too long
                parts = self.split_content(page_text, max_length=4000)  # Adjust max_length if necessary

                for idx, part in enumerate(parts, 1):
                    futures.append(executor.submit(
                        self.process_single_part, document_name, page_num, idx, part
                    ))

            # Wait for all tasks to complete
            for future in as_completed(futures):
                pass  # Logging is handled within individual tasks

        self.logger.info(f"✅ Completed processing of {pdf_path.name}")
        return True

    def process_all_pdfs(self):
        """
        Process all PDF files in the input directory.

        The method iterates through each PDF file, processing them concurrently
        using a thread pool for efficiency. Progress is displayed using a rich Progress bar.
        """
        pdf_files = list(self.input_dir.glob('*.pdf'))
        total_files = len(pdf_files)

        self.logger.info(f"📢 Starting processing of {total_files} PDF files in '{self.input_dir}'")

        with Progress(
            SpinnerColumn(),
            TextColumn("[progress.description]{task.description}"),
            BarColumn(),
            "[progress.percentage]{task.percentage:>3.0f}%",
            TimeElapsedColumn(),
            TimeRemainingColumn(),
            console=Console()
        ) as progress:
            pdf_progress = progress.add_task("[green]Processing PDFs...", total=total_files)
            for pdf_path in pdf_files:
                self.process_pdf(pdf_path)
                progress.update(pdf_progress, advance=1)

        self.logger.info(f"🎉 Completed. Processed {total_files} PDF files.")


class EmbeddingProcessor:
    """
    A class for processing text embeddings using OpenAI's API.

    This processor handles the chunking of text, contextualization using GPT-4,
    and embedding generation. It manages API rate limits by cycling through
    multiple API keys and supports concurrent processing for efficiency.

    Attributes:
        input_dir (Path): Directory containing input text files.
        output_dir (Path): Directory where embeddings and metadata are saved.
        all_embeddings (list): List to store all generated embeddings.
        all_metadata (list): List to store metadata associated with each embedding.
        openai_api_keys (list): List of OpenAI API keys for cycling.
        headers_cycle (cycle): Iterator cycling through API headers based on the keys.
        lock (threading.Lock): Thread lock to synchronize access to shared resources.
        logger (logging.Logger): Logger for recording actions and errors.
        verbose (bool): Flag to enable verbose logging.
    """

    def __init__(self, input_dir, output_dir, openai_api_keys, verbose=False, logger=None):
        """
        Initialize the EmbeddingProcessor with necessary configurations.

        Args:
            input_dir (str or Path): Directory containing input text files.
            output_dir (str or Path): Directory to save embeddings and metadata.
            openai_api_keys (list): List of OpenAI API keys for cycling.
            verbose (bool, optional): Flag to enable verbose logging. Defaults to False.
            logger (logging.Logger, optional): Logger for logging information and errors. Defaults to None.
        """
        # Configure paths
        self.input_dir = Path(input_dir)
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)

        # Initialize global lists for all files
        self.all_embeddings = []
        self.all_metadata = []

        # Configure OpenAI API
        self.openai_api_keys = openai_api_keys
        self.headers_cycle = cycle([
            {
                "Authorization": f"Bearer {key}",
                "Content-Type": "application/json"
            } for key in self.openai_api_keys
        ])
        self.lock = threading.Lock()

        # Configure logging
        self.logger = logger or logging.getLogger(__name__)
        self.verbose = verbose

    def chunk_text(self, text, chunk_size=1200, overlap_size=100):
        """
        Split text into smaller chunks with overlapping regions.

        This method ensures that each chunk is within the specified `chunk_size`, adding
        an overlap of `overlap_size` tokens to maintain context between chunks.

        It also handles cases where the text is shorter than the chunk size.

        Args:
            text (str): The text to be split.
            chunk_size (int, optional): Maximum number of tokens per chunk. Defaults to 1200.
            overlap_size (int, optional): Number of overlapping tokens between chunks. Defaults to 100.

        Returns:
            list: List of text chunks.
        """
        try:
            tokens = text.split()

            # If text is shorter than chunk size, process as a single chunk
            if len(tokens) <= chunk_size:
                return [text]

            chunks = []
            for i in range(0, len(tokens), chunk_size - overlap_size):
                chunk = ' '.join(tokens[i:i + chunk_size])
                chunks.append(chunk)

            # Ensure the last chunk isn't too small
            if len(chunks) > 1 and len(tokens[-(chunk_size - overlap_size):]) < chunk_size // 2:
                # Merge the last chunk with the previous one if it's too small
                last_chunk = ' '.join(tokens[-(chunk_size):])
                chunks[-1] = last_chunk

            return chunks

        except Exception as e:
            self.logger.error(f"Error splitting text: {str(e)}")
            return [text]  # Return full text in case of error

    def get_contextualized_chunk(self, chunk, full_text, headers, document_name, page_num, chunk_id):
        """
        Obtain contextual information for a text chunk using GPT-4.

        The method sends a system prompt and the chunk to GPT-4 to generate contextual
        information that enhances understanding of the chunk within the larger document.

        Args:
            chunk (str): The text chunk to contextualize.
            full_text (str): The complete text of the document for reference.
            headers (dict): HTTP headers containing the API authorization.
            document_name (str): Name of the document being processed.
            page_num (int): Page number within the document.
            chunk_id (int): Identifier for the chunk within the page.

        Returns:
            str or None: The contextual information generated by GPT-4 if successful, None otherwise.
        """
        try:
            system_prompt = {
                "role": "system",
                "content": (
                    "You are an expert analyst. The following text is an excerpt from a larger document. "
                    "Your task is to provide context for the next section by referencing the overall document content. "
                    "Ensure the context helps in better understanding the excerpt."
                )
            }
            user_prompt = {
                "role": "user",
                "content": f"Document: {full_text}\n\nChunk: {chunk}\n\nPlease provide context for this excerpt in French."
            }

            payload = {
                "model": "gpt-4",
                "messages": [system_prompt, user_prompt],
                "temperature": 0,
                "max_tokens": 200,
                "top_p": 1,
                "frequency_penalty": 0,
                "presence_penalty": 0
            }

            if self.verbose:
                self.logger.info(f"Calling LLM for {document_name} page {page_num}, chunk {chunk_id}")

            self.logger.info(f"Initiating GPT API call for {document_name} page {page_num} chunk {chunk_id}")

            response = requests.post(
                'https://api.openai.com/v1/chat/completions',
                headers=headers,
                json=payload,
                timeout=60
            )
            response.raise_for_status()
            return response.json()['choices'][0]['message']['content']

        except Exception as e:
            self.logger.error(f"Error during contextualization: {str(e)}")
            return None

    def get_embedding(self, text, headers, document_name, page_num, chunk_id):
        """
        Obtain an embedding vector for a given text using OpenAI's Embedding API.

        The method sends the text to the Embedding API and retrieves the corresponding
        embedding. It handles exceptions and logs any errors encountered.

        Args:
            text (str): The text to embed.
            headers (dict): HTTP headers containing the API authorization.
            document_name (str): Name of the document being processed.
            page_num (int): Page number within the document.
            chunk_id (int): Identifier for the chunk within the page.

        Returns:
            list or None: The embedding vector if successful, None otherwise.
        """
        try:
            payload = {
                "input": text,
                "model": "text-embedding-ada-002",  # Use the appropriate embedding model
                "encoding_format": "float"
            }

            if self.verbose:
                self.logger.info(f"Calling Embedding API for {document_name} page {page_num} chunk {chunk_id}")

            self.logger.info(f"🔗 Calling Embedding API for {document_name} page {page_num} chunk {chunk_id}")

            response = requests.post(
                'https://api.openai.com/v1/embeddings',
                headers=headers,
                json=payload,
                timeout=60
            )
            response.raise_for_status()
            return response.json()['data'][0]['embedding']

        except Exception as e:
            self.logger.error(f"Error retrieving embedding: {str(e)}")
            return None

    def process_chunk(self, chunk_info):
        """
        Process a specific text chunk by contextualizing and embedding it.

        This method handles the entire pipeline for a single chunk:
            1. Obtaining contextual information from GPT-4.
            2. Combining context with the original chunk.
            3. Generating an embedding for the combined text.
            4. Storing the embedding and associated metadata.

        Args:
            chunk_info (tuple): A tuple containing:
                - txt_file_path (Path): Path to the text file.
                - chunk_id (int): Identifier for the chunk.
                - chunk (str): The text content of the chunk.
                - full_text (str): The complete text of the document.
                - document_name (str): Name of the document.
                - page_num (int): Page number within the document.

        Returns:
            tuple: A tuple containing the embedding and its metadata if successful, (None, None) otherwise.
        """
        try:
            txt_file_path, chunk_id, chunk, full_text, document_name, page_num = chunk_info

            with self.lock:
                headers = next(self.headers_cycle)

            context = self.get_contextualized_chunk(chunk, full_text, headers, document_name, page_num, chunk_id)
            if not context:
                return None, None

            combined_text = f"{context}\n\nContext:\n{chunk}"
            embedding = self.get_embedding(combined_text, headers, document_name, page_num, chunk_id)

            if embedding:
                metadata = {
                    "filename": txt_file_path.name,
                    "chunk_id": chunk_id,
                    "page_num": page_num,
                    "text_raw": chunk,
                    "context": context,
                    "text": combined_text
                }
                return embedding, metadata

            return None, None

        except Exception as e:
            self.logger.error(f"Error processing chunk: {str(e)}")
            return None, None

    def process_file(self, txt_file_path):
        """
        Prepare chunk information from a single text file for embedding.

        This method reads the entire text file, splits it into chunks, and organizes
        the necessary information for each chunk to be processed.

        Args:
            txt_file_path (Path): Path to the text file.

        Returns:
            list: A list of tuples containing chunk information for processing.
        """
        try:
            self.logger.info(f"📂 Processing file: {txt_file_path}")

            with open(txt_file_path, 'r', encoding='utf-8') as file:
                full_text = file.read()

            chunks = self.chunk_text(full_text)

            # Extract page number from filename
            match = re.search(r'_page_(\d+)_', txt_file_path.stem)
            if match:
                page_num = int(match.group(1))
            else:
                page_num = 1  # Default if not found

            chunk_infos = [
                (txt_file_path, i, chunk, full_text, txt_file_path.stem, page_num)
                for i, chunk in enumerate(chunks, 1)
            ]

            return chunk_infos

        except Exception as e:
            self.logger.error(f"Error processing file {txt_file_path}: {str(e)}")
            return []

    def process_all_files(self):
        """
        Process all text files in the input directory to generate embeddings.

        The method iterates through each text file, prepares chunks, and processes
        them concurrently using a thread pool. It aggregates all embeddings and
        associated metadata, saving them to designated output files.
        """
        try:
            txt_files = list(self.input_dir.glob('*.txt'))
            total_files = len(txt_files)
            self.logger.info(f"📢 Starting processing of {total_files} files in '{self.input_dir}'")

            with ThreadPoolExecutor(max_workers=self.max_workers) as executor:
                futures = []
                for txt_file_path in txt_files:
                    chunk_infos = self.process_file(txt_file_path)
                    for chunk_info in chunk_infos:
                        futures.append(executor.submit(self.process_chunk, chunk_info))

                for future in as_completed(futures):
                    embedding, metadata = future.result()
                    if embedding and metadata:
                        self.all_embeddings.append(embedding)
                        self.all_metadata.append(metadata)

            if self.all_embeddings:
                # Save results
                chunks_json_path = self.output_dir / "chunks.json"
                with open(chunks_json_path, 'w', encoding='utf-8') as json_file:
                    json.dump({"metadata": self.all_metadata}, json_file, ensure_ascii=False, indent=4)

                embeddings_npy_path = self.output_dir / "embeddings.npy"
                np.save(embeddings_npy_path, np.array(self.all_embeddings))

                self.logger.info(f"✅ Files created: {chunks_json_path} and {embeddings_npy_path}")

        except Exception as e:
            self.logger.error(f"Error processing files: {str(e)}")
            raise


class IntegrationManager:
    """
    A manager class to integrate the web crawling, PDF extraction, and embedding processing components.

    This class orchestrates the entire pipeline by initializing each component with
    the provided configuration, setting up logging, and executing each processing phase
    in sequence. It ensures that all components work together seamlessly and handles
    any errors that occur during the integrated process.

    Attributes:
        crawler_config (dict): Configuration settings for the WebCrawler.
        extractor_config (dict): Configuration settings for the PDFExtractor.
        embedding_config (dict): Configuration settings for the EmbeddingProcessor.
        logger (logging.Logger): Logger for recording actions and errors.
        crawler (WebCrawler): Instance of the WebCrawler.
        extractor (PDFExtractor): Instance of the PDFExtractor.
        embedding (EmbeddingProcessor): Instance of the EmbeddingProcessor.
    """

    def __init__(self, config):
        """
        Initialize the IntegrationManager with a configuration dictionary.

        Args:
            config (dict): Dictionary containing configuration settings for all components.
        """
        # Load settings from the configuration dictionary
        self.crawler_config = config.get('crawler', {})
        self.extractor_config = config.get('extractor', {})
        self.embedding_config = config.get('embedding', {})

        # Set up logging based on configuration
        self.setup_logging(config.get('logging', {}))
        self.logger = logging.getLogger('IntegrationManager')

        # Initialize the WebCrawler
        self.crawler = WebCrawler(
            start_url=self.crawler_config.get('start_url'),
            max_depth=self.crawler_config.get('max_depth', 2),
            use_playwright=self.crawler_config.get('use_playwright', False),
            excluded_paths=self.crawler_config.get('excluded_paths'),
            download_extensions=self.crawler_config.get('download_extensions'),
            language_pattern=self.crawler_config.get('language_pattern'),
            base_dir=self.crawler_config.get('base_dir')
        )

        # Initialize the PDFExtractor
        self.extractor = PDFExtractor(
            input_dir=self.extractor_config.get('input_dir'),
            output_dir=self.extractor_config.get('output_dir'),
            api_keys_file=self.extractor_config.get('api_keys_file'),
            max_workers=self.extractor_config.get('max_workers', 10),
            initial_dpi=self.extractor_config.get('initial_dpi', 300),
            retry_dpi=self.extractor_config.get('retry_dpi', 200),
            logger=self.logger
        )

        # Initialize the EmbeddingProcessor
        self.embedding = EmbeddingProcessor(
            input_dir=self.embedding_config.get('input_dir'),
            output_dir=self.embedding_config.get('output_dir'),
            openai_api_keys=self.embedding_config.get('openai_api_keys'),
            verbose=self.embedding_config.get('verbose', False),
            logger=self.logger
        )

    def setup_logging(self, logging_config):
        """
        Configure the logging system based on the provided configuration.

        The method sets the logging level, format, and file handler to ensure that
        all components log their actions consistently.

        Args:
            logging_config (dict): Dictionary containing logging configuration settings.
        """
        log_level = logging_config.get('level', 'INFO').upper()
        log_format = logging_config.get('format', '%(asctime)s - %(levelname)s - %(message)s')
        log_file = logging_config.get('file', 'integration_manager.log')

        logging.basicConfig(
            level=log_level,
            format=log_format,
            handlers=[
                logging.FileHandler(log_file),
                logging.StreamHandler()
            ]
        )

    def run_crawling(self):
        """
        Execute the web crawling phase.

        This method starts the crawling process using the configured WebCrawler,
        which extracts URLs and content from the target website.
        """
        self.logger.info("🛠️  Starting crawling phase")
        self.crawler.crawl()
        self.logger.info("✅ Crawling phase completed")

    def run_extraction(self):
        """
        Execute the PDF/DOC extraction phase.

        This method starts the extraction process using the configured PDFExtractor,
        which converts PDFs to text and structures the content.
        """
        self.logger.info("🛠️  Starting PDF/DOC extraction phase")
        self.extractor.process_all_pdfs()
        self.logger.info("✅ PDF/DOC extraction phase completed")

    def run_embedding(self):
        """
        Execute the embedding processing phase.

        This method starts the embedding process using the configured EmbeddingProcessor,
        which generates embeddings for the extracted text and saves them for future use.
        """
        self.logger.info("🛠️  Starting embedding processing phase")
        self.embedding.process_all_files()
        self.logger.info("✅ Embedding processing phase completed")

    def run_all(self):
        """
        Run all integrated processing phases in sequence.

        This method orchestrates the entire workflow by sequentially executing
        crawling, extraction, and embedding phases. It ensures that each phase
        completes successfully before moving to the next and logs the overall process.
        """
        try:
            self.run_crawling()
            self.run_extraction()
            self.run_embedding()
            self.logger.info("🎉 All integrated processes completed successfully")
        except Exception as e:
            self.logger.error(f"❌ Error during integrated process: {str(e)}")
            raise


def main():
    """
    The main function to execute the integrated web crawling, extraction, and embedding process.

    This function performs the following steps:
        1. Load environment variables if necessary.
        2. Define the configuration settings for all components.
        3. Check for the availability of OpenAI API keys.
        4. Initialize the IntegrationManager with the configuration.
        5. Execute all processing phases in sequence.
        6. Handle any initialization or runtime errors gracefully.

    Notes:
        - Ensure that the 'api_keys.txt' file exists and contains valid OpenAI API keys.
        - Adjust the configuration parameters as needed to fit specific requirements.
    """
    # Load environment variables if necessary
    load_dotenv()

    # Define the configuration settings
    config = {
        'crawler': {
            'start_url': "https://liquid-air.ca",
            'max_depth': 3,
            'use_playwright': True,
            'excluded_paths': ['selecteur-de-produits'],
            'download_extensions': {
                'PDF': ['.pdf'],
                'Image': ['.png', '.jpg', '.jpeg', '.gif', '.svg'],
                'Doc': ['.doc', '.docx', '.xls', '.xlsx', '.ppt', '.pptx']
            },
            'language_pattern': re.search(r'/(fr|en)-(ca|us)/', "https://liquid-air.ca"),  # Adjust as needed
            'base_dir': "crawler_output"  # Optional, otherwise auto-generated
        },
        'extractor': {
            'input_dir': "crawler_output/PDF",
            'output_dir': "extraction_output/content",
            'api_keys_file': "api_keys.txt",
            'max_workers': 10,
            'initial_dpi': 300,
            'retry_dpi': 200
        },
        'embedding': {
            'input_dir': "extraction_output/content",
            'output_dir': "embeddings_output",
            'openai_api_keys': [key.strip() for key in open('api_keys.txt').readlines() if key.strip()],
            'verbose': False
        },
        'logging': {
            'level': 'INFO',
            'format': '%(asctime)s - %(levelname)s - %(message)s',
            'file': 'integration_manager.log'
        }
    }

    # Check for OpenAI API keys
    if not config['embedding']['openai_api_keys']:
        print("🚫 No OpenAI API keys found. Please check the 'api_keys.txt' file.")
        return

    # Initialize and run the integration manager
    try:
        manager = IntegrationManager(config)
        manager.run_all()
    except Exception as e:
        print(f"❌ Integration error: {str(e)}")
        sys.exit(1)


if __name__ == "__main__":
    main()
