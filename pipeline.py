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

# Initialisation des modules Rich pour les tracebacks
install()

# Initialisation Colorama
init(autoreset=True)

# Classe pour un formatteur de logs colorés
class ColoredFormatter(logging.Formatter):
    """Formatter personnalisé pour ajouter des couleurs, des symboles et des '#' à la fin des logs."""

    # Définition des couleurs et symboles
    COLORS = {
        'DEBUG': Fore.CYAN,
        'INFO': Fore.GREEN,
        'WARNING': Fore.YELLOW,
        'ERROR': Fore.RED,
        'CRITICAL': Fore.RED + Style.BRIGHT
    }

    SYMBOLS = {
        'INFO': '✔',
        'WARNING': '⚠',
        'ERROR': '✘',
        'CRITICAL': '✘'
    }

    def format(self, record):
        color = self.COLORS.get(record.levelname, Fore.WHITE)
        symbol = self.SYMBOLS.get(record.levelname, '')
        # Format initial avec le symbole et le timestamp, suivi de '#'
        header = f"{color}{symbol} {self.formatTime(record, self.datefmt)}#"
        # Niveau de log, suivi de '#'
        level = f"- {record.levelname}#"
        # Message, suivi de '#'
        message = f"- {record.getMessage()}#"
        return f"{header}\n{level}\n{message}"

# Classe pour afficher un indicateur dynamique dans le terminal
class MovingIndicator(threading.Thread):
    """Thread pour afficher un indicateur dynamique se déplaçant de droite à gauche avec des '#' à la fin."""

    def __init__(self, delay=0.1, length=20):
        super().__init__()
        self.delay = delay
        self.length = length
        self.running = False
        self.position = self.length - 1  # Commencer à droite
        self.direction = -1  # Déplacer vers la gauche

    def run(self):
        self.running = True
        while self.running:
            # Créer la représentation de l'indicateur
            line = [' '] * self.length
            if 0 <= self.position < self.length:
                line[self.position] = '#'
            indicator = ''.join(line) + '##'  # Ajouter '##' à la fin pour dynamisme
            # Afficher l'indicateur
            sys.stdout.write(f"\r{indicator}")
            sys.stdout.flush()
            # Mettre à jour la position
            self.position += self.direction
            if self.position == 0 or self.position == self.length - 1:
                self.direction *= -1  # Changer de direction
            time.sleep(self.delay)

    def stop(self):
        self.running = False
        self.join()
        # Nettoyer la ligne de l'indicateur
        sys.stdout.write('\r' + ' ' * (self.length + 2) + '\r')  # +2 pour les '##'
        sys.stdout.flush()

# Classe pour le Crawling Web
class WebCrawler:
    def __init__(self, start_url, max_depth=2, use_playwright=False, excluded_paths=None, download_extensions=None, language_pattern=None, base_dir=None):
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
        """Configure une session requests avec retry et timeouts"""
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
        session.verify = False  # Pour désactiver la vérification SSL si nécessaire
        session.headers.update({
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) '
                          'AppleWebKit/537.36 (KHTML, like Gecko) '
                          'Chrome/91.0.4472.124 Safari/537.36'
        })
        return session

    def create_directories(self):
        """Crée la structure de dossiers nécessaire pour le crawler"""
        directories = ['content', 'PDF', 'Image', 'Doc', 'logs']
        for dir_name in directories:
            path = os.path.join(self.base_dir, dir_name)
            os.makedirs(path, exist_ok=True)

    def setup_logging(self):
        """Configure le système de logging avec couleurs, symboles et '#' à la fin des lignes"""
        log_format = '%(asctime)s - %(levelname)s - %(message)s'
        formatter = ColoredFormatter(log_format)

        logger = logging.getLogger()
        logger.setLevel(logging.INFO)

        # Handler pour le fichier log (sans couleurs)
        file_handler = logging.FileHandler(os.path.join(self.base_dir, 'logs', 'crawler.log'), encoding='utf-8')
        file_handler.setFormatter(logging.Formatter(log_format))
        logger.addHandler(file_handler)

        # Handler pour la console (avec couleurs)
        console_handler = logging.StreamHandler()
        console_handler.setFormatter(formatter)
        logger.addHandler(console_handler)

        # Marqueur de début
        logging.info(f"Démarrage du crawler avec le pattern de langue : {self.language_pattern}")

    def should_exclude(self, url):
        """Détermine si une URL doit être exclue en fonction des segments définis"""
        for excluded in self.excluded_paths:
            if excluded in url:
                return True
        return False

    def is_same_language(self, url):
        """Vérifie si l'URL respecte le même pattern linguistique que l'URL de départ"""
        if not self.language_pattern:
            return True
        return self.language_pattern in url

    def is_downloadable_file(self, url):
        """Vérifie si l'URL pointe vers un fichier téléchargeable en utilisant des expressions régulières."""
        parsed_url = urlparse(url)
        path = parsed_url.path.lower()
        # Créer un pattern regex pour détecter les extensions, même avec des suffixes comme .pdf.aspx
        pattern = re.compile(r'\.(' + '|'.join([ext.strip('.') for exts in self.downloadable_extensions.values() for ext in exts]) + r')(\.[a-z0-9]+)?$', re.IGNORECASE)
        return bool(pattern.search(path))

    def get_file_type_and_extension(self, url, response):
        """
        Détermine le type de fichier et l'extension appropriée en fonction de l'URL et du Content-Type.
        Retourne un tuple (file_type, extension).
        """
        parsed_url = urlparse(url)
        path = parsed_url.path.lower()

        # Première tentative : déduire le type de fichier basé sur l'URL
        for file_type, extensions in self.downloadable_extensions.items():
            for ext in extensions:
                # Adapter le pattern pour inclure des suffixes comme .aspx
                pattern = re.compile(re.escape(ext) + r'(\.[a-z0-9]+)?$', re.IGNORECASE)
                if pattern.search(path):
                    return file_type, self.content_type_mapping[file_type].get(response.headers.get('Content-Type', '').lower(), ext)

        # Seconde tentative : déduire le type de fichier basé sur le Content-Type
        content_type = response.headers.get('Content-Type', '').lower()
        for file_type, mapping in self.content_type_mapping.items():
            if content_type in mapping:
                return file_type, mapping[content_type]

        # Si aucun type n'est déterminé, retourner None
        return None, None

    def sanitize_filename(self, url, file_type, extension, page_number=None):
        """Crée un nom de fichier sécurisé à partir de l'URL, en ajustant l'extension si nécessaire."""
        # Création d'un hash court de l'URL
        url_hash = hashlib.md5(url.encode()).hexdigest()[:8]

        # Extraction du dernier segment de l'URL
        filename = url.split('/')[-1]
        if not filename:
            filename = 'index'

        # Nettoyage du nom de fichier
        filename = re.sub(r'[^\w\-_.]', '_', filename)

        # Suppression des extensions existantes
        name, _ = os.path.splitext(filename)

        # Définir l'extension en fonction du type de fichier
        if not extension:
            extension = '.txt'  # Extension par défaut si non déterminée

        if page_number is not None:
            sanitized = f"{name}_page_{page_number:03d}_{url_hash}{extension}"
        else:
            sanitized = f"{name}_{url_hash}{extension}"

        logging.debug(f"Nom de fichier sanitizé: {sanitized}")
        return sanitized

    def download_file(self, url, file_type):
        """Télécharge un fichier et le sauvegarde dans le dossier approprié."""
        try:
            logging.info(f"Tentative de téléchargement de fichier {file_type} depuis : {url}")

            # Déterminer le type de fichier et l'extension
            response = self.session.head(url, allow_redirects=True, timeout=10)
            file_type_detected, extension = self.get_file_type_and_extension(url, response)
            if not file_type_detected:
                logging.warning(f"⚠ Impossible de déterminer le type de fichier pour : {url}")
                return False

            # Renommer le fichier correctement
            filename = self.sanitize_filename(url, file_type_detected, extension)
            save_path = os.path.join(self.base_dir, file_type_detected, filename)

            # Vérifier si le fichier existe déjà
            if os.path.exists(save_path):
                logging.info(f"📂 Fichier déjà téléchargé, passage : {filename}")
                return False

            # Télécharger le fichier avec une barre de progression
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
                logging.warning(f"⚠ Téléchargement incomplet pour {url}")
                return False

            self.stats[f'{file_type_detected}_downloaded'] += 1
            self.downloaded_files.add(url)
            logging.info(f"✅ Téléchargement réussi de {file_type_detected} : {filename}")
            return True

        except Exception as e:
            logging.error(f"✘ Erreur lors du téléchargement de {url} : {str(e)}")
            return False

    def convert_links_to_absolute(self, soup, base_url):
        """Convertit tous les liens relatifs en liens absolus."""
        # Inclure les balises <embed>, <iframe>, et <object> en plus des <a> et <link>
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
        """Nettoie et formate le texte en réduisant les espaces inutiles tout en conservant une séparation claire."""
        if not text:
            return ""

        # Suppression des caractères spéciaux inutiles
        text = re.sub(r'[\x00-\x08\x0B\x0C\x0E-\x1F\x7F-\x9F]', '', text)

        # Normalisation des espaces (remplacer les espaces multiples par un seul espace)
        text = re.sub(r'[ \t]+', ' ', text)

        # Normalisation des nouvelles lignes (remplacer les sauts de ligne multiples par deux sauts de ligne)
        text = re.sub(r'\n\s*\n', '\n\n', text)

        return text.strip()

    def fetch_page_content(self, url):
        """Récupère le contenu d'une page en utilisant Playwright ou requests."""
        if self.use_playwright:
            try:
                logging.info(f"🔍 Récupération avec Playwright : {url}")
                self.page.goto(url, timeout=20000)
                time.sleep(2)  # Attendre que la page soit complètement chargée
                content = self.page.content()
                return content
            except Exception as e:
                logging.error(f"✘ Playwright a échoué à récupérer {url} : {str(e)}")
                return None
        else:
            try:
                response = self.session.get(url, timeout=20)
                if response.status_code == 200:
                    logging.info(f"✅ Contenu récupéré avec succès : {url}")
                    return response.text
                else:
                    logging.warning(f"⚠ Échec de récupération de {url} avec le code de statut {response.status_code}")
                    return None
            except Exception as e:
                logging.error(f"✘ Requests a échoué à récupérer {url} : {str(e)}")
                return None

    def extract_content(self, url):
        """Extrait le contenu d'une page et le sauvegarde en format markdown."""
        logging.info(f"📄 Extraction du contenu de : {url}")

        try:
            if self.is_downloadable_file(url):
                logging.info(f"🔗 Passage de l'extraction du contenu pour le fichier téléchargeable : {url}")
                return

            page_content = self.fetch_page_content(url)
            if page_content is None:
                logging.warning(f"⚠ Impossible de récupérer le contenu pour : {url}")
                return

            soup = BeautifulSoup(page_content, 'html.parser')

            # Suppression des éléments non désirés
            for element in soup.find_all(['nav', 'header', 'footer', 'script', 'style', 'aside', 'iframe']):
                element.decompose()

            # Extraction du contenu principal
            main_content = (
                soup.find('main') or
                soup.find('article') or
                soup.find('div', class_='content') or
                soup.find('div', id='content')
            )

            if main_content:
                # Conversion des liens relatifs en liens absolus
                main_content = self.convert_links_to_absolute(main_content, url)

                # Conversion du contenu principal en markdown
                markdown_content = self.html_converter.handle(str(main_content))

                # Construction du contenu final avec titre
                content_parts = []

                # Ajout du titre
                title = soup.find('h1')
                if title:
                    content_parts.append(f"# {title.get_text().strip()}")

                # Ajout de l'URL source
                content_parts.append(f"**Source:** {url}")

                # Ajout du contenu principal
                content_parts.append(markdown_content)

                # Nettoyage du contenu
                content = self.clean_text('\n\n'.join(content_parts))

                if content:
                    # Création du nom de fichier
                    filename = self.sanitize_filename(url, 'Doc', '.txt')  # Utiliser 'Doc' avec extension '.txt' pour les pages
                    save_path = os.path.join(self.base_dir, 'content', filename)
                    with open(save_path, 'w', encoding='utf-8') as f:
                        f.write(content)

                    self.stats['pages_processed'] += 1
                    logging.info(f"✅ Contenu sauvegardé avec succès dans : {filename}")
                else:
                    logging.warning(f"⚠ Aucun contenu significatif trouvé pour : {url}")

                # Traitement des fichiers téléchargeables trouvés dans la page
                downloadable_tags = main_content.find_all(['a', 'embed', 'iframe', 'object'], href=True)

                if downloadable_tags:
                    logging.info(f"🔄 Détection de {len(downloadable_tags)} fichiers téléchargeables dans la page.")

                for tag in downloadable_tags:
                    href = tag.get('href') or tag.get('src')
                    if href:
                        file_url = urljoin(url, href)
                        if self.is_downloadable_file(file_url) and file_url not in self.downloaded_files:
                            # Utiliser HEAD pour obtenir le Content-Type sans télécharger le fichier
                            try:
                                response_head = self.session.head(file_url, allow_redirects=True, timeout=10)
                                file_type_detected, _ = self.get_file_type_and_extension(file_url, response_head)
                            except:
                                # Fallback à GET si HEAD échoue
                                response_head = self.session.get(file_url, allow_redirects=True, timeout=10)
                                file_type_detected, _ = self.get_file_type_and_extension(file_url, response_head)

                            if file_type_detected:
                                # Renommer le fichier correctement
                                filename = self.sanitize_filename(file_url, file_type_detected, self.content_type_mapping[file_type_detected].get(response_head.headers.get('Content-Type', '').lower(), ''))
                                save_path = os.path.join(self.base_dir, file_type_detected, filename)

                                if os.path.exists(save_path):
                                    logging.info(f"📂 Fichier déjà téléchargé, passage : {filename}")
                                    continue

                                self.download_file(file_url, file_type_detected)

            else:
                logging.warning(f"⚠ Aucun contenu principal trouvé pour : {url}")

        except Exception as e:
            logging.error(f"✘ Erreur lors du traitement de {url} : {str(e)}")

    def extract_urls(self, start_url):
        """Extrait récursivement les URLs d'une page jusqu'à la profondeur maximale."""
        queue = deque()
        queue.append((start_url, 0))
        self.visited_pages.add(start_url)

        pbar = tqdm(total=1, desc="🔍 Extraction des URLs", unit="page", ncols=100)

        while queue:
            current_url, depth = queue.popleft()

            if depth > self.max_depth:
                pbar.update(1)
                continue

            # Vérifier si l'URL doit être exclue
            if self.should_exclude(current_url):
                logging.info(f"🚫 URL exclue en raison d'un segment exclu : {current_url}")
                pbar.update(1)
                continue

            logging.info(f"🔎 Extraction des URLs depuis : {current_url} (profondeur : {depth})")

            try:
                if self.is_downloadable_file(current_url):
                    # Utiliser HEAD pour obtenir le Content-Type sans télécharger le fichier
                    try:
                        response_head = self.session.head(current_url, allow_redirects=True, timeout=10)
                        file_type_detected, _ = self.get_file_type_and_extension(current_url, response_head)
                    except:
                        # Fallback à GET si HEAD échoue
                        response_head = self.session.get(current_url, allow_redirects=True, timeout=10)
                        file_type_detected, _ = self.get_file_type_and_extension(current_url, response_head)

                    if file_type_detected:
                        # Renommer le fichier pour vérifier l'existence
                        filename = self.sanitize_filename(current_url, file_type_detected, self.content_type_mapping[file_type_detected].get(response_head.headers.get('Content-Type', '').lower(), ''))
                        save_path = os.path.join(self.base_dir, file_type_detected, filename)

                        if os.path.exists(save_path):
                            logging.info(f"📂 Fichier déjà téléchargé, passage : {filename}")
                            pbar.update(1)
                            continue

                        self.download_file(current_url, file_type_detected)
                        self.downloaded_files.add(current_url)
                    pbar.update(1)
                    continue

                # Récupérer le contenu de la page (avec Playwright ou requests)
                page_content = self.fetch_page_content(current_url)
                if page_content is None:
                    logging.warning(f"⚠ Impossible de récupérer le contenu pour : {current_url}")
                    pbar.update(1)
                    continue

                soup = BeautifulSoup(page_content, 'html.parser')

                # Recherche de fichiers téléchargeables et de liens
                for tag in soup.find_all(['a', 'link', 'embed', 'iframe', 'object'], href=True):
                    href = tag.get('href') or tag.get('src')
                    if href:
                        absolute_url = urljoin(current_url, href)
                        parsed_url = urlparse(absolute_url)

                        # Vérification si c'est un fichier téléchargeable
                        if self.is_downloadable_file(absolute_url):
                            # Utiliser HEAD pour obtenir le Content-Type sans télécharger le fichier
                            try:
                                response_head = self.session.head(absolute_url, allow_redirects=True, timeout=10)
                                file_type_detected, _ = self.get_file_type_and_extension(absolute_url, response_head)
                            except:
                                # Fallback à GET si HEAD échoue
                                response_head = self.session.get(absolute_url, allow_redirects=True, timeout=10)
                                file_type_detected, _ = self.get_file_type_and_extension(absolute_url, response_head)

                            if file_type_detected:
                                # Renommer le fichier pour vérifier l'existence
                                filename = self.sanitize_filename(absolute_url, file_type_detected, self.content_type_mapping[file_type_detected].get(response_head.headers.get('Content-Type', '').lower(), ''))
                                save_path = os.path.join(self.base_dir, file_type_detected, filename)

                                if os.path.exists(save_path):
                                    logging.info(f"📂 Fichier déjà téléchargé, passage : {filename}")
                                    continue

                                self.download_file(absolute_url, file_type_detected)
                                self.downloaded_files.add(absolute_url)
                            continue

                        # Vérification des liens internes
                        if (self.domain in parsed_url.netloc and
                            self.is_same_language(absolute_url) and
                            absolute_url not in self.visited_pages and
                            not absolute_url.endswith(('#', 'javascript:void(0)', 'javascript:;')) and
                            not self.should_exclude(absolute_url)):

                            # Ajouter à la queue avec profondeur incrémentée
                            queue.append((absolute_url, depth + 1))
                            self.visited_pages.add(absolute_url)
                            pbar.total += 1  # Augmenter la barre de progression
                            pbar.refresh()

            except Exception as e:
                logging.error(f"✘ Erreur lors du crawling de {current_url} : {str(e)}")

            pbar.update(1)

        pbar.close()
        logging.info("🔍 Extraction des URLs terminée.")

    def crawl(self):
        """Méthode principale de crawling."""
        start_time = time.time()
        logging.info(f"🚀 Début du crawl de {self.start_url}")
        logging.info(f"🌐 Pattern de langue : {self.language_pattern}")
        logging.info(f"📏 Profondeur maximale : {self.max_depth}")

        # Charger les fichiers téléchargés précédemment
        self.load_downloaded_files()

        # Démarrer l'indicateur dynamique
        self.indicator.start()

        try:
            # Phase 1: Extraction des URLs
            logging.info("🔍 Phase 1 : Début de l'extraction des URLs")
            self.extract_urls(self.start_url)

            # Phase 2: Extraction du contenu
            logging.info("📄 Phase 2 : Début de l'extraction du contenu")
            visited_without_files = [url for url in self.visited_pages if not self.is_downloadable_file(url)]
            
            pbar_content = tqdm(total=len(visited_without_files), desc="📄 Extraction du Contenu", unit="page", ncols=100)
            for i, url in enumerate(visited_without_files, 1):
                logging.info(f"📝 Traitement de l'URL {i}/{len(visited_without_files)} : {url}")
                self.extract_content(url)
                pbar_content.update(1)
            pbar_content.close()
            logging.info("📄 Extraction du contenu terminée.")

            # Génération du rapport final
            end_time = time.time()
            self.generate_report(end_time - start_time)

        except Exception as e:
            logging.error(f"⚠ Erreur critique durant le crawling : {str(e)}")
            self.generate_report(time.time() - start_time, error=str(e))

        finally:
            # Arrêter l'indicateur dynamique
            self.indicator.stop()

            # Sauvegarder les fichiers téléchargés
            self.save_downloaded_files()

            # Fermer Playwright si utilisé
            if self.use_playwright:
                self.page.close()
                self.browser.close()
                self.playwright.stop()

    def load_downloaded_files(self):
        """Charge les URLs des fichiers déjà téléchargés depuis le fichier de suivi."""
        downloaded_files_path = os.path.join(self.base_dir, 'logs', 'downloaded_files.txt')
        if os.path.exists(downloaded_files_path):
            with open(downloaded_files_path, 'r', encoding='utf-8') as f:
                for line in f:
                    self.downloaded_files.add(line.strip())
            logging.info(f"📥 Chargé {len(self.downloaded_files)} fichiers téléchargés depuis le fichier de suivi.")
        else:
            logging.info("🆕 Aucun fichier de suivi des téléchargements trouvé, démarrage à zéro.")

    def save_downloaded_files(self):
        """Sauvegarde les URLs des fichiers téléchargés dans le fichier de suivi."""
        downloaded_files_path = os.path.join(self.base_dir, 'logs', 'downloaded_files.txt')
        try:
            with open(downloaded_files_path, 'w', encoding='utf-8') as f:
                for url in sorted(self.downloaded_files):
                    f.write(url + '\n')
            logging.info(f"💾 Sauvegardé {len(self.downloaded_files)} fichiers téléchargés dans le fichier de suivi.")
        except Exception as e:
            logging.error(f"✘ Erreur lors de la sauvegarde du suivi des téléchargements : {str(e)}")

    def generate_report(self, duration, error=None):
        """Génère un rapport détaillé du processus de crawling."""
        report_sections = []

        # En-tête du rapport
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

        # Section des erreurs si présentes
        if error:
            report_sections.append(f"""  
Errors  
------  
Critical Error: {error}

""")

        # Liste des URLs crawlées
        report_sections.append("""  
Processed URLs  
-------------  
""")
        for url in sorted(self.visited_pages):
            report_sections.append(url)

        # Liste des fichiers générés
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

        # Sauvegarde du rapport
        report_content = '\n'.join(report_sections)
        report_path = os.path.join(self.base_dir, 'crawler_report.txt')

        try:
            with open(report_path, 'w', encoding='utf-8') as f:
                f.write(report_content)
            logging.info(f"📄 Rapport généré avec succès : {report_path}")
        except Exception as e:
            logging.error(f"✘ Erreur lors de la génération du rapport : {str(e)}")

        # Création d'un fichier de résumé
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
            logging.info(f"📄 Résumé généré avec succès : {os.path.join(self.base_dir, 'summary.txt')}")
        except Exception as e:
            logging.error(f"✘ Erreur lors de la génération du résumé : {str(e)}")

# Classe pour l'Extraction PDF/DOC
class PDFExtractor:
    def __init__(self, input_dir, output_dir, api_keys_file, max_workers=10, initial_dpi=300, retry_dpi=200, logger=None):
        # Configuration des chemins
        self.input_dir = Path(input_dir)
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        
        # Chargement des clés API OpenAI depuis un fichier
        self.api_keys = Queue()
        try:
            with open(api_keys_file, 'r') as f:
                for line in f:
                    key = line.strip()
                    if key:
                        self.api_keys.put(key)
            if self.api_keys.empty():
                raise ValueError("Aucune clé API chargée.")
        except Exception as e:
            if logger:
                logger.error(f"🚫 Erreur lors du chargement des clés API: {str(e)}")
            else:
                print(f"🚫 Erreur lors du chargement des clés API: {str(e)}")
            raise
        
        self.max_workers = max_workers
        self.initial_dpi = initial_dpi
        self.retry_dpi = retry_dpi
        self.logger = logger or logging.getLogger(__name__)

    def preprocess_image(self, image):
        """Prétraitement de l'image pour OCR"""
        if isinstance(image, Image.Image):
            image = np.array(image)

        if image is None:
            raise ValueError("⚠️ Image vide ou corrompue.")
        
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
            raise ValueError(f"⚠️ Erreur lors du prétraitement de l'image: {str(e)}")

    def convert_pdf_to_images(self, pdf_path, dpi):
        """Convertit un PDF en images avec un DPI spécifique"""
        try:
            self.logger.info(f"📄 Conversion de {pdf_path.name} en images avec DPI={dpi}")
            images = convert_from_path(pdf_path, dpi=dpi, fmt='jpeg', thread_count=1)
            self.logger.info(f"✅ Conversion réussie pour {pdf_path.name} avec DPI={dpi}")
            return images
        except Exception as e:
            self.logger.error(f"❌ Erreur lors de la conversion de {pdf_path.name} en images avec DPI={dpi}: {str(e)}")
            return None

    def extract_text_with_ocr(self, pdf_path):
        """Extraction de texte par OCR avec gestion des erreurs et reprises"""
        # Première tentative avec le DPI initial
        images = self.convert_pdf_to_images(pdf_path, self.initial_dpi)
        if images is None:
            # Deuxième tentative avec un DPI réduit
            images = self.convert_pdf_to_images(pdf_path, self.retry_dpi)
            if images is None:
                self.logger.error(f"❌ Échec de la conversion de {pdf_path.name} en images avec tous les DPI tentés.")
                return None
        
        ocr_texts = []
        for i, image in enumerate(images, 1):
            self.logger.info(f"🔍 OCR page {i}/{len(images)} de {pdf_path.name}")
            try:
                processed_img = self.preprocess_image(image)
            except Exception as e:
                self.logger.error(f"⚠️ Prétraitement de l'image échoué pour la page {i} de {pdf_path.name}: {str(e)}")
                ocr_texts.append("")
                continue

            try:
                text = pytesseract.image_to_string(
                    processed_img,
                    lang='fra+eng',
                    config='--psm 1'
                )
                if len(text.strip()) < 100:
                    self.logger.info(f"🔄 OCR insuffisant (moins de 100 caractères) pour la page {i} de {pdf_path.name}, tentative avec psm 3 et oem 1")
                    text = pytesseract.image_to_string(
                        processed_img,
                        lang='fra+eng',
                        config='--psm 3 --oem 1'
                    )
                ocr_texts.append(text)
            except Exception as e:
                self.logger.error(f"❌ OCR échoué pour la page {i} de {pdf_path.name}: {str(e)}")
                ocr_texts.append("")
        
        return ocr_texts

    def extract_text_with_pypdf_per_page(self, pdf_path, page_num):
        """Extraction texte avec PyPDF pour une page spécifique"""
        try:
            with open(pdf_path, 'rb') as file:
                reader = pypdf.PdfReader(file)
                if page_num < 1 or page_num > len(reader.pages):
                    self.logger.error(f"⚠️ Numéro de page invalide: {page_num} dans {pdf_path.name}")
                    return ''
                page = reader.pages[page_num - 1]
                text = page.extract_text() or ''
                self.logger.info(f"📝 Extraction PyPDF page {page_num} de {pdf_path.name}: {len(text)} caractères")
                return text
        except Exception as e:
            self.logger.error(f"❌ Erreur PyPDF pour la page {page_num} de {pdf_path.name}: {str(e)}")
            return ''

    def get_api_key(self):
        """Récupère une clé API de la queue"""
        try:
            api_key = self.api_keys.get(timeout=10)
            return api_key
        except Empty:
            self.logger.error("🚫 Aucune clé API disponible.")
            return None

    def process_with_gpt(self, content):
        """Traitement du contenu avec GPT-4 pour structurer le texte en Markdown"""
        system_prompt = {
            "role": "system",
            "content": (
                "Vous êtes un assistant expert en analyse de documents. Votre tâche est de : "
                "1. Extraire et structurer les informations clés du texte fourni en suivant ces règles :\n"
                "   - Créer une hiérarchie claire avec des titres (# ## ###)\n"
                "   - Séparer les sections par des sauts de ligne\n"
                "   - Assurer une cohérence dans la présentation\n\n"
                "2. Pour les tableaux :\n"
                "   - Convertir chaque ligne en items de liste\n"
                "   - Utiliser le format '- **[Nom colonne] :** [valeur]'\n"
                "   - Grouper les items liés avec une indentation\n"
                "   - Ajouter des séparateurs '---' entre les groupes\n\n"
                "3. Appliquer le formatage suivant :\n"
                "   - Mettre en italique (*) les termes importants\n"
                "   - Utiliser le gras (**) pour les titres de colonnes\n"
                "   - Créer des listes à puces (-) pour les énumérations\n"
                "   - Utiliser des citations (>) pour les notes importantes\n\n"
                "4. Nettoyer et améliorer le texte :\n"
                "   - Corriger les erreurs typographiques d'OCR\n"
                "   - Unifier la ponctuation\n"
                "   - Éliminer les caractères parasites\n"
                "   - Vérifier l'alignement et l'espacement\n\n"
                "Exemple de transformation :\n"
                "Table : 'Produit | Prix | Stock\n"
                "         Pommes | 2.50 | 100\n"
                "         Poires | 3.00 | 85'\n\n"
                "Devient :\n"
                "### Liste des produits\n\n"
                "- **Produit :** Pommes\n"
                "  - **Prix :** 2.50€\n"
                "  - **Stock :** 100 unités\n\n"
                "---\n\n"
                "- **Produit :** Poires\n"
                "  - **Prix :** 3.00€\n"
                "  - **Stock :** 85 unités"
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
            time.sleep(1)  # Pause pour respecter les limites de taux
            return processed_content
        except Exception as e:
            self.logger.error(f"❌ Erreur GPT: {str(e)}")
            return None
        finally:
            # Remettre la clé API dans la queue
            if api_key:
                self.api_keys.put(api_key)

    def split_content(self, content, max_length=4000):
        """Divise le contenu en parties plus petites si nécessaire"""
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

    def process_single_part(self, document_name, page_num, part_num, content):
        """Traitement d'une seule partie du contenu avec GPT"""
        self.logger.info(f"📝 Traitement du Document: {document_name}, Page: {page_num}, Partie: {part_num}")
        processed_content = self.process_with_gpt(content)
        
        if processed_content:
            output_file_name = self.output_dir / f"{document_name}_page_{page_num}_part_{part_num}.txt"
            try:
                with open(output_file_name, 'a', encoding='utf-8') as f:
                    f.write(f"📄 Document ID: {document_name}\n\n{processed_content}\n\n")
                self.logger.info(f"✅ Fichier créé: {output_file_name.name}")
            except Exception as e:
                self.logger.error(f"❌ Erreur sauvegarde Document: {document_name}, Page: {page_num}, Partie: {part_num}: {str(e)}")

    def process_pdf(self, pdf_path):
        """Traitement complet d'un PDF"""
        document_name = pdf_path.stem
        self.logger.info(f"📂 Début traitement de {pdf_path.name}")
        
        # Extraction de texte par OCR
        ocr_texts = self.extract_text_with_ocr(pdf_path)
        if ocr_texts is None:
            self.logger.error(f"❌ Échec de l'extraction OCR pour {pdf_path.name}")
            return False

        with ThreadPoolExecutor(max_workers=self.max_workers) as executor:
            futures = []
            for page_num, ocr_text in enumerate(ocr_texts, 1):
                self.logger.info(f"🔄 Préparation de la page {page_num}/{len(ocr_texts)} de {pdf_path.name}")
                
                if ocr_text and len(ocr_text.strip()) >= 100:
                    page_text = ocr_text
                    self.logger.info(f"✅ OCR réussi pour la page {page_num} de {pdf_path.name}")
                else:
                    self.logger.info(f"🔄 OCR insuffisant pour la page {page_num} de {pdf_path.name}, utilisation de PyPDF")
                    pypdf_text = self.extract_text_with_pypdf_per_page(pdf_path, page_num)
                    page_text = pypdf_text
                
                if not page_text.strip():
                    self.logger.warning(f"⚠️ Aucun texte extrait pour la page {page_num} de {pdf_path.name}")
                    continue  # Passer à la page suivante si aucun texte n'est extrait
                
                # Diviser le texte si trop long
                parts = self.split_content(page_text, max_length=4000)  # Ajustez max_length si nécessaire
                
                for idx, part in enumerate(parts, 1):
                    futures.append(executor.submit(
                        self.process_single_part, document_name, page_num, idx, part
                    ))
            
            # Attente des tâches terminées avec mise à jour de la barre de progression
            for future in as_completed(futures):
                pass  # Les logs sont gérés dans les tâches individuelles
        
        self.logger.info(f"✅ Terminé traitement de {pdf_path.name}")
        return True

    def process_all_pdfs(self):
        """Traitement de tous les PDF"""
        pdf_files = list(self.input_dir.glob('*.pdf'))
        total_files = len(pdf_files)
        
        self.logger.info(f"📢 Début traitement de {total_files} fichiers PDF dans '{self.input_dir}'")
        
        with Progress(
            SpinnerColumn(),
            TextColumn("[progress.description]{task.description}"),
            BarColumn(),
            "[progress.percentage]{task.percentage:>3.0f}%",
            TimeElapsedColumn(),
            TimeRemainingColumn(),
            console=Console()
        ) as progress:
            pdf_progress = progress.add_task("[green]Traitement des PDF...", total=total_files)
            for pdf_path in pdf_files:
                self.process_pdf(pdf_path)
                progress.update(pdf_progress, advance=1)
        
        self.logger.info(f"🎉 Terminé. {total_files} fichiers PDF traités.")

# Classe pour le Traitement des Embeddings
class EmbeddingProcessor:
    def __init__(self, input_dir, output_dir, openai_api_keys, verbose=False, logger=None):
        # Configuration des chemins
        self.input_dir = Path(input_dir)
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)

        # Initialisation des listes globales pour tous les fichiers
        self.all_embeddings = []
        self.all_metadata = []

        # Configuration OpenAI
        self.openai_api_keys = openai_api_keys
        self.headers_cycle = cycle([
            {
                "Authorization": f"Bearer {key}",
                "Content-Type": "application/json"
            } for key in self.openai_api_keys
        ])
        self.lock = threading.Lock()

        # Configuration logging
        self.logger = logger or logging.getLogger(__name__)
        self.verbose = verbose

    def chunk_text(self, text, chunk_size=1200, overlap_size=100):
        """Découpe le texte en chunks avec un chevauchement. Traite aussi les textes courts."""
        try:
            tokens = text.split()
            
            # Si le texte est plus court que la taille du chunk, le traiter comme un seul chunk
            if len(tokens) <= chunk_size:
                return [text]
                
            chunks = []
            for i in range(0, len(tokens), chunk_size - overlap_size):
                chunk = ' '.join(tokens[i:i + chunk_size])
                chunks.append(chunk)
                
            # S'assurer que le dernier chunk n'est pas trop petit
            if len(chunks) > 1 and len(tokens[-(chunk_size - overlap_size):]) < chunk_size // 2:
                # Fusionner le dernier chunk avec l'avant-dernier s'il est trop petit
                last_chunk = ' '.join(tokens[-(chunk_size):])
                chunks[-1] = last_chunk
            
            return chunks
            
        except Exception as e:
            self.logger.error(f"Erreur lors du découpage du texte: {str(e)}")
            return [text]  # Retourner le texte complet en cas d'erreur

    def get_contextualized_chunk(self, chunk, full_text, headers, document_name, page_num, chunk_id):
        """Demande à GPT-4 de contextualiser chaque chunk."""
        try:
            system_prompt = {
                "role": "system",
                "content": (
                    "Vous êtes un expert analyste. Le texte suivant est un extrait d'un document plus important. "
                    "Votre tâche consiste à fournir un contexte à la section suivante en faisant référence au contenu de l'ensemble du document. "
                    "Veiller à ce que le contexte permette de mieux comprendre le morceau."
                )
            }
            user_prompt = {
                "role": "user",
                "content": f"Document: {full_text}\n\nChunk: {chunk}\n\nVeuillez fournir un contexte pour ce morceau en français"
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
                self.logger.info(f"Appel LLM pour {document_name} page {page_num}, chunk {chunk_id}")

            self.logger.info(f"Début de l'appel API GPT pour {document_name} page {page_num} chunk {chunk_id}")  
            
            response = requests.post(
                'https://api.openai.com/v1/chat/completions',
                headers=headers,
                json=payload,
                timeout=60
            )
            response.raise_for_status()
            return response.json()['choices'][0]['message']['content']

        except Exception as e:
            self.logger.error(f"Erreur lors de la contextualisation: {str(e)}")
            return None

    def get_embedding(self, text, headers, document_name, page_num, chunk_id):
        """Obtenir l'embedding pour un texte."""
        try:
            payload = {
                "input": text,
                "model": "text-embedding-ada-002",  # Utiliser le modèle d'embedding approprié
                "encoding_format": "float"
            }

            if self.verbose:
                self.logger.info(f"Appel API Embedding pour {document_name} page {page_num} chunk {chunk_id}")

            self.logger.info(f"🔗 Appel API Embedding pour {document_name} page {page_num} chunk {chunk_id}")  
            
            response = requests.post(
                'https://api.openai.com/v1/embeddings',
                headers=headers,
                json=payload,
                timeout=60
            )
            response.raise_for_status()
            return response.json()['data'][0]['embedding']

        except Exception as e:
            self.logger.error(f"Erreur lors de la récupération de l'embedding: {str(e)}")
            return None

    def process_chunk(self, chunk_info):
        """Processus pour un chunk spécifique."""
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
            self.logger.error(f"Erreur lors du traitement du chunk: {str(e)}")
            return None, None

    def process_file(self, txt_file_path):
        """Processus pour un fichier texte."""
        try:
            self.logger.info(f"📂 Traitement du fichier: {txt_file_path}")
            
            with open(txt_file_path, 'r', encoding='utf-8') as file:
                full_text = file.read()

            chunks = self.chunk_text(full_text)
            
            # Extraire le numéro de page du nom du fichier
            match = re.search(r'_page_(\d+)_', txt_file_path.stem)
            if match:
                page_num = int(match.group(1))
            else:
                page_num = 1  # Par défaut si non trouvé
            
            chunk_infos = [
                (txt_file_path, i, chunk, full_text, txt_file_path.stem, page_num)
                for i, chunk in enumerate(chunks, 1)
            ]

            return chunk_infos

        except Exception as e:
            self.logger.error(f"Erreur lors du traitement du fichier {txt_file_path}: {str(e)}")
            return []

    def process_all_files(self):
        """Processus pour tous les fichiers dans le dossier d'entrée avec parallélisme."""
        try:
            txt_files = list(self.input_dir.glob('*.txt'))
            total_files = len(txt_files)
            self.logger.info(f"📢 Début traitement de {total_files} fichiers dans '{self.input_dir}'")

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
                # Sauvegarde des résultats
                chunks_json_path = self.output_dir / "chunks.json"
                with open(chunks_json_path, 'w', encoding='utf-8') as json_file:
                    json.dump({"metadata": self.all_metadata}, json_file, ensure_ascii=False, indent=4)

                embeddings_npy_path = self.output_dir / "embeddings.npy"
                np.save(embeddings_npy_path, np.array(self.all_embeddings))

                self.logger.info(f"✅ Fichiers créés: {chunks_json_path} et {embeddings_npy_path}")

        except Exception as e:
            self.logger.error(f"Erreur lors du traitement des fichiers: {str(e)}")
            raise

# Classe Principale pour l'Intégration
class IntegrationManager:
    def __init__(self, config):
        # Charger les paramètres depuis le dictionnaire de configuration
        self.crawler_config = config.get('crawler', {})
        self.extractor_config = config.get('extractor', {})
        self.embedding_config = config.get('embedding', {})
        
        # Configurer le logging
        self.setup_logging(config.get('logging', {}))
        self.logger = logging.getLogger('IntegrationManager')
        
        # Initialiser les composants
        self.crawler = WebCrawler(
            start_url=self.crawler_config.get('start_url'),
            max_depth=self.crawler_config.get('max_depth', 2),
            use_playwright=self.crawler_config.get('use_playwright', False),
            excluded_paths=self.crawler_config.get('excluded_paths'),
            download_extensions=self.crawler_config.get('download_extensions'),
            language_pattern=self.crawler_config.get('language_pattern'),
            base_dir=self.crawler_config.get('base_dir')
        )
        
        self.extractor = PDFExtractor(
            input_dir=self.extractor_config.get('input_dir'),
            output_dir=self.extractor_config.get('output_dir'),
            api_keys_file=self.extractor_config.get('api_keys_file'),
            max_workers=self.extractor_config.get('max_workers', 10),
            initial_dpi=self.extractor_config.get('initial_dpi', 300),
            retry_dpi=self.extractor_config.get('retry_dpi', 200),
            logger=self.logger
        )
        
        self.embedding = EmbeddingProcessor(
            input_dir=self.embedding_config.get('input_dir'),
            output_dir=self.embedding_config.get('output_dir'),
            openai_api_keys=self.embedding_config.get('openai_api_keys'),
            verbose=self.embedding_config.get('verbose', False),
            logger=self.logger
        )
    
    def setup_logging(self, logging_config):
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
        self.logger.info("🛠️  Début du crawling")
        self.crawler.crawl()
        self.logger.info("✅ Crawling terminé")
    
    def run_extraction(self):
        self.logger.info("🛠️  Début de l'extraction PDF/DOC")
        self.extractor.process_all_pdfs()
        self.logger.info("✅ Extraction PDF/DOC terminée")
    
    def run_embedding(self):
        self.logger.info("🛠️  Début du traitement des embeddings")
        self.embedding.process_all_files()
        self.logger.info("✅ Traitement des embeddings terminé")
    
    def run_all(self):
        try:
            self.run_crawling()
            self.run_extraction()
            self.run_embedding()
            self.logger.info("🎉 Processus complet terminé avec succès")
        except Exception as e:
            self.logger.error(f"❌ Erreur durant le processus intégré: {str(e)}")
            raise

# Fonction Principale
def main():
    # Charger les variables d'environnement si nécessaire
    load_dotenv()
    
    # Définir les paramètres de configuration
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
            'language_pattern': re.search(r'/(fr|en)-(ca|us)/', "https://liquid-air.ca"),  # Ajustez selon besoin
            'base_dir': "crawler_output"  # Optionnel, sinon généré automatiquement
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
    
    # Vérifier les clés API OpenAI
    if not config['embedding']['openai_api_keys']:
        print("🚫 Aucune clé API OpenAI trouvée. Veuillez vérifier le fichier 'api_keys.txt'.")
        return
    
    # Initialiser et exécuter l'intégration
    try:
        manager = IntegrationManager(config)
        manager.run_all()
    except Exception as e:
        print(f"❌ Erreur lors de l'intégration: {str(e)}")
        sys.exit(1)

if __name__ == "__main__":
    main()
