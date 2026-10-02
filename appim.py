import sqlite3
import json
import hashlib
from pathlib import Path
from datetime import datetime, timezone
from io import BytesIO
from PIL import Image, ExifTags, ImageFile
from flask import Flask, request, jsonify, Response, render_template, send_file
from threading import Thread, Lock
import time
import os
from flask_wtf.csrf import CSRFProtect, CSRFError
from concurrent.futures import ThreadPoolExecutor, as_completed



IMAGE_EXTENSIONS = {'.jpg', '.jpeg', '.png', '.webp', '.bmp', '.gif', '.tiff'}
THUMB_SIZE = (300, 300)
WEBP_QUALITY = 75
PER_PAGE = 100
Image.MAX_IMAGE_PIXELS = 100_000_000
ImageFile.LOAD_TRUNCATED_IMAGES = False
INDEX_WORKERS = int(os.environ.get("INDEX_WORKERS", max(1, min(2, os.cpu_count() or 2))))




db_lock = Lock()


def get_db(db_path: Path):
    conn = sqlite3.connect(
        str(db_path),
        timeout=10,
        isolation_level=None,
        check_same_thread=False,
    )

    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA busy_timeout=10000")
    conn.execute("PRAGMA temp_store=MEMORY")
    conn.execute("PRAGMA cache_size=-64000")

    return conn




class LRUCache:
    def __init__(self, max_size_mb=100):
        self.max_size = max_size_mb * 1024 * 1024
        self.cache = {}
        self.order = []
        self.current_size = 0
        self.lock = Lock()

    def get(self, key):
        with self.lock:
            if key in self.cache:
                self.order.remove(key)
                self.order.append(key)
                return self.cache[key]
        return None

    def delete(self, key):
        with self.lock:
            value = self.cache.pop(key, None)

            if key in self.order:
                self.order.remove(key)

            if value is not None:
                self.current_size -= (
                    len(value) if isinstance(value, bytes) else 100
                )


    def set(self, key, value):
        size = len(value) if isinstance(value, bytes) else 100
        with self.lock:
            if key in self.cache:
                self.current_size -= len(self.cache[key]) if isinstance(self.cache[key], bytes) else 100
                self.order.remove(key)

            while self.current_size + size > self.max_size and self.order:
                oldest = self.order.pop(0)
                old_val = self.cache.pop(oldest, None)
                if old_val:
                    self.current_size -= len(old_val) if isinstance(old_val, bytes) else 100

            self.cache[key] = value
            self.order.append(key)
            self.current_size += size


class DatabasePool:
    def __init__(self, db_path: Path, max_connections=5):
        self.db_path = db_path
        self.max_connections = max_connections
        self.lock = Lock()
        self.connections = []

    def get_connection(self):
        with self.lock:
            if self.connections:
                return self.connections.pop()
        return get_db(self.db_path)

    def return_connection(self, conn):
        with self.lock:
            if len(self.connections) < self.max_connections:
                self.connections.append(conn)
            else:
                try:
                    conn.close()
                except Exception as e:
                    print(f"Something went wrong: {e}")


    def execute(self, query, params=None):
        conn = self.get_connection()
        try:
            result = conn.execute(query, params or ()).fetchall()
            return result
        finally:
            self.return_connection(conn)

    def execute_one(self, query, params=None):
        conn = self.get_connection()
        try:
            return conn.execute(query, params or ()).fetchone()
        finally:
            self.return_connection(conn)

    def execute_write(self, query, params=None):
        with db_lock:
            conn = self.get_connection()
            try:
                conn.execute(query, params or ())
                return True
            finally:
                self.return_connection(conn)


    def execute_many(self, query, params_list):
        with db_lock:
            conn = self.get_connection()
            try:
                conn.executemany(query, params_list)
                return True
            finally:
                self.return_connection(conn)



db_pool = None
thumb_cache = LRUCache(max_size_mb=200)


def init_db(db_path: Path):
    conn = get_db(db_path)
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA synchronous=NORMAL")

    has_photos = conn.execute(
        "SELECT name FROM sqlite_master WHERE type='table' AND name='photos'"
    ).fetchone()

    if not has_photos:
        print("  Creating new database...")

        conn.execute("""
            CREATE TABLE photos (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                file_hash TEXT UNIQUE NOT NULL,
                filename TEXT NOT NULL,
                filepath TEXT NOT NULL,
                file_size INTEGER,
                file_modified TEXT,
                width INTEGER,
                height INTEGER,

                exif_date TEXT,
                exif_camera TEXT,
                exif_gps_lat REAL,
                exif_gps_lon REAL,

                thumb_webp BLOB,
                dominant_color TEXT,

                tags_json TEXT,
                categories_json TEXT,
                caption TEXT,
                detailed_caption TEXT,
                ocr_text TEXT,
                embedding BLOB,

                indexed_at TEXT,
                processed_at TEXT
            )
        """)
        conn.execute("""CREATE UNIQUE INDEX IF NOT EXISTS idx_photos_filepath_unique ON photos(filepath)""")
        conn.execute("CREATE INDEX IF NOT EXISTS idx_file_hash ON photos(file_hash)")
        conn.execute("CREATE INDEX IF NOT EXISTS idx_filename ON photos(filename)")
        conn.execute("CREATE INDEX IF NOT EXISTS idx_exif_date ON photos(exif_date)")
        conn.execute("CREATE INDEX IF NOT EXISTS idx_file_modified ON photos(file_modified)")
    else:
        for col, col_type in [
            ("thumb_webp", "BLOB"),
            ("dominant_color", "TEXT"),
            ("tags_json", "TEXT"),
            ("categories_json", "TEXT"),
            ("caption", "TEXT"),
            ("detailed_caption", "TEXT"),
            ("ocr_text", "TEXT"),
            ("embedding", "BLOB"),
            ("processed_at", "TEXT"),
        ]:
            try:
                conn.execute(f"ALTER TABLE photos ADD COLUMN {col} {col_type}")
            except Exception as e:
                print(f"Something went wrong: {e}")

    # FTS setup
    try:
        has_fts = conn.execute(
            "SELECT name FROM sqlite_master WHERE type='table' AND name='photos_fts'"
        ).fetchone()

        if not has_fts:
            conn.execute("""
                CREATE VIRTUAL TABLE photos_fts USING fts5(
                    filename, caption, detailed_caption, ocr_text, tags_text, categories_text
                )
            """)

            rows = conn.execute("""
                SELECT id, filename, caption, detailed_caption, ocr_text, tags_json, categories_json
                FROM photos
            """).fetchall()

            for row in rows:
                tags_text = ''
                cats_text = ''
                if row['tags_json']:
                    try:
                        tags_text = ' '.join(json.loads(row['tags_json']).keys())
                    except Exception as e:
                        print(f"Something went wrong: {e}")
                if row['categories_json']:
                    try:
                        cats_text = ' '.join(json.loads(row['categories_json']).keys())
                    except Exception as e:
                         print(f"Something went wrong: {e}")

                conn.execute("""
                    INSERT INTO photos_fts(rowid, filename, caption, detailed_caption, ocr_text, tags_text, categories_text)
                    VALUES (?, ?, ?, ?, ?, ?, ?)
                """, (row['id'], row['filename'] or '', row['caption'] or '',
                      row['detailed_caption'] or '', row['ocr_text'] or '', tags_text, cats_text))
    except Exception as e:
        print(f"  FTS warning: {e}")

    conn.close()



def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def extract_dominant_color(img: Image.Image) -> str:
    try:
        small = img.copy()
        small.thumbnail((32, 32), Image.Resampling.BILINEAR)

        if small.mode != 'RGB':
            small = small.convert('RGB')

        pixels = list(small.getdata())

        if not pixels:
            return "#1a1a1a"

        avg_r = sum(p[0] for p in pixels) // len(pixels)
        avg_g = sum(p[1] for p in pixels) // len(pixels)
        avg_b = sum(p[2] for p in pixels) // len(pixels)

        small.close()

        return f"#{avg_r:02x}{avg_g:02x}{avg_b:02x}"

    except Exception:
        return "#1a1a1a"



def extract_exif_safe(img: Image.Image) -> dict:
    data = {}
    try:
        exif = img.getexif()
        if not exif:
            return data

        for tag_id in [36867, 36868, 306]:
            try:
                val = exif.get(tag_id)
                if val:
                    if isinstance(val, bytes):
                        val = val.decode('utf-8', errors='ignore')
                    val = str(val).strip().replace('\x00', '')
                    if val and len(val) >= 19:
                        data['date'] = datetime.strptime(val[:19], "%Y:%m:%d %H:%M:%S").isoformat()
                        break
            except Exception as e:
                print(f"Something went wrong: {e}")

        try:
            make = exif.get(271, '')
            model = exif.get(272, '')
            if isinstance(make, bytes):
                make = make.decode('utf-8', errors='ignore')
            if isinstance(model, bytes):
                model = model.decode('utf-8', errors='ignore')
            make = str(make).strip().replace('\x00', '')
            model = str(model).strip().replace('\x00', '')
            if make or model:
                data['camera'] = f"{make} {model}".strip()
        except Exception as e:
            print(f"Something went wrong: {e}")

        try:
            if hasattr(ExifTags, 'IFD'):
                gps = exif.get_ifd(ExifTags.IFD.GPSInfo)
                if gps and 2 in gps and 4 in gps:
                    def to_dec(coords, ref):
                        d, m, s = [float(x) for x in coords]
                        dec = d + m / 60 + s / 3600
                        return -dec if ref in ['S', 'W'] else dec
                    data['gps_lat'] = to_dec(gps[2], gps.get(1, 'N'))
                    data['gps_lon'] = to_dec(gps[4], gps.get(3, 'E'))
        except Exception as e:
            print(f"Something went wrong: {e}")
    except Exception as e:
        print(f"Something went wrong: {e}")

    return data


def make_thumbnail_webp(img):
    thumb = img.copy()
    thumb.thumbnail(THUMB_SIZE, Image.Resampling.LANCZOS)

    if thumb.mode != 'RGB':
        thumb = thumb.convert('RGB')

    buf = BytesIO()
    thumb.save(
        buf,
        format='WEBP',
        quality=WEBP_QUALITY,
        method=4
    )

    thumb.close()

    return buf.getvalue()
def make_thumbnail_data(img):
    thumb = img.copy()
    thumb.thumbnail(THUMB_SIZE, Image.Resampling.LANCZOS)

    if thumb.mode != 'RGB':
        thumb = thumb.convert('RGB')

    small = thumb.copy()
    small.thumbnail((32, 32), Image.Resampling.BILINEAR)

    pixels = list(small.getdata())

    if pixels:
        avg_r = sum(p[0] for p in pixels) // len(pixels)
        avg_g = sum(p[1] for p in pixels) // len(pixels)
        avg_b = sum(p[2] for p in pixels) // len(pixels)

        dominant_color = f"#{avg_r:02x}{avg_g:02x}{avg_b:02x}"
    else:
        dominant_color = "#1a1a1a"

    small.close()

    buf = BytesIO()

    thumb.save(
        buf,
        format='WEBP',
        quality=WEBP_QUALITY,
        method=4
    )

    thumb.close()

    return buf.getvalue(), dominant_color


def safe_read_file(filepath: str) -> tuple[bytes | None, str | None]:

    path = Path(filepath)

    try:
        if path.exists() and path.is_file():
            return path.read_bytes(), None
    except OSError:
        pass

    try:
        with open(filepath, 'rb') as f:
            data = f.read()
        return data, None
    except OSError:
        pass

    if os.name == 'nt':
        try:
            import ctypes
            buf = ctypes.create_unicode_buffer(512)
            result = ctypes.windll.kernel32.GetShortPathNameW(
                str(path), buf, 512
            )
            if result > 0:
                short_path = buf.value
                with open(short_path, 'rb') as f:
                    data = f.read()
                return data, None
        except Exception:
            pass

    if os.name == 'nt':
        try:
            abs_path = os.path.abspath(filepath)
            if not abs_path.startswith('\\\\?\\'):
                abs_path = '\\\\?\\' + abs_path
            with open(abs_path, 'rb') as f:
                data = f.read()
            return data, None
        except OSError:
            pass

    try:
        chunks = []
        with open(filepath, 'rb') as f:
            while True:
                chunk = f.read(1024 * 1024)  # 1MB chunks
                if not chunk:
                    break
                chunks.append(chunk)
        if chunks:
            return b''.join(chunks), None
    except OSError:
        pass

    return None, f"Cannot read file: {filepath}"


def safe_check_exists(filepath: str) -> bool:
    """Check if file exists, handling Windows path edge cases."""
    try:
        return os.path.isfile(filepath)
    except (OSError, ValueError):
        pass

    try:
        return Path(filepath).is_file()
    except (OSError, ValueError):
        pass

    if os.name == 'nt':
        try:
            abs_path = os.path.abspath(filepath)
            if not abs_path.startswith('\\\\?\\'):
                abs_path = '\\\\?\\' + abs_path
            return os.path.isfile(abs_path)
        except (OSError, ValueError):
            pass

    return False


class Indexer:
    def __init__(self, folder: Path, db_path: Path):
        self.folder = folder
        self.db_path = db_path
        self._running = False

    def scan_folder(self) -> list:
        images = []

        def scan_dir(path):
            try:
                for entry in os.scandir(path):
                    try:
                        if entry.is_dir(follow_symlinks=False):
                            scan_dir(entry.path)
                        elif entry.is_file(follow_symlinks=False):
                            ext = os.path.splitext(entry.name)[1].lower()
                            if ext in IMAGE_EXTENSIONS:
                                images.append(Path(entry.path))
                    except Exception as e:
                        print(f"Something went wrong: {e}")
            except Exception as e:
                print(f"Something went wrong: {e}")

        scan_dir(self.folder)
        return sorted(images)

    def get_indexed(self) -> dict:
        rows = db_pool.execute(
            "SELECT id, file_hash, filepath, file_size, file_modified FROM photos"
        )
        return {
            r['filepath']: {
                'id': r['id'],
                'file_hash': r['file_hash'],
                'file_size': r['file_size'],
                'file_modified': r['file_modified']
            }
            for r in rows
        }

    def process_new_image(self, path: Path):
        try:
            # Read the file once.
            file_data = path.read_bytes()

            # Hash the bytes we already have in memory.
            fhash = hashlib.sha256(file_data).hexdigest()

            return self.process_image(path, file_data, fhash), None

        except Exception as e:
            return None, (path.name, str(e))


    def process_images_parallel(self, paths):

        results = []
        errors = []

        if not paths:
            return results, errors

        with ThreadPoolExecutor(max_workers=INDEX_WORKERS) as executor:
            futures = {
                executor.submit(self.process_new_image, path): path
                for path in paths
            }

            for future in as_completed(futures):
                path = futures[future]

                try:
                    result, error = future.result()

                    if error:
                        errors.append(error)
                    elif result:
                        results.append(result)

                except Exception as e:
                    errors.append((path.name, str(e)))

        return results, errors



    def process_image(
        self,
        path: Path,
        file_data: bytes = None,
        fhash: str = None
    ) -> tuple:

        if file_data is None:
            file_data = path.read_bytes()

        if fhash is None:
            fhash = hashlib.sha256(file_data).hexdigest()

        stat = path.stat()

        # Decode the image from the bytes we already read.
        img = Image.open(BytesIO(file_data))
        img.load()

        exif = extract_exif_safe(img)

        thumb_webp, dominant_color = make_thumbnail_data(img)

        width, height = img.size

        try:
            img.close()
        except Exception as e:
            print(f"Something went wrong: {e}")

        data = (
            path.name,
            str(path.absolute()),
            stat.st_size,
            datetime.fromtimestamp(stat.st_mtime).isoformat(),
            width,
            height,
            exif.get('date'),
            exif.get('camera'),
            exif.get('gps_lat'),
            exif.get('gps_lon'),
            thumb_webp,
            dominant_color,
            now_iso()
        )

        return fhash, data


    def quick_scan(self, show_progress=True):
        scan_started = time.perf_counter()
        db_started = time.perf_counter()
        existing = self.get_indexed()
        existing_count = len(existing)
        db_time = time.perf_counter() - db_started
        existing_hashes = {v['file_hash']: v for v in existing.values()}

        folder_started = time.perf_counter()
        images = self.scan_folder()
        folder_count = len(images)
        folder_time = time.perf_counter() - folder_started

        print(
            f"  Timing: DB={db_time:.2f}s | "
            f"folder={folder_time:.2f}s"
        )

        scan_time = time.perf_counter() - scan_started

        if show_progress:
            print(
                f"  Found {folder_count:,} images "
                f"in {scan_time:.2f}s"
            )


        if show_progress:
            print(f"  Database: {existing_count} | Folder: {folder_count}")

        new_images = []
        new_image_paths = []

        found_paths = set()
        skipped = []

        compare_started = time.perf_counter()
        for i, path in enumerate(images):
            try:
                path_str = str(path.absolute())
                found_paths.add(path_str)
                stat = path.stat()
                file_mtime = datetime.fromtimestamp(stat.st_mtime).isoformat()

                if path_str in existing:
                    info = existing[path_str]
                    if info['file_size'] == stat.st_size and info['file_modified'] == file_mtime:
                        continue
                    file_data = path.read_bytes()
                    fhash = hashlib.sha256(file_data).hexdigest()

                    if fhash == info['file_hash']:
                        db_pool.execute_write(
                            """
                            UPDATE photos
                            SET file_modified=?, file_size=?
                            WHERE id=?
                            """,
                            (file_mtime, stat.st_size, info['id'])
                        )
                    else:
                        _, data = self.process_image(
                            path,
                            file_data=file_data,
                            fhash=fhash
                        )


                        with db_lock:
                            conn = get_db(self.db_path)
                            try:
                                conn.execute("""
                                    UPDATE photos
                                    SET
                                        file_hash=?,
                                        filename=?,
                                        filepath=?,
                                        file_size=?,
                                        file_modified=?,
                                        width=?,
                                        height=?,
                                        exif_date=?,
                                        exif_camera=?,
                                        exif_gps_lat=?,
                                        exif_gps_lon=?,
                                        thumb_webp=?,
                                        dominant_color=?,
                                        indexed_at=?
                                    WHERE id=?
                                """, (
                                    fhash,
                                    data[0],   # filename
                                    data[1],   # filepath
                                    data[2],   # file_size
                                    data[3],   # file_modified
                                    data[4],   # width
                                    data[5],   # height
                                    data[6],   # exif_date
                                    data[7],   # camera
                                    data[8],   # gps lat
                                    data[9],   # gps lon
                                    data[10],  # thumbnail
                                    data[11],  # dominant color
                                    data[12],  # indexed_at
                                    info['id']
                                ))

                                # Rebuild FTS entry for this photo.
                                try:
                                    conn.execute(
                                        "DELETE FROM photos_fts WHERE rowid=?",
                                        (info['id'],)
                                    )

                                    conn.execute("""
                                        INSERT INTO photos_fts(
                                            rowid,
                                            filename,
                                            caption,
                                            detailed_caption,
                                            ocr_text,
                                            tags_text,
                                            categories_text
                                        )
                                        SELECT
                                            id,
                                            filename,
                                            COALESCE(caption, ''),
                                            COALESCE(detailed_caption, ''),
                                            COALESCE(ocr_text, ''),
                                            '',
                                            ''
                                        FROM photos
                                        WHERE id=?
                                    """, (info['id'],))

                                except Exception as e:
                                    print(f"    FTS update warning: {e}")

                            finally:
                                conn.close()

                        thumb_cache.delete(f"thumb_{info['file_hash']}_webp")
                        thumb_cache.delete(f"thumb_{fhash}_webp")


                        if show_progress:
                            print(f"    Updated: {path.name}")

                else:
                    new_image_paths.append(path)


            except Exception as e:
                skipped.append((path.name, str(e)))
                if show_progress:
                    print(f"    Error: {path.name} - {e}")

            if show_progress and (i + 1) % 500 == 0 and not new_images:
                print(f"    Checked {i + 1}/{folder_count}...")
        compare_time = time.perf_counter() - compare_started

        if new_image_paths:
            process_started = time.perf_counter()

            if show_progress:
                print(
                    f"  Processing {len(new_image_paths):,} new images "
                    f"with {INDEX_WORKERS} workers..."
                )

            processed_results, processing_errors = self.process_images_parallel(
                new_image_paths
            )

            new_images.extend(processed_results)
            skipped.extend(processing_errors)

            process_time = time.perf_counter() - process_started

            if show_progress:
                print(
                    f"  Parallel processing: "
                    f"{len(processed_results):,} images "
                    f"in {process_time:.2f}s"
                )


        print(
            f"  Timing: comparison={compare_time:.2f}s"
        )

        if show_progress and skipped:
            print(f"    Skipped {len(skipped)} files")

        new_count = 0
        removed = 0
        print(f"  Preparing to write {len(new_images)} new images to database...")


        if new_images or len(found_paths) < existing_count:
            with db_lock:
                conn = get_db(self.db_path)

                try:
                    conn.execute("BEGIN")

                    for fhash, data in new_images:
                        try:
                            conn.execute("""
                                INSERT INTO photos (
                                    file_hash,
                                    filename,
                                    filepath,
                                    file_size,
                                    file_modified,
                                    width,
                                    height,
                                    exif_date,
                                    exif_camera,
                                    exif_gps_lat,
                                    exif_gps_lon,
                                    thumb_webp,
                                    dominant_color,
                                    indexed_at
                                )
                                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                            """, (fhash,) + data)

                            new_count += 1

                        except Exception as e:
                            print(f"    DB insert error: {data[0]} - {e}")
                            raise

                    for path_str, info in existing.items():
                        if path_str not in found_paths:
                            conn.execute(
                                "DELETE FROM photos WHERE id=?",
                                (info['id'],)
                            )

                            try:
                                conn.execute(
                                    "DELETE FROM photos_fts WHERE rowid=?",
                                    (info['id'],)
                                )
                            except Exception as e:
                                print(f"    FTS delete warning: {e}")

                            removed += 1

                    for fhash, data in new_images:
                        row = conn.execute(
                            "SELECT id FROM photos WHERE file_hash=?",
                            (fhash,)
                        ).fetchone()

                        if row:
                            try:
                                conn.execute("""
                                    INSERT OR REPLACE INTO photos_fts(
                                        rowid,
                                        filename,
                                        caption,
                                        detailed_caption,
                                        ocr_text,
                                        tags_text,
                                        categories_text
                                    )
                                    VALUES (?, ?, '', '', '', '', '')
                                """, (row['id'], data[0]))

                            except Exception as e:
                                print(f"    FTS insert warning: {e}")

                    conn.execute("COMMIT")
                    check = conn.execute("""
                        SELECT COUNT(*) AS cnt,
                            COUNT(filename) AS filenames,
                            COUNT(thumb_webp) AS thumbnails
                        FROM photos
                    """).fetchone()

                    print(
                        f"    DB VERIFY: {check['cnt']} rows, "
                        f"{check['filenames']} filenames, "
                        f"{check['thumbnails']} WebP thumbnails"
                    )

                except Exception as e:
                    try:
                        conn.execute("ROLLBACK")
                    except Exception:
                        pass

                    print(f"    DATABASE ERROR: {e}")
                    raise

                finally:
                    conn.close()


        if show_progress:
            parts = []
            if new_count:
                parts.append(f"+{new_count} added")
            if removed:
                parts.append(f"-{removed} removed")
            if skipped:
                parts.append(f"{len(skipped)} skipped")
            print(f"  ✓ {', '.join(parts) if parts else 'no changes'}")


        total_time = time.perf_counter() - scan_started

        if show_progress:
            print(f"  Total scan time: {total_time:.2f}s")

        return new_count

    def background_scan(self, interval=120):
        def run():
            while self._running:
                time.sleep(interval)
                try:
                    self.quick_scan(show_progress=False)
                except Exception as e:
                    print(f"Something went wrong: {e}")

        self._running = True
        Thread(target=run, daemon=True).start()

    def stop(self):
        self._running = False



def create_app(folder: Path, db_path: Path):
    global db_pool

    app = Flask(__name__)

    app.config.update(
        SECRET_KEY=os.environ.get(
            "FLASK_SECRET_KEY",
            "dev-only-change-this-secret"
        ),
        WTF_CSRF_ENABLED=True,
        WTF_CSRF_TIME_LIMIT=3600,
        SESSION_COOKIE_HTTPONLY=True,
        SESSION_COOKIE_SAMESITE="Lax",
        SESSION_COOKIE_SECURE=os.environ.get("FLASK_HTTPS", "0") == "1",
    )

    csrf = CSRFProtect(app)

    @app.context_processor
    def inject_csrf_token():
        from flask_wtf.csrf import generate_csrf
        return {"csrf_token": generate_csrf}

    @app.errorhandler(CSRFError)
    def handle_csrf_error(e):
        return jsonify({
            "error": "CSRF validation failed"
        }), 400

    init_db(db_path)
    db_pool = DatabasePool(db_path)
    indexer = Indexer(folder, db_path)

    @app.route('/api/photos')
    def api_photos():
        page = max(1, request.args.get('page', 1, type=int))
        per_page = max( 1, min( request.args.get('per_page', PER_PAGE, type=int), 500))
        search = request.args.get('search', '').strip()
        sort = request.args.get('sort', 'date')
        order = request.args.get('order', 'desc')

        try:
            if search:
                safe = search.replace('"', '""').replace("'", "''")
                ids = []

                try:
                    rows = db_pool.execute(
                        "SELECT rowid FROM photos_fts WHERE photos_fts MATCH ? ORDER BY rank LIMIT 10000",
                        (f'"{safe}"*',)
                    )
                    ids = [r[0] for r in rows]
                except Exception as e:
                    print(f"Something went wrong: {e}")

                if not ids:
                    rows = db_pool.execute(
                        "SELECT id FROM photos WHERE filename LIKE ? LIMIT 10000",
                        (f'%{search}%',)
                    )
                    ids = [r[0] for r in rows]

                total = len(ids)
                page_ids = ids[(page - 1) * per_page: page * per_page]

                if page_ids:
                    placeholders = ','.join('?' * len(page_ids))
                    rows = db_pool.execute(f"""
                        SELECT id, filename, width, height, exif_date, file_modified,
                               dominant_color, thumb_webp IS NOT NULL as has_webp,
                               tags_json IS NOT NULL as has_tags
                        FROM photos WHERE id IN ({placeholders})
                    """, tuple(page_ids))

                    id_map = {r['id']: dict(r) for r in rows}
                    photos = [id_map[i] for i in page_ids if i in id_map]
                else:
                    photos = []
            else:
                order_sql = "DESC" if order == 'desc' else "ASC"
                order_by = {
                    'date': f"COALESCE(exif_date, file_modified) {order_sql}",
                    'name': f"filename {order_sql}",
                }.get(sort, f"id {order_sql}")

                total_row = db_pool.execute_one("SELECT COUNT(*) as cnt FROM photos")
                total = total_row['cnt'] if total_row else 0

                rows = db_pool.execute(f"""
                    SELECT id, filename, width, height, exif_date, file_modified,
                           dominant_color, thumb_webp IS NOT NULL as has_webp,
                           tags_json IS NOT NULL as has_tags
                    FROM photos ORDER BY {order_by} LIMIT ? OFFSET ?
                """, (per_page, (page - 1) * per_page))
                photos = [dict(r) for r in rows]

            for p in photos:
                date_str = p.get('exif_date') or p.get('file_modified') or ''
                p['date_group'] = date_str[:10] if date_str else ''

        except Exception as e:
            print(f"API error: {e}")

            return jsonify({
                'photos': [],
                'total': 0,
                'page': page,
                'per_page': per_page,
                'error': 'Internal server error'
            }), 500


        return jsonify({
            'photos': photos, 'total': total,
            'page': page, 'per_page': per_page
        })

    @app.route('/api/photo/<int:photo_id>', methods=['GET'])
    def api_photo(photo_id):
        try:
            row = db_pool.execute_one("SELECT * FROM photos WHERE id = ?", (photo_id,))
        except Exception as e:
            return jsonify({'error': str(e)}), 500

        if not row:
            return jsonify({'error': 'Not found'}), 404

        d = dict(row)
        d['tags'] = json.loads(d['tags_json']) if d.get('tags_json') else {}
        d['categories'] = json.loads(d['categories_json']) if d.get('categories_json') else {}
        d['date'] = d.get('exif_date') or d.get('file_modified')
        if (
            d.get('exif_gps_lat') is not None
            and d.get('exif_gps_lon') is not None
        ):
            d['gps'] = {
                'lat': d['exif_gps_lat'],
                'lon': d['exif_gps_lon']
            }
        else:
            d['gps'] = None


        filepath = d.get('filepath', '')
        d['file_accessible'] = safe_check_exists(filepath)

        for key in ['thumbnail', 'thumb_webp', 'embedding', 'tags_json', 'categories_json']:
            d.pop(key, None)

        return jsonify(d)

    @app.route('/api/photo/<int:photo_id>', methods=['DELETE'])
    def api_delete_photo(photo_id):
        try:
            row = db_pool.execute_one(
                "SELECT filepath, file_hash FROM photos WHERE id = ?",
                (photo_id,)
            )


            if not row:
                return jsonify({'success': False, 'error': 'Photo not found'}), 404

            filepath = row['filepath']

            if safe_check_exists(filepath):
                try:
                    os.remove(filepath)
                except Exception as e:
                    print(f"Warning: Could not delete file {filepath}: {e}")
                    return jsonify({
                        'success': False,
                        'error': f'Could not delete image file: {e}'
                    }), 500

            with db_lock:
                conn = get_db(db_path)
                try:
                    conn.execute(
                        "DELETE FROM photos WHERE id = ?",
                        (photo_id,)
                    )

                    try:
                        conn.execute(
                            "DELETE FROM photos_fts WHERE rowid = ?",
                            (photo_id,)
                        )
                    except Exception as e:
                        print(f"FTS delete warning: {e}")

                finally:
                    conn.close()

            thumb_cache.delete(f"thumb_{row['file_hash']}_webp")



            return jsonify({'success': True})


        except Exception as e:
            print(f"Delete error: {e}")
            return jsonify({'success': False, 'error': str(e)}), 500

    @app.route('/api/photos/batch')
    def api_photos_batch():
        ids = request.args.get('ids', '')
        if not ids:
            return jsonify({'photos': []})

        try:
            id_list = [int(i) for i in ids.split(',')[:100]]
            placeholders = ','.join('?' * len(id_list))
            rows = db_pool.execute(f"""
                SELECT id, filename, width, height, exif_date, file_modified,
                       dominant_color, thumb_webp IS NOT NULL as has_webp,
                       tags_json IS NOT NULL as has_tags
                FROM photos WHERE id IN ({placeholders})
            """, tuple(id_list))

            return jsonify({'photos': [dict(r) for r in rows]})
        except Exception as e:
            return jsonify({'error': str(e)}), 500

    @app.route('/api/stats')
    def api_stats():
        try:
            total = db_pool.execute_one("SELECT COUNT(*) as cnt FROM photos")
            tagged = db_pool.execute_one(
                "SELECT COUNT(*) as cnt FROM photos WHERE tags_json IS NOT NULL"
            )
            date_range = db_pool.execute_one("""
                SELECT MIN(COALESCE(exif_date, file_modified)) as oldest,
                       MAX(COALESCE(exif_date, file_modified)) as newest
                FROM photos
            """)

            return jsonify({
                'total': total['cnt'] if total else 0,
                'with_tags': tagged['cnt'] if tagged else 0,
                'folder': str(folder),
                'oldest': date_range['oldest'] if date_range else None,
                'newest': date_range['newest'] if date_range else None,
            })
        except Exception as e:
            return jsonify({'error': str(e)}), 500

    @app.route('/api/rescan', methods=['POST'])
    def api_rescan():
        try:
            count = indexer.quick_scan(show_progress=True)
            return jsonify({'new_images': count, 'success': True})
        except Exception as e:
            print(f"Rescan error: {e}")
            return jsonify({'error': str(e), 'new_images': 0}), 500

    @app.route('/api/debug/path/<int:photo_id>')
    def api_debug_path(photo_id):
        """Debug endpoint to diagnose path issues."""
        row = db_pool.execute_one(
            "SELECT id, filepath, filename FROM photos WHERE id = ?", (photo_id,)
        )
        if not row:
            return jsonify({'error': 'Not found'}), 404

        filepath = row['filepath']
        info = {
            'id': row['id'],
            'filename': row['filename'],
            'filepath_stored': filepath,
            'filepath_repr': repr(filepath),
            'filepath_len': len(filepath),
            'os_name': os.name,
        }

        problematic = []
        for i, ch in enumerate(filepath):
            code = ord(ch)
            if code > 127:
                problematic.append({
                    'pos': i, 'char': ch,
                    'unicode': f'U+{code:04X}', 'name': repr(ch)
                })
            elif ch in '<>"|?*' and i > 1:  
                problematic.append({
                    'pos': i, 'char': ch, 'note': 'invalid on Windows'
                })
        info['problematic_chars'] = problematic

        tests = {}

        try:
            tests['os.path.exists'] = os.path.exists(filepath)
        except Exception as e:
            tests['os.path.exists'] = f'ERROR: {e}'

        try:
            tests['Path.exists'] = Path(filepath).exists()
        except Exception as e:
            tests['Path.exists'] = f'ERROR: {e}'

        try:
            with open(filepath, 'rb') as f:
                f.read(1)
            tests['open_read'] = True
        except Exception as e:
            tests['open_read'] = f'ERROR: {e}'

        if os.name == 'nt':
            abs_path = os.path.abspath(filepath)
            ext_path = '\\\\?\\' + abs_path
            info['extended_path'] = ext_path
            try:
                with open(ext_path, 'rb') as f:
                    f.read(1)
                tests['extended_path_read'] = True
            except Exception as e:
                tests['extended_path_read'] = f'ERROR: {e}'

        info['access_tests'] = tests

        data, err = safe_read_file(filepath)
        info['safe_read_success'] = data is not None
        if err:
            info['safe_read_error'] = err
        if data:
            info['file_size_bytes'] = len(data)

        return jsonify(info)

    @app.route('/thumbnail/<int:photo_id>')
    def serve_thumbnail(photo_id):

        try:
            row = db_pool.execute_one(
                "SELECT thumb_webp, filepath, file_hash FROM photos WHERE id = ?",
                (photo_id,)
            )
        except Exception:
            return Response(status=500)

        if not row:
            return Response(status=404)

        # IMPORTANT: cache by the actual image hash, NOT the database ID.
        cache_key = f"thumb_{row['file_hash']}_webp"

        cached = thumb_cache.get(cache_key)

        if cached:
            return Response(
                cached,
                mimetype='image/webp',
                headers={
                    'Cache-Control': 'no-store, no-cache, must-revalidate, max-age=0',
                    'Pragma': 'no-cache'
                }
            )

        thumb = row['thumb_webp']

        if not thumb:
            try:
                filepath = row['filepath']
                file_data, err = safe_read_file(filepath)

                if file_data is None:
                    print(f"Thumb gen failed for id={photo_id}: {err}")
                    return Response(status=404)

                img = Image.open(BytesIO(file_data))
                img.load()

                thumb = make_thumbnail_webp(img)

                img.close()

                db_pool.execute_write(
                    "UPDATE photos SET thumb_webp = ? WHERE id = ?",
                    (thumb, photo_id)
                )

            except Exception as e:
                print(f"Thumb gen error id={photo_id}: {e}")
                return Response(status=404)

        thumb_cache.set(cache_key, thumb)

        return Response(
            thumb,
            mimetype='image/webp',
            headers={
                'Cache-Control': 'no-store, no-cache, must-revalidate, max-age=0',
                'Pragma': 'no-cache'
            }
        )



    @app.route('/thumbnails/batch')
    def serve_thumbnails_batch():
        ids = request.args.get('ids', '')
        if not ids:
            return Response(status=400)

        try:
            id_list = [int(i) for i in ids.split(',')[:50]]
        except:
            return Response(status=400)

        placeholders = ','.join('?' * len(id_list))
        col = 'thumb_webp'


        rows = db_pool.execute(f"""
            SELECT id, {col} as thumb FROM photos WHERE id IN ({placeholders})
        """, tuple(id_list))

        import base64
        result = {}
        for row in rows:
            if row['thumb']:
                result[str(row['id'])] = base64.b64encode(row['thumb']).decode('ascii')

        return jsonify(result)

    @app.route('/image/<int:photo_id>')
    def serve_image(photo_id):
        try:
            row = db_pool.execute_one(
                "SELECT filepath, filename, file_hash FROM photos WHERE id = ?",
                (photo_id,)
            )

        except Exception as e:
            print(f"DB error for image/{photo_id}: {e}")
            return Response(status=500)

        if not row:
            return Response(status=404)

        filepath = row['filepath']
        filename = row['filename']

        data, err = safe_read_file(filepath)

        if data is None:
            print(f"Image read failed id={photo_id}: {err}")
            print(f"  Path: {repr(filepath)}")

            data = _try_find_and_read(filename, folder)

            if data is None:
                return Response(status=404)
            else:
                print(f"  Found via filename search: {filename}")

        ext = os.path.splitext(filename)[1].lower()
        mime_types = {
            '.jpg': 'image/jpeg', '.jpeg': 'image/jpeg',
            '.png': 'image/png', '.gif': 'image/gif',
            '.webp': 'image/webp', '.bmp': 'image/bmp',
            '.tiff': 'image/tiff',
        }
        mimetype = mime_types.get(ext, 'image/jpeg')

        return Response(
            data,
            mimetype=mimetype,
            headers={
                'Cache-Control': 'no-store, no-cache, must-revalidate, max-age=0',
                'Pragma': 'no-cache',
                'Content-Length': str(len(data)),
            }
        )


    def _try_find_and_read(filename: str, base_folder: Path) -> bytes | None:
        """
        Last-resort: walk the folder tree looking for a file by name.
        If found, also update the DB with the correct path.
        """
        try:
            for dirpath, _, filenames in os.walk(base_folder):
                if filename in filenames:
                    found_path = os.path.join(dirpath, filename)
                    data, err = safe_read_file(found_path)
                    if data is not None:

                        db_pool.execute_write(
                            "UPDATE photos SET filepath = ? WHERE filename = ?",
                            (found_path, filename)
                        )
                        return data
        except Exception:
            pass
        return None

    @app.route('/')
    def gallery():
        return render_template('gallery.html')

    print("Scanning...")
    indexer.quick_scan()
    indexer.background_scan(interval=120)

    return app


def main():
    folder = Path(r"C:\Users\biere\Downloads\Images")


    if not folder.exists():
        print(f"Folder not found: {folder}")
        return

    db_path = folder / '.photos.db'
    print(f"\n Photo Gallery")
    print(f"   Folder: {folder}")
    print(f"   URL: http://localhost:5000\n")
    app = create_app(folder, db_path)
    app.run(host='127.0.0.1', port=5000, debug=False, use_reloader=False)


if __name__ == "__main__":
    main()
