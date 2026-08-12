"""
Image categorization script that works with the existing photos database.
Processes images that don't have tags/categories yet.
Uses: RAM++ (tagging), SigLIP (embeddings + zero-shot), BLIP (captions), EasyOCR
"""

import os
import sys
import json
import argparse
import gc
import warnings
import sqlite3
import struct
from pathlib import Path
from datetime import datetime, timezone
from typing import Optional
from dataclasses import dataclass, field

import numpy as np
import torch
import torch.nn.functional as F
from PIL import Image
from tqdm import tqdm

warnings.filterwarnings("ignore", category=UserWarning)


@dataclass
class Config:
    # Image settings
    image_extensions: set = field(default_factory=lambda: {
        '.jpg', '.jpeg', '.png', '.webp', '.bmp', '.gif', '.tiff'
    })
    max_image_size: int = 1024

    # Device
    device: str = "cuda" if torch.cuda.is_available() else "cpu"

    # Batch sizes
    batch_size_siglip: int = 8
    batch_size_ram: int = 4

    # Model settings
    siglip_model: str = "google/siglip-so400m-patch14-384"
    tag_threshold: float = 0.5
    category_threshold: float = 0.3

    # OCR
    ocr_languages: list = field(default_factory=lambda: ["en"])

    # Custom categories for zero-shot classification
    custom_categories: list = field(default_factory=lambda: [
        # Activities
        "hiking", "swimming", "cooking", "reading", "working at desk",
        "traveling", "party", "wedding", "birthday celebration", "concert",
        "sports", "exercise", "camping", "fishing", "gardening",
        # Nature
        "mountain landscape", "beach", "forest", "lake", "river",
        "sunset", "sunrise", "night sky", "flowers", "wildlife",
        "garden", "park", "desert", "snow scene", "autumn leaves",
        # People
        "portrait", "group photo", "selfie", "family gathering",
        "friends", "children playing", "baby", "couple",
        # Technical/Work
        "industrial machinery", "manufacturing equipment", "factory floor",
        "electronic components", "circuit board", "engine", "motor",
        "mechanical parts", "tools", "measurement equipment",
        "technical diagram", "blueprint", "schematic", "CAD drawing",
        "laboratory equipment", "scientific instrument", "control panel",
        "construction site", "heavy equipment", "vehicle engine",
        "electrical wiring", "plumbing", "HVAC system",
        # Documents
        "document", "receipt", "invoice", "screenshot",
        "presentation slide", "chart", "graph", "handwritten note",
        # Places
        "indoor", "outdoor", "home interior", "office", "restaurant",
        "city street", "rural area", "architecture", "building exterior",
        # Objects
        "food", "meal", "vehicle", "car", "furniture",
        "product photo", "packaging",
        # Photo types
        "professional photo", "casual photo", "black and white",
        "aerial view", "macro shot", "panorama",
    ])


CONFIG = Config()


# ---------------------------------------------------------------------------
# Database helper — talks directly to the backend's photos table
# ---------------------------------------------------------------------------

class PhotosDB:
    """
    Wraps the existing .photos.db used by the Flask backend.
    Ensures all needed columns exist, reads/writes the same rows.
    """

    # Columns this script needs that might not exist yet
    REQUIRED_COLUMNS = {
        "tags_json":         "TEXT",
        "categories_json":   "TEXT",
        "caption":           "TEXT",
        "detailed_caption":  "TEXT",
        "ocr_text":          "TEXT",
        "embedding":         "BLOB",
        "processed_at":      "TEXT",
    }

    def __init__(self, db_path: Path):
        self.db_path = db_path
        self._ensure_columns()

    def _get_conn(self) -> sqlite3.Connection:
        conn = sqlite3.connect(str(self.db_path), timeout=30)
        conn.row_factory = sqlite3.Row
        conn.execute("PRAGMA journal_mode=WAL")
        conn.execute("PRAGMA busy_timeout=30000")
        return conn

    def _ensure_columns(self):
        """Add any missing columns to the photos table."""
        conn = self._get_conn()
        try:
            existing = {
                row[1]
                for row in conn.execute("PRAGMA table_info(photos)").fetchall()
            }
            for col, col_type in self.REQUIRED_COLUMNS.items():
                if col not in existing:
                    print(f"  Adding column: {col} ({col_type})")
                    conn.execute(
                        f"ALTER TABLE photos ADD COLUMN {col} {col_type}"
                    )
        finally:
            conn.close()

    # ------ Queries used by the processor ------

    def get_unprocessed_ids(self) -> list[dict]:
        """
        Return rows where processing hasn't happened yet.
        'Not processed' = processed_at IS NULL
        This means: first run tags everything, subsequent runs skip them.
        """
        conn = self._get_conn()
        try:
            rows = conn.execute("""
                SELECT id, filepath, filename
                FROM photos
                WHERE processed_at IS NULL
                ORDER BY id
            """).fetchall()
            return [dict(r) for r in rows]
        finally:
            conn.close()

    def get_needs_tags(self) -> list[dict]:
        """Photos that have no tags yet."""
        conn = self._get_conn()
        try:
            rows = conn.execute("""
                SELECT id, filepath, filename
                FROM photos
                WHERE tags_json IS NULL
                ORDER BY id
            """).fetchall()
            return [dict(r) for r in rows]
        finally:
            conn.close()

    def get_needs_categories(self) -> list[dict]:
        """Photos that have no categories yet."""
        conn = self._get_conn()
        try:
            rows = conn.execute("""
                SELECT id, filepath, filename
                FROM photos
                WHERE categories_json IS NULL
                ORDER BY id
            """).fetchall()
            return [dict(r) for r in rows]
        finally:
            conn.close()

    def get_needs_caption(self) -> list[dict]:
        """Photos that have no caption yet."""
        conn = self._get_conn()
        try:
            rows = conn.execute("""
                SELECT id, filepath, filename
                FROM photos
                WHERE caption IS NULL
                ORDER BY id
            """).fetchall()
            return [dict(r) for r in rows]
        finally:
            conn.close()

    def get_needs_ocr(self) -> list[dict]:
        """Photos that have no OCR text yet."""
        conn = self._get_conn()
        try:
            rows = conn.execute("""
                SELECT id, filepath, filename
                FROM photos
                WHERE ocr_text IS NULL
                ORDER BY id
            """).fetchall()
            return [dict(r) for r in rows]
        finally:
            conn.close()

    def get_needs_embedding(self) -> list[dict]:
        """Photos that have no embedding yet."""
        conn = self._get_conn()
        try:
            rows = conn.execute("""
                SELECT id, filepath, filename
                FROM photos
                WHERE embedding IS NULL
                ORDER BY id
            """).fetchall()
            return [dict(r) for r in rows]
        finally:
            conn.close()

    def update_tags(self, photo_id: int, tags: dict):
        conn = self._get_conn()
        try:
            conn.execute(
                "UPDATE photos SET tags_json = ? WHERE id = ?",
                (json.dumps(tags), photo_id)
            )
            conn.commit()
        finally:
            conn.close()

    def update_categories(self, photo_id: int, categories: dict):
        conn = self._get_conn()
        try:
            conn.execute(
                "UPDATE photos SET categories_json = ? WHERE id = ?",
                (json.dumps(categories), photo_id)
            )
            conn.commit()
        finally:
            conn.close()

    def update_captions(self, photo_id: int, caption: str, detailed: str):
        conn = self._get_conn()
        try:
            conn.execute(
                "UPDATE photos SET caption = ?, detailed_caption = ? WHERE id = ?",
                (caption, detailed, photo_id)
            )
            conn.commit()
        finally:
            conn.close()

    def update_ocr(self, photo_id: int, text: str):
        conn = self._get_conn()
        try:
            conn.execute(
                "UPDATE photos SET ocr_text = ? WHERE id = ?",
                (text, photo_id)
            )
            conn.commit()
        finally:
            conn.close()

    def update_embedding(self, photo_id: int, embedding: np.ndarray):
        blob = embedding.astype(np.float32).tobytes()
        conn = self._get_conn()
        try:
            conn.execute(
                "UPDATE photos SET embedding = ? WHERE id = ?",
                (blob, photo_id)
            )
            conn.commit()
        finally:
            conn.close()

    def mark_processed(self, photo_id: int):
        now = datetime.now(timezone.utc).isoformat()
        conn = self._get_conn()
        try:
            conn.execute(
                "UPDATE photos SET processed_at = ? WHERE id = ?",
                (now, photo_id)
            )
            conn.commit()
        finally:
            conn.close()

    def mark_processed_batch(self, photo_ids: list[int]):
        now = datetime.now(timezone.utc).isoformat()
        conn = self._get_conn()
        try:
            conn.executemany(
                "UPDATE photos SET processed_at = ? WHERE id = ?",
                [(now, pid) for pid in photo_ids]
            )
            conn.commit()
        finally:
            conn.close()

    def update_fts(self, photo_id: int):
        """Rebuild FTS entry for one photo after we added text data."""
        conn = self._get_conn()
        try:
            # Check FTS table exists
            has_fts = conn.execute(
                "SELECT name FROM sqlite_master "
                "WHERE type='table' AND name='photos_fts'"
            ).fetchone()
            if not has_fts:
                return

            row = conn.execute("""
                SELECT filename, caption, detailed_caption, ocr_text,
                       tags_json, categories_json
                FROM photos WHERE id = ?
            """, (photo_id,)).fetchone()

            if not row:
                return

            tags_text = ""
            cats_text = ""
            if row["tags_json"]:
                try:
                    tags_text = " ".join(json.loads(row["tags_json"]).keys())
                except Exception:
                    pass
            if row["categories_json"]:
                try:
                    cats_text = " ".join(json.loads(row["categories_json"]).keys())
                except Exception:
                    pass

            # Delete old entry then insert fresh
            conn.execute("DELETE FROM photos_fts WHERE rowid = ?", (photo_id,))
            conn.execute("""
                INSERT INTO photos_fts(
                    rowid, filename, caption, detailed_caption,
                    ocr_text, tags_text, categories_text
                ) VALUES (?, ?, ?, ?, ?, ?, ?)
            """, (
                photo_id,
                row["filename"] or "",
                row["caption"] or "",
                row["detailed_caption"] or "",
                row["ocr_text"] or "",
                tags_text,
                cats_text,
            ))
            conn.commit()
        except Exception as e:
            print(f"  FTS update warning for id={photo_id}: {e}")
        finally:
            conn.close()

    def get_total(self) -> int:
        conn = self._get_conn()
        try:
            row = conn.execute("SELECT COUNT(*) as cnt FROM photos").fetchone()
            return row["cnt"] if row else 0
        finally:
            conn.close()

    def get_processed_count(self) -> int:
        conn = self._get_conn()
        try:
            row = conn.execute(
                "SELECT COUNT(*) as cnt FROM photos WHERE processed_at IS NOT NULL"
            ).fetchone()
            return row["cnt"] if row else 0
        finally:
            conn.close()

    def get_all_embeddings(self) -> tuple[list[int], Optional[np.ndarray]]:
        conn = self._get_conn()
        try:
            rows = conn.execute(
                "SELECT id, embedding FROM photos WHERE embedding IS NOT NULL"
            ).fetchall()
            if not rows:
                return [], None
            ids = []
            embs = []
            for r in rows:
                ids.append(r["id"])
                embs.append(np.frombuffer(r["embedding"], dtype=np.float32))
            return ids, np.stack(embs)
        finally:
            conn.close()


# ---------------------------------------------------------------------------
# GPU helpers
# ---------------------------------------------------------------------------

def clear_vram():
    gc.collect()
    if torch.cuda.is_available():
        torch.cuda.empty_cache()
        torch.cuda.synchronize()


# ---------------------------------------------------------------------------
# Models (same logic as before, cleaned up)
# ---------------------------------------------------------------------------

class SigLIPModel:
    def __init__(self):
        self.device = CONFIG.device
        self.model = None
        self.processor = None

    def load(self):
        from transformers import AutoProcessor, AutoModel
        print(f"  Loading SigLIP ({CONFIG.siglip_model.split('/')[-1]})...")
        self.processor = AutoProcessor.from_pretrained(CONFIG.siglip_model)
        self.model = AutoModel.from_pretrained(
            CONFIG.siglip_model, torch_dtype=torch.float16
        ).to(self.device).eval()
        print("  SigLIP ready")

    def unload(self):
        del self.model, self.processor
        self.model = self.processor = None
        clear_vram()

    @torch.no_grad()
    def get_embeddings(self, images: list[Image.Image]) -> np.ndarray:
        inputs = self.processor(images=images, return_tensors="pt", padding=True)
        inputs = {k: v.to(self.device) for k, v in inputs.items()}
        outputs = self.model.get_image_features(**inputs)
        embeddings = F.normalize(outputs, p=2, dim=-1)
        return embeddings.cpu().float().numpy()

    @torch.no_grad()
    def classify_zero_shot(
        self, images: list[Image.Image], categories: list[str]
    ) -> list[dict]:
        texts = [f"a photo of {cat}" for cat in categories]
        text_inputs = self.processor(
            text=texts, return_tensors="pt",
            padding="max_length", truncation=True
        )
        text_inputs = {k: v.to(self.device) for k, v in text_inputs.items()}
        text_embeds = self.model.get_text_features(**text_inputs)
        text_embeds = F.normalize(text_embeds, p=2, dim=-1)

        img_inputs = self.processor(
            images=images, return_tensors="pt", padding=True
        )
        img_inputs = {k: v.to(self.device) for k, v in img_inputs.items()}
        image_embeds = self.model.get_image_features(**img_inputs)
        image_embeds = F.normalize(image_embeds, p=2, dim=-1)

        logit_scale = self.model.logit_scale.exp()
        logits = image_embeds @ text_embeds.T * logit_scale
        probs = torch.sigmoid(logits)

        results = []
        for prob_row in probs.cpu():
            result = {
                cat: round(float(p), 4)
                for cat, p in zip(categories, prob_row)
                if p > CONFIG.category_threshold
            }
            results.append(
                dict(sorted(result.items(), key=lambda x: x[1], reverse=True))
            )
        return results

    @torch.no_grad()
    def encode_text(self, query: str) -> np.ndarray:
        inputs = self.processor(
            text=[query], return_tensors="pt",
            padding="max_length", truncation=True
        )
        inputs = {k: v.to(self.device) for k, v in inputs.items()}
        text_embeds = self.model.get_text_features(**inputs)
        text_embeds = F.normalize(text_embeds, p=2, dim=-1)
        return text_embeds.cpu().float().numpy().flatten()


class RAMModel:
    def __init__(self):
        self.device = CONFIG.device
        self.model = None
        self.processor = None
        self._use_pipeline = False

    def load(self):
        print("  Loading RAM++...")
        try:
            from transformers import (
                AutoProcessor,
                AutoModelForZeroShotImageClassification,
            )
            self.processor = AutoProcessor.from_pretrained(
                "xinyu1205/recognize-anything-plus-model",
                trust_remote_code=True,
            )
            self.model = (
                AutoModelForZeroShotImageClassification.from_pretrained(
                    "xinyu1205/recognize-anything-plus-model",
                    trust_remote_code=True,
                )
                .to(self.device)
                .eval()
            )
        except Exception:
            print("  RAM++ failed, falling back to BLIP2 pipeline for tags")
            self._load_fallback()
        print("  RAM++ ready")

    def _load_fallback(self):
        from transformers import pipeline
        self.pipe = pipeline(
            "image-to-text",
            model="Salesforce/blip2-opt-2.7b",
            device=0 if self.device == "cuda" else -1,
            torch_dtype=torch.float16,
        )
        self._use_pipeline = True

    def unload(self):
        if self._use_pipeline:
            del self.pipe
        else:
            del self.model, self.processor
        self.model = self.processor = None
        clear_vram()

    @torch.no_grad()
    def tag_images(self, images: list[Image.Image]) -> list[dict]:
        if self._use_pipeline:
            return self._tag_with_pipeline(images)
        results = []
        for img in images:
            try:
                inputs = self.processor(
                    images=img, return_tensors="pt"
                ).to(self.device)
                outputs = self.model(**inputs)
                probs = torch.sigmoid(outputs.logits)[0]
                tags = {}
                for idx, prob in enumerate(probs):
                    if prob > CONFIG.tag_threshold:
                        tag_name = self.model.config.id2label.get(
                            idx, f"tag_{idx}"
                        )
                        tags[tag_name] = round(float(prob), 4)
                results.append(
                    dict(sorted(tags.items(), key=lambda x: x[1], reverse=True))
                )
            except Exception as e:
                print(f"    RAM tag error: {e}")
                results.append({})
        return results

    def _tag_with_pipeline(self, images: list[Image.Image]) -> list[dict]:
        results = []
        for img in images:
            try:
                output = self.pipe(img, max_new_tokens=50)
                caption = output[0]["generated_text"]
                words = caption.lower().replace(",", "").replace(".", "").split()
                tags = {w: 1.0 for w in words if len(w) > 3}
                results.append(tags)
            except Exception:
                results.append({})
        return results


class BLIP2Model:
    def __init__(self):
        self.device = CONFIG.device
        self.pipe_short = None
        self.pipe_detailed = None

    def load(self):
        from transformers import pipeline
        print("  Loading BLIP captioning...")
        self.pipe_short = pipeline(
            "image-to-text",
            model="Salesforce/blip-image-captioning-base",
            device=0 if self.device == "cuda" else -1,
            torch_dtype=torch.float16,
        )
        self.pipe_detailed = pipeline(
            "image-to-text",
            model="Salesforce/blip-image-captioning-large",
            device=0 if self.device == "cuda" else -1,
            torch_dtype=torch.float16,
        )
        print("  BLIP ready (base + large)")

    def unload(self):
        self.pipe_short = self.pipe_detailed = None
        clear_vram()

    def caption(self, image: Image.Image) -> tuple[str, str]:
        image = image.convert("RGB")
        try:
            short = self.pipe_short(image, max_new_tokens=20)[0]["generated_text"]
            detailed = self.pipe_detailed(image, max_new_tokens=50)[0][
                "generated_text"
            ]
            return short, detailed
        except Exception as e:
            print(f"    BLIP error: {e}")
            return "image", "scene"


class EasyOCRModel:
    def __init__(self):
        self.reader = None

    def load(self):
        print("  Loading EasyOCR...")
        try:
            import easyocr
            self.reader = easyocr.Reader(
                ["en"], gpu=torch.cuda.is_available()
            )
            print("  EasyOCR ready")
        except ImportError:
            print("  ⚠ easyocr not installed (pip install easyocr)")

    def unload(self):
        self.reader = None

    def extract_text(self, image: Image.Image) -> str:
        if self.reader is None:
            return ""
        try:
            results = self.reader.readtext(image, detail=0)
            return " ".join(results) if results else ""
        except Exception:
            return ""


# ---------------------------------------------------------------------------
# Image loading helper
# ---------------------------------------------------------------------------

def load_image_for_model(filepath: str, max_size: int = 1024) -> Optional[Image.Image]:
    try:
        img = Image.open(filepath).convert("RGB")
        if max(img.size) > max_size:
            ratio = max_size / max(img.size)
            new_size = (int(img.width * ratio), int(img.height * ratio))
            img = img.resize(new_size, Image.Resampling.LANCZOS)
        return img
    except Exception as e:
        print(f"    Cannot load {filepath}: {e}")
        return None


# ---------------------------------------------------------------------------
# Main processor
# ---------------------------------------------------------------------------

class ImageProcessor:
    def __init__(self, db: PhotosDB):
        self.db = db

    def process_all(self):
        """
        Run every model phase, but only on photos that are missing that data.
        Photos already tagged/captioned/etc. are skipped automatically.
        At the end, mark everything as processed.
        """
        total = self.db.get_total()
        done = self.db.get_processed_count()
        print(f"\n{'='*60}")
        print(f"  Image Categorization Pipeline")
        print(f"  Total photos in DB : {total}")
        print(f"  Already processed  : {done}")
        print(f"  Device             : {CONFIG.device}")
        print(f"{'='*60}")

        # Collect what needs doing
        needs_tags       = self.db.get_needs_tags()
        needs_categories = self.db.get_needs_categories()
        needs_embedding  = self.db.get_needs_embedding()
        needs_caption    = self.db.get_needs_caption()
        needs_ocr        = self.db.get_needs_ocr()

        print(f"\n  Need tags       : {len(needs_tags)}")
        print(f"  Need categories : {len(needs_categories)}")
        print(f"  Need embeddings : {len(needs_embedding)}")
        print(f"  Need captions   : {len(needs_caption)}")
        print(f"  Need OCR        : {len(needs_ocr)}")

        anything = (
            needs_tags or needs_categories or needs_embedding
            or needs_caption or needs_ocr
        )
        if not anything:
            print("\n  ✓ Nothing to do — all photos already processed.")
            return

        # Phase 1: RAM++ tags
        if needs_tags:
            self._run_ram(needs_tags)

        # Phase 2: SigLIP embeddings + zero-shot categories
        # Merge the two need-lists so we load SigLIP only once
        needs_siglip_ids = {r["id"] for r in needs_categories} | {
            r["id"] for r in needs_embedding
        }
        if needs_siglip_ids:
            # Build combined row list (deduplicated)
            id_to_row = {}
            for r in needs_categories + needs_embedding:
                id_to_row[r["id"]] = r
            combined = [id_to_row[i] for i in sorted(needs_siglip_ids)]
            need_cat_ids = {r["id"] for r in needs_categories}
            need_emb_ids = {r["id"] for r in needs_embedding}
            self._run_siglip(combined, need_cat_ids, need_emb_ids)

        # Phase 3: BLIP captions
        if needs_caption:
            self._run_blip(needs_caption)

        # Phase 4: OCR
        if needs_ocr:
            self._run_ocr(needs_ocr)

        # Mark everything processed + rebuild FTS
        all_touched_ids = set()
        for lst in [needs_tags, needs_categories, needs_embedding,
                    needs_caption, needs_ocr]:
            for r in lst:
                all_touched_ids.add(r["id"])

        print(f"\n  Updating FTS for {len(all_touched_ids)} photos...")
        for pid in tqdm(sorted(all_touched_ids), desc="  FTS", leave=False):
            self.db.update_fts(pid)

        self.db.mark_processed_batch(list(all_touched_ids))
        print(f"\n  ✓ Done — {len(all_touched_ids)} photos processed")

    # ---------- per-model phases ----------

    def _load_batch_images(
        self, rows: list[dict]
    ) -> list[tuple[dict, Image.Image]]:
        """Load images for a batch, skip failures."""
        loaded = []
        for r in rows:
            img = load_image_for_model(r["filepath"])
            if img:
                loaded.append((r, img))
        return loaded

    def _run_ram(self, rows: list[dict]):
        print(f"\n  Phase 1/4: RAM++ Tagging ({len(rows)} images)")
        model = RAMModel()
        model.load()

        batch_size = CONFIG.batch_size_ram
        for i in tqdm(range(0, len(rows), batch_size), desc="  Tagging"):
            batch_rows = rows[i : i + batch_size]
            loaded = self._load_batch_images(batch_rows)
            if not loaded:
                continue
            pil_imgs = [img for _, img in loaded]
            try:
                tags_list = model.tag_images(pil_imgs)
                for (row, _), tags in zip(loaded, tags_list):
                    self.db.update_tags(row["id"], tags)
            except Exception as e:
                print(f"    Batch error: {e}")

        model.unload()

    def _run_siglip(
        self,
        rows: list[dict],
        need_cat_ids: set[int],
        need_emb_ids: set[int],
    ):
        total = len(rows)
        print(
            f"\n  Phase 2/4: SigLIP Embeddings & Categories ({total} images)"
        )
        model = SigLIPModel()
        model.load()

        batch_size = CONFIG.batch_size_siglip
        for i in tqdm(range(0, total, batch_size), desc="  SigLIP"):
            batch_rows = rows[i : i + batch_size]
            loaded = self._load_batch_images(batch_rows)
            if not loaded:
                continue
            pil_imgs = [img for _, img in loaded]

            try:
                # Always compute embeddings (cheap, needed for search)
                embeddings = model.get_embeddings(pil_imgs)

                # Zero-shot only if any in this batch need categories
                batch_need_cats = any(
                    r["id"] in need_cat_ids for r, _ in loaded
                )
                if batch_need_cats:
                    cats_list = model.classify_zero_shot(
                        pil_imgs, CONFIG.custom_categories
                    )
                else:
                    cats_list = [None] * len(loaded)

                for idx, ((row, _), emb) in enumerate(zip(loaded, embeddings)):
                    if row["id"] in need_emb_ids:
                        self.db.update_embedding(row["id"], emb)
                    if cats_list[idx] is not None and row["id"] in need_cat_ids:
                        self.db.update_categories(row["id"], cats_list[idx])
            except Exception as e:
                print(f"    Batch error: {e}")

        model.unload()

    def _run_blip(self, rows: list[dict]):
        print(f"\n  Phase 3/4: BLIP Captioning ({len(rows)} images)")
        model = BLIP2Model()
        model.load()

        for row in tqdm(rows, desc="  Captioning"):
            img = load_image_for_model(row["filepath"])
            if not img:
                continue
            try:
                caption, detailed = model.caption(img)
                self.db.update_captions(row["id"], caption, detailed)
            except Exception as e:
                print(f"    Error {row['filename']}: {e}")

        model.unload()

    def _run_ocr(self, rows: list[dict]):
        print(f"\n  Phase 4/4: EasyOCR ({len(rows)} images)")
        model = EasyOCRModel()
        model.load()
        if model.reader is None:
            print("  Skipping OCR (not installed)")
            # Still mark as empty string so we don't retry
            for row in rows:
                self.db.update_ocr(row["id"], "")
            return

        for row in tqdm(rows, desc="  OCR"):
            img = load_image_for_model(row["filepath"])
            if not img:
                self.db.update_ocr(row["id"], "")
                continue
            try:
                text = model.extract_text(img)
                self.db.update_ocr(row["id"], text)
            except Exception as e:
                print(f"    Error {row['filename']}: {e}")
                self.db.update_ocr(row["id"], "")

        model.unload()


# ---------------------------------------------------------------------------
# Search (standalone, for CLI)
# ---------------------------------------------------------------------------

class ImageSearcher:
    def __init__(self, db: PhotosDB):
        self.db = db
        self.siglip = None
        self._ids = None
        self._embeddings = None

    def _ensure_loaded(self):
        if self.siglip is None:
            self.siglip = SigLIPModel()
            self.siglip.load()
        if self._embeddings is None:
            self._ids, self._embeddings = self.db.get_all_embeddings()

    def semantic_search(
        self, query: str, top_k: int = 20
    ) -> list[tuple[int, float]]:
        self._ensure_loaded()
        if self._embeddings is None or len(self._embeddings) == 0:
            return []
        query_emb = self.siglip.encode_text(query)
        sims = self._embeddings @ query_emb
        top_idx = np.argsort(sims)[::-1][:top_k]
        return [(self._ids[i], float(sims[i])) for i in top_idx]

    def unload(self):
        if self.siglip:
            self.siglip.unload()


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Categorize images in the photos database",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  Process images:  python categorize.py
  Custom DB path:  python categorize.py --database ./images/.photos.db
  Search:          python categorize.py --search "sunset beach"
  Stats:           python categorize.py --stats
        """,
    )
    parser.add_argument(
        "--database", "-d",
        type=Path,
        default=Path("./images/.photos.db"),
        help="Path to .photos.db (default: ./images/.photos.db)",
    )
    parser.add_argument("--search", "-s", type=str, help="Semantic search query")
    parser.add_argument("--stats", action="store_true", help="Show database stats")
    parser.add_argument(
        "--force", action="store_true",
        help="Re-process ALL photos (ignore processed_at)",
    )

    args = parser.parse_args()

    if not args.database.exists():
        print(f"\n  ✗ Database not found: {args.database}")
        print(f"    Start the gallery backend first, or specify --database")
        sys.exit(1)

    db = PhotosDB(args.database)

    if args.stats:
        total = db.get_total()
        done = db.get_processed_count()
        print(f"\n  Database       : {args.database}")
        print(f"  Total photos   : {total}")
        print(f"  Processed      : {done}")
        print(f"  Remaining      : {total - done}")
        return

    if args.search:
        print(f"\n  🔍 Searching: '{args.search}'")
        searcher = ImageSearcher(db)
        results = searcher.semantic_search(args.search, top_k=10)
        if results:
            for i, (photo_id, score) in enumerate(results, 1):
                conn = db._get_conn()
                row = conn.execute(
                    "SELECT filename FROM photos WHERE id = ?", (photo_id,)
                ).fetchone()
                conn.close()
                name = row["filename"] if row else f"id={photo_id}"
                print(f"    {i:2d}. {name}  (score: {score:.3f})")
        else:
            print("    No results")
        searcher.unload()
        return

    # Force mode: clear processed_at so everything re-runs
    if args.force:
        print("  Force mode: clearing processed_at for all photos...")
        conn = db._get_conn()
        conn.execute(
            "UPDATE photos SET processed_at = NULL, tags_json = NULL, "
            "categories_json = NULL, caption = NULL, detailed_caption = NULL, "
            "ocr_text = NULL, embedding = NULL"
        )
        conn.commit()
        conn.close()

    processor = ImageProcessor(db)
    processor.process_all()


if __name__ == "__main__":
    main()
