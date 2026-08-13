# ImageviewerAI
An engineering-grade, self-hosted photo gallery that brings the power of Google Photos to your local machine. This project focuses on Privacy-by-Design, high-performance data handling, and local Edge-AI orchestration.

## 🏗 System Architecture & AI Pipeline
The system is built as a multi-stage pipeline, orchestrating models locally to extract deep metadata without cloud reliance.
|Phase|Model|Domain|Impact|
|-|-|-|-|
|1|RAM++|Multi-label Tagging|Generates high-confidence keyword tags (e.g., Industrial, circuitry, outdoor).|
|2|SigLIP|Semantic Embedding|Powers vector-based search and zero-shot classification for conceptual queries.|
|3|BLIP|Visual Prompting|Generates descriptive natural language captions for enhanced context.|
|4|EasyOCR|Text Extraction|Digitizes text within images (OCR), enabling searchability for technical documents.|

All models are downloaded automatically on first run.

## 🛠 Engineering Highlights

*   **Asynchronous Model Orchestration:** Developed a multi-stage AI pipeline that sequentially triggers **RAM++**, **SigLIP**, and **BLIP** models to extract structured metadata without blocking the main UI thread.
*   **High-Concurrency Database Architecture:** Optimized **SQLite (WAL mode)** with a custom **Connection Pool** and **FTS5 (Full-Text Search)** indexing to provide sub-second search results across thousands of documents and images.
*   **Custom LRU Caching Layer:** Engineered an in-memory **Least Recently Used (LRU) cache** for JIT (Just-In-Time) WebP thumbnail transcoding, significantly reducing disk I/O and front-end latency.
*   **Robust File System Integration:** Implemented "Safe Read" logic to handle complex Windows environments, including UNC paths, Unicode character sets, and Long Path (260+ char) edge cases.
*   **Semantic Vector Embedding:** Leveraged **SigLIP embeddings** to enable natural language "concept search," allowing users to query images by abstract descriptions rather than just filenames.

---

## ✨ Features

- **Browser-based gallery** — clean dark UI with masonry grid layout
- **Auto-indexing** — scans your image folder on startup and re-scans in the background every 2 minutes
- **AI tagging** — run the categorizer manually to tag images with RAM++; tagged photos show an `AI` badge
- **Semantic search** — search by concept (e.g. `electrical`, `sunset`, `engine`) using SigLIP embeddings
- **Full-text search** — FTS5-powered search over filenames, captions, tags, OCR text (not yet working perfect)
- **EXIF extraction** — date, camera model, GPS coordinates
- **WebP thumbnails** — fast-loading, cached in-memory LRU cache
- **Offline** — no cloud, no telemetry, everything stays on your machine
- **Windows path support** — handles long paths, Unicode filenames, and UNC paths


This runs locally on your machine (GPU recommended). Once complete, photos get an AI badge and become searchable by content. 


Start page
<img width="1918" height="921" alt="Screenshot 2026-08-11 143344" src="https://github.com/user-attachments/assets/576ada08-2c96-4710-ad7b-6200302da700" />
Searching 'electrical'
<img width="1916" height="775" alt="Screenshot 2026-08-11 143527" src="https://github.com/user-attachments/assets/5b92c4a0-7b69-42c4-8540-bef38b5fb8a8" />
Searching 'bicycle'
<img width="1915" height="776" alt="Screenshot 2026-08-11 143602" src="https://github.com/user-attachments/assets/aa727074-43c3-4a72-a9da-210258202f9a" />
Searching 'tree'
<img width="1914" height="545" alt="Screenshot 2026-08-11 143817" src="https://github.com/user-attachments/assets/c88639f0-3955-4377-b54a-8ed38ea4e6b3" />



Clicking on imges opens modal with all information and coordinates are clickable to google maps location.
<img width="1919" height="915" alt="Screenshot 2026-08-12 141808" src="https://github.com/user-attachments/assets/32ac1301-3f51-4456-abde-3fda20e0ccfa" />

  

<img width="1459" height="867" alt="Screenshot 2026-08-11 144051" src="https://github.com/user-attachments/assets/0179f613-ea30-4949-8fb0-8ce5639c572e" />

Future ideas:
- optimize system further to search faster and do AI classification faster. Also webpage sometimes hangs when viewing many images after each other. 
- Add database of known persons linked to image so images can be linked to certain person names. That way I can search images based on names.
- Fix full-text search so document text become searchable. 

