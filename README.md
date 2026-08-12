# ImageviewerAI
A self-hosted, offline-first photo gallery that runs in your browser — like Google Photos, but fully local. Point it at a folder, and it automatically indexes your images, generates thumbnails, and lets you search them using AI-powered tags, captions, and semantic understanding.

Start page
<img width="1918" height="921" alt="Screenshot 2026-08-11 143344" src="https://github.com/user-attachments/assets/576ada08-2c96-4710-ad7b-6200302da700" />
Searching 'electrical'
<img width="1916" height="775" alt="Screenshot 2026-08-11 143527" src="https://github.com/user-attachments/assets/5b92c4a0-7b69-42c4-8540-bef38b5fb8a8" />
Searching 'bicycle'
<img width="1915" height="776" alt="Screenshot 2026-08-11 143602" src="https://github.com/user-attachments/assets/aa727074-43c3-4a72-a9da-210258202f9a" />
Searching 'tree'
<img width="1914" height="545" alt="Screenshot 2026-08-11 143817" src="https://github.com/user-attachments/assets/c88639f0-3955-4377-b54a-8ed38ea4e6b3" />

## ✨ Features

- **Browser-based gallery** — clean dark UI with masonry grid layout
- **Auto-indexing** — scans your image folder on startup and re-scans in the background every 2 minutes
- **AI tagging** — run the categorizer manually to tag images with RAM++; tagged photos show an `AI` badge
- **Semantic search** — search by concept (e.g. `electrical`, `sunset`, `engine`) using SigLIP embeddings
- **Full-text search** — FTS5-powered search over filenames, captions, tags, OCR text
- **EXIF extraction** — date, camera model, GPS coordinates
- **WebP thumbnails** — fast-loading, cached in-memory LRU cache
- **Offline** — no cloud, no telemetry, everything stays on your machine
- **Windows path support** — handles long paths, Unicode filenames, and UNC paths

---


Tags are stated from several models and categorized in database
<img width="1459" height="867" alt="Screenshot 2026-08-11 144051" src="https://github.com/user-attachments/assets/0179f613-ea30-4949-8fb0-8ce5639c572e" />

