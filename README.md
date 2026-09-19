# ImageviewerAI
### 🔎 Search your personal photo library with local AI

ImageviewerAI is a privacy-first, self-hosted photo browser that brings
AI-powered search to your existing image folders — without uploading
your photos to the cloud.

Start page
<img width="1918" height="921" alt="Screenshot 2026-08-11 143344" src="https://github.com/user-attachments/assets/576ada08-2c96-4710-ad7b-6200302da700" />
Searching 'electrical'
<img width="1916" height="775" alt="Screenshot 2026-08-11 143527" src="https://github.com/user-attachments/assets/5b92c4a0-7b69-42c4-8540-bef38b5fb8a8" />
Searching 'bicycle'
<img width="1915" height="776" alt="Screenshot 2026-08-11 143602" src="https://github.com/user-attachments/assets/aa727074-43c3-4a72-a9da-210258202f9a" />
Searching 'tree'
<img width="1914" height="545" alt="Screenshot 2026-08-11 143817" src="https://github.com/user-attachments/assets/c88639f0-3955-4377-b54a-8ed38ea4e6b3" />


## Why ImageviewerAI?

Your photos already live in folders. ImageviewerAI indexes them in place
instead of forcing you to migrate your library into another platform.

With local AI, you can search for things such as:

- 🐕 Photos containing a dog
- 🚲 Photos containing bicycles
- ⚡ Electrical equipment
- 📄 Text appearing inside documents
- 🌲 Outdoor / nature scenes
- 📍 Photos with GPS information
- 🔎 Visually or semantically similar images

No cloud upload. No AI API key. No subscription.

## Features

### 📁 Photo library

- Index existing folders without moving your files
- Recursive directory scanning
- Detect new and modified images
- Detect moved files using content hashes
- EXIF metadata extraction
- GPS coordinates
- Automatic thumbnails
- Large-library browsing

### 🤖 Local AI

- Automatic image tagging
- Semantic embeddings
- Image captions
- OCR
- Zero-shot classification
- Background processing
- GPU acceleration when available

### 🔎 Search

Search across:

- filenames
- folders
- dates
- EXIF metadata
- AI-generated tags
- captions
- OCR text
- semantic embeddings

### 🔐 Privacy

- Photos remain in their original locations
- AI processing runs locally
- No cloud photo service required
- No external AI API required
- No subscription


## Local AI pipeline

ImageviewerAI runs several computer-vision models locally to enrich your
photo library with searchable information.

| Model | Purpose |
|---|---|
| RAM++ | Automatic image tagging |
| SigLIP | Semantic embeddings and zero-shot classification |
| BLIP | Image captions |
| EasyOCR | Text extraction |

The resulting metadata is stored locally and can be searched without
sending your images to an external service.

```
Image
 │
 ├── EXIF ──────────────┐
 │                      │
 ├── Thumbnail          │
 │                      ▼
 └── AI processing ──► SQLite
       │                │
       ├── Tags         │
       ├── Captions     │
       ├── OCR          │
       └── Embeddings   │
                        │
                        ▼
                   Search/API
                        │
                        ▼
                  Web interface
```

## Important note about metadata
ImageviewerAI can read metadata such as GPS coordinates from image EXIF data. If the application is made accessible to other devices or networks, treat the generated metadata and API endpoints as potentially sensitive.

For maximum privacy, run the application only on a trusted machine/network and review the deployment configuration before exposing it externally.

## Installation
### Requirements
Python 3.10+
A machine with enough RAM/VRAM for the selected AI models
Your existing photo library
GPU acceleration is recommended for large libraries, although the exact requirements depend on which models you enable.

## Clone the repository
```
git clone https://github.com/berend21/ImageviewerAI.git
cd ImageviewerAI
```
## Install dependencies
```
pip install -r requirements.txt
```
## Start ImageviewerAI
```
python appim.py
```
Then open the local web interface in your browser.

The exact startup command and configuration may change as the project evolves. Check the repository configuration for the current recommended setup.

## Indexing a library
Point ImageviewerAI at an existing photo directory.

The indexer keeps track of files using metadata and content hashes, allowing it to avoid unnecessarily reprocessing unchanged files.

A typical workflow looks like:

Initial scan
    ↓
Read filesystem metadata
    ↓
Identify new/changed files
    ↓
Extract EXIF
    ↓
Generate thumbnails
    ↓
Run AI processing
    ↓
Store metadata + embeddings
    ↓
Searchable library

Subsequent scans can skip files that have not changed.

## Performance
Performance depends heavily on:

- number of images
- image resolution
- CPU
- GPU
- available RAM/VRAM
- enabled AI models
- filesystem/storage speed
- The expensive part of indexing is generally AI inference rather than database operations.

For large libraries, ImageviewerAI is therefore designed around incremental/background processing rather than requiring the entire library to be analyzed before it can be used.

Benchmarks for specific hardware are planned. Until reproducible benchmarks are available, performance claims should be treated as workload-dependent.

## Project status
ImageviewerAI is an actively developed personal project.

The core photo indexing and browsing functionality is usable, while the architecture and feature set are still evolving.

Areas of ongoing development include:

- search quality
- indexing performance
- AI model optimization
- library scalability
- UI improvements
- reliability and error handling
- automated testing
- deployment and security hardening

## ⚠️ Security

ImageviewerAI is intended primarily for trusted, local networks.

The application can expose:

- your images
- image metadata
- GPS coordinates
- filesystem information
- indexed photo operations

Do not expose the development server directly to the public internet.

If you need remote access, put ImageviewerAI behind appropriate
authentication and network controls.


Clicking on imges opens modal with all information and coordinates are clickable to google maps location.
<img width="1919" height="915" alt="Screenshot 2026-08-12 141808" src="https://github.com/user-attachments/assets/32ac1301-3f51-4456-abde-3fda20e0ccfa" />

<img width="1459" height="867" alt="Screenshot 2026-08-11 144051" src="https://github.com/user-attachments/assets/0179f613-ea30-4949-8fb0-8ce5639c572e" />

## Project status

🚧 **Early / active development**

ImageviewerAI is currently usable for local photo indexing, browsing and
AI-assisted search, but the project is still evolving.

### Working

- [x] Recursive image indexing
- [x] SQLite metadata database
- [x] Thumbnail generation
- [x] EXIF extraction
- [x] Content hashing
- [x] Web gallery
- [x] AI tagging
- [x] Semantic embeddings
- [x] Image captions
- [x] OCR

### In progress

- [ ] Search quality improvements
- [ ] Faster AI processing
- [ ] Person recognition/search
- [ ] Map-based location browsing
- [ ] Improved document/OCR search
- [ ] Automated tests
- [ ] Deployment hardening

## Known limitations

- Large sequential image browsing can occasionally cause the web UI to hang.
- OCR/full-text document search is still being improved.
- AI processing performance depends heavily on hardware.
- There are currently limited automated tests.

## Roadmap

- Person identification and named people
- Map-based photo browsing
- Faster semantic search
- Improved GPU utilization
- Better deployment options

## Technology

| Component | Technology |
|---|---|
| Backend | Python / Flask |
| Database | SQLite |
| Full-text search | SQLite FTS5 |
| Image processing | Pillow |
| AI inference | PyTorch |
| Semantic search | SigLIP |
| Image tagging | RAM++ |
| Captioning | BLIP |
| OCR | EasyOCR |
| Frontend | HTML / CSS / JavaScript |
