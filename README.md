# ImageviewerAI
A local-first, AI-powered photo manager for large personal image libraries.

ImageviewerAI is a self-hosted photo browser and search engine designed for people who want the convenience of AI-powered photo organization without uploading their library to a cloud service.

It indexes your existing folders, extracts metadata, generates thumbnails, analyzes images with local AI models, and makes the resulting library searchable through a web interface.

Local-first: your photos and AI processing stay on your machine. No cloud account or external AI API is required.

# Why ImageviewerAI?
Large photo collections become difficult to manage once they contain tens or hundreds of thousands of files.

Traditional file browsers are good at navigating folders, but poor at answering questions like:

- "Find photos of my dog."
- "Show me pictures containing a bicycle."
- "Find the photo where I am standing next to a car."
- "Search for text visible in a photo."
- "Find visually similar images."
- "Show me everything taken in a particular location."
- ImageviewerAI combines traditional photo-library indexing with local computer vision and semantic search to make those queries possible.

## System Architecture & AI Pipeline
The system is built as a multi-stage pipeline, orchestrating models locally to extract deep metadata without cloud reliance.
|Phase|Model|Domain|Impact|
|-|-|-|-|
|1|RAM++|Multi-label Tagging|Generates high-confidence keyword tags (e.g., Industrial, circuitry, outdoor).|
|2|SigLIP|Semantic Embedding|Powers vector-based search and zero-shot classification for conceptual queries.|
|3|BLIP|Visual Prompting|Generates descriptive natural language captions for enhanced context.|
|4|EasyOCR|Text Extraction|Digitizes text within images (OCR), enabling searchability for technical documents.|

This runs locally on your machine (GPU recommended). Once complete, photos get an AI badge and become searchable by content. 
All models are downloaded automatically on first run.

# Photo library
- Index existing folders without reorganizing your files
- Detect new, modified, moved, and removed files
- Content hashing for duplicate/moved-file detection
- EXIF metadata extraction
- Date and location information
- Automatic thumbnail generation
- Efficient browsing of large libraries
  
# Search
Search combines traditional metadata with AI-generated information.

Depending on the indexed data, you can search using:

- filenames
- folders
- dates
- EXIF metadata
 -detected tags
- OCR text
- generated captions
- semantic similarity
- SQLite FTS5 is used for full-text search.

# Architecture
At a high level, ImageviewerAI follows this pipeline:

                    Photo folders
                         │
                         ▼
                  Filesystem scanner
                         │
               ┌─────────┴─────────┐
               │                   │
               ▼                   ▼
          File metadata        Content hash
               │                   │
               └─────────┬─────────┘
                         ▼
                      SQLite
                         │
              ┌──────────┼──────────┐
              │          │          │
              ▼          ▼          ▼
            Tags       OCR       Captions
              │          │          │
              └──────────┼──────────┘
                         ▼
                    Embeddings
                         │
                         ▼
                    Search / API
                         │
                         ▼
                    Web interface

The application uses SQLite with WAL mode for persistent metadata and FTS5 for full-text search.

A background indexing process handles expensive operations such as image analysis and thumbnail generation so that the web interface remains responsive while a library is being processed.

# Privacy
Privacy is one of the main reasons ImageviewerAI exists.

# Local processing
Images are processed by models running on your own machine. ImageviewerAI does not require:

- a cloud photo provider
- an AI API key
- uploading your library to a third-party service
- a subscription
- Your original image files remain in their existing locations.

# Important note about metadata
ImageviewerAI can read metadata such as GPS coordinates from image EXIF data. If the application is made accessible to other devices or networks, treat the generated metadata and API endpoints as potentially sensitive.

For maximum privacy, run the application only on a trusted machine/network and review the deployment configuration before exposing it externally.

# Installation
# Requirements
Python 3.10+
A machine with enough RAM/VRAM for the selected AI models
Your existing photo library
GPU acceleration is recommended for large libraries, although the exact requirements depend on which models you enable.

# Clone the repository
```
git clone https://github.com/berend21/ImageviewerAI.git
cd ImageviewerAI
```
# Install dependencies
```
pip install -r requirements.txt
```
# Start ImageviewerAI
```
python appim.py
```
Then open the local web interface in your browser.

The exact startup command and configuration may change as the project evolves. Check the repository configuration for the current recommended setup.

# Indexing a library
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

# Performance
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

# Project status
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

# Security
ImageviewerAI is primarily designed for local/self-hosted use.

If you expose the application beyond localhost, you should place it behind an appropriate authentication and network security layer.

In particular, be careful when exposing an application that can:

access your photo library
expose image files
expose EXIF metadata
modify/delete indexed files
Do not expose an unprotected development instance directly to the public internet.


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
- Make locations searchable on a map and visible on the map. 
- Fix full-text search so document text become searchable. 

