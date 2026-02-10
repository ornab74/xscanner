# XScanner

AX Scanner (X dashboard) is a Flask app that combines X feed scanning, risk scoring, and quantum/LLM tooling. This README lists the deployment environment variables and common runtime notes.

## Required environment variables

These must be set before starting the app:

- `INVITE_CODE_SECRET_KEY` — secret used for session/CSRF derivations.
- `admin_username` — bootstrap admin username.
- `admin_pass` — bootstrap admin password (must pass the strength checks in `main.py`).

## Recommended base settings

- `REGISTRATION_ENABLED` — enable/disable self-service registration (`true`/`false`).
- `ENCRYPTION_PASSPHRASE` — passphrase for sealed vaults (auto-generated if missing).
- `STRICT_PQ2_ONLY` — `1` enforces PQ-only encryption; `0` allows hybrid fallback.
- `QRS_ENABLE_SEALED` — enable sealed store (`1`/`0`).
- `QRS_BOOTSTRAP_SHOW` — `1` to print bootstrap exports on startup.
- `QRS_ROTATE_SESSION_KEY` — `1` to enable rolling session key derivation.
- `QRS_SESSION_KEY_ROTATION_PERIOD_SECONDS` — rotation window (default `1800`).
- `QRS_SESSION_KEY_ROTATION_LOOKBACK` — number of key windows to accept (default `8`).
- `QRS_COMPRESS_MIN` — minimum payload size before compression (bytes).
- `QRS_ENV_CAP_BYTES` — max envelope size for encrypted blobs.
- `QRS_BG_LOCK_PATH` — lock file path for background workers.

## LLM provider configuration

OpenAI:
- `OPENAI_API_KEY` (or `OPENAI_KEY`) — OpenAI API key.
- `OPENAI_MODEL` — default OpenAI model (defaults to `gpt-5.2`).
- `OPENAI_REASONING_EFFORT` — reasoning effort for OpenAI responses.

Grok:
- `GROK_API_KEY` — Grok API key.
- `XAI_API_KEY` — XAI API key (preferred over per-user vault storage).
- `XAI_MODEL` — default XAI model name (e.g. `grok-2`).

Switches:
- `USE_GROK` — enable Grok calls (`1`/`0`).
- `USE_CHATGPT` — enable OpenAI calls (`1`/`0`).
- `DUAL_READINGS` — enable dual LLM readings (`1`/`0`).

Local Llama:
- `LLAMA_MODELS_DIR` — model directory (default `/var/data/models`).
- `LLAMA_MODEL_REPO` — model download repo URL.
- `LLAMA_MODEL_FILE` — model file name.
- `LLAMA_EXPECTED_SHA256` — checksum used to validate the model download.

## X dashboard / feed controls

- `RGN_X_TEST_API` — `synthetic` or URL to inject test payloads.
- `RGN_X_TEST_SEED` — seed for synthetic payloads.
- `RGN_X_FETCH_MAX` — max tweets per fetch.
- `RGN_LABEL_BATCH` — max label batch size.
- `RGN_X2_CAROUSEL_MIN_DWELL` — min carousel dwell seconds.
- `RGN_X2_CAROUSEL_MAX_DWELL` — max carousel dwell seconds.
- `RGN_X2_CAROUSEL_MAX_ITEMS` — carousel cap.
- `RGN_X2_MAX_STORE` — max stored posts.
- `RGN_X2_DEFAULT_MODEL` — default labeling model.

Autonomous runner:
- `RGN_AUTON_START` — daily start window (`HH:MM`).
- `RGN_AUTON_END` — daily end window (`HH:MM`).
- `RGN_AUTON_INTERVAL_S` — repeat interval seconds.
- `RGN_AUTON_TZ` — timezone (default `America/New_York`).

Networking:
- `RGN_HTTP_TIMEOUT` — outbound HTTP timeout seconds.
- `RGN_SOCIAL_DB` — sqlite path for the X social store.

## Geocoding / weather

- `WEATHER_LLM_MODEL` — model used for weather prompts.
- `REVGEOCODE_CACHE_TTL_S` — reverse geocode cache TTL.
- `NOMINATIM_URL` — override Nominatim endpoint.
- `NOMINATIM_USER_AGENT` — custom UA for Nominatim.
- `DISABLE_NOMINATIM` — `1` to disable Nominatim lookups.

## Media vault and cache

- `X_MEDIA_MAX_MB` — maximum uploaded media size (MB).
- `X_MEDIA_CHUNK_KB` — chunk size for encrypted uploads (KB).
- `X_MEDIA_TTL_S` — TTL for encrypted media.
- `X_CACHE_TTL_S` — TTL for the per-user cache bucket.

## Blog backup

- `BLOG_BACKUP_PATH` — location for blog backups (default `/var/data/blog_posts_backup.json`).

## Quick start (local)

```bash
export INVITE_CODE_SECRET_KEY="devsecret"
export admin_username="admin"
export admin_pass="AdminPass123!"
export REGISTRATION_ENABLED=true
export STRICT_PQ2_ONLY=0
python main.py
```

Open `http://localhost:3000/x` after logging in.
