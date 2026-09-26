"""Download and verify the exact BillBot Market Updater snapshot used by Android v1.4.46.

Source of truth:
  https://github.com/oswade/bbdata/releases/latest/download/manifest.json

The BillBot Market Updater Android app publishes ``manifest.json`` and ``latest.db.gz``
(as well as a browser projection). Android v1.4.46 follows the manifest's ``download_url``
to ``latest.db.gz``. This module deliberately does the same: it does not use a separate
agent snapshot and does not depend on GitHub Actions.
"""
from __future__ import annotations

import datetime as dt
import gzip
import hashlib
import json
import os
import re
import sqlite3
import tempfile
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Any, Dict, Optional, Tuple

DEFAULT_MANIFEST_URL = "https://github.com/oswade/bbdata/releases/latest/download/manifest.json"
USER_AGENT = "BillBot-Agent/1.2 (Android-v1.4.46-compatible market client)"
MANIFEST_FORMAT_VERSION = 1
SNAPSHOT_FORMAT_VERSION = 2
NORMALIZER_VERSION = 1
EXPECTED_PUBLISHER_PREFIX = "BillBot Market Updater Android"
MAX_MANIFEST_BYTES = 128 * 1024
MAX_COMPRESSED_BYTES = 250 * 1024 * 1024
MAX_UNCOMPRESSED_BYTES = 750 * 1024 * 1024
_HEX64 = re.compile(r"^[0-9a-fA-F]{64}$")
_REQUIRED_TABLES = {"energy_plans", "cdr_plans", "sync_state", "nbn_offers", "savings_products"}


def _https(url: str) -> str:
    parsed = urllib.parse.urlparse(str(url or ""))
    if parsed.scheme.lower() != "https" or not parsed.hostname:
        raise ValueError("BillBot market downloads must use an absolute HTTPS URL.")
    return url


def _resolve_https(base_url: str, value: str) -> str:
    return _https(urllib.parse.urljoin(base_url, str(value or "")))


def _check_final_https(response: Any) -> None:
    final = getattr(response, "geturl", lambda: "")() or ""
    if final:
        _https(final)


def _read_small_url(url: str, *, max_bytes: int, timeout: int = 30) -> bytes:
    request = urllib.request.Request(_https(url), headers={
        "User-Agent": USER_AGENT,
        "Accept": "application/json,application/octet-stream,*/*",
        "Cache-Control": "no-cache",
        "Pragma": "no-cache",
    })
    with urllib.request.urlopen(request, timeout=timeout) as response:
        _check_final_https(response)
        length = response.headers.get("Content-Length")
        if length and int(length) > max_bytes:
            raise ValueError(f"Download refused: Content-Length {length} exceeds safety limit.")
        data = response.read(max_bytes + 1)
        if len(data) > max_bytes:
            raise ValueError("Download exceeded safety limit.")
        return data


def _parse_time(value: Any) -> dt.datetime:
    text = str(value or "").strip()
    if not text:
        raise ValueError("BillBot manifest has no generation timestamp.")
    try:
        parsed = dt.datetime.fromisoformat(text.replace("Z", "+00:00"))
    except ValueError as exc:
        raise ValueError("BillBot manifest generation timestamp is invalid.") from exc
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=dt.timezone.utc)
    return parsed.astimezone(dt.timezone.utc)


def fetch_manifest(manifest_url: str = DEFAULT_MANIFEST_URL) -> Dict[str, Any]:
    """Fetch and validate the same manifest contract Android v1.4.46 accepts."""
    raw = _read_small_url(manifest_url, max_bytes=MAX_MANIFEST_BYTES, timeout=30)
    manifest = json.loads(raw.decode("utf-8"))
    if not isinstance(manifest, dict):
        raise ValueError("BillBot manifest was not a JSON object.")

    if int(manifest.get("manifest_format_version") or 0) != MANIFEST_FORMAT_VERSION:
        raise ValueError("Unsupported BillBot market manifest format.")
    if int(manifest.get("snapshot_format_version") or 0) != SNAPSHOT_FORMAT_VERSION:
        raise ValueError("Unsupported BillBot market snapshot format.")
    normalizer = int(manifest.get("normalizer_version") or 0)
    if normalizer < 1 or normalizer > NORMALIZER_VERSION:
        raise ValueError("BillBot market snapshot requires a newer normalizer/client.")

    snapshot_id = str(manifest.get("snapshot_id") or "")
    compressed_sha = str(manifest.get("sha256") or "")
    database_sha = str(manifest.get("database_sha256") or "")
    if not _HEX64.fullmatch(snapshot_id):
        raise ValueError("BillBot market snapshot_id is invalid.")
    if not _HEX64.fullmatch(compressed_sha):
        raise ValueError("BillBot market compressed SHA-256 is invalid.")
    if database_sha and not _HEX64.fullmatch(database_sha):
        raise ValueError("BillBot market database SHA-256 is invalid.")

    generated = _parse_time(manifest.get("generated_at"))
    if generated > dt.datetime.now(dt.timezone.utc) + dt.timedelta(days=1):
        raise ValueError("BillBot market generation timestamp is implausibly in the future.")

    compressed_bytes = int(manifest.get("compressed_bytes") or -1)
    uncompressed_bytes = int(manifest.get("uncompressed_bytes") or -1)
    if not 1 <= compressed_bytes <= MAX_COMPRESSED_BYTES:
        raise ValueError("BillBot market compressed size is invalid.")
    if not 1 <= uncompressed_bytes <= MAX_UNCOMPRESSED_BYTES:
        raise ValueError("BillBot market uncompressed size is invalid.")

    publisher = str(manifest.get("publisher") or "").strip()
    if not publisher.startswith(EXPECTED_PUBLISHER_PREFIX):
        raise ValueError(
            "BillBot manifest was not published by the BillBot Market Updater Android app; "
            "refusing a legacy/unknown publisher snapshot."
        )

    download_url = _resolve_https(manifest_url, str(manifest.get("download_url") or ""))
    if Path(urllib.parse.urlparse(download_url).path).name != "latest.db.gz":
        raise ValueError("BillBot Market Updater manifest must point to latest.db.gz.")
    manifest["download_url"] = download_url
    counts = manifest.get("counts") if isinstance(manifest.get("counts"), dict) else {}
    if int(counts.get("electricity_plans") or 0) <= 0:
        raise ValueError("BillBot manifest reports no electricity plans; refusing snapshot.")
    if int(counts.get("gas_plans") or 0) <= 0:
        raise ValueError("BillBot manifest reports no gas plans; snapshot is not the Android market snapshot.")
    if int(counts.get("savings_products") or 0) <= 0:
        raise ValueError("BillBot manifest reports no Banking savings products; snapshot is not the Android market snapshot.")
    return manifest


def _download_to_file(
    url: str,
    destination: Path,
    expected_sha256: str,
    expected_bytes: int,
    *,
    timeout: int = 240,
) -> int:
    request = urllib.request.Request(_https(url), headers={
        "User-Agent": USER_AGENT,
        "Accept": "application/gzip,application/octet-stream,*/*",
        "Cache-Control": "no-cache",
        "Pragma": "no-cache",
    })
    h = hashlib.sha256()
    total = 0
    with urllib.request.urlopen(request, timeout=timeout) as response, destination.open("wb") as out:
        _check_final_https(response)
        length = response.headers.get("Content-Length")
        if length:
            length_i = int(length)
            if length_i > MAX_COMPRESSED_BYTES:
                raise ValueError("Snapshot Content-Length exceeds safety limit.")
            if expected_bytes > 0 and length_i != expected_bytes:
                raise ValueError("Snapshot HTTP size differs from the BillBot manifest.")
        while True:
            chunk = response.read(1024 * 1024)
            if not chunk:
                break
            total += len(chunk)
            if total > MAX_COMPRESSED_BYTES:
                raise ValueError("Snapshot download exceeded safety limit.")
            h.update(chunk)
            out.write(chunk)
    if expected_bytes > 0 and total != expected_bytes:
        destination.unlink(missing_ok=True)
        raise ValueError(f"BillBot snapshot size mismatch: expected {expected_bytes}, got {total} bytes.")
    if h.hexdigest().lower() != expected_sha256.lower():
        destination.unlink(missing_ok=True)
        raise ValueError("BillBot snapshot SHA-256 did not match manifest; download rejected.")
    return total


def _gunzip_bounded(source: Path, destination: Path, expected_bytes: int) -> str:
    digest = hashlib.sha256()
    total = 0
    with gzip.open(source, "rb") as src, destination.open("wb") as dst:
        while True:
            chunk = src.read(1024 * 1024)
            if not chunk:
                break
            total += len(chunk)
            if total > MAX_UNCOMPRESSED_BYTES:
                raise ValueError("BillBot database expanded beyond the safety limit.")
            if expected_bytes > 0 and total > expected_bytes:
                raise ValueError("BillBot database expanded beyond its declared manifest size.")
            digest.update(chunk)
            dst.write(chunk)
    if expected_bytes > 0 and total != expected_bytes:
        destination.unlink(missing_ok=True)
        raise ValueError(f"BillBot database size mismatch: expected {expected_bytes}, got {total} bytes.")
    return digest.hexdigest()


def _cache_root(cache_dir: Optional[str] = None) -> Path:
    requested = cache_dir or os.environ.get("BILLBOT_CACHE_DIR")
    candidates = [Path(requested)] if requested else [Path.home() / ".cache" / "billbot-agent"]
    if not requested:
        candidates.append(Path(tempfile.gettempdir()) / "billbot-agent-cache")
    last_error: Optional[Exception] = None
    for root in candidates:
        try:
            root.mkdir(parents=True, exist_ok=True)
            probe = root / ".write-test"
            probe.write_bytes(b"")
            probe.unlink(missing_ok=True)
            return root
        except Exception as exc:  # pragma: no cover - environment-specific fallback
            last_error = exc
    raise OSError(f"No writable BillBot cache directory was available: {last_error}")


def _sync_state(con: sqlite3.Connection) -> Dict[str, str]:
    return {str(row[0]): str(row[1] if row[1] is not None else "") for row in con.execute("SELECT key,value FROM sync_state")}


def _validate_sqlite(path: Path, manifest: Dict[str, Any], *, require_generated_at: bool) -> None:
    """Mirror Android v1.4.46's cloud-snapshot validation contract."""
    con = sqlite3.connect(str(path))
    try:
        result = con.execute("PRAGMA integrity_check").fetchone()
        if not result or str(result[0]).lower() != "ok":
            raise ValueError(f"SQLite integrity check failed: {result}")

        tables = {str(row[0]) for row in con.execute("SELECT name FROM sqlite_master WHERE type='table'")}
        missing = _REQUIRED_TABLES - tables
        if missing:
            raise ValueError("Snapshot is missing Android market table(s): " + ", ".join(sorted(missing)))

        energy = int(con.execute("SELECT COUNT(*) FROM energy_plans WHERE COALESCE(is_active,1)=1").fetchone()[0])
        electricity = int(con.execute("SELECT COUNT(*) FROM energy_plans WHERE COALESCE(is_active,1)=1 AND UPPER(fuel_type)='ELECTRICITY'").fetchone()[0])
        gas = int(con.execute("SELECT COUNT(*) FROM energy_plans WHERE COALESCE(is_active,1)=1 AND UPPER(fuel_type)='GAS'").fetchone()[0])
        savings = int(con.execute("SELECT COUNT(*) FROM savings_products").fetchone()[0])
        incomplete = int(con.execute(
            "SELECT COUNT(*) FROM energy_plans WHERE COALESCE(is_active,1)=1 AND "
            "(COALESCE(summary_json,'')='' OR COALESCE(detail_json,'')='' OR COALESCE(detail_cached,0)<>1)"
        ).fetchone()[0])
        newer = int(con.execute(
            "SELECT COUNT(*) FROM energy_plans WHERE COALESCE(is_active,1)=1 AND COALESCE(normalizer_version,0)>?",
            (NORMALIZER_VERSION,),
        ).fetchone()[0])
        if energy <= 0 or electricity <= 0 or gas <= 0 or savings <= 0:
            raise ValueError("Snapshot does not contain the usable Energy + Banking baseline required by Android v1.4.46.")
        if incomplete:
            raise ValueError(f"Snapshot contains {incomplete} incomplete active Energy rows.")
        if newer:
            raise ValueError(f"Snapshot contains {newer} Energy rows from a newer normalizer.")

        counts = manifest.get("counts") if isinstance(manifest.get("counts"), dict) else {}
        actual = {
            "energy_plans": energy,
            "electricity_plans": electricity,
            "gas_plans": gas,
            "savings_products": savings,
        }
        for key, value in actual.items():
            if key in counts and int(counts.get(key) or -1) != value:
                raise ValueError(f"BillBot manifest count mismatch for {key}: manifest={counts.get(key)}, database={value}.")

        state = _sync_state(con)
        if int(state.get("cloud_snapshot_format_version", "0") or 0) != int(manifest.get("snapshot_format_version") or 0):
            raise ValueError("Snapshot internal format version differs from manifest.")
        if state.get("cloud_snapshot_id", "").lower() != str(manifest.get("snapshot_id") or "").lower():
            raise ValueError("Snapshot internal cloud_snapshot_id differs from manifest.")
        if int(state.get("cloud_normalizer_version", "0") or 0) != int(manifest.get("normalizer_version") or 0):
            raise ValueError("Snapshot internal normalizer version differs from manifest.")
        if require_generated_at and state.get("cloud_generated_at", "") != str(manifest.get("generated_at") or ""):
            raise ValueError("Snapshot internal generation timestamp differs from manifest.")
    finally:
        con.close()



def _newer_cached_snapshot(root: Path, manifest: Dict[str, Any]) -> Optional[Tuple[str, Dict[str, Any]]]:
    """Return a locally cached snapshot newer than the currently advertised cloud manifest.

    Android v1.4.46 never rolls a device backwards when a stale/rolled-back latest release is
    observed. Mirror that behaviour for long-lived agent/MCP caches.
    """
    advertised_time = _parse_time(manifest.get("generated_at"))
    advertised_id = str(manifest.get("snapshot_id") or "").lower()
    best: Optional[Tuple[dt.datetime, Path, Dict[str, Any]]] = None
    for meta_path in root.glob("*-android-market.manifest.json"):
        try:
            cached_manifest = json.loads(meta_path.read_text(encoding="utf-8"))
            cached_id = str(cached_manifest.get("snapshot_id") or "").lower()
            if not _HEX64.fullmatch(cached_id) or cached_id == advertised_id:
                continue
            cached_time = _parse_time(cached_manifest.get("generated_at"))
            if cached_time <= advertised_time:
                continue
            db_path = root / f"{cached_id}-android-market.db"
            if not db_path.exists():
                continue
            # A semantically identical snapshot can be republished with a new generated_at, so
            # cached validation intentionally keys on its snapshot metadata rather than requiring
            # the database's embedded timestamp to equal the latest publication timestamp.
            _validate_sqlite(db_path, cached_manifest, require_generated_at=False)
            if best is None or cached_time > best[0]:
                best = (cached_time, db_path, cached_manifest)
        except Exception:
            continue
    if best is None:
        return None
    return str(best[1]), best[2]

def get_market_database(
    manifest_url: str = DEFAULT_MANIFEST_URL,
    cache_dir: Optional[str] = None,
    force: bool = False,
) -> Tuple[str, Dict[str, Any]]:
    """Return the verified ``latest.db.gz`` database advertised by the Market Updater manifest.

    Cache identity follows Android: ``snapshot_id`` is a semantic fingerprint. If the updater
    republishes an unchanged market with a new generated_at timestamp, the same cached semantic
    snapshot can be reused without re-downloading hundreds of MB.
    """
    manifest = fetch_manifest(manifest_url)
    root = _cache_root(cache_dir)

    # Match Android's stale-cloud guard: if GitHub's current Latest release ever rolls back to an
    # older snapshot, do not replace a newer already-verified local cache with it.
    if not force:
        newer_cached = _newer_cached_snapshot(root, manifest)
        if newer_cached is not None:
            return newer_cached

    snapshot = str(manifest["snapshot_id"]).lower()
    db_path = root / f"{snapshot}-android-market.db"
    meta_path = root / f"{snapshot}-android-market.manifest.json"

    if db_path.exists() and meta_path.exists() and not force:
        try:
            # generated_at may legitimately differ when Market Updater republishes an unchanged
            # semantic snapshot; Android v1.4.46 also treats the snapshot_id as the no-change key.
            _validate_sqlite(db_path, manifest, require_generated_at=False)
            meta_path.write_text(json.dumps(manifest, indent=2, sort_keys=True), encoding="utf-8")
            return str(db_path), manifest
        except Exception:
            db_path.unlink(missing_ok=True)
            meta_path.unlink(missing_ok=True)

    gz_fd, gz_name = tempfile.mkstemp(prefix="billbot-", suffix=".db.gz", dir=root)
    os.close(gz_fd)
    gz_path = Path(gz_name)
    db_fd, db_name = tempfile.mkstemp(prefix="billbot-", suffix=".db", dir=root)
    os.close(db_fd)
    temp_db = Path(db_name)
    try:
        _download_to_file(
            manifest["download_url"],
            gz_path,
            str(manifest["sha256"]),
            int(manifest["compressed_bytes"]),
        )
        raw_sha = _gunzip_bounded(gz_path, temp_db, int(manifest["uncompressed_bytes"]))
        expected_raw = str(manifest.get("database_sha256") or "").lower()
        if expected_raw and raw_sha.lower() != expected_raw:
            raise ValueError("Uncompressed BillBot database SHA-256 did not match manifest.")
        _validate_sqlite(temp_db, manifest, require_generated_at=True)
        os.replace(temp_db, db_path)
        meta_path.write_text(json.dumps(manifest, indent=2, sort_keys=True), encoding="utf-8")
    finally:
        gz_path.unlink(missing_ok=True)
        temp_db.unlink(missing_ok=True)

    cached = sorted(root.glob("*-android-market.db"), key=lambda p: p.stat().st_mtime, reverse=True)
    for stale in cached[2:]:
        stale.unlink(missing_ok=True)
        stale.with_suffix(".manifest.json").unlink(missing_ok=True)
    return str(db_path), manifest
