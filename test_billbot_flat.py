import datetime as dt
import gzip
import hashlib
import io
import json
import os
import sqlite3
import tempfile
import unittest
from decimal import Decimal
from pathlib import Path
from unittest import mock

import billbot_core
import market
from bill import normalise_bill
from compare import compare_bill
from seasonality import (
    _profile_for,
    estimate_annual_usage,
    estimate_from_observations,
    expected_share,
)


class FakeResponse(io.BytesIO):
    def __init__(self, data: bytes, *, url: str, content_length: bool = True):
        super().__init__(data)
        self.headers = {"Content-Length": str(len(data))} if content_length else {}
        self._url = url

    def __enter__(self):
        return self

    def __exit__(self, *args):
        self.close()

    def geturl(self):
        return self._url


class BillBotAgentTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.db = os.path.join(self.tmp.name, "market.db")
        json.loads(billbot_core.init_app(self.db))
        # Twelve current residential single-rate products with distinct costs.
        for i in range(12):
            rate = 0.145 + i * 0.0075  # ex-GST dollars/kWh in the CDR fixture
            detail = {
                "planId": f"P{i+1}",
                "fuelType": "ELECTRICITY",
                "displayName": f"Saver {i+1}",
                "customerType": "RESIDENTIAL",
                "brand": f"Energy {i+1}",
                "geography": {"distributors": ["United Energy"]},
                "electricityContract": {
                    "pricingModel": "SINGLE_RATE",
                    "tariffPeriod": [
                        {
                            "rateBlockUType": "singleRate",
                            "dailySupplyCharges": str(0.80 + i * 0.01),
                            "singleRate": {
                                "displayName": "Usage",
                                "rates": [{"unitPrice": str(rate)}],
                            },
                        }
                    ],
                },
            }
            summary = {k: detail[k] for k in ("planId", "fuelType", "displayName", "customerType", "geography")}
            retailer = {
                "name": f"Energy {i+1}",
                "base_uri": f"https://example.test/{i+1}",
                "brand": f"e{i+1}",
                "source": "test",
            }
            record = billbot_core._normalise_plan(retailer, summary, detail, "ELECTRICITY")
            with billbot_core._connect(self.db) as con:
                billbot_core._schema(con)
                billbot_core._upsert_plan(con, record)
                con.commit()
        self.manifest = {
            "manifest_format_version": 1,
            "snapshot_format_version": 2,
            "normalizer_version": 1,
            "snapshot_id": "a" * 64,
            "generated_at": "2026-09-26T00:00:00+00:00",
            "counts": {"electricity_plans": 12, "gas_plans": 1, "savings_products": 1},
            "download_url": "https://github.com/oswade/bbdata/releases/latest/download/latest.db.gz",
            "sha256": "0" * 64,
            "publisher": "BillBot Market Updater Android / GitHub Releases",
            "publisher_version": "1.1.9",
        }

    def tearDown(self):
        self.tmp.cleanup()

    def bill(self):
        return {
            "fuel_type": "ELECTRICITY",
            "customer_type": "RESIDENTIAL",
            "retailer_name": "Current Energy",
            "current_plan_name": "Current Saver",
            "distributor_name": "United Energy",
            "service_postcode": "3168",
            "service_state": "VIC",
            "billing_period_start": "2026-06-09",
            "billing_period_end": "2026-07-08",
            "bill_days": 30,
            "usage_lines": [
                {
                    "description": "Anytime",
                    "kwh": 823.215,
                    "unit_rate_cents": 30.0,
                    "line_total_dollars": 246.9645,
                }
            ],
            "supply_charge_lines": [
                {
                    "description": "Supply",
                    "days": 30,
                    "unit_rate_cents_per_day": 110.0,
                    "line_total_dollars": 33.0,
                }
            ],
            "controlled_load_lines": [],
            "solar_export_lines": [],
            "demand_lines": [],
        }

    def _strict_market_snapshot(self, snapshot_id: str = "b" * 64, generated_at: str = "2026-09-26T00:00:00+00:00", filename: str = "strict-updater.db"):
        """Build the minimum schema accepted by Android-compatible snapshot validation."""
        path = Path(self.tmp.name) / filename
        con = sqlite3.connect(path)
        try:
            con.executescript(
                """
                CREATE TABLE energy_plans(
                    is_active INTEGER, fuel_type TEXT, summary_json TEXT, detail_json TEXT,
                    detail_cached INTEGER, normalizer_version INTEGER
                );
                CREATE TABLE cdr_plans(id INTEGER);
                CREATE TABLE sync_state(key TEXT PRIMARY KEY, value TEXT);
                CREATE TABLE nbn_offers(id INTEGER);
                CREATE TABLE savings_products(id INTEGER);
                """
            )
            summary = json.dumps({"planId": "E1"})
            detail = json.dumps({"planId": "E1", "electricityContract": {}})
            con.execute("INSERT INTO energy_plans VALUES(1,'ELECTRICITY',?,?,1,1)", (summary, detail))
            con.execute("INSERT INTO energy_plans VALUES(1,'GAS',?,?,1,1)", (summary, detail))
            con.execute("INSERT INTO savings_products VALUES(1)")
            state = {
                "cloud_snapshot_format_version": "2",
                "cloud_snapshot_id": snapshot_id,
                "cloud_generated_at": generated_at,
                "cloud_normalizer_version": "1",
            }
            con.executemany("INSERT INTO sync_state(key,value) VALUES(?,?)", state.items())
            con.commit()
        finally:
            con.close()
        raw = path.read_bytes()
        compressed = gzip.compress(raw, mtime=0)
        manifest = {
            "manifest_format_version": 1,
            "snapshot_format_version": 2,
            "normalizer_version": 1,
            "snapshot_id": snapshot_id,
            "generated_at": generated_at,
            "compressed_bytes": len(compressed),
            "uncompressed_bytes": len(raw),
            "sha256": hashlib.sha256(compressed).hexdigest(),
            "database_sha256": hashlib.sha256(raw).hexdigest(),
            "download_url": "https://github.com/oswade/bbdata/releases/latest/download/latest.db.gz",
            "counts": {
                "energy_plans": 2,
                "electricity_plans": 1,
                "gas_plans": 1,
                "savings_products": 1,
            },
            "publisher": "BillBot Market Updater Android / GitHub Releases",
            "publisher_version": "1.1.9",
            # Deliberately include a misleading old experimental field. The v1.0 client must ignore it.
            "agent_energy": {
                "download_url": "https://example.test/agent-energy.db.gz",
                "sha256": "f" * 64,
            },
        }
        return raw, compressed, manifest

    def test_clayton_exact_date_aer_shape_matches_android_reference(self):
        r = estimate_annual_usage(823.215, "2026-06-09", "2026-07-08", postcode="3168", state="VIC")
        self.assertEqual(r.method, "aer_climate_normal_exact_date")
        self.assertAlmostEqual(float(r.adjusted_annual_usage), 8103.9, delta=3.0)
        self.assertLess(float(r.adjusted_annual_usage), float(r.raw_annual_usage))

    def test_cross_year_leap_summer_uses_actual_season_days(self):
        profile, _, _, _ = _profile_for(postcode="3168", state="VIC")
        self.assertIsNotNone(profile)
        share = expected_share(dt.date(2027, 12, 1), dt.date(2028, 2, 29), profile)
        self.assertAlmostEqual(float(share), float(profile[0]), places=12)

    def test_multiple_bills_pool_expected_profile_share(self):
        one = estimate_from_observations(
            [{"start": "2026-06-01", "end": "2026-08-31", "usage": 2000}],
            postcode="3168",
            state="VIC",
        )
        two = estimate_from_observations(
            [
                {"start": "2026-06-01", "end": "2026-08-31", "usage": 2000},
                {"start": "2026-09-01", "end": "2026-11-30", "usage": 1500},
            ],
            postcode="3168",
            state="VIC",
        )
        self.assertEqual(two.observation_count, 2)
        self.assertGreater(two.observed_days, one.observed_days)
        self.assertEqual(two.method, "aer_climate_normal_exact_date")

    def test_more_than_330_noncontiguous_days_still_uses_seasonality(self):
        obs = [
            {"start": f"{year}-06-01", "end": f"{year}-08-31", "usage": 2000}
            for year in (2023, 2024, 2025, 2026)
        ]
        r = estimate_from_observations(obs, postcode="3168", state="VIC")
        self.assertGreater(r.observed_days, 330)
        self.assertEqual(r.method, "aer_climate_normal_exact_date")

    def test_overlapping_bill_is_ignored(self):
        r = estimate_from_observations(
            [
                {"start": "2026-06-01", "end": "2026-08-31", "usage": 2000, "label": "A"},
                {"start": "2026-07-01", "end": "2026-07-31", "usage": 700, "label": "duplicate"},
            ],
            postcode="3168",
            state="VIC",
        )
        self.assertEqual(r.observation_count, 1)
        self.assertTrue(any("overlapping" in x.lower() for x in r.warnings))

    def test_conflicting_exact_duplicate_keeps_first_and_warns(self):
        r = estimate_from_observations(
            [
                {"start": "2026-06-01", "end": "2026-06-30", "usage": 500, "label": "latest"},
                {"start": "2026-06-01", "end": "2026-06-30", "usage": 800, "label": "other"},
            ],
            postcode="3168",
            state="VIC",
        )
        self.assertEqual(r.observation_count, 1)
        self.assertTrue(any("conflicting usage" in x.lower() for x in r.warnings))
        profile, _, _, _ = _profile_for(postcode="3168", state="VIC")
        expected = Decimal("500") / expected_share(dt.date(2026, 6, 1), dt.date(2026, 6, 30), profile)
        self.assertAlmostEqual(float(r.adjusted_annual_usage), float(expected), places=6)


    def test_explicit_bill_days_handles_exclusive_end_date(self):
        b = self.bill()
        b["billing_period_start"] = "2026-06-01"
        b["billing_period_end"] = "2026-07-01"  # 31 inclusive dates, but a 30-day charge period
        b["bill_days"] = 30
        b["usage_lines"] = [{"description": "Anytime", "kwh": 600, "unit_rate_cents": 30, "line_total_dollars": 180}]
        n = normalise_bill(b)
        self.assertEqual(n["bill"]["bill_days"], 30)
        self.assertEqual(n["seasonality"]["observed_days"], 30)
        self.assertTrue(any("bill states 30" in x.lower() for x in n["warnings"]))

    def test_bill_normaliser_separates_controlled_load(self):
        b = self.bill()
        b["controlled_load_lines"] = [
            {"description": "Controlled load", "kwh": 120, "unit_rate_cents": 18, "line_total_dollars": 21.6}
        ]
        n = normalise_bill(b)
        self.assertGreater(n["annual_controlled_load_usage"], 0)
        self.assertAlmostEqual(n["bill"]["general_usage_kwh"], 823.215, places=3)

    def test_supply_rate_weights_total_and_rate_only_rows_together(self):
        b = self.bill()
        b["billing_period_start"] = "2026-06-01"
        b["billing_period_end"] = "2026-06-30"
        b["supply_charge_lines"] = [
            {"days": 10, "line_total_dollars": 10.0, "unit_rate_cents_per_day": 100.0},
            {"days": 20, "unit_rate_cents_per_day": 200.0},
        ]
        n = normalise_bill(b)
        self.assertAlmostEqual(n["current_daily_supply"], 166.6666667, places=5)

    def test_postcode_wins_over_conflicting_state(self):
        b = self.bill()
        b["service_state"] = "QLD"
        n = normalise_bill(b)
        self.assertEqual(n["state"], "VIC")
        self.assertTrue(any("conflicts with service postcode" in x for x in n["warnings"]))

    def test_market_updater_download_exact_latest_db_and_integrity(self):
        raw, compressed, manifest = self._strict_market_snapshot()
        manifest_bytes = json.dumps(manifest).encode()
        responses = [
            FakeResponse(manifest_bytes, url="https://github.com/oswade/bbdata/releases/download/test/manifest.json"),
            FakeResponse(compressed, url="https://objects.githubusercontent.com/test/latest.db.gz"),
        ]
        with tempfile.TemporaryDirectory() as cache, mock.patch(
            "market.urllib.request.urlopen", side_effect=responses
        ) as urlopen:
            db_path, got = market.get_market_database(
                "https://github.com/oswade/bbdata/releases/latest/download/manifest.json", cache_dir=cache
            )
            self.assertTrue(Path(db_path).exists())
            self.assertEqual(got["snapshot_id"], "b" * 64)
            self.assertTrue(got["download_url"].endswith("/latest.db.gz"))
            requested_urls = [call.args[0].full_url for call in urlopen.call_args_list]
            self.assertNotIn("https://example.test/agent-energy.db.gz", requested_urls)
            self.assertTrue(requested_urls[1].endswith("/latest.db.gz"))
            self.assertEqual(Path(db_path).read_bytes(), raw)

    def test_market_rejects_legacy_non_updater_publisher(self):
        _, _, manifest = self._strict_market_snapshot()
        manifest["publisher"] = "GitHub Actions"
        response = FakeResponse(json.dumps(manifest).encode(), url="https://github.com/oswade/bbdata/releases/test/manifest.json")
        with mock.patch("market.urllib.request.urlopen", return_value=response):
            with self.assertRaisesRegex(ValueError, "Market Updater"):
                market.fetch_manifest("https://github.com/oswade/bbdata/releases/latest/download/manifest.json")

    def test_market_rejects_non_latest_db_download_url(self):
        _, _, manifest = self._strict_market_snapshot()
        manifest["download_url"] = "https://github.com/oswade/bbdata/releases/latest/download/web-market.json.gz"
        response = FakeResponse(json.dumps(manifest).encode(), url="https://github.com/oswade/bbdata/releases/test/manifest.json")
        with mock.patch("market.urllib.request.urlopen", return_value=response):
            with self.assertRaisesRegex(ValueError, "latest.db.gz"):
                market.fetch_manifest("https://github.com/oswade/bbdata/releases/latest/download/manifest.json")

    def test_same_snapshot_cache_survives_republish_generated_at_change(self):
        raw, compressed, manifest = self._strict_market_snapshot()
        responses = [
            FakeResponse(json.dumps(manifest).encode(), url="https://github.com/oswade/bbdata/releases/test/manifest.json"),
            FakeResponse(compressed, url="https://objects.githubusercontent.com/test/latest.db.gz"),
        ]
        with tempfile.TemporaryDirectory() as cache:
            with mock.patch("market.urllib.request.urlopen", side_effect=responses):
                first, _ = market.get_market_database(cache_dir=cache)
            republished = dict(manifest)
            republished["generated_at"] = "2026-09-26T01:00:00+00:00"
            with mock.patch(
                "market.urllib.request.urlopen",
                return_value=FakeResponse(json.dumps(republished).encode(), url="https://github.com/oswade/bbdata/releases/test/manifest.json"),
            ) as urlopen:
                second, _ = market.get_market_database(cache_dir=cache)
                self.assertEqual(first, second)
                self.assertEqual(urlopen.call_count, 1)  # manifest only; DB cache reused by snapshot_id


    def test_stale_cloud_manifest_does_not_roll_back_newer_cached_snapshot(self):
        newer_id = "c" * 64
        newer_raw, _, newer_manifest = self._strict_market_snapshot(
            snapshot_id=newer_id,
            generated_at="2026-09-26T03:00:00+00:00",
            filename="newer.db",
        )
        _, _, older_manifest = self._strict_market_snapshot(
            snapshot_id="d" * 64,
            generated_at="2026-09-26T02:00:00+00:00",
            filename="older.db",
        )
        with tempfile.TemporaryDirectory() as cache:
            root = Path(cache)
            (root / f"{newer_id}-android-market.db").write_bytes(newer_raw)
            (root / f"{newer_id}-android-market.manifest.json").write_text(json.dumps(newer_manifest))
            with mock.patch(
                "market.urllib.request.urlopen",
                return_value=FakeResponse(
                    json.dumps(older_manifest).encode(),
                    url="https://github.com/oswade/bbdata/releases/test/manifest.json",
                ),
            ) as urlopen:
                db_path, used = market.get_market_database(cache_dir=cache)
            self.assertTrue(db_path.endswith(f"{newer_id}-android-market.db"))
            self.assertEqual(used["snapshot_id"], newer_id)
            self.assertEqual(urlopen.call_count, 1)  # stale manifest fetched; older DB not downloaded

    def test_compare_returns_top_10_sorted_and_html(self):
        with mock.patch("compare.get_market_database", return_value=(self.db, self.manifest)):
            result = compare_bill(self.bill(), top_n=10)
        self.assertTrue(result["ok"])
        self.assertEqual(len(result["top_plans"]), 10)
        costs = [p["annual_cost"] for p in result["top_plans"]]
        self.assertEqual(costs, sorted(costs))
        self.assertTrue(all(p["savings"] is not None for p in result["top_plans"]))
        self.assertIn("BillBot", result["html"])
        self.assertIn("Top 10 plans", result["html"])
        self.assertIn("climate-normal", result["html"])
        self.assertEqual(result["market"]["publisher"], "BillBot Market Updater Android / GitHub Releases")

    def test_current_plan_name_fallback_is_excluded_when_plan_id_missing(self):
        b = self.bill()
        b["retailer_name"] = "Energy 1"
        b["current_plan_name"] = "Saver 1"
        b["current_plan_id"] = ""
        with mock.patch("compare.get_market_database", return_value=(self.db, self.manifest)):
            result = compare_bill(b, top_n=10)
        self.assertTrue(all(not (p["retailer"] == "Energy 1" and p["plan_name"] == "Saver 1") for p in result["top_plans"]))
        self.assertEqual(len(result["top_plans"]), 10)

    def test_compare_includes_sense_check_and_run_id(self):
        with mock.patch("compare.get_market_database", return_value=(self.db, self.manifest)):
            result = compare_bill(self.bill(), top_n=10)
        self.assertTrue(result["run_id"])
        self.assertIn(result["sense_check"]["status"], {"PASS", "WARN", "FAIL"})
        self.assertTrue(result["sense_check"]["llm_final_review_required"])
        self.assertGreaterEqual(len(result["sense_check"]["llm_checklist"]), 4)
        self.assertEqual(result["diagnostics"]["run_id"], result["run_id"])

    def test_unreasonable_output_is_logged(self):
        from diagnostics import DiagnosticRecorder, read_log, sense_check_result
        with tempfile.TemporaryDirectory() as logdir:
            rec = DiagnosticRecorder(log_dir=logdir)
            result = {
                "bill": {"general_usage_kwh": 1, "bill_days": 30},
                "seasonality": {"adjusted_annual_usage": 10, "raw_annual_usage": 12, "seasonal_adjustment_factor": 0.2},
                "current": {"annual_comparable_cost": 20},
                "top_plans": [{"rank": 1, "plan_id": "x", "annual_cost": 5, "savings": 1}],
                "market": {"candidate_count": 1},
            }
            check = sense_check_result(result, rec)
            self.assertEqual(check["status"], "WARN")
            rows = read_log(run_id=rec.run_id, log_dir=logdir)
            self.assertTrue(rows)
            codes = {r["code"] for r in rows}
            self.assertIn("UNUSUAL_ANNUAL_USAGE", codes)
            self.assertIn("UNUSUAL_SEASONAL_FACTOR", codes)
            self.assertIn("SAVINGS_ARITHMETIC_MISMATCH", codes)

    def test_error_log_excludes_sensitive_details(self):
        from diagnostics import DiagnosticRecorder, read_log
        with tempfile.TemporaryDirectory() as logdir:
            rec = DiagnosticRecorder(log_dir=logdir)
            rec.warning("TEST", "privacy", "test warning", {
                "customer_name": "Secret Name",
                "email": "secret@example.com",
                "nmi": "123456",
                "annual_usage_kwh": 5000,
            })
            row = read_log(run_id=rec.run_id, log_dir=logdir)[0]
            self.assertNotIn("customer_name", row["details"])
            self.assertNotIn("email", row["details"])
            self.assertNotIn("nmi", row["details"])
            self.assertEqual(row["details"]["annual_usage_kwh"], 5000)

    def test_failed_comparison_writes_run_specific_error_log(self):
        from compare import compare_bill
        from diagnostics import BillBotComparisonError, read_log
        with tempfile.TemporaryDirectory() as logdir:
            bad = {"fuel_type": "ELECTRICITY", "billing_period_start": "bad", "billing_period_end": "bad"}
            with self.assertRaises(BillBotComparisonError) as ctx:
                compare_bill(bad, log_dir=logdir)
            self.assertTrue(ctx.exception.run_id)
            rows = read_log(run_id=ctx.exception.run_id, log_dir=logdir)
            self.assertTrue(any(r["level"] == "ERROR" for r in rows))
            self.assertTrue(any(r["code"] == "BILL_NORMALISATION_FAILED" for r in rows))


if __name__ == "__main__":
    unittest.main()
