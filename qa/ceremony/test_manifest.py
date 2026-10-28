#!/usr/bin/env python3
"""Offline setup-description and canonicalization regressions."""

import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import manifest


HERE = Path(__file__).parent
FIXTURES = HERE / "fixtures"


class ManifestTests(unittest.TestCase):
    def fixture(self, profile="standard"):
        return manifest.load(FIXTURES / f"{profile}.manifest")

    def test_fixture_canonical_bytes_and_digests(self):
        for profile in ("standard", "aggregator"):
            with self.subTest(profile=profile):
                encoded = manifest.canonical_bytes(self.fixture(profile))
                self.assertEqual(encoded, (FIXTURES / f"{profile}.manifest").read_bytes())
                self.assertEqual(hashlib.sha256(encoded).hexdigest(),
                                 (FIXTURES / f"{profile}.manifest.sha256").read_text().strip())
                self.assertEqual(manifest.continuation_profile(self.fixture(profile)), profile)

    def test_object_order_is_canonical_but_array_order_is_preserved(self):
        original = self.fixture()
        reversed_keys = dict(reversed(list(original.items())))
        self.assertEqual(manifest.canonical_bytes(original), manifest.canonical_bytes(reversed_keys))
        reordered = copy.deepcopy(original)
        reordered["setup"]["application_steps"].reverse()
        self.assertNotEqual(manifest.canonical_bytes(original), manifest.canonical_bytes(reordered))

    def test_setup_choices_change_the_manifest_digest(self):
        original = self.fixture("aggregator")
        encoded = manifest.canonical_bytes(original)
        variants = []
        for path, value in [
            (("setup", "native_registry"), ["fixture:native1", "fixture:native0"]),
            (("setup", "ranks_and_capacities"), {"rank": 14}),
            (("artifacts", "public_parameters", "sha256"), "01" * 32),
            (("setup", "verified_setups"), [{"profile": "standard", "manifest_sha256": "02" * 32,
                                            "record_sha256": "03" * 32}]),
        ]:
            changed = copy.deepcopy(original)
            parent = changed
            for key in path[:-1]:
                parent = parent[key]
            parent[path[-1]] = value
            variants.append(changed)
        for variant in variants:
            self.assertNotEqual(hashlib.sha256(encoded).digest(),
                                hashlib.sha256(manifest.canonical_bytes(variant)).digest())

    def test_required_setup_fields_cannot_be_omitted(self):
        for path in [
            ("setup", "profile"), ("setup", "native_registry"),
            ("setup", "nested_registry"), ("setup", "ranks_and_capacities"),
            ("setup", "transcript_rules_and_dst"), ("setup", "verified_setups"),
            ("artifacts", "public_parameters", "sha256"),
        ]:
            with self.subTest(path=path):
                value = self.fixture()
                parent = value
                for key in path[:-1]:
                    parent = parent[key]
                del parent[path[-1]]
                with self.assertRaises(ValueError):
                    manifest.canonical_bytes(value)

    def test_profile_and_label_mismatches_are_rejected(self):
        for profile in ("standard", "aggregator"):
            value = self.fixture(profile)
            value["beacon"]["native_registry_label"] = "wrong label"
            with self.assertRaisesRegex(ValueError, "does not match profile"):
                manifest.canonical_bytes(value)
        value = self.fixture()
        value["setup"]["profile"]["name"] = "unknown"
        with self.assertRaisesRegex(ValueError, "unsupported QA profile"):
            manifest.canonical_bytes(value)

    def test_bad_digests_and_dependencies_are_rejected(self):
        value = self.fixture()
        value["artifacts"]["source"]["sha256"] = "short"
        with self.assertRaisesRegex(ValueError, "SHA-256"):
            manifest.canonical_bytes(value)
        value = self.fixture("aggregator")
        value["setup"]["verified_setups"] = [{"profile": "standard", "manifest_sha256": "02" * 32}]
        with self.assertRaisesRegex(ValueError, "record_sha256"):
            manifest.canonical_bytes(value)
        value = self.fixture("aggregator")
        value["setup"]["verified_setups"] = [{"profile": "standard", "manifest_sha256": "short"}]
        with self.assertRaisesRegex(ValueError, "SHA-256"):
            manifest.canonical_bytes(value)

    def test_unresolved_placeholders_are_rejected(self):
        value = self.fixture()
        value["setup"]["configuration"] = {"network": "<choose a network>"}
        with self.assertRaisesRegex(ValueError, "placeholder"):
            manifest.canonical_bytes(value)

    def test_nonobject_records_are_rejected(self):
        with self.assertRaisesRegex(ValueError, "object"):
            manifest.continuation_profile([])

    def test_legacy_record_can_be_inspected_but_not_prepared_as_new(self):
        value = self.fixture()
        del value["setup"]["profile"]
        del value["setup"]["verified_setups"]
        self.assertEqual(manifest.continuation_profile(value), "standard")
        with self.assertRaisesRegex(ValueError, "setup.profile"):
            manifest.canonical_bytes(value)

    def test_invalid_json_has_no_partial_output(self):
        for text in ['{"format":1,"format":2}', '{"value":1.5}', '{"value":NaN}']:
            with self.subTest(text=text), tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "bad.json"
                path.write_text(text)
                result = subprocess.run([sys.executable, str(HERE / "manifest.py"), str(path)],
                                        capture_output=True, text=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")


if __name__ == "__main__":
    unittest.main()
