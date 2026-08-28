#!/usr/bin/env python3
"""Forged-record fixtures for scripts/validate_comparator_result.py (CX-052).

The publish job's validator is the write boundary: whatever it accepts becomes a
dated verifier claim in comparator/comparator-status.json and on the blueprint's
comparator page. A validator is only as good as the forgeries it rejects, so
each fixture here is a result record that a weaker check would wave through, and
each test names the field family it must be caught by.

Running these in the trusted `build` job, in seconds, is the point: the
rejection behaviour of the gate that decides what gets published is itself
checked before anything expensive runs.

The fixtures are self-contained: the stub config and the stub certified sources
are written into a temporary directory by `setUpClass`, and the digests baked
into the JSON fixtures are the digests of exactly those bytes. Nothing here
reads the live comparator configuration -- the live coupling is enforced on
every CI run, by the workflow, against the real checkout.

Run: python3 scripts/tests/test_validate_comparator_result.py
"""

import hashlib
import io
import json
import os
import shutil
import sys
import tempfile
import unittest
from contextlib import redirect_stdout

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(REPO, "scripts"))

import validate_comparator_result as validator  # noqa: E402

# The exact bytes the fixture digests were computed from.
STUB_CONFIG = json.dumps(
    {
        "challenge_module": "Challenge",
        "solution_module": "Solution",
        "theorem_names": ["Mathoverflow1973.stub_theorem"],
        "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "enable_nanoda": True,
    },
    indent=2,
) + "\n"
STUB_CHALLENGE = "-- comparator fixture: challenge stub\n"
STUB_SOLUTION = "-- comparator fixture: solution stub\n"

# Trusted inputs the publish job would pass; they match result-valid.json.
TRUSTED = [
    "--repository", "eric-vergo/HopfProblem",
    "--run-id", "99999999999",
    "--commit", "1111111111111111111111111111111111111111",
    "--toolchain", "leanprover/lean4:v4.33.0",
    "--tool-ref", "v4.33.0",
    "--tool-sha", "3927ad383f208ae977c340a91c48ac9b497d2097",
    "--tool-toolchain", "leanprover/lean4:v4.33.0",
    "--landrun-ref", "811cfff51ceaf3d9843708aa6d22e9b84ccac8b4",
    "--nanoda-ref", "05055695879dfebb6628a67da88ceca6cd6b0421",
    "--nanoda-repository", "https://github.com/ammkrn/nanoda_lib",
    "--af-unix-guard", "active",
    "--config-path", "comparator/config.json",
    "--probe-config", "comparator/config-probe.json",
    "--selftest-tier", "pre-run-trusted",
    "--probe-tier", "defense-in-depth",
    "--now", "2026-08-27T12:35:00Z",
    "--max-age-seconds", "43200",
]


class ValidatorFixtures(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.mkdtemp(prefix="comparator-validator-")
        cls.config = os.path.join(cls.tmp, "config.json")
        cls.challenge = os.path.join(cls.tmp, "Challenge.lean")
        cls.solution = os.path.join(cls.tmp, "Solution.lean")
        for path, text in (
            (cls.config, STUB_CONFIG),
            (cls.challenge, STUB_CHALLENGE),
            (cls.solution, STUB_SOLUTION),
        ):
            with open(path, "w", encoding="utf-8") as handle:
                handle.write(text)

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def run_validator(self, fixture, extra=()):
        argv = [
            "--result", os.path.join(HERE, fixture),
            "--config-file", self.config,
            "--hash-file", "comparator_config=" + self.config,
            "--hash-file", "challenge_lean=" + self.challenge,
            "--hash-file", "solution_lean=" + self.solution,
        ] + TRUSTED + list(extra)
        buffer = io.StringIO()
        with redirect_stdout(buffer):
            status = validator.main(argv)
        return status, buffer.getvalue()

    def assertRejected(self, fixture, *fields, **kwargs):
        extra = kwargs.pop("extra", ())
        status, output = self.run_validator(fixture, extra)
        self.assertEqual(status, 1, "{} was accepted:\n{}".format(fixture, output))
        for field in fields:
            self.assertIn(field, output, "{} did not report {}:\n{}".format(fixture, field, output))

    # --- the fixture digests must describe the stub bytes -------------------
    def test_fixture_digests_describe_the_stub_sources(self):
        with open(os.path.join(HERE, "result-valid.json"), encoding="utf-8") as handle:
            record = json.load(handle)
        for key, path in (
            ("comparator_config", self.config),
            ("challenge_lean", self.challenge),
            ("solution_lean", self.solution),
        ):
            with open(path, "rb") as source:
                digest = hashlib.sha256(source.read()).hexdigest()
            self.assertEqual(record["inputs_sha256_after"][key], digest, key)

    # --- the honest record --------------------------------------------------
    def test_valid_record_is_accepted(self):
        status, output = self.run_validator("result-valid.json")
        self.assertEqual(status, 0, output)
        self.assertIn("accepted", output)

    # --- CX-052's "less conspicuous" forgery --------------------------------
    def test_forged_provenance_is_rejected(self):
        # Verdict, commit, config, modules, theorem names, permitted axioms and
        # the whole post-run source manifest are correct here. Only the
        # provenance is invented -- which is exactly what the status refresh
        # would have republished as verifier evidence.
        self.assertRejected(
            "result-forged-provenance.json",
            "repository",
            "run_id",
            "tool_ref",
            "tool_sha",
            "tool_toolchain",
            "landrun_ref",
            "nanoda_ref",
            "af_unix_guard",
            "sandbox_selftest.tier",
            "sandbox_selftest.exit_code",
            "sandbox_write_probe.config",
        )

    # --- integrity across the verification gap ------------------------------
    def test_forged_hashes_are_rejected(self):
        self.assertRejected(
            "result-forged-hashes.json",
            "inputs_sha256.challenge_lean",
            "inputs_sha256_after.solution_lean",
        )

    # --- record shape -------------------------------------------------------
    def test_forged_key_set_is_rejected(self):
        self.assertRejected(
            "result-forged-keys.json",
            "unexpected key 'note'",
            "missing key 'nanoda_ref'",
            "missing key 'nanoda'",
            "unexpected key 'extra_binary'",
            "missing key 'sentinel_observed'",
        )

    # --- containment evidence -----------------------------------------------
    def test_forged_probe_evidence_is_rejected(self):
        self.assertRejected(
            "result-forged-probe.json",
            "af_unix_guard",
            "sandbox_selftest.denied",
            "sandbox_selftest.exit_code",
            "sandbox_selftest.sentinel_observed",
            "sandbox_selftest.targets",
            "sandbox_write_probe.denied",
            "sandbox_write_probe.exit_code",
            "sandbox_write_probe.tier",
        )

    # --- run window ---------------------------------------------------------
    def test_forged_run_window_is_rejected(self):
        self.assertRejected(
            "result-forged-window.json",
            "started_at",
            "finished_at",
        )

    def test_unparsable_timestamp_is_rejected(self):
        record_path = os.path.join(self.tmp, "result-bad-timestamp.json")
        with open(os.path.join(HERE, "result-valid.json"), encoding="utf-8") as handle:
            record = json.load(handle)
        record["finished_at"] = "yesterday"
        with open(record_path, "w", encoding="utf-8") as handle:
            json.dump(record, handle)
        argv = [
            "--result", record_path,
            "--config-file", self.config,
            "--hash-file", "comparator_config=" + self.config,
            "--hash-file", "challenge_lean=" + self.challenge,
            "--hash-file", "solution_lean=" + self.solution,
        ] + TRUSTED
        buffer = io.StringIO()
        with redirect_stdout(buffer):
            status = validator.main(argv)
        self.assertEqual(status, 1, buffer.getvalue())
        self.assertIn("finished_at", buffer.getvalue())

    # --- checker identity (CX-064) ------------------------------------------
    def test_forged_kernel_identity_is_rejected(self):
        # Well-formed in every syntactic sense -- a 40-hex revision, a 64-hex
        # digest, the right label -- and about a different program from the one
        # this workflow pinned and hashed. Well-formedness is what a forger has
        # for free; agreement with the job's own constants is not.
        self.assertRejected(
            "result-forged-identity.json",
            "kernel_identities[0].repository",
            "kernel_identities[0].source_commit",
            "kernel_identities[0].executable_sha256",
        )

    def test_kernel_identity_must_match_the_hash_manifest(self):
        # The identity and the input-hash manifest are two encodings of "which
        # nanoda binary ran". A record whose identity digest is not the digest
        # the same run's manifest recorded describes two programs.
        record_path = os.path.join(self.tmp, "result-identity-drift.json")
        with open(os.path.join(HERE, "result-valid.json"), encoding="utf-8") as handle:
            record = json.load(handle)
        record["kernel_identities"][0]["executable_sha256"] = "e" * 64
        with open(record_path, "w", encoding="utf-8") as handle:
            json.dump(record, handle)
        argv = [
            "--result", record_path,
            "--config-file", self.config,
            "--hash-file", "comparator_config=" + self.config,
            "--hash-file", "challenge_lean=" + self.challenge,
            "--hash-file", "solution_lean=" + self.solution,
        ] + TRUSTED
        buffer = io.StringIO()
        with redirect_stdout(buffer):
            status = validator.main(argv)
        output = buffer.getvalue()
        self.assertEqual(status, 1, output)
        self.assertIn("kernel_identities[0].executable_sha256", output)

    # --- the claim fields come from the config, not from the record ---------
    def test_claim_fields_must_match_the_checked_out_config(self):
        config_path = os.path.join(self.tmp, "other-config.json")
        with open(config_path, "w", encoding="utf-8") as handle:
            json.dump(
                {
                    "challenge_module": "Challenge",
                    "solution_module": "Solution",
                    "theorem_names": ["Mathoverflow1973.something_else"],
                    "permitted_axioms": ["propext"],
                    "enable_nanoda": False,
                },
                handle,
            )
        argv = [
            "--result", os.path.join(HERE, "result-valid.json"),
            "--config-file", config_path,
            "--hash-file", "comparator_config=" + self.config,
            "--hash-file", "challenge_lean=" + self.challenge,
            "--hash-file", "solution_lean=" + self.solution,
        ] + TRUSTED
        buffer = io.StringIO()
        with redirect_stdout(buffer):
            status = validator.main(argv)
        output = buffer.getvalue()
        self.assertEqual(status, 1, output)
        for field in ("theorem_names", "permitted_axioms", "nanoda_replay"):
            self.assertIn(field, output)

    # --- a missing --hash-file must not be a silent pass --------------------
    def test_missing_certified_source_hash_is_rejected(self):
        argv = [
            "--result", os.path.join(HERE, "result-valid.json"),
            "--config-file", self.config,
            "--hash-file", "comparator_config=" + self.config,
        ] + TRUSTED
        buffer = io.StringIO()
        with redirect_stdout(buffer):
            status = validator.main(argv)
        output = buffer.getvalue()
        self.assertEqual(status, 1, output)
        self.assertIn("challenge_lean", output)
        self.assertIn("solution_lean", output)


if __name__ == "__main__":
    unittest.main(verbosity=2)
