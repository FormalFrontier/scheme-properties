# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
"""Data-only adapter controls on supplied records, never Lean/native execution.

The control suite uses explicitly synthetic notes in memory/temporary directories.
Add --check-committed to also require the assembled real API and notes to match.
These checks do not authenticate native execution or approve note semantics.
"""
import argparse
from collections import Counter
import copy
from html import escape
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

import generate_api as api

ROOT = Path(__file__).resolve().parent.parent
RECORDS = {}
SOURCES = api.read_sources(ROOT)
FIXTURE_NOTES = {name: "Synthetic data-test note, not release documentation." for name in api.NOTE_NAMES}


def fixture():
    return copy.deepcopy(RECORDS), dict(SOURCES)


def first(records):
    return next(row for record in records.values() for row in record["declarations"])


def render(records=None, sources=None, notes=None):
    return api.render(RECORDS if records is None else records, api.SOURCE,
                      SOURCES if sources is None else sources,
                      FIXTURE_NOTES if notes is None else notes, {"fixture": "synthetic"})


class Controls(unittest.TestCase):
    def test_actual_module_site_kind_and_client_inventory(self):
        raw, manifest = render()
        self.assertEqual(len(api.MODULES), 73)
        self.assertEqual(len(api.INPUTS), 76)
        self.assertEqual(len(api.EXPECTED), 381)
        self.assertEqual(len(FIXTURE_NOTES), 77)
        self.assertEqual(raw.count(b"\n### "), 381)
        self.assertEqual(raw.count(b"**API note (not a source docstring):**"), 77)
        self.assertEqual(Counter(r["kind"] for r in api.EXPECTED.values()),
                         {"theorem": 230, "def": 99, "instance": 42, "class": 5, "ctor": 5})
        self.assertEqual(Counter(r["display_kind"] for r in api.EXPECTED.values()),
                         api.CONTRACT["display_kinds"])
        zero = [m for m in api.MODULES if not RECORDS[m]["declarations"]]
        self.assertEqual(len(zero), 37)
        self.assertEqual(Counter(api.CONTRACT["module_scopes"][m] for m in zero),
                         {"aggregate": 1, "example": 15, "test": 21})
        metadata = json.loads(manifest)
        self.assertEqual(metadata["inputs"], metadata["analyzed_inputs"])
        self.assertNotIn("dependency_translation", metadata)
        self.assertFalse(metadata["proof_certification"])
        self.assertFalse(metadata["release_acceptance"])
        self.assertIn(b"not a raw/private declaration census", raw)

    def test_literal_headers_names_kinds_and_unique_anchors(self):
        raw, _ = render()
        headings = [line for line in raw.decode().splitlines() if line.startswith("### ")]
        self.assertEqual(set(headings), {"### `" + n + "`" for n in api.EXPECTED})
        for record in RECORDS.values():
            for row in record["declarations"]:
                self.assertIn(api.Header(row["header"]).rendered().encode(), raw)
        anchors = re.findall(rb'<a id="(api-[0-9a-f]{16})"></a>', raw)
        self.assertEqual(len(anchors), len(set(anchors)))
        self.assertEqual(len(anchors), 381)
        self.assertIn(b"noncomputable instance", raw)
        self.assertIn(b"constructor ", raw)

    def test_relative_exact_source_ranges(self):
        raw, _ = render()
        links = re.findall(r"\[Source\]\(\.\./([^#)]+)#L(\d+)-L(\d+)\)", raw.decode())
        self.assertEqual(len(links), 381)
        for path, start, end in links:
            self.assertIn(path, api.MODULE_PATHS.values())
            self.assertTrue(0 < int(start) <= int(end) <= len(SOURCES[path].splitlines()))
        self.assertNotIn(api.GITHUB_SOURCE.encode(), raw)

    def test_parser_entities_nested_names_and_malformed_markup(self):
        self.assertEqual(api.Header('<div><span>{A : Type u} [Module R A]</span> :'
                                    '<div class="decl_type">x &lt; y</div></div>').rendered(),
                         '{A : Type u} [Module R A] : x < y')
        for value in ('<script>x</script>', '<div><span></div>', '<div>unclosed',
                      '<span onclick="x">x</span>', '<div><!--x--></div>',
                      '<!DOCTYPE html>', 'outside', '<div/>tail'):
            with self.subTest(value=value), self.assertRaises(ValueError):
                api.Header(value)

    def test_module_name_kind_duplicate_missing_and_line_refusals(self):
        nonempty = next(m for m in api.MODULES if RECORDS[m]["declarations"])
        changes = [lambda r: r.pop(api.MODULES[0]),
                   lambda r: r.update(Extra=dict(name="Extra", declarations=[])),
                   lambda r: r[nonempty]["declarations"].pop(),
                   lambda r: r[nonempty]["declarations"].append(copy.deepcopy(first(r))),
                   lambda r: r[nonempty].update(name="Wrong")]
        for key, value in (("name", "Wrong"), ("kind", "axiom"), ("line", 0),
                           ("line", True), ("line", 999999), ("docLink", "wrong")):
            changes.append(lambda r, k=key, v=value: first(r)["info"].update({k: v}))
        for index, change in enumerate(changes):
            records, sources = fixture()
            change(records)
            with self.subTest(index=index), self.assertRaises(ValueError):
                render(records, sources)

    def test_signature_and_implicit_binder_loss(self):
        for needle, replacement in (("noncomputable def", "def"), (">Type</a> u", ">Type</a> v")):
            records, sources = fixture()
            row = next(r for m in records.values() for r in m["declarations"] if needle in r["header"])
            row["header"] = row["header"].replace(needle, replacement)
            with self.subTest(needle=needle), self.assertRaises(ValueError):
                render(records, sources)
        records, sources = fixture()
        row = next(r for m in records.values() for r in m["declarations"]
                   if re.search(r"\[[^\]]+\]", api.Header(r["header"]).rendered()))
        parsed = api.Header(row["header"])
        kind, name = "".join(parsed.kinds), "".join(parsed.names)
        visible = parsed.rendered()
        tail = re.sub(r"\[[^\]]+\]", "", visible[len(kind + " " + name):], count=1)
        row["header"] = ('<div><span class="decl_kind">' + escape(kind) + '</span> '
                         '<span class="decl_name">' + escape(name) + '</span><span>' +
                         escape(tail) + '</span></div>')
        with self.assertRaises(ValueError):
            render(records, sources)

    def test_docstring_bytes_presence_and_authored_note_scope(self):
        for empty in (False, True):
            records, sources = fixture()
            row = next(r for m in records.values() for r in m["declarations"]
                       if (r["info"]["name"] in api.NOTE_NAMES) == empty)
            row["info"]["doc"] += "fabricated"
            with self.subTest(empty=empty), self.assertRaises(ValueError):
                render(records, sources)
        name = next(iter(FIXTURE_NOTES))
        changes = [dict(FIXTURE_NOTES, Extra="bad"), {},
                   {k: v for k, v in FIXTURE_NOTES.items() if k != name}]
        changes += [dict(FIXTURE_NOTES, **{name: value}) for value in ("", "  ", 3, "```bad")]
        for notes in changes:
            with self.assertRaises(ValueError):
                render(notes=notes)

    def test_native_uri_exact_range_and_record_byte_refusals(self):
        records, _ = fixture()
        valid = first(records)["info"]["sourceLink"]
        base = valid.split("#")[0]
        changes = [valid.replace("github.com", "github.com.evil.invalid"),
                   valid.replace("https:", "http:"), valid.replace(api.SOURCE, "b" * 40),
                   valid.replace("/scheme-properties/", "/other/"), base, valid + "\n",
                   valid + "?query", base + "#L0-L1", base + "#L1-L999999", base + "#L01-L2"]
        for value in changes:
            records, sources = fixture()
            first(records)["info"]["sourceLink"] = value
            with self.subTest(value=value), self.assertRaises(ValueError):
                render(records, sources)
        records, sources = fixture()
        records[api.MODULES[0]]["unrendered-extra"] = "drift"
        with self.assertRaisesRegex(ValueError, "native record drift"):
            render(records, sources)

    def test_all_76_sources_configs_and_forged_manifest_refused(self):
        _, encoded = render()
        manifest = json.loads(encoded)
        api.manifest_source_binding(manifest, api.SOURCE, SOURCES)
        for path in api.INPUTS:
            altered = dict(SOURCES, **{path: SOURCES[path] + b"\n"})
            forged = copy.deepcopy(manifest)
            forged["inputs"][path] = api.digest(altered[path])
            forged["analyzed_inputs"][path] = api.digest(altered[path])
            with self.subTest(path=path), self.assertRaisesRegex(ValueError, "drift"):
                api.manifest_source_binding(forged, api.SOURCE, altered)
            with self.subTest(render_path=path), self.assertRaisesRegex(ValueError, "drift"):
                render(sources=altered)
            absent = dict(SOURCES)
            absent.pop(path)
            with self.subTest(missing=path), self.assertRaises(ValueError):
                render(sources=absent)
        for key in api.provenance():
            changed = dict(manifest, **{key: None})
            with self.subTest(key=key), self.assertRaises(ValueError):
                api.manifest_source_binding(changed, api.SOURCE, SOURCES)
        for value in (True, 2, "1"):
            with self.assertRaises(ValueError):
                api.manifest_source_binding(dict(manifest, format=value), api.SOURCE, SOURCES)
        for value in ("main", "a" * 40, api.SOURCE.upper()):
            with self.assertRaises(ValueError):
                api.render(RECORDS, value, SOURCES, FIXTURE_NOTES, {})

    def test_source_only_parentless_git_drift_and_hidden_module(self):
        with tempfile.TemporaryDirectory(prefix="scheme-api-controls-") as temporary:
            root, native = Path(temporary) / "candidate", Path(temporary) / "native"
            native.mkdir()
            for module, record in RECORDS.items():
                (native / ("declaration-data-" + module + ".bmp")).write_text(json.dumps(record))
            paths = list(api.INPUTS) + ["scripts/" + p for p in
                     ("generate_api.py", "test_generate_api.py", "api_contract.json")]
            for path in paths:
                target = root / path
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / path, target)
            (root / "scripts/api_notes.json").write_text(json.dumps(FIXTURE_NOTES))
            files = ("generate_api.py", "test_generate_api.py", "api_contract.json", "api_notes.json")
            hashes = {"scripts/" + p: api.digest((root / "scripts" / p).read_bytes()) for p in files}
            raw, manifest = api.render(RECORDS, api.SOURCE, SOURCES, FIXTURE_NOTES, hashes)
            (root / "docs").mkdir()
            (root / "docs/API.md").write_bytes(raw)
            (root / "docs/api-manifest.json").write_bytes(manifest)
            argv = [sys.executable, "-B"] + ["-O"] * sys.flags.optimize + [
                "scripts/generate_api.py", "--native-data", str(native),
                "--source-revision", api.SOURCE, "--check"]
            def run(ok, expected):
                result = subprocess.run(argv, cwd=root, capture_output=True)
                self.assertEqual(result.returncode == 0, ok, result.stderr.decode())
                self.assertIn(expected, (result.stdout + result.stderr).decode())
            def drifts():
                for path in api.INPUTS:
                    old = (root / path).read_bytes()
                    try:
                        (root / path).write_bytes(old + b"\n")
                        run(False, "drift")
                    finally:
                        (root / path).write_bytes(old)
            run(True, "committed-source-hashes")
            drifts()
            extra = root / "Hidden.lean"
            extra.write_text("module\n")
            run(False, "shipped Lean module inventory differs")
            extra.unlink()
            (root / ".git").write_text("invalid worktree marker\n")
            run(False, "refusing fallback")
            (root / ".git").unlink()
            subprocess.run(["git", "init", "-q", str(root)], check=True, capture_output=True)
            subprocess.run(["git", "-C", str(root), "add", "."], check=True, capture_output=True)
            subprocess.run(["git", "-C", str(root), "-c", "user.name=Fixture", "-c",
                            "user.email=fixture@example.invalid", "commit", "-qm",
                            "Synthetic independent-root fixture"], check=True, capture_output=True)
            self.assertEqual(subprocess.check_output(["git", "-C", str(root), "rev-list", "--count", "HEAD"]).strip(), b"1")
            run(True, "committed-source-hashes")
            drifts()
            tree = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD^{tree}"]).decode().strip()
            with self.assertRaisesRegex(ValueError, "not a commit"):
                api.git_source_available(root, tree)
            subprocess.run(["git", "-C", str(root), "fetch", "--quiet", "--no-tags", "--depth=1",
                            str(ROOT), api.SOURCE], check=True, capture_output=True)
            run(True, "git-object")
            drifts()
            for path in ("scripts/api_notes.json", "scripts/test_generate_api.py", "docs/API.md"):
                old = (root / path).read_bytes()
                (root / path).write_bytes(old + b"\n")
                run(False, "generated file differs")
                (root / path).write_bytes(old)
            old = (root / "scripts/api_contract.json").read_bytes()
            (root / "scripts/api_contract.json").write_bytes(old + b"\n")
            run(False, "contract drift")
            (root / "scripts/api_contract.json").write_bytes(old)
            (native / "declaration-data-Extra.bmp").write_text("{}")
            run(False, "native module file inventory differs")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native-data", type=Path, required=True)
    parser.add_argument("--check-committed", action="store_true")
    args = parser.parse_args()
    RECORDS.update(api.load_records(args.native_data))
    if args.check_committed:
        subprocess.run([sys.executable, "-B"] + ["-O"] * sys.flags.optimize + [
            str(ROOT / "scripts/generate_api.py"), "--native-data", str(args.native_data),
            "--source-revision", api.SOURCE, "--check"], check=True)
    unittest.main(argv=[sys.argv[0]], verbosity=2)
