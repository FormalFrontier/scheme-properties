#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
"""Fixed Scheme Markdown adapter for authenticated native doc-gen4 records.

This is not a Lean parser, native-provenance attestation or proof checker.
It performs no Lean/cache/native generation. See docs/README.md.
"""
import argparse
from collections import Counter
import hashlib
from html.parser import HTMLParser
import json
import os
from pathlib import Path
import re
import subprocess

SOURCE = "a05b182aa17ea7cd1a591ec7b60aa7d6f2b6704c"
TOOL = "97d4ecdfc8e09e7f511724c25e303d448de6a3db"
CONTRACT_SHA256 = "e4d42fa592de1e49161a2c410935944ec6e1564ed9af9cdadc7389be742b4e2b"
HERE = Path(__file__).resolve().parent
GITHUB_SOURCE = "https://github.com/FormalFrontier/scheme-properties/blob/"


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def canonical_hash(value):
    # Match the retained intake's JSON normalization, including its separators.
    return digest(json.dumps(value, sort_keys=True).encode())


def load_contract(path):
    raw = path.read_bytes()
    require(digest(raw) == CONTRACT_SHA256, "fixed documentation contract drift")
    contract = json.loads(raw)
    require(contract["source"] == SOURCE and contract["docgen"] == TOOL,
            "contract source/tool differs")
    return contract


CONTRACT = load_contract(HERE / "api_contract.json")
MODULE_PATHS = CONTRACT["module_paths"]
MODULES = tuple(MODULE_PATHS)
INPUTS = CONTRACT["inputs"]
EXPECTED = CONTRACT["sites"]
NATIVE_RECORDS = CONTRACT["native_records"]
NOTE_NAMES = set(CONTRACT["missing_docstrings"])


def source_binding(sources):
    require(set(sources) == set(INPUTS), "source/pin inventory differs")
    require({p: digest(raw) for p, raw in sources.items()} == INPUTS,
            "source/pin drift from fixed native inputs")


def read_sources(root):
    # The source-only mode must not silently ignore an extra shipped Lean module.
    found = set()
    for directory, dirs, files in os.walk(root, followlinks=False):
        dirs[:] = [d for d in dirs if d not in {".git", ".lake"}]
        require(not any((Path(directory) / d).is_symlink() for d in dirs),
                "symlink directory in source tree")
        for filename in files:
            if filename.endswith(".lean"):
                path = Path(directory) / filename
                require(not path.is_symlink(), "symlink Lean source")
                found.add(path.relative_to(root).as_posix())
    require(found == set(MODULE_PATHS.values()), "shipped Lean module inventory differs")
    require(all(not (root / p).is_symlink() for p in INPUTS), "symlink checking input")
    sources = {p: (root / p).read_bytes() for p in INPUTS}
    source_binding(sources)
    return sources


def git_source_available(root, revision):
    marker = root / ".git"
    if not marker.exists() and not marker.is_symlink():
        return False
    result = subprocess.run(["git", "--no-replace-objects", "cat-file", "--batch-check"],
                            input=(revision + "\n").encode(), cwd=root,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    require(result.returncode == 0, "cannot inspect Git object; refusing fallback")
    line = result.stdout.decode().strip()
    if line == revision + " missing":
        return False
    require(re.fullmatch(re.escape(revision) + r" commit [0-9]+", line) is not None,
            "selected Git object is not a commit")
    return True


def git_source_binding(root, revision, sources):
    require(revision == SOURCE, "wrong frozen analyzed source revision")
    source_binding(sources)
    for path in INPUTS:
        old = subprocess.check_output(["git", "--no-replace-objects", "show",
                                       revision + ":" + path], cwd=root)
        require(old == sources[path], "Git source/pin drift: " + path)


def manifest_source_binding(manifest, revision, sources):
    source_binding(sources)
    require(revision == SOURCE and type(manifest.get("format")) is int
            and manifest["format"] == 1, "manifest format or revision differs")
    for key, expected in provenance().items():
        require(manifest.get(key) == expected, "manifest provenance differs: " + key)


def provenance():
    return dict(docgen_revision=TOOL, analyzed_source_revision=SOURCE,
                analyzed_source_tree=CONTRACT["source_tree"],
                contract_sha256=CONTRACT_SHA256, modules=list(MODULES),
                module_paths=MODULE_PATHS, module_scopes=CONTRACT["module_scopes"],
                inputs=INPUTS, analyzed_inputs=INPUTS,
                native_record_sha256=NATIVE_RECORDS)


class Header(HTMLParser):
    """Preserve visible native tokens/implicit binders; discard display markup."""

    def __init__(self, value):
        super().__init__(convert_charrefs=True)
        self.stack, self.text, self.kinds, self.names = [], [], [], []
        self.feed(value)
        self.close()
        require(not self.stack, "unclosed native header")

    def handle_starttag(self, tag, attrs):
        require(tag in {"div", "span", "a"}, "unexpected native header tag")
        attrs = dict(attrs)
        require(not any(a.startswith("on") for a in attrs), "active header attribute")
        if tag == "div" and "decl_type" in attrs.get("class", "").split():
            self.text.append(" ")
        self.stack.append((tag, set(attrs.get("class", "").split())))

    def handle_endtag(self, tag):
        require(bool(self.stack) and self.stack[-1][0] == tag, "unbalanced native header")
        self.stack.pop()

    def handle_data(self, value):
        require(bool(self.stack) or not value.strip(), "text outside native header")
        self.text.append(value)
        if any("decl_kind" in classes for _, classes in self.stack):
            self.kinds.append(value)
        if any("decl_name" in classes for _, classes in self.stack):
            self.names.append(value)

    def handle_comment(self, _):
        raise ValueError("unexpected header comment")

    def handle_decl(self, _):
        raise ValueError("unexpected header declaration")

    def rendered(self):
        return " ".join("".join(self.text).split())


def source_range(info, path, sources):
    require(type(info["line"]) is int, "invalid native source line")
    url = GITHUB_SOURCE + SOURCE + "/" + path
    match = re.fullmatch(re.escape(url) + r"#L([1-9][0-9]*)-L([1-9][0-9]*)",
                         info["sourceLink"])
    require(match is not None, "native source URI/range differs")
    start, end = map(int, match.groups())
    require(start == info["line"] and 0 < start <= end <= len(sources[path].splitlines()),
            "native source line/range out of bounds")
    return start, end


def validate_notes(notes):
    require(type(notes) is dict and set(notes) == NOTE_NAMES and len(notes) == 77,
            "authored API note inventory differs")
    require(all(type(v) is str and bool(v.strip()) and "```" not in v for v in notes.values()),
            "invalid authored API note")


def render(records, revision, sources, notes, documentation_inputs):
    require(revision == SOURCE, "wrong frozen analyzed source revision")
    source_binding(sources)
    validate_notes(notes)
    require(set(records) == set(MODULES) and len(MODULES) == 73, "native module inventory differs")
    require(len(EXPECTED) == 381, "bounded display inventory differs")
    rows, found = [], set()
    for module in MODULES:
        record = records[module]
        require(record["name"] == module, "native module name differs")
        for row in record["declarations"]:
            info = row["info"]
            name, kind = info["name"], info["kind"]
            require(name in EXPECTED and EXPECTED[name]["kind"] == kind
                    and EXPECTED[name]["module"] == module, "unexpected name/kind/module")
            require(name not in found, "duplicate display name")
            path = MODULE_PATHS[module]
            start, end = source_range(info, path, sources)
            expected = EXPECTED[name]
            require((start, end) == (expected["start"], expected["end"]), "native source span differs")
            require(info["docLink"] == "./" + module.replace(".", "/") + ".html#" + name,
                    "native self link differs")
            header = Header(row["header"])
            require("".join(header.names) == name and "".join(header.kinds) == expected["display_kind"],
                    "native header identity differs")
            text = header.rendered()
            require(digest(text.encode()) == expected["header_sha256"], "native signature token drift")
            require(digest(info["doc"].encode()) == expected["doc_sha256"], "native source docstring drift")
            require(bool(info["doc"].strip()) == (name not in NOTE_NAMES), "docstring presence differs")
            require("```" not in text and "```" not in info["doc"], "unsupported Markdown fence")
            found.add(name)
            rows.append(dict(name=name, kind=kind, module=module, path=path,
                             start=start, end=end, header=text, doc=info["doc"].strip()))
    require(found == set(EXPECTED), "missing display name")
    require({m: canonical_hash(records[m]) for m in MODULES} == NATIVE_RECORDS, "native record drift")
    require(dict(Counter(row["kind"] for row in rows)) == CONTRACT["kinds"], "kind census differs")
    rows.sort(key=lambda r: (r["module"], r["start"], r["name"]))
    lines = ["# Generated API reference", "",
        "This reference contains 381 native display sites in 36 library modules:",
        "230 theorems, 99 definitions, 42 instances, five classes and five constructors.",
        "The aggregate, 15 example modules and 21 test modules have zero display sites;",
        "that does not mean they contain no mathematical bodies or generated declarations.",
        "Import `SchemeProperties` for the library; examples and tests are separate targets.", "",
        "These are native doc-gen4 display signatures, not complete declarations with proof bodies.",
        "All visible tokens, including implicit binders and noncomputable modifiers, are preserved;",
        "only whitespace is normalized. Pretty-printing uses source namespaces, notation and",
        "inference; consult the source for suppressed inferred types and universe conventions.",
        "Displayed fragments need not elaborate alone in a fresh namespace.", "",
        "Display counts are not a raw/private declaration census or proof certification.",
        "This documentation generator does not determine release or source-coverage acceptance.",
        "Source links refer to this same checkout; no development history is needed to follow them.",
        "See [generation instructions](README.md), the [mathematical guide](Guide.md) and",
        "[exact input manifest](api-manifest.json). Authored notes are labeled separately from source docstrings.", "",
        "## Complete module inventory", "", "| Module | Scope | Display sites |",
        "| --- | --- | --- |"]
    lines += ["| `" + m + "` | " + CONTRACT["module_scopes"][m] + " | " +
              str(len(records[m]["declarations"])) + " |" for m in MODULES]
    previous = None
    for row in rows:
        if row["module"] != previous:
            previous = row["module"]
            lines += ["", "## " + previous, ""]
        anchor = "api-" + digest(row["name"].encode())[:16]
        lines += ['<a id="' + anchor + '"></a>', "", "### `" + row["name"] + "`", "",
                  "```lean", row["header"], "```", ""]
        lines += [row["doc"] if row["doc"] else
                  "**API note (not a source docstring):** " + notes[row["name"]], ""]
        lines += [f"[Source](../{row['path']}#L{row['start']}-L{row['end']}) (native source range).", ""]
    markdown = "\n".join(lines).encode()
    manifest = dict(format=1, generator="scripts/generate_api.py", **provenance(),
                    library_display_sites=381, boundary_client_display_sites=0,
                    documentation_inputs=documentation_inputs,
                    native_display_declarations=[r["name"] for r in rows],
                    notes_sha256=canonical_hash(notes), api_sha256=digest(markdown),
                    proof_certification=False, release_acceptance=False)
    return markdown, (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode()


def load_records(directory):
    require({p.name for p in directory.glob("declaration-data-*.bmp")} ==
            {"declaration-data-" + m + ".bmp" for m in MODULES}, "native module file inventory differs")
    return {m: json.loads((directory / ("declaration-data-" + m + ".bmp")).read_bytes()) for m in MODULES}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native-data", type=Path, required=True)
    parser.add_argument("--source-revision", required=True)
    parser.add_argument("--check", action="store_true", help="compare, never write")
    args = parser.parse_args()
    require(args.source_revision == SOURCE, "wrong frozen analyzed source revision")
    root = HERE.parent
    sources = read_sources(root)
    if git_source_available(root, args.source_revision):
        git_source_binding(root, args.source_revision, sources)
        binding = "git-object"
    else:
        manifest_source_binding(json.loads((root / "docs/api-manifest.json").read_bytes()),
                                args.source_revision, sources)
        binding = "committed-source-hashes"
    paths = ("generate_api.py", "test_generate_api.py", "api_contract.json", "api_notes.json")
    documentation_inputs = {"scripts/" + p: digest((HERE / p).read_bytes()) for p in paths}
    notes = json.loads((HERE / "api_notes.json").read_bytes())
    api, manifest = render(load_records(args.native_data), args.source_revision, sources,
                           notes, documentation_inputs)
    if not args.check:
        (root / "docs").mkdir(exist_ok=True)
    for name, raw in (("API.md", api), ("api-manifest.json", manifest)):
        target = root / "docs" / name
        if args.check:
            require(target.read_bytes() == raw, "generated file differs: " + name)
        else:
            target.write_bytes(raw)
    print(json.dumps(dict(status="matched" if args.check else "generated", declarations=381,
                          api_sha256=digest(api), source_binding=binding, release_acceptance=False)))


if __name__ == "__main__":
    main()
