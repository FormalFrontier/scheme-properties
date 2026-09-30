# API documentation and reproduction

[API.md](API.md) is a **fixed historical** Markdown rendering of native doc-gen4
records from the 73-module snapshot `a05b182aa17ea7cd1a591ec7b60aa7d6f2b6704c`,
not a current complete library census or a source-text declaration scanner.
[Guide.md](Guide.md) explains the mathematics; [FinitePresentations.md](FinitePresentations.md)
and the new Lean source describe the native finite-presentation additions, which
are absent from this generated reference. [api-manifest.json](api-manifest.json)
binds only the unchanged historical page and inputs; reproduce its contract
against the exact frozen snapshot, not the present checkout.
The [dense-open rational category guide](DenseOpenRationalCategory.md)
documents a later separate category and is explicitly **outside** that unchanged
historical 73-module API snapshot and its generated manifest.
The [relative dense-open rational category guide](DenseOpenRationalCategoryOver.md)
documents the later arbitrary-base relative category and its private client,
also **outside** that fixed historical snapshot and manifest.
The [integral dominant rational category guide](IntegralDominantRationalCategory.md)
documents the later integral-object full-subcategory equivalence with native
dominant rational-map arrows, also **outside** that unchanged snapshot and
manifest.

## What the reference contains

The historical native input covered all 73 then-shipped Lean modules: 36 focused library modules,
the aggregate, 15 examples and 21 tests. There are 381 native display sites in
the focused library modules: 230 theorems, 99 definitions, 42 instances, five
classes and five constructors. The other modules have no display sites, which
does not mean they have no mathematical bodies or generated declarations.
That snapshot's complete module inventory is included in the API reference;
this statement does not inventory the current checkout.

All visible native signature tokens are retained, including implicit binders,
class/constructor distinctions and literal noncomputable modifiers. Only
whitespace is normalized. Native pretty-printing depends on each source's
namespaces, notation, universes and inferred types; fragments are not promised
to elaborate by themselves. Source-docstring text is preserved. The 77 sites
without one have separately authored, explicitly labeled API notes; constructor,
field and reassociated-lemma notes do not pretend to be source docstrings.
Source ranges come from native records; a generated reassociation lemma may
point to its parent's attribute line, and a field may point to only its starting
line. Consult the surrounding source for the complete definition.

Display sites are not a complete raw/private declaration or stored-value census.
Neither the generator nor its manifest certifies proofs, source coverage or
release acceptance. At this documentation preparation on September 26, 2026,
the native source/client build was complete; the separate complete proof intake
and fresh exact-candidate release review were not yet recorded.

## Fixed input contract

Native analysis used source `a05b182aa17ea7cd1a591ec7b60aa7d6f2b6704c`, tree
`5a8afee42778b0666e8ecf47ddcc079b1d14ad60`, and doc-gen4
`97d4ecdfc8e09e7f511724c25e303d448de6a3db`. It used the exact current official
GitHub dependency configurations: there is no historical-config translation
or allowed pin drift in this adapter.

The immutable checksum in [generate_api.py](../scripts/generate_api.py) binds
[api_contract.json](../scripts/api_contract.json): all 73 module paths, 76
source/configuration hashes, 73 normalized native records, 381 names/kinds,
header/docstring hashes and source ranges. Updating this contract requires
new native evidence and review, not learning hashes from a modified checkout.
The manifest additionally hashes the adapter, tests, contract and authored notes.

When the analyzed Git object is present, every source/configuration byte is
compared with it. An independent public-history checkout or source archive can
instead use the committed manifest and the same fixed hashes. Only an explicit
missing Git object or a source tree without Git permits that fallback; a broken
Git repository is refused. Relative source links work in either history.
The original native GitHub linker is validated as provenance, not claimed to be
a publicly fetchable development commit or emitted as the reader's source link.

## Data-only reproduction from native records

Obtain the native `doc-data` records from a matching authenticated generation
or reproduce them as below. They are inputs to the adapter, not bundled raw
execution transcripts. Python 3's standard library suffices for this step:

```sh
python -B scripts/generate_api.py --native-data /path/to/rendered/doc-data --source-revision a05b182aa17ea7cd1a591ec7b60aa7d6f2b6704c --check
python -B scripts/test_generate_api.py --native-data /path/to/rendered/doc-data --check-committed
python -B -O scripts/test_generate_api.py --native-data /path/to/rendered/doc-data --check-committed
python -B -OO scripts/test_generate_api.py --native-data /path/to/rendered/doc-data --check-committed
```

Omit `--check` only when intentionally regenerating `docs/API.md` and its
manifest. The tests use explicitly synthetic notes in temporary fixtures for
refusal/layout checks; `--check-committed` additionally verifies the assembled
real notes and generated files. Neither test mode approves mathematical note
semantics. Full headers, missing/extra/duplicate records, altered signatures,
all 76 changed inputs, forged manifests, invalid source URLs/ranges, hidden Lean
modules, damaged Git state and independent-history fallback are exercised.

## Native generation procedure

Use the pinned Lean toolchain and declared dependency access. Before any new
Scheme build, successfully fetch its matching mathlib cache from this checkout:

```sh
lake exe cache get
lake --wfail -v build SchemeProperties SchemePropertiesTest SchemePropertiesExamples
```

In a separate clean checkout of [doc-gen4](https://github.com/leanprover/doc-gen4)
at the exact revision above, use its pinned toolchain and manifest, ensure the
toolchain's `cc` is on PATH, and run `lake build doc-gen4`. This core-only tool
has no mathlib dependency. Use the resulting absolute executable path from the
Scheme checkout through `lake env`, so it sees the Scheme project's artifacts.
For each exact `module_paths` entry `(module, path)` in the contract, run:

```text
lake env /absolute/path/to/doc-gen4 single --build /absolute/path/to/analysis MODULE api.db https://github.com/FormalFrontier/scheme-properties/blob/a05b182aa17ea7cd1a591ec7b60aa7d6f2b6704c/PATH
lake env /absolute/path/to/doc-gen4 bibPrepass --build /absolute/path/to/rendered --none
lake env /absolute/path/to/doc-gen4 fromDb --build /absolute/path/to/rendered --manifest /absolute/path/to/rendered/manifest.json /absolute/path/to/analysis/api.db
```

Substitute `MODULE` and `PATH` for every one of the 73 entries; `single` runs
once per module, then bibliography/render once. Use fresh output directories.
The source hashes must still match the fixed contract even if the development
commit is absent from the checkout's independent history. Retain command exits,
complete streams, source/pin checks, output hashes and resource evidence when
using a new run for review. These command templates describe native generation,
not an automatic resource supervisor or a reason to repeat accepted evidence.

The retained native run replayed cached ProofWidgets npm warnings, two old
vulnerability summaries (each 4 moderate and 6 high), and circular-dependency
notices. An initial zero-warning regex missed those forms and was corrected in
the evidence. This is not a new security scan or a warning-free claim. No npm
audit/fix or dependency substitution is part of the reproduction procedure.
