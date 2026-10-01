# Documentation and API reproduction

[Reader guide](Guide.md) indexes the current mathematical modules and examples;
the [README](../README.md) summarizes headline results and usage. The focused
guides here explain later APIs, including
[generic-point rational noninvertibility](GenericPointRationalNoninvertibility.md).
[API.md](API.md) is a navigation-adjusted
historical **73-module** reference, not a census of the current
checkout. Its original byte-identical [generated API page](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/docs/API.md)
and the unchanged [api-manifest.json](api-manifest.json) belong to the original
published revision `6b204a3e49f022e51d78a9f93e77513b99a87e00`.

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
Source ranges come from historical native records and link to the original
published source, not the shifted line numbers in this checkout. A generated
reassociation lemma may point to its parent's attribute line, and a field may
point to only its starting line. Consult the surrounding source for the
complete definition.

Display sites are not a complete raw/private declaration or stored-value census.
Neither the generator nor its manifest certifies proofs, source coverage or
release acceptance.

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
compared with it. The original published revision has an independent Git
history: when the private analyzed-source object is absent, the adapter uses
its committed manifest and requires the same fixed **76** source/configuration
hashes and **73** module paths. This is verification, not permission to repin
or learn hashes from changed files. Only an explicit missing Git object or a
source tree without Git permits that fallback; a broken Git repository is
refused. Fetching the private analyzed-source object is not required.
Historical source-range links here target the matching original published
revision; the reader guide and current module links remain local.
The original native GitHub linker is validated as provenance, not claimed to be
a publicly fetchable development commit or emitted as the reader's source link.

## Data-only reproduction from native records

For **both** adapter checks and optional native generation below, use a
**separate checkout** of the exact original published revision. It contains
the original generated API, the fixed contract, manifest, adapter and tests.
Access to the published GitHub repository currently requires authorization;
its public visibility is a separate decision. From a parent directory outside
this current checkout, for example:

```sh
cd /path/to/parent-directory
git clone https://github.com/FormalFrontier/scheme-properties.git scheme-properties-historical
cd scheme-properties-historical
git checkout --detach 6b204a3e49f022e51d78a9f93e77513b99a87e00
```

Run the following commands **in that historical checkout**, with the 73-module
Lean source and all 76 frozen inputs, not from the current checkout.
Obtain the native `doc-data` records from a matching authenticated generation
or reproduce them as below. They are inputs to the adapter, not bundled raw
execution transcripts. Python 3's standard library suffices for this step:

```sh
python -B scripts/generate_api.py --native-data /path/to/rendered/doc-data --source-revision a05b182aa17ea7cd1a591ec7b60aa7d6f2b6704c --check
python -B scripts/test_generate_api.py --native-data /path/to/rendered/doc-data --check-committed
python -B -O scripts/test_generate_api.py --native-data /path/to/rendered/doc-data --check-committed
python -B -OO scripts/test_generate_api.py --native-data /path/to/rendered/doc-data --check-committed
```

Here `--check` checks the **original** `docs/API.md` at the historical revision,
not the navigation-adjusted current page. Omit it only when intentionally
regenerating that historical checkout's `docs/API.md` and its manifest.
The tests use explicitly synthetic notes in temporary fixtures for
refusal/layout checks; `--check-committed` additionally verifies the assembled
real notes and generated files. Neither test mode approves mathematical note
semantics. Full headers, missing/extra/duplicate records, altered signatures,
all 76 changed inputs, forged manifests, invalid source URLs/ranges, hidden Lean
modules, damaged Git state and independent-history fallback are exercised.

## Native generation procedure

Stay in that separate historical Scheme checkout for optional native generation.
Use its pinned Lean toolchain and declared dependency access. Before any new
Scheme build, successfully fetch its matching mathlib cache there:

```sh
lake exe cache get
lake --wfail -v build SchemeProperties SchemePropertiesTest SchemePropertiesExamples
```

In a separate clean checkout of [doc-gen4](https://github.com/leanprover/doc-gen4)
at the exact revision above, use its pinned toolchain and manifest, ensure the
toolchain's `cc` is on PATH, and run `lake build doc-gen4`. This core-only tool
has no mathlib dependency. Use the resulting absolute executable path from the
historical Scheme checkout through `lake env`, so it sees that project's artifacts.
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
