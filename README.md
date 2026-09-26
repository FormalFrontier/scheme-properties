# scheme-properties

Reusable Lean theory of scheme properties under specialization, localization,
and local-to-global criteria.

**Authors: Formal Frontier Agents.** Original project work is licensed under
[Apache-2.0](LICENSE). Distinct contributor and reused-formal-expression credits
are in [CREDITS](docs/CREDITS.md). See the [reader guide](docs/Guide.md) for
focused imports, precise hypotheses and inspected example clients.
The [generated API reference](docs/API.md) preserves the native display
signatures and links directly to the source in this checkout. Its exact input
contract and reproduction instructions are in [API generation](docs/README.md).

The library's official `coherent-modules` and `finite-etale-algebras` dependencies
are pinned to **private** GitHub repositories. Users require authorized access
to fetch them; this is not a public-availability promise.

## Status

This repository is under active development. At documentation preparation on
September 26, 2026, the frozen 73-module source and official dependency pins had
passed a fresh source/client build and native API generation. Complete release
proof/axiom intake and independent exact-candidate release review were not yet
recorded for this assembly. Build success and generated documentation are not
release acceptance. Results on feature branches become accepted library API
only after independent review and integration into protected `main`.

## Intended API

The first unit packages three facts:

- `IsLocalization.isReduced` allows source and localization rings in independent
  universes;
- `IsLocalization.AtPrime.isReduced_of_le` passes reducedness between two prime
  localizations in the direction induced by inclusion of the primes; and
- `AlgebraicGeometry.isReduced_stalk_of_specializes` preserves reducedness of
  scheme stalks under generalization.

The API is source-independent and makes no compactness, Noetherianity,
finite-type, separation, field, or nonemptiness assumption.

The second unit proves that domain stalks make irreducible components locally
disjoint, and packages the resulting criterion that a connected locally
Noetherian scheme with domain stalks is integral. The exact Noetherian form is
also exposed for source-facing clients.

The third unit defines a normal scheme by requiring every stalk to be an
integrally closed domain. It proves localization and generalization lemmas,
normality of spectra of locally normal rings, the equivalence between affine-
spectrum normality and local normality of the coordinate ring, preservation
under open immersions and scheme isomorphisms, an open-cover criterion, and
that normal schemes are reduced. The local ring interface permits disconnected
rings, is preserved by ring equivalences, and specializes automatically from
integrally closed domains. Arbitrary localizations preserve this local
normality, including for disconnected bases. Polynomial rings and
finite-variable multivariate polynomial rings also preserve local normality
without a global domain hypothesis on the base. Finite etale algebras preserve
local normality as well, with independently varying base and target universes.
Flat directed unions of locally normal subrings are locally normal. Consequently,
tensoring a locally normal algebra with a transcendental-separable field
extension preserves local normality, including for disconnected algebras.
Consequently, normal schemes remain normal after base change along such field
extensions.

The fourth unit packages every locally connected scheme as the coproduct of
its open connected-component subschemes. It also provides the corresponding
summand compatibility and the componentwise map from a scheme into a coproduct
of copies of a target. The construction permits empty schemes and infinitely
many components.

The fifth unit proves that Noetherian spaces are locally connected and applies
this to Noetherian schemes. Their connected-component index is finite; each
component open subscheme is connected and Noetherian; the components form an
open cover on which normality can be checked; and the components of a normal
Noetherian scheme are integral. The unit reuses the general coproduct
isomorphism from the fourth unit.

The sixth unit defines a factorial scheme by unique factorization in every
stalk. It proves localization and generalization lemmas, factoriality of spectra
of unique factorization domains and Dedekind domains, preservation under open
immersions and scheme isomorphisms, and an open-cover criterion. The Dedekind
result applies even when the original domain is not a unique factorization
domain, since all of its local rings are principal ideal domains.

The seventh unit proves that every factorial scheme is normal by combining the
factorial stalk instances with the existing integrally-closed theorem for GCD
domains. It adds no competing ring-theoretic definition or UFD theorem.

The eighth unit connects the scheme-facing restriction API for modules with
the over-site API used in the definition of quasicoherence. It proves that, on
any fixed affine open cover, a module is quasicoherent if and only if every
restricted module is recovered by the affine `fromTildeΓ` map after transport
along the canonical spectrum isomorphism. Arbitrary covers, empty schemes and
zero modules are supported without finiteness, nonemptiness, Noetherian,
reduced, integral, finite-type, separation or field assumptions.

The ninth unit characterizes torsion modules over **any commutative ring** by
vanishing after base change to a localization at its non-zero-divisors, including
the canonical total quotient ring. It defines stalkwise
torsion-freeness and vanishing at component generic points for arbitrary
modules on schemes, with isomorphism invariance, empty-scheme and zero-module
instances, and equivalent irreducible-component indexing. For modules on an
integral affine spectrum produced by `tilde`, generic vanishing is equivalent
both to torsion and to zero fraction-ring base change. This last equivalence
requires an integral affine base, unlike the general commutative-ring torsion
theorem; the stalkwise predicates themselves do not require quasicoherence,
reducedness, finiteness or nonemptiness.

The tenth unit proves that the tensor product of arbitrary extension fields of
a separably closed field has connected prime spectrum, including over
imperfect bases and for transcendental extensions. Consequently every
connected scheme over a separably closed field is geometrically connected,
without finite-type, reducedness, irreducibility, separation, properness,
algebraicity or rational-point hypotheses. The scheme API currently follows
mathlib's same-universe boundary.

The eleventh unit proves the module-valued qcqs lemma. For a quasicoherent
module and a section on any compact quasiseparated open, restriction of module
sections to the associated basic open is localization away from that section;
a global-sections specialization is also provided. The result supports empty
schemes and opens, zero modules, and the sections `0` and `1`, without
Noetherianity, reducedness, affineness, nonemptiness, separation, or finiteness
assumptions beyond compactness and quasiseparatedness of the chosen open.

The twelfth unit identifies the global sections of a quasicompact,
quasiseparated scheme after extending its base field from `k` to `K` with
`K ⊗[k] Γ(X, ⊤)`. The canonical `K`-algebra equivalence includes formulas
for both tensor-product generators and arbitrary pure tensors, agrees with the
tensor left unitor for the identity extension, and is compatible with direct
and successive extensions through its canonical pullback isomorphism. It
supports empty schemes, zero global rings, and infinite field extensions,
without assuming that the scheme is affine, separated, reduced, connected, or
nonempty. The scheme API currently follows mathlib's same-universe boundary.

The thirteenth unit proves that the native full subcategory of quasicoherent
modules on an arbitrary scheme is abelian. It establishes closure under zero,
finite products, kernels, and cokernels by proving finite-limit preservation for
the affine `tilde` functor and for restriction along open immersions, then gluing
over affine opens. No Noetherianity, separation, qcqs, nonemptiness, cover
finiteness, or module finiteness assumption is used.

The fourteenth unit connects native quasicoherent module sections with
`Module.IsCoherent`. On any compact quasiseparated open, coherence of the
section module is preserved on a principal open, and it descends from an
arbitrary set-indexed family of principal opens whose defining sections span
the unit ideal. The statements retain the principal-open structure ring and
its scalar tower explicitly, allow zero sections, zero modules, zero rings and
an empty spanning set when its span is top, and impose no artificial
nonemptiness or finiteness condition. On an affine spectrum in the same
universe, the unit also exposes the inverse image of `ModuleCat.isCoherent`
under the native `tildeEquiv.inverse`, with literal membership and `tilde`
bridge lemmas. This unit uses the exact one-way dependency on
`coherent-modules` pinned in `lakefile.toml`; `coherent-modules` remains
independent of this repository.

The fifteenth unit constructs the finite-etale component scheme of a
quasi-compact scheme locally of finite type over a field. It selects the
greatest finite-etale subalgebra of global sections, proves that the canonical
map to its spectrum is surjective, and gives the exact universal factorization
through every finite-etale affine target. The construction supports empty
schemes, zero global rings, disconnected schemes, and nonreduced schemes, and
does not assume separatedness, reducedness, connectedness, or nonemptiness.
This unit uses the exact one-way dependency on `finite-etale-algebras` pinned in
`lakefile.toml`; `finite-etale-algebras` remains independent of this repository.

The sixteenth unit proves that the component scheme commutes canonically with
every same-universe field extension. It supplies the comparison on coordinate
algebras, the corresponding comparison of schemes and compatibility triangle,
literal equality of the scalar-extended and newly selected component
subalgebras, and the resulting algebra equivalence and categorical isomorphism.
It applies to identity, separable, purely inseparable, transcendental, and
mixed extensions, including disconnected, nonreduced, and empty sources, with
no algebraicity, finite-dimensionality, separability, perfectness,
connectedness, reducedness, nonemptiness, or separatedness hypothesis.

The seventeenth unit identifies each scheme-theoretic residue-field fibre of
the component map with its connected component on underlying points and proves
that the fibre is geometrically connected. Equivalently, the fibre's greatest
finite-etale subalgebra of global sections is exactly the scalar subalgebra.
It supports disconnected, nonreduced and empty sources and arbitrary residue
fields without separatedness, reducedness, connectedness, nonemptiness,
algebraic-closure, separability or perfectness assumptions. The scheme API
retains the existing same-universe boundary.

The eighteenth unit identifies sections on an arbitrary open of a
same-universe indexed coproduct of schemes with the dependent product of the
sections on its component preimages. Its forward map is literally pullback to
each coproduct summand, and its coordinate formula commutes with restriction,
including restriction to basic opens through the existing
`Scheme.preimage_basicOpen` API. It imposes no finiteness, nonemptiness,
affineness, separation, compactness, or Noetherian hypothesis.

The nineteenth unit proves that a same-universe indexed coproduct of
quasiseparated schemes is quasiseparated, including empty families and empty
components. It also proves that such a coproduct is not compact when the index
type is infinite and every component is nonempty. The quasiseparated instance
adds no compactness, nonemptiness, Noetherianity, separation, reducedness,
affineness, or finiteness assumption.

The twentieth unit, available from `import SchemeProperties.StructureSheaf`,
proves `AlgebraicGeometry.Scheme.Modules.unit_isQuasicoherent`: the structure
sheaf is quasicoherent as a module over itself on every scheme, including the
empty scheme, with no finiteness or separation assumptions.

The twenty-first unit packages every `Scheme.IdealSheafData` as the sectionwise
kernel submodule of its canonical quotient map. It identifies affine sections
with the specified ideals, proves basic-open localization and quasicoherence,
and exposes the nilradical through thin module and subobject clients. The
construction supports zero rings and empty schemes and opens without additional
nonemptiness, finiteness, separation, compactness, or reducedness assumptions.

A further unit constructs the ambient tensor product of arbitrary modules on a
scheme by sheafifying their pointwise presheaf tensor. It provides a bifunctor,
the sheafification unit, pure tensor sections with additive, scalar and
restriction laws, the exact all-target sheafification Hom equivalence, and a
natural pure-compatible symmetry. It supports zero modules, zero rings, empty
schemes and empty opens, without quasicoherence, finiteness, nonemptiness,
compactness or separation assumptions. It adds no monoidal-category instance on
the category of scheme modules.

Restriction along an open immersion commutes with this ambient tensor via
`Scheme.Modules.restrictTensorNatIso`, naturally in both module arguments.
`restrictTensorNatIso_inv_app_tmul` gives the explicit pure-tensor formula
through the native restriction/scalar identifications. The comparison uses
actual sheafification and supports arbitrary modules, zero rings, empty schemes
and empty opens; it does not assume quasicoherence or introduce a global
monoidal instance. It is available directly from
`import SchemeProperties.ModuleTensorRestriction` or the aggregate root.

Taking stalks commutes with the pointwise tensor of presheaves of modules over
a commutative-ring presheaf: `PresheafOfModulesOfCommRing.stalkTensorEquiv` uses
the native ring-stalk module structures, identifies germs of pure tensors, and
is natural in both module arguments. The linear stalk map
`stalkMapLinear` and its germ formula are also available directly from
`import SchemeProperties.PresheafModuleTensorStalk`, without scheme imports or
a sheaf assumption.

For any commutative ring `R`, `Scheme.Modules.affineTensorNatIso` identifies
the existing sheafified tensor of associated modules on `Spec R` with the
associated module of their algebraic tensor product, naturally in both inputs.
`affineTensorNatIso_inv_app_top_tmul` gives its inverse component on top-open
pure-tensor sections. No quasicoherence, finiteness or nonemptiness assumption
is required; zero rings and modules are included. Import
`SchemeProperties.ModuleTensorAffine` directly or use the aggregate root.

On a principal open `D(f)` of `Spec R`,
`Scheme.Modules.basicTensorEquiv` identifies the tensor of associated-module
sections over the *native* ring `Γ(Spec R, D(f))` with sections of their
sheafified tensor. Its forward map is the actual `tensorUnit` component, and
`basicTensorEquiv_tmul` records its pure-tensor law. The native localization
`locTensor` sends `m ⊗ n` to the tensor of their basic-open sections;
`actual_restriction_square` identifies the inverse tensor-unit map after
restriction from the top open with this localization after
`topTensorEquiv`. Every inclusion of principal opens respects the comparison,
semilinearly along the actual structure-sheaf restriction, and the map is
natural in both modules. `awayTensorEquiv` transports it to the native
`Localization.Away f` presentation, with `awayLocTensor` built independently
from native localization maps. There are no nonzero, regularity, finiteness or
nonemptiness assumptions, including when `f = 0` or the ring is zero. This
does **not** assert a tensor-of-sections equivalence on arbitrary opens.
Import `SchemeProperties.ModuleTensorLocalization` or the aggregate root.

`import SchemeProperties.SheafFinitePresentation` provides the site-generic
`SheafOfModules.LocalGeneratorsData.isFinitePresentation_of_isLocallyFreeData`:
for one local-generator datum with both a local basis and finite generators on
each chart, the underlying sheaf of modules is finitely presented in mathlib's
native sense. The cover need not be finite and basis sizes may vary, including
zero; the theorem assumes the native sheafification conditions on each over-site
and does not infer compatibility of two independently chosen local covers.
It depends only on mathlib and is also available from the aggregate root.

Downstream projects should import the aggregate root:

```lean
import SchemeProperties
```

## Reproduction

Install [elan](https://github.com/leanprover/elan) and use the pinned Lean
v4.34.0-rc2 toolchain, mathlib `83abb3e776bdefcbc447a1e44d0debe4010039e5`
and exact official private `coherent-modules` / `finite-etale-algebras` revisions
in `lakefile.toml` and `lake-manifest.json`. Once dependency access is available,
fetch the matching precompiled mathlib cache before every build in a new
checkout or after changing pins, then build the default library, all shipped
`Examples` and `Test` targets:

```sh
lake exe cache get
lake --wfail build SchemeProperties SchemePropertiesTest SchemePropertiesExamples
```

The native-documentation source build used these three targets, with verbose
traces, on source `a05b182aa17ea7cd1a591ec7b60aa7d6f2b6704c` and the exact
official pins now bound in [api-manifest.json](docs/api-manifest.json).
Cached ProofWidgets tasks replayed npm warnings and vulnerability/circular-
dependency notices; these were retained, not treated as a fresh security audit
or repaired by changing dependencies. Neither a successful build nor example
compilation alone checks every declaration's axioms or establishes mathematical
source coverage. See [API generation](docs/README.md) for the distinct data-only
adapter and native generation procedures.

### Expected build cost

A September 26, 2026 baseline on x86_64 Linux with the pinned Lean
v4.34.0-rc2 and dependency revisions measured 104.624 seconds for the matching
mathlib-cache step, followed by 353.895 seconds for a fresh default build of all
73 shipped modules: 37 library/root modules, 21 `Test` modules and 15 `Examples`
modules. Thus, allow roughly six minutes for this source build plus about two
minutes for that cache step on a comparable environment. Unchanged dependencies
came from the matching cache; these are not cache-free dependency-rebuild timings.

That run used a 15 GiB worker memory limit. Its build-specific sampled cgroup
current-memory peak was 12.86 GiB, largely file cache; the sampled
current-minus-inactive-file peak was 1.53 GiB. Neither quantity establishes a
minimum RAM requirement. CPU model/quota were not recorded, and timings depend
on CPU availability, storage, network and cache state. The baseline excludes
toolchain installation, cloning, API documentation generation, separate
proof/axiom checks and downstream workloads; it is an initial measured baseline,
not a performance guarantee or a claimed speedup.
