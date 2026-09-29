# Integral schemes and dominant rational-map categories

Import `SchemeProperties.IntegralDominantRationalCategory` directly, or use the
`SchemeProperties` aggregate. `AlgebraicGeometry.IntegralDominantRationalScheme.{u}`
has integral same-universe schemes as objects and **dominant native quotient
rational maps** as arrows. An object has `toScheme` and a proof-only
`IsIntegral` field; `IntegralDominantRationalScheme.of X` packages an integral
scheme. `Hom.toRationalMap` and `Hom.dominant` expose the quotient and its
dominance proof. `hom r hr` constructs an arrow, `toRationalMap_hom` projects
it, and `hom_ext` identifies arrows with equal quotient maps. The category's
identity projects to native `Scheme.RationalMap.id`, and composition projects
to native `Scheme.RationalMap.comp`, via `toRationalMap_id` and
`toRationalMap_comp`.

`IntegralDenseOpenRationalScheme.{u}` is the integral-object
`ObjectProperty.FullSubcategory` of `DenseOpenRationalScheme`: the latter is a
category of **rational arrows**, not the ordinary category of scheme morphisms.
The full subcategory's `toRationalMap_comp` identifies its controlled
dense-open composition with native quotient composition at integral endpoints.
`IntegralDenseOpenRationalScheme.toNative` and
`IntegralDominantRationalScheme.toDenseOpen` preserve the underlying quotient.
The actual equivalence `integralDenseOpenEquivalence` has natural unit
`nativeUnitIso`, counit `nativeCounitIso` and a triangle law, not merely a
bijection of hom types; the inverse arrow converts dominance to dense-open
pullback using **both** integral endpoints.

`IsIntegral` provides nonemptiness and irreducibility, hence
preirreducibility, at each object. Native composition uses dominance of the
first arrow and nonemptiness of its target; dominance of the composite uses
**both** dominant arrows. Associativity uses the first two dominant arrows
and integrality of the first three objects. The controlled-to-native comparison
uses the first arrow's pullback property and dominance. These results do not
assert equality of arbitrary rational-map representative domains, a category
of all rational maps on arbitrary schemes, a functor to total scheme
morphisms, a relative-base statement, or finite-type, separatedness or
base-field assumptions. They do not change the ordinary `Scheme` category.

The [16 private direct-import uses](../Test/IntegralDominantRationalCategoryClient.lean)
exercise constructors, projections, extensionality, category laws, both
functors, their quotient-preserving maps and the unit and counit. They are
clients, not new public results; the [producer](../SchemeProperties/IntegralDominantRationalCategory.lean)
contains the reusable API.

## Reproduction and provenance

The [toolchain](../lean-toolchain) is `leanprover/lean4:v4.34.0-rc2`;
the [Lake requirements](../lakefile.toml) and [resolved manifest](../lake-manifest.json)
pin mathlib `83abb3e776bdefcbc447a1e44d0debe4010039e5` and official
private-GitHub `coherent-modules`
`fc30df937c7476f1c01f7cb39005f8cae37f8f34` and
`finite-etale-algebras` `79575f65c9edec560f27756917761eed78331a2a`.
Authorized access to private dependencies is needed. In a fresh checkout,
install the pinned Lean toolchain, successfully fetch the matching precompiled
mathlib cache before building, and compile the focused module and client:

```sh
lake exe cache get
LAKE_JOBS=2 lake --wfail build SchemeProperties.IntegralDominantRationalCategory
LAKE_JOBS=2 lake --wfail build SchemePropertiesTest
```

Build success alone is not a complete transitive standard-axiom audit (including
private and generated declarations). The repository's configured CI and
independent review can supply revision-specific destination evidence; neither
the originally checked incubator inputs nor this guide alone establishes
destination acceptance, official publication or selected-source coverage.
The original proof expression and actual contributor identities are recorded
in [Credits](CREDITS.md).

**Preparation history (September 29, 2026):** This module was mapped from an
independently reviewed isolated category contribution to the already accepted
`DenseOpenRationalScheme` interface. Its direct import and the aggregate root
are distinct destination inputs, requiring destination-specific checks and
review. Publication and source correspondence are separate owner decisions.
