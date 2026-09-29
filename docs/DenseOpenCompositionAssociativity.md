# Associativity for controlled dense-open composition

Import `SchemeProperties.DenseOpenCompositionAssociativity` directly (or the
aggregate `SchemeProperties`) for
`AlgebraicGeometry.Scheme.PartialMap.compOfPullsDenseOpens_assoc` and
`AlgebraicGeometry.Scheme.RationalMap.compOfPullsDenseOpens_assoc`. The
[producer](../SchemeProperties/DenseOpenCompositionAssociativity.lean) imports
the [two-factor closure theorem](../SchemeProperties/DenseOpenCompositionClosure.lean);
the independent [direct-import client](../Test/DenseOpenCompositionAssociativityClient.lean)
uses both new theorems without importing the aggregate root.

For arbitrary same-universe schemes `X Y Z T : Scheme.{u}`, partial maps
`f : X.PartialMap Y`, `g : Y.PartialMap Z`, `h : Z.PartialMap T`, and only
`hf : f.PullsDenseOpens`, `hg : g.PullsDenseOpens`, the partial-map theorem
establishes **literal equality of partial maps**:

```lean
(f.compOfPullsDenseOpens hf g).compOfPullsDenseOpens
  (f.pullsDenseOpens_compOfPullsDenseOpens hf g hg) h =
  f.compOfPullsDenseOpens hf (g.compOfPullsDenseOpens hg h)
```

For `r : X ⤏ Y`, `s : Y ⤏ Z`, `t : Z ⤏ T` with only
`hr : r.PullsDenseOpens`, `hs : s.PullsDenseOpens`, the quotient theorem is:

```lean
(r.compOfPullsDenseOpens hr s).compOfPullsDenseOpens
  (r.pullsDenseOpens_compOfPullsDenseOpens hr s hs) t =
  r.compOfPullsDenseOpens hr (s.compOfPullsDenseOpens hs t)
```

The closure witness for the **left** bracketing uses the first two maps'
predicates; the right bracketing uses the second map's predicate. Neither
theorem constrains the third map, assumes dominance, irreducibility,
nonemptiness or reducedness, or establishes an over-base/category law.
`PullsDenseOpens` measures density in the **ambient source scheme** rather
than only the partial map's dense domain. Literal partial-map equality includes
open domains and transported homs; rational-map equality holds in Andrew
Yang's existing quotient without identifying arbitrary representatives' domains.

The partial proof adapts Justus Springer's native domain **and morphism**
normalization using restriction/image isomorphisms and monicity of open
inclusions; it does not use native `PartialMap.comp_assoc` with its stronger
geometric premises. The rational proof transports arbitrary representatives
via `toRationalMap` and the controlled-composition bridges. The private client
checks both generic laws, a partial-to-rational representative instance and
an iterated partial composition (one private definition and its equality).
These parameterized clients do not construct exceptional schemes.

**Provenance and rights.** The producer retains Springer's authentic 2026
copyright, Apache-2.0 and author notice for the adapted mathlib
`Mathlib/AlgebraicGeometry/Birational/Composition.lean` expression.
Yang's native partial/rational quotient and representative APIs are imported,
not copied. The isolated Lean donor is commit
`026707accc8303e154ef50b21af18fe1e3cedeb8`; this library adaptation
has separate [contributor credits](CREDITS.md). Neither these theorems nor
their private examples assert source-specific coverage or an eventual release.

Use the repository's pinned Lean `leanprover/lean4:v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and exact
`lake-manifest.json` dependencies. Authorized access to the pinned private
GitHub dependencies is required. From the repository root, the matching
mathlib-cache fetch **must succeed before any build**:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
LAKE_JOBS=2 lake exe cache get
LAKE_JOBS=2 lake --wfail build SchemeProperties.DenseOpenCompositionAssociativity
LAKE_JOBS=2 lake --wfail build SchemePropertiesTest SchemeProperties
```

Completeness requires an applicable successful build and a transitive axiom
audit of the actual public, generated and private declarations, with only
`propext`, `Classical.choice` and `Quot.sound`, plus independent destination
review and maintainer acceptance. This guide itself is not evidence of those
checks or of publication.
