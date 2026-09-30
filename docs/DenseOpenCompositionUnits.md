# Unit laws for controlled dense-open composition

Import `SchemeProperties.DenseOpenCompositionUnits` directly, or import the
aggregate `SchemeProperties`. The [producer](../SchemeProperties/DenseOpenCompositionUnits.lean)
directly imports [controlled composition](../SchemeProperties/DenseOpenComposition.lean);
the [private direct-import client](../Test/DenseOpenCompositionUnitsClient.lean)
checks all six laws and two representative instances without the aggregate root.
These declarations live in the native `AlgebraicGeometry.Scheme.PartialMap`
and `AlgebraicGeometry.Scheme.RationalMap` namespaces.

For any same-universe `X Y : Scheme.{u}`, without geometric typeclasses,
there are **six** entry points:

| Native namespace | Identity predicate | Left unit | Right unit |
| --- | --- | --- | --- |
| `PartialMap` | `pullsDenseOpens_id (X : Scheme.{u}) : (PartialMap.id X).PullsDenseOpens` | `id_compOfPullsDenseOpens (f : X.PartialMap Y)`: `(PartialMap.id X).compOfPullsDenseOpens (pullsDenseOpens_id X) f = f`, with **no** predicate on `f` | `compOfPullsDenseOpens_id (f : X.PartialMap Y) (hf : f.PullsDenseOpens)`: `f.compOfPullsDenseOpens hf (PartialMap.id Y) = f` |
| `RationalMap` | `pullsDenseOpens_id (X : Scheme.{u}) : (RationalMap.id X).PullsDenseOpens` | `id_compOfPullsDenseOpens (r : X ⤏ Y)`: `(RationalMap.id X).compOfPullsDenseOpens (pullsDenseOpens_id X) r = r`, with **no** predicate on `r` | `compOfPullsDenseOpens_id (r : X ⤏ Y) (hr : r.PullsDenseOpens)`: `r.compOfPullsDenseOpens hr (RationalMap.id Y) = r` |

`PullsDenseOpens` means that the preimage of every dense target open has
dense image in **ambient `X`**, not just inside a partial map's domain.
The identity has this property even for empty or reducible schemes. The
controlled operation needs only its first-map predicate; the left unit needs
the identity predicate but imposes none on the arbitrary second map. The
right unit requires the actual first map's predicate. There is no dominance,
irreducibility, nonemptiness, reducedness or over-base assumption.

The partial left unit is **literal partial-map equality**: it identifies the
actual pullback-image open domain and the hom after transport through
`Scheme.isoOfEq`. The partial right proof uses the total-second bridge and
native `PartialMap.compHom_id`. Rational laws are **equalities in the native
quotient**, valid for arbitrary representatives; they do not equate arbitrary
representatives' literal open domains or homs. The rational left proof uses
the accepted first-representative bridge. It does **not** identify the
quotient's chosen identity representative with the literal `PartialMap.id X`.
The rational right proof uses an arbitrary representative, the total-second
bridge and `PartialMap.compHom_id` via `RationalMap.compHom_toRationalMap`;
it does not assume a general rational `compHom_id`. In contrast,
`RationalMap.id_compHom` has rational identity on the **left** and an ordinary
morphism on the **right**; it is not the rational right-unit theorem.

The direct client also specializes rational left and right unit laws to
`f.toRationalMap`, without asserting equality of representatives. The
[predicate](DenseOpenPullback.md), [controlled operation](DenseOpenComposition.md),
[two-factor closure](DenseOpenCompositionClosure.md),
[associativity](DenseOpenCompositionAssociativity.md) and
[over-base companion](DenseOpenCompositionOver.md) remain separate focused APIs:
closure requires **both** predicates, and associativity the **first two**
predicates with no condition on the third map. This leaf adds no new maps,
category or subtype structure, identity functor, or over-base theorem.

**Provenance and rights.** The producer preserves Justus Springer's authentic
2026 copyright, Apache-2.0 and author notice for adapted native partial-map
**domain and morphism** normalization from mathlib's
`Mathlib/AlgebraicGeometry/Birational/Composition.lean`. Andrew Yang's native
partial-map and rational-quotient/representative APIs are imported, not copied.
The Formal Frontier adaptation and individual upstream authors are distinguished
in [Credits](CREDITS.md) and the Lean header.

For reproducibility, use the repository's pinned Lean
`leanprover/lean4:v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and the exact
`lake-manifest.json` graph. Authorized access to the two pinned private
GitHub dependencies is required. From the project root, **successfully fetch
the matching mathlib cache before building**:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake --wfail build SchemeProperties.DenseOpenCompositionUnits
lake --wfail build SchemePropertiesTest SchemeProperties
```

The focused modules set `warningAsError true`. For adapted mathlib expression
and original project contributions, see [Credits](CREDITS.md).
