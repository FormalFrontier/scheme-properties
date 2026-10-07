# Dense-open rational-map category

Import `SchemeProperties.DenseOpenRationalCategory` directly, or use the
`SchemeProperties` aggregate. For any same-universe `Scheme.{u}` objects,
`AlgebraicGeometry.DenseOpenRationalScheme.of X` wraps the underlying scheme;
there is no irreducibility, nonemptiness, reducedness or dominance assumption
on objects. Arrows `X ⟶ Y` are proof-only bundles of mathlib's native quotient
`X.toScheme ⤏ Y.toScheme` with the existing
`Scheme.RationalMap.PullsDenseOpens` property. This is a **separate** category:
the ordinary `Scheme` category and its morphisms are unchanged, and no
forgetful functor to total scheme morphisms is asserted.

`AlgebraicGeometry.DenseOpenRationalScheme.hom r hr` constructs an arrow;
`toRationalMap_hom` recovers the original *quotient rational map*, and
`hom_ext` proves arrow equality from equality of underlying rational maps.
The anonymous `Category` instance supplies identity and composition over
arbitrary same-universe schemes. Identity projects to `Scheme.RationalMap.id`
via `toRationalMap_id`. Composition projects via `toRationalMap_comp` to
`RationalMap.compOfPullsDenseOpens`, using the **first** arrow's property;
closure of the arrow predicate requires **both** factors. Associativity uses
the controlled-composition law with dense-open pullback on the **first two**
maps. Ordinary `Category.id_comp`, `Category.comp_id` and `Category.assoc`
therefore apply without any additional geometric hypotheses.

```lean
import SchemeProperties.DenseOpenRationalCategory

open AlgebraicGeometry AlgebraicGeometry.DenseOpenRationalScheme CategoryTheory

example {X Y Z : DenseOpenRationalScheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toRationalMap =
      f.toRationalMap.compOfPullsDenseOpens f.pullsDenseOpens g.toRationalMap :=
  toRationalMap_comp f g
```

Only when **both** underlying schemes are preirreducible **and** nonempty does
`homEquivDominant X Y` identify their hom type with the subtype of native
rational maps satisfying `IsDominant`; `homEquivDominant_apply_val` identifies
its underlying map. This is not an unrestricted dominance iff. The existing
`compOfPullsDenseOpens_eq_comp` comparison with native composition has its
own additional hypotheses and does not identify arbitrary representatives.
The [direct-import private client](../Test/DenseOpenRationalCategoryClient.lean)
exercises constructors, category laws, projections, extensionality and the
bounded dominance equivalence.

## Reproduction and status

The [pinned toolchain](../lean-toolchain) is
`leanprover/lean4:v4.34.0-rc2`. The [Lake requirements](../lakefile.toml) and
[resolved manifest](../lake-manifest.json) pin mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and the official
private-GitHub `coherent-modules` release
`408a52bd54df17ccc928ce970942f1313ff10d5c` and
`finite-etale-algebras` release
`79575f65c9edec560f27756917761eed78331a2a`. Authorized access to
those dependencies is required. With the pinned toolchain installed, fetch
the matching precompiled mathlib cache successfully **before** any build:

```sh
lake exe cache get
lake --wfail build SchemeProperties.DenseOpenRationalCategory SchemePropertiesTest SchemeProperties
```

The category is implemented in the focused module and tested by its
direct-import client. See [Credits](CREDITS.md) for adapted expression.
