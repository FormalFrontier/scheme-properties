# Controlled dense-open composition over a scheme

Import `SchemeProperties.DenseOpenCompositionOver` directly, or import the
aggregate `SchemeProperties`. The [producer](../SchemeProperties/DenseOpenCompositionOver.lean)
imports [controlled composition](../SchemeProperties/DenseOpenComposition.lean),
which in turn supplies the existing partial- and rational-map operations. These
are named preservation lemmas, not new map types or global instances.

For arbitrary `X Y Z S : Scheme.{u}` with `[X.Over S] [Y.Over S] [Z.Over S]`,
the two public declarations in `AlgebraicGeometry.Scheme` are:

| Declaration | Maps and conclusion |
| --- | --- |
| `PartialMap.isOver_compOfPullsDenseOpens` | For `f : X.PartialMap Y`, `hf : f.PullsDenseOpens`, `g : Y.PartialMap Z`, `[f.IsOver S] [g.IsOver S]`, proves `(f.compOfPullsDenseOpens hf g).IsOver S`. |
| `RationalMap.isOver_compOfPullsDenseOpens` | For `f : X ⤏ Y`, `hf : f.PullsDenseOpens`, `g : Y ⤏ Z`, `[f.IsOver S] [g.IsOver S]`, proves `(f.compOfPullsDenseOpens hf g).IsOver S`. |

The first-map predicate says that **every** dense target open pulls back
densely in the whole source; it is supplied explicitly. There is no
second-map `PullsDenseOpens` assumption, dominance, nonemptiness,
preirreducibility, integrality, reducedness or separation hypothesis. In
particular, these results do not assert that the predicate is closed under
composition or that the controlled composite satisfies category laws.

The partial-map proof checks the composite's structure-morphism triangle
using `PartialMap.isOver_iff`, `morphismRestrict_ι` and
`Scheme.Hom.isoImage_inv_ι`. The rational-map proof uses
`RationalMap.exists_partialMap_over S` to choose **over-`S`** representatives,
transports the predicate via `PartialMap.pullsDenseOpens_toRationalMap_iff`,
and identifies the quotient composite via
`RationalMap.toRationalMap_compOfPullsDenseOpens`. It does **not** claim that
an arbitrarily chosen representative is over `S` on its entire domain; only
an over-`S` representative or a suitable dense restriction is guaranteed.

The [ordinary-import client](../Test/DenseOpenCompositionOverClient.lean)
checks five *private* generic theorems: the two direct lemmas, a quotient
representative, an open-first sufficient condition via
`PartialMap.pullsDenseOpens_of_isOpenMap`, and a total-second compatibility via
`PartialMap.compOfPullsDenseOpens_toPartialMap`. They are not public API or
constructed empty, reducible or nondominant examples. For the predicate
itself, see [dense-open pullback](DenseOpenPullback.md); for the controlled
operations, see [controlled composition](DenseOpenComposition.md). The
[separate native composition results](RationalMapComposition.md) instead
assume a dominant first map, preirreducible source and nonempty intermediate
scheme, with their own native `comp` operation.

## Reproduction and status

Use the pinned `lean-toolchain` (`leanprover/lean4:v4.34.0-rc2`),
`lakefile.toml` and `lake-manifest.json` (mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`). Official
`coherent-modules` and `finite-etale-algebras` dependencies are private
GitHub repositories and require authorized access. From a fresh checkout,
install the pinned toolchain and successfully fetch the matching mathlib
cache **before** building:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake --wfail build SchemeProperties.DenseOpenCompositionOver SchemePropertiesTest SchemeProperties
```

The producer adapts imported native partial/rational-map and over-base
interfaces by Andrew Yang and composition/image-isomorphism interfaces by
Justus Springer. Their authentic individual notices remain in the Lean
source; see [Credits](CREDITS.md).
