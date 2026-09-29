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
LAKE_JOBS=2 lake exe cache get
LAKE_JOBS=2 lake --wfail build SchemeProperties.DenseOpenCompositionOver SchemePropertiesTest SchemeProperties
```

These are reproduction instructions, **not** destination-build evidence.
Complete acceptance also requires an applicable destination build and a
transitive audit of all actual public and private/generated origin declarations,
allowing only `propext`, `Classical.choice` and `Quot.sound`. The three-file
isolated incubator donor `ca314988f69afd77a1e7010678d92917c957134e`
was accepted independently with its own checks and review; the translation
here is prepared on accepted Scheme Properties main
`91c8a5621a6410568183b55d60b8bcace832a24c`. The destination candidate
is **not** thereby accepted, integrated or officially released; later
publication awaits the parent's official release and separate destination
review/checks. Neither client tests nor this guide establish selected-source
correspondence or coverage.

## Expression provenance

This producer reuses imported mathlib partial/rational-map and over-base APIs
by Andrew Yang and native composition/image-isomorphism APIs by Justus
Springer; their authentic copyright/Apache-2.0 notices remain in the
[producer](../SchemeProperties/DenseOpenCompositionOver.lean). Its partial-map
structure-triangle *proof expression* is adapted from the earlier Formal
Frontier [Scheme Properties RationalMapComposition proof](https://github.com/FormalFrontier/scheme-properties/blob/1af9eb14b0e3a0679cf6eac0ed59e186a4a6c636/SchemeProperties/RationalMapComposition.lean),
original Hive Task `hive-request-d04a528c8fefc542b1e53f2a0d565eecd90fde23`
(UID `94b1be7d-b4fc-4bc6-8fcf-c08d31f48c9e`), not from a copied
mathlib proof. The new donor proof and client were authored by Hive Task
`hive-request-5661a06674dafb5829660f4b9a743ffdb93c3d80`
(UID `1d6aee74-dee3-48bc-829f-fb75f94fb841`), independently reviewed by
Hive Task `hive-request-14519b787df658fed3e4d8842cf939ab26a9619b`
(UID `fa09a5dd-5607-4180-977d-5c04c3847550`), and statically
transferred here by Hive Task
`hive-request-dcea208125ec931be38b0d72b65e6e1fd842afaf`
(UID `15a63375-1cd2-4e7c-99c9-14b3c9ac98e3`). Atlas selects the
destination and controls review, integration and release. See
[CREDITS](CREDITS.md) for the distinct contributor and dependency credits.
