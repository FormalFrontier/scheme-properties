# Dense-open pullback closure for controlled composition

Import `SchemeProperties.DenseOpenCompositionClosure` to use the two
closure theorems on mathlib's existing partial maps and rational-map quotient.
The producer imports `SchemeProperties.DenseOpenComposition` directly;
the private [direct-import client](../Test/DenseOpenCompositionClosureClient.lean)
exercises six generic uses. The aggregate `SchemeProperties` also imports this
leaf. These APIs use the repository's declared private GitHub dependencies,
which require authorized access.

For arbitrary same-universe schemes `X Y Z : Scheme.{u}` and maps
`f : X.PartialMap Y`, `g : Y.PartialMap Z`, the theorem
`PartialMap.pullsDenseOpens_compOfPullsDenseOpens f hf g hg` proves
`(f.compOfPullsDenseOpens hf g).PullsDenseOpens` from
`hf : f.PullsDenseOpens` and `hg : g.PullsDenseOpens`. Similarly,
`RationalMap.pullsDenseOpens_compOfPullsDenseOpens f hf g hg` proves the
same result for `f : X ⤏ Y` and `g : Y ⤏ Z`. The original
`compOfPullsDenseOpens` operations themselves retain only the **first**
predicate as an argument. `PullsDenseOpens` measures density in each map's
**ambient source scheme**, not just its open domain.

The partial-map proof first identifies the composite's pullback of *every*
open `W : Z.Opens` with the first map's pullback of the second map's pullback
of `W`. The composite morphism uses the inverse of the image isomorphism from
the preimage open to its ambient open image. `Hom.comp_preimage`,
`Hom.inv_preimage`, `Hom.comp_image`, `Hom.isoImage_hom_ι` and the arbitrary-map
`image_morphismRestrict_preimage` normalize this identity. For dense `W`, the
second predicate supplies a dense open of `Y`, to which the first predicate
applies. The rational-map theorem transports both predicates to chosen native
representatives, applies partial closure and uses the existing quotient
`pullsDenseOpens_toRationalMap_iff`, `toRationalMap_representative` and
`compOfPullsDenseOpens_def` interfaces; it creates no new quotient.

The domain normalization adapts Justus Springer's Apache-2.0 native
partial-composition proof; his authentic notice remains in the Lean source.
The closure proofs are original project work. The private client checks
parameterized partial and quotient maps; it does not construct exceptional
reducible, nondominant or empty examples. Closure alone adds no new category,
associativity or relative-base theorem. See [Credits](CREDITS.md).
