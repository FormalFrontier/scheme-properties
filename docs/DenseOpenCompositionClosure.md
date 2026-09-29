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

**Provenance and rights.** The domain normalization adapts Justus Springer's
Apache-2.0 native partial-composition proof in mathlib
`Mathlib/AlgebraicGeometry/Birational/Composition.lean` (in particular its
`PartialMap.comp_assoc` *domain branch*, not the theorem with its stronger
premises). The code retains Springer's copyright and author notice, and
credits Andrew Yang's native rational-map quotient, the Formal Frontier Agents'
accepted prerequisite `DenseOpenPullback`/`DenseOpenComposition` implementations
(incubator #200/#203, isolated parent `b592c13ff04fc9b8b87ef615c622f9a1e8e1ef86`),
and the implementing worker-a Hive Task
`hive-request-c948f27e37b152b7fb56b55980796bc16ccc3637`
(UID `eea5b0b3-750d-4571-bae3-e75a6715ce2b`). Distinct origin, review
and destination-transfer attribution is in [CREDITS](CREDITS.md). Neither
source-specific correspondence nor selected-source research is needed to use
these independent Lean APIs; coverage decisions remain outside this library.

The repository pins Lean `leanprover/lean4:v4.34.0-rc2` and mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, and declares exact official
`coherent-modules` and `finite-etale-algebras` GitHub dependencies. From the
Scheme Properties project root, install the toolchain, successfully fetch its
precompiled mathlib cache, then run the focused warning-fatal checks:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
LAKE_JOBS=2 lake exe cache get
LAKE_JOBS=2 lake --wfail build SchemeProperties.DenseOpenCompositionClosure SchemePropertiesTest SchemeProperties
```

The configured native CI must also supply an applicable complete actual-origin
transitive axiom audit including private and generated declarations; only `propext`,
`Classical.choice` and `Quot.sound` are allowed. The import client exercises
arbitrary partial/quotient maps, quotient representative transfer and predicates
derived from open underlying morphisms. Parameterized statements do **not**
construct special reducible, nondominant or empty examples. No new geometry,
category law, associativity or relative-base result is asserted by this module.
This guide does not certify destination acceptance, release or source coverage.
