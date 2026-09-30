# Integral dominant rational maps over a fixed base

Directly import `SchemeProperties.IntegralDominantRationalCategoryOver` (or
`SchemeProperties`) to use the following `AlgebraicGeometry` APIs for **any**
`S : Scheme.{u}`, including nonintegral bases. This relative equivalence is
distinct from the [absolute integral equivalence](IntegralDominantRationalCategory.md)
and the [general relative rational-arrow category](DenseOpenRationalCategoryOver.md).

| API | Meaning |
| --- | --- |
| `IntegralDenseOpenRationalSchemeOver S` | The actual `ObjectProperty.FullSubcategory` of `DenseOpenRationalSchemeOver S` with `IsIntegral X.toScheme`. |
| `IntegralDominantRationalSchemeOver S` | Integral scheme objects with arbitrary chosen total maps `X ⟶ S`; arrows are dominant native quotient rational maps carrying existential `IsOver S` witnesses for those choices. |
| `IntegralDenseOpenRationalSchemeOver.toNative` | A quotient-preserving functor from controlled integral relative arrows to dominant native relative arrows. |
| `IntegralDominantRationalSchemeOver.toDenseOpen` | The converse quotient-preserving functor from dominant native to controlled integral relative arrows. |
| `integralDenseOpenEquivalenceOver S` | The bundled equivalence with natural unit and counit and triangle laws. |
| `IntegralDenseOpenRationalSchemeOver.forget`, `IntegralDominantRationalSchemeOver.forget` | Faithful functors to the respective **absolute integral** categories; neither is asserted full. |
| `IntegralDenseOpenRationalSchemeOver.forgetInclusionIso` | Natural comparison between relative full-subcategory inclusion followed by absolute forgetting and the opposite route. |
| `IntegralDenseOpenRationalSchemeOver.forgetNativeIso` | Natural comparison between relative and absolute forward conversion after forgetting. |
| `IntegralDominantRationalSchemeOver.forgetDenseOpenIso` | Natural comparison between relative and absolute backward conversion after forgetting. |

Use `IntegralDenseOpenRationalSchemeOver.of p` or
`IntegralDominantRationalSchemeOver.of p` for an integral `X` and an arbitrary
total `p : X ⟶ S`. The native `hom r hr hS` takes a quotient rational map
`r : X ⤏ Y`, its dominance `hr : r.IsDominant` and the native **existential**
over-base condition
`hS : @Scheme.RationalMap.IsOver _ _ S (.ofHom X.toBase) (.ofHom Y.toBase) r`.
The arrow projections `toRationalMap`, `dominant` and `isOver` retain them.
`IntegralDominantRationalSchemeOver.isOver_iff_compHom` identifies this
condition with `r.compHom Y.toBase = X.toBase.toRationalMap`; it does not
require an arbitrary selected representative to be over `S` on its entire
domain. Source, middle and target chosen structure maps stay distinct, even
when their underlying scheme carriers coincide.

Native `toRationalMap_id` and `toRationalMap_comp` expose identity and **native**
`RationalMap.comp`. Controlled integral `toRationalMap_comp` projects to native
composition through the controlled/native comparison. `nativeHom` and
`denseHom` preserve quotient arrows in both directions, with inverse hom
roundtrips. `nativeUnitIso` and `nativeCounitIso` are natural comparisons,
not just inverse maps on homs; their components agree with the absolute
comparisons after forgetting the chosen base maps. The three named forgetting
isos likewise compare **identity-quotient** arrows, not total scheme maps.

```lean
import SchemeProperties.IntegralDominantRationalCategoryOver

open AlgebraicGeometry CategoryTheory

example {S : Scheme} {X Y Z : IntegralDominantRationalSchemeOver S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toRationalMap = f.toRationalMap.comp g.toRationalMap :=
  IntegralDominantRationalSchemeOver.toRationalMap_comp f g
```

Integrality of both endpoints provides the nonemptiness and
preirreducibility needed to relate `PullsDenseOpens` to native dominance.
Native composition needs the first arrow's dominance; closure needs both.
Relative preservation also uses both over-base witnesses and all three chosen
structure maps. No integrality, dominance or other geometric assumption is
placed on `S` or its structure maps. The
[direct-import private client](../Test/IntegralDominantRationalCategoryOverClient.lean)
checks constructors, representatives, category and functor laws, naturality,
triangles, equal-carrier chosen-map behavior and the absolute comparisons.
It is in the `SchemePropertiesTest` target, not part of this public module.

The producer and client are under
[`SchemeProperties/IntegralDominantRationalCategoryOver.lean`](../SchemeProperties/IntegralDominantRationalCategoryOver.lean)
and the client path above. The pinned Lean toolchain is
`leanprover/lean4:v4.34.0-rc2`, with mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and official
`coherent-modules` `fc30df937c7476f1c01f7cb39005f8cae37f8f34`
and `finite-etale-algebras` `79575f65c9edec560f27756917761eed78331a2a`
GitHub dependencies in the [exact manifest](../lake-manifest.json). The
latter two repositories require authorized private GitHub access. To reproduce
the focused verification in this project's pinned environment, fetch the
matching precompiled mathlib cache **before** any build:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
LAKE_JOBS=2 lake --wfail build SchemeProperties.IntegralDominantRationalCategoryOver SchemePropertiesTest
```

The configured repository checks also cover the aggregate, examples and
transitive axiom dependencies, including private declarations. These
reproduction commands are not a claim of a successful destination build,
independent destination review or release; those require separate exact-input
evidence. No total-map functor, fullness of forgetting, dominant structure
maps, categorical slice, unrestricted reduced-source composition, base-change
or source-formalization result is asserted. Original contributors, reviewed
expression and imported mathlib interfaces are distinguished in
[Credits](CREDITS.md); no book text or third-party proof bodies are copied.
