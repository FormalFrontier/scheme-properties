# Rational maps and function fields

See the [overview](../README.md), [reader guide](Guide.md) and
[documentation index](README.md) for navigation and imports. Mathematical
[references](../README.md#references) and [credits](CREDITS.md) apply throughout.

## Generic points and birational geometry

- [Compatible partial-map gluing](../SchemeProperties/PartialMapGluing.lean):
  a dense-open partial map and a morphism on any open, agreeing as scheme
  morphisms on their intersection, glue on exactly the union. Both whole-open
  restrictions characterize the glued morphism uniquely; it preserves the
  anchor's rational-map class and the structure over any common base when both
  inputs are over that base. Gluing two partial maps specializes this construction
  and recovers both partial maps and rational classes. The added open need not
  be dense; reducedness and separatedness are not required. Direct import:
  `SchemeProperties.PartialMapGluing`.
- [Canonical generic-point function-field map](GenericPointFunctionField.md):
  for integral `Y`, its total map `j : Spec Y.functionField ⟶ Y` and native
  rational quotient are dominant; the actual reversed
  `j.toRationalMap.functionFieldMap` reads back on `Spec` as the generic stalk
  map of the field spectrum and is `IsIso`, without finite-type hypotheses.
  With `[JacobsonSpace Y] [Nontrivial Y]`, `j` is not locally of finite type,
  nor is `j ≫ sY` for **any independent** `sY : Y ⟶ S`. This does not assert
  a total-scheme isomorphism or a rational inverse/noninverse theorem. Direct
  import: `SchemeProperties.GenericPointFunctionField`; its
  [client](../SchemePropertiesTest/GenericPointFunctionFieldClient.lean) uses the actual
  function field of `Spec ℚ[X]`, not a literal `RatFunc ℚ` identification.
- [Jacobson birational obstruction](JacobsonBirationalObstruction.md):
  a `PartialIso X Y` with `[Subsingleton X] [JacobsonSpace Y]` forces
  `Subsingleton Y`, even for empty `X`; `[Nontrivial Y]` thus rules out
  `Birational X Y`. The spectrum of `k[X]` is nontrivial for **every** field
  `k`, giving `¬ Birational (Spec K) (Spec k[X])` for arbitrary fields `K,k`
  in the same universe, including finite fields. No integrality, Noetherian,
  infinite-field or finite-type premise enters the general theorem. This
  does not prove a canonical function-field-map isomorphism or noninvertibility
  of a specified native rational arrow. Direct import:
  `SchemeProperties.JacobsonBirationalObstruction`; [one direct-import client with five anonymous examples](../SchemePropertiesTest/JacobsonBirationalObstructionClient.lean).
- [Generic-point rational noninvertibility](GenericPointRationalNoninvertibility.md):
  independently dominant native quotients between integral schemes cannot
  satisfy both source-first inverse laws when the source is subsingleton and
  the target is nontrivial Jacobson. For integral `Y` and any chosen
  `sY : Y ⟶ S`, the generic inclusion `g` yields a rational arrow whose
  source structure is exactly `g ≫ sY`: under the Jacobson/nontrivial
  hypotheses its actual reversed function-field map is `IsIso`, but the
  chosen-base rational arrow is not. The `Spec ℚ[X]` client has a locally
  finite-type target structure, non-locally-finite-type induced source,
  field-map isomorphism and noninvertible arrow; a `ZMod 2` client rules out
  an implicit infinite-field premise. No extra finite-type, Noetherian or
  separatedness condition, literal `RatFunc` identification, universal
  converse or category equivalence is asserted. Direct import:
  `SchemeProperties.GenericPointRationalNoninvertibility`; the earlier two
  module-specific noninverse disclaimers do not constrain this composition.
- [Exact rational inverses on dense opens](RationalMapPartialIso.md): two
  independently chosen dominant native quotients `X ⤏ Y` and `Y ⤏ X` on
  integral schemes satisfying **both** source-first inverse equations yield a
  partial isomorphism of dense opens whose forward and reverse quotients are
  precisely those chosen maps. For any base scheme and independently chosen
  structure maps, **one forward quotient base equation** also makes the
  partial iso literally over the base; converse dominance, inverse and both
  quotient base laws are available. No local finite type, separatedness or
  integral-base hypothesis, total-scheme isomorphism or categorical
  equivalence is asserted. Direct import:
  `SchemeProperties.RationalMapPartialIso`; [four private clients](../SchemePropertiesTest/RationalMapPartialIsoClient.lean)
  check the exact readbacks and six-part converse.
- [Integral birational isomorphisms](../SchemeProperties/IntegralBirationalIsomorphism.lean):
  for `{X Y : Scheme.{u}}` with `[IsIntegral X] [IsIntegral Y] [IsNormal Y]`,
  and `f : X ⟶ Y` with `[IsIntegralHom f] [IsDominant f]`, the condition
  `[IsIso f.toRationalMap.functionFieldMap]` implies `IsIso f`.
  Direct import: `SchemeProperties.IntegralBirationalIsomorphism`.
- [Valuation-stalk extension](../SchemeProperties/RationalMapValuativeExtension.lean):
  for integral `X` over an arbitrary base `S` and a relatively proper map
  `sY : Y ⟶ S`, a native partial map `p` over `S` has a chosen compatible
  representative defined at any point `x` whose stalk is a valuation ring.
  `Scheme.PartialMap.extensionOfValuationRingStalk` preserves the rational-map
  quotient and agrees with `p` as a full scheme morphism on their entire domain
  intersection. No old-domain containment, uniqueness or absolute separatedness
  of `Y` or `S` is asserted or assumed. This is the local valuative ingredient,
  not a global normal-source or codimension theorem. Direct import:
  `SchemeProperties.RationalMapValuativeExtension`.
- [Relative valuative extension](../SchemeProperties/RelativeValuativeExtension.lean):
  for a locally Noetherian source `X` over any base `S` and a relatively proper
  `sY : Y ⟶ S`, an over-base partial map extends across any point whose domain
  stalk is a valuation ring. The extension contains the point and the **whole
  original domain**, preserves its full scheme morphism and rational-map class,
  agrees on the full domain intersection, and remains over `S`. For normal `X`,
  the rational map is defined at every point of coheight at most one; if `X` has
  absolute dimension at most one, the partial map extends uniquely over `S` to
  all of `X`, using arbitrary open covers. The valuation-stalk result requires
  no global integrality or reducedness away from the point. No absolute
  separatedness of `S` or `Y`, quasi-compactness, global Noetherianity,
  nonemptiness or finite-cover hypothesis is imposed. Direct import:
  `SchemeProperties.RelativeValuativeExtension`.
## Function fields

- [Function-field naturality](../SchemeProperties/RationalFunctionFieldNaturality.lean):
  for a dominant morphism between integral same-universe schemes, pullback of
  sections on any nonempty target open commutes with the canonical maps to
  function fields. Dominance also ensures that the inverse-image open is
  nonempty. The [affine-line example](../SchemePropertiesExamples/FunctionFieldNaturality.lean)
  applies this to the structure morphism `Spec ℚ[X] → Spec ℚ`.
  Direct import: `SchemeProperties.RationalFunctionFieldNaturality`.
- [Function-field inverse criterion](RationalFunctionFieldInverse.md):
  for integral same-universe endpoints over arbitrary independently chosen
  total maps to `S`, isomorphism of the **given** dominant native quotient
  rational arrow implies isomorphism of its reversed function-field map
  **without** a local finite type premise. Reflection, and hence the iff,
  needs only local finite type of the **original source** structure map, not
  the target map or separatedness. This is not a total-scheme isomorphism or
  a supplied `PartialIso`/`BirationalOver` conversion.
- [Function-field reconstruction](RationalFunctionFieldReconstruction.md):
  for integral same-universe `X` and `Y`, arbitrary chosen `sX : X ⟶ S` and
  `sY : Y ⟶ S` with **only target `sY` locally of finite type**, a reversed
  unital map `φ : Y.functionField ⟶ X.functionField` satisfying the explicit
  generic-point geometric triangle constructs a dominant native quotient
  `X ⤏ Y`. Its composite with `sY` equals `sX.toRationalMap`, and its
  function-field map is `φ`. Conversely an independently dominant quotient
  satisfying that base equation gives the triangle **without** local finite
  type and is reconstructed when `sY` is locally of finite type. This does
  not assert unrestricted fullness, equivalence or all-representative overness.
- [Function-field pullback](RationalFunctionFieldPullback.md): dominant
  native quotient rational maps between integral schemes induce reversed
  unital maps of function fields. The native `fromFunctionField_comp` law
  assumes only first-arrow dominance (arbitrary second arrow and target);
  functorial ring-map composition additionally assumes target integrality and
  both dominances. The existing integral dominant rational-map category thus
  carries a contravariant functor to commutative rings, without a relative,
  reconstruction or faithfulness claim **within that focused pullback module**.
- [Function-field faithfulness companion](RationalFunctionFieldFaithfulness.md):
  independently dominant native quotient rational maps between integral schemes
  are equal when their function-field maps agree. The existing opposite integral
  dominant rational-map functor is faithful; that companion alone asserts no
  fullness or reconstruction.
## Categories and controlled composition

- [Integral dominant rational-map category](IntegralDominantRationalCategory.md):
  integral same-universe schemes and dominant native quotient rational maps
  form a category under native identity and composition. An actual equivalence
  identifies it with the integral-object full subcategory of the distinct
  `DenseOpenRationalScheme` rational-arrow category, preserving the quotient
  in both directions with natural unit and counit. It is not a full subcategory
  of ordinary `Scheme` or a functor to total scheme morphisms.
- [Dense-open rational-map category](DenseOpenRationalCategory.md): the
  separate category has arbitrary same-universe scheme objects and
  quotient rational-map arrows carrying `PullsDenseOpens`. Composition uses
  controlled composition and closure, while `homEquivDominant` needs **both**
  underlying schemes nonempty and preirreducible. This does not change the
  ordinary `Scheme` category or give a total-map forgetful functor.
- [Relative dense-open rational-map category](DenseOpenRationalCategoryOver.md):
  over any scheme `S`, arbitrary total structure maps `X ⟶ S` define objects;
  arrows are native quotient rational maps with `PullsDenseOpens` and the
  existential native `IsOver` witness. They form a category with a faithful
  forgetful functor to the absolute rational-arrow category. This general-relative
  module alone does not supply the integral-relative equivalence; see the separate
  integral-relative module below. Its forgetful functor is faithful, not asserted
  full, and no total-map functor is defined.
- [Integral dominant rational-map category over a base](IntegralDominantRationalCategoryOver.md):
  over any scheme `S`, the integral-object full subcategory of the relative
  dense-open rational-arrow category is equivalent to the category of integral
  schemes with chosen total maps to `S` and dominant native quotient rational
  arrows satisfying existential `IsOver`. Conversion preserves rational
  quotients; natural unit/counit and both triangle laws compare the categories.
  Forgetful functors to the absolute integral categories are faithful, not
  asserted full, with natural comparisons to inclusion and conversion.
- [Dense-open pullback and dominance](DenseOpenPullbackDominance.md):
  `PullsDenseOpens` implies dominance for native partial and quotient rational
  maps under `[Nonempty X] [PreirreducibleSpace Y]`. Under
  `[PreirreducibleSpace X] [Nonempty X] [PreirreducibleSpace Y] [Nonempty Y]`,
  both maps have a pullback–dominance iff; the dominance-to-pullback direction
  retains the earlier `[Nonempty Y]` requirement. Density is measured in
  ambient `X`, not only the partial-map domain.
- [Dense-open controlled composition](DenseOpenComposition.md) composes
  arbitrary native partial or rational maps when the first map explicitly
  pulls back every dense target open densely. Both representative changes
  preserve the quotient result; total-second and native-dominant compatibility
  recover existing `compHom` and `comp` under their respective premises. The
  [controlled over-base companion](DenseOpenCompositionOver.md) also
  preserves `IsOver S` for both maps over `S` without dominance or geometric
  hypotheses, given the first-map dense-open pullback condition.
- [Dense-open closure](DenseOpenCompositionClosure.md) proves that the
  controlled composite of arbitrary partial or rational maps pulls back
  every dense target open densely when **both** maps satisfy `PullsDenseOpens`.
  The composition operation itself still needs only the first condition;
  this closure module alone adds no associativity, category law or geometric
  assumptions.
- [Controlled associativity](DenseOpenCompositionAssociativity.md) proves
  associativity of the existing controlled composition of three arbitrary
  same-universe partial or quotient rational maps, assuming `PullsDenseOpens`
  for the first two maps only. The partial result is literal equality of
  partial maps; the rational result is equality in the existing quotient,
  not equality of arbitrary representatives' domains. No third-map predicate,
  category structure or relative-base law is asserted.
- [Controlled units](DenseOpenCompositionUnits.md) give identity predicates
  and left/right unit laws for both partial and quotient rational maps over
  arbitrary same-universe schemes. The left laws impose no predicate on the
  second map; the right laws require `PullsDenseOpens` on the first. Partial
  equality is literal (including domains and transported homs), while rational
  equality is in the quotient, not equality of arbitrary representatives.
- [Dense-open pullback](DenseOpenPullback.md) defines when a native partial or
  rational map pulls back **every** dense target open densely in the whole source.
  Equivalence and dense restriction preserve the predicate; open underlying maps
  suffice without dominance, while the separate dominant route assumes a
  preirreducible source and nonempty target.
- [Relative rational-map composition](RationalMapComposition.md) preserves
  being over a common base for a dominant first native partial/rational map and
  an arbitrary second map, assuming a preirreducible source and nonempty
  intermediate scheme; these **native-composition** lemmas retain those
  premises, unlike the separate controlled over-base companion above.
