# scheme-properties

Reusable Lean theory of scheme properties under specialization, localization,
and local-to-global criteria, with a distinct category of native rational maps
pulling back dense opens densely, its arbitrary-base relative category, and
its integral-object comparison with dominant native rational maps both
absolutely and over any chosen base scheme, and contravariant function-field
pullback along dominant native rational maps of integral schemes. A separate
faithfulness companion shows that this pullback distinguishes dominant rational
maps. A reconstruction companion builds a dominant native quotient from a
compatible reversed function-field map under local finite type on the target's
chosen base arrow. An inverse companion reflects isomorphisms of the **given**
dominant rational arrow from isomorphisms of function-field maps under local
finite type of its original source map; the reverse implication needs no
finiteness assumption.

**Authors: Formal Frontier Agents.** Original project work is licensed under
[Apache-2.0](LICENSE). Distinct contributor and reused-formal-expression credits
are in [CREDITS](docs/CREDITS.md). See the [reader guide](docs/Guide.md) for
focused imports, precise hypotheses and inspected example clients.
The [generated API reference](docs/API.md) preserves the native display
signatures for its fixed historical 73-module snapshot, not the new native
finite-presentation, rational-map-composition, dense-open-pullback,
dense-open dominance, controlled-composition, dense-open closure,
controlled associativity, controlled unit laws, controlled over-base or
dense-open rational-map category, relative dense-open rational-map category,
integral dominant rational-map category, integral relative rational-map category,
function-field pullback, faithfulness, reconstruction and inverse modules or
updated aggregate.
The later added declarations and direct imports are explained in
[Finite Presentations](docs/FinitePresentations.md),
[Relative Composition](docs/RationalMapComposition.md),
[Dense-Open Pullback](docs/DenseOpenPullback.md),
[Dense-Open Dominance](docs/DenseOpenPullbackDominance.md),
[Controlled Composition](docs/DenseOpenComposition.md),
[Dense-Open Closure](docs/DenseOpenCompositionClosure.md),
[Controlled Associativity](docs/DenseOpenCompositionAssociativity.md),
[Controlled Units](docs/DenseOpenCompositionUnits.md),
[Controlled Over-Base Companion](docs/DenseOpenCompositionOver.md), and
[Dense-Open Rational Category](docs/DenseOpenRationalCategory.md),
[Relative Dense-Open Rational Category](docs/DenseOpenRationalCategoryOver.md),
[Integral Dominant Rational Category](docs/IntegralDominantRationalCategory.md),
[Integral Dominant Rational Category Over a Base](docs/IntegralDominantRationalCategoryOver.md),
[Function-Field Pullback](docs/RationalFunctionFieldPullback.md),
[Function-Field Faithfulness](docs/RationalFunctionFieldFaithfulness.md), and
[Function-Field Reconstruction](docs/RationalFunctionFieldReconstruction.md), and
[Function-Field Inverses](docs/RationalFunctionFieldInverse.md), together with
their Lean sources.
The exact historical input contract and reproduction
instructions are in [API generation](docs/README.md).

The library's official `coherent-modules` and `finite-etale-algebras` dependencies
are pinned to **private** GitHub repositories. Users require authorized access
to fetch them; this is not a public-availability promise.

## Status

This repository is under active development. The existing 73-module base was
accepted at `ca6d6f41b169bcd57d4e5fa4429fd2203fe5e01a` and its equal-tree
official release at `6b204a3e49f022e51d78a9f93e77513b99a87e00` was verified.
The native finite-presentation modules and nine direct clients extend that
base. The relative-composition module and private direct clients are a separate
later addition. The generated reference remains a historical snapshot, with the
additions documented separately below. The dense-open pullback module and its
anonymous direct client add another native partial/rational-map interface.
The separate dense-open dominance companion and four private generic clients
relate that ambient-source predicate to native dominance under explicit
nonemptiness and preirreducibility hypotheses; origin review is distinct from
destination checks, review, acceptance, official publication and source coverage.
The controlled-composition module and its private direct clients use that
predicate to build partial- and quotient-rational-map composites.
The new dense-open closure leaf and six private direct clients establish that
both partial- and rational-map controlled composites pull back dense opens
densely when **both** factors do. This is distinct from the first-only premise
for constructing the composite. The separate associativity leaf and five
generic private direct clients give literal partial-map and quotient rational-map
associativity when the first **two** maps satisfy `PullsDenseOpens`; the third
map is arbitrary. The controlled over-base companion and five
private direct clients establish preservation of a common scheme base for those
composites under both maps'
over-base hypotheses; its destination was independently accepted and its
equal-tree official release verified. An earlier closure-transfer preparation
snapshot said that separate destination review and checks remained. By
2026-09-29 14:07:40 UTC, closure had instead reached accepted and integrated main
`dc40583057f29dda1b9d81394ba10869e2ce6ea2` and its
[verified official private-GitHub release `2f467da`](https://github.com/FormalFrontier/scheme-properties/commit/2f467da9150694b0c6366cd9125b047a7f7d76cb).
Acceptance and publication are recorded for exact
revisions; neither this descriptive status nor an unmerged feature branch
establishes them. Official releases are identified by their exact release commits.
The separate controlled-units leaf and eight private generic direct-client uses
add two identity predicates and left/right unit laws for native partial and
quotient rational maps. The September 29, 2026 transfer preparation is not
destination acceptance, integration, publication or source coverage.

**Category transfer-time history (September 29, 2026, before acceptance):**
This proposed category transfer bundles native quotient rational maps with
`PullsDenseOpens` into arrows between separately wrapped arbitrary schemes;
its ten-path destination candidate, including the new private client, still
awaits destination build/audit, independent review and maintainer acceptance.
It neither changes the ordinary `Scheme` category nor establishes publication
or source correspondence.

**Dated update, September 29, 2026, 21:58 UTC:** the category code at
`b919dd2c98fb040e491c1f4d1fc341127b47cd01` passed its destination build
and complete transitive standard-axiom audit, received independent review and
maintainer acceptance, and was integrated into development main at 21:47:36 UTC.
Its separate release/publication was still pending at this update. The
implemented category and client are available in this tree; the transfer-time
paragraph above is retained as history, not a current unmet-check claim.
Official publication is identified by the exact verified release commit,
not by a main merge or this status text. No source coverage is asserted.

**Transfer-time history, before destination acceptance:**

**Relative-category proposal, September 30, 2026:** This branch also contains
the mathematically unchanged isolated relative dense-open rational-map category
and an adapted direct-import client. The original incubator code is accepted;
destination review, applicable build/axiom checks, maintainer acceptance,
integration, release and source correspondence remain separate. See the
[relative category guide](docs/DenseOpenRationalCategoryOver.md).

**Dated destination update, September 30, 2026, 02:25:15 UTC:** the corrected
relative-category code at `855d795b76b6a63b828c54253e69a75ffb60bda8`
passed the destination build and complete transitive standard-axiom audit,
including private and generated declarations, received independent review and
maintainer acceptance, and was integrated into development main. Its separate
official release/publication was still pending at this update. The proposal
paragraph above is preserved as transfer-time history, not a current unmet-check
claim. A development-main merge does not establish official publication or
source coverage.

**Function-field transfer candidate, September 30, 2026:** the focused
[function-field pullback](docs/RationalFunctionFieldPullback.md) and nine
private direct-import checks transfer the accepted isolated incubator result
onto the integrated Scheme Properties category. Original-donor review and
proof checks do not certify this destination module. At the original
September 30, 2026 preparation before Scheme Properties PR #138's later
review, destination CI, independent review, maintainer acceptance,
integration and a distinct official release were pending; the preceding
integral-relative release had to be verified before this contribution's
public release. This is not a later current verdict: consult Scheme Properties
PR #138 and Atlas's incubator #285 for subsequent exact-revision evidence and
decisions. No source coverage or shared-incubator disposition is claimed here.

**Reconstruction transfer, September 30, 2026:** this tree adds the accepted
isolated reconstruction producer, adapted six-private-theorem client and
standalone guide. Its original independent review and focused proof evidence
do not certify this destination; native Scheme CI, fresh promotion review,
maintainer acceptance, integration and official publication are separate.
See [the reconstruction guide](docs/RationalFunctionFieldReconstruction.md).

**Dated clarification, September 30, 2026:** the reconstruction transfer's
pending-destination language above describes its preparation stage. Its
independent destination acceptance and verified official publication later
reached `5e98363b3a8738544d966d1603ace4df183573d4` (incubator #328).
That release does not certify the distinct inverse transfer below.

**Rational inverse transfer preparation, September 30, 2026:** the isolated donor
code had independent review and code-only acceptance under incubator issue #343.
At the original preparation before Scheme Properties PR #148's later review,
this destination addition's native build, complete private-inclusive transitive
axiom audit, independent transfer review, Atlas's acceptance/integration and
distinct reviewed release/publication were pending. This is a historical
preparation snapshot, not a later current verdict; consult PR #148 and Atlas's
incubator #343 for subsequent exact-revision evidence and decisions. Donor or
destination code acceptance does not itself establish official publication or
source coverage. See the
[inverse guide](docs/RationalFunctionFieldInverse.md).

## Headline results

- [Function-field inverse criterion](docs/RationalFunctionFieldInverse.md):
  for integral same-universe endpoints over arbitrary independently chosen
  total maps to `S`, isomorphism of the **given** dominant native quotient
  rational arrow implies isomorphism of its reversed function-field map
  **without** a local finite type premise. Reflection, and hence the iff,
  needs only local finite type of the **original source** structure map, not
  the target map or separatedness. This is not a total-scheme isomorphism or
  a supplied `PartialIso`/`BirationalOver` conversion.
- [Function-field reconstruction](docs/RationalFunctionFieldReconstruction.md):
  for integral same-universe `X` and `Y`, arbitrary chosen `sX : X ⟶ S` and
  `sY : Y ⟶ S` with **only target `sY` locally of finite type**, a reversed
  unital map `φ : Y.functionField ⟶ X.functionField` satisfying the explicit
  generic-point geometric triangle constructs a dominant native quotient
  `X ⤏ Y`. Its composite with `sY` equals `sX.toRationalMap`, and its
  function-field map is `φ`. Conversely an independently dominant quotient
  satisfying that base equation gives the triangle **without** local finite
  type and is reconstructed when `sY` is locally of finite type. This does
  not assert unrestricted fullness, equivalence or all-representative overness.
- [Function-field pullback](docs/RationalFunctionFieldPullback.md): dominant
  native quotient rational maps between integral schemes induce reversed
  unital maps of function fields. The native `fromFunctionField_comp` law
  assumes only first-arrow dominance (arbitrary second arrow and target);
  functorial ring-map composition additionally assumes target integrality and
  both dominances. The existing integral dominant rational-map category thus
  carries a contravariant functor to commutative rings, without a relative,
  reconstruction or faithfulness claim **within that focused pullback module**.
- [Function-field faithfulness companion](docs/RationalFunctionFieldFaithfulness.md):
  independently dominant native quotient rational maps between integral schemes
  are equal when their function-field maps agree. The existing opposite integral
  dominant rational-map functor is faithful; that companion alone asserts no
  fullness or reconstruction.
- [Integral dominant rational-map category](docs/IntegralDominantRationalCategory.md):
  integral same-universe schemes and dominant native quotient rational maps
  form a category under native identity and composition. An actual equivalence
  identifies it with the integral-object full subcategory of the distinct
  `DenseOpenRationalScheme` rational-arrow category, preserving the quotient
  in both directions with natural unit and counit. It is not a full subcategory
  of ordinary `Scheme` or a functor to total scheme morphisms.
- [Dense-open rational-map category](docs/DenseOpenRationalCategory.md): the
  separate category has arbitrary same-universe scheme objects and
  quotient rational-map arrows carrying `PullsDenseOpens`. Composition uses
  controlled composition and closure, while `homEquivDominant` needs **both**
  underlying schemes nonempty and preirreducible. This does not change the
  ordinary `Scheme` category or give a total-map forgetful functor.
- [Relative dense-open rational-map category](docs/DenseOpenRationalCategoryOver.md):
  over any scheme `S`, arbitrary total structure maps `X ⟶ S` define objects;
  arrows are native quotient rational maps with `PullsDenseOpens` and the
  existential native `IsOver` witness. They form a category with a faithful
  forgetful functor to the absolute rational-arrow category. This general-relative
  module alone does not supply the integral-relative equivalence; see the separate
  integral-relative module below. Its forgetful functor is faithful, not asserted
  full, and no total-map functor is defined.
- [Integral dominant rational-map category over a base](docs/IntegralDominantRationalCategoryOver.md):
  over any scheme `S`, the integral-object full subcategory of the relative
  dense-open rational-arrow category is equivalent to the category of integral
  schemes with chosen total maps to `S` and dominant native quotient rational
  arrows satisfying existential `IsOver`. Conversion preserves rational
  quotients; natural unit/counit and both triangle laws compare the categories.
  Forgetful functors to the absolute integral categories are faithful, not
  asserted full, with natural comparisons to inclusion and conversion.
- [Dense-open pullback and dominance](docs/DenseOpenPullbackDominance.md):
  `PullsDenseOpens` implies dominance for native partial and quotient rational
  maps under `[Nonempty X] [PreirreducibleSpace Y]`. Under
  `[PreirreducibleSpace X] [Nonempty X] [PreirreducibleSpace Y] [Nonempty Y]`,
  both maps have a pullback–dominance iff; the dominance-to-pullback direction
  retains the earlier `[Nonempty Y]` requirement. Density is measured in
  ambient `X`, not only the partial-map domain.
- [Dense-open controlled composition](docs/DenseOpenComposition.md) composes
  arbitrary native partial or rational maps when the first map explicitly
  pulls back every dense target open densely. Both representative changes
  preserve the quotient result; total-second and native-dominant compatibility
  recover existing `compHom` and `comp` under their respective premises. The
  [controlled over-base companion](docs/DenseOpenCompositionOver.md) also
  preserves `IsOver S` for both maps over `S` without dominance or geometric
  hypotheses, given the first-map dense-open pullback condition.
- [Dense-open closure](docs/DenseOpenCompositionClosure.md) proves that the
  controlled composite of arbitrary partial or rational maps pulls back
  every dense target open densely when **both** maps satisfy `PullsDenseOpens`.
  The composition operation itself still needs only the first condition;
  this closure module alone adds no associativity, category law or geometric
  assumptions.
- [Controlled associativity](docs/DenseOpenCompositionAssociativity.md) proves
  associativity of the existing controlled composition of three arbitrary
  same-universe partial or quotient rational maps, assuming `PullsDenseOpens`
  for the first two maps only. The partial result is literal equality of
  partial maps; the rational result is equality in the existing quotient,
  not equality of arbitrary representatives' domains. No third-map predicate,
  category structure or relative-base law is asserted.
- [Controlled units](docs/DenseOpenCompositionUnits.md) give identity predicates
  and left/right unit laws for both partial and quotient rational maps over
  arbitrary same-universe schemes. The left laws impose no predicate on the
  second map; the right laws require `PullsDenseOpens` on the first. Partial
  equality is literal (including domains and transported homs), while rational
  equality is in the quotient, not equality of arbitrary representatives.
- [Dense-open pullback](docs/DenseOpenPullback.md) defines when a native partial or
  rational map pulls back **every** dense target open densely in the whole source.
  Equivalence and dense restriction preserve the predicate; open underlying maps
  suffice without dominance, while the separate dominant route assumes a
  preirreducible source and nonempty target.
- [Relative rational-map composition](docs/RationalMapComposition.md) preserves
  being over a common base for a dominant first native partial/rational map and
  an arbitrary second map, assuming a preirreducible source and nonempty
  intermediate scheme; these **native-composition** lemmas retain those
  premises, unlike the separate controlled over-base companion above.
- [Normality and factoriality](SchemeProperties/FactorialNormal.lean) relates
  stalkwise factorial schemes to normal schemes; the [local-normality
  interfaces](SchemeProperties/NormalSeparableScheme.lean) also cover base
  change along transcendental-separable field extensions, not all extensions.
- [Finite-étale component schemes](SchemeProperties/ComponentScheme.lean)
  give the universal factorization through finite-étale affine targets for a
  quasicompact scheme locally of finite type over a field; the construction
  includes empty and nonreduced schemes.
- [Module tensors](SchemeProperties/ModuleTensor.lean) sheafify the tensor of
  arbitrary scheme modules, with a [principal-affine-open section
  comparison](SchemeProperties/ModuleTensorLocalization.lean), not an
  arbitrary-open sections equivalence or a global monoidal instance.

## Intended API

Direct import `SchemeProperties.RationalFunctionFieldPullback` or the aggregate
root for `AlgebraicGeometry.Scheme.RationalMap.fromFunctionField_closedPoint`,
`functionFieldMap`, `functionFieldMap_eq_of_fromFunctionField_eq`,
`fromFunctionField_comp`, `functionFieldMap_id`, `functionFieldMap_comp` and
`AlgebraicGeometry.IntegralDominantRationalScheme.functionFieldFunctor`.
The [standalone guide](docs/RationalFunctionFieldPullback.md) explains the
different first-only and two-arrow dominance premises; the
[nine private direct-import checks](Test/RationalFunctionFieldPullbackClient.lean)
do not add public theorems.

Direct import `SchemeProperties.RationalFunctionFieldFaithfulness` (or the
aggregate root) for `AlgebraicGeometry.Scheme.RationalMap.eq_of_functionFieldMap_eq`
and the anonymous `Faithful` instance on the existing
`AlgebraicGeometry.IntegralDominantRationalScheme.functionFieldFunctor`.
The [companion guide](docs/RationalFunctionFieldFaithfulness.md) and
[two private direct-import clients](Test/RationalFunctionFieldFaithfulnessClient.lean)
explain quotient equality reflection and reversed-arrow injectivity.

Direct import `SchemeProperties.RationalFunctionFieldReconstruction` (or the
aggregate root) for `AlgebraicGeometry.Scheme.RationalMap.ofFunctionFieldMap`,
`ofFunctionFieldMap_compHom`, `isDominant_ofFunctionFieldMap`, the inferred
`ofFunctionFieldMap_isDominant` instance,
`functionFieldMap_ofFunctionFieldMap`, `functionFieldMap_compatible` and
`ofFunctionFieldMap_functionFieldMap`. The [reconstruction guide](docs/RationalFunctionFieldReconstruction.md)
states their exact chosen-base triangle and target-only finite-type hypotheses;
[six private ordinary-import checks](Test/RationalFunctionFieldReconstructionClient.lean)
exercise construction, readback, compatibility and inverse laws without exporting
additional theorems. To reproduce the focused checks, first run
`lake exe cache get` in the pinned project, then
`lake build SchemeProperties.RationalFunctionFieldReconstruction` and
`lake build Test.RationalFunctionFieldReconstructionClient`.

Direct import `SchemeProperties.RationalFunctionFieldInverse` (or the
aggregate root) for
`AlgebraicGeometry.IntegralDominantRationalSchemeOver.isIso_functionFieldMap`
and `isIso_iff_isIso_functionFieldMap`. The [inverse guide](docs/RationalFunctionFieldInverse.md)
states the source-only finite-type hypothesis and categorical limitations;
[three private ordinary-import checks](Test/RationalFunctionFieldInverseClient.lean)
exercise independent chosen maps and both native quotient inverse laws.
After a successful pinned `lake exe cache get`, reproduce with
`lake build SchemeProperties.RationalFunctionFieldInverse` and
`lake build Test.RationalFunctionFieldInverseClient`. These commands are not
a claim that destination checks have passed.

Direct import `SchemeProperties.IntegralDominantRationalCategory` (or the
aggregate root) for `AlgebraicGeometry.IntegralDominantRationalScheme.of`,
`Hom`, `hom`, `hom_ext`, `toRationalMap_id` and `toRationalMap_comp`.
`IntegralDenseOpenRationalScheme` is the integral-object full subcategory of
**rational-arrow** `DenseOpenRationalScheme`; `toNative`, `toDenseOpen` and
`integralDenseOpenEquivalence` give the quotient-preserving functors and
equivalence. Both endpoints are integral. See the
[standalone guide](docs/IntegralDominantRationalCategory.md) and
[16 private direct-import uses](Test/IntegralDominantRationalCategoryClient.lean).

Direct import `SchemeProperties.DenseOpenRationalCategory` (or the aggregate
root) for `AlgebraicGeometry.DenseOpenRationalScheme.of`, `Hom`, `hom`,
`hom_ext`, `toRationalMap_id` and `toRationalMap_comp`; an anonymous category
instance supplies categorical identities, composition and laws over arbitrary
same-universe schemes. `homEquivDominant` and its projection theorem require
nonempty preirreducible **source and target**. See the
[standalone category guide](docs/DenseOpenRationalCategory.md) and
[ten private direct-import client uses](Test/DenseOpenRationalCategoryClient.lean).
This is a separate implemented category, not a new instance on `Scheme`.

Direct import `SchemeProperties.DenseOpenRationalCategoryOver` (or the aggregate
root) for `AlgebraicGeometry.DenseOpenRationalSchemeOver.of`, `Hom`, `hom`,
`isOver_iff_compHom`, `hom_ext`, quotient identity/composition projections and
the faithful `forget S` functor. Chosen structure maps are explicit, including
for three objects on the same carrier. See the
[standalone relative guide](docs/DenseOpenRationalCategoryOver.md) and
[parameterized direct-import client](Test/DenseOpenRationalCategoryOverClient.lean).

Direct import `SchemeProperties.IntegralDominantRationalCategoryOver` (or the
aggregate root) for `AlgebraicGeometry.IntegralDenseOpenRationalSchemeOver S`,
`IntegralDominantRationalSchemeOver S`, the quotient-preserving `toNative` and
`toDenseOpen` functors, and `integralDenseOpenEquivalenceOver S`. The base `S`
need not be integral; chosen object maps and existential over-base witnesses
remain explicit. See the [standalone integral-relative guide](docs/IntegralDominantRationalCategoryOver.md)
and [private direct-import client](Test/IntegralDominantRationalCategoryOverClient.lean).

The native finite-presentation additions are available by direct imports
`SchemeProperties.SheafFinitePresentationTransport` and
`SchemeProperties.ModuleFinitePresentation`, or through the aggregate
`SchemeProperties`. See the [standalone guide](docs/FinitePresentations.md) for the
five declarations, assumptions, zero-ring/empty-index clients and limitations.

The native relative-composition lemmas are available by direct import
`SchemeProperties.RationalMapComposition` or through `SchemeProperties`:
`AlgebraicGeometry.Scheme.PartialMap.isOver_comp_of_isDominant_first` and
`AlgebraicGeometry.Scheme.RationalMap.isOver_comp_of_isDominant_first` show that
composition over a common base preserves the base for a dominant first map and
an arbitrary second map. See the [standalone guide](docs/RationalMapComposition.md)
for the precise hypotheses, proof route and ordinary-import clients.

The native dense-open pullback predicate is available from direct import
`SchemeProperties.DenseOpenPullback` or the aggregate root. For arbitrary
same-universe schemes `X` and `Y`, it asks whether the inverse image of
**every** dense open of `Y` under a native partial map has dense image in
ambient `X`, not just in its dense domain. It is invariant under equivalent
representatives and dense restriction, and has `toRationalMap` and chosen-
representative equivalences. An open underlying map suffices without dominance;
the separate dominant route assumes `[PreirreducibleSpace X] [Nonempty Y]`
and `[IsDominant f.hom]`. See the [standalone guide](docs/DenseOpenPullback.md)
and [seven anonymous direct-import examples](Test/DenseOpenPullbackClient.lean).
Direct import `SchemeProperties.DenseOpenPullbackDominance` (or the aggregate
root) for the partial/rational-map `isDominant_of_pullsDenseOpens` under
`[Nonempty X] [PreirreducibleSpace Y]` and `pullsDenseOpens_iff_isDominant`
under all four nonempty/preirreducible source/target hypotheses. See the
[dominance guide](docs/DenseOpenPullbackDominance.md) and
[four private direct-import examples](Test/DenseOpenPullbackDominanceClient.lean).
The pullback predicate module alone does not define composition; the separate
controlled-composition module does, without claiming category laws.

Direct import `SchemeProperties.DenseOpenComposition` or the aggregate root to
use `PartialMap.compOfPullsDenseOpens` and `RationalMap.compOfPullsDenseOpens`.
Given an explicit first-map `PullsDenseOpens` proof, they compose arbitrary
same-universe native partial/quotient rational maps without dominance or
irreducibility. See the [focused guide](docs/DenseOpenComposition.md) and
[eleven private direct-import clients](Test/DenseOpenCompositionClient.lean)
for both representative bridges and native/total-second compatibilities.
Direct import `SchemeProperties.DenseOpenCompositionClosure` (or the aggregate
root) for `PartialMap.pullsDenseOpens_compOfPullsDenseOpens` and
`RationalMap.pullsDenseOpens_compOfPullsDenseOpens`: each takes both `hf` and
`hg` to prove that the controlled composite satisfies `PullsDenseOpens`.
See the [closure guide](docs/DenseOpenCompositionClosure.md) and
[six private generic clients](Test/DenseOpenCompositionClosureClient.lean).
Direct import `SchemeProperties.DenseOpenCompositionAssociativity` (or the
aggregate root) for `PartialMap.compOfPullsDenseOpens_assoc` and
`RationalMap.compOfPullsDenseOpens_assoc`. Both require the first two factors'
`PullsDenseOpens` proofs, use the closure witness for left-bracketed
composition and leave the third map unrestricted. See the
[associativity guide](docs/DenseOpenCompositionAssociativity.md) and
[five generic private uses](Test/DenseOpenCompositionAssociativityClient.lean),
including one private definition; these are not constructed exceptional examples.
Direct import `SchemeProperties.DenseOpenCompositionUnits` (or the aggregate
root) for `PartialMap.pullsDenseOpens_id`, `RationalMap.pullsDenseOpens_id`,
and their respective `id_compOfPullsDenseOpens` and
`compOfPullsDenseOpens_id` laws. The left laws need no predicate on the second
map, while right units need the first-map predicate; both identity predicates
measure density in ambient `X`. See the [unit guide](docs/DenseOpenCompositionUnits.md)
and [eight private direct-client uses](Test/DenseOpenCompositionUnitsClient.lean).
The [controlled over-base companion](docs/DenseOpenCompositionOver.md), by
direct import `SchemeProperties.DenseOpenCompositionOver` or through the root,
adds `PartialMap.isOver_compOfPullsDenseOpens` and
`RationalMap.isOver_compOfPullsDenseOpens` for maps `f : X ⤏ Y` or partial
maps and `g : Y ⤏ Z` or partial maps, all schemes over the same `S`. Both
need `hf : f.PullsDenseOpens` and `[f.IsOver S] [g.IsOver S]`, but no
second-map predicate, dominance, nonemptiness or preirreducibility. Its
[five private direct-import clients](Test/DenseOpenCompositionOverClient.lean)
do not establish concrete nondominant examples. The original operation and
over-base modules alone do not assert predicate closure (the new closure leaf
does), category structure or that arbitrary quotient
representatives are globally over `S`.

The first unit packages three facts:

- `IsLocalization.isReduced` allows source and localization rings in independent
  universes;
- `IsLocalization.AtPrime.isReduced_of_le` passes reducedness between two prime
  localizations in the direction induced by inclusion of the primes; and
- `AlgebraicGeometry.isReduced_stalk_of_specializes` preserves reducedness of
  scheme stalks under generalization.

The API is source-independent and makes no compactness, Noetherianity,
finite-type, separation, field, or nonemptiness assumption.

The second unit proves that domain stalks make irreducible components locally
disjoint, and packages the resulting criterion that a connected locally
Noetherian scheme with domain stalks is integral. The exact Noetherian form is
also exposed for source-facing clients.

The third unit defines a normal scheme by requiring every stalk to be an
integrally closed domain. It proves localization and generalization lemmas,
normality of spectra of locally normal rings, the equivalence between affine-
spectrum normality and local normality of the coordinate ring, preservation
under open immersions and scheme isomorphisms, an open-cover criterion, and
that normal schemes are reduced. The local ring interface permits disconnected
rings, is preserved by ring equivalences, and specializes automatically from
integrally closed domains. Arbitrary localizations preserve this local
normality, including for disconnected bases. Polynomial rings and
finite-variable multivariate polynomial rings also preserve local normality
without a global domain hypothesis on the base. Finite etale algebras preserve
local normality as well, with independently varying base and target universes.
Flat directed unions of locally normal subrings are locally normal. Consequently,
tensoring a locally normal algebra with a transcendental-separable field
extension preserves local normality, including for disconnected algebras.
Consequently, normal schemes remain normal after base change along such field
extensions.

The fourth unit packages every locally connected scheme as the coproduct of
its open connected-component subschemes. It also provides the corresponding
summand compatibility and the componentwise map from a scheme into a coproduct
of copies of a target. The construction permits empty schemes and infinitely
many components.

The fifth unit proves that Noetherian spaces are locally connected and applies
this to Noetherian schemes. Their connected-component index is finite; each
component open subscheme is connected and Noetherian; the components form an
open cover on which normality can be checked; and the components of a normal
Noetherian scheme are integral. The unit reuses the general coproduct
isomorphism from the fourth unit.

The sixth unit defines a factorial scheme by unique factorization in every
stalk. It proves localization and generalization lemmas, factoriality of spectra
of unique factorization domains and Dedekind domains, preservation under open
immersions and scheme isomorphisms, and an open-cover criterion. The Dedekind
result applies even when the original domain is not a unique factorization
domain, since all of its local rings are principal ideal domains.

The seventh unit proves that every factorial scheme is normal by combining the
factorial stalk instances with the existing integrally-closed theorem for GCD
domains. It adds no competing ring-theoretic definition or UFD theorem.

The eighth unit connects the scheme-facing restriction API for modules with
the over-site API used in the definition of quasicoherence. It proves that, on
any fixed affine open cover, a module is quasicoherent if and only if every
restricted module is recovered by the affine `fromTildeΓ` map after transport
along the canonical spectrum isomorphism. Arbitrary covers, empty schemes and
zero modules are supported without finiteness, nonemptiness, Noetherian,
reduced, integral, finite-type, separation or field assumptions.

The ninth unit characterizes torsion modules over **any commutative ring** by
vanishing after base change to a localization at its non-zero-divisors, including
the canonical total quotient ring. It defines stalkwise
torsion-freeness and vanishing at component generic points for arbitrary
modules on schemes, with isomorphism invariance, empty-scheme and zero-module
instances, and equivalent irreducible-component indexing. For modules on an
integral affine spectrum produced by `tilde`, generic vanishing is equivalent
both to torsion and to zero fraction-ring base change. This last equivalence
requires an integral affine base, unlike the general commutative-ring torsion
theorem; the stalkwise predicates themselves do not require quasicoherence,
reducedness, finiteness or nonemptiness.

The tenth unit proves that the tensor product of arbitrary extension fields of
a separably closed field has connected prime spectrum, including over
imperfect bases and for transcendental extensions. Consequently every
connected scheme over a separably closed field is geometrically connected,
without finite-type, reducedness, irreducibility, separation, properness,
algebraicity or rational-point hypotheses. The scheme API currently follows
mathlib's same-universe boundary.

The eleventh unit proves the module-valued qcqs lemma. For a quasicoherent
module and a section on any compact quasiseparated open, restriction of module
sections to the associated basic open is localization away from that section;
a global-sections specialization is also provided. The result supports empty
schemes and opens, zero modules, and the sections `0` and `1`, without
Noetherianity, reducedness, affineness, nonemptiness, separation, or finiteness
assumptions beyond compactness and quasiseparatedness of the chosen open.

The twelfth unit identifies the global sections of a quasicompact,
quasiseparated scheme after extending its base field from `k` to `K` with
`K ⊗[k] Γ(X, ⊤)`. The canonical `K`-algebra equivalence includes formulas
for both tensor-product generators and arbitrary pure tensors, agrees with the
tensor left unitor for the identity extension, and is compatible with direct
and successive extensions through its canonical pullback isomorphism. It
supports empty schemes, zero global rings, and infinite field extensions,
without assuming that the scheme is affine, separated, reduced, connected, or
nonempty. The scheme API currently follows mathlib's same-universe boundary.

The thirteenth unit proves that the native full subcategory of quasicoherent
modules on an arbitrary scheme is abelian. It establishes closure under zero,
finite products, kernels, and cokernels by proving finite-limit preservation for
the affine `tilde` functor and for restriction along open immersions, then gluing
over affine opens. No Noetherianity, separation, qcqs, nonemptiness, cover
finiteness, or module finiteness assumption is used.

The fourteenth unit connects native quasicoherent module sections with
`Module.IsCoherent`. On any compact quasiseparated open, coherence of the
section module is preserved on a principal open, and it descends from an
arbitrary set-indexed family of principal opens whose defining sections span
the unit ideal. The statements retain the principal-open structure ring and
its scalar tower explicitly, allow zero sections, zero modules, zero rings and
an empty spanning set when its span is top, and impose no artificial
nonemptiness or finiteness condition. On an affine spectrum in the same
universe, the unit also exposes the inverse image of `ModuleCat.isCoherent`
under the native `tildeEquiv.inverse`, with literal membership and `tilde`
bridge lemmas. This unit uses the exact one-way dependency on
`coherent-modules` pinned in `lakefile.toml`; `coherent-modules` remains
independent of this repository.

The fifteenth unit constructs the finite-etale component scheme of a
quasi-compact scheme locally of finite type over a field. It selects the
greatest finite-etale subalgebra of global sections, proves that the canonical
map to its spectrum is surjective, and gives the exact universal factorization
through every finite-etale affine target. The construction supports empty
schemes, zero global rings, disconnected schemes, and nonreduced schemes, and
does not assume separatedness, reducedness, connectedness, or nonemptiness.
This unit uses the exact one-way dependency on `finite-etale-algebras` pinned in
`lakefile.toml`; `finite-etale-algebras` remains independent of this repository.

The sixteenth unit proves that the component scheme commutes canonically with
every same-universe field extension. It supplies the comparison on coordinate
algebras, the corresponding comparison of schemes and compatibility triangle,
literal equality of the scalar-extended and newly selected component
subalgebras, and the resulting algebra equivalence and categorical isomorphism.
It applies to identity, separable, purely inseparable, transcendental, and
mixed extensions, including disconnected, nonreduced, and empty sources, with
no algebraicity, finite-dimensionality, separability, perfectness,
connectedness, reducedness, nonemptiness, or separatedness hypothesis.

The seventeenth unit identifies each scheme-theoretic residue-field fibre of
the component map with its connected component on underlying points and proves
that the fibre is geometrically connected. Equivalently, the fibre's greatest
finite-etale subalgebra of global sections is exactly the scalar subalgebra.
It supports disconnected, nonreduced and empty sources and arbitrary residue
fields without separatedness, reducedness, connectedness, nonemptiness,
algebraic-closure, separability or perfectness assumptions. The scheme API
retains the existing same-universe boundary.

The eighteenth unit identifies sections on an arbitrary open of a
same-universe indexed coproduct of schemes with the dependent product of the
sections on its component preimages. Its forward map is literally pullback to
each coproduct summand, and its coordinate formula commutes with restriction,
including restriction to basic opens through the existing
`Scheme.preimage_basicOpen` API. It imposes no finiteness, nonemptiness,
affineness, separation, compactness, or Noetherian hypothesis.

The nineteenth unit proves that a same-universe indexed coproduct of
quasiseparated schemes is quasiseparated, including empty families and empty
components. It also proves that such a coproduct is not compact when the index
type is infinite and every component is nonempty. The quasiseparated instance
adds no compactness, nonemptiness, Noetherianity, separation, reducedness,
affineness, or finiteness assumption.

The twentieth unit, available from `import SchemeProperties.StructureSheaf`,
proves `AlgebraicGeometry.Scheme.Modules.unit_isQuasicoherent`: the structure
sheaf is quasicoherent as a module over itself on every scheme, including the
empty scheme, with no finiteness or separation assumptions.

The twenty-first unit packages every `Scheme.IdealSheafData` as the sectionwise
kernel submodule of its canonical quotient map. It identifies affine sections
with the specified ideals, proves basic-open localization and quasicoherence,
and exposes the nilradical through thin module and subobject clients. The
construction supports zero rings and empty schemes and opens without additional
nonemptiness, finiteness, separation, compactness, or reducedness assumptions.

A further unit constructs the ambient tensor product of arbitrary modules on a
scheme by sheafifying their pointwise presheaf tensor. It provides a bifunctor,
the sheafification unit, pure tensor sections with additive, scalar and
restriction laws, the exact all-target sheafification Hom equivalence, and a
natural pure-compatible symmetry. It supports zero modules, zero rings, empty
schemes and empty opens, without quasicoherence, finiteness, nonemptiness,
compactness or separation assumptions. It adds no monoidal-category instance on
the category of scheme modules.

Restriction along an open immersion commutes with this ambient tensor via
`Scheme.Modules.restrictTensorNatIso`, naturally in both module arguments.
`restrictTensorNatIso_inv_app_tmul` gives the explicit pure-tensor formula
through the native restriction/scalar identifications. The comparison uses
actual sheafification and supports arbitrary modules, zero rings, empty schemes
and empty opens; it does not assume quasicoherence or introduce a global
monoidal instance. It is available directly from
`import SchemeProperties.ModuleTensorRestriction` or the aggregate root.

Taking stalks commutes with the pointwise tensor of presheaves of modules over
a commutative-ring presheaf: `PresheafOfModulesOfCommRing.stalkTensorEquiv` uses
the native ring-stalk module structures, identifies germs of pure tensors, and
is natural in both module arguments. The linear stalk map
`stalkMapLinear` and its germ formula are also available directly from
`import SchemeProperties.PresheafModuleTensorStalk`, without scheme imports or
a sheaf assumption.

For any commutative ring `R`, `Scheme.Modules.affineTensorNatIso` identifies
the existing sheafified tensor of associated modules on `Spec R` with the
associated module of their algebraic tensor product, naturally in both inputs.
`affineTensorNatIso_inv_app_top_tmul` gives its inverse component on top-open
pure-tensor sections. No quasicoherence, finiteness or nonemptiness assumption
is required; zero rings and modules are included. Import
`SchemeProperties.ModuleTensorAffine` directly or use the aggregate root.

On a principal open `D(f)` of `Spec R`,
`Scheme.Modules.basicTensorEquiv` identifies the tensor of associated-module
sections over the *native* ring `Γ(Spec R, D(f))` with sections of their
sheafified tensor. Its forward map is the actual `tensorUnit` component, and
`basicTensorEquiv_tmul` records its pure-tensor law. The native localization
`locTensor` sends `m ⊗ n` to the tensor of their basic-open sections;
`actual_restriction_square` identifies the inverse tensor-unit map after
restriction from the top open with this localization after
`topTensorEquiv`. Every inclusion of principal opens respects the comparison,
semilinearly along the actual structure-sheaf restriction, and the map is
natural in both modules. `awayTensorEquiv` transports it to the native
`Localization.Away f` presentation, with `awayLocTensor` built independently
from native localization maps. There are no nonzero, regularity, finiteness or
nonemptiness assumptions, including when `f = 0` or the ring is zero. This
does **not** assert a tensor-of-sections equivalence on arbitrary opens.
Import `SchemeProperties.ModuleTensorLocalization` or the aggregate root.

`import SchemeProperties.SheafFinitePresentation` provides the site-generic
`SheafOfModules.LocalGeneratorsData.isFinitePresentation_of_isLocallyFreeData`:
for one local-generator datum with both a local basis and finite generators on
each chart, the underlying sheaf of modules is finitely presented in mathlib's
native sense. The cover need not be finite and basis sizes may vary, including
zero; the theorem assumes the native sheafification conditions on each over-site
and does not infer compatibility of two independently chosen local covers.
It depends only on mathlib and is also available from the aggregate root.

Downstream projects should import the aggregate root:

```lean
import SchemeProperties
```

## Reproduction

Install [elan](https://github.com/leanprover/elan) and use the pinned Lean
v4.34.0-rc2 toolchain, mathlib `83abb3e776bdefcbc447a1e44d0debe4010039e5`
and exact official private `coherent-modules` / `finite-etale-algebras` revisions
in `lakefile.toml` and `lake-manifest.json`. Once dependency access is available,
fetch the matching precompiled mathlib cache before every build in a new
checkout or after changing pins, then build the default library, all shipped
`Examples` and `Test` targets:

```sh
lake exe cache get
lake --wfail build SchemeProperties SchemePropertiesTest SchemePropertiesExamples
```

The native-documentation source build used these three targets, with verbose
traces, on source `a05b182aa17ea7cd1a591ec7b60aa7d6f2b6704c` and the exact
official pins now bound in [api-manifest.json](docs/api-manifest.json).
Cached ProofWidgets tasks replayed npm warnings and vulnerability/circular-
dependency notices; these were retained, not treated as a fresh security audit
or repaired by changing dependencies. Neither a successful build nor example
compilation alone checks every declaration's axioms or establishes mathematical
source coverage. See [API generation](docs/README.md) for the distinct data-only
adapter and native generation procedures.

### Expected build cost

A September 26, 2026 baseline on x86_64 Linux with the pinned Lean
v4.34.0-rc2 and dependency revisions measured 104.624 seconds for the matching
mathlib-cache step, followed by 353.895 seconds for a fresh default build of all
73 shipped modules: 37 library/root modules, 21 `Test` modules and 15 `Examples`
modules. Thus, allow roughly six minutes for this source build plus about two
minutes for that cache step on a comparable environment. Unchanged dependencies
came from the matching cache; these are not cache-free dependency-rebuild timings.

That run used a 15 GiB worker memory limit. Its build-specific sampled cgroup
current-memory peak was 12.86 GiB, largely file cache; the sampled
current-minus-inactive-file peak was 1.53 GiB. Neither quantity establishes a
minimum RAM requirement. CPU model/quota were not recorded, and timings depend
on CPU availability, storage, network and cache state. The baseline excludes
toolchain installation, cloning, API documentation generation, separate
proof/axiom checks and downstream workloads; it is an initial measured baseline,
not a performance guarantee or a claimed speedup.
