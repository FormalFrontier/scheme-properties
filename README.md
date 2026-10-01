# Scheme Properties

Reusable Lean interfaces for local scheme properties, components, quasicoherent
modules, native rational maps and function fields. These constructions complement,
but do not replace, mathlib's scheme and native rational-map APIs.

**Authors: Formal Frontier Agents.** Original project work is
[Apache-2.0 licensed](LICENSE). [Credits](docs/CREDITS.md) distinguish adapted
formal expression and upstream notices. These source-independent results do
not by themselves claim coverage of any selected source.

## Headline results

### Generic points and birational geometry

- [Canonical generic-point function-field map](docs/GenericPointFunctionField.md):
  for integral `Y`, its total map `j : Spec Y.functionField ⟶ Y` and native
  rational quotient are dominant; the actual reversed
  `j.toRationalMap.functionFieldMap` reads back on `Spec` as the generic stalk
  map of the field spectrum and is `IsIso`, without finite-type hypotheses.
  With `[JacobsonSpace Y] [Nontrivial Y]`, `j` is not locally of finite type,
  nor is `j ≫ sY` for **any independent** `sY : Y ⟶ S`. This does not assert
  a total-scheme isomorphism or a rational inverse/noninverse theorem. Direct
  import: `SchemeProperties.GenericPointFunctionField`; its
  [client](Test/GenericPointFunctionFieldClient.lean) uses the actual
  function field of `Spec ℚ[X]`, not a literal `RatFunc ℚ` identification.
- [Jacobson birational obstruction](docs/JacobsonBirationalObstruction.md):
  a `PartialIso X Y` with `[Subsingleton X] [JacobsonSpace Y]` forces
  `Subsingleton Y`, even for empty `X`; `[Nontrivial Y]` thus rules out
  `Birational X Y`. The spectrum of `k[X]` is nontrivial for **every** field
  `k`, giving `¬ Birational (Spec K) (Spec k[X])` for arbitrary fields `K,k`
  in the same universe, including finite fields. No integrality, Noetherian,
  infinite-field or finite-type premise enters the general theorem. This
  does not prove a canonical function-field-map isomorphism or noninvertibility
  of a specified native rational arrow. Direct import:
  `SchemeProperties.JacobsonBirationalObstruction`; [one direct-import client with five private declarations](Test/JacobsonBirationalObstructionClient.lean).
- [Generic-point rational noninvertibility](docs/GenericPointRationalNoninvertibility.md):
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
- [Exact rational inverses on dense opens](docs/RationalMapPartialIso.md): two
  independently chosen dominant native quotients `X ⤏ Y` and `Y ⤏ X` on
  integral schemes satisfying **both** source-first inverse equations yield a
  partial isomorphism of dense opens whose forward and reverse quotients are
  precisely those chosen maps. For any base scheme and independently chosen
  structure maps, **one forward quotient base equation** also makes the
  partial iso literally over the base; converse dominance, inverse and both
  quotient base laws are available. No local finite type, separatedness or
  integral-base hypothesis, total-scheme isomorphism or categorical
  equivalence is asserted. Direct import:
  `SchemeProperties.RationalMapPartialIso`; [four private clients](Test/RationalMapPartialIsoClient.lean)
  check the exact readbacks and six-part converse.
### Function fields

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
### Categories and controlled composition

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
### Local properties, components and modules

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

- [Finite presentations](docs/FinitePresentations.md): finite presentations of
  sheaves of modules restrict along open immersions, and locally finitely
  presented sheaves admit finite presentations on an affine open cover; the
  cover need not be finite. See [the adapted construction](SchemeProperties/ModuleFinitePresentation.lean).
- [Components and quasicoherence](docs/Guide.md): component schemes,
  coproduct sections, geometric connectedness, quasicoherent abelian structure
  and tensors have distinct hypotheses indexed in the reader guide.

## Navigation and imports

`import SchemeProperties` loads the [aggregate](SchemeProperties.lean). For
focused imports use `SchemeProperties.<Module>` from the [reader guide's module
tables](docs/Guide.md); the [documentation index](docs/README.md) links focused
mathematical guides. Inspect direct-import [Test clients](Test/) and concrete
[Examples](Examples/) for use cases. For instance, import
`SchemeProperties.GenericPointFunctionField`,
`SchemeProperties.GenericPointRationalNoninvertibility`,
`SchemeProperties.RationalMapPartialIso` or
`SchemeProperties.ModuleFinitePresentation` directly.

[API.md](docs/API.md) and its [manifest](docs/api-manifest.json) are a **fixed
historical 73-module** native-doc snapshot, not a current declaration
census. The [API reproduction guide](docs/README.md) explains its immutable
input contract; later results are in focused guides and source files.

## Build

[Lean](lean-toolchain) is pinned to v4.34.0-rc2; mathlib and the two official
dependencies have exact revisions in [Lake](lakefile.toml) and the
[manifest](lake-manifest.json). `coherent-modules` and `finite-etale-algebras`
are **private GitHub dependencies** requiring authorized access. Install
[elan](https://github.com/leanprover/elan), fetch the matching mathlib cache
successfully for this checkout (again after changing pins or `.lake`), then
build the library, tests and examples:

```sh
lake exe cache get
lake --wfail build SchemeProperties SchemePropertiesTest SchemePropertiesExamples
```

### Historical measured cost

On September 26, 2026, a fresh **73-module** build (37 library/root, 21 Test,
15 Examples) on x86_64 Linux took 353.895 seconds *after* a matching cache
fetch of 104.624 seconds. Under a 15 GiB worker limit, sampled cgroup
current-memory peaked at 12.86 GiB (largely file cache) and sampled current
minus inactive file peaked at 1.53 GiB. This is **not** a benchmark of the
current checkout, a minimum-RAM requirement or a performance
guarantee. CPU model/quota were not recorded. The baseline excludes toolchain
installation, cloning, doc generation, axiom checks and dependency rebuilding.
