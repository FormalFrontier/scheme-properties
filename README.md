# Scheme Properties

Reusable Lean interfaces for local scheme properties, components, quasicoherent
modules, native rational maps and function fields. These constructions complement,
but do not replace, mathlib's scheme and native rational-map APIs.

**Authors: Formal Frontier Agents.** Original project work is
[Apache-2.0 licensed](LICENSE). [Credits](docs/CREDITS.md) distinguish adapted
formal expression, original contributors, mathematical sources and upstream
notices. The [references](#references) identify the published arguments and
prior formalizations used throughout the library; the credits explain their
different roles in the Lean constructions. The group-object construction uses
the existing single-cover extension API and Mathlib's Cartesian group-object
infrastructure; Milne's Proposition 5.12 motivates its conditional presheaf form.

## Headline results

### Single-cover subfunctors

- [Single-cover extension](SchemeProperties/SingleCoverExtension.lean): in an
  arbitrary category, let `W` admit pullbacks along its morphisms and be stable
  under base change. If a subfunctor `D` of `F` is one-cover dense and `Y`
  satisfies descent for each singleton `W`-cover, restriction is an equivalence
  between natural transformations `F ⟶ Y` and `D ⟶ Y`. Neither identities nor
  composition stability in `W` nor a sheaf condition on `F` or `D` is required.
  If both ambient presheaves satisfy singleton descent, an isomorphism of two
  one-cover dense subfunctors extends uniquely to an ambient isomorphism;
  extension preserves the prescribed restrictions, identity, inverses and
  composition. Neither subfunctor needs descent.
  Direct import: `SchemeProperties.SingleCoverExtension`.
- [Change of test category](SchemeProperties/SingleCoverTransport.lean): for a
  full, essentially surjective functor `J` and a morphism class `W` respecting
  isomorphisms, a subfunctor is one-cover dense exactly when its precomposition
  is dense for `W.inverseImage J`. Reflection needs only essential surjectivity,
  not fullness; in particular density is invariant under equivalences of test
  categories. No faithfulness, sheaf condition, pullbacks, identity covers or
  composition stability is required. The witnesses use a single covering
  arrow, not a covering family. Direct import:
  `SchemeProperties.SingleCoverTransport`.
- [Group objects from one-cover-dense subfunctors](SchemeProperties/SingleCoverGroup.lean):
  if a group-valued subfunctor `D ⊆ F` is one-cover dense for a morphism class
  with relative pullbacks and stability under base change and composition, and
  the target presheaf `F` satisfies singleton-cover descent, its multiplication,
  unit and inversion extend to a group-object law on the **exact given** `F`.
  This is the unique such law making inclusion a monoid homomorphism. No ambient
  group law, descent for `D`, topology, or arbitrary finite limits on test
  objects are assumed. A proper dense `Bool` example recovers an independently
  specified group law and computes nonunit operations. This does not establish
  the corresponding represented finite-type group-scheme claim. Direct import:
  `SchemeProperties.SingleCoverGroup`.
- [Finite-type represented targets](SchemeProperties/FiniteTypeSingleCover.lean):
  over a field `K`, for finite-type `K`-schemes `X` and `Y`, maps from a one-cover
  dense subfunctor of the restricted points of `X` into those of `Y` correspond
  to `K`-morphisms `X ⟶ Y`. Tests are finitely generated `K`-algebras and
  density is witnessed by one faithfully flat algebra map. Target descent uses
  Mathlib fpqc descent and pullback comparison, not a full induced-site
  equivalence or a translation of Milne's ring-level proof. Direct import:
  `SchemeProperties.FiniteTypeSingleCover`.
- [Finite-type isomorphism extension](SchemeProperties/FiniteTypeSingleCover.lean):
  over any field, an isomorphism of two one-cover dense subfunctors of restricted
  points of finite-type schemes extends uniquely to a scheme isomorphism,
  with both prescribed restriction triangles. Neither scheme needs affineness,
  separatedness or group structure. Tests and covers are as above; no transport
  to Milne's chosen small test category is asserted.
- [Faithfully flat image density](SchemeProperties/FlatImageDensity.lean): a
  flat, surjective, locally finitely presented map of arbitrary schemes lifts
  every affine test after one faithfully flat *finitely presented* algebra
  map, with a commuting triangle. Over a field, flat surjections of locally
  finite-type schemes are one-cover dense on finitely generated algebra
  points; finite-type schemes specialize this result. Neither the schemes nor
  the morphism need be quasi-compact. The finite-type case extends Milne's
  Proposition 5.7 via Mathlib's finite affine refinement and coproduct.
  Direct import: `SchemeProperties.FlatImageDensity`.
- [Unit-power images and boundaries](SchemeProperties/PowerImage.lean): over any
  commutative base ring, including the zero ring, the image of the power map on
  units is one-cover dense for `0 < n`, using one finite-free root algebra.
  Over a field and for `2 ≤ n`, the Laurent unit lies outside this image, which
  also fails singleton descent on its root cover. The zero additive subfunctor
  is not one-cover dense over a field. These distinguish density from pointwise
  fullness and from descent for the subfunctor. Direct import:
  `SchemeProperties.PowerImage`.

### Ring-pullback spectra

- [Whole prime-spectrum pushout of a surjective ring pullback](SchemeProperties/PullbackSpectrumPushout.lean):
  for commutative rings `A → C ← B`, with only `A → C` surjective and
  `B → C` arbitrary, the whole `Spec (A ×_C B)` is the pushout of
  `Spec A ← Spec C → Spec B` as **topological spaces**, including the closed
  gluing locus and zero-ring cases. Ring carriers may live in independent
  universes. A subset of the pullback spectrum is open exactly when its
  preimages in `Spec A` and `Spec B` are open; continuous maps from these
  spectra that agree on `Spec C` descend uniquely to any target topological
  space, regardless of its universe. This does not assert a scheme pushout.
  Direct import: `SchemeProperties.PullbackSpectrumPushout`.

- [Open immersions on ring-pullback complements](docs/PullbackOpenImmersion.md):
  for arbitrary commutative-ring maps `R → T ← S`, the actual maps from
  `Spec R \ V(ker f)` and `Spec S \ V(ker g)` to the spectrum of their ring
  pullback are open immersions. Their respective ranges are the complements
  of the *opposite* projection kernels; they are disjoint and cover the
  complement of the common-map kernel. These opens may be empty; no total
  Spec-map immersion or connected-component claim follows. Direct import:
  `SchemeProperties.PullbackOpenImmersion`; the [direct-import client](Test/PullbackOpenImmersionClient.lean)
  is included.

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

## References

- Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*: Exercise
  5.3.C informs the integrality criterion; the aside to Exercise 5.4.M informs
  separable-base-change normality; Definition 6.1.1, Theorem 6.1.2 and the
  opening of §6.3 inform affine-cover quasicoherence and its abelian structure.
- J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type over
  a Field*: item 1.4/Appendix A.33 informs finite-type set-valued points;
  Propositions 1.29–1.31, the paragraph before 1.30 and Corollary 1.32(a)
  inform finite-étale components and their fibres. Appendix A.14 supplies the
  Noetherian finite/clopen-component antecedent. Definition 5.6, its following
  power-image example, Lemma 5.9 and Proposition 5.10 inform one-cover density
  and extension; Proposition 5.7 is the finite-type antecedent for flat-image
  density. Corollary 5.11 informs the isomorphism extension from two dense
  subfunctors, whose inverse laws follow from extension uniqueness. Proposition
  5.12 motivates the generic group-object extension, not a represented-scheme
  group-law theorem. Mathlib fpqc descent supplies the represented-target proof,
  while finite affine refinement supplies the flat-image lifting proof.
- Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Chapter I, §5: motivation for affine finite-presentation work.
- [The Stacks Project](https://stacks.math.columbia.edu/), tags 037U, 0386,
  0385 and 0363: a proof route from field-extension geometric connectedness
  to connected schemes over separably closed fields.
- [Mathlib](https://github.com/leanprover-community/mathlib4): reused scheme,
  rational-map, restricted-Yoneda, flat-sections, tensor, sheaf and descent
  methods, as well as adapted constructions detailed in
  [Credits](docs/CREDITS.md), with authentic upstream notices preserved.
- [Coherent Modules](https://github.com/FormalFrontier/coherent-modules) and
  [Finite Étale Algebras](https://github.com/FormalFrontier/finite-etale-algebras):
  prior formalizations used for coherent-module localization and finite-étale
  component algebras and descent.

The [credits](docs/CREDITS.md) distinguish mathematical antecedents, followed
proof patterns, imported APIs, adapted expression and original project work.
