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

### Going down and flat stalk dimensions

- [Going down](SchemeProperties/RingTheory/KrullDimension/GoingDown.lean) bounds
  the height of the contraction of **any** ideal by its height, including infinite
  heights. A generalizing local ring map with local target bounds the source
  dimension by the target dimension; flat local maps specialize this result.
- [Flat stalk dimensions](SchemeProperties/FlatStalkDimension.lean): at any point
  where the canonical stalk map is flat, the full target-stalk dimension is at
  most the source-stalk dimension. Flat scheme morphisms satisfy this everywhere.
  Neither bound requires Noetherianity or finite dimension.

### Affine test objects

- [Affine schemes separate morphisms](SchemeProperties/AffineTestObjects.lean):
  affine schemes form a separating family in Mathlib's `ObjectProperty` API.
  For arbitrary `f : X ⟶ Y` in `Scheme.{u}`, `Mono f` is equivalent to
  injectivity of `g ↦ g ≫ f` on `Spec (CommRingCat.of R) ⟶ X` for every
  commutative ring `R : Type u`. No reducedness, finite-type, quasi-compactness
  or separatedness hypothesis is needed; zero rings and empty schemes are
  included. This is a monomorphism criterion, not an isomorphism criterion,
  and field-valued points alone do not suffice. The
  [line-in-plane example](SchemePropertiesTest/AffineTestObjects.lean) has
  two distinct rational source points with distinct images.
  Direct import: `SchemeProperties.AffineTestObjects`.

### Affine tests for isomorphisms

- [Affine generators](SchemeProperties/AffineGenerators.lean): affine schemes form
  a strong generator of `Scheme.{u}` and detect isomorphisms. For arbitrary
  `f : X ⟶ Y`, `IsIso f` is equivalent to bijectivity of `g ↦ g ≫ f` on maps
  `Spec R ⟶ X` for **every** commutative ring `R : Type u`, including the zero
  ring. No finiteness, separatedness or monomorphism premise is required.
  Direct import: `SchemeProperties.AffineGenerators`; the
  [affine-line examples](SchemePropertiesTest/AffineGenerators.lean) contrast
  the identity with the zero section, which misses the rational point at one.

### Affine density

- [Affine density](SchemeProperties/AffineDensity.lean) shows that
  `Scheme.Spec : CommRingCat.{u}ᵒᵖ ⥤ Scheme.{u}` is cover-dense for the big
  Zariski topology and dense among all schemes in that universe. All commutative
  rings, including the zero ring, are tests; empty and nonreduced schemes are included.
  No field, finite-type, separatedness or small-test-category hypothesis is imposed.
  Full faithfulness and reconstruction for the existing
  `Presheaf.restrictedULiftYoneda.{0} Scheme.Spec` are supplied by Mathlib from
  density, not by a new points functor or separate theorem here.
  Its values are `ULift.{0} (Spec R ⟶ X) : Type u`; natural-transformation Homs
  lie in `Type (u + 1)`. See the [API note](docs/API.md#affine-density)
  and [affine reconstruction example](SchemePropertiesTest/AffineDensity.lean).
  Direct import: `SchemeProperties.AffineDensity`.

### Finitely generated algebras

- [Universe lifting](SchemeProperties/FiniteTypeUniverseLift.lean): for a
  commutative ring `R : Type u` with `[Small.{v} R]`, Mathlib's existing
  `FGAlgCat.uliftFunctor R : FGAlgCat.{v} R ⥤ FGAlgCat.{max v w} R` is an
  equivalence, with independent universes `u`, `v` and `w`. Zero algebras are
  included; no global universe-order assumption is needed. This compares
  the categories of finitely generated algebras themselves, not a chosen
  presentation category. Direct import: `SchemeProperties.FiniteTypeUniverseLift`.

### Morphisms from reduced schemes

- [Reduced-source extensionality](SchemeProperties/ReducedHomExt.lean): for
  morphisms `f g : X ⟶ Y` with reduced source, agreement after every canonical
  residue-field map implies `f = g`
  (`Scheme.Hom.ext_of_fromSpecResidueField`). Equivalently, it suffices to agree
  after **all** field-valued points (`Scheme.Hom.ext_of_field_valued_points`),
  with fields in the common scheme universe. The target is arbitrary: no
  separatedness, finite-type or Noetherian hypothesis is imposed. Empty sources
  are allowed. These tests compare scheme morphisms, not just maps of points.
  Direct import: `SchemeProperties.ReducedHomExt`; see the
  [affine-line application](SchemePropertiesTest/ReducedHomExt.lean).

### Sections and dense closed-point tests

For any field `K : Type u`, any scheme `Y : Scheme.{u}`, and morphisms
`f g : Spec ↧K ⟶ Y`, the section criterion
[`Scheme.Hom.ext_of_apply_closedPoint_eq_of_comp_eq_id`](SchemeProperties/RationalPointExtensionality.lean)
uses a specified `i : Y ⟶ Spec ↧K`, both identities `f ≫ i = 𝟙 _` and
`g ≫ i = 𝟙 _`, and agreement at `IsLocalRing.closedPoint K` to conclude
`f = g` as scheme morphisms. Neither algebraic closedness of `K` nor separatedness,
finite type or reducedness of `Y`, nor a monomorphism hypothesis on `i`, is needed.
The section identities control the residue-field embeddings, not just the image points; see
Mathlib's [residue-field classification](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/AlgebraicGeometry/ResidueField.lean).
The [coordinate-section application](SchemePropertiesTest/RationalPointExtensionality.lean)
uses independently constructed sections of the affine line over `ℚ` to recover
equality of their rational parameters from agreement of their image points.

For schemes `X Y : Scheme.{u}` over an algebraically closed field `K : Type u`,
[`Scheme.Hom.ext_of_apply_eq_on_dense_closedPoints`](SchemeProperties/RationalPointExtensionality.lean)
compares `f g : X ⟶ Y` with a specified separated morphism `i : Y ⟶ Spec ↧K`.
It assumes `X` is reduced, `f ≫ i` is locally of finite type, a subset `S : Set X`
is dense and locally closed, `f x = g x` for each `x ∈ S` whose singleton is closed,
and the base compatibility `f ≫ i = g ≫ i`; it concludes `f = g`.
There is no locally finite type assumption on `i`. This generalizes Mathlib's
[closed-point criterion](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/AlgebraicGeometry/AlgClosed/Basic.lean).
The [affine-line application](SchemePropertiesTest/RationalPointExtensionality.lean)
uses closed-point sections to determine the coordinate pullback of endomorphisms
compatible with the structure map. Direct import for both criteria:
`SchemeProperties.RationalPointExtensionality`.

### Geometric-point lifting

- [Surjectivity and geometric points](SchemeProperties/GeometricPointLifting.lean):
  a locally finite type morphism `f : X ⟶ Y` is surjective exactly when,
  for every algebraically closed field `K` in the schemes' common universe and
  every `p : Spec K ⟶ Y`, there is `q : Spec K ⟶ X` with `q ≫ f = p`.
  The lift uses the same `K`, without a field extension; the implication from
  lifting to surjectivity does not require local finite type.
  Direct import: `SchemeProperties.GeometricPointLifting`; see the
  [three lifting theorems](docs/API.md#geometric-point-lifting-authored-note).

### Quasi-finite point fibers

- [Field-valued lift fibers](SchemeProperties/QuasiFinitePoints.lean): for
  `f : X ⟶ Y` and any field `K` in the schemes' universe,
  `[LocallyQuasiFinite f] [QuasiCompact f]` gives
  `Set.Finite {q : Spec (CommRingCat.of K) ⟶ X | q ≫ f = g}`
  for every `g : Spec (CommRingCat.of K) ⟶ Y`. Neither algebraic closedness
  of `K` nor local finite type of `f` is assumed in this direction.
  Conversely, for `[LocallyOfFiniteType f]`, finiteness of these lift fibers
  for **every** algebraically closed `K` and **every** such `g` implies
  `LocallyQuasiFinite f`, without quasi-compactness. With local finite type
  and quasi-compactness, this is an equivalence. Mathlib's
  `LocallyQuasiFinite` is fiberwise and does not itself require local finite
  type. The fibers use ordinary scheme morphisms, with no new point carrier.
  Direct import: `SchemeProperties.QuasiFinitePoints`; see the
  [authored API note](docs/API.md#current-quasi-finite-point-interfaces-authored-note).

### Field-extension lifting

- [Lifting field-valued points](SchemeProperties/FieldExtensionLifting.lean):
  an arbitrary morphism `f : X ⟶ Y` is surjective exactly when, for every
  field `K` in the schemes' universe, every `g : Spec K ⟶ Y` lifts to
  `q : Spec L ⟶ X` after some field extension `ι : K → L`, with
  `q ≫ f = Spec.map ι ≫ g`. No local finite type, quasi-compactness,
  algebraic closedness, nonemptiness or chosen ground field is assumed.
  The extension may be transcendental; a lift over `K` itself is not guaranteed.
  Direct import: `SchemeProperties.FieldExtensionLifting`.

### Universal injectivity and field-valued points

- [Algebraically closed field-valued points](SchemeProperties/UniversallyInjectiveGeometricPoints.lean):
  universal injectivity of an arbitrary scheme morphism is equivalent to
  injectivity on `Spec K`-valued points for every algebraically closed field.
  No finiteness, reducedness or separation hypothesis is imposed. The
  [guide](docs/UniversallyInjectiveGeometricPoints.md) relates this to Mathlib's
  all-field criterion and distinguishes it from underlying injectivity and monomorphisms.
  Direct import: `SchemeProperties.UniversallyInjectiveGeometricPoints`.

### Finite-field points

- [Finite-field lifts](SchemeProperties/FiniteFieldPoints.lean): for a finite
  field `K`, a locally-finite-type, quasi-compact `p : X ⟶ S` has finitely many
  lifts of any `q : Spec K ⟶ S`, expressed as the over-category Hom-set
  `Over.mk q ⟶ Over.mk p`. The base is arbitrary; no properness, separatedness,
  reducedness, integrality or group structure is assumed. The
  [affine-line client](SchemePropertiesTest/FiniteFieldPointsModel.lean) uses
  `Spec (Polynomial (ZMod 2)) → Spec (ZMod 2)` with distinct evaluation sections.
- [Finite-target algebra homomorphisms](SchemeProperties/FiniteAlgHom.lean):
  `Algebra.FiniteType.finite_algHom` proves `Finite (A →ₐ[R] B)` for a finite-type
  `R`-algebra `A` and finite `R`-algebra `B`. Only `R` is a commutative semiring;
  `A` and `B` may be noncommutative semirings in independent universes. This
  Mathlib-only leaf exports an explicit theorem, not a global instance, and
  does not require a module-finite or finite source. The geometric proof uses
  it chartwise. Neither leaf asserts an exact point count or Frobenius formula.

### Polynomial quotient points

- [Polynomial-quotient scheme points](SchemeProperties/PolynomialQuotientClosedPoints.lean):
  at a common universe, quotient evaluation at a zero over any field and any
  variable type gives a base-compatible affine scheme point whose image of the
  field's closed point is the evaluation-kernel prime. For an algebraically
  closed field and finitely many variables, Mathlib's base-compatible
  scheme-point/closed-point equivalence agrees with the polynomial zero-locus
  equivalence for every ideal, including nonreduced quotients. These are
  point-set comparisons, not topology, sheaf or cross-universe statements.
  Direct import: `SchemeProperties.PolynomialQuotientClosedPoints`.

### Reduced local rings

- [Reduced-localization locus](SchemeProperties/ReducedLocus.lean): over any
  commutative ring, a prime localization is reduced exactly when its prime is
  outside the **module** support of the nilradical. Consequently the nonreduced
  locus equals that support, and finite generation of the nilradical as a module
  suffices for the reduced locus to be open; this finiteness is not necessary.
  On any locally Noetherian scheme the locus of points with reduced stalks is
  open, without a quasi-compactness assumption. The proofs use Mathlib's
  localization of radicals, module support and affine stalk descriptions.
  Direct import: `SchemeProperties.ReducedLocus`.
- [Ring-equivalence reduced loci](SchemeProperties/ReducedLocusEquiv.lean):
  an equivalence of commutative semirings with independent universes preserves
  reducedness of localizations at corresponding primes and openness of the
  **entire** reduced prime-localization locus. No finiteness or reducedness
  hypothesis is needed. Direct import: `SchemeProperties.ReducedLocusEquiv`.
- [Square-zero reduced localizations](SchemeProperties/TrivSqZeroExtReducedLocus.lean):
  for any commutative ring `R`, any `R`-module `M` and a prime `p` of `R`, an
  arbitrary prime-localization model of the square-zero extension at the prime
  over `p` is reduced precisely when an arbitrary prime-localization model of
  `R` at `p` is reduced **and** `p` lies outside the module support of `M`.
  If `R` is reduced, the pullback of the reduced-localization locus is exactly
  the complement of that support; the full extension locus is open if and only
  if the support itself is closed. Neither finite generation nor a Noetherian
  hypothesis is required. The criterion uses Mathlib's prime-localization,
  support and square-zero projection-kernel APIs, together with Coherent Modules'
  canonical actions on the extension.
  Direct import: `SchemeProperties.TrivSqZeroExtReducedLocus`.
- [Polynomial point modules](SchemeProperties/PolynomialPointReducedLocus.lean):
  for any family of points over a field, the support of the direct sum of
  evaluation quotients is exactly the image of their evaluation primes. This
  support is closed, and the full reduced prime-localization locus of its
  square-zero extension is open, precisely when the family has finite image.
  Even an infinite family constantly repeating one point satisfies the
  criterion. Direct imports: `SchemeProperties.PolynomialPointPrime` and
  `SchemeProperties.PolynomialPointReducedLocus`.
- [Polynomial point quotients](SchemeProperties/PolynomialPointSquareZeroReducedLocus.lean):
  for an injective family of points over any field, the reduced-localization
  locus at **all** primes of its square-zero polynomial quotient is open exactly
  when the point family's image is finite. Injectivity supplies pairwise unit
  differences for the canonical quotient presentation; this does not classify
  nonseparated point families. The singleton quotient can be nonreduced while
  its reduced-localization locus is open. Direct import:
  `SchemeProperties.PolynomialPointSquareZeroReducedLocus`.

### Global dimension under flat surjections

- [Ring dimension](SchemeProperties/RingTheory/KrullDimension/GeneralizingMap.lean):
  a ring homomorphism `R →+* S` whose prime contraction is **generalizing and
  surjective** satisfies `ringKrullDim R ≤ ringKrullDim S`. In particular,
  faithful flatness suffices; the commutative rings may have independent universes.
- [Scheme dimension](SchemeProperties/FlatKrullDimension.lean): a **flat,
  point-surjective** morphism `f : X ⟶ Y` of schemes in a common universe gives
  `Order.krullDim Y ≤ Order.krullDim X`. This is a global bound, not equality
  of a chosen pair of stalk dimensions. No Noetherianity, quasi-compactness,
  finite-type or quasi-finiteness assumption is needed. Dimensions lie in
  `WithBot ℕ∞`, including `⊥` for zero rings/empty schemes and `∞`.
  The [private affine-line client](SchemePropertiesTest/FlatKrullDimension.lean)
  applies all three bounds to `ℚ → ℚ[X]` and `Spec ℚ[X] → Spec ℚ`, with
  independent dimensions `0 < 1`; the flat fraction-ring map shows why
  surjectivity cannot simply be omitted. Direct imports:
  `SchemeProperties.RingTheory.KrullDimension.GeneralizingMap` and
  `SchemeProperties.FlatKrullDimension`.

### Quasi-finite dimension bounds and local preservation

- [Global ring bounds](SchemeProperties/RingTheory/KrullDimension/QuasiFinite.lean):
  `RingHom.QuasiFinite.strictMono_comap hf` makes contraction strict on
  **comparable** primes, not globally injective on all primes.
  `RingHom.QuasiFinite.ringKrullDim_le hf` gives `ringKrullDim S ≤ ringKrullDim R`
  for `f : R →+* S`, with independent ring universes.
- [Global scheme bounds](SchemeProperties/QuasiFiniteKrullDimension.lean):
  `AlgebraicGeometry.LocallyQuasiFinite.krullDim_le f` gives
  `Order.krullDim X ≤ Order.krullDim Y` for `f : X ⟶ Y` between schemes in
  a common universe. The scheme order reverses specialization. Both global
  bounds take values in `WithBot ℕ∞`, including empty spectra of dimension
  `⊥` and infinite dimension. They need no flatness, Noetherianity, local
  finite type or quasi-compactness: quasi-finiteness means Mathlib's
  finite-dimensional residue-field fibers. These are upper bounds for whole
  spaces, not equalities of stalk dimensions. The [closed-origin example](SchemePropertiesTest/QuasiFiniteKrullDimension.lean)
  uses the finite, nonflat evaluation `ℚ[X] →+* ℚ` and its Spec map, with
  dimensions independently computed as `0 < 1`; the opposite coefficient
  inclusion and affine-line projection fail the respective quasi-finiteness
  hypotheses.

### Flat quasi-finite dimension preservation

- [Prime heights and local rings](SchemeProperties/RingTheory/KrullDimension/QuasiFinite.lean):
  a quasi-finite algebra with going down preserves the height of each prime
  under contraction. A flat quasi-finite local homomorphism of commutative
  local rings therefore preserves Krull dimension, with independent ring
  universes. No Noetherian or finite-type hypothesis is required.
  Direct import: `SchemeProperties.RingTheory.KrullDimension.QuasiFinite`.
- [Full scheme stalks](SchemeProperties/FlatQuasiFinite.lean): for a scheme
  morphism `f : X ⟶ Y` and a point `x`, flatness and quasi-finiteness of the
  stalk map imply equality of the Krull dimensions of the full stalks at
  `x` and `f x`. The assumptions are pointwise, not global morphism classes;
  these are not fibre-stalk dimensions.
  Direct import: `SchemeProperties.FlatQuasiFinite`.

### Integral neighborhoods

- [Integral neighborhoods](SchemeProperties/Integral.lean): on a locally
  Noetherian scheme, every point with a domain local ring has an integral open
  neighborhood, and the locus of such points is open. No global reducedness or
  quasi-compactness assumption is required. In particular, a connected locally
  Noetherian scheme whose local rings are domains is integral.
  Direct import: `SchemeProperties.Integral`.

### Projective spectra

- [Reducedness and integrality](SchemeProperties/ProjectiveSpectrum.lean): for an
  `ℕ`-grading `𝒜` of a commutative ring `A`, `Proj 𝒜` is reduced if `A` is
  reduced, and preirreducible if `A` is a domain, including when it is empty.
  A nonempty projective spectrum of a domain is integral. No finite generation
  or generation in degree one is required.
  Direct import: `SchemeProperties.ProjectiveSpectrum`.

### Local normality

- [Normality under scheme morphisms](SchemeProperties/NormalMorphisms.lean):
  for a morphism `f : X ⟶ Y` of schemes, a normal target and smooth `f`
  imply a normal source (`AlgebraicGeometry.isNormal_of_smooth`). A normal
  source and flat, point-surjective `f` imply a normal target
  (`AlgebraicGeometry.isNormal_of_surjective_of_flat`), without a
  quasi-compactness assumption. Étale ascent follows from étale ⇒ smooth.
  Direct import: `SchemeProperties.NormalMorphisms`.
- [Faithfully flat descent](SchemeProperties/NormalFaithfullyFlat.lean): for
  commutative rings `R` and `S` in independent universes, an `R`-algebra `S`
  that is faithfully flat as its canonical `R`-module and locally normal
  implies that `R` is locally normal. Here local normality means that every
  prime localization is an integrally closed domain; disconnected and zero
  rings are allowed. No Noetherian, finite or global-domain hypothesis is
  needed. The entry point is `IsLocallyNormalRing.of_faithfullyFlat`, a theorem
  rather than an instance. Direct import: `SchemeProperties.NormalFaithfullyFlat`.

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
  `SchemeProperties.PullbackOpenImmersion`; the [direct-import client](SchemePropertiesTest/PullbackOpenImmersionClient.lean)
  is included.

### Generic points and birational geometry

- [Compatible partial-map gluing](SchemeProperties/PartialMapGluing.lean):
  a dense-open partial map and a morphism on any open, agreeing as scheme
  morphisms on their intersection, glue on exactly the union. Both whole-open
  restrictions characterize the glued morphism uniquely; it preserves the
  anchor's rational-map class and the structure over any common base when both
  inputs are over that base. Gluing two partial maps specializes this construction
  and recovers both partial maps and rational classes. The added open need not
  be dense; reducedness and separatedness are not required. Direct import:
  `SchemeProperties.PartialMapGluing`.
- [Canonical generic-point function-field map](docs/GenericPointFunctionField.md):
  for integral `Y`, its total map `j : Spec Y.functionField ⟶ Y` and native
  rational quotient are dominant; the actual reversed
  `j.toRationalMap.functionFieldMap` reads back on `Spec` as the generic stalk
  map of the field spectrum and is `IsIso`, without finite-type hypotheses.
  With `[JacobsonSpace Y] [Nontrivial Y]`, `j` is not locally of finite type,
  nor is `j ≫ sY` for **any independent** `sY : Y ⟶ S`. This does not assert
  a total-scheme isomorphism or a rational inverse/noninverse theorem. Direct
  import: `SchemeProperties.GenericPointFunctionField`; its
  [client](SchemePropertiesTest/GenericPointFunctionFieldClient.lean) uses the actual
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
  `SchemeProperties.JacobsonBirationalObstruction`; [one direct-import client with five anonymous examples](SchemePropertiesTest/JacobsonBirationalObstructionClient.lean).
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
  `SchemeProperties.RationalMapPartialIso`; [four private clients](SchemePropertiesTest/RationalMapPartialIsoClient.lean)
  check the exact readbacks and six-part converse.
- [Valuation-stalk extension](SchemeProperties/RationalMapValuativeExtension.lean):
  for integral `X` over an arbitrary base `S` and a relatively proper map
  `sY : Y ⟶ S`, a native partial map `p` over `S` has a chosen compatible
  representative defined at any point `x` whose stalk is a valuation ring.
  `Scheme.PartialMap.extensionOfValuationRingStalk` preserves the rational-map
  quotient and agrees with `p` as a full scheme morphism on their entire domain
  intersection. No old-domain containment, uniqueness or absolute separatedness
  of `Y` or `S` is asserted or assumed. This is the local valuative ingredient,
  not a global normal-source or codimension theorem. Direct import:
  `SchemeProperties.RationalMapValuativeExtension`.
- [Relative valuative extension](SchemeProperties/RelativeValuativeExtension.lean):
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
### Function fields

- [Function-field naturality](SchemeProperties/RationalFunctionFieldNaturality.lean):
  for a dominant morphism between integral same-universe schemes, pullback of
  sections on any nonempty target open commutes with the canonical maps to
  function fields. Dominance also ensures that the inverse-image open is
  nonempty. The [affine-line example](SchemePropertiesExamples/FunctionFieldNaturality.lean)
  applies this to the structure morphism `Spec ℚ[X] → Spec ℚ`.
  Direct import: `SchemeProperties.RationalFunctionFieldNaturality`.
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

- [Local normality under étale algebras](SchemeProperties/NormalEtale.lean):
  an étale algebra over a locally normal commutative ring is locally normal,
  with independent base and target universes. Neither module-finiteness nor
  Noetherianity is assumed; the algebra itself may be disconnected.
- [Geometric irreducibility implies geometric connectedness](SchemeProperties/GeometricallyConnected.lean):
  every geometrically irreducible morphism of arbitrary same-universe schemes
  is geometrically connected, by typeclass synthesis. No finite-type or
  nonempty-target assumption is needed. Direct import:
  `SchemeProperties.GeometricallyConnected`.
- [Connectedness through closed points](SchemeProperties/JacobsonConnectedness.lean):
  any Jacobson topological space is connected if and only if its induced subspace
  of closed points is connected, with no separation, Noetherianity, compactness
  or nonemptiness assumption. The [affine-line example](SchemePropertiesTest/JacobsonConnectedness.lean)
  has a connected proper closed-point subspace. Direct import:
  `SchemeProperties.JacobsonConnectedness`.
- [Products of locally normal rings](SchemeProperties/LocallyNormalRing/Pi.lean):
  local normality of an arbitrary product descends to each factor, and a finite
  product is locally normal if and only if all its factors are. The index and
  coefficient universes are independent; empty products and zero factors are
  included. The finite-product theorem is also available from
  `SchemeProperties.NormalEtale`.
- [Local normality at maximal ideals](SchemeProperties/LocallyNormalRing/Maximal.lean):
  a commutative ring is locally normal exactly when its localizations at all
  maximal ideals are domains and integrally closed. This includes zero and
  disconnected rings, with no Noetherian or global-domain assumption.
  Direct import: `SchemeProperties.LocallyNormalRing.Maximal`.
- [Normality and factoriality](SchemeProperties/FactorialNormal.lean) relates
  stalkwise factorial schemes to normal schemes. The
  [normality criteria](SchemeProperties/Normal.lean) characterize normality of an
  affine scheme by local normality of its global sections, of an affine open by
  local normality of its ambient ring of sections, and of a scheme by local
  normality of every coordinate ring of any affine open cover. The cover's index
  universe may be independent of the scheme universe. The [local-normality
  interfaces](SchemeProperties/NormalSeparableScheme.lean) also cover base
  change along transcendental-separable field extensions, not all extensions.
- [Locally normal binary products](SchemeProperties/LocallyNormalRing/Product.lean):
  for commutative rings `R : Type u` and `S : Type v`, `R × S` is locally
  normal if and only if both factors are locally normal. The universes are
  independent, zero-ring factors are allowed, and no domain or Noetherian
  hypothesis is needed. Direct import: `SchemeProperties.LocallyNormalRing.Product`.
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

The Mathlib-only algebra leaf
`SchemeProperties.RingTheory.KrullDimension.QuasiFinite` supplies global ring
dimension bounds, prime-height preservation and local-ring dimension preservation.
`SchemeProperties.QuasiFiniteKrullDimension` supplies the global scheme bound;
these two modules can be imported directly. The closed-origin use is in
`SchemePropertiesTest.QuasiFiniteKrullDimension`. `SchemeProperties.FlatQuasiFinite`
adds the distinct pointwise full-stalk equality application; the affine-line
double-cover use is maintained in `SchemePropertiesTest.FlatQuasiFinite`.

`import SchemeProperties` loads the [aggregate](SchemeProperties.lean). For
focused imports use `SchemeProperties.<Module>` from the [reader guide's module
tables](docs/Guide.md); the [documentation index](docs/README.md) links focused
mathematical guides. Inspect direct-import [test clients](SchemePropertiesTest/) and concrete
[examples](SchemePropertiesExamples/) for use cases; the [module-name guide](docs/ModuleNames.md)
lists their import roots. For instance, import
`SchemeProperties.GenericPointFunctionField`,
`SchemeProperties.GenericPointRationalNoninvertibility`,
`SchemeProperties.RationalMapPartialIso` or
`SchemeProperties.ModuleFinitePresentation` directly. The ring-equivalence
reduced-locus theorems are in `SchemeProperties.ReducedLocusEquiv`; the
polynomial quotient theorem uses the released Multivariate Polynomials
presentation in `SchemeProperties.PolynomialPointSquareZeroReducedLocus`.

`SchemeProperties.Reduced` re-exports
`MinimalPrimes.RingTheory.Localization.Reduced`. Its theorem
`IsReduced.of_isLocalization` preserves reducedness under arbitrary localization
of commutative semirings in independent universes. The prime-localization and
scheme-stalk results use this theorem; `IsLocalization.isReduced` retains the
commutative-ring interface as a deprecated specialization.

[API.md](docs/API.md) and its [manifest](docs/api-manifest.json) are a **fixed
historical 73-module** native-doc snapshot, not a current declaration
census. The [API reproduction guide](docs/README.md) explains its immutable
input contract; later results are in focused guides and source files.

## Build

[Lean](lean-toolchain) is pinned to v4.34.0-rc2; mathlib and the four official
dependencies have exact revisions in [Lake](lakefile.toml) and the
[manifest](lake-manifest.json). `coherent-modules`, `finite-etale-algebras`,
`multivariate-polynomials` and `minimal-primes` use public GitHub releases. Install
[elan](https://github.com/leanprover/elan), fetch the matching mathlib cache
successfully for this checkout (again after changing pins or `.lake`), then
build the library, tests and examples:

```sh
lake exe cache get
lake build SchemeProperties SchemePropertiesTest SchemePropertiesExamples
```

An optional `lake --wfail build ...` check makes warnings fatal. These targets
currently emit linter warnings, so that check can fail even when the normal
build succeeds.

## References

- Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*: Exercise
  5.3.C informs the integrality criterion; the aside to Exercise 5.4.M informs
  separable-base-change normality; the discussion of reduced local rings and
  their locus informs the reduced-stalk openness result; Definition 6.1.1,
  Theorem 6.1.2 and the opening of §6.3 inform affine-cover quasicoherence and
  its abelian structure.
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
- J. S. Milne, *Abelian Varieties*, version 2.00, Conventions, p. v:
  motivation for the independent Jacobson-space comparison between
  closed-point and whole-space connectedness, not a named theorem of that text.
- Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Chapter I, §5: motivation for affine finite-presentation work.
- [The Stacks Project](https://stacks.math.columbia.edu/), tags 037U, 0386,
  0385 and 0363: a proof route from field-extension geometric connectedness
  to connected schemes over separably closed fields.
- [Mathlib](https://github.com/leanprover-community/mathlib4): reused scheme,
  rational-map, restricted-Yoneda, flat-sections, tensor, sheaf and descent
  methods, as well as adapted constructions detailed in
  [Credits](docs/CREDITS.md), with authentic upstream notices preserved.
- [Coherent Modules](https://github.com/FormalFrontier/coherent-modules),
  [Finite Étale Algebras](https://github.com/FormalFrontier/finite-etale-algebras)
  and [Multivariate Polynomials](https://github.com/FormalFrontier/multivariate-polynomials):
  prior formalizations used for coherent-module localization, finite-étale
  component algebras and descent, and the polynomial point-quotient presentation.

- [Minimal Primes](https://github.com/FormalFrontier/minimal-primes) supplies
  `IsReduced.of_isLocalization`, the canonical independent-universe
  commutative-semiring theorem used for reducedness under localization. It
  generalizes Andrew Yang's Mathlib `isReduced_localizationPreserves` and the
  earlier commutative-ring formulation in `SchemeProperties.Reduced`; its proof
  uses Mathlib's radical-localization and nilradical APIs.

The [credits](docs/CREDITS.md) distinguish mathematical antecedents, followed
proof patterns, imported APIs, adapted expression and original project work.
