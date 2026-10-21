# Points and morphism criteria

See the [overview](../README.md), [reader guide](Guide.md) and
[documentation index](README.md) for navigation and imports. Mathematical
[references](../README.md#references) and [credits](CREDITS.md) apply throughout.

## Affine test objects

- [Affine schemes separate morphisms](../SchemeProperties/AffineTestObjects.lean):
  affine schemes form a separating family in Mathlib's `ObjectProperty` API.
  For arbitrary `f : X ⟶ Y` in `Scheme.{u}`, `Mono f` is equivalent to
  injectivity of `g ↦ g ≫ f` on `Spec (CommRingCat.of R) ⟶ X` for every
  commutative ring `R : Type u`. No reducedness, finite-type, quasi-compactness
  or separatedness hypothesis is needed; zero rings and empty schemes are
  included. This is a monomorphism criterion, not an isomorphism criterion,
  and field-valued points alone do not suffice. The
  [line-in-plane example](../SchemePropertiesTest/AffineTestObjects.lean) has
  two distinct rational source points with distinct images.
  Direct import: `SchemeProperties.AffineTestObjects`.

## Affine tests for isomorphisms

- [Affine generators](../SchemeProperties/AffineGenerators.lean): affine schemes form
  a strong generator of `Scheme.{u}` and detect isomorphisms. For arbitrary
  `f : X ⟶ Y`, `IsIso f` is equivalent to bijectivity of `g ↦ g ≫ f` on maps
  `Spec R ⟶ X` for **every** commutative ring `R : Type u`, including the zero
  ring. No finiteness, separatedness or monomorphism premise is required.
  Direct import: `SchemeProperties.AffineGenerators`; the
  [affine-line examples](../SchemePropertiesTest/AffineGenerators.lean) contrast
  the identity with the zero section, which misses the rational point at one.

## Affine density

- [Affine density](../SchemeProperties/AffineDensity.lean) shows that
  `Scheme.Spec : CommRingCat.{u}ᵒᵖ ⥤ Scheme.{u}` is cover-dense for the big
  Zariski topology and dense among all schemes in that universe. All commutative
  rings, including the zero ring, are tests; empty and nonreduced schemes are included.
  No field, finite-type, separatedness or small-test-category hypothesis is imposed.
  Full faithfulness and reconstruction for the existing
  `Presheaf.restrictedULiftYoneda.{0} Scheme.Spec` are supplied by Mathlib from
  density, not by a new points functor or separate theorem here.
  Its values are `ULift.{0} (Spec R ⟶ X) : Type u`; natural-transformation Homs
  lie in `Type (u + 1)`. See the [API note](API.md#affine-density)
  and [affine reconstruction example](../SchemePropertiesTest/AffineDensity.lean).
  Direct import: `SchemeProperties.AffineDensity`.

## Finitely generated algebras

- [Universe lifting](../SchemeProperties/FiniteTypeUniverseLift.lean): for a
  commutative ring `R : Type u` with `[Small.{v} R]`, Mathlib's existing
  `FGAlgCat.uliftFunctor R : FGAlgCat.{v} R ⥤ FGAlgCat.{max v w} R` is an
  equivalence, with independent universes `u`, `v` and `w`. Zero algebras are
  included; no global universe-order assumption is needed. This compares
  the categories of finitely generated algebras themselves, not a chosen
  presentation category. Direct import: `SchemeProperties.FiniteTypeUniverseLift`.

## Morphisms from reduced schemes

- [Reduced-source extensionality](../SchemeProperties/ReducedHomExt.lean): for
  morphisms `f g : X ⟶ Y` with reduced source, agreement after every canonical
  residue-field map implies `f = g`
  (`Scheme.Hom.ext_of_fromSpecResidueField`). Equivalently, it suffices to agree
  after **all** field-valued points (`Scheme.Hom.ext_of_field_valued_points`),
  with fields in the common scheme universe. The target is arbitrary: no
  separatedness, finite-type or Noetherian hypothesis is imposed. Empty sources
  are allowed. These tests compare scheme morphisms, not just maps of points.
  Direct import: `SchemeProperties.ReducedHomExt`; see the
  [affine-line application](../SchemePropertiesTest/ReducedHomExt.lean).
- **Sections are determined by their point maps:** if `i : Y ⟶ X`, `X` is reduced,
  and `s t : X ⟶ Y` both satisfy `s ≫ i = 𝟙 X` and `t ≫ i = 𝟙 X`, then
  agreement at **every** point of `X` implies `s = t`
  (`Scheme.Hom.ext_of_apply_eq_of_comp_eq_id`). The target and structural map
  are arbitrary, and `X` may be empty. Both section equations are essential;
  this is not point-map extensionality for arbitrary morphisms. The same
  [application](../SchemePropertiesTest/ReducedHomExt.lean) treats integer
  evaluation sections of the affine line over `Spec ℤ`.

## Sections and dense closed-point tests

For any field `K : Type u`, any scheme `Y : Scheme.{u}`, and morphisms
`f g : Spec ↧K ⟶ Y`, the section criterion
[`Scheme.Hom.ext_of_apply_closedPoint_eq_of_comp_eq_id`](../SchemeProperties/RationalPointExtensionality.lean)
uses a specified `i : Y ⟶ Spec ↧K`, both identities `f ≫ i = 𝟙 _` and
`g ≫ i = 𝟙 _`, and agreement at `IsLocalRing.closedPoint K` to conclude
`f = g` as scheme morphisms. Neither algebraic closedness of `K` nor separatedness,
finite type or reducedness of `Y`, nor a monomorphism hypothesis on `i`, is needed.
The section identities control the residue-field embeddings, not just the image points; see
Mathlib's [residue-field classification](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/AlgebraicGeometry/ResidueField.lean).
The [coordinate-section application](../SchemePropertiesTest/RationalPointExtensionality.lean)
uses independently constructed sections of the affine line over `ℚ` to recover
equality of their rational parameters from agreement of their image points.

For schemes `X Y : Scheme.{u}` over an algebraically closed field `K : Type u`,
[`Scheme.Hom.ext_of_apply_eq_on_dense_closedPoints`](../SchemeProperties/RationalPointExtensionality.lean)
compares `f g : X ⟶ Y` with a specified separated morphism `i : Y ⟶ Spec ↧K`.
It assumes `X` is reduced, `f ≫ i` is locally of finite type, a subset `S : Set X`
is dense and locally closed, `f x = g x` for each `x ∈ S` whose singleton is closed,
and the base compatibility `f ≫ i = g ≫ i`; it concludes `f = g`.
There is no locally finite type assumption on `i`. This generalizes Mathlib's
[closed-point criterion](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/AlgebraicGeometry/AlgClosed/Basic.lean).
The [affine-line application](../SchemePropertiesTest/RationalPointExtensionality.lean)
uses closed-point sections to determine the coordinate pullback of endomorphisms
compatible with the structure map. Direct import for both criteria:
`SchemeProperties.RationalPointExtensionality`.

## Geometric-point lifting

- [Surjectivity and geometric points](../SchemeProperties/GeometricPointLifting.lean):
  a locally finite type morphism `f : X ⟶ Y` is surjective exactly when,
  for every algebraically closed field `K` in the schemes' common universe and
  every `p : Spec K ⟶ Y`, there is `q : Spec K ⟶ X` with `q ≫ f = p`.
  The lift uses the same `K`, without a field extension; the implication from
  lifting to surjectivity does not require local finite type.
  Direct import: `SchemeProperties.GeometricPointLifting`; see the
  [three lifting theorems](API.md#geometric-point-lifting-authored-note).

## Quasi-finite point fibers

- [Field-valued lift fibers](../SchemeProperties/QuasiFinitePoints.lean): for
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
  [authored API note](API.md#current-quasi-finite-point-interfaces-authored-note).

## Field-extension lifting

- [Lifting field-valued points](../SchemeProperties/FieldExtensionLifting.lean):
  an arbitrary morphism `f : X ⟶ Y` is surjective exactly when, for every
  field `K` in the schemes' universe, every `g : Spec K ⟶ Y` lifts to
  `q : Spec L ⟶ X` after some field extension `ι : K → L`, with
  `q ≫ f = Spec.map ι ≫ g`. No local finite type, quasi-compactness,
  algebraic closedness, nonemptiness or chosen ground field is assumed.
  The extension may be transcendental; a lift over `K` itself is not guaranteed.
  Direct import: `SchemeProperties.FieldExtensionLifting`.

## Universal injectivity and field-valued points

- [Algebraically closed field-valued points](../SchemeProperties/UniversallyInjectiveGeometricPoints.lean):
  universal injectivity of an arbitrary scheme morphism is equivalent to
  injectivity on `Spec K`-valued points for every algebraically closed field.
  No finiteness, reducedness or separation hypothesis is imposed. The
  [guide](UniversallyInjectiveGeometricPoints.md) relates this to Mathlib's
  all-field criterion and distinguishes it from underlying injectivity and monomorphisms.
  Direct import: `SchemeProperties.UniversallyInjectiveGeometricPoints`.

## Residue fields of monomorphisms

- [Residue-field maps](../SchemeProperties/ResidueField.lean): for arbitrary
  `f : X ⟶ Y` in `Scheme.{u}` with `[Mono f]` and every `x : X`, the canonical
  map `κ(f x) → κ(x)`, `f.residueFieldMap x`, is an isomorphism.
  `AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_of_mono` supplies
  `IsIso (f.residueFieldMap x)` as a named theorem, not a new global instance;
  its conclusion can be used as a local instance with `inv` and `asIso`.
  No finiteness, local finite type, affineness, reducedness, separatedness,
  field-base or splitting hypothesis is required. Universal injectivity alone
  does not imply this conclusion. Direct import: `SchemeProperties.ResidueField`.

## Finite-field points

- [Finite-field lifts](../SchemeProperties/FiniteFieldPoints.lean): for a finite
  field `K`, a locally-finite-type, quasi-compact `p : X ⟶ S` has finitely many
  lifts of any `q : Spec K ⟶ S`, expressed as the over-category Hom-set
  `Over.mk q ⟶ Over.mk p`. The base is arbitrary; no properness, separatedness,
  reducedness, integrality or group structure is assumed. The
  [affine-line client](../SchemePropertiesTest/FiniteFieldPointsModel.lean) uses
  `Spec (Polynomial (ZMod 2)) → Spec (ZMod 2)` with distinct evaluation sections.
- [Finite-target algebra homomorphisms](../SchemeProperties/FiniteAlgHom.lean):
  `Algebra.FiniteType.finite_algHom` proves `Finite (A →ₐ[R] B)` for a finite-type
  `R`-algebra `A` and finite `R`-algebra `B`. Only `R` is a commutative semiring;
  `A` and `B` may be noncommutative semirings in independent universes. This
  Mathlib-only leaf exports an explicit theorem, not a global instance, and
  does not require a module-finite or finite source. The geometric proof uses
  it chartwise. Neither leaf asserts an exact point count or Frobenius formula.

## Polynomial quotient points

- [Polynomial-quotient scheme points](../SchemeProperties/PolynomialQuotientClosedPoints.lean):
  at a common universe, quotient evaluation at a zero over any field and any
  variable type gives a base-compatible affine scheme point whose image of the
  field's closed point is the evaluation-kernel prime. For an algebraically
  closed field and finitely many variables, Mathlib's base-compatible
  scheme-point/closed-point equivalence agrees with the polynomial zero-locus
  equivalence for every ideal, including nonreduced quotients. These are
  point-set comparisons, not topology, sheaf or cross-universe statements.
  Direct import: `SchemeProperties.PolynomialQuotientClosedPoints`.
