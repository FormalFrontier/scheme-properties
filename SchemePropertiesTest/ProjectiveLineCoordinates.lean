/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The independent arithmetic point `[1 : (2,3)]`

Concrete support for the disconnected normal-source model. The target is the whole
`Proj` of `ℤ[X₀,X₁]`, proper over the actual `Spec ℤ`. The total map from
`Spec (ℤ × ℤ)` is constructed by evaluating the `X₀` standard chart, independently
of any extension theorem. Source geometry and partial-map restriction are separate.

-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveLineCoordinates

noncomputable section

/-- The two-variable homogeneous coordinate ring over the integers. -/
abbrev PolynomialRing := MvPolynomial (Fin 2) ℤ

/-- Its ordinary total-degree grading. -/
abbrev grading : ℕ → Submodule ℤ PolynomialRing :=
  MvPolynomial.homogeneousSubmodule (Fin 2) ℤ

instance grading_gradedAlgebra : GradedAlgebra grading :=
  MvPolynomial.gradedAlgebra (σ := Fin 2) (R := ℤ)

/-- The degree-zero subring. -/
abbrev DegreeZero := grading 0

/-- Constant coefficient on the degree-zero subtype. -/
def degreeZeroToInt : DegreeZero →+* ℤ :=
  MvPolynomial.constantCoeff.comp (algebraMap DegreeZero PolynomialRing)

theorem degreeZero_eq_C (a : DegreeZero) :
    (a : PolynomialRing) = MvPolynomial.C (degreeZeroToInt a) := by
  change (a : PolynomialRing) = MvPolynomial.C ((a : PolynomialRing).coeff 0)
  exact MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
    ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 2)).mpr a.property)

theorem degreeZeroToInt_injective : Function.Injective degreeZeroToInt := by
  intro a b h
  apply Subtype.ext
  rw [degreeZero_eq_C a, degreeZero_eq_C b, h]

theorem degreeZeroToInt_surjective : Function.Surjective degreeZeroToInt := by
  intro n
  refine ⟨⟨MvPolynomial.C n,
    MvPolynomial.isHomogeneous_C (σ := Fin 2) (R := ℤ) n⟩, ?_⟩
  change MvPolynomial.constantCoeff (MvPolynomial.C n : PolynomialRing) = n
  exact MvPolynomial.constantCoeff_C (Fin 2) n

/-- The concrete coefficient-ring identification, using the stock constant-coefficient map. -/
def degreeZeroEquiv : DegreeZero ≃+* ℤ :=
  RingEquiv.ofBijective degreeZeroToInt
    ⟨degreeZeroToInt_injective, degreeZeroToInt_surjective⟩

/-- The integer spectrum. -/
abbrev base : Scheme := Spec (.of ℤ)

/-- The whole projective line, not one of its affine charts. -/
abbrev target : Scheme := Proj grading

/-- The spectrum isomorphism induced by the degree-zero coefficient equivalence. -/
def baseIso : Spec (.of DegreeZero) ≅ base :=
  Scheme.Spec.mapIso degreeZeroEquiv.symm.toCommRingCatIso.op

instance degreeZero_finiteType : Algebra.FiniteType DegreeZero PolynomialRing := by
  have : IsScalarTower ℤ DegreeZero PolynomialRing :=
    AddCommGroup.intIsScalarTower (R := DegreeZero) (M := PolynomialRing)
  exact Algebra.FiniteType.of_restrictScalars_finiteType ℤ DegreeZero PolynomialRing

/-- The projective-line structure morphism over the integers. -/
def structureMap : target ⟶ base :=
  Proj.toSpecZero grading ≫ baseIso.hom

instance structureMap_isProper : IsProper structureMap := by
  unfold structureMap
  infer_instance

abbrev coordinate0 : PolynomialRing := MvPolynomial.X (0 : Fin 2)
abbrev coordinate1 : PolynomialRing := MvPolynomial.X (1 : Fin 2)

theorem coordinate0_mem : coordinate0 ∈ grading 1 :=
  MvPolynomial.isHomogeneous_X ℤ (0 : Fin 2)

theorem coordinate1_mem : coordinate1 ∈ grading 1 :=
  MvPolynomial.isHomogeneous_X ℤ (1 : Fin 2)

/-- Evaluate the homogeneous coordinates at `X₀ = 1`, `X₁ = (2,3)`. -/
def evaluate : PolynomialRing →+* (ℤ × ℤ) :=
  MvPolynomial.eval₂Hom (Int.castRingHom (ℤ × ℤ))
    (fun i : Fin 2 => if i = 0 then 1 else (2, 3))

@[simp]
theorem evaluate_coordinate0 : evaluate coordinate0 = 1 := by
  simp [evaluate, coordinate0, MvPolynomial.eval₂Hom_X']

@[simp]
theorem evaluate_coordinate1 : evaluate coordinate1 = (2, 3) := by
  simp [evaluate, coordinate1, MvPolynomial.eval₂Hom_X']

/-- Ordinary localization evaluation, obtained from the existing universal property. -/
def localizedEvaluation : Localization.Away coordinate0 →+* (ℤ × ℤ) :=
  IsLocalization.Away.lift (S := Localization.Away coordinate0) (g := evaluate)
    coordinate0 (by rw [evaluate_coordinate0]; exact isUnit_one)

/-- The degree-zero localization defining the `X₀` chart. -/
abbrev ChartRing := HomogeneousLocalization.Away grading coordinate0

/-- Evaluation on the chart, through the existing homogeneous-localization forgetful map. -/
def chartEvaluation : ChartRing →+* (ℤ × ℤ) :=
  localizedEvaluation.comp
    (algebraMap ChartRing (Localization.Away coordinate0))

/-- The affine coordinate `X₁ / X₀` in the standard chart ring. -/
def chartCoordinate : ChartRing :=
  HomogeneousLocalization.Away.mk grading coordinate0_mem 1 coordinate1
    (by simpa using coordinate1_mem)

/-- The characteristic coordinate of the point is the pair `(2,3)`. -/
theorem chartEvaluation_chartCoordinate :
    chartEvaluation chartCoordinate = (2, 3) := by
  change localizedEvaluation chartCoordinate.val = (2, 3)
  simp only [chartCoordinate, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk']
  unfold localizedEvaluation IsLocalization.Away.lift
  apply (IsLocalization.lift_mk'_spec _ _ _ _).mpr
  simp [evaluate, coordinate0, coordinate1, MvPolynomial.eval₂Hom_X']

/-- The standard chart maps into the projective line. -/
def chartMap : Spec (.of ChartRing) ⟶ target :=
  Proj.awayι grading coordinate0 coordinate0_mem Nat.zero_lt_one

/-- The morphism `[1:(2,3)]` from the product-ring spectrum. -/
def point : Spec (.of (ℤ × ℤ)) ⟶ target :=
  Spec.map (CommRingCat.ofHom chartEvaluation) ≫ chartMap

/-- The diagonal integer structure morphism on the product-ring spectrum. -/
def sourceStructureMap : Spec (.of (ℤ × ℤ)) ⟶ base :=
  Spec.map (CommRingCat.ofHom (Int.castRingHom (ℤ × ℤ)))

theorem chartMap_toSpecZero :
    chartMap ≫ Proj.toSpecZero grading =
      Spec.map (CommRingCat.ofHom
        (HomogeneousLocalization.fromZeroRingHom grading (Submonoid.powers coordinate0))) :=
  Proj.awayι_toSpecZero grading coordinate0 coordinate0_mem Nat.zero_lt_one

/-- The full over-base equation for the independent total morphism. -/
theorem point_structureMap : point ≫ structureMap = sourceStructureMap := by
  unfold point structureMap
  rw [Category.assoc,
    ← Category.assoc chartMap (Proj.toSpecZero grading) baseIso.hom,
    chartMap_toSpecZero]
  change Spec.map (CommRingCat.ofHom chartEvaluation) ≫
      (Spec.map (CommRingCat.ofHom
          (HomogeneousLocalization.fromZeroRingHom grading (Submonoid.powers coordinate0))) ≫
        Spec.map (CommRingCat.ofHom degreeZeroEquiv.symm.toRingHom)) = sourceStructureMap
  rw [← Spec.map_comp, ← Spec.map_comp]
  unfold sourceStructureMap
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact Subsingleton.elim _ _

instance targetOverBase : target.Over base := .ofHom structureMap

instance sourceOverBase : (Spec (.of (ℤ × ℤ))).Over base := .ofHom sourceStructureMap

instance point_isOver : point.IsOver base :=
  ⟨point_structureMap⟩

end

end AlgebraicGeometry.ProjectiveLineCoordinates
