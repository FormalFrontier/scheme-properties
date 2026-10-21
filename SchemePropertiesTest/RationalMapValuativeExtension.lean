/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.RationalMapValuativeExtension
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # A punctured affine-line map to the projective line

Evaluate the homogeneous coordinates of `Proj ℚ[X₀, X₁]` at `(1, t)` and use the
existing global-sections constructor. The resulting map is nonconstant, its restriction
to `D(t)` omits the origin, and the total map is an independent extension. The base is
the spectrum of the degree-zero homogeneous component; properness is relative
to `Proj.toSpecZero`. No coefficient-base isomorphism is used.

The origin's scheme stalk is a valuation ring. A separate generic-point stalk
records the field case, with coheight zero. The coordinate construction and its model
proofs do not use the extension theorem or its chosen representative constructor.
A separate final application uses the public extension theorem at the origin.
At the origin, the first homogeneous coordinate is nonvanishing and the second vanishes,
as for `[1:0]`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SchemePropertiesTest.RationalMapValuativeExtension

attribute [local instance] MvPolynomial.gradedAlgebra

private abbrev affineLine : Scheme := Spec (CommRingCat.of (Polynomial ℚ))

private abbrev homogeneousCoordinateRing := MvPolynomial (Fin 2) ℚ

private abbrev homogeneousGrading := MvPolynomial.homogeneousSubmodule (Fin 2) ℚ

private abbrev projectiveLine : Scheme := Proj homogeneousGrading

private abbrev coefficientBase : Scheme := Spec (CommRingCat.of (homogeneousGrading 0))

private def coordinateOpen : affineLine.Opens :=
  PrimeSpectrum.basicOpen (Polynomial.X : Polynomial ℚ)

private def origin : PrimeSpectrum (Polynomial ℚ) :=
  ⟨Ideal.span {Polynomial.X},
    (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X⟩

private theorem coordinateOpen_dense : Dense (coordinateOpen : Set affineLine) := by
  apply coordinateOpen.isOpen.dense
  refine ⟨⟨⊥, inferInstance⟩, ?_⟩
  change (Polynomial.X : Polynomial ℚ) ∉ (⊥ : Ideal (Polynomial ℚ))
  simpa only [Ideal.mem_bot] using (Polynomial.X_ne_zero (R := ℚ))

private theorem origin_not_mem_coordinateOpen : origin ∉ coordinateOpen := by
  change ¬ (Polynomial.X : Polynomial ℚ) ∉ Ideal.span {Polynomial.X}
  intro h
  exact h (Ideal.subset_span (by simp))

private theorem coordinateOpen_ne_top : coordinateOpen ≠ ⊤ := by
  intro h
  apply origin_not_mem_coordinateOpen
  rw [h]
  trivial

private instance origin_stalk_isDomain : IsDomain (affineLine.presheaf.stalk origin) :=
  (StructureSheaf.stalkIso (Polynomial ℚ) origin).symm.toRingEquiv.toMulEquiv.isDomain _

private theorem origin_valuationRing : ValuationRing (affineLine.presheaf.stalk origin) := by
  let : Algebra (Polynomial ℚ) (affineLine.presheaf.stalk origin) :=
    StructureSheaf.stalkAlgebra (Polynomial ℚ) origin
  let : IsLocalization.AtPrime (affineLine.presheaf.stalk origin) origin.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (Polynomial ℚ) origin
  let : IsLocalRing (affineLine.presheaf.stalk origin) :=
    IsLocalization.AtPrime.isLocalRing _ origin.asIdeal
  let : IsDedekindDomain (affineLine.presheaf.stalk origin) :=
    IsLocalization.AtPrime.isDedekindDomain (Polynomial ℚ) origin.asIdeal _
  infer_instance

private def coordinateValues (i : Fin 2) : Polynomial ℚ :=
  if i = 0 then 1 else Polynomial.X

private def coordinateEvaluation : homogeneousCoordinateRing →+* Polynomial ℚ :=
  (MvPolynomial.aeval coordinateValues).toRingHom

private def sectionEvaluation : homogeneousCoordinateRing →+* Γ(affineLine, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℚ))).inv.hom.comp coordinateEvaluation

private theorem coordinate_mem_degree_one (i : Fin 2) :
    (MvPolynomial.X i : homogeneousCoordinateRing) ∈ homogeneousGrading 1 :=
  (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X ℚ i)

private theorem map_irrelevant_eq_top :
    (HomogeneousIdeal.irrelevant homogeneousGrading).toIdeal.map sectionEvaluation = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have h := Ideal.mem_map_of_mem sectionEvaluation
    (HomogeneousIdeal.mem_irrelevant_of_mem homogeneousGrading Nat.zero_lt_one
      (coordinate_mem_degree_one 0))
  simpa [sectionEvaluation, coordinateEvaluation, coordinateValues] using h

private def projectiveMap : affineLine ⟶ projectiveLine :=
  Proj.fromOfGlobalSections homogeneousGrading sectionEvaluation map_irrelevant_eq_top

private instance degreeZero_finiteType :
    Algebra.FiniteType (homogeneousGrading 0) homogeneousCoordinateRing := by
  let : IsScalarTower ℚ (homogeneousGrading 0) homogeneousCoordinateRing :=
    IsScalarTower.of_algebraMap_eq' (R := ℚ) (S := homogeneousGrading 0)
      (A := homogeneousCoordinateRing) rfl
  exact Algebra.FiniteType.of_restrictScalars_finiteType
    ℚ (homogeneousGrading 0) homogeneousCoordinateRing

private def projectiveStructureMap : projectiveLine ⟶ coefficientBase :=
  Proj.toSpecZero homogeneousGrading

private instance projectiveStructureMap_isProper : IsProper projectiveStructureMap := by
  change IsProper (Proj.toSpecZero homogeneousGrading)
  infer_instance

private def affineStructureMap : affineLine ⟶ coefficientBase :=
  projectiveMap ≫ projectiveStructureMap

private theorem projectiveMap_preimage_first_chart :
    projectiveMap ⁻¹ᵁ Proj.basicOpen homogeneousGrading (MvPolynomial.X (0 : Fin 2)) = ⊤ := by
  change Proj.fromOfGlobalSections homogeneousGrading sectionEvaluation map_irrelevant_eq_top
    ⁻¹ᵁ Proj.basicOpen homogeneousGrading (MvPolynomial.X (0 : Fin 2)) = ⊤
  rw [Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ Nat.zero_lt_one
    (coordinate_mem_degree_one 0)]
  simp [sectionEvaluation, coordinateEvaluation, coordinateValues]

private theorem projectiveMap_preimage_second_chart :
    projectiveMap ⁻¹ᵁ Proj.basicOpen homogeneousGrading (MvPolynomial.X (1 : Fin 2)) =
      coordinateOpen := by
  change Proj.fromOfGlobalSections homogeneousGrading sectionEvaluation map_irrelevant_eq_top
    ⁻¹ᵁ Proj.basicOpen homogeneousGrading (MvPolynomial.X (1 : Fin 2)) = coordinateOpen
  rw [Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ Nat.zero_lt_one
    (coordinate_mem_degree_one 1)]
  change affineLine.basicOpen
    ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℚ))).inv
      (coordinateEvaluation (MvPolynomial.X (1 : Fin 2)))) = coordinateOpen
  rw [show coordinateEvaluation (MvPolynomial.X (1 : Fin 2)) = Polynomial.X by
    simp [coordinateEvaluation, coordinateValues]]
  exact basicOpen_eq_of_affine (R := CommRingCat.of (Polynomial ℚ)) Polynomial.X

private theorem origin_image_coordinates :
    MvPolynomial.X (0 : Fin 2) ∉ (projectiveMap origin).asHomogeneousIdeal ∧
      MvPolynomial.X (1 : Fin 2) ∈ (projectiveMap origin).asHomogeneousIdeal := by
  have h0 : origin ∈
      projectiveMap ⁻¹ᵁ Proj.basicOpen homogeneousGrading (MvPolynomial.X (0 : Fin 2)) := by
    rw [projectiveMap_preimage_first_chart]
    trivial
  have h1 : origin ∉
      projectiveMap ⁻¹ᵁ Proj.basicOpen homogeneousGrading (MvPolynomial.X (1 : Fin 2)) := by
    rw [projectiveMap_preimage_second_chart]
    exact origin_not_mem_coordinateOpen
  change MvPolynomial.X (0 : Fin 2) ∉ (projectiveMap origin).asHomogeneousIdeal at h0
  change ¬¬ MvPolynomial.X (1 : Fin 2) ∈ (projectiveMap origin).asHomogeneousIdeal at h1
  exact ⟨h0, not_not.mp h1⟩

private theorem projectiveMap_not_constant :
    ¬ ∃ y : projectiveLine, ∀ x : affineLine, projectiveMap x = y := by
  rintro ⟨y, hy⟩
  obtain ⟨z, hz⟩ := coordinateOpen_dense.nonempty
  have hz' : projectiveMap z ∈
      Proj.basicOpen homogeneousGrading (MvPolynomial.X (1 : Fin 2)) := by
    change z ∈ projectiveMap ⁻¹ᵁ Proj.basicOpen homogeneousGrading (MvPolynomial.X (1 : Fin 2))
    rw [projectiveMap_preimage_second_chart]
    exact hz
  have h0 : projectiveMap origin ∉
      Proj.basicOpen homogeneousGrading (MvPolynomial.X (1 : Fin 2)) := by
    change origin ∉
      projectiveMap ⁻¹ᵁ Proj.basicOpen homogeneousGrading (MvPolynomial.X (1 : Fin 2))
    rw [projectiveMap_preimage_second_chart]
    exact origin_not_mem_coordinateOpen
  apply h0
  rw [hy origin, ← hy z]
  exact hz'

private def puncturedProjective : affineLine.PartialMap projectiveLine where
  domain := coordinateOpen
  dense_domain := coordinateOpen_dense
  hom := coordinateOpen.ι ≫ projectiveMap

private theorem puncturedProjective_extends_at_origin :
    IsIntegral affineLine ∧
    IsProper projectiveStructureMap ∧
    ValuationRing (affineLine.presheaf.stalk origin) ∧
    origin ∉ puncturedProjective.domain ∧
    puncturedProjective.domain ≠ ⊤ ∧
    (¬ ∃ y : projectiveLine, ∀ x : affineLine, projectiveMap x = y) ∧
    puncturedProjective.hom ≫ projectiveStructureMap =
      puncturedProjective.domain.ι ≫ affineStructureMap ∧
    ∃ q : affineLine.PartialMap projectiveLine,
      origin ∈ q.domain ∧
      q.hom ≫ projectiveStructureMap = q.domain.ι ≫ affineStructureMap ∧
      q.toRationalMap = puncturedProjective.toRationalMap ∧
      affineLine.homOfLE
          (inf_le_left : puncturedProjective.domain ⊓ q.domain ≤ puncturedProjective.domain) ≫
        puncturedProjective.hom =
      affineLine.homOfLE
          (inf_le_right : puncturedProjective.domain ⊓ q.domain ≤ q.domain) ≫ q.hom := by
  refine ⟨inferInstance, inferInstance, origin_valuationRing,
    origin_not_mem_coordinateOpen, coordinateOpen_ne_top, projectiveMap_not_constant, ?_, ?_⟩
  · exact Category.assoc _ _ _
  · refine ⟨projectiveMap.toPartialMap, by trivial, ?_, ?_, ?_⟩
    · change (affineLine.topIso.hom ≫ projectiveMap) ≫ projectiveStructureMap =
        (⊤ : affineLine.Opens).ι ≫ (projectiveMap ≫ projectiveStructureMap)
      simp only [Category.assoc, Scheme.topIso_hom]
    · apply Scheme.PartialMap.toRationalMap_eq_iff.mpr
      refine ⟨coordinateOpen, coordinateOpen_dense, le_top, le_rfl, ?_⟩
      change affineLine.homOfLE (show coordinateOpen ≤ ⊤ from le_top) ≫
          (affineLine.topIso.hom ≫ projectiveMap) =
        affineLine.homOfLE (show coordinateOpen ≤ coordinateOpen from le_rfl) ≫
          (coordinateOpen.ι ≫ projectiveMap)
      simp only [← Category.assoc, Scheme.topIso_hom, Scheme.homOfLE_ι,
        Scheme.homOfLE_rfl, Category.id_comp]
    · change affineLine.homOfLE (inf_le_left : coordinateOpen ⊓ ⊤ ≤ coordinateOpen) ≫
          (coordinateOpen.ι ≫ projectiveMap) =
        affineLine.homOfLE (inf_le_right : coordinateOpen ⊓ ⊤ ≤ ⊤) ≫
          (affineLine.topIso.hom ≫ projectiveMap)
      simp only [← Category.assoc, Scheme.topIso_hom, Scheme.homOfLE_ι]

private theorem generic_stalk_field_boundary :
    Order.coheight (genericPoint affineLine) = 0 ∧
    IsField (affineLine.presheaf.stalk (genericPoint affineLine)) ∧
    ValuationRing (affineLine.presheaf.stalk (genericPoint affineLine)) := by
  refine ⟨?_, ?_, ?_⟩
  · change Order.coheight (⊤ : affineLine) = 0
    exact Order.coheight_top affineLine
  · change IsField affineLine.functionField
    exact Field.toIsField _
  · change ValuationRing affineLine.functionField
    infer_instance

/-- Apply the valuation-stalk extension theorem to the nonconstant punctured-line map.
The original representative omits the origin, whereas the resulting one is defined there. -/
private theorem puncturedProjective_extension_via_valuation_stalk :
    origin ∉ puncturedProjective.domain ∧
    ∃ q : affineLine.PartialMap projectiveLine,
      origin ∈ q.domain ∧ q.toRationalMap = puncturedProjective.toRationalMap := by
  refine ⟨origin_not_mem_coordinateOpen, ?_⟩
  let : ValuationRing (affineLine.presheaf.stalk origin) := origin_valuationRing
  obtain ⟨q, hxq, _, hqrat, _⟩ :=
    Scheme.PartialMap.exists_extension_of_valuationRing_stalk
      affineStructureMap projectiveStructureMap puncturedProjective
      (Category.assoc _ _ _) origin
  exact ⟨q, hxq, hqrat⟩

end SchemePropertiesTest.RationalMapValuativeExtension
