/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.FlatStalkDimension
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Flat.Localization

/-!
# A field inside a formal discrete valuation ring

The constant inclusion `ℚ → ℚ⟦X⟧` is flat and local, with strictly increasing
Krull dimension `0 < 1`. Its spectrum map at the closed point gives a strict
stalk-dimension inequality. The dimension computations use Mathlib's field,
principal ideal domain, and affine stalk results, independently of the bounds.
Each of the five height and dimension bounds is used below on these objects.

The residue map of this DVR is local but not flat; its fraction-field map is
flat but not local. Both reverse the dimension inequality. The unit ideal
also tests the arbitrary-ideal bound at infinite height.

## References

Mathlib's `PowerSeries` supplies the formal DVR and its nonfield theorem;
`IsPrincipalIdealRing.ringKrullDim_eq_one` computes its dimension.
`idealHeight_eq_coheight` and `ringKrullDim_stalk_eq_coheight` give the affine
stalk computations. Flatness over a field and of localizations is from Mathlib.
-/

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace SchemePropertiesTest.FlatStalkDimension

private abbrev A := PowerSeries ℚ

private theorem constants_flat : (algebraMap ℚ A).Flat :=
  RingHom.Flat.of_isField (Field.toIsField ℚ) _

private theorem series_dimension : ringKrullDim A = 1 :=
  IsPrincipalIdealRing.ringKrullDim_eq_one A PowerSeries.not_isField

private theorem constants_strict : ringKrullDim ℚ < ringKrullDim A := by
  simp [series_dimension]

private theorem maximal_height : (IsLocalRing.maximalIdeal A).height = 1 :=
  IsPrincipalIdealRing.height_eq_one_of_isMaximal _ PowerSeries.not_isField

private theorem contracted_maximal_height_bound :
    ((IsLocalRing.maximalIdeal A).under ℚ).height ≤ 1 := by
  simpa only [maximal_height] using
    Ideal.height_under_le_of_hasGoingDown (R := ℚ) (IsLocalRing.maximalIdeal A)

private theorem unit_ideal_height_bound :
    ((⊤ : Ideal A).under ℚ).height ≤ (⊤ : Ideal A).height :=
  Ideal.height_under_le_of_hasGoingDown _

private theorem constants_generalizing_dimension_bound : ringKrullDim ℚ ≤ 1 := by
  rw [← series_dimension]
  exact (algebraMap ℚ A).ringKrullDim_le_of_generalizingMap
    constants_flat.generalizingMap_comap

private theorem constants_flat_dimension_bound : 0 ≤ ringKrullDim A := by
  rw [← ringKrullDim_eq_zero_of_field ℚ]
  exact constants_flat.ringKrullDim_le

private def closedPoint : Spec (.of A) :=
  ⟨IsLocalRing.maximalIdeal A, inferInstance⟩

private def constantsSpectrum : Spec (.of A) ⟶ Spec (.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ A))

private instance : Flat constantsSpectrum :=
  Flat.SpecMap_iff.mpr constants_flat

private theorem closedPoint_dimension :
    ringKrullDim ((Spec (.of A)).presheaf.stalk closedPoint) = 1 := by
  rw [ringKrullDim_stalk_eq_coheight, ← idealHeight_eq_coheight]
  change ((IsLocalRing.maximalIdeal A).height : WithBot ℕ∞) = 1
  simp [maximal_height]

private theorem image_stalk_dimension :
    ringKrullDim ((Spec (.of ℚ)).presheaf.stalk (constantsSpectrum closedPoint)) = 0 := by
  rw [ringKrullDim_stalk_eq_coheight]
  have h : Order.coheight (constantsSpectrum closedPoint) = 0 :=
    Order.coheight_eq_zero.mpr (fun _ _ ↦ le_of_eq (Subsingleton.elim _ _))
  simp [h]

private theorem closedPoint_pointwise_bound :
    ringKrullDim ((Spec (.of ℚ)).presheaf.stalk (constantsSpectrum closedPoint)) ≤ 1 := by
  rw [← closedPoint_dimension]
  exact constantsSpectrum.ringKrullDim_stalk_le_of_flat_stalkMap closedPoint
    (Flat.stalkMap constantsSpectrum closedPoint)

private theorem closedPoint_global_bound_and_strict :
    ringKrullDim ((Spec (.of ℚ)).presheaf.stalk (constantsSpectrum closedPoint)) ≤
        ringKrullDim ((Spec (.of A)).presheaf.stalk closedPoint) ∧
      ringKrullDim ((Spec (.of ℚ)).presheaf.stalk (constantsSpectrum closedPoint)) <
        ringKrullDim ((Spec (.of A)).presheaf.stalk closedPoint) := by
  refine ⟨Flat.ringKrullDim_stalk_le constantsSpectrum closedPoint, ?_⟩
  simp [image_stalk_dimension, closedPoint_dimension]

private theorem residue_dimension_drops :
    ringKrullDim (IsLocalRing.ResidueField A) < ringKrullDim A := by
  simp [series_dimension]

private theorem residue_not_flat : ¬ (IsLocalRing.residue A).Flat := by
  intro h
  exact (not_le_of_gt residue_dimension_drops) h.ringKrullDim_le

private theorem fraction_flat : (algebraMap A (FractionRing A)).Flat :=
  RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (nonZeroDivisors A))

private theorem fraction_dimension_drops :
    ringKrullDim (FractionRing A) < ringKrullDim A := by
  simp [series_dimension]

private theorem fraction_not_local : ¬ IsLocalHom (algebraMap A (FractionRing A)) := by
  intro h
  letI := h
  exact (not_le_of_gt fraction_dimension_drops) fraction_flat.ringKrullDim_le

end SchemePropertiesTest.FlatStalkDimension
