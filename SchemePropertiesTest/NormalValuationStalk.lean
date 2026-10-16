/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import SchemeProperties.NormalValuationStalk

/-!
# Examples of valuation stalks

The closed point `(2)` of `Spec ℤ` has coheight one, and the valuation-stalk theorem
applies using the normal-spectrum and Noetherian-stalk instances. The spectrum of
an arbitrary field tests the coheight-zero boundary, where the stalk is a field.
Coheight computations reuse Mathlib's ideal-height and order characterizations.
-/

open AlgebraicGeometry

universe u

namespace SchemePropertiesTest.NormalValuationStalk

private theorem valuationRing_stalk_at_two :
    ∃ x : Spec (.of ℤ),
      x.asIdeal = Ideal.span {(2 : ℤ)} ∧ Order.coheight x = 1 ∧
      ValuationRing ((Spec (.of ℤ)).presheaf.stalk x) := by
  have htwo : Prime (2 : ℤ) := Int.prime_two
  let x : Spec (.of ℤ) :=
    ⟨Ideal.span {(2 : ℤ)}, (Ideal.span_singleton_prime htwo.ne_zero).mpr htwo⟩
  have hx : Order.coheight x = 1 := by
    rw [← idealHeight_eq_coheight]
    exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr htwo.ne_zero) htwo.not_isUnit
  exact ⟨x, rfl, hx, valuationRing_stalk_of_coheight_le_one x hx.le⟩

private theorem field_stalk_boundary (K : Type u) [Field K] (x : Spec (.of K)) :
    IsField ((Spec (.of K)).presheaf.stalk x) ∧ Order.coheight x = 0 ∧
      ValuationRing ((Spec (.of K)).presheaf.stalk x) := by
  have hx : Order.coheight x = 0 := Order.coheight_eq_zero.mpr (by
    intro y _
    exact le_of_eq (Subsingleton.elim _ _))
  letI : Ring.KrullDimLE 0 ((Spec (.of K)).presheaf.stalk x) :=
    krullDimLE_of_coheight_le hx.le
  exact ⟨Ring.KrullDimLE.isField_of_isDomain, hx,
    valuationRing_stalk_of_coheight_le_one x (by simp [hx])⟩

end SchemePropertiesTest.NormalValuationStalk
