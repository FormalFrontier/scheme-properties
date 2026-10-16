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
# Field and discrete valuation stalks

The point of `Spec ℚ` tests the coheight-zero field characterization and the
field-not-DVR boundary. The prime `(2)` of `Spec ℤ` tests the coheight-one DVR
characterization. The prime-height computation follows the valuation-stalk
example in `SchemePropertiesTest.NormalValuationStalk`, using Mathlib's
principal-ideal height theorem. Scheme coheight, rather than scheme height,
corresponds to prime-ideal height because the specialization order is reversed.
-/

open AlgebraicGeometry

namespace SchemePropertiesTest.StalkCoheight

private def rationalPoint : Spec (.of ℚ) := ⟨⊥, inferInstance⟩

private theorem rationalPoint_coheight : Order.coheight rationalPoint = 0 :=
  Order.coheight_eq_zero.mpr (by
    intro y _
    exact le_of_eq (Subsingleton.elim _ _))

private theorem rationalPoint_field_not_dvr :
    IsField ((Spec (.of ℚ)).presheaf.stalk rationalPoint) ∧
      ¬ IsDiscreteValuationRing ((Spec (.of ℚ)).presheaf.stalk rationalPoint) := by
  have hf := (isField_stalk_iff_coheight_eq_zero rationalPoint).mpr rationalPoint_coheight
  refine ⟨hf, fun h ↦ ?_⟩
  let := h
  exact IsDiscreteValuationRing.not_isField _ hf

private def integerPrimePoint : Spec (.of ℤ) :=
  ⟨Ideal.span {(2 : ℤ)}, (Ideal.span_singleton_prime Int.prime_two.ne_zero).mpr Int.prime_two⟩

private theorem integerPrimePoint_coheight : Order.coheight integerPrimePoint = 1 := by
  rw [← idealHeight_eq_coheight]
  exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr Int.prime_two.ne_zero) Int.prime_two.not_isUnit

private theorem integerPrimePoint_dvr :
    IsDiscreteValuationRing ((Spec (.of ℤ)).presheaf.stalk integerPrimePoint) :=
  (isDiscreteValuationRing_stalk_iff_coheight_eq_one integerPrimePoint).mpr
    integerPrimePoint_coheight

end SchemePropertiesTest.StalkCoheight
