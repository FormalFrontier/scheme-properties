/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.LocallyNormalRing.Maximal
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Ring.PUnit

/-!
# Maximal-localization clients

The integers satisfy the maximal-localization criterion using their stock domain
and GCD structure, and have a maximal ideal. The zero ring `PUnit` has empty prime
spectrum, so its independently constructed local normality gives the maximal
condition as well.
-/

namespace SchemePropertiesExamples.LocallyNormalRing

private theorem int_locallyNormalRing_and_exists_maximal :
    IsLocallyNormalRing ℤ ∧ ∃ m : Ideal ℤ, m.IsMaximal := by
  refine ⟨?_, Ideal.exists_maximal ℤ⟩
  apply (isLocallyNormalRing_iff_localization_maximal ℤ).mpr
  intro m hm
  exact ⟨IsLocalization.isDomain_of_atPrime (Localization.AtPrime m) m,
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime m) m.primeCompl
      m.primeCompl_le_nonZeroDivisors⟩

private theorem punit_localization_maximal :
    ∀ (m : Ideal PUnit) [m.IsMaximal],
      IsDomain (Localization.AtPrime m) ∧ IsIntegrallyClosed (Localization.AtPrime m) := by
  have h : IsLocallyNormalRing PUnit :=
    { isDomain_atPrime := fun p ↦ isEmptyElim p
      isIntegrallyClosed_atPrime := fun p ↦ isEmptyElim p }
  exact (isLocallyNormalRing_iff_localization_maximal PUnit).mp h

end SchemePropertiesExamples.LocallyNormalRing
