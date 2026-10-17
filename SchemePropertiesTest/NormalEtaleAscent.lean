/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.NormalEtale
import SchemeProperties.NormalLocalization
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

/-!
# The nonfinite étale localization of the integers away from two

The canonical algebra `ℤ → Localization.Away (2 : ℤ)` is étale and locally
normal, but not finite as a module. Its local normality is proved independently
by the localization theorem, independently of the étale-ascent theorems.

The final two private clients apply the étale-ascent theorems to this same algebra.
All preceding private data and proofs are independent of them.
The inverse element, localization map into `ℚ`, and integral-closedness argument
reuse Mathlib; source and target normality reuse `Normal` and `NormalLocalization`.
-/

noncomputable section

private theorem int_isDomain : IsDomain ℤ := inferInstance

private theorem int_isIntegrallyClosed : IsIntegrallyClosed ℤ := inferInstance

private theorem int_isLocallyNormalRing : IsLocallyNormalRing ℤ := by
  let _ : IsDomain ℤ := int_isDomain
  let _ : IsIntegrallyClosed ℤ := int_isIntegrallyClosed
  exact isLocallyNormalRing_of_isDomain ℤ

private theorem awayTwo_etale : Algebra.Etale ℤ (Localization.Away (2 : ℤ)) :=
  Algebra.Etale.of_isLocalizationAway (2 : ℤ)

private theorem awayTwo_isLocallyNormalRing :
    IsLocallyNormalRing (Localization.Away (2 : ℤ)) := by
  let _ : IsLocallyNormalRing ℤ := int_isLocallyNormalRing
  exact IsLocallyNormalRing.of_isLocalization (Submonoid.powers (2 : ℤ))
    (Localization.Away (2 : ℤ))

private def awayTwoInverse : Localization.Away (2 : ℤ) :=
  IsLocalization.Away.invSelf (2 : ℤ)

private theorem awayTwoInverse_spec :
    algebraMap ℤ (Localization.Away (2 : ℤ)) 2 * awayTwoInverse = 1 :=
  IsLocalization.Away.mul_invSelf (2 : ℤ)

private def awayTwoToRat : Localization.Away (2 : ℤ) →ₐ[ℤ] ℚ :=
  IsLocalization.Away.liftAlgHom (2 : ℤ) (f := Algebra.ofId ℤ ℚ)
    (by norm_num : IsUnit ((Algebra.ofId ℤ ℚ) (2 : ℤ)))

private theorem awayTwoToRat_mul_inverse : (2 : ℚ) * awayTwoToRat awayTwoInverse = 1 := by
  have htwo : awayTwoToRat (algebraMap ℤ (Localization.Away (2 : ℤ)) 2) = (2 : ℚ) := by
    rw [AlgHom.commutes]
    norm_num
  have h := congrArg awayTwoToRat awayTwoInverse_spec
  rw [map_mul, htwo, map_one] at h
  exact h

private theorem awayTwo_not_finite : ¬ Module.Finite ℤ (Localization.Away (2 : ℤ)) := by
  intro hfinite
  -- The integer-module instance and the localization algebra's module agree by
  -- uniqueness of the integer action; finiteness must use the latter here.
  let _ : @Module.Finite ℤ (Localization.Away (2 : ℤ)) _ _ Algebra.toModule := by
    convert hfinite using 1
    exact Subsingleton.elim _ _
  let _ : IsIntegrallyClosed ℤ := int_isIntegrallyClosed
  have hinverse : IsIntegral ℤ awayTwoInverse := IsIntegral.of_finite ℤ awayTwoInverse
  have hintegral : IsIntegral ℤ (awayTwoToRat awayTwoInverse) :=
    IsIntegral.map awayTwoToRat hinverse
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hintegral
  have hmul : (2 : ℤ) * z = 1 := by
    apply Rat.intCast_injective
    have hrat : (2 : ℚ) * (z : ℚ) = 1 := by
      simpa [← hz] using awayTwoToRat_mul_inverse
    simpa using hrat
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hmul with h | h <;> norm_num at h

-- These clients use étale ascent, separately from the localization witness above.
private theorem awayTwo_of_etale : IsLocallyNormalRing (Localization.Away (2 : ℤ)) := by
  let _ : IsLocallyNormalRing ℤ := int_isLocallyNormalRing
  let _ : Algebra.Etale ℤ (Localization.Away (2 : ℤ)) := awayTwo_etale
  exact IsLocallyNormalRing.of_etale (R := ℤ)

private theorem awayTwo_of_etale_of_isDomain :
    IsLocallyNormalRing (Localization.Away (2 : ℤ)) := by
  let _ : IsDomain ℤ := int_isDomain
  let _ : IsIntegrallyClosed ℤ := int_isIntegrallyClosed
  let _ : Algebra.Etale ℤ (Localization.Away (2 : ℤ)) := awayTwo_etale
  exact IsLocallyNormalRing.of_etale_of_isDomain (R := ℤ)
