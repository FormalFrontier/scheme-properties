/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.LocallyNormalRing.Pi
public import SchemeProperties.LocallyNormalRing.Maximal
import Mathlib.Data.ZMod.Defs
public import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Local normality of finite products

Prime localizations of the product `Fin 2 → ℤ` and, independently, of `ℤ` are
integrally closed domains. The empty product and a zero factor illustrate that
local normality does not require a nonempty index or nontrivial factors.
-/

/-- Independently chosen prime localizations of the product of two copies of `ℤ`
and of `ℤ` are integrally closed domains. The integer prime is not computed from
the product prime. -/
public theorem IsLocallyNormalRing.int_pi_prime_localizations
    (p : PrimeSpectrum (Fin 2 → ℤ)) (q : PrimeSpectrum ℤ) :
    (IsDomain (Localization.AtPrime p.asIdeal) ∧
      IsIntegrallyClosed (Localization.AtPrime p.asIdeal)) ∧
    (IsDomain (Localization.AtPrime q.asIdeal) ∧
      IsIntegrallyClosed (Localization.AtPrime q.asIdeal)) := by
  let : IsLocallyNormalRing (Fin 2 → ℤ) :=
    (IsLocallyNormalRing.pi_iff (fun _ : Fin 2 ↦ ℤ)).mpr
      fun _ ↦ isLocallyNormalRing_of_isDomain ℤ
  let : IsLocallyNormalRing ℤ :=
    IsLocallyNormalRing.of_pi (fun _ : Fin 2 ↦ ℤ) 0
  exact ⟨⟨inferInstance, inferInstance⟩, ⟨inferInstance, inferInstance⟩⟩

-- The zero prime of `ℤ` pulls back to a prime of the nondomain product.
example :
    (IsDomain (Localization.AtPrime
      ((⊥ : Ideal ℤ).comap (Pi.evalRingHom (fun _ : Fin 2 ↦ ℤ) 0))) ∧
      IsIntegrallyClosed (Localization.AtPrime
        ((⊥ : Ideal ℤ).comap (Pi.evalRingHom (fun _ : Fin 2 ↦ ℤ) 0)))) ∧
    (IsDomain (Localization.AtPrime (⊥ : Ideal ℤ)) ∧
      IsIntegrallyClosed (Localization.AtPrime (⊥ : Ideal ℤ))) :=
  IsLocallyNormalRing.int_pi_prime_localizations
    (PrimeSpectrum.comap (Pi.evalRingHom (fun _ : Fin 2 ↦ ℤ) 0)
      ⟨⊥, Ideal.isPrime_bot⟩) ⟨⊥, Ideal.isPrime_bot⟩

/-- The empty product is a zero ring and is locally normal. -/
private theorem emptyPi_locallyNormal :
    Subsingleton (Fin 0 → ℤ) ∧ IsLocallyNormalRing (Fin 0 → ℤ) := by
  refine ⟨⟨fun f g ↦ funext fun i ↦ Fin.elim0 i⟩, ?_⟩
  exact (IsLocallyNormalRing.pi_iff (fun _ : Fin 0 ↦ ℤ)).mpr
    fun i ↦ Fin.elim0 i

/-- Local normality descends to the zero factor `ZMod 1`, whose prime spectrum
is empty. -/
private theorem zeroFactor_locallyNormal :
    Subsingleton (ZMod 1) ∧ IsLocallyNormalRing (ZMod 1) := by
  let : IsLocallyNormalRing (ZMod 1) :=
    { isDomain_atPrime p := isEmptyElim p
      isIntegrallyClosed_atPrime p := isEmptyElim p }
  let : IsLocallyNormalRing (Fin 1 → ZMod 1) :=
    IsLocallyNormalRing.pi (fun _ : Fin 1 ↦ ZMod 1)
  exact ⟨inferInstance, IsLocallyNormalRing.of_pi (fun _ : Fin 1 ↦ ZMod 1) 0⟩

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
