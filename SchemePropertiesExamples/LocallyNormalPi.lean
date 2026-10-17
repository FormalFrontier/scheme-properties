/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.LocallyNormalRing.Pi
import Mathlib.Data.ZMod.Defs
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Local normality of finite products

Prime localizations of the product `Fin 2 → ℤ` and its coordinates are
integrally closed domains. The empty product and a zero factor illustrate that
local normality does not require a nonempty index or nontrivial factors.
-/

/-- Prime localizations of the product of two copies of `ℤ` and of a coordinate
are integrally closed domains. -/
private theorem integerPi_primeLocal
    (p : PrimeSpectrum (Fin 2 → ℤ)) (q : PrimeSpectrum ℤ) :
    (IsDomain (Localization.AtPrime p.asIdeal) ∧
      IsIntegrallyClosed (Localization.AtPrime p.asIdeal)) ∧
    (IsDomain (Localization.AtPrime q.asIdeal) ∧
      IsIntegrallyClosed (Localization.AtPrime q.asIdeal)) := by
  letI : IsLocallyNormalRing (Fin 2 → ℤ) :=
    (IsLocallyNormalRing.pi_iff (fun _ : Fin 2 ↦ ℤ)).mpr
      fun _ ↦ isLocallyNormalRing_of_isDomain ℤ
  letI : IsLocallyNormalRing ℤ :=
    IsLocallyNormalRing.of_pi (fun _ : Fin 2 ↦ ℤ) 0
  exact ⟨⟨inferInstance, inferInstance⟩, ⟨inferInstance, inferInstance⟩⟩

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
  letI : IsLocallyNormalRing (ZMod 1) :=
    { isDomain_atPrime p := isEmptyElim p
      isIntegrallyClosed_atPrime p := isEmptyElim p }
  letI : IsLocallyNormalRing (Fin 1 → ZMod 1) :=
    IsLocallyNormalRing.pi (fun _ : Fin 1 ↦ ZMod 1)
  exact ⟨inferInstance, IsLocallyNormalRing.of_pi (fun _ : Fin 1 ↦ ZMod 1) 0⟩
