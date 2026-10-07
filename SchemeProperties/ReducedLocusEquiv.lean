/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.ReducedLocus
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Localization.AtPrime.Basic

@[expose] public section

set_option warningAsError true

/-!
# Reduced prime localizations under ring equivalences

An equivalence of commutative semirings identifies reducedness at corresponding
prime localizations and hence preserves openness of the reduced locus.

## References

* Mathlib's prime-spectrum homeomorphism and prime-localization APIs.
-/

namespace PrimeSpectrum

universe u v

section

/-- The prime localizations at corresponding primes under a ring equivalence
are reduced simultaneously. The two semirings may have independent universes. -/
theorem isReduced_atPrime_homeomorphOfRingEquiv_iff
    {A : Type u} {B : Type v} [CommSemiring A] [CommSemiring B]
    (e : A ≃+* B) (p : PrimeSpectrum A) :
    _root_.IsReduced (Localization.AtPrime
      (PrimeSpectrum.homeomorphOfRingEquiv e p).asIdeal) ↔
      _root_.IsReduced (Localization.AtPrime p.asIdeal) := by
  let localEquiv : Localization.AtPrime
      (homeomorphOfRingEquiv e p).asIdeal ≃+* Localization.AtPrime p.asIdeal :=
    Localization.localRingEquiv _ _ e.symm rfl
  constructor
  · intro h
    exact @isReduced_of_injective _ _ _ _ _ _ _ localEquiv.symm
      localEquiv.symm.injective h
  · intro h
    exact @isReduced_of_injective _ _ _ _ _ _ _ localEquiv
      localEquiv.injective h

/-- A ring equivalence preserves openness of the entire reduced prime-localization
locus, with no finiteness or reducedness assumption on the semirings. -/
theorem isOpen_isReduced_atPrime_iff_ringEquiv
    {A : Type u} {B : Type v} [CommSemiring A] [CommSemiring B]
    (e : A ≃+* B) :
    IsOpen {p : PrimeSpectrum A |
      _root_.IsReduced (Localization.AtPrime p.asIdeal)} ↔
    IsOpen {p : PrimeSpectrum B |
      _root_.IsReduced (Localization.AtPrime p.asIdeal)} := by
  let h := homeomorphOfRingEquiv e
  have hpreimage : h ⁻¹' {p : PrimeSpectrum B |
      _root_.IsReduced (Localization.AtPrime p.asIdeal)} =
      {p : PrimeSpectrum A |
        _root_.IsReduced (Localization.AtPrime p.asIdeal)} := by
    ext p
    simpa only [Set.mem_preimage, Set.mem_ofPred_eq] using
      (isReduced_atPrime_homeomorphOfRingEquiv_iff e p)
  rw [← hpreimage]
  exact h.isOpen_preimage

end

end PrimeSpectrum
