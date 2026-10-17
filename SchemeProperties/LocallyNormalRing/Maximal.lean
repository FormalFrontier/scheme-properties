/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.Normal

@[expose] public section

/-!
# Local normality at maximal ideals

A commutative ring is locally normal if and only if its localizations at maximal
ideals are domains and integrally closed. No nontriviality or finiteness assumption
is needed.
-/

universe u

/-- A commutative ring is locally normal if and only if its localizations at
maximal ideals are domains and integrally closed. -/
theorem isLocallyNormalRing_iff_localization_maximal (R : Type u) [CommRing R] :
    IsLocallyNormalRing R ↔
      ∀ (m : Ideal R) [m.IsMaximal],
        IsDomain (Localization.AtPrime m) ∧ IsIntegrallyClosed (Localization.AtPrime m) := by
  constructor
  · intro h m hm
    let _ : IsLocallyNormalRing R := h
    exact ⟨IsLocallyNormalRing.isDomain_atPrime ⟨m, inferInstance⟩,
      IsLocallyNormalRing.isIntegrallyClosed_atPrime ⟨m, inferInstance⟩⟩
  · intro h
    have hp : ∀ p : PrimeSpectrum R,
        IsDomain (Localization.AtPrime p.asIdeal) ∧
          IsIntegrallyClosed (Localization.AtPrime p.asIdeal) := by
      intro p
      obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
      let _ : m.IsMaximal := hm
      let _ : IsDomain (Localization.AtPrime m) := (h m).1
      let _ : IsIntegrallyClosed (Localization.AtPrime m) := (h m).2
      exact ⟨IsLocalization.AtPrime.isDomain_of_le
        (R := R) (Localization.AtPrime m) (Localization.AtPrime p.asIdeal) hpm,
        IsLocalization.AtPrime.isIntegrallyClosed_of_le
          (R := R) (Localization.AtPrime m) (Localization.AtPrime p.asIdeal) hpm⟩
    exact
      { isDomain_atPrime := fun p ↦ (hp p).1
        isIntegrallyClosed_atPrime := fun p ↦ (hp p).2 }
