/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.Normal

public section

set_option warningAsError true

/-!
# Localizations of locally normal rings

This file proves that arbitrary localizations preserve local normality.
-/

universe u v

noncomputable section

/-- Any localization of a locally normal ring is locally normal. -/
theorem IsLocallyNormalRing.of_isLocalization
    {R : Type u} [CommRing R] (M : Submonoid R) (S : Type v)
    [CommRing S] [Algebra R S] [IsLocalization M S]
    [IsLocallyNormalRing R] : IsLocallyNormalRing S := by
  constructor
  · intro p
    let q := p.asIdeal.comap (algebraMap R S)
    have _ : IsLocalization.AtPrime (Localization.AtPrime p.asIdeal) q :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
        (Localization.AtPrime p.asIdeal) p.asIdeal
    let _ : IsDomain (Localization.AtPrime q) :=
      IsLocallyNormalRing.isDomain_atPrime ⟨q, inferInstance⟩
    exact (IsLocalization.algEquiv q.primeCompl
      (Localization.AtPrime q)
      (Localization.AtPrime p.asIdeal)).symm.toMulEquiv.isDomain _
  · intro p
    let q := p.asIdeal.comap (algebraMap R S)
    have _ : IsLocalization.AtPrime (Localization.AtPrime p.asIdeal) q :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
        (Localization.AtPrime p.asIdeal) p.asIdeal
    let _ : IsIntegrallyClosed (Localization.AtPrime q) :=
      IsLocallyNormalRing.isIntegrallyClosed_atPrime ⟨q, inferInstance⟩
    exact IsIntegrallyClosed.of_equiv (R := Localization.AtPrime q) <|
      (IsLocalization.algEquiv q.primeCompl
        (Localization.AtPrime q)
        (Localization.AtPrime p.asIdeal)).toRingEquiv

/-- The canonical localization at any submonoid of a locally normal ring is
locally normal. -/
instance Localization.isLocallyNormalRing
    {R : Type u} [CommRing R] [IsLocallyNormalRing R] (M : Submonoid R) :
    IsLocallyNormalRing (Localization M) :=
  IsLocallyNormalRing.of_isLocalization M (Localization M)
