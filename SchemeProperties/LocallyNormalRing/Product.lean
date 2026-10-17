/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.NormalLocalization
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Binary products of locally normal rings

For commutative rings `R : Type u` and `S : Type v`, the canonical product `R × S`
is locally normal exactly when both factors are locally normal. The universes
`u` and `v` are independent. Either factor may be the zero ring; no domain,
Noetherian or nontriviality hypothesis is required.

## Main results

* `Prod.isLocallyNormalRing` is the instance that constructs local normality of
  `R × S` from local normality of both `R` and `S`.
* `IsLocallyNormalRing.of_prod_left` and `IsLocallyNormalRing.of_prod_right`
  descend local normality of `R × S` to each factor. They are theorems, not
  instances, so they do not introduce typeclass search loops.
* `isLocallyNormalRing_prod_iff` combines these directions into the criterion.

## Implementation notes

The product proof splits a prime of `R × S` according to the product-spectrum
decomposition, then identifies its prime localization with the corresponding
factor's prime localization by a ring equivalence. The projections to `R` and
`S` are localizations away from `(1, 0)` and `(0, 1)`, respectively. Descent
reuses `IsLocallyNormalRing.of_isLocalization` for these projection localizations.

The related finite indexed-product theorem `IsLocallyNormalRing.pi` in
`SchemeProperties.NormalEtale` treats a dependent family whose factor carriers
share one common universe; its index type may lie in a different universe.
Here the binary carrier `R × S` is handled directly, without a Pi encoding or
universe lifts.

## References

* Mathlib's product-spectrum API: `PrimeSpectrum.primeSpectrumProd`,
  `PrimeSpectrum.primeSpectrumProd_symm_inl` and `PrimeSpectrum.primeSpectrumProd_symm_inr`.
* Mathlib's projection localizations: `IsLocalization.away_fst` and `IsLocalization.away_snd`.
-/

@[expose] public section

universe u v

noncomputable section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

private def localizationAtPrimeFstEquiv (S : Type v) [CommRing S]
    (p : PrimeSpectrum R) :
    Localization.AtPrime (p.asIdeal.comap (RingHom.fst R S)) ≃+*
      Localization.AtPrime p.asIdeal := by
  let _ : Algebra (R × S) R := (RingHom.fst R S).toAlgebra
  let _ : IsScalarTower (R × S) R (Localization.AtPrime p.asIdeal) := inferInstance
  let _ : IsLocalization.Away ((1, 0) : R × S) R := IsLocalization.away_fst
  let _ : IsLocalization.AtPrime (Localization.AtPrime p.asIdeal)
      (p.asIdeal.comap (RingHom.fst R S)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers ((1, 0) : R × S)) (Localization.AtPrime p.asIdeal) p.asIdeal
  exact (IsLocalization.algEquiv (p.asIdeal.comap (RingHom.fst R S)).primeCompl
      (Localization.AtPrime (p.asIdeal.comap (RingHom.fst R S)))
      (Localization.AtPrime p.asIdeal)).toRingEquiv

private def localizationAtPrimeSndEquiv (R : Type u) [CommRing R]
    (p : PrimeSpectrum S) :
    Localization.AtPrime (p.asIdeal.comap (RingHom.snd R S)) ≃+*
      Localization.AtPrime p.asIdeal := by
  let _ : Algebra (R × S) S := (RingHom.snd R S).toAlgebra
  let _ : IsScalarTower (R × S) S (Localization.AtPrime p.asIdeal) := inferInstance
  let _ : IsLocalization.Away ((0, 1) : R × S) S := IsLocalization.away_snd
  let _ : IsLocalization.AtPrime (Localization.AtPrime p.asIdeal)
      (p.asIdeal.comap (RingHom.snd R S)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers ((0, 1) : R × S)) (Localization.AtPrime p.asIdeal) p.asIdeal
  exact (IsLocalization.algEquiv (p.asIdeal.comap (RingHom.snd R S)).primeCompl
      (Localization.AtPrime (p.asIdeal.comap (RingHom.snd R S)))
      (Localization.AtPrime p.asIdeal)).toRingEquiv

private theorem normal_atPrime_prod [IsLocallyNormalRing R] [IsLocallyNormalRing S]
    (p : PrimeSpectrum (R × S)) :
    IsDomain (Localization.AtPrime p.asIdeal) ∧
      IsIntegrallyClosed (Localization.AtPrime p.asIdeal) := by
  obtain ⟨q, rfl⟩ := (PrimeSpectrum.primeSpectrumProd R S).symm.surjective p
  rcases q with q | q
  · rw [PrimeSpectrum.primeSpectrumProd_symm_inl]
    let _ : IsDomain (Localization.AtPrime q.asIdeal) :=
      IsLocallyNormalRing.isDomain_atPrime q
    let _ : IsIntegrallyClosed (Localization.AtPrime q.asIdeal) :=
      IsLocallyNormalRing.isIntegrallyClosed_atPrime q
    let e := localizationAtPrimeFstEquiv S q
    exact And.intro (e.toMulEquiv.isDomain _) (IsIntegrallyClosed.of_equiv e.symm)
  · rw [PrimeSpectrum.primeSpectrumProd_symm_inr]
    let _ : IsDomain (Localization.AtPrime q.asIdeal) :=
      IsLocallyNormalRing.isDomain_atPrime q
    let _ : IsIntegrallyClosed (Localization.AtPrime q.asIdeal) :=
      IsLocallyNormalRing.isIntegrallyClosed_atPrime q
    let e := localizationAtPrimeSndEquiv R q
    exact And.intro (e.toMulEquiv.isDomain _) (IsIntegrallyClosed.of_equiv e.symm)

/-- The product of two locally normal commutative rings is locally normal. -/
instance Prod.isLocallyNormalRing [IsLocallyNormalRing R] [IsLocallyNormalRing S] :
    IsLocallyNormalRing (R × S) where
  isDomain_atPrime p := (normal_atPrime_prod p).1
  isIntegrallyClosed_atPrime p := (normal_atPrime_prod p).2

/-- The left factor of a locally normal product is locally normal. -/
theorem IsLocallyNormalRing.of_prod_left (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [IsLocallyNormalRing (R × S)] :
    IsLocallyNormalRing R := by
  let _ : Algebra (R × S) R := (RingHom.fst R S).toAlgebra
  let _ : IsLocalization.Away ((1, 0) : R × S) R := IsLocalization.away_fst
  exact IsLocallyNormalRing.of_isLocalization (Submonoid.powers ((1, 0) : R × S)) R

/-- The right factor of a locally normal product is locally normal. -/
theorem IsLocallyNormalRing.of_prod_right (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [IsLocallyNormalRing (R × S)] :
    IsLocallyNormalRing S := by
  let _ : Algebra (R × S) S := (RingHom.snd R S).toAlgebra
  let _ : IsLocalization.Away ((0, 1) : R × S) S := IsLocalization.away_snd
  exact IsLocallyNormalRing.of_isLocalization (Submonoid.powers ((0, 1) : R × S)) S

/-- A product is locally normal exactly when both of its factors are locally normal. -/
theorem isLocallyNormalRing_prod_iff (R : Type u) (S : Type v) [CommRing R] [CommRing S] :
    IsLocallyNormalRing (R × S) ↔ IsLocallyNormalRing R ∧ IsLocallyNormalRing S := by
  constructor
  · intro h
    let _ := h
    exact ⟨IsLocallyNormalRing.of_prod_left R S, IsLocallyNormalRing.of_prod_right R S⟩
  · rintro ⟨hR, hS⟩
    let _ := hR
    let _ := hS
    infer_instance
