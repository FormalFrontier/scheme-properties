/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.Normal
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Polynomial.IsIntegral

public section

set_option warningAsError true

/-!
# Polynomial rings over locally normal rings

This file proves that polynomial rings, and multivariate polynomial rings in
finitely many variables, are locally normal over a locally normal base.
-/

open scoped Polynomial

universe u

noncomputable section

/-- A polynomial ring over a locally normal ring is locally normal. -/
instance Polynomial.isLocallyNormalRing_of_isLocallyNormalRing
    {R : Type u} [CommRing R] [IsLocallyNormalRing R] :
    IsLocallyNormalRing R[X] := by
  constructor
  · intro p
    let q := p.asIdeal.comap Polynomial.C
    let S := (Localization.AtPrime q)[X]
    let pc := Submonoid.map Polynomial.C.toMonoidHom q.primeCompl
    let _ : Algebra R[X] S := Polynomial.algebra R (Localization.AtPrime q)
    have _ : IsLocalization pc S := Polynomial.isLocalization _ _
    let pS := p.asIdeal.map (algebraMap R[X] S)
    have disj : Disjoint (pc : Set R[X]) (p.asIdeal : Set R[X]) := by
      simpa [pc, q] using! Set.disjoint_image_left.mpr
        (Set.disjoint_compl_left_iff_subset.mpr (fun _ a ↦ a))
    have _ : pS.IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint pc _ _ inferInstance disj
    have _ : IsLocalization.AtPrime (Localization.AtPrime pS) p.asIdeal := by
      convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization pc
        (Localization.AtPrime pS) pS
      exact (IsLocalization.under_map_of_isPrime_disjoint pc _ inferInstance disj).symm
    let _ : IsDomain (Localization.AtPrime q) :=
      IsLocallyNormalRing.isDomain_atPrime ⟨q, inferInstance⟩
    let _ : IsIntegrallyClosed (Localization.AtPrime q) :=
      IsLocallyNormalRing.isIntegrallyClosed_atPrime ⟨q, inferInstance⟩
    let _ : IsDomain S := inferInstance
    let _ : IsIntegrallyClosed S := inferInstance
    let _ : IsDomain (Localization.AtPrime pS) :=
      IsLocalization.isDomain_of_atPrime _ pS
    exact (IsLocalization.algEquiv p.asIdeal.primeCompl
      (Localization.AtPrime pS) (Localization.AtPrime p.asIdeal)).symm.toMulEquiv.isDomain _
  · intro p
    let q := p.asIdeal.comap Polynomial.C
    let S := (Localization.AtPrime q)[X]
    let pc := Submonoid.map Polynomial.C.toMonoidHom q.primeCompl
    let _ : Algebra R[X] S := Polynomial.algebra R (Localization.AtPrime q)
    have _ : IsLocalization pc S := Polynomial.isLocalization _ _
    let pS := p.asIdeal.map (algebraMap R[X] S)
    have disj : Disjoint (pc : Set R[X]) (p.asIdeal : Set R[X]) := by
      simpa [pc, q] using! Set.disjoint_image_left.mpr
        (Set.disjoint_compl_left_iff_subset.mpr (fun _ a ↦ a))
    have _ : pS.IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint pc _ _ inferInstance disj
    have _ : IsLocalization.AtPrime (Localization.AtPrime pS) p.asIdeal := by
      convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization pc
        (Localization.AtPrime pS) pS
      exact (IsLocalization.under_map_of_isPrime_disjoint pc _ inferInstance disj).symm
    let _ : IsDomain (Localization.AtPrime q) :=
      IsLocallyNormalRing.isDomain_atPrime ⟨q, inferInstance⟩
    let _ : IsIntegrallyClosed (Localization.AtPrime q) :=
      IsLocallyNormalRing.isIntegrallyClosed_atPrime ⟨q, inferInstance⟩
    let _ : IsDomain S := inferInstance
    let _ : IsIntegrallyClosed S := inferInstance
    let _ : IsIntegrallyClosed (Localization.AtPrime pS) :=
      isIntegrallyClosed_of_isLocalization _ pS.primeCompl
        pS.primeCompl_le_nonZeroDivisors
    exact IsIntegrallyClosed.of_equiv (R := Localization.AtPrime pS)
      (IsLocalization.algEquiv p.asIdeal.primeCompl
        (Localization.AtPrime pS) (Localization.AtPrime p.asIdeal)).toRingEquiv

/-- A multivariate polynomial ring in finitely many variables over a locally
normal ring is locally normal. -/
instance MvPolynomial.isLocallyNormalRing_of_isLocallyNormalRing
    {R : Type u} [CommRing R] [IsLocallyNormalRing R]
    {ι : Type*} [Finite ι] : IsLocallyNormalRing (MvPolynomial ι R) := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e H =>
      exact IsLocallyNormalRing.of_ringEquiv (MvPolynomial.renameEquiv R e).toRingEquiv
  | h_empty =>
      exact IsLocallyNormalRing.of_ringEquiv (MvPolynomial.isEmptyRingEquiv R _).symm
  | h_option IH =>
      exact IsLocallyNormalRing.of_ringEquiv
        (MvPolynomial.optionEquivLeft R _).toRingEquiv.symm
