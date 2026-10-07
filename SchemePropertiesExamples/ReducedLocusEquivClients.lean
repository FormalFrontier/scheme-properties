/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.ReducedLocusEquiv
public import SchemeProperties.PolynomialPointPrime
import Mathlib.Algebra.Ring.ULift

@[expose] public section

set_option warningAsError true

/-!
# Clients of ring-equivalence reduced-locus transport

The examples apply prime-localization transport across a genuinely
universe-changing ring equivalence.
-/

open scoped Polynomial

namespace PrimeSpectrum

private noncomputable def polynomialULiftEquiv : ULift.{1} ℚ[X] ≃+* ℚ[X] :=
  ULift.ringEquiv

private noncomputable def polynomialULiftEvalPrime : PrimeSpectrum (ULift.{1} ℚ[X]) :=
  (homeomorphOfRingEquiv polynomialULiftEquiv).symm
    (Polynomial.evalPrime (0 : ℚ))

/-- The evaluation prime on a universe-lifted polynomial ring has reduced
localization by prime-localization transport. -/
theorem ulift_polynomial_evalPrime_isReduced_atPrime : _root_.IsReduced
    (Localization.AtPrime
      ((homeomorphOfRingEquiv (ULift.ringEquiv : ULift.{1} ℚ[X] ≃+* ℚ[X])).symm
        (Polynomial.evalPrime (0 : ℚ))).asIdeal) := by
  change _root_.IsReduced (Localization.AtPrime polynomialULiftEvalPrime.asIdeal)
  apply (isReduced_atPrime_homeomorphOfRingEquiv_iff
    polynomialULiftEquiv polynomialULiftEvalPrime).mp
  infer_instance

/-- Openness is transported to the universe-lifted polynomial ring. -/
theorem ulift_polynomial_isOpen_reduced_atPrime :
    IsOpen {p : PrimeSpectrum (ULift.{1} ℚ[X]) |
    _root_.IsReduced (Localization.AtPrime p.asIdeal)} := by
  apply (isOpen_isReduced_atPrime_iff_ringEquiv polynomialULiftEquiv).mpr
  have heq : {p : PrimeSpectrum ℚ[X] |
      _root_.IsReduced (Localization.AtPrime p.asIdeal)} = Set.univ := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    infer_instance
  rw [heq]
  exact isOpen_univ

end PrimeSpectrum
