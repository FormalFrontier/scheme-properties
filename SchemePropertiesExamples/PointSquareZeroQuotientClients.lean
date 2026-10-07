/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.PolynomialPointSquareZeroReducedLocus
public import SchemePropertiesExamples.PointSquareZeroQuotientFixtures

@[expose] public section

set_option warningAsError true

/-!
# Clients of the polynomial point-quotient reduced-locus criterion

These instances apply the full prime-localization criterion. The family
separation, finite or infinite images, and nilpotence witnesses come from
independently proved fixtures.
-/

namespace MvPolynomial

/-- The empty point quotient has an open reduced-prime-localization locus. -/
example : IsOpen {p : PrimeSpectrum (pointSquareZeroQuotient rationalEmptyPoints) |
    _root_.IsReduced (Localization.AtPrime p.asIdeal)} :=
  (isOpen_reduced_atPrime_pointSquareZeroQuotient_iff_finite_range
    rationalEmptyPoints rationalEmptyPoints_injective_and_finite.1).mpr
      rationalEmptyPoints_injective_and_finite.2

/-- The singleton point quotient has an open reduced locus, but contains a
nonzero nilpotent coordinate. -/
example : IsOpen {p : PrimeSpectrum (pointSquareZeroQuotient rationalSingletonPoints) |
    _root_.IsReduced (Localization.AtPrime p.asIdeal)} ∧
    ∃ x : pointSquareZeroQuotient rationalSingletonPoints, x ≠ 0 ∧ x ^ 2 = 0 := by
  refine ⟨(isOpen_reduced_atPrime_pointSquareZeroQuotient_iff_finite_range
    rationalSingletonPoints rationalSingletonPoints_injective_and_finite.1).mpr
      rationalSingletonPoints_injective_and_finite.2, ?_⟩
  exact ⟨Ideal.Quotient.mk (pointSquareZeroIdeal rationalSingletonPoints)
    (X (some (PUnit.unit : PUnit.{1}))), rationalSingletonPoints_nonzero_nilpotent⟩

/-- Two rational point coordinates give an open reduced locus. -/
example : IsOpen {p : PrimeSpectrum (pointSquareZeroQuotient rationalTwoPoints) |
    _root_.IsReduced (Localization.AtPrime p.asIdeal)} :=
  (isOpen_reduced_atPrime_pointSquareZeroQuotient_iff_finite_range
    rationalTwoPoints rationalTwoPoints_injective_and_finite.1).mpr
      rationalTwoPoints_injective_and_finite.2

/-- An infinite injective family gives a non-open full prime-localization locus. -/
theorem rationalPositivePoints_not_isOpen_reduced_atPrime :
    ¬ IsOpen {p : PrimeSpectrum (pointSquareZeroQuotient rationalPositivePoints) |
    _root_.IsReduced (Localization.AtPrime p.asIdeal)} := by
  intro hopen
  exact rationalPositivePoints_injective_and_infinite.2
    ((isOpen_reduced_atPrime_pointSquareZeroQuotient_iff_finite_range
      rationalPositivePoints rationalPositivePoints_injective_and_infinite.1).mp hopen)

/-- The infinite counterexample also has a genuinely larger index universe. -/
example : ¬ IsOpen {p : PrimeSpectrum
    (pointSquareZeroQuotient
      (fun i : ULift.{1} ℕ => rationalPositivePoints i.down)) |
    _root_.IsReduced (Localization.AtPrime p.asIdeal)} := by
  intro hopen
  exact rationalULiftPositivePoints_injective_and_infinite.2
    ((isOpen_reduced_atPrime_pointSquareZeroQuotient_iff_finite_range
      (fun i : ULift.{1} ℕ => rationalPositivePoints i.down)
      rationalULiftPositivePoints_injective_and_infinite.1).mp hopen)

end MvPolynomial
