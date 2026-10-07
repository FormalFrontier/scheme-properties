/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.PointSquareZeroQuotient
public import SchemeProperties.PolynomialPointReducedLocus
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic.FinCases

@[expose] public section

set_option warningAsError true

/-!
# Rational polynomial point-quotient boundary families

The empty, singleton, two-point and infinite families meet the separation
condition for the polynomial point-quotient equivalence. Their image finiteness
is checked independently of any reduced-locus transport. A singleton coordinate
is nonzero and square-zero, even though the corresponding family is finite.

## References

* Multivariate Polynomials' point-square-zero presentation and forward map.
* Mathlib's direct-sum and polynomial-evaluation APIs.
-/

open scoped Polynomial TrivSqZeroExt

namespace MvPolynomial

universe u

/-- The empty family of rational points. -/
def rationalEmptyPoints : Empty → ℚ := Empty.elim

/-- The singleton family supported at zero. -/
def rationalSingletonPoints : PUnit.{1} → ℚ := fun _ => 0

/-- Two distinct rational points, zero and one. -/
def rationalTwoPoints (i : Fin 2) : ℚ := if i = 0 then 0 else 1

/-- An infinite family of pairwise distinct positive integer points. -/
def rationalPositivePoints (n : ℕ) : ℚ := ((n + 1 : ℕ) : ℚ)

/-- Vacuous injectivity and finite image for the empty family. -/
theorem rationalEmptyPoints_injective_and_finite :
    Function.Injective rationalEmptyPoints ∧ (Set.range rationalEmptyPoints).Finite := by
  constructor
  · intro i
    exact i.elim
  · exact Set.finite_range rationalEmptyPoints

/-- The singleton family is injective and has finite image. -/
theorem rationalSingletonPoints_injective_and_finite :
    Function.Injective rationalSingletonPoints ∧
      (Set.range rationalSingletonPoints).Finite := by
  constructor
  · intro i j _
    exact Subsingleton.elim i j
  · exact Set.finite_range rationalSingletonPoints

/-- The two-point family is injective and has finite image. -/
theorem rationalTwoPoints_injective_and_finite :
    Function.Injective rationalTwoPoints ∧ (Set.range rationalTwoPoints).Finite := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [rationalTwoPoints]
  · exact Set.finite_range rationalTwoPoints

/-- The positive rational points form an injective family with infinite image. -/
theorem rationalPositivePoints_injective_and_infinite :
    Function.Injective rationalPositivePoints ∧
      (Set.range rationalPositivePoints).Infinite := by
  have hinjective : Function.Injective rationalPositivePoints := by
    intro m n h
    exact Nat.add_right_cancel (Nat.cast_injective h)
  exact ⟨hinjective, Set.infinite_range_of_injective hinjective⟩

/-- A higher-universe index type still permits an injective infinite family
over the small field of rationals. -/
theorem rationalULiftPositivePoints_injective_and_infinite :
    Function.Injective (fun i : ULift.{u} ℕ => rationalPositivePoints i.down) ∧
      (Set.range (fun i : ULift.{u} ℕ => rationalPositivePoints i.down)).Infinite := by
  have hinjective : Function.Injective
      (fun i : ULift.{u} ℕ => rationalPositivePoints i.down) := by
    intro i j h
    exact ULift.down_injective
      (rationalPositivePoints_injective_and_infinite.1 h)
  exact ⟨hinjective, Set.infinite_range_of_injective hinjective⟩

/-- A nonzero square-zero coordinate survives in the singleton quotient. -/
theorem rationalSingletonPoints_nonzero_nilpotent :
    (Ideal.Quotient.mk (pointSquareZeroIdeal rationalSingletonPoints)
      (X (some (PUnit.unit : PUnit.{1})))) ≠ 0 ∧
    (Ideal.Quotient.mk (pointSquareZeroIdeal rationalSingletonPoints)
      (X (some (PUnit.unit : PUnit.{1})))) ^ 2 = 0 := by
  have hunit :
      (Ideal.Quotient.mk (RingHom.ker
          (Polynomial.evalRingHom (rationalSingletonPoints PUnit.unit)))
        (1 : ℚ[X])) ≠ 0 := by
    intro h
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp h
    simp [RingHom.mem_ker] at hmem
  constructor
  · intro h
    have hdelta : pointSquareZeroDelta rationalSingletonPoints PUnit.unit = 0 := by
      apply (TrivSqZeroExt.inr_injective (R := ℚ[X]))
      rw [← pointSquareZeroForward_mk_some, h, map_zero]
      rfl
    have hcomponent := congrArg
      (fun d : pointSquareZeroModule rationalSingletonPoints => d PUnit.unit) hdelta
    apply hunit
    simpa only [pointSquareZeroDelta, DirectSum.lof_apply,
      DFinsupp.zero_apply] using hcomponent
  · exact pointSquareZero_sq rationalSingletonPoints PUnit.unit

/-- For an injective rational family, field subtraction supplies the pairwise
unit differences needed by the released presentation equivalence. -/
private theorem rationalPoints_unit_sub_of_injective {ι : Type u}
    (a : ι → ℚ) (ha : Function.Injective a) :
    ∀ i j : ι, i ≠ j → IsUnit (a i - a j) := by
  intro i j hij
  exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (fun h => hij (ha h)))

/-- Separation is vacuous for the empty family. -/
example : ∀ i j : Empty, i ≠ j →
    IsUnit (rationalEmptyPoints i - rationalEmptyPoints j) :=
  rationalPoints_unit_sub_of_injective rationalEmptyPoints
    rationalEmptyPoints_injective_and_finite.1

/-- The singleton family satisfies separation even though its coordinate
is nonzero and square-zero in the quotient. -/
example : ∀ i j : PUnit.{1}, i ≠ j →
    IsUnit (rationalSingletonPoints i - rationalSingletonPoints j) :=
  rationalPoints_unit_sub_of_injective rationalSingletonPoints
    rationalSingletonPoints_injective_and_finite.1

/-- The zero and one rational points are unit-separated. -/
example : ∀ i j : Fin 2, i ≠ j →
    IsUnit (rationalTwoPoints i - rationalTwoPoints j) :=
  rationalPoints_unit_sub_of_injective rationalTwoPoints
    rationalTwoPoints_injective_and_finite.1

/-- The infinite positive rational family is pairwise unit-separated. -/
example : ∀ i j : ℕ, i ≠ j →
    IsUnit (rationalPositivePoints i - rationalPositivePoints j) :=
  rationalPoints_unit_sub_of_injective rationalPositivePoints
    rationalPositivePoints_injective_and_infinite.1

/-- The released presentation equivalence has the canonical square-zero
codomain used by the existing full-prime-locus criterion. This applies both
proved APIs without invoking a quotient reduced-locus transport theorem. -/
theorem rationalPoints_equiv_and_squareZero_locus_criterion
    {ι : Type u} (a : ι → ℚ) (ha : Function.Injective a) :
    Nonempty (pointSquareZeroQuotient a ≃ₐ[ℚ[X]]
      TrivSqZeroExt ℚ[X] (pointSquareZeroModule a)) ∧
    (IsOpen {p : PrimeSpectrum (TrivSqZeroExt ℚ[X] (pointSquareZeroModule a)) |
        _root_.IsReduced (Localization.AtPrime p.asIdeal)} ↔
      (Set.range a).Finite) := by
  exact ⟨⟨pointSquareZeroAlgEquiv a (rationalPoints_unit_sub_of_injective a ha)⟩,
    Polynomial.isOpen_reduced_atPrime_directSum_evalQuotient_iff_finite_range a⟩

/-- The separated infinite family also inhabits the canonical equivalence
and existing square-zero reduced-locus criterion. -/
example : Nonempty (pointSquareZeroQuotient rationalPositivePoints ≃ₐ[ℚ[X]]
    TrivSqZeroExt ℚ[X] (pointSquareZeroModule rationalPositivePoints)) ∧
    (IsOpen {p : PrimeSpectrum (TrivSqZeroExt ℚ[X]
        (pointSquareZeroModule rationalPositivePoints)) |
      _root_.IsReduced (Localization.AtPrime p.asIdeal)} ↔
        (Set.range rationalPositivePoints).Finite) :=
  rationalPoints_equiv_and_squareZero_locus_criterion rationalPositivePoints
    rationalPositivePoints_injective_and_infinite.1

end MvPolynomial
