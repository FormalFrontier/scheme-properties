/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.PolynomialProjCoordinates

/-!
# Separation of coordinate points in polynomial projective spectra

A coordinate point belongs to the basic open at a variable exactly when that variable
is its coordinate. Distinct coordinates therefore give distinct underlying points over
any fixed coefficient prime. Consequently the total-degree polynomial projective spectrum
is nontrivial over any nontrivial commutative ring with a nontrivial variable type.
The variable type and coefficient ring have independent universes.

## Boundaries

The coefficient hypothesis is essential: over the zero ring there is no coefficient
prime and the projective spectrum is empty. The variable hypothesis is essential for
a uniform two-point assertion: with one variable over a field the projective spectrum
has one point. This does not assert that the one-variable spectrum is a singleton over
an arbitrary coefficient ring. These are assertions about underlying points, not equality
of scheme morphisms.

## References

The argument uses Mathlib's projective charts (Jujian Zhang and Andrew Yang), homogeneous
localizations and grading (Jujian Zhang, Eric Wieser and Johan Commelin), polynomial
evaluation (Johannes Hölzl, Johan Commelin and Mario Carneiro), and prime spectra
(Johan Commelin, Filippo A. E. Nuccio and Andrew Yang), through the coordinate-point API
of Formal Frontier Agents.
-/

@[expose] public section

namespace AlgebraicGeometry.Proj

universe u v

attribute [local instance] MvPolynomial.gradedAlgebra

variable {σ : Type v} {R : Type u} [CommRing R]

/-- A coordinate point belongs to a coordinate basic open exactly when the indices agree. -/
@[simp] theorem coordinatePoint_mem_basicOpen_iff (i j : σ) (p : PrimeSpectrum R) :
    coordinatePoint i p ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule σ R) (MvPolynomial.X j) ↔ i = j := by
  classical
  rw [coordinatePoint_eq_awayι]
  change PrimeSpectrum.comap (coordinateAwayEval i) p ∈
      (Proj.awayι (MvPolynomial.homogeneousSubmodule σ R) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one) ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule σ R) (MvPolynomial.X j) ↔ i = j
  rw [Proj.awayι_preimage_basicOpen (MvPolynomial.homogeneousSubmodule σ R)
    (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one
    (MvPolynomial.isHomogeneous_X R j) Nat.zero_lt_one]
  have hmem (a : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule σ R)
      (MvPolynomial.X i)) :
      PrimeSpectrum.comap (coordinateAwayEval i) p ∈ PrimeSpectrum.basicOpen a ↔
        coordinateAwayEval i a ∉ p.asIdeal := by
    simpa only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] using
      (PrimeSpectrum.mem_basicOpen a (PrimeSpectrum.comap (coordinateAwayEval i) p))
  refine (hmem _).trans ?_
  simp only [HomogeneousLocalization.Away.isLocalizationElem, pow_one]
  rw [coordinateAwayEval_mk, MvPolynomial.eval_X]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    exact iff_of_true p.isPrime.one_notMem rfl
  · rw [ite_eq_right (Ne.symm hij)]
    exact iff_of_false (not_not_intro p.asIdeal.zero_mem) hij

/-- Distinct coordinates give distinct points over the same coefficient prime. -/
theorem coordinatePoint_ne (i j : σ) (p : PrimeSpectrum R) (hij : i ≠ j) :
    coordinatePoint i p ≠ coordinatePoint j p := by
  intro h
  apply hij
  apply (coordinatePoint_mem_basicOpen_iff i j p).mp
  rw [h]
  exact coordinatePoint_mem_basicOpen j p

/-- The total-degree polynomial projective spectrum has at least two underlying points
when the coefficient ring and variable type are nontrivial. -/
theorem nontrivial_mvPolynomial [Nontrivial σ] [Nontrivial R] :
    Nontrivial (Proj (MvPolynomial.homogeneousSubmodule σ R)) := by
  classical
  obtain ⟨i, j, hij⟩ := exists_pair_ne σ
  let p : PrimeSpectrum R := Classical.choice inferInstance
  exact ⟨⟨coordinatePoint i p, coordinatePoint j p, coordinatePoint_ne i j p hij⟩⟩

end AlgebraicGeometry.Proj
