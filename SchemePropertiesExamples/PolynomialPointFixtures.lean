/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.PolynomialPointPrime
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.RingTheory.ZMod

@[expose] public section

set_option warningAsError true

/-!
# Independent polynomial point-module boundary examples

The empty direct sum, distinct points, constant infinite families, and infinite
image are built without invoking the support or reduced-locus statements.
-/

namespace Polynomial

/-- An empty family has a zero direct sum of evaluation quotient modules. -/
example : Subsingleton
    (DirectSum Empty (fun _ => ℚ[X] ⧸ RingHom.ker (evalRingHom (0 : ℚ)))) :=
  inferInstance

/-- Evaluation quotients have a nonzero unit for every rational point. -/
example (x : ℚ) :
    (Ideal.Quotient.mk (RingHom.ker (evalRingHom x)) (1 : ℚ[X])) ≠ 0 := by
  intro h
  have hmem : (1 : ℚ[X]) ∈ RingHom.ker (evalRingHom x) :=
    (Ideal.Quotient.eq_zero_iff_mem).mp h
  have hzero : (1 : ℚ[X]).eval x = 0 := by
    simpa only [← evalPrime_asIdeal, mem_evalPrime_iff] using hmem
  simp at hzero

/-- Two distinct rational points give different evaluation primes. -/
theorem rational_evalPrime_zero_ne_one : evalPrime (0 : ℚ) ≠ evalPrime 1 := by
  intro h
  exact zero_ne_one ((evalPrime_injective h))

/-- A family can contain both distinct evaluation points and separate summands. -/
example : (if (0 : Fin 2) = 0 then (0 : ℚ) else 1) ≠
    (if (1 : Fin 2) = 0 then (0 : ℚ) else 1) := by
  simp

/-- An infinite indexing set can index infinitely many nonzero summands at one point. -/
example : (Set.range (fun _ : ℕ => (0 : ℚ))).Finite :=
  Set.finite_range_const

/-- The unit in a chosen direct-sum summand remains visible in that coordinate. -/
example (n : ℕ) :
    (DirectSum.lof ℚ[X] ℕ
      (fun _ => ℚ[X] ⧸ RingHom.ker (evalRingHom (0 : ℚ))) n
      (Ideal.Quotient.mk _ 1)) n ≠ 0 := by
  rw [DirectSum.lof_apply]
  intro h
  have hmem : (1 : ℚ[X]) ∈ RingHom.ker (evalRingHom (0 : ℚ)) :=
    (Ideal.Quotient.eq_zero_iff_mem).mp h
  have hzero : (1 : ℚ[X]).eval (0 : ℚ) = 0 := by
    simpa only [← evalPrime_asIdeal, mem_evalPrime_iff] using hmem
  simp at hzero

/-- A genuinely infinite-image family of rational points. -/
example : (Set.range (fun n : ℕ => ((n + 1 : ℕ) : ℚ))).Infinite := by
  apply Set.infinite_range_of_injective
  intro m n h
  exact Nat.add_right_cancel (Nat.cast_injective h)

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Over a finite field, even an infinite indexing family has finite image. -/
example : (Set.range (fun n : ℕ => (n : ZMod 2))).Finite :=
  Set.toFinite _

end Polynomial
