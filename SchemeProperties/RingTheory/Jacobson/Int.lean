/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# The integers are a Jacobson ring

The zero ideal of `ℤ` has zero Jacobson radical: if `a` belongs to that radical,
then `a * (-3) + 1` is a unit, hence is `1` or `-1`. Integer arithmetic forces
`a = 0`. Every nonzero prime ideal is maximal because `ℤ` is a principal ideal
domain. The prime-ideal criterion therefore proves `IsJacobsonRing ℤ`.

The canonical instance also supplies the integer base for Mathlib's polynomial
and finite-type Jacobson results.

## References

* Mathlib's Jacobson theory, developed by Devon Tuma, supplies the prime-ideal
  criterion and the unit characterization of the Jacobson radical of zero.
* Mathlib's principal-ideal-domain theory, developed by Chris Hughes and
  Morenikeji Neri, supplies maximality of nonzero prime ideals.
-/

@[expose] public section

/-- The ring of integers is a Jacobson ring. -/
instance Int.isJacobsonRing : IsJacobsonRing ℤ := by
  classical
  apply isJacobsonRing_iff_prime_eq.mpr
  intro P hP
  by_cases hzero : P = ⊥
  · subst P
    apply le_antisymm ?_ Ideal.le_jacobson
    intro a ha
    rw [Ideal.mem_bot]
    have hunit := Ideal.mem_jacobson_bot.mp ha (-3)
    rcases Int.isUnit_iff.mp hunit with h | h <;> omega
  · have : P.IsPrime := hP
    have : P.IsMaximal := IsPrime.to_maximal_ideal hzero
    exact Ideal.jacobson_eq_self_of_isMaximal
