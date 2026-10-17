/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.FiniteType
import Mathlib.Basic.Finite.Prod

/-!
# Algebra homomorphisms into a finite algebra

A finite-type algebra has finitely many algebra homomorphisms into any finite
algebra over the same commutative semiring. The source and target algebras may
be noncommutative semirings, and all three types have independent universes.
Finite generation is as an algebra, not as a module; the source need not have a
finite underlying set.

`Algebra.FiniteType.finite_algHom` is an explicit theorem, not a global instance.
It can be installed locally when a `Finite` instance is needed. The proof
restricts each homomorphism to a finite set of algebra generators, on which its
values determine the entire homomorphism.

## References

* Mathlib's `Algebra.FiniteType.out` supplies finite algebra generators.
* Mathlib's `AlgHom.ext_of_adjoin_eq_top` supplies extensionality on generators.
* Mathlib's `Pi.finite` and `Finite.of_injective` supply finiteness of the
  function space on generators and transfer it to algebra homomorphisms.
-/

@[expose] public section

universe u v w

namespace Algebra.FiniteType

/-- A finite-type algebra has finitely many algebra homomorphisms into a finite algebra. -/
theorem finite_algHom
    {R : Type u} {A : Type v} {B : Type w}
    [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    [Algebra.FiniteType R A] [Finite B] : Finite (A →ₐ[R] B) := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := A)
  refine Finite.of_injective (fun f : A →ₐ[R] B => fun a : s => f a) ?_
  intro f g h
  apply AlgHom.ext_of_adjoin_eq_top hs
  intro a ha
  exact congrFun h ⟨a, ha⟩

end Algebra.FiniteType
