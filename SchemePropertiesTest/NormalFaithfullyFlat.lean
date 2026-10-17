/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.NormalFaithfullyFlat
import SchemeProperties.NormalEtale
import SchemeProperties.NormalPolynomial
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.Tactic.FinCases

/-!
# A faithfully flat polynomial extension of a disconnected normal ring

The canonical algebra from `Fin 2 → ℤ` to its polynomial ring is faithfully flat
and not surjective. Both rings are locally normal but neither is a domain. The
normality proofs use the finite-product and polynomial results independently of
the descent theorem; two nonzero orthogonal idempotents witness the domain
boundary. The algebra and module structures are Mathlib's canonical ones. A final
client recovers base normality using descent.
-/

open scoped Polynomial

namespace SchemePropertiesTest.NormalFaithfullyFlat

private abbrev IntegerPair := Fin 2 → ℤ
private abbrev IntegerPairPolynomial := IntegerPair[X]

private def firstIdempotent : IntegerPair := Pi.single 0 1
private def secondIdempotent : IntegerPair := Pi.single 1 1

private theorem firstIdempotent_ne_zero : firstIdempotent ≠ 0 := by
  intro h
  have hzero := congrFun h 0
  simp [firstIdempotent] at hzero

private theorem secondIdempotent_ne_zero : secondIdempotent ≠ 0 := by
  intro h
  have hzero := congrFun h 1
  simp [secondIdempotent] at hzero

private theorem firstIdempotent_mul_self : firstIdempotent * firstIdempotent = firstIdempotent := by
  ext i
  fin_cases i <;> simp [firstIdempotent]

private theorem secondIdempotent_mul_self :
    secondIdempotent * secondIdempotent = secondIdempotent := by
  ext i
  fin_cases i <;> simp [secondIdempotent]

private theorem idempotents_mul_eq_zero : firstIdempotent * secondIdempotent = 0 := by
  ext i
  fin_cases i <;> simp [firstIdempotent, secondIdempotent]

private theorem integerPair_not_isDomain : ¬ IsDomain IntegerPair := by
  intro h
  let _ := h
  exact mul_ne_zero firstIdempotent_ne_zero secondIdempotent_ne_zero idempotents_mul_eq_zero

private theorem polynomial_not_isDomain : ¬ IsDomain IntegerPairPolynomial := by
  intro h
  let _ := h
  exact integerPair_not_isDomain (Polynomial.C_injective.isDomain Polynomial.C)

private theorem integerPair_locallyNormal : IsLocallyNormalRing IntegerPair :=
  IsLocallyNormalRing.pi (fun _ : Fin 2 ↦ ℤ)

private theorem polynomial_locallyNormal : IsLocallyNormalRing IntegerPairPolynomial := by
  let _ := integerPair_locallyNormal
  infer_instance

private theorem polynomial_faithfullyFlat :
    Module.FaithfullyFlat IntegerPair IntegerPairPolynomial := by
  infer_instance

private theorem algebraMap_not_surjective :
    ¬ Function.Surjective (algebraMap IntegerPair IntegerPairPolynomial) := by
  intro h
  obtain ⟨a, ha⟩ := h Polynomial.X
  exact Polynomial.X_ne_C a ha.symm

-- Recover base normality by descent rather than by the finite-product proof.
private theorem integerPair_locallyNormal_via_descent : IsLocallyNormalRing IntegerPair := by
  let _ := polynomial_faithfullyFlat
  let _ := polynomial_locallyNormal
  exact IsLocallyNormalRing.of_faithfullyFlat (S := IntegerPairPolynomial)

end SchemePropertiesTest.NormalFaithfullyFlat
