/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.ProjIrreducible
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Irreducibility of the projective line

The standard total-degree grading on `K[X₀, X₁]` gives an irreducible projective
spectrum. A point is constructed from the zero homogeneous ideal; evaluation
at `(1, 1)` shows that `X₀` is nonzero and proves relevance.

This uses Mathlib's homogeneous-polynomial grading, developed by Johan Commelin
and Eric Wieser, and its projective spectrum, developed by Jujian Zhang,
Johan Commelin and Andrew Yang.
-/

noncomputable section

universe u

namespace AlgebraicGeometry

variable (K : Type u) [Field K]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin 2) K

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem x_zero_mem_irrelevant :
    (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K) ∈
      HomogeneousIdeal.irrelevant 𝒜 := by
  have hX : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K) ∈ 𝒜 1 :=
    (MvPolynomial.mem_homogeneousSubmodule 1 _).2
      (MvPolynomial.isHomogeneous_X K (0 : Fin 2))
  exact HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 (i := 1) (Nat.zero_lt_succ 0) hX

private theorem x_zero_ne_zero :
    (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K) ≠ 0 := by
  intro h
  have h_eval := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (1 : K))) h
  simp at h_eval

/-- A point of the projective line whose homogeneous ideal is zero. -/
private def projectiveLinePoint : Proj 𝒜 where
  asHomogeneousIdeal := ⊥
  isPrime := by
    simpa only [HomogeneousIdeal.toIdeal_bot] using
      (inferInstance : (⊥ : Ideal (MvPolynomial (Fin 2) K)).IsPrime)
  not_irrelevant_le := by
    intro h
    have hx : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K) ∈
        (⊥ : HomogeneousIdeal 𝒜) := h (x_zero_mem_irrelevant K)
    have hx' : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K) ∈
        (⊥ : HomogeneousIdeal 𝒜).toIdeal := HomogeneousIdeal.mem_iff.mpr hx
    exact x_zero_ne_zero K (by
      simpa only [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] using hx')

private theorem projectiveLine_irreducibleSpace : IrreducibleSpace (Proj 𝒜) := by
  let : Nonempty (Proj 𝒜) := ⟨projectiveLinePoint K⟩
  exact Proj.irreducibleSpace 𝒜

end AlgebraicGeometry
