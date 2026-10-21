/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import SchemeProperties.PolynomialProjProper

/-!
# Coefficient morphisms for polynomial projective spectra

The projective line over a field, the empty variable set over an arbitrary
commutative ring, and a zero coefficient ring all use the same coefficient
morphism. A separate concrete example constructs the homogeneous zero prime of
`MvPolynomial (Fin 2) (ZMod 2)` as a point of `Proj` and places it in D₊(X₀),
using Mathlib's projective-spectrum constructor and basic-open membership API.
This is the generic topological point, not a closed or F₂-rational point `[1:0]`.
The kernel description of `[1:0]` and the emptiness of the boundary cases in
`docs/PolynomialProjProper.md` remain mathematical explanations, not assertions
of those point or emptiness constructions here.
-/

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

-- The standard nonempty geometric case: the projective line over a field.
example (K : Type u) [Field K] :
    IsProper
      (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) K) ≫
        (Scheme.Spec.mapIso
          (MvPolynomial.gradeZeroAlgEquiv (Fin 2) K).toRingEquiv.toCommRingCatIso.op).hom :
        Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K) ⟶ Spec (CommRingCat.of K)) :=
  Proj.isProper_toSpec_mvPolynomial K (Fin 2)

-- An empty variable set does not require a nontrivial coefficient ring.
example (R : Type u) [CommRing R] :
    IsProper
      (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 0) R) ≫
        (Scheme.Spec.mapIso
          (MvPolynomial.gradeZeroAlgEquiv (Fin 0) R).toRingEquiv.toCommRingCatIso.op).hom :
        Proj (MvPolynomial.homogeneousSubmodule (Fin 0) R) ⟶ Spec (CommRingCat.of R)) :=
  Proj.isProper_toSpec_mvPolynomial R (Fin 0)

-- Every zero coefficient ring is covered, for every finite number of variables.
example (R : Type u) [CommRing R] [Subsingleton R] (n : ℕ) :
    IsProper
      (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin n) R) ≫
        (Scheme.Spec.mapIso
          (MvPolynomial.gradeZeroAlgEquiv (Fin n) R).toRingEquiv.toCommRingCatIso.op).hom :
        Proj (MvPolynomial.homogeneousSubmodule (Fin n) R) ⟶ Spec (CommRingCat.of R)) :=
  Proj.isProper_toSpec_mvPolynomial R (Fin n)

private lemma binaryPolynomial_X_notMem_bot :
    (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) (ZMod 2)) ∉
      (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 2) (ZMod 2))) := by
  intro hx
  have hx' := HomogeneousIdeal.mem_iff.mpr hx
  rw [HomogeneousIdeal.toIdeal_bot] at hx'
  exact MvPolynomial.X_ne_zero (R := ZMod 2) (0 : Fin 2)
    ((Submodule.mem_bot (MvPolynomial (Fin 2) (ZMod 2))).mp hx')

-- The homogeneous zero prime is relevant because the degree-one variable X₀ survives.
private noncomputable def binaryProjectiveGenericPoint :
    Proj (MvPolynomial.homogeneousSubmodule (Fin 2) (ZMod 2)) where
  asHomogeneousIdeal := ⊥
  isPrime := by
    simpa only [HomogeneousIdeal.toIdeal_bot] using
      (Ideal.isPrime_bot : (⊥ : Ideal (MvPolynomial (Fin 2) (ZMod 2))).IsPrime)
  not_irrelevant_le := by
    intro h
    apply binaryPolynomial_X_notMem_bot
    apply h
    exact HomogeneousIdeal.mem_irrelevant_of_mem _ (i := 1) (by decide)
      ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr
        (MvPolynomial.isHomogeneous_X (ZMod 2) (0 : Fin 2)))

-- This chart witness is independent of the properness statement above.
example :
    ∃ x : Proj (MvPolynomial.homogeneousSubmodule (Fin 2) (ZMod 2)),
      x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) (ZMod 2))
        (MvPolynomial.X (0 : Fin 2)) := by
  refine ⟨binaryProjectiveGenericPoint, ?_⟩
  exact (Proj.mem_basicOpen _ _ _).mpr binaryPolynomial_X_notMem_bot
