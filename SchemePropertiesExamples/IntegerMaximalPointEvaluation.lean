/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.MaximalPointHom
public import SchemeProperties.RingTheory.Jacobson.Int
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Evaluation at zero over the integers

Evaluation at zero, `ℤ[X] →ₐ[ℤ] ℤ`, gives a morphism of maximal-point locally
ringed spaces over `Spec ℤ`. Its underlying geometric map is the canonical
maximal-point map, and its recovered ring homomorphism is evaluation at zero;
in particular, the recovered map sends `X` to `0`.

The scalar ring is not a field. The canonical self-algebra structure makes `ℤ`
finite type over itself, while Mathlib's polynomial instance makes `ℤ[X]`
Jacobson from the integer instance. All algebra actions are the canonical ones.

## References

* `SchemeProperties.MaximalPointHom` for the finite-type algebra-homomorphism
  equivalence and its geometric and global-section readbacks.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry.Spec

example :
    let φ : Polynomial ℤ →ₐ[ℤ] ℤ := Polynomial.aeval (0 : ℤ)
    let g := maximalPointAlgHomEquivOfFiniteType
      (K := ℤ) (R := Polynomial ℤ) (S := ℤ) φ
    g.left = maximalPointMapOfAlgHom φ ∧
      maximalPointRingHom g.left = (φ : Polynomial ℤ →+* ℤ) ∧
      maximalPointRingHom g.left Polynomial.X = 0 := by
  let φ : Polynomial ℤ →ₐ[ℤ] ℤ := Polynomial.aeval (0 : ℤ)
  let e := maximalPointAlgHomEquivOfFiniteType
    (K := ℤ) (R := Polynomial ℤ) (S := ℤ)
  have hrecover : maximalPointRingHom (e φ).left = (φ : Polynomial ℤ →+* ℤ) := by
    calc
      _ = (e.symm (e φ) : Polynomial ℤ →+* ℤ) :=
        (maximalPointAlgHomEquivOfFiniteType_symm_apply_toRingHom (e φ)).symm
      _ = (φ : Polynomial ℤ →+* ℤ) :=
        congrArg AlgHom.toRingHom (e.symm_apply_apply φ)
  refine ⟨maximalPointAlgHomEquivOfFiniteType_apply_left φ, hrecover, ?_⟩
  rw [hrecover]
  exact Polynomial.aeval_X (0 : ℤ)
