/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.PolynomialQuotientClosedPoints
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Scheme points of polynomial quotients: boundary clients

The rational example uses infinitely many variables, while the algebraically
closed examples exhibit distinct points, the square-zero quotient and the
empty-variable case. The unit ideal has no zeros and hence supplies no point.
-/

@[expose] public section

set_option warningAsError true

noncomputable section

open CategoryTheory

namespace SchemePropertiesExamples

private def rationalZero : MvPolynomial.zeroLocus ℚ
    (⊥ : Ideal (MvPolynomial ℕ ℚ)) :=
  ⟨fun _ => 0, by simp⟩

private theorem rationalInfiniteVariableAtSchemePoint (s : ℕ) :
    (Ideal.Quotient.mkₐ ℚ (⊥ : Ideal (MvPolynomial ℕ ℚ)) (MvPolynomial.X s)) ∈
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (MvPolynomial.zeroLocusQuotientEval
          (⊥ : Ideal (MvPolynomial ℕ ℚ)) rationalZero).toRingHom)
        (IsLocalRing.closedPoint ℚ)).asIdeal := by
  rw [← MvPolynomial.zeroLocusClosedPoint_specMap,
    MvPolynomial.zeroLocusClosedPoint_mem_iff]
  simp [rationalZero]

private theorem rationalInfiniteMorphismIsBaseCompatible :
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (MvPolynomial.zeroLocusQuotientEval
        (⊥ : Ideal (MvPolynomial ℕ ℚ)) rationalZero).toRingHom) =
      ((AlgebraicGeometry.Spec.homEquivAlgHom (R := ℚ)
        (A := MvPolynomial ℕ ℚ ⧸ (⊥ : Ideal (MvPolynomial ℕ ℚ))) (B := ℚ)).symm
        (MvPolynomial.zeroLocusQuotientEval _ rationalZero)).val :=
  MvPolynomial.zeroLocusQuotientEval_specMap _ rationalZero

private def zeroTuple (K : Type*) [Field K] : MvPolynomial.zeroLocus K
    (⊥ : Ideal (MvPolynomial (Fin 1) K)) :=
  ⟨fun _ => 0, by simp⟩

private def oneTuple (K : Type*) [Field K] : MvPolynomial.zeroLocus K
    (⊥ : Ideal (MvPolynomial (Fin 1) K)) :=
  ⟨fun _ => 1, by simp⟩

private theorem zeroTuple_ne_oneTuple (K : Type*) [Field K] :
    zeroTuple K ≠ oneTuple K := by
  intro h
  exact zero_ne_one (congrFun (congrArg Subtype.val h) 0)

private theorem distinctAlgebraicClosureSchemePoints :
    AlgebraicGeometry.pointEquivClosedPoint
        (AlgebraicGeometry.Spec ↧(MvPolynomial (Fin 1) (AlgebraicClosure ℚ) ⧸ ⊥) ↘
          AlgebraicGeometry.Spec ↧(AlgebraicClosure ℚ))
        (MvPolynomial.zeroLocusSchemePoint _
          (zeroTuple (AlgebraicClosure ℚ))) ≠
      AlgebraicGeometry.pointEquivClosedPoint
        (AlgebraicGeometry.Spec ↧(MvPolynomial (Fin 1) (AlgebraicClosure ℚ) ⧸ ⊥) ↘
          AlgebraicGeometry.Spec ↧(AlgebraicClosure ℚ))
        (MvPolynomial.zeroLocusSchemePoint _
          (oneTuple (AlgebraicClosure ℚ))) := by
  rw [← MvPolynomial.zeroLocusEquivClosedPoints_pointEquiv,
    ← MvPolynomial.zeroLocusEquivClosedPoints_pointEquiv]
  intro h
  apply zeroTuple_ne_oneTuple (AlgebraicClosure ℚ)
  exact (MvPolynomial.zeroLocusEquivClosedPoints _).injective h

private def squareZeroTuple : MvPolynomial.zeroLocus (AlgebraicClosure ℚ)
    (Ideal.span {((MvPolynomial.X (0 : Fin 1) :
      MvPolynomial (Fin 1) (AlgebraicClosure ℚ)) ^ 2)}) :=
  ⟨fun _ => 0, by rw [MvPolynomial.zeroLocus_span]; simp⟩

private theorem squareZeroSchemePointVariableVanishes :
    (Ideal.Quotient.mkₐ (AlgebraicClosure ℚ) _
      (MvPolynomial.X (0 : Fin 1))) ∈
      (AlgebraicGeometry.pointEquivClosedPoint
        (AlgebraicGeometry.Spec ↧(MvPolynomial (Fin 1) (AlgebraicClosure ℚ) ⧸
          Ideal.span {((MvPolynomial.X (0 : Fin 1) :
            MvPolynomial (Fin 1) (AlgebraicClosure ℚ)) ^ 2)}) ↘
          AlgebraicGeometry.Spec ↧(AlgebraicClosure ℚ))
        (MvPolynomial.zeroLocusSchemePoint _ squareZeroTuple)).val.asIdeal := by
  rw [← MvPolynomial.zeroLocusEquivClosedPoints_pointEquiv,
    MvPolynomial.zeroLocusEquivClosedPoints_mem_iff]
  simp [squareZeroTuple]

private def emptyTuple : MvPolynomial.zeroLocus (AlgebraicClosure ℚ)
    (⊥ : Ideal (MvPolynomial (Fin 0) (AlgebraicClosure ℚ))) :=
  ⟨fun s => s.elim0, by simp⟩

private theorem emptyVariableSchemePoint :
    AlgebraicGeometry.pointEquivClosedPoint
        (AlgebraicGeometry.Spec ↧(MvPolynomial (Fin 0) (AlgebraicClosure ℚ) ⧸ ⊥) ↘
          AlgebraicGeometry.Spec ↧(AlgebraicClosure ℚ))
        (MvPolynomial.zeroLocusSchemePoint _ emptyTuple) =
      MvPolynomial.zeroLocusClosedPoint _ emptyTuple := by
  rw [← MvPolynomial.zeroLocusEquivClosedPoints_pointEquiv,
    MvPolynomial.zeroLocusEquivClosedPoints_apply]

/-- The unit ideal has no zeros, including in zero variables. -/
theorem unitIdealHasNoZeros :
    IsEmpty (MvPolynomial.zeroLocus ℚ (⊤ : Ideal (MvPolynomial (Fin 0) ℚ))) := by
  constructor
  intro a
  have h := a.property (1 : MvPolynomial (Fin 0) ℚ) (by simp)
  simp at h

end SchemePropertiesExamples
