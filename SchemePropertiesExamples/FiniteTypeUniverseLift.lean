/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.FiniteTypeUniverseLift
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Finitely generated algebras across universes

The polynomial algebra, its evaluation endomorphism, and the zero quotient algebra
give independent examples of objects and morphisms. The last example uses essential
surjectivity to compare an arbitrary target-universe algebra to a source-universe one.
-/

@[expose] public section

noncomputable section

open CategoryTheory

private def polynomialTest : FGAlgCat.{0} ℤ :=
  ⟨CommAlgCat.of ℤ (Polynomial ℤ), inferInstance⟩

private def integerTest : FGAlgCat.{0} ℤ :=
  ⟨CommAlgCat.of ℤ ℤ, inferInstance⟩

private def evaluationAtZero : polynomialTest ⟶ integerTest :=
  ObjectProperty.homMk (CommAlgCat.ofHom (Polynomial.aeval (0 : ℤ)))

example : evaluationAtZero.hom.hom Polynomial.X = 0 := by
  change Polynomial.aeval (0 : ℤ) Polynomial.X = 0
  simp

private def polynomialEvaluation : polynomialTest ⟶ polynomialTest :=
  ObjectProperty.homMk (CommAlgCat.ofHom (Polynomial.aeval (0 : Polynomial ℤ)))

/-- Evaluation at zero is not the identity endomorphism of the integer polynomial algebra. -/
theorem polynomial_aeval_zero_ne_id :
    Polynomial.aeval (0 : Polynomial ℤ) ≠ AlgHom.id ℤ (Polynomial ℤ) := by
  intro equality
  have evaluated := congrArg
    (fun f : Polynomial ℤ →ₐ[ℤ] Polynomial ℤ => f Polynomial.X) equality
  have : (0 : Polynomial ℤ) = Polynomial.X := by simpa using evaluated
  exact Polynomial.X_ne_zero this.symm

private theorem polynomialEvaluation_ne_id : polynomialEvaluation ≠ 𝟙 polynomialTest := by
  intro equality
  have evaluated := congrArg
    (fun f : polynomialTest ⟶ polynomialTest => f.hom.hom Polynomial.X) equality
  have hzero : polynomialEvaluation.hom.hom Polynomial.X = 0 := by
    change Polynomial.aeval (0 : Polynomial ℤ) Polynomial.X = 0
    simp
  have hid : (𝟙 polynomialTest : polynomialTest ⟶ polynomialTest).hom.hom
      Polynomial.X = Polynomial.X := rfl
  rw [hzero, hid] at evaluated
  have : (0 : Polynomial ℤ) = Polynomial.X := evaluated
  exact Polynomial.X_ne_zero this.symm

private abbrev zeroAlgebra :=
  (Polynomial ℤ) ⧸ (⊤ : Ideal (Polynomial ℤ))

private def zeroTest : FGAlgCat.{0} ℤ :=
  ⟨CommAlgCat.of ℤ zeroAlgebra, inferInstance⟩

example : Subsingleton zeroTest.obj := by
  dsimp [zeroTest, zeroAlgebra]
  infer_instance

example : Subsingleton
    ((FGAlgCat.uliftFunctor ℤ : FGAlgCat.{0} ℤ ⥤ FGAlgCat.{1} ℤ).obj zeroTest).obj := by
  rw [FGAlgCat.uliftFunctor_obj_obj]
  have singleton : Subsingleton zeroTest.obj := by
    dsimp [zeroTest, zeroAlgebra]
    infer_instance
  constructor
  intro x y
  cases x
  cases y
  exact congrArg ULift.up (singleton.elim _ _)

example (B : FGAlgCat.{1} ℤ) : Small.{0} B.obj :=
  Algebra.FiniteType.small (R := ℤ) (S := B.obj)

example (p : Polynomial ℤ) :
    ((FGAlgCat.uliftFunctor ℤ : FGAlgCat.{0} ℤ ⥤ FGAlgCat.{1} ℤ).map
      polynomialEvaluation).hom (ULift.up p) =
      ULift.up (Polynomial.aeval (0 : Polynomial ℤ) p) := by
  have mapped :
      ((FGAlgCat.uliftFunctor ℤ : FGAlgCat.{0} ℤ ⥤ FGAlgCat.{1} ℤ).map
        polynomialEvaluation).hom (ULift.up p) =
        ULift.up (polynomialEvaluation.hom p) :=
    FGAlgCat.uliftFunctor_map_apply ℤ polynomialEvaluation p
  exact mapped

example :
    (FGAlgCat.uliftFunctor ℤ : FGAlgCat.{0} ℤ ⥤ FGAlgCat.{1} ℤ).map
      polynomialEvaluation ≠
        𝟙 ((FGAlgCat.uliftFunctor ℤ : FGAlgCat.{0} ℤ ⥤ FGAlgCat.{1} ℤ).obj
          polynomialTest) := by
  intro equality
  apply polynomialEvaluation_ne_id
  exact (FGAlgCat.uliftFunctor ℤ : FGAlgCat.{0} ℤ ⥤ FGAlgCat.{1} ℤ).map_injective
    (by simpa using equality)

example (B : FGAlgCat.{1} ℤ) :
    ∃ A : FGAlgCat.{0} ℤ,
      Nonempty (((FGAlgCat.uliftFunctor ℤ : FGAlgCat.{0} ℤ ⥤ FGAlgCat.{1} ℤ).obj A) ≅ B) :=
  (inferInstance : (FGAlgCat.uliftFunctor ℤ : FGAlgCat.{0} ℤ ⥤
    FGAlgCat.{1} ℤ).EssSurj).mem_essImage B

example (B : FGAlgCat.{1} ℤ) :
    ((FGAlgCat.uliftFunctor ℤ : FGAlgCat.{0} ℤ ⥤ FGAlgCat.{1} ℤ).asEquivalence).functor.obj
      (((FGAlgCat.uliftFunctor ℤ : FGAlgCat.{0} ℤ ⥤
        FGAlgCat.{1} ℤ).asEquivalence).inverse.obj B) ≅ B :=
  ((FGAlgCat.uliftFunctor ℤ : FGAlgCat.{0} ℤ ⥤ FGAlgCat.{1} ℤ).asEquivalence).counitIso.app B
