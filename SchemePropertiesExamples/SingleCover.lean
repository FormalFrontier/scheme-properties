/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.PowerImage

/-!
# Single-cover extension boundaries over the rational numbers

The square-power image is one-cover dense despite a Laurent unit outside it;
that same image fails descent along its explicit root cover. The zero additive
subfunctor has the opposite one-cover behavior.
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry

example :
    (powerImage ℚ 2).IsOneCoverDense (faithfullyFlatTestMorphisms ℚ) ∧
      laurentUnit ℚ ∉ (powerImage ℚ 2).obj (op (op (laurentTest ℚ))) ∧
      ¬ Presieve.IsSheafFor ((powerImage ℚ 2).toFunctor)
        (Presieve.singleton (powerRootMap ℚ 2 (laurentTest ℚ) (laurentUnit ℚ)).op) := by
  exact ⟨powerImage_isOneCoverDense ℚ 2 (by decide),
    laurentUnit_not_mem_powerImage ℚ 2 (by decide),
    powerImage_not_isSheafFor_root ℚ 2 (by decide)⟩

example :
    faithfullyFlatTestMorphisms ℚ
      (powerRootMap ℚ 2 (laurentTest ℚ) (laurentUnit ℚ)).op ∧
    (unitsTestPoints ℚ).map
      (powerRootMap ℚ 2 (laurentTest ℚ) (laurentUnit ℚ)).op.op (laurentUnit ℚ) ∈
        (powerImage ℚ 2).obj
          (op (op (powerRootAlgebra ℚ 2 (laurentTest ℚ) (laurentUnit ℚ)))) := by
  exact ⟨powerRootMap_faithfullyFlat ℚ 2 (laurentTest ℚ) (laurentUnit ℚ) (by decide),
    powerRootMap_mem_powerImage ℚ 2 (laurentTest ℚ) (laurentUnit ℚ) (by decide)⟩

example :
    (powerImage ℚ 2).IsOneCoverDense (faithfullyFlatTestMorphisms ℚ) ∧
      ¬ (zeroAdditiveSubfunctor ℚ).IsOneCoverDense (faithfullyFlatTestMorphisms ℚ) := by
  exact ⟨powerImage_isOneCoverDense ℚ 2 (by decide),
    zeroAdditiveSubfunctor_not_oneCoverDense ℚ⟩

example (Y : algebraicOver ℚ)
    (φ : (powerImage ℚ 2).toFunctor ⟶ (algebraicOverPoints ℚ).obj Y) :
    ∃ ψ : unitsTestPoints ℚ ⟶ (algebraicOverPoints ℚ).obj Y,
      (powerImage ℚ 2).ι ≫ ψ = φ ∧
        ∀ (A : FGAlgCat ℚ) (a : (powerImage ℚ 2).toFunctor.obj (op (op A))),
          ψ.app (op (op A)) ((powerImage ℚ 2).ι.app (op (op A)) a) =
            φ.app (op (op A)) a := by
  have : Limits.HasPullbacks ((FGAlgCat ℚ)ᵒᵖ) := hasPullbacks_finiteTypeAffineTests ℚ
  have : (faithfullyFlatTestMorphisms ℚ).IsStableUnderBaseChange :=
    faithfullyFlatTestMorphisms_isStableUnderBaseChange ℚ
  let hD := powerImage_isOneCoverDense ℚ 2 (by decide)
  let hY : ∀ {X U : (FGAlgCat ℚ)ᵒᵖ} (f : U ⟶ X),
      faithfullyFlatTestMorphisms ℚ f →
        Presieve.IsSheafFor ((algebraicOverPoints ℚ).obj Y) (Presieve.singleton f) :=
    fun f hf ↦ algebraicOverPoints_isSheafFor_faithfullyFlat ℚ Y f hf
  refine ⟨Subfunctor.extendOneCover hD hY φ, Subfunctor.ι_comp_extendOneCover hD hY φ, ?_⟩
  intro A a
  have h := congrArg (fun θ ↦ θ.app (op (op A)) a)
    (Subfunctor.ι_comp_extendOneCover hD hY φ)
  simpa only [NatTrans.comp_app, types_comp_apply] using h

end AlgebraicGeometry
