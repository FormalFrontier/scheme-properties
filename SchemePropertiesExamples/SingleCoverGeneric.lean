/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.SingleCoverExtension

/-!
# Boolean-valued invariants on one-cover dense subfunctors

A locally specified Boolean-valued invariant extends uniquely across a one-cover dense
subfunctor. The constant Boolean presheaf satisfies singleton descent without a
representability hypothesis on either the domain or the target.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u

namespace CategoryTheory.Subfunctor

variable {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type}

example {W : MorphismProperty C} [W.HasPullbacks] [W.IsStableUnderBaseChange]
    {D : Subfunctor F} (hD : D.IsOneCoverDense W)
    (φ : D.toFunctor ⟶ (Functor.const Cᵒᵖ).obj Bool) :
    ∃! ψ : F ⟶ (Functor.const Cᵒᵖ).obj Bool, D.ι ≫ ψ = φ := by
  have hBool : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor ((Functor.const Cᵒᵖ).obj Bool) (Presieve.singleton f) := by
    intro X U f _
    rw [Presieve.isSheafFor_singleton]
    intro x _
    refine ⟨x, by simp, ?_⟩
    intro y hy
    simpa using hy
  refine ⟨extendOneCover hD hBool φ, ι_comp_extendOneCover hD hBool φ, ?_⟩
  intro ψ hψ
  exact extendOneCover_unique hD hBool φ ψ hψ

end CategoryTheory.Subfunctor
