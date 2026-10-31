/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Dense
public import Mathlib.CategoryTheory.Limits.Comma

/-!
# Dense functors into over categories

If `F : C ⥤ D` is dense, the functor from `CostructuredArrow F B` to `Over B`
that retains each given structure arrow is dense as well.

The proof uses Mathlib's canonical-colimit characterization of density and its
`CostructuredArrow.costructuredArrowToOverEquivalence`. For `Y : Over B`, this equivalence
identifies the underlying density diagram at `Y` with the density diagram of `F` at `Y.left`.
An identity-component natural isomorphism transports the colimit between these diagrams,
and an isomorphism of cocones identifies their legs. The forgetful functor creates this
particular colimit; no general existence of colimits is required.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.CostructuredArrow

open Limits

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- A dense functor remains dense when its costructured arrows are regarded as objects
of an over category. -/
instance isDense_toOver (F : C ⥤ D) [F.IsDense] (B : D) : (toOver F B).IsDense where
  isDenseAt Y := by
    apply (Functor.isDenseAt_iff (F := toOver F B)).2
    obtain ⟨h⟩ :=
      (Functor.isDenseAt_iff (F := F)).1 (Functor.IsDense.isDenseAt F Y.left)
    let e := costructuredArrowToOverEquivalence F Y
    let diagramIso :
        ((proj (toOver F B) Y ⋙ toOver F B) ⋙ Over.forget B) ≅
          e.functor ⋙ proj F Y.left ⋙ F :=
      NatIso.ofComponents (fun _ => Iso.refl _) (by
        intro X X' f
        change F.map f.left.left ≫ 𝟙 _ = 𝟙 _ ≫ F.map f.left.left
        simp only [Category.comp_id, Category.id_comp])
    refine ⟨isColimitOfReflects (Over.forget B) ?_⟩
    refine IsColimit.ofIsoColimit
      ((IsColimit.precomposeHomEquiv diagramIso _).symm (h.whiskerEquivalence e)) ?_
    refine Cocone.ext (Iso.refl _) ?_
    intro X
    simp only [Functor.comp_obj, proj_obj, Over.forget_obj, Functor.mapCocone_pt,
      Functor.LeftExtension.coconeAt_pt, Functor.LeftExtension.mk_right, Functor.id_obj,
      Cocone.precompose_obj_pt, Cocone.whisker_pt, Cocone.precompose_obj_ι, Cocone.whisker_ι,
      NatTrans.comp_app, Functor.const_obj_obj, Functor.whiskerLeft_app,
      Functor.LeftExtension.coconeAt_ι_app, Functor.whiskeringLeft_obj_obj,
      Functor.LeftExtension.mk_hom, Functor.rightUnitor_inv_app, Functor.id_map,
      Category.id_comp, Iso.refl_hom, Category.comp_id, Functor.mapCocone_ι_app, Over.forget_map]
    change 𝟙 _ ≫ X.hom.left = X.hom.left
    simp only [Category.id_comp]

end CategoryTheory.CostructuredArrow
