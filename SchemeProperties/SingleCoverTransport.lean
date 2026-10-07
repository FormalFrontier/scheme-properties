/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.SingleCoverExtension
public import Mathlib.CategoryTheory.Equivalence

/-!
# One-cover density under change of test category

Precomposing a subfunctor with a functor between test categories preserves its
sections, restriction maps, and inclusion. One-cover density compares using the
inverse image of the covering morphism property. Fullness is needed to lift a
covering arrow whose endpoints lie in the image; essential surjectivity allows
objects outside the strict image to be compared by isomorphism. Faithfulness is
not needed for the existential single-arrow condition.

## References

- Mathlib's `Subfunctor`, `MorphismProperty.inverseImage`, and categorical equivalences.
- J. S. Milne, *Algebraic Groups*, Definition 5.6, for the single-arrow condition.
-/

@[expose] public section

open CategoryTheory Opposite

universe u₁ v₁ u₂ v₂ w

namespace CategoryTheory.Subfunctor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {G : D ⥤ Type w}

/-- Restrict a subfunctor to the objects and arrows selected by `J`. -/
def precomp (S : Subfunctor G) (J : C ⥤ D) : Subfunctor (J ⋙ G) where
  obj X := S.obj (J.obj X)
  map f := S.map (J.map f)

@[simp]
theorem precomp_obj (S : Subfunctor G) (J : C ⥤ D) (X : C) :
    (S.precomp J).obj X = S.obj (J.obj X) := rfl

@[simp]
theorem mem_precomp_obj_iff (S : Subfunctor G) (J : C ⥤ D)
    (X : C) (x : G.obj (J.obj X)) :
    x ∈ (S.precomp J).obj X ↔ x ∈ S.obj (J.obj X) := Iff.rfl

/-- Precomposition commutes with passing from a subfunctor to its functor of sections. -/
theorem precomp_toFunctor (S : Subfunctor G) (J : C ⥤ D) :
    (S.precomp J).toFunctor = J ⋙ S.toFunctor := rfl

/-- The precomposed inclusion is the original inclusion evaluated at `J.obj X`. -/
theorem precomp_ι_app (S : Subfunctor G) (J : C ⥤ D) (X : C) :
    (S.precomp J).ι.app X = S.ι.app (J.obj X) := rfl

variable {F : Dᵒᵖ ⥤ Type w} (S : Subfunctor F) (W : MorphismProperty D)
variable (J : C ⥤ D)

/-- One-cover density restricts along a full, essentially surjective test functor.
In particular no faithfulness hypothesis is required. -/
theorem IsOneCoverDense.precomp [J.Full] [J.EssSurj] [W.RespectsIso]
    (hS : S.IsOneCoverDense W) :
    (S.precomp J.op).IsOneCoverDense (W.inverseImage J) := by
  intro X x
  obtain ⟨U, f, hf, hx⟩ := hS (J.obj X) x
  let V := J.objPreimage U
  let e : J.obj V ≅ U := J.objObjPreimageIso U
  refine ⟨V, J.preimage (e.hom ≫ f), ?_, ?_⟩
  · change W (J.map (J.preimage (e.hom ≫ f)))
    rw [J.map_preimage]
    exact MorphismProperty.RespectsIso.precomp W e.hom f hf
  · rw [mem_precomp_obj_iff]
    change F.map (J.map (J.preimage (e.hom ≫ f))).op x ∈ S.obj (op (J.obj V))
    rw [J.map_preimage, op_comp, F.map_comp]
    exact S.map e.hom.op hx

/-- Density on the smaller test category gives density on the larger one when
every larger test object is isomorphic to a smaller one. -/
theorem IsOneCoverDense.of_precomp [J.EssSurj] [W.RespectsIso]
    (hS : (S.precomp J.op).IsOneCoverDense (W.inverseImage J)) :
    S.IsOneCoverDense W := by
  intro X x
  let V := J.objPreimage X
  let e : J.obj V ≅ X := J.objObjPreimageIso X
  obtain ⟨U, f, hf, hx⟩ := hS V (F.map e.hom.op x)
  refine ⟨J.obj U, J.map f ≫ e.hom,
    MorphismProperty.RespectsIso.postcomp W e.hom (J.map f) hf, ?_⟩
  rw [mem_precomp_obj_iff] at hx
  change F.map (J.map f).op (F.map e.hom.op x) ∈ S.obj (op (J.obj U)) at hx
  rwa [op_comp, F.map_comp]

/-- Fullness and essential surjectivity suffice to transport single-arrow density
in both directions; faithfulness, sheaf conditions, and pullbacks are unnecessary. -/
theorem isOneCoverDense_precomp_iff [J.Full] [J.EssSurj] [W.RespectsIso] :
    (S.precomp J.op).IsOneCoverDense (W.inverseImage J) ↔ S.IsOneCoverDense W := by
  exact ⟨IsOneCoverDense.of_precomp S W J, IsOneCoverDense.precomp S W J⟩

/-- Single-arrow density is invariant under equivalence of test categories. -/
theorem isOneCoverDense_equivalence_iff [W.RespectsIso] (e : C ≌ D) :
    (S.precomp e.functor.op).IsOneCoverDense (W.inverseImage e.functor) ↔
      S.IsOneCoverDense W := by
  exact isOneCoverDense_precomp_iff S W e.functor

end CategoryTheory.Subfunctor
