/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.ClosedPointLocallyRingedSpace

/-!
# Morphisms on closed-point locally ringed spaces

A morphism of Jacobson locally ringed spaces that takes closed points to closed
points induces a morphism on their closed-point locally ringed spaces. Its full
sheaf component is transported along the correspondence of opens.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Functor TopCat TopologicalSpace Opposite Topology

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Y Z : LocallyRingedSpace.{u}}
variable [JacobsonSpace X] [JacobsonSpace Y] [JacobsonSpace Z]
variable (f : X ⟶ Y) (hf : Set.MapsTo f.base (closedPoints X) (closedPoints Y))

/-- The continuous restriction of a closed-point-preserving morphism. -/
@[simps!]
def closedPointMapBase :
    TopCat.of (closedPoints X) ⟶ TopCat.of (closedPoints Y) :=
  TopCat.ofHom
    ⟨fun x => ⟨f.base x.val, hf x.property⟩,
      (f.base.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- Extending a closed-point open commutes with inverse image. -/
lemma closedPointMap_extendOpen (W : Opens (closedPoints Y)) :
    (Opens.closedPointsOrderIso X).symm ((Opens.map (closedPointMapBase f hf)).obj W) =
      (Opens.map f.base).obj ((Opens.closedPointsOrderIso Y).symm W) := by
  apply (Opens.closedPointsOrderIso X).injective
  rw [OrderIso.apply_symm_apply]
  ext x
  have h := congrArg (fun V : Opens (closedPoints Y) =>
      (⟨f.base x.val, hf x.property⟩ : closedPoints Y) ∈ V)
    ((Opens.closedPointsOrderIso Y).apply_symm_apply W)
  exact (Iff.of_eq h).symm

/-- The transported morphism of presheafed spaces. -/
def closedPointMapPresheafedSpaceHom :
    (closedPointSheafedSpace X).toPresheafedSpace ⟶
      (closedPointSheafedSpace Y).toPresheafedSpace where
  base := closedPointMapBase f hf
  c := whiskerLeft (Opens.closedPointsOrderIso Y).symm.monotone.functor.op f.c ≫
    (isoWhiskerRight
      (NatIso.ofComponents (fun W =>
        eqToIso (congrArg op (closedPointMap_extendOpen f hf W.unop).symm)) :
        (Opens.closedPointsOrderIso Y).symm.monotone.functor.op ⋙ (Opens.map f.base).op ≅
          (Opens.map (closedPointMapBase f hf)).op ⋙
            (Opens.closedPointsOrderIso X).symm.monotone.functor.op)
      X.presheaf).hom

@[simp]
lemma closedPointMapPresheafedSpaceHom_base :
    (closedPointMapPresheafedSpaceHom f hf).base = closedPointMapBase f hf := rfl

/-- The transported component is the original component followed by the canonical
identification of the two ambient inverse-image opens. -/
@[simp]
lemma closedPointMapPresheafedSpaceHom_c_app (W : Opens (closedPoints Y)) :
    (closedPointMapPresheafedSpaceHom f hf).c.app (op W) =
      f.c.app (op ((Opens.closedPointsOrderIso Y).symm W)) ≫
        X.presheaf.map (eqToHom (closedPointMap_extendOpen f hf W)).op := by
  change f.c.app _ ≫ X.presheaf.map _ = f.c.app _ ≫ X.presheaf.map _
  congr 1
  exact congrArg X.presheaf.map (Subsingleton.elim _ _)

set_option backward.isDefEq.respectTransparency false in
/-- The square with the inclusions commutes as a square of presheafed spaces. -/
lemma closedPointMapPresheafedSpaceHom_comp :
    closedPointMapPresheafedSpaceHom f hf ≫ closedPointPresheafedSpaceHom Y =
      closedPointPresheafedSpaceHom X ≫ f.toHom := by
  refine PresheafedSpace.ext
    (closedPointMapPresheafedSpaceHom f hf ≫ closedPointPresheafedSpaceHom Y)
    (closedPointPresheafedSpaceHom X ≫ f.toHom) (by ext x; rfl) ?_
  simp only [eqToHom_refl]
  erw [whiskerRight_id', Category.comp_id]
  ext1 U
  simp only [PresheafedSpace.comp_c_app, closedPointPresheafedSpaceHom_c_app,
    closedPointMapPresheafedSpaceHom_c_app, closedPointPresheafedSpaceHom_preimage]
  erw [← Category.assoc, f.c.naturality]
  simp only [Category.assoc, Presheaf.pushforward_obj_map, ← Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- A closed-point-preserving morphism induces a locally ringed space morphism. -/
@[simps! toHom]
def closedPointMap : closedPointSpace X ⟶ closedPointSpace Y where
  toHom := closedPointMapPresheafedSpaceHom f hf
  prop x := by
    let a := (closedPointPresheafedSpaceHom Y).stalkMap (closedPointMapBase f hf x)
    have : IsIso a := closedPointPresheafedSpaceHom_stalkMap_isIso Y _
    have he : (closedPointMapPresheafedSpaceHom f hf).stalkMap x =
        inv a ≫ f.stalkMap x.val ≫ (fromClosedPoints X).stalkMap x := by
      have h := PresheafedSpace.stalkMap.congr_hom
        (closedPointMapPresheafedSpaceHom f hf ≫ closedPointPresheafedSpaceHom Y)
        (closedPointPresheafedSpaceHom X ≫ f.toHom)
        (closedPointMapPresheafedSpaceHom_comp f hf) x
      apply (IsIso.eq_inv_comp a).mpr
      calc
        _ = (closedPointMapPresheafedSpaceHom f hf ≫
            closedPointPresheafedSpaceHom Y).stalkMap x :=
          (PresheafedSpace.stalkMap.comp (closedPointMapPresheafedSpaceHom f hf)
            (closedPointPresheafedSpaceHom Y) x).symm
        _ = (closedPointPresheafedSpaceHom X ≫ f.toHom).stalkMap x := by
          simpa only [eqToHom_refl, Category.id_comp] using h
        _ = _ := PresheafedSpace.stalkMap.comp (closedPointPresheafedSpaceHom X) f.toHom x
    rw [he]
    have ha := isLocalHom_of_isIso (inv a)
    have hX := isLocalHomStalkMap (fromClosedPoints X) x
    have hf' := isLocalHomStalkMap f x.val
    have hmid := @CommRingCat.isLocalHom_comp _ _ _
      (f.stalkMap x.val) ((fromClosedPoints X).stalkMap x) hX hf'
    exact @CommRingCat.isLocalHom_comp _ _ _ (inv a)
      (f.stalkMap x.val ≫ (fromClosedPoints X).stalkMap x) hmid ha

/-- The full square with the canonical inclusions commutes. -/
@[reassoc]
lemma closedPointMap_comp_fromClosedPoints :
    closedPointMap f hf ≫ fromClosedPoints Y = fromClosedPoints X ≫ f := by
  apply Hom.ext'
  exact closedPointMapPresheafedSpaceHom_comp f hf

@[simp]
lemma closedPointMap_base_apply (x : closedPointSpace X) :
    (closedPointMap f hf).base x = ⟨f.base x.val, hf x.property⟩ := rfl

/-- On every open the section map is transported from the original morphism. -/
lemma closedPointMap_c_app (W : Opens (closedPointSpace Y)) :
    (closedPointMap f hf).c.app (op W) =
      f.c.app (op ((Opens.closedPointsOrderIso Y).symm W)) ≫
        X.presheaf.map (eqToHom (congrArg op (closedPointMap_extendOpen f hf W).symm)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The canonical stalk comparisons intertwine the full induced stalk map. -/
@[reassoc]
lemma closedPointMap_stalkMap (x : closedPointSpace X) :
    (closedPointStalkIso Y ((closedPointMap f hf).base x)).hom ≫
        (closedPointMap f hf).stalkMap x =
      f.stalkMap x.val ≫ (closedPointStalkIso X x).hom := by
  have h := LocallyRingedSpace.stalkMap_congr_hom
    (closedPointMap f hf ≫ fromClosedPoints Y) (fromClosedPoints X ≫ f)
    (closedPointMap_comp_fromClosedPoints f hf) x
  simpa only [stalkMap_comp, comp_base, TopCat.comp_app,
    fromClosedPoints_base_apply, closedPointMap_base_apply,
    TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp, closedPointStalkIso_hom] using h

/-- The map is independent of the proof of closed-point preservation. -/
lemma closedPointMap_proof_irrel
    (hf' : Set.MapsTo f.base (closedPoints X) (closedPoints Y)) :
    closedPointMap f hf = closedPointMap f hf' := rfl

/-- The transported morphism is the unique lift of the full commuting square. -/
lemma closedPointMap_unique (g : closedPointSpace X ⟶ closedPointSpace Y)
    (hg : g ≫ fromClosedPoints Y = fromClosedPoints X ≫ f) :
    g = closedPointMap f hf :=
  fromClosedPoints_hom_ext Y (hg.trans (closedPointMap_comp_fromClosedPoints f hf).symm)

/-- Restricting an identity morphism gives an identity. -/
@[simp]
lemma closedPointMap_id :
    closedPointMap (𝟙 X) (fun _ hx => hx) = 𝟙 (closedPointSpace X) := by
  apply fromClosedPoints_hom_ext X
  exact (closedPointMap_comp_fromClosedPoints (𝟙 X) (fun _ hx => hx)).trans
    ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- Restriction to closed points respects composition. -/
@[simp]
lemma closedPointMap_comp (g : Y ⟶ Z)
    (hg : Set.MapsTo g.base (closedPoints Y) (closedPoints Z)) :
    closedPointMap (f ≫ g) (hg.comp hf) = closedPointMap f hf ≫ closedPointMap g hg := by
  apply fromClosedPoints_hom_ext Z
  calc
    _ = fromClosedPoints X ≫ (f ≫ g) :=
      closedPointMap_comp_fromClosedPoints (f ≫ g) (hg.comp hf)
    _ = (fromClosedPoints X ≫ f) ≫ g := (Category.assoc _ _ _).symm
    _ = (closedPointMap f hf ≫ fromClosedPoints Y) ≫ g :=
      congrArg (fun k => k ≫ g) (closedPointMap_comp_fromClosedPoints f hf).symm
    _ = closedPointMap f hf ≫ (fromClosedPoints Y ≫ g) := Category.assoc _ _ _
    _ = closedPointMap f hf ≫ (closedPointMap g hg ≫ fromClosedPoints Z) :=
      congrArg (fun k => closedPointMap f hf ≫ k)
        (closedPointMap_comp_fromClosedPoints g hg).symm
    _ = _ := (Category.assoc _ _ _).symm

end AlgebraicGeometry.LocallyRingedSpace
