/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.ClosedPointMorphisms

/-!
# Lifting morphisms to the closed-point target

A morphism from an arbitrary locally ringed space to a Jacobson locally ringed
space lifts to its closed-point space precisely when all its image points are
closed. The lift is a
full morphism of locally ringed spaces: its composition with the given inclusion
is the original morphism, including its sheaf component and local stalk maps.

The construction uses Mathlib's fully faithful precomposition along the existing
order equivalence on opens. Uniqueness uses the existing monomorphism of locally
ringed spaces. No Jacobson hypothesis is imposed on the source.

## References

The transport uses Mathlib's `Equivalence.congrLeft` and
`Functor.FullyFaithful.preimage`; the closed-point sheaf and stalk comparisons
are those of `SchemeProperties.ClosedPointLocallyRingedSpace`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Functor TopCat TopologicalSpace Opposite

namespace AlgebraicGeometry.LocallyRingedSpace

variable {T X Y Z B : LocallyRingedSpace.{u}} [JacobsonSpace Y]
variable (f : X ⟶ Y) (hf : ∀ x : X, f.base x ∈ closedPoints Y)

private def closedPointLiftBase : X.toTopCat ⟶ (closedPointSpace Y).toTopCat :=
  TopCat.ofHom ⟨fun x => ⟨f.base x, hf x⟩, f.base.hom.continuous.subtype_mk _⟩

-- The target of the component is the actual composite pushforward, definitionally.
set_option backward.isDefEq.respectTransparency false in
private def closedPointLiftPresheafedSpaceHom :
    X.toPresheafedSpace ⟶ (closedPointSpace Y).toPresheafedSpace where
  base := closedPointLiftBase f hf
  c := (Equivalence.congrLeft (E := CommRingCat)
    (Opens.closedPointsOrderIso Y).equivalence.op).fullyFaithfulInverse.preimage
      (X := (closedPointSpace Y).presheaf)
      (Y := (closedPointLiftBase f hf) _* X.presheaf)
      ((closedPointSheafIso Y).inv ≫ f.c)

-- The two actual comap functors are definitionally equal after unfolding the lift base.
set_option backward.isDefEq.respectTransparency false in
private lemma closedPointLiftPresheafedSpaceHom_comp :
    closedPointLiftPresheafedSpaceHom f hf ≫ (fromClosedPoints Y).toHom = f.toHom := by
  refine PresheafedSpace.ext _ _ (by ext x; rfl) ?_
  simp only [eqToHom_refl]
  erw [whiskerRight_id', Category.comp_id]
  change (fromClosedPoints Y).c ≫
    (Presheaf.pushforward CommRingCat (fromClosedPoints Y).base).map
      ((Equivalence.congrLeft (E := CommRingCat)
        (Opens.closedPointsOrderIso Y).equivalence.op).fullyFaithfulInverse.preimage
          (X := (closedPointSpace Y).presheaf)
          (Y := (closedPointLiftBase f hf) _* X.presheaf)
          ((closedPointSheafIso Y).inv ≫ f.c)) = f.c
  rw [Functor.FullyFaithful.map_preimage]
  exact (closedPointSheafIso Y).hom_inv_id_assoc f.c

-- The inclusion composite has exactly the original base, so the canonical stalk
-- equality transport is definitionally the identity.
set_option backward.isDefEq.respectTransparency false in
/-- The canonical lift of a morphism whose every image point is closed.
Only the target is required to be Jacobson. -/
def closedPointLift : X ⟶ closedPointSpace Y where
  toHom :=
    let b : X.toTopCat ⟶ (closedPointSpace Y).toTopCat :=
      TopCat.ofHom ⟨fun x => ⟨f.base x, hf x⟩, f.base.hom.continuous.subtype_mk _⟩
    { base := b
      c := (Equivalence.congrLeft (E := CommRingCat)
        (Opens.closedPointsOrderIso Y).equivalence.op).fullyFaithfulInverse.preimage
          (X := (closedPointSpace Y).presheaf) (Y := b _* X.presheaf)
          ((closedPointSheafIso Y).inv ≫ f.c) }
  prop x := by
    change IsLocalHom ((closedPointLiftPresheafedSpaceHom f hf).stalkMap x).hom
    let a := (fromClosedPoints Y).toHom.stalkMap
      ((closedPointLiftPresheafedSpaceHom f hf).base x)
    have : IsIso a := fromClosedPoints_stalkMap_isIso Y _
    have he : (closedPointLiftPresheafedSpaceHom f hf).stalkMap x =
        inv a ≫ f.toHom.stalkMap x := by
      apply (IsIso.eq_inv_comp a).mpr
      have h := PresheafedSpace.stalkMap.congr_hom
        (closedPointLiftPresheafedSpaceHom f hf ≫ (fromClosedPoints Y).toHom)
        f.toHom (closedPointLiftPresheafedSpaceHom_comp f hf) x
      simpa only [PresheafedSpace.stalkMap.comp, eqToHom_refl, Category.id_comp] using h
    rw [he]
    have ha := isLocalHom_of_isIso (inv a)
    exact @CommRingCat.isLocalHom_comp _ _ _ (inv a) (f.toHom.stalkMap x)
      (isLocalHomStalkMap' f x) ha

/-- Composing the lift with the given inclusion recovers the full original arrow. -/
@[simp, reassoc]
lemma closedPointLift_comp_fromClosedPoints :
    closedPointLift f hf ≫ fromClosedPoints Y = f := by
  apply Hom.ext'
  exact closedPointLiftPresheafedSpaceHom_comp f hf

/-- The point map is the original point map, with its closed-image proof. -/
@[simp]
lemma closedPointLift_base_apply (x : X) :
    (closedPointLift f hf).base x = ⟨f.base x, hf x⟩ := rfl

/-- Taking inverse images of an ambient open agrees with the original morphism. -/
@[simp]
lemma closedPointLift_preimage (U : Opens Y) :
    (Opens.map (closedPointLift f hf).base).obj ((Opens.closedPointsOrderIso Y) U) =
      (Opens.map f.base).obj U := rfl

-- Unfold the given closed-point carrier when comparing its opens with subtype opens.
set_option backward.isDefEq.respectTransparency false in
/-- The inverse image of an arbitrary closed-point open is the original inverse
image of its canonical extension. -/
lemma closedPointLift_preimage_extendOpen (W : Opens (closedPointSpace Y)) :
    (Opens.map (closedPointLift f hf).base).obj W =
      (Opens.map f.base).obj ((Opens.closedPointsOrderIso Y).symm W) := by
  ext x
  exact (Opens.val_mem_closedPointsOrderIso_symm_apply
    (X := Y) (x := ⟨f.base x, hf x⟩)).symm

-- These opens are equal by definition, not just isomorphic.
set_option backward.isDefEq.respectTransparency false in
/-- On every ambient open the given full section comparison followed by the
lift's component is exactly the original section map. -/
@[reassoc]
lemma closedPointLift_c_app (U : Opens Y) :
    (closedPointSectionsIso Y U).hom ≫
        (closedPointLift f hf).c.app (op ((Opens.closedPointsOrderIso Y) U)) =
      f.c.app (op U) := by
  have h := PresheafedSpace.congr_app
    (congrArg (fun g : X ⟶ Y => g.toHom) (closedPointLift_comp_fromClosedPoints f hf))
    (op U)
  simp only [LocallyRingedSpace.comp_c_app, eqToHom_refl] at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h

-- Unfold the closed-point carrier and the definitionally equal inverse-image opens.
set_option backward.isDefEq.respectTransparency false in
/-- The component on any closed-point open is the original component, transported
through the given full section comparison. Both equality transports are canonical. -/
lemma closedPointLift_c_app_eq (W : Opens (closedPointSpace Y)) :
    (closedPointLift f hf).c.app (op W) =
      (closedPointSpace Y).presheaf.map
          (eqToHom (congrArg op ((Opens.closedPointsOrderIso Y).apply_symm_apply W).symm)) ≫
        (closedPointSectionsIso Y ((Opens.closedPointsOrderIso Y).symm W)).inv ≫
          f.c.app (op ((Opens.closedPointsOrderIso Y).symm W)) ≫
            X.presheaf.map (eqToHom
              (congrArg op (closedPointLift_preimage_extendOpen f hf W).symm)) := by
  let U := (Opens.closedPointsOrderIso Y).symm W
  let i : op W ⟶ op ((Opens.closedPointsOrderIso Y) U) :=
    eqToHom (congrArg op ((Opens.closedPointsOrderIso Y).apply_symm_apply W).symm)
  let d := ((closedPointLift f hf).base _* X.presheaf).map i
  let β := X.presheaf.map (eqToHom
    (congrArg op (closedPointLift_preimage_extendOpen f hf W).symm))
  have hdβ : d ≫ β = 𝟙 _ := by
    change X.presheaf.map _ ≫ X.presheaf.map _ = 𝟙 _
    rw [← CategoryTheory.Functor.map_comp]
    exact (congrArg X.presheaf.map (Subsingleton.elim _ (𝟙 _))).trans
      (X.presheaf.map_id _)
  have ha : (closedPointLift f hf).c.app (op ((Opens.closedPointsOrderIso Y) U)) =
      (closedPointSectionsIso Y U).inv ≫ f.c.app (op U) := by
    apply (cancel_epi (closedPointSectionsIso Y U).hom).mp
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    exact closedPointLift_c_app f hf U
  calc
    (closedPointLift f hf).c.app (op W) =
        ((closedPointLift f hf).c.app (op W) ≫ d) ≫ β := by
      rw [Category.assoc, hdβ, Category.comp_id]
    _ = ((closedPointSpace Y).presheaf.map i ≫
        (closedPointLift f hf).c.app (op ((Opens.closedPointsOrderIso Y) U))) ≫ β := by
      rw [← (closedPointLift f hf).c.naturality i]
    _ = _ := by
      rw [ha]
      simp only [Category.assoc]
      rfl

-- The subtype-valued base makes the canonical target-stalk equality transport
-- definitionally the identity; no stalk or residue-ring replacement is used.
set_option backward.isDefEq.respectTransparency false in
/-- The given comparison on full stalks followed by the lift is the original
local ring homomorphism. -/
@[reassoc]
lemma closedPointLift_stalkMap (x : X) :
    (closedPointStalkIso Y ((closedPointLift f hf).base x)).hom ≫
        (closedPointLift f hf).stalkMap x = f.stalkMap x := by
  have h := LocallyRingedSpace.stalkMap_congr_hom
    (closedPointLift f hf ≫ fromClosedPoints Y) f
    (closedPointLift_comp_fromClosedPoints f hf) x
  simpa only [stalkMap_comp, comp_base, TopCat.comp_app, fromClosedPoints_base_apply,
    closedPointLift_base_apply, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp, closedPointStalkIso_hom] using h

/-- The lift does not depend on the proof of the image condition. -/
lemma closedPointLift_proof_irrel (hf' : ∀ x : X, f.base x ∈ closedPoints Y) :
    closedPointLift f hf = closedPointLift f hf' := rfl

/-- Every full factorization through the given inclusion is the canonical lift. -/
lemma closedPointLift_unique (g : X ⟶ closedPointSpace Y)
    (hg : g ≫ fromClosedPoints Y = f) : g = closedPointLift f hf :=
  fromClosedPoints_hom_ext Y (hg.trans (closedPointLift_comp_fromClosedPoints f hf).symm)

/-- Lifting the inclusion composite recovers any arrow to the closed-point space. -/
@[simp]
lemma closedPointLift_comp_inclusion (g : X ⟶ closedPointSpace Y) :
    closedPointLift (g ≫ fromClosedPoints Y) (fun x => (g.base x).property) = g :=
  (closedPointLift_unique _ _ g rfl).symm

/-- The target-inclusion universal property, for an arbitrary locally ringed source. -/
def closedPointInclusionHomEquiv (X Y : LocallyRingedSpace.{u}) [JacobsonSpace Y] :
    (X ⟶ closedPointSpace Y) ≃ {f : X ⟶ Y // ∀ x : X, f.base x ∈ closedPoints Y} where
  toFun g := ⟨g ≫ fromClosedPoints Y, fun x => (g.base x).property⟩
  invFun f := closedPointLift f.val f.property
  left_inv := closedPointLift_comp_inclusion
  right_inv f := Subtype.ext (closedPointLift_comp_fromClosedPoints f.val f.property)

/-- The forward equivalence is composition with the existing inclusion. -/
@[simp]
lemma closedPointInclusionHomEquiv_apply_val (g : X ⟶ closedPointSpace Y) :
    (closedPointInclusionHomEquiv X Y g).val = g ≫ fromClosedPoints Y := rfl

/-- The inverse equivalence is the canonical full lift. -/
@[simp]
lemma closedPointInclusionHomEquiv_symm_apply
    (f : {f : X ⟶ Y // ∀ x : X, f.base x ∈ closedPoints Y}) :
    (closedPointInclusionHomEquiv X Y).symm f = closedPointLift f.val f.property := rfl

/-- A full arrow admits a unique lift exactly when all its image points are closed. -/
lemma existsUnique_closedPointLift_iff :
    (∃! g : X ⟶ closedPointSpace Y, g ≫ fromClosedPoints Y = f) ↔
      ∀ x : X, f.base x ∈ closedPoints Y := by
  constructor
  · rintro ⟨g, hg, _⟩ x
    rw [← hg]
    exact (g.base x).property
  · intro hf
    exact ⟨closedPointLift f hf, closedPointLift_comp_fromClosedPoints f hf,
      fun g hg => closedPointLift_unique f hf g hg⟩

-- The induced image proof uses the original composite base, definitionally.
set_option backward.isDefEq.respectTransparency false in
/-- Lifting commutes with precomposition by every locally ringed space morphism. -/
@[simp]
lemma closedPointLift_precomp (g : T ⟶ X) :
    closedPointLift (g ≫ f) (fun t => hf (g.base t)) = g ≫ closedPointLift f hf := by
  apply fromClosedPoints_hom_ext Y
  simp only [Category.assoc, closedPointLift_comp_fromClosedPoints]

-- Unfold the composite base and the stock MapsTo predicate while rewriting.
set_option backward.isDefEq.respectTransparency false in
/-- Target naturality uses the existing map on closed-point spaces and its exact
closed-point-preservation hypothesis. -/
lemma closedPointLift_postcomp [JacobsonSpace Z] (k : Y ⟶ Z)
    (hk : Set.MapsTo k.base (closedPoints Y) (closedPoints Z)) :
    closedPointLift (f ≫ k) (fun x => hk (hf x)) =
      closedPointLift f hf ≫ closedPointMap k hk := by
  apply fromClosedPoints_hom_ext Z
  rw [closedPointLift_comp_fromClosedPoints, Category.assoc,
    closedPointMap_comp_fromClosedPoints, ← Category.assoc,
    closedPointLift_comp_fromClosedPoints]

/-- The old restricted-source construction is the same target-only lift. -/
lemma closedPointLift_fromClosedPoints [JacobsonSpace X] (k : X ⟶ Y)
    (hk : Set.MapsTo k.base (closedPoints X) (closedPoints Y)) :
    closedPointLift (fromClosedPoints X ≫ k) (fun x => hk x.property) =
      closedPointMap k hk :=
  (closedPointLift_unique _ _ _ (closedPointMap_comp_fromClosedPoints k hk)).symm

/-- A supplied structure-map triangle is preserved without changing its maps. -/
lemma closedPointLift_comp_structure (σY : Y ⟶ B) (σX : X ⟶ B)
    (h : f ≫ σY = σX) :
    closedPointLift f hf ≫ fromClosedPoints Y ≫ σY = σX := by
  rw [← Category.assoc, closedPointLift_comp_fromClosedPoints, h]

/-- The given global-section comparison reads the lift back as the original map. -/
@[reassoc]
lemma closedPointLift_globalSections :
    (closedPointGlobalSectionsIso Y).hom ≫ Γ.map (closedPointLift f hf).op =
      Γ.map f.op := by
  rw [closedPointGlobalSectionsIso_hom, ← Functor.map_comp, ← op_comp,
    closedPointLift_comp_fromClosedPoints]

end AlgebraicGeometry.LocallyRingedSpace
