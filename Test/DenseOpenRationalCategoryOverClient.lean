/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.DenseOpenRationalCategoryOver

@[expose] public section

set_option warningAsError true

universe u

open AlgebraicGeometry AlgebraicGeometry.DenseOpenRationalSchemeOver CategoryTheory

namespace SchemePropertiesTest.DenseOpenRationalCategoryOver

private theorem objectScheme {X S : Scheme.{u}} (p : X ⟶ S) :
    (of p).toScheme = X := toScheme_of p

private theorem objectMap {X S : Scheme.{u}} (p : X ⟶ S) :
    (of p).toBase = p := toBase_of p

variable {S : Scheme.{u}}
variable {X Y Z T : DenseOpenRationalSchemeOver S}

private theorem arrowConstructor (r : X.toScheme ⤏ Y.toScheme)
    (hr : r.PullsDenseOpens)
    (hS : @Scheme.RationalMap.IsOver _ _ S
      (.ofHom X.toBase) (.ofHom Y.toBase) r) :
    (hom r hr hS).toRationalMap = r := toRationalMap_hom r hr hS

private theorem nativeOverWitness (f : X ⟶ Y) :
    @Scheme.RationalMap.IsOver _ _ S
      (.ofHom X.toBase) (.ofHom Y.toBase) f.toRationalMap := f.isOver

private theorem nativeOverRepresentative (f : X ⟶ Y) :
    ∃ representative : X.toScheme.PartialMap Y.toScheme,
      (letI : X.toScheme.Over S := .ofHom X.toBase
       letI : Y.toScheme.Over S := .ofHom Y.toBase
       representative.IsOver S) ∧ representative.toRationalMap = f.toRationalMap := by
  exact @Scheme.RationalMap.exists_partialMap_over _ _ S
    (.ofHom X.toBase) (.ofHom Y.toBase) f.toRationalMap f.isOver

private theorem nativeOverProjection (f : X ⟶ Y) :
    f.toRationalMap.compHom Y.toBase = X.toBase.toRationalMap :=
  isOver_iff_compHom.mp f.isOver

private theorem arrowExtensionality (f g : X ⟶ Y)
    (h : f.toRationalMap = g.toRationalMap) : f = g := hom_ext h

private theorem leftIdentity (f : X ⟶ Y) : 𝟙 X ≫ f = f := Category.id_comp f
private theorem rightIdentity (f : X ⟶ Y) : f ≫ 𝟙 Y = f := Category.comp_id f
private theorem associativity (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h) := Category.assoc f g h

private theorem identityProjection (X : DenseOpenRationalSchemeOver S) :
    (𝟙 X : X ⟶ X).toRationalMap = Scheme.RationalMap.id X.toScheme :=
  toRationalMap_id X

private theorem compositionProjection (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toRationalMap =
      f.toRationalMap.compOfPullsDenseOpens f.pullsDenseOpens g.toRationalMap :=
  toRationalMap_comp f g

private theorem compositionOver (f : X ⟶ Y) (g : Y ⟶ Z) :
    @Scheme.RationalMap.IsOver _ _ S
      (.ofHom X.toBase) (.ofHom Z.toBase) (f ≫ g).toRationalMap :=
  (f ≫ g).isOver

private theorem forgetObject (X : DenseOpenRationalSchemeOver S) :
    ((forget S).obj X).toScheme = X.toScheme := forget_obj_toScheme X

private theorem forgetMap (f : X ⟶ Y) :
    ((forget S).map f).toRationalMap = f.toRationalMap :=
  forget_map_toRationalMap f

private theorem forgetIdentity (X : DenseOpenRationalSchemeOver S) :
    (forget S).map (𝟙 X) = 𝟙 ((forget S).obj X) := (forget S).map_id X

private theorem forgetComposition (f : X ⟶ Y) (g : Y ⟶ Z) :
    (forget S).map (f ≫ g) = (forget S).map f ≫ (forget S).map g :=
  (forget S).map_comp f g

private theorem forgetFaithful (f g : X ⟶ Y)
    (h : (forget S).map f = (forget S).map g) : f = g :=
  (forget S).map_injective h

private theorem distinctStructureMaps {V : Scheme.{u}} (p q : V ⟶ S)
    (r : V ⤏ V) (hr : r.PullsDenseOpens)
    (hS : @Scheme.RationalMap.IsOver _ _ S (.ofHom p) (.ofHom q) r) :
    (hom r hr hS : of p ⟶ of q).toRationalMap = r :=
  rfl

private theorem distinctComposition {V : Scheme.{u}} (p q t : V ⟶ S)
    (r s : V ⤏ V) (hr : r.PullsDenseOpens) (hs : s.PullsDenseOpens)
    (hpq : @Scheme.RationalMap.IsOver _ _ S (.ofHom p) (.ofHom q) r)
    (hqt : @Scheme.RationalMap.IsOver _ _ S (.ofHom q) (.ofHom t) s) :
    @Scheme.RationalMap.IsOver _ _ S (.ofHom p) (.ofHom t)
      (let first : (of p : DenseOpenRationalSchemeOver S) ⟶ of q := hom r hr hpq
       let second : (of q : DenseOpenRationalSchemeOver S) ⟶ of t := hom s hs hqt
       (first ≫ second).toRationalMap) := by
  let first : (of p : DenseOpenRationalSchemeOver S) ⟶ of q := hom r hr hpq
  let second : (of q : DenseOpenRationalSchemeOver S) ⟶ of t := hom s hs hqt
  exact (first ≫ second).isOver

end SchemePropertiesTest.DenseOpenRationalCategoryOver
