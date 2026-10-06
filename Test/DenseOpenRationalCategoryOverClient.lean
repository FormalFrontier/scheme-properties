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

example {X S : Scheme.{u}} (p : X ⟶ S) :
    (of p).toScheme = X := toScheme_of p

example {X S : Scheme.{u}} (p : X ⟶ S) :
    (of p).toBase = p := toBase_of p

variable {S : Scheme.{u}}
variable {X Y Z T : DenseOpenRationalSchemeOver S}

example (r : X.toScheme ⤏ Y.toScheme)
    (hr : r.PullsDenseOpens)
    (hS : @Scheme.RationalMap.IsOver _ _ S
      (.ofHom X.toBase) (.ofHom Y.toBase) r) :
    (hom r hr hS).toRationalMap = r := toRationalMap_hom r hr hS

example (f : X ⟶ Y) :
    @Scheme.RationalMap.IsOver _ _ S
      (.ofHom X.toBase) (.ofHom Y.toBase) f.toRationalMap := f.isOver

example (f : X ⟶ Y) :
    ∃ representative : X.toScheme.PartialMap Y.toScheme,
      (letI : X.toScheme.Over S := .ofHom X.toBase
       letI : Y.toScheme.Over S := .ofHom Y.toBase
       representative.IsOver S) ∧ representative.toRationalMap = f.toRationalMap := by
  exact @Scheme.RationalMap.exists_partialMap_over _ _ S
    (.ofHom X.toBase) (.ofHom Y.toBase) f.toRationalMap f.isOver

example (f : X ⟶ Y) :
    f.toRationalMap.compHom Y.toBase = X.toBase.toRationalMap :=
  isOver_iff_compHom.mp f.isOver

example (f g : X ⟶ Y)
    (h : f.toRationalMap = g.toRationalMap) : f = g := hom_ext h

example (f : X ⟶ Y) : 𝟙 X ≫ f = f := Category.id_comp f
example (f : X ⟶ Y) : f ≫ 𝟙 Y = f := Category.comp_id f
example (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h) := Category.assoc f g h

example (X : DenseOpenRationalSchemeOver S) :
    (𝟙 X : X ⟶ X).toRationalMap = Scheme.RationalMap.id X.toScheme :=
  toRationalMap_id X

example (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toRationalMap =
      f.toRationalMap.compOfPullsDenseOpens f.pullsDenseOpens g.toRationalMap :=
  toRationalMap_comp f g

example (f : X ⟶ Y) (g : Y ⟶ Z) :
    @Scheme.RationalMap.IsOver _ _ S
      (.ofHom X.toBase) (.ofHom Z.toBase) (f ≫ g).toRationalMap :=
  (f ≫ g).isOver

example (X : DenseOpenRationalSchemeOver S) :
    ((forget S).obj X).toScheme = X.toScheme := forget_obj_toScheme X

example (f : X ⟶ Y) :
    ((forget S).map f).toRationalMap = f.toRationalMap :=
  forget_map_toRationalMap f

example (X : DenseOpenRationalSchemeOver S) :
    (forget S).map (𝟙 X) = 𝟙 ((forget S).obj X) := (forget S).map_id X

example (f : X ⟶ Y) (g : Y ⟶ Z) :
    (forget S).map (f ≫ g) = (forget S).map f ≫ (forget S).map g :=
  (forget S).map_comp f g

example (f g : X ⟶ Y)
    (h : (forget S).map f = (forget S).map g) : f = g :=
  (forget S).map_injective h

example {V : Scheme.{u}} (p q : V ⟶ S)
    (r : V ⤏ V) (hr : r.PullsDenseOpens)
    (hS : @Scheme.RationalMap.IsOver _ _ S (.ofHom p) (.ofHom q) r) :
    (hom r hr hS : of p ⟶ of q).toRationalMap = r :=
  rfl

example {V : Scheme.{u}} (p q t : V ⟶ S)
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
