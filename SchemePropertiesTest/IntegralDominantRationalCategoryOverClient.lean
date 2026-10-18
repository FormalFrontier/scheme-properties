/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.IntegralDominantRationalCategoryOver

@[expose] public section

set_option warningAsError true

universe u

open AlgebraicGeometry CategoryTheory

namespace SchemePropertiesTest.IntegralDominantRationalCategoryOver

variable {S : Scheme.{u}}
variable {X Y Z T : IntegralDominantRationalSchemeOver S}
variable {A B C D : IntegralDenseOpenRationalSchemeOver S}

example {V : Scheme.{u}} [IsIntegral V] (p : V ⟶ S) :
    (IntegralDominantRationalSchemeOver.of p).toBase = p := rfl

example {V : Scheme.{u}} [IsIntegral V] (p : V ⟶ S) :
    (IntegralDenseOpenRationalSchemeOver.of p).obj.toBase = p := rfl

example (r : A.obj.toScheme ⤏ B.obj.toScheme)
    (hr : r.PullsDenseOpens)
    (hS : @Scheme.RationalMap.IsOver _ _ S
      (.ofHom A.obj.toBase) (.ofHom B.obj.toBase) r) :
    IntegralDenseOpenRationalSchemeOver.toRationalMap
      (ObjectProperty.homMk (DenseOpenRationalSchemeOver.hom r hr hS) : A ⟶ B) = r := rfl

example (r : X.toScheme ⤏ Y.toScheme)
    (hr : r.IsDominant)
    (hS : @Scheme.RationalMap.IsOver _ _ S (.ofHom X.toBase) (.ofHom Y.toBase) r) :
    (IntegralDominantRationalSchemeOver.hom r hr hS).toRationalMap = r := rfl

example (f : X ⟶ Y) :
    @Scheme.RationalMap.IsOver _ _ S
      (.ofHom X.toBase) (.ofHom Y.toBase) f.toRationalMap := f.isOver

example (f : X ⟶ Y) :
    ∃ representative : X.toScheme.PartialMap Y.toScheme,
      (letI : X.toScheme.Over S := .ofHom X.toBase
       letI : Y.toScheme.Over S := .ofHom Y.toBase
       representative.IsOver S) ∧ representative.toRationalMap = f.toRationalMap :=
  @Scheme.RationalMap.exists_partialMap_over _ _ S
    (.ofHom X.toBase) (.ofHom Y.toBase) f.toRationalMap f.isOver

example (f : X ⟶ Y) :
    f.toRationalMap.compHom Y.toBase = X.toBase.toRationalMap :=
  IntegralDominantRationalSchemeOver.isOver_iff_compHom.mp f.isOver

example (f g : X ⟶ Y)
    (h : f.toRationalMap = g.toRationalMap) : f = g :=
  IntegralDominantRationalSchemeOver.hom_ext h

example (f : X ⟶ Y) : 𝟙 X ≫ f = f := Category.id_comp f
example (f : X ⟶ Y) : f ≫ 𝟙 Y = f :=
  Category.comp_id f
example (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h) := Category.assoc f g h

example (X : IntegralDominantRationalSchemeOver S) :
    (𝟙 X : X ⟶ X).toRationalMap = Scheme.RationalMap.id X.toScheme :=
  IntegralDominantRationalSchemeOver.toRationalMap_id X

example (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toRationalMap = f.toRationalMap.comp g.toRationalMap :=
  IntegralDominantRationalSchemeOver.toRationalMap_comp f g

example (f : X ⟶ Y) (g : Y ⟶ Z) :
    @Scheme.RationalMap.IsOver _ _ S
      (.ofHom X.toBase) (.ofHom Z.toBase) (f ≫ g).toRationalMap :=
  (f ≫ g).isOver

example (f : A ⟶ B) : 𝟙 A ≫ f = f := Category.id_comp f
example (f : A ⟶ B) : f ≫ 𝟙 B = f := Category.comp_id f
example (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h) := Category.assoc f g h

example (f : A ⟶ B) :
    @Scheme.RationalMap.IsOver _ _ S
      (.ofHom A.obj.toBase) (.ofHom B.obj.toBase)
      (IntegralDenseOpenRationalSchemeOver.toRationalMap f) := f.hom.isOver

example (f : A ⟶ B) (g : B ⟶ C) :
    IntegralDenseOpenRationalSchemeOver.toRationalMap (f ≫ g) =
      (IntegralDenseOpenRationalSchemeOver.toRationalMap f).comp
        (IntegralDenseOpenRationalSchemeOver.toRationalMap g) :=
  IntegralDenseOpenRationalSchemeOver.toRationalMap_comp f g

example (A : IntegralDenseOpenRationalSchemeOver S) :
    IntegralDenseOpenRationalSchemeOver.toNative.map (𝟙 A) =
      𝟙 (IntegralDenseOpenRationalSchemeOver.toNative.obj A) :=
  IntegralDenseOpenRationalSchemeOver.toNative.map_id A

example (f : A ⟶ B) (g : B ⟶ C) :
    IntegralDenseOpenRationalSchemeOver.toNative.map (f ≫ g) =
      IntegralDenseOpenRationalSchemeOver.toNative.map f ≫
        IntegralDenseOpenRationalSchemeOver.toNative.map g :=
  IntegralDenseOpenRationalSchemeOver.toNative.map_comp f g

example (X : IntegralDominantRationalSchemeOver S) :
    IntegralDominantRationalSchemeOver.toDenseOpen.map (𝟙 X) =
      𝟙 (IntegralDominantRationalSchemeOver.toDenseOpen.obj X) :=
  IntegralDominantRationalSchemeOver.toDenseOpen.map_id X

example (f : X ⟶ Y) (g : Y ⟶ Z) :
    IntegralDominantRationalSchemeOver.toDenseOpen.map (f ≫ g) =
      IntegralDominantRationalSchemeOver.toDenseOpen.map f ≫
        IntegralDominantRationalSchemeOver.toDenseOpen.map g :=
  IntegralDominantRationalSchemeOver.toDenseOpen.map_comp f g

example (f : A ⟶ B) :
    (IntegralDenseOpenRationalSchemeOver.toNative.map f).toRationalMap =
      IntegralDenseOpenRationalSchemeOver.toRationalMap f := rfl

example (f : X ⟶ Y) :
    (IntegralDominantRationalSchemeOver.toDenseOpen.map f).hom.toRationalMap =
      f.toRationalMap := rfl

example (f : A ⟶ B) :
    IntegralDominantRationalSchemeOver.denseHom
      (IntegralDenseOpenRationalSchemeOver.nativeHom f) = f :=
  IntegralDominantRationalSchemeOver.denseHom_nativeHom f

example (f : X ⟶ Y) :
    IntegralDenseOpenRationalSchemeOver.nativeHom
      (IntegralDominantRationalSchemeOver.denseHom f) = f :=
  IntegralDominantRationalSchemeOver.nativeHom_denseHom f

example (f : A ⟶ B) :
    (IntegralDenseOpenRationalSchemeOver.nativeUnitIso (S := S)).hom.app A ≫
      (IntegralDenseOpenRationalSchemeOver.toNative ⋙
        IntegralDominantRationalSchemeOver.toDenseOpen).map f =
      f ≫ (IntegralDenseOpenRationalSchemeOver.nativeUnitIso (S := S)).hom.app B :=
  (IntegralDenseOpenRationalSchemeOver.nativeUnitIso (S := S)).hom.naturality f |>.symm

example (f : X ⟶ Y) :
    (IntegralDominantRationalSchemeOver.nativeCounitIso (S := S)).hom.app X ≫ f =
      (IntegralDominantRationalSchemeOver.toDenseOpen ⋙
        IntegralDenseOpenRationalSchemeOver.toNative).map f ≫
          (IntegralDominantRationalSchemeOver.nativeCounitIso (S := S)).hom.app Y :=
  (IntegralDominantRationalSchemeOver.nativeCounitIso (S := S)).hom.naturality f |>.symm

example (A : IntegralDenseOpenRationalSchemeOver S) :
    (integralDenseOpenEquivalenceOver S).functor.map
      ((integralDenseOpenEquivalenceOver S).unitIso.hom.app A) ≫
      (integralDenseOpenEquivalenceOver S).counitIso.hom.app
        ((integralDenseOpenEquivalenceOver S).functor.obj A) =
        𝟙 ((integralDenseOpenEquivalenceOver S).functor.obj A) :=
  (integralDenseOpenEquivalenceOver S).functor_unitIso_comp A

example (X : IntegralDominantRationalSchemeOver S) :
    (integralDenseOpenEquivalenceOver S).unitIso.hom.app
      ((integralDenseOpenEquivalenceOver S).inverse.obj X) ≫
      (integralDenseOpenEquivalenceOver S).inverse.map
        ((integralDenseOpenEquivalenceOver S).counitIso.hom.app X) =
      𝟙 ((integralDenseOpenEquivalenceOver S).inverse.obj X) :=
  (integralDenseOpenEquivalenceOver S).unit_inverse_comp X

example (f g : A ⟶ B)
    (h : (IntegralDenseOpenRationalSchemeOver.forget (S := S)).map f =
      (IntegralDenseOpenRationalSchemeOver.forget (S := S)).map g) : f = g :=
  (IntegralDenseOpenRationalSchemeOver.forget (S := S)).map_injective h

example (f g : X ⟶ Y)
    (h : (IntegralDominantRationalSchemeOver.forget (S := S)).map f =
      (IntegralDominantRationalSchemeOver.forget (S := S)).map g) : f = g :=
  (IntegralDominantRationalSchemeOver.forget (S := S)).map_injective h

example (A : IntegralDenseOpenRationalSchemeOver S) :
    (IntegralDenseOpenRationalSchemeOver.forget (S := S)).map (𝟙 A) =
      𝟙 ((IntegralDenseOpenRationalSchemeOver.forget (S := S)).obj A) :=
  (IntegralDenseOpenRationalSchemeOver.forget (S := S)).map_id A

example (f : A ⟶ B) (g : B ⟶ C) :
    (IntegralDenseOpenRationalSchemeOver.forget (S := S)).map (f ≫ g) =
      (IntegralDenseOpenRationalSchemeOver.forget (S := S)).map f ≫
        (IntegralDenseOpenRationalSchemeOver.forget (S := S)).map g :=
  (IntegralDenseOpenRationalSchemeOver.forget (S := S)).map_comp f g

example (X : IntegralDominantRationalSchemeOver S) :
    (IntegralDominantRationalSchemeOver.forget (S := S)).map (𝟙 X) =
      𝟙 ((IntegralDominantRationalSchemeOver.forget (S := S)).obj X) :=
  (IntegralDominantRationalSchemeOver.forget (S := S)).map_id X

example (f : X ⟶ Y) (g : Y ⟶ Z) :
    (IntegralDominantRationalSchemeOver.forget (S := S)).map (f ≫ g) =
      (IntegralDominantRationalSchemeOver.forget (S := S)).map f ≫
        (IntegralDominantRationalSchemeOver.forget (S := S)).map g :=
  (IntegralDominantRationalSchemeOver.forget (S := S)).map_comp f g

example (f : A ⟶ B) :
    ((IntegralDenseOpenRationalSchemeOver.forgetInclusionIso (S := S)).hom).app A ≫
      ((IntegralDenseOpenRationalSchemeOver.forget (S := S)) ⋙
        integralDenseOpenProperty.ι).map f =
      ((integralDenseOpenOverProperty S).ι ⋙ DenseOpenRationalSchemeOver.forget S).map f ≫
        ((IntegralDenseOpenRationalSchemeOver.forgetInclusionIso (S := S)).hom).app B :=
  (IntegralDenseOpenRationalSchemeOver.forgetInclusionIso (S := S)).hom.naturality f |>.symm

example (f : A ⟶ B) :
    (IntegralDenseOpenRationalSchemeOver.forgetNativeIso (S := S)).hom.app A ≫
      (IntegralDenseOpenRationalSchemeOver.toNative ⋙
        IntegralDominantRationalSchemeOver.forget).map f =
      (IntegralDenseOpenRationalSchemeOver.forget (S := S) ⋙
        IntegralDenseOpenRationalScheme.toNative).map f ≫
          (IntegralDenseOpenRationalSchemeOver.forgetNativeIso (S := S)).hom.app B :=
  (IntegralDenseOpenRationalSchemeOver.forgetNativeIso (S := S)).hom.naturality f |>.symm

example (f : X ⟶ Y) :
    (IntegralDominantRationalSchemeOver.forgetDenseOpenIso (S := S)).hom.app X ≫
      (IntegralDominantRationalSchemeOver.toDenseOpen ⋙
        IntegralDenseOpenRationalSchemeOver.forget).map f =
      (IntegralDominantRationalSchemeOver.forget (S := S) ⋙
        IntegralDominantRationalScheme.toDenseOpen).map f ≫
          (IntegralDominantRationalSchemeOver.forgetDenseOpenIso (S := S)).hom.app Y :=
  (IntegralDominantRationalSchemeOver.forgetDenseOpenIso (S := S)).hom.naturality f |>.symm

example (A : IntegralDenseOpenRationalSchemeOver S) :
    (IntegralDenseOpenRationalSchemeOver.forget (S := S)).map
      ((IntegralDenseOpenRationalSchemeOver.nativeUnitIso (S := S)).hom.app A) =
      IntegralDenseOpenRationalScheme.nativeUnitIso.hom.app
        ((IntegralDenseOpenRationalSchemeOver.forget (S := S)).obj A) :=
  IntegralDenseOpenRationalSchemeOver.forget_nativeUnitIso_hom A

example (X : IntegralDominantRationalSchemeOver S) :
    (IntegralDominantRationalSchemeOver.forget (S := S)).map
      ((IntegralDominantRationalSchemeOver.nativeCounitIso (S := S)).hom.app X) =
      IntegralDominantRationalScheme.nativeCounitIso.hom.app
        ((IntegralDominantRationalSchemeOver.forget (S := S)).obj X) :=
  IntegralDominantRationalSchemeOver.forget_nativeCounitIso_hom X

example {V : Scheme.{u}} [IsIntegral V]
    (p q t : V ⟶ S) (r s : V ⤏ V) (hr : r.IsDominant) (hs : s.IsDominant)
    (hpq : @Scheme.RationalMap.IsOver _ _ S (.ofHom p) (.ofHom q) r)
    (hqt : @Scheme.RationalMap.IsOver _ _ S (.ofHom q) (.ofHom t) s) :
    @Scheme.RationalMap.IsOver _ _ S (.ofHom p) (.ofHom t)
      (let first : (IntegralDominantRationalSchemeOver.of p :
          IntegralDominantRationalSchemeOver S) ⟶
            IntegralDominantRationalSchemeOver.of q :=
              IntegralDominantRationalSchemeOver.hom r hr hpq
       let second : (IntegralDominantRationalSchemeOver.of q :
          IntegralDominantRationalSchemeOver S) ⟶
            IntegralDominantRationalSchemeOver.of t :=
              IntegralDominantRationalSchemeOver.hom s hs hqt
       (first ≫ second).toRationalMap) := by
  let first : (IntegralDominantRationalSchemeOver.of p :
      IntegralDominantRationalSchemeOver S) ⟶ IntegralDominantRationalSchemeOver.of q :=
    IntegralDominantRationalSchemeOver.hom r hr hpq
  let second : (IntegralDominantRationalSchemeOver.of q :
      IntegralDominantRationalSchemeOver S) ⟶ IntegralDominantRationalSchemeOver.of t :=
    IntegralDominantRationalSchemeOver.hom s hs hqt
  exact (first ≫ second).isOver

end SchemePropertiesTest.IntegralDominantRationalCategoryOver
