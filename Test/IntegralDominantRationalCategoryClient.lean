/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.IntegralDominantRationalCategory

@[expose] public section

set_option warningAsError true

universe u

namespace SchemePropertiesTest.IntegralDominantRationalCategory

open AlgebraicGeometry CategoryTheory

private theorem objectConstructor (X : Scheme.{u}) [IsIntegral X] :
    (IntegralDominantRationalScheme.of X).toScheme = X := rfl

private theorem denseObjectConstructor (X : Scheme.{u}) [IsIntegral X] :
    (IntegralDenseOpenRationalScheme.of X).obj.toScheme = X := rfl

variable {X Y Z T : IntegralDominantRationalScheme.{u}}

private theorem arrowConstructor (r : X.toScheme ⤏ Y.toScheme) (hr : r.IsDominant) :
    (IntegralDominantRationalScheme.hom r hr).toRationalMap = r :=
  IntegralDominantRationalScheme.toRationalMap_hom r hr

private theorem arrowExtensionality (f g : X ⟶ Y)
    (h : f.toRationalMap = g.toRationalMap) : f = g :=
  IntegralDominantRationalScheme.hom_ext h

private theorem leftIdentity (f : X ⟶ Y) : 𝟙 X ≫ f = f := Category.id_comp f
private theorem rightIdentity (f : X ⟶ Y) : f ≫ 𝟙 Y = f := Category.comp_id f

private theorem associativity (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h) := Category.assoc f g h

private theorem identityProjection (X : IntegralDominantRationalScheme.{u}) :
    (𝟙 X : X ⟶ X).toRationalMap = Scheme.RationalMap.id X.toScheme :=
  IntegralDominantRationalScheme.toRationalMap_id X

private theorem compositionProjection (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toRationalMap = f.toRationalMap.comp g.toRationalMap :=
  IntegralDominantRationalScheme.toRationalMap_comp f g

variable {A B C : IntegralDenseOpenRationalScheme.{u}}

private theorem controlledProjection (f : A ⟶ B) (g : B ⟶ C) :
    IntegralDenseOpenRationalScheme.toRationalMap (f ≫ g) =
      (IntegralDenseOpenRationalScheme.toRationalMap f).comp
        (IntegralDenseOpenRationalScheme.toRationalMap g) :=
  IntegralDenseOpenRationalScheme.toRationalMap_comp f g

private theorem forwardMapProjection (f : A ⟶ B) :
    (IntegralDenseOpenRationalScheme.toNative.map f).toRationalMap =
      IntegralDenseOpenRationalScheme.toRationalMap f :=
  IntegralDenseOpenRationalScheme.nativeHom_toRationalMap f

private theorem inverseMapProjection (f : X ⟶ Y) :
    (IntegralDominantRationalScheme.toDenseOpen.map f).hom.toRationalMap =
      f.toRationalMap :=
  IntegralDominantRationalScheme.denseHom_toRationalMap f

private theorem equivalenceForward (f : A ⟶ B) :
    (integralDenseOpenEquivalence.functor.map f).toRationalMap =
      IntegralDenseOpenRationalScheme.toRationalMap f :=
  forwardMapProjection f

private theorem equivalenceInverse (f : X ⟶ Y) :
    (integralDenseOpenEquivalence.inverse.map f).hom.toRationalMap =
      f.toRationalMap :=
  inverseMapProjection f

private theorem equivalenceUnit (A : IntegralDenseOpenRationalScheme.{u}) :
    integralDenseOpenEquivalence.unitIso.hom.app A = 𝟙 A := rfl

private theorem equivalenceCounit (X : IntegralDominantRationalScheme.{u}) :
    integralDenseOpenEquivalence.counitIso.hom.app X = 𝟙 X := rfl

end SchemePropertiesTest.IntegralDominantRationalCategory
