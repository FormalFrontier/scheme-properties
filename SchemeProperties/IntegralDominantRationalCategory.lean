/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.DenseOpenRationalCategory
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Equivalence

@[expose] public section

/-!
# Integral schemes and dominant rational maps

`IntegralDominantRationalScheme` has integral schemes as objects and dominant
native quotient rational maps as arrows. Its composition is native
`Scheme.RationalMap.comp`. It is equivalent to the integral-object full
subcategory of `DenseOpenRationalScheme`, whose arrows compose via controlled
dense-open pullbacks. Neither category changes the category of scheme morphisms.
-/

set_option warningAsError true

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The integral-object full subcategory of the dense-open rational-map category. -/
abbrev integralDenseOpenProperty : ObjectProperty DenseOpenRationalScheme.{u} :=
  fun X => IsIntegral X.toScheme

/-- Integral schemes with dense-open-pullback rational maps as arrows. -/
abbrev IntegralDenseOpenRationalScheme :=
  integralDenseOpenProperty.{u}.FullSubcategory

instance (X : IntegralDenseOpenRationalScheme.{u}) : IsIntegral X.obj.toScheme :=
  X.property

namespace IntegralDenseOpenRationalScheme

/-- Package an integral scheme as an object in the dense-open rational-map category. -/
def of (X : Scheme.{u}) [IsIntegral X] : IntegralDenseOpenRationalScheme.{u} :=
  ⟨DenseOpenRationalScheme.of X, ‹IsIntegral X›⟩

/-- The quotient rational map underlying an arrow in the integral full subcategory. -/
abbrev toRationalMap {X Y : IntegralDenseOpenRationalScheme.{u}} (f : X ⟶ Y) :
    X.obj.toScheme ⤏ Y.obj.toScheme := f.hom.toRationalMap

instance {X Y : IntegralDenseOpenRationalScheme.{u}} (f : X ⟶ Y) :
    (toRationalMap f).IsDominant :=
  (Scheme.RationalMap.pullsDenseOpens_iff_isDominant _).mp f.hom.pullsDenseOpens

@[simp] theorem toRationalMap_id (X : IntegralDenseOpenRationalScheme.{u}) :
    toRationalMap (𝟙 X) = Scheme.RationalMap.id X.obj.toScheme := rfl

/-- The controlled composition of integral dense-open arrows agrees with native composition. -/
@[simp] theorem toRationalMap_comp {X Y Z : IntegralDenseOpenRationalScheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    toRationalMap (f ≫ g) = (toRationalMap f).comp (toRationalMap g) := by
  exact Scheme.RationalMap.compOfPullsDenseOpens_eq_comp
    f.hom.toRationalMap f.hom.pullsDenseOpens g.hom.toRationalMap

end IntegralDenseOpenRationalScheme

/-- An integral scheme regarded as an object with dominant quotient rational-map arrows. -/
structure IntegralDominantRationalScheme where
  toScheme : Scheme.{u}
  integral : IsIntegral toScheme

namespace IntegralDominantRationalScheme

/-- Regard an integral scheme as an object of the dominant rational-map category. -/
def of (X : Scheme.{u}) [IsIntegral X] : IntegralDominantRationalScheme.{u} :=
  ⟨X, inferInstance⟩

instance (X : IntegralDominantRationalScheme.{u}) : IsIntegral X.toScheme :=
  X.integral

/-- A dominant native quotient rational map, with a proof-only dominance field. -/
structure Hom (X Y : IntegralDominantRationalScheme.{u}) where
  toRationalMap : X.toScheme ⤏ Y.toScheme
  dominant : toRationalMap.IsDominant

instance {X Y : IntegralDominantRationalScheme.{u}} (f : Hom X Y) :
    f.toRationalMap.IsDominant := f.dominant

/-- Package a dominant native quotient rational map as an arrow. -/
def hom {X Y : IntegralDominantRationalScheme.{u}} (r : X.toScheme ⤏ Y.toScheme)
    (hr : r.IsDominant) : Hom X Y := ⟨r, hr⟩

@[simp] theorem toRationalMap_hom {X Y : IntegralDominantRationalScheme.{u}}
    (r : X.toScheme ⤏ Y.toScheme) (hr : r.IsDominant) :
    (hom r hr).toRationalMap = r := rfl

/-- Dominant-arrow equality is equality of the underlying quotient rational maps. -/
@[ext] theorem hom_ext {X Y : IntegralDominantRationalScheme.{u}} {f g : Hom X Y}
    (h : f.toRationalMap = g.toRationalMap) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Native quotient rational-map composition defines a category of integral schemes. -/
noncomputable instance : Category IntegralDominantRationalScheme.{u} where
  Hom := Hom
  id X := hom (Scheme.RationalMap.id X.toScheme)
    ((Scheme.RationalMap.pullsDenseOpens_iff_isDominant _).mp
      (Scheme.RationalMap.pullsDenseOpens_id X.toScheme))
  comp f g := hom (f.toRationalMap.comp g.toRationalMap) inferInstance
  id_comp f := hom_ext (Scheme.RationalMap.id_comp f.toRationalMap)
  comp_id f := hom_ext (Scheme.RationalMap.comp_id f.toRationalMap)
  assoc f g h := hom_ext (Scheme.RationalMap.comp_assoc
    f.toRationalMap g.toRationalMap h.toRationalMap)

@[simp] theorem toRationalMap_id (X : IntegralDominantRationalScheme.{u}) :
    (𝟙 X : X ⟶ X).toRationalMap = Scheme.RationalMap.id X.toScheme := rfl

@[simp] theorem toRationalMap_comp {X Y Z : IntegralDominantRationalScheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toRationalMap = f.toRationalMap.comp g.toRationalMap := rfl

end IntegralDominantRationalScheme

namespace IntegralDenseOpenRationalScheme

/-- Forget and repackage an integral dense-open object as a native dominant object. -/
abbrev nativeObject (X : IntegralDenseOpenRationalScheme.{u}) :
    IntegralDominantRationalScheme.{u} := ⟨X.obj.toScheme, X.property⟩

/-- The dominant native arrow underlying an integral dense-open arrow. -/
def nativeHom {X Y : IntegralDenseOpenRationalScheme.{u}} (f : X ⟶ Y) :
    nativeObject X ⟶ nativeObject Y :=
  IntegralDominantRationalScheme.hom (toRationalMap f)
    ((Scheme.RationalMap.pullsDenseOpens_iff_isDominant _).mp f.hom.pullsDenseOpens)

@[simp] theorem nativeHom_toRationalMap {X Y : IntegralDenseOpenRationalScheme.{u}}
    (f : X ⟶ Y) : (nativeHom f).toRationalMap = toRationalMap f := rfl

/-- Map from integral dense-open rational arrows to dominant native rational arrows. -/
def toNative : IntegralDenseOpenRationalScheme.{u} ⥤
    IntegralDominantRationalScheme.{u} where
  obj := nativeObject
  map := nativeHom
  map_id X := by
    apply IntegralDominantRationalScheme.hom_ext
    rfl
  map_comp f g := by
    apply IntegralDominantRationalScheme.hom_ext
    exact toRationalMap_comp f g

end IntegralDenseOpenRationalScheme

namespace IntegralDominantRationalScheme

/-- Repackage a native dominant object as an integral dense-open object. -/
abbrev denseObject (X : IntegralDominantRationalScheme.{u}) :
    IntegralDenseOpenRationalScheme.{u} :=
  ⟨⟨X.toScheme⟩, X.integral⟩

/-- Pull a dominant native arrow back into the integral dense-open category. -/
noncomputable def denseHom {X Y : IntegralDominantRationalScheme.{u}} (f : X ⟶ Y) :
    denseObject X ⟶ denseObject Y :=
  ObjectProperty.homMk (DenseOpenRationalScheme.hom f.toRationalMap
    ((Scheme.RationalMap.pullsDenseOpens_iff_isDominant _).mpr f.dominant))

@[simp] theorem denseHom_toRationalMap {X Y : IntegralDominantRationalScheme.{u}}
    (f : X ⟶ Y) : (denseHom f).hom.toRationalMap = f.toRationalMap := rfl

@[simp] theorem denseHom_nativeHom {X Y : IntegralDenseOpenRationalScheme.{u}}
    (f : X ⟶ Y) : denseHom (IntegralDenseOpenRationalScheme.nativeHom f) = f := by
  apply ObjectProperty.hom_ext
  apply DenseOpenRationalScheme.hom_ext
  rfl

@[simp] theorem nativeHom_denseHom {X Y : IntegralDominantRationalScheme.{u}}
    (f : X ⟶ Y) : IntegralDenseOpenRationalScheme.nativeHom (denseHom f) = f := by
  apply hom_ext
  rfl

/-- Map from native dominant rational arrows to integral dense-open arrows. -/
noncomputable def toDenseOpen : IntegralDominantRationalScheme.{u} ⥤
    IntegralDenseOpenRationalScheme.{u} where
  obj := denseObject
  map := denseHom
  map_id X := by
    apply ObjectProperty.hom_ext
    apply DenseOpenRationalScheme.hom_ext
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply DenseOpenRationalScheme.hom_ext
    exact (Scheme.RationalMap.compOfPullsDenseOpens_eq_comp
      f.toRationalMap ((Scheme.RationalMap.pullsDenseOpens_iff_isDominant _).mpr f.dominant)
      g.toRationalMap).symm

end IntegralDominantRationalScheme

namespace IntegralDenseOpenRationalScheme

/-- Natural identification of an integral dense-open object with its round trip. -/
noncomputable def nativeUnitIso : 𝟭 IntegralDenseOpenRationalScheme.{u} ≅
    toNative ⋙ IntegralDominantRationalScheme.toDenseOpen :=
  NatIso.ofComponents (fun X => Iso.refl X) (by
    intro X Y f
    change f ≫ 𝟙 Y = 𝟙 X ≫
      IntegralDominantRationalScheme.denseHom (nativeHom f)
    rw [Category.comp_id]
    rw [Category.id_comp]
    exact (IntegralDominantRationalScheme.denseHom_nativeHom f).symm)

end IntegralDenseOpenRationalScheme

namespace IntegralDominantRationalScheme

/-- Natural identification of a native dominant object with its round trip. -/
noncomputable def nativeCounitIso : toDenseOpen ⋙ IntegralDenseOpenRationalScheme.toNative ≅
    𝟭 IntegralDominantRationalScheme.{u} :=
  NatIso.ofComponents (fun X => Iso.refl X) (by
    intro X Y f
    change IntegralDenseOpenRationalScheme.nativeHom (denseHom f) ≫ 𝟙 Y =
      𝟙 X ≫ f
    rw [Category.comp_id]
    rw [Category.id_comp]
    exact nativeHom_denseHom f)

end IntegralDominantRationalScheme

/-- An equivalence between integral dense-open rational maps and dominant native
quotient rational maps, preserving their underlying maps. -/
noncomputable def integralDenseOpenEquivalence : IntegralDenseOpenRationalScheme.{u} ≌
    IntegralDominantRationalScheme.{u} where
  functor := IntegralDenseOpenRationalScheme.toNative
  inverse := IntegralDominantRationalScheme.toDenseOpen
  unitIso := IntegralDenseOpenRationalScheme.nativeUnitIso
  counitIso := IntegralDominantRationalScheme.nativeCounitIso
  functor_unitIso_comp X := by
    change IntegralDenseOpenRationalScheme.toNative.map (𝟙 X) ≫
      𝟙 (IntegralDenseOpenRationalScheme.toNative.obj X) = 𝟙 _
    simp

end AlgebraicGeometry
