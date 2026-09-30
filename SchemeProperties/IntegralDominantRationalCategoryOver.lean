module

public import SchemeProperties.DenseOpenRationalCategoryOver
public import SchemeProperties.IntegralDominantRationalCategory
public import SchemeProperties.RationalMapComposition

@[expose] public section

/-!
# Integral dominant rational maps over a scheme

For any scheme `S`, the integral-object full subcategory of dense-open rational
maps over `S` is equivalent to a category whose arrows are dominant native
quotient rational maps admitting an over-`S` representative. The structure
morphisms of objects are arbitrary total morphisms, not necessarily dominant.
-/

set_option warningAsError true
set_option maxHeartbeats 400000

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Integrality of the underlying scheme of a controlled rational object over `S`. -/
abbrev integralDenseOpenOverProperty (S : Scheme.{u}) :
    ObjectProperty (DenseOpenRationalSchemeOver S) := fun X => IsIntegral X.toScheme

/-- The integral-object full subcategory of controlled rational maps over `S`. -/
abbrev IntegralDenseOpenRationalSchemeOver (S : Scheme.{u}) :=
  (integralDenseOpenOverProperty S).FullSubcategory

instance {S : Scheme.{u}} (X : IntegralDenseOpenRationalSchemeOver S) :
    IsIntegral X.obj.toScheme := X.property

namespace IntegralDenseOpenRationalSchemeOver

/-- Package an integral scheme with an arbitrary chosen total map to `S`. -/
def of {S X : Scheme.{u}} [IsIntegral X] (p : X ⟶ S) :
    IntegralDenseOpenRationalSchemeOver S :=
  ⟨DenseOpenRationalSchemeOver.of p, ‹IsIntegral X›⟩

/-- The native rational quotient of an arrow in the integral full subcategory. -/
abbrev toRationalMap {S : Scheme.{u}} {X Y : IntegralDenseOpenRationalSchemeOver S}
    (f : X ⟶ Y) : X.obj.toScheme ⤏ Y.obj.toScheme := f.hom.toRationalMap

instance {S : Scheme.{u}} {X Y : IntegralDenseOpenRationalSchemeOver S} (f : X ⟶ Y) :
    (toRationalMap f).IsDominant :=
  (Scheme.RationalMap.pullsDenseOpens_iff_isDominant _).mp f.hom.pullsDenseOpens

@[simp] theorem toRationalMap_id {S : Scheme.{u}} (X : IntegralDenseOpenRationalSchemeOver S) :
    toRationalMap (𝟙 X) = Scheme.RationalMap.id X.obj.toScheme := rfl

@[simp] theorem toRationalMap_comp {S : Scheme.{u}}
    {X Y Z : IntegralDenseOpenRationalSchemeOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    toRationalMap (f ≫ g) = (toRationalMap f).comp (toRationalMap g) :=
  Scheme.RationalMap.compOfPullsDenseOpens_eq_comp
    f.hom.toRationalMap f.hom.pullsDenseOpens g.hom.toRationalMap

end IntegralDenseOpenRationalSchemeOver

/-- Integral scheme equipped with an arbitrary chosen total structure morphism. -/
structure IntegralDominantRationalSchemeOver (S : Scheme.{u}) where
  toScheme : Scheme.{u}
  toBase : toScheme ⟶ S
  integral : IsIntegral toScheme

namespace IntegralDominantRationalSchemeOver

/-- Package an integral scheme with its chosen total structure morphism. -/
def of {S X : Scheme.{u}} [IsIntegral X] (p : X ⟶ S) :
    IntegralDominantRationalSchemeOver S := ⟨X, p, inferInstance⟩

instance {S : Scheme.{u}} (X : IntegralDominantRationalSchemeOver S) :
    IsIntegral X.toScheme := X.integral

/-- A dominant rational quotient with an over-base partial representative.
The endpoint `Over` dictionaries are chosen from these two objects. -/
structure Hom {S : Scheme.{u}} (X Y : IntegralDominantRationalSchemeOver S) where
  toRationalMap : X.toScheme ⤏ Y.toScheme
  dominant : toRationalMap.IsDominant
  isOver : @Scheme.RationalMap.IsOver _ _ S
    (.ofHom X.toBase) (.ofHom Y.toBase) toRationalMap

instance {S : Scheme.{u}} {X Y : IntegralDominantRationalSchemeOver S} (f : Hom X Y) :
    f.toRationalMap.IsDominant := f.dominant

/-- Bundle a native quotient and its dominance and chosen-map over-base witnesses. -/
def hom {S : Scheme.{u}} {X Y : IntegralDominantRationalSchemeOver S}
    (r : X.toScheme ⤏ Y.toScheme) (hr : r.IsDominant)
    (hS : @Scheme.RationalMap.IsOver _ _ S (.ofHom X.toBase) (.ofHom Y.toBase) r) :
    Hom X Y := ⟨r, hr, hS⟩

@[simp] theorem toRationalMap_hom {S : Scheme.{u}}
    {X Y : IntegralDominantRationalSchemeOver S} (r : X.toScheme ⤏ Y.toScheme)
    (hr : r.IsDominant)
    (hS : @Scheme.RationalMap.IsOver _ _ S (.ofHom X.toBase) (.ofHom Y.toBase) r) :
    (hom r hr hS).toRationalMap = r := rfl

/-- The over-base proof is the native existential condition with the chosen maps. -/
theorem isOver_hom {S : Scheme.{u}} {X Y : IntegralDominantRationalSchemeOver S}
    (r : X.toScheme ⤏ Y.toScheme) (hr : r.IsDominant)
    (hS : @Scheme.RationalMap.IsOver _ _ S (.ofHom X.toBase) (.ofHom Y.toBase) r) :
    (hom r hr hS).isOver = hS := rfl

/-- Characterize the chosen-base condition by equality of rational quotients. -/
theorem isOver_iff_compHom {S : Scheme.{u}}
    {X Y : IntegralDominantRationalSchemeOver S} {r : X.toScheme ⤏ Y.toScheme} :
    @Scheme.RationalMap.IsOver _ _ S (.ofHom X.toBase) (.ofHom Y.toBase) r ↔
      r.compHom Y.toBase = X.toBase.toRationalMap :=
  @Scheme.RationalMap.isOver_iff _ _ S (.ofHom X.toBase) (.ofHom Y.toBase) r

@[ext] theorem hom_ext {S : Scheme.{u}}
    {X Y : IntegralDominantRationalSchemeOver S} {f g : Hom X Y}
    (h : f.toRationalMap = g.toRationalMap) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Native dominant composition, with the three chosen structure morphisms
passed independently to the over-base closure theorem. -/
noncomputable instance {S : Scheme.{u}} : Category (IntegralDominantRationalSchemeOver S) where
  Hom := Hom
  id X := by
    letI : X.toScheme.Over S := .ofHom X.toBase
    exact hom (Scheme.RationalMap.id X.toScheme)
      ((Scheme.RationalMap.pullsDenseOpens_iff_isDominant _).mp
        (Scheme.RationalMap.pullsDenseOpens_id X.toScheme)) inferInstance
  comp {X Y Z} f g :=
    hom (f.toRationalMap.comp g.toRationalMap) inferInstance
      (@Scheme.RationalMap.isOver_comp_of_isDominant_first
        X.toScheme Y.toScheme Z.toScheme S
        (by infer_instance) (by infer_instance)
        (.ofHom X.toBase) (.ofHom Y.toBase) (.ofHom Z.toBase)
        f.toRationalMap f.dominant g.toRationalMap f.isOver g.isOver)
  id_comp f := by
    apply hom_ext
    exact Scheme.RationalMap.id_comp f.toRationalMap
  comp_id f := by
    apply hom_ext
    exact Scheme.RationalMap.comp_id f.toRationalMap
  assoc f g h := by
    apply hom_ext
    exact Scheme.RationalMap.comp_assoc f.toRationalMap g.toRationalMap h.toRationalMap

@[simp] theorem toRationalMap_id {S : Scheme.{u}} (X : IntegralDominantRationalSchemeOver S) :
    (𝟙 X : X ⟶ X).toRationalMap = Scheme.RationalMap.id X.toScheme := rfl

@[simp] theorem toRationalMap_comp {S : Scheme.{u}}
    {X Y Z : IntegralDominantRationalSchemeOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toRationalMap = f.toRationalMap.comp g.toRationalMap := rfl

end IntegralDominantRationalSchemeOver

namespace IntegralDenseOpenRationalSchemeOver

/-- Repackage an integral controlled object as a native dominant object over `S`. -/
abbrev nativeObject {S : Scheme.{u}} (X : IntegralDenseOpenRationalSchemeOver S) :
    IntegralDominantRationalSchemeOver S := ⟨X.obj.toScheme, X.obj.toBase, X.property⟩

/-- Convert dense-open pullback to dominance, preserving the over-base witness. -/
def nativeHom {S : Scheme.{u}} {X Y : IntegralDenseOpenRationalSchemeOver S}
    (f : X ⟶ Y) : nativeObject X ⟶ nativeObject Y :=
  IntegralDominantRationalSchemeOver.hom (toRationalMap f)
    ((Scheme.RationalMap.pullsDenseOpens_iff_isDominant _).mp f.hom.pullsDenseOpens)
    f.hom.isOver

@[simp] theorem nativeHom_toRationalMap {S : Scheme.{u}}
    {X Y : IntegralDenseOpenRationalSchemeOver S} (f : X ⟶ Y) :
    (nativeHom f).toRationalMap = toRationalMap f := rfl

/-- Convert integral controlled rational arrows to dominant native arrows. -/
def toNative {S : Scheme.{u}} : IntegralDenseOpenRationalSchemeOver S ⥤
    IntegralDominantRationalSchemeOver S where
  obj := nativeObject
  map := nativeHom
  map_id _ := IntegralDominantRationalSchemeOver.hom_ext rfl
  map_comp f g := IntegralDominantRationalSchemeOver.hom_ext (toRationalMap_comp f g)

end IntegralDenseOpenRationalSchemeOver

namespace IntegralDominantRationalSchemeOver

/-- Repackage a native dominant object as an integral controlled object. -/
abbrev denseObject {S : Scheme.{u}} (X : IntegralDominantRationalSchemeOver S) :
    IntegralDenseOpenRationalSchemeOver S := ⟨⟨X.toScheme, X.toBase⟩, X.integral⟩

/-- Convert dominance to dense-open pullback, preserving the over-base witness. -/
noncomputable def denseHom {S : Scheme.{u}} {X Y : IntegralDominantRationalSchemeOver S}
    (f : X ⟶ Y) : denseObject X ⟶ denseObject Y :=
  ObjectProperty.homMk (DenseOpenRationalSchemeOver.hom f.toRationalMap
    ((Scheme.RationalMap.pullsDenseOpens_iff_isDominant _).mpr f.dominant) f.isOver)

@[simp] theorem denseHom_toRationalMap {S : Scheme.{u}}
    {X Y : IntegralDominantRationalSchemeOver S} (f : X ⟶ Y) :
    (denseHom f).hom.toRationalMap = f.toRationalMap := rfl

@[simp] theorem denseHom_nativeHom {S : Scheme.{u}}
    {X Y : IntegralDenseOpenRationalSchemeOver S} (f : X ⟶ Y) :
    denseHom (IntegralDenseOpenRationalSchemeOver.nativeHom f) = f := by
  apply ObjectProperty.hom_ext
  apply DenseOpenRationalSchemeOver.hom_ext
  rfl

@[simp] theorem nativeHom_denseHom {S : Scheme.{u}}
    {X Y : IntegralDominantRationalSchemeOver S} (f : X ⟶ Y) :
    IntegralDenseOpenRationalSchemeOver.nativeHom (denseHom f) = f := by
  apply hom_ext
  rfl

/-- Convert native dominant arrows back to the integral full subcategory. -/
noncomputable def toDenseOpen {S : Scheme.{u}} : IntegralDominantRationalSchemeOver S ⥤
    IntegralDenseOpenRationalSchemeOver S where
  obj := denseObject
  map := denseHom
  map_id _ := by
    apply ObjectProperty.hom_ext
    apply DenseOpenRationalSchemeOver.hom_ext
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply DenseOpenRationalSchemeOver.hom_ext
    exact (Scheme.RationalMap.compOfPullsDenseOpens_eq_comp
      f.toRationalMap ((Scheme.RationalMap.pullsDenseOpens_iff_isDominant _).mpr f.dominant)
      g.toRationalMap).symm

end IntegralDominantRationalSchemeOver

namespace IntegralDenseOpenRationalSchemeOver

/-- Natural quotient-identity comparison with the integral full-subcategory round trip. -/
noncomputable def nativeUnitIso {S : Scheme.{u}} :
    𝟭 (IntegralDenseOpenRationalSchemeOver S) ≅
      toNative ⋙ IntegralDominantRationalSchemeOver.toDenseOpen :=
  NatIso.ofComponents (fun X => Iso.refl X) (by
    intro X Y f
    change f ≫ 𝟙 Y = 𝟙 X ≫
      IntegralDominantRationalSchemeOver.denseHom (nativeHom f)
    rw [Category.comp_id, Category.id_comp]
    exact (IntegralDominantRationalSchemeOver.denseHom_nativeHom f).symm)

end IntegralDenseOpenRationalSchemeOver

namespace IntegralDominantRationalSchemeOver

/-- Natural quotient-identity comparison with the native dominant round trip. -/
noncomputable def nativeCounitIso {S : Scheme.{u}} :
    toDenseOpen ⋙ IntegralDenseOpenRationalSchemeOver.toNative ≅
      𝟭 (IntegralDominantRationalSchemeOver S) :=
  NatIso.ofComponents (fun X => Iso.refl X) (by
    intro X Y f
    change IntegralDenseOpenRationalSchemeOver.nativeHom (denseHom f) ≫ 𝟙 Y = 𝟙 X ≫ f
    rw [Category.comp_id, Category.id_comp]
    exact nativeHom_denseHom f)

end IntegralDominantRationalSchemeOver

/-- Quotient-preserving equivalence between integral controlled and native
dominant rational maps over any scheme. -/
noncomputable def integralDenseOpenEquivalenceOver (S : Scheme.{u}) :
    IntegralDenseOpenRationalSchemeOver S ≌ IntegralDominantRationalSchemeOver S where
  functor := IntegralDenseOpenRationalSchemeOver.toNative
  inverse := IntegralDominantRationalSchemeOver.toDenseOpen
  unitIso := IntegralDenseOpenRationalSchemeOver.nativeUnitIso
  counitIso := IntegralDominantRationalSchemeOver.nativeCounitIso
  functor_unitIso_comp X := by
    change IntegralDenseOpenRationalSchemeOver.toNative.map (𝟙 X) ≫
      𝟙 (IntegralDenseOpenRationalSchemeOver.toNative.obj X) = 𝟙 _
    simp

namespace IntegralDenseOpenRationalSchemeOver

/-- Forget the chosen base map, retaining the native quotient and its integral carrier. -/
noncomputable def forget {S : Scheme.{u}} : IntegralDenseOpenRationalSchemeOver S ⥤
    IntegralDenseOpenRationalScheme.{u} where
  obj X := ⟨DenseOpenRationalScheme.of X.obj.toScheme, X.property⟩
  map f := ObjectProperty.homMk
    (DenseOpenRationalScheme.hom (toRationalMap f) f.hom.pullsDenseOpens)
  map_id _ := by
    apply ObjectProperty.hom_ext
    apply DenseOpenRationalScheme.hom_ext
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply DenseOpenRationalScheme.hom_ext
    rfl

@[simp] theorem forget_obj_toScheme {S : Scheme.{u}}
    (X : IntegralDenseOpenRationalSchemeOver S) :
    ((forget (S := S)).obj X).obj.toScheme = X.obj.toScheme := rfl

@[simp] theorem forget_map_toRationalMap {S : Scheme.{u}}
    {X Y : IntegralDenseOpenRationalSchemeOver S} (f : X ⟶ Y) :
    IntegralDenseOpenRationalScheme.toRationalMap ((forget (S := S)).map f) =
      toRationalMap f := rfl

/-- Forgetting a chosen base map is faithful, but need not be full. -/
instance {S : Scheme.{u}} : (forget (S := S)).Faithful where
  map_injective := by
    intro X Y f g h
    apply ObjectProperty.hom_ext
    apply DenseOpenRationalSchemeOver.hom_ext
    exact congrArg IntegralDenseOpenRationalScheme.toRationalMap h

end IntegralDenseOpenRationalSchemeOver

namespace IntegralDominantRationalSchemeOver

/-- Forget the chosen base map and its native existential over-base witness. -/
def forget {S : Scheme.{u}} : IntegralDominantRationalSchemeOver S ⥤
    IntegralDominantRationalScheme.{u} where
  obj X := ⟨X.toScheme, X.integral⟩
  map f := IntegralDominantRationalScheme.hom f.toRationalMap f.dominant
  map_id _ := IntegralDominantRationalScheme.hom_ext rfl
  map_comp _ _ := IntegralDominantRationalScheme.hom_ext rfl

@[simp] theorem forget_obj_toScheme {S : Scheme.{u}}
    (X : IntegralDominantRationalSchemeOver S) :
    ((forget (S := S)).obj X).toScheme = X.toScheme := rfl

@[simp] theorem forget_map_toRationalMap {S : Scheme.{u}}
    {X Y : IntegralDominantRationalSchemeOver S} (f : X ⟶ Y) :
    ((forget (S := S)).map f).toRationalMap = f.toRationalMap := rfl

/-- The dominant forgetful functor is faithful, not generally full. -/
instance {S : Scheme.{u}} : (forget (S := S)).Faithful where
  map_injective := fun {_ _} _ _ h =>
    hom_ext (congrArg IntegralDominantRationalScheme.Hom.toRationalMap h)

end IntegralDominantRationalSchemeOver

namespace IntegralDenseOpenRationalSchemeOver

/-- Forgetting to absolute controlled rational maps commutes with integral
full-subcategory inclusion by an identity-quotient natural isomorphism. -/
noncomputable def forgetInclusionIso {S : Scheme.{u}} :
    (integralDenseOpenOverProperty S).ι ⋙ DenseOpenRationalSchemeOver.forget S ≅
      forget (S := S) ⋙ integralDenseOpenProperty.ι :=
  NatIso.ofComponents (fun X => Iso.refl _) (by
    intro X Y f
    change (DenseOpenRationalSchemeOver.forget S).map f.hom ≫ 𝟙 _ =
      𝟙 _ ≫ ((forget (S := S)).map f).hom
    rw [Category.comp_id, Category.id_comp]
    apply DenseOpenRationalScheme.hom_ext
    rfl)

/-- The relative-to-native conversion commutes with forgetting to the existing
absolute integral dominant category. -/
noncomputable def forgetNativeIso {S : Scheme.{u}} :
    forget (S := S) ⋙ IntegralDenseOpenRationalScheme.toNative ≅
      toNative ⋙ IntegralDominantRationalSchemeOver.forget :=
  NatIso.ofComponents (fun X => Iso.refl _) (by
    intro X Y f
    change IntegralDenseOpenRationalScheme.nativeHom ((forget (S := S)).map f) ≫ 𝟙 _ =
      𝟙 _ ≫ (IntegralDominantRationalSchemeOver.forget (S := S)).map (nativeHom f)
    rw [Category.comp_id, Category.id_comp]
    apply IntegralDominantRationalScheme.hom_ext
    rfl)

/-- The unit has the same rational identity quotient as the absolute unit
after forgetting the chosen base morphism. -/
theorem forget_nativeUnitIso_hom {S : Scheme.{u}}
    (X : IntegralDenseOpenRationalSchemeOver S) :
    (forget (S := S)).map ((nativeUnitIso (S := S)).hom.app X) =
      IntegralDenseOpenRationalScheme.nativeUnitIso.hom.app ((forget (S := S)).obj X) := by
  apply ObjectProperty.hom_ext
  apply DenseOpenRationalScheme.hom_ext
  rfl

end IntegralDenseOpenRationalSchemeOver

namespace IntegralDominantRationalSchemeOver

/-- The native-to-controlled conversion commutes with forgetting to the
existing absolute integral dense-open category. -/
noncomputable def forgetDenseOpenIso {S : Scheme.{u}} :
    forget (S := S) ⋙ IntegralDominantRationalScheme.toDenseOpen ≅
      toDenseOpen ⋙ IntegralDenseOpenRationalSchemeOver.forget :=
  NatIso.ofComponents (fun X => Iso.refl _) (by
    intro X Y f
    change IntegralDominantRationalScheme.denseHom ((forget (S := S)).map f) ≫ 𝟙 _ =
      𝟙 _ ≫ (IntegralDenseOpenRationalSchemeOver.forget (S := S)).map (denseHom f)
    rw [Category.comp_id, Category.id_comp]
    apply ObjectProperty.hom_ext
    apply DenseOpenRationalScheme.hom_ext
    rfl)

/-- The counit has the absolute counit's rational identity quotient after
forgetting the chosen base morphism. -/
theorem forget_nativeCounitIso_hom {S : Scheme.{u}}
    (X : IntegralDominantRationalSchemeOver S) :
    (forget (S := S)).map ((nativeCounitIso (S := S)).hom.app X) =
      IntegralDominantRationalScheme.nativeCounitIso.hom.app ((forget (S := S)).obj X) := by
  apply IntegralDominantRationalScheme.hom_ext
  rfl

end IntegralDominantRationalSchemeOver

end AlgebraicGeometry
