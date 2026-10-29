/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.Topology.ClosedPointOpens
public import SchemeProperties.Topology.OpensSiteEquivalence
public import SchemeProperties.Topology.PresheafedSpaceStalks
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Topology.Sheaves.CommRingCat

/-!
# Locally ringed spaces on closed points

For a Jacobson locally ringed space, the inverse image map from its opens to
opens of its closed-point subspace is an order isomorphism. Transporting its
structure sheaf along this isomorphism gives a locally ringed space on the
closed points. The inclusion has an isomorphism as its sheaf component and on
all stalks, but need not be an isomorphism of spaces.

The construction uses Mathlib's equivalence of sheaf categories and inducing-map
pushforward stalks. No separation or nonemptiness assumptions are needed.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Functor TopCat TopologicalSpace Opposite Topology

namespace AlgebraicGeometry.SheafedSpace

/-- Forgetting the sheaf condition returns the structure presheaf. -/
@[simp]
lemma sheaf_obj {C : Type*} [Category* C] (X : SheafedSpace C) :
    X.sheaf.obj = X.presheaf := rfl

end AlgebraicGeometry.SheafedSpace

namespace AlgebraicGeometry.LocallyRingedSpace

variable (X : LocallyRingedSpace.{u}) [JacobsonSpace X]

/-- The inclusion of the closed-point subspace into the underlying space. -/
@[simps!]
def closedPointInclusion : TopCat.of (closedPoints X) ⟶ X.toTopCat :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The structure sheaf transported to the subspace of closed points. -/
def closedPointSheaf : Sheaf CommRingCat (TopCat.of (closedPoints X)) := by
  let e := (Opens.closedPointsOrderIso X).equivalence
  letI : e.inverse.IsDenseSubsite
      (Opens.grothendieckTopology (closedPoints X)) (Opens.grothendieckTopology X) :=
    (Opens.closedPointsOrderIso X).symm.isDenseSubsite_opens
  exact (e.sheafCongr (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology (closedPoints X)) CommRingCat).functor.obj X.sheaf

/-- The comparison with the pushforward of the closed-point structure sheaf. -/
def closedPointSheafIso : X.presheaf ≅
    (closedPointInclusion X) _* (closedPointSheaf X).obj :=
  isoWhiskerRight (Opens.closedPointsOrderIso X).equivalence.op.unitIso X.presheaf

/-- The sheafed space with the closed points and the transported structure sheaf. -/
def closedPointSheafedSpace : SheafedSpace CommRingCat where
  carrier := TopCat.of (closedPoints X)
  presheaf := (closedPointSheaf X).obj
  IsSheaf := (closedPointSheaf X).property

/-- The inclusion as a morphism of presheafed spaces. -/
@[simps]
def closedPointPresheafedSpaceHom :
    (closedPointSheafedSpace X).toPresheafedSpace ⟶ X.toPresheafedSpace where
  base := closedPointInclusion X
  c := (closedPointSheafIso X).hom

@[simp]
lemma closedPointPresheafedSpaceHom_base_apply (x : closedPointSheafedSpace X) :
    (closedPointPresheafedSpaceHom X).base x = x.val := rfl

/-- Inverse image under the inclusion is the closed-point trace of an ambient open. -/
@[simp]
lemma closedPointPresheafedSpaceHom_preimage (U : Opens X) :
    (Opens.map (closedPointPresheafedSpaceHom X).base).obj U =
      (Opens.closedPointsOrderIso X) U := rfl

/-- The inclusion's component is restriction along the ambient open reconstructed
from its closed-point trace. -/
@[simp]
lemma closedPointPresheafedSpaceHom_c_app (U : Opens X) :
    (closedPointPresheafedSpaceHom X).c.app (op U) =
      X.presheaf.map (eqToHom ((Opens.closedPointsOrderIso X).symm_apply_apply U)).op := rfl

instance closedPointPresheafedSpaceHom_c_isIso :
    IsIso (closedPointPresheafedSpaceHom X).c :=
  (closedPointSheafIso X).isIso_hom

instance closedPointPresheafedSpaceHom_stalkMap_isIso (x : closedPointSheafedSpace X) :
    IsIso ((closedPointPresheafedSpaceHom X).stalkMap x) :=
  PresheafedSpace.stalkMap.isIso_of_isInducing _ IsInducing.subtypeVal x

/-- The locally ringed space on the closed points of a Jacobson locally ringed space. -/
def closedPointSpace : LocallyRingedSpace where
  toSheafedSpace := closedPointSheafedSpace X
  isLocalRing x :=
    (asIso ((closedPointPresheafedSpaceHom X).stalkMap x)).commRingCatIsoToRingEquiv.isLocalRing

/-- The canonical morphism from the closed-point locally ringed space. -/
@[simps! toHom]
def fromClosedPoints : closedPointSpace X ⟶ X where
  toHom := closedPointPresheafedSpaceHom X
  prop x := @isLocalHom_of_isIso _ _
    ((closedPointPresheafedSpaceHom X).stalkMap x)
    (closedPointPresheafedSpaceHom_stalkMap_isIso X x)

instance fromClosedPoints_c_isIso : IsIso (fromClosedPoints X).c :=
  (closedPointSheafIso X).isIso_hom

/-- The canonical map on stalks is an isomorphism. -/
instance fromClosedPoints_stalkMap_isIso (x : closedPointSpace X) :
    IsIso ((fromClosedPoints X).stalkMap x) := by
  have : IsIso (fromClosedPoints X).toHom.c := (closedPointSheafIso X).isIso_hom
  exact PresheafedSpace.stalkMap.isIso_of_isInducing
    (fromClosedPoints X).toHom IsInducing.subtypeVal x

/-- The comparison as an isomorphism of full sheaves of commutative rings. -/
def closedPointSheafComparison : X.sheaf ≅
    (TopCat.Sheaf.pushforward CommRingCat (closedPointInclusion X)).obj
      (closedPointSpace X).sheaf :=
  ObjectProperty.isoMk _ (closedPointSheafIso X)

@[simp]
lemma closedPointSheafComparison_hom_hom :
    (closedPointSheafComparison X).hom.hom = (fromClosedPoints X).c := rfl

/-- The isomorphism of full stalks induced by the inclusion. -/
def closedPointStalkIso (x : closedPointSpace X) :
    X.presheaf.stalk x.val ≅ (closedPointSpace X).presheaf.stalk x :=
  @asIso CommRingCat _ _ _ ((fromClosedPoints X).stalkMap x)
    (fromClosedPoints_stalkMap_isIso X x)

@[simp]
lemma fromClosedPoints_base_apply (x : closedPointSpace X) :
    (fromClosedPoints X).base x = x.val := rfl

@[simp]
lemma closedPointStalkIso_hom (x : closedPointSpace X) :
    (closedPointStalkIso X x).hom = (fromClosedPoints X).stalkMap x := rfl

/-- The comparison on every open is the component of the canonical morphism. -/
def closedPointSectionsIso (U : Opens X) :
    X.presheaf.obj (op U) ≅ (closedPointSpace X).presheaf.obj
      (op ((Opens.closedPointsOrderIso X) U)) :=
  (closedPointSheafIso X).app (op U)

@[simp]
lemma closedPointSectionsIso_hom (U : Opens X) :
    (closedPointSectionsIso X U).hom = (fromClosedPoints X).c.app (op U) := rfl

/-- The canonical inclusion induces an isomorphism on global sections. -/
def closedPointGlobalSectionsIso : Γ.obj (op X) ≅ Γ.obj (op (closedPointSpace X)) :=
  closedPointSectionsIso X ⊤

@[simp]
lemma closedPointGlobalSectionsIso_hom :
    (closedPointGlobalSectionsIso X).hom = Γ.map (fromClosedPoints X).op := rfl

instance fromClosedPoints_Γ_isIso : IsIso (Γ.map (fromClosedPoints X).op) :=
  (closedPointGlobalSectionsIso X).isIso_hom

/-- The all-open comparison commutes with every restriction map. -/
@[reassoc]
lemma closedPointSectionsIso_naturality {U V : Opens X} (i : U ⟶ V) :
    X.presheaf.map i.op ≫ (closedPointSectionsIso X U).hom =
      (closedPointSectionsIso X V).hom ≫
        (closedPointSpace X).presheaf.map
          ((Opens.closedPointsOrderIso X).monotone.functor.map i).op :=
  (fromClosedPoints X).c.naturality i.op

/-- The comparison on stalks is compatible with the germs of every section. -/
@[reassoc]
lemma closedPointSectionsIso_germ (U : Opens X) (x : closedPointSpace X) (hx : x.val ∈ U) :
    X.presheaf.germ U x.val hx ≫ (closedPointStalkIso X x).hom =
      (closedPointSectionsIso X U).hom ≫
        (closedPointSpace X).presheaf.germ ((Opens.closedPointsOrderIso X) U) x hx :=
  LocallyRingedSpace.stalkMap_germ (fromClosedPoints X) U x hx

/-- The inclusion of closed points is a monomorphism of locally ringed spaces. -/
instance fromClosedPoints_mono : Mono (fromClosedPoints X) := by
  apply forgetToSheafedSpace.mono_of_mono_map
  refine SheafedSpace.mono_of_base_injective_of_stalk_epi
    (fromClosedPoints X).toShHom Subtype.val_injective (fun x => ?_)
  exact @IsIso.epi_of_iso _ _ _ _ ((fromClosedPoints X).stalkMap x)
    (fromClosedPoints_stalkMap_isIso X x)

/-- Morphisms into the closed-point space are determined after its inclusion. -/
lemma fromClosedPoints_hom_ext {T : LocallyRingedSpace.{u}}
    {f g : T ⟶ closedPointSpace X}
    (h : f ≫ fromClosedPoints X = g ≫ fromClosedPoints X) : f = g :=
  (cancel_mono (fromClosedPoints X)).mp h

end AlgebraicGeometry.LocallyRingedSpace
