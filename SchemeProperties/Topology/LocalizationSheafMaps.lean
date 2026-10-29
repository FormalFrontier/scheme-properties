/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Uniqueness of maps from localization presheaves

Let a presheaf of commutative rings have compatible actions of a ring `R`,
and let its sections on a basis indexed by `r : R` be localizations away
from `r`. Maps from this presheaf to a sheaf are determined by their maps
on global coordinates. No algebra structure on the target is required.

The proof uses the uniqueness of homomorphisms out of a localization on
each basis open, then `TopCat.Sheaf.hom_ext` to pass to all opens. The
source need not be a sheaf. In particular, the target may be the
pushforward of a sheaf along a fixed continuous map.
-/

@[expose] public section

universe u v w

open CategoryTheory TopologicalSpace Opposite

namespace TopCat.Presheaf

/-- Maps from a presheaf whose basis sections are localizations away from the
indexing coordinate are determined by their values on global coordinates.
Only the target is required to satisfy the sheaf condition. -/
theorem hom_ext_of_isLocalizationAway {X : TopCat.{w}} (R : Type u) [CommRing R]
    (F : X.Presheaf CommRingCat.{v}) (G : Sheaf CommRingCat.{v} X)
    (B : R → Opens X) (hB : Opens.IsBasis (Set.range B))
    [∀ U, Algebra R (F.obj U)]
    [∀ r : R, IsLocalization.Away r (F.obj (op (B r)))]
    (hF : ∀ {U V : Opens X} (i : U ⟶ V) (r : R),
      F.map i.op (algebraMap R _ r) = algebraMap R _ r)
    {α β : F ⟶ G.obj}
    (h : (α.app (op ⊤)).hom.comp (algebraMap R _) =
      (β.app (op ⊤)).hom.comp (algebraMap R _)) : α = β := by
  apply TopCat.Sheaf.hom_ext F G hB
  intro r
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (Submonoid.powers r)
  ext x
  change α.app (op (B r)) (algebraMap R _ x) =
    β.app (op (B r)) (algebraMap R _ x)
  let i : B r ⟶ ⊤ := homOfLE le_top
  have hα := congrArg (fun g => g (algebraMap R (F.obj (op ⊤)) x))
    (α.naturality i.op)
  have hβ := congrArg (fun g => g (algebraMap R (F.obj (op ⊤)) x))
    (β.naturality i.op)
  simp only [ConcreteCategory.comp_apply, hF] at hα hβ
  have hx : α.app (op ⊤) (algebraMap R _ x) =
      β.app (op ⊤) (algebraMap R _ x) :=
    DFunLike.congr_fun h x
  exact hα.trans ((congrArg (G.obj.map i.op) hx).trans hβ.symm)

end TopCat.Presheaf
