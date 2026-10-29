/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Geometry.RingedSpace.Stalks

/-!
# Stalk maps over inducing maps

A morphism of presheafed spaces whose underlying map is inducing and whose
presheaf component is an isomorphism induces isomorphisms on stalks. This
uses the stalk maps of presheafed-space morphisms, without requiring a sheaf
condition or any algebraic structure on the target category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.PresheafedSpace.stalkMap

variable {C : Type u} [Category.{v} C] [HasColimits C]
  {X Y : PresheafedSpace.{_, _, v} C}

/-- An inducing morphism of presheafed spaces with an isomorphism as its presheaf
component induces an isomorphism on every stalk. -/
theorem isIso_of_isInducing (f : X ⟶ Y) [IsIso f.c]
    (hf : Topology.IsInducing f.base) (x : X) : IsIso (f.stalkMap x) := by
  exact IsIso.comp_isIso'
    ((TopCat.Presheaf.stalkFunctor C (f.base x)).map_isIso f.c)
    (TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing C hf
      X.presheaf x)

end AlgebraicGeometry.PresheafedSpace.stalkMap
