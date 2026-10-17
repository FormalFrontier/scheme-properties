/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.RationalFunctionFieldReconstruction

public section

/-!
# Pulling sections back to function fields

For a dominant morphism of integral schemes, pulling back a section and taking
its germ at the generic point agrees with first taking its generic germ and
then applying the induced homomorphism of function fields. Dominance ensures
that the inverse image of every nonempty open is nonempty.

## References

* Mathlib, `Mathlib.AlgebraicGeometry.Stalk` (Andrew Yang, Fangming Li):
  naturality of the maps from stalk spectra.
* Mathlib, `Mathlib.AlgebraicGeometry.Scheme`: naturality of germs and stalk maps.
* Scheme Properties, `RationalFunctionFieldReconstruction`: compatibility of
  function-field homomorphisms with maps from generic stalk spectra.
-/

set_option warningAsError true

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The inverse image of a nonempty open under a dominant morphism is nonempty. -/
theorem Hom.nonempty_preimage_of_isDominant {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsDominant f] (U : Y.Opens) [Nonempty U] : Nonempty (f ⁻¹ᵁ U) := by
  obtain ⟨y, hyU, x, rfl⟩ :=
    f.denseRange.inter_open_nonempty (U : Set Y) U.isOpen
      (Set.nonempty_coe_sort.mp ‹Nonempty U›)
  exact ⟨⟨x, hyU⟩⟩

attribute [local instance] Hom.nonempty_preimage_of_isDominant

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Pullback of sections along a dominant morphism commutes with the canonical
maps to function fields, on every nonempty open of the target. -/
theorem Hom.app_germToFunctionField (f : X ⟶ Y) [IsDominant f]
    (U : Y.Opens) [Nonempty U] :
    f.app U ≫ X.germToFunctionField (f ⁻¹ᵁ U) =
      Y.germToFunctionField U ≫ f.toRationalMap.functionFieldMap := by
  have hη : f (genericPoint X) = genericPoint Y := by
    apply ((genericPoint_spec Y).eq _).symm
    convert (genericPoint_spec X).image f.continuous using 1
    simpa only [Set.image_univ] using f.denseRange.closure_eq.symm
  have hfield : f.toRationalMap.functionFieldMap =
      (Y.presheaf.stalkCongr (.of_eq hη.symm)).hom ≫ f.stalkMap (genericPoint X) := by
    apply Spec.map_injective
    rw [← cancel_mono (Y.fromSpecStalk (genericPoint Y))]
    calc
      Spec.map f.toRationalMap.functionFieldMap ≫ Y.fromSpecStalk (genericPoint Y) =
          X.fromSpecStalk (genericPoint X) ≫ f := by
        simpa only [Category.comp_id] using
          RationalMap.functionFieldMap_compatible f (𝟙 Y) f.toRationalMap (by
            rw [Hom.toRationalMap, ← RationalMap.compHom_toRationalMap, PartialMap.compHom_id])
      _ = Spec.map ((Y.presheaf.stalkCongr (.of_eq hη.symm)).hom ≫
          f.stalkMap (genericPoint X)) ≫ Y.fromSpecStalk (genericPoint Y) := by
        rw [Spec.map_comp_assoc, TopCat.Presheaf.stalkCongr_hom,
          SpecMap_stalkSpecializes_fromSpecStalk, SpecMap_stalkMap_fromSpecStalk]
  rw [hfield]
  simpa only [germToFunctionField, ← Category.assoc, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.germ_stalkSpecializes] using
    (f.germ_stalkMap U (genericPoint X) (by
      rw [hη]
      exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr
        (by simpa using (Set.nonempty_coe_sort.mp ‹Nonempty U›)))).symm

end AlgebraicGeometry.Scheme
