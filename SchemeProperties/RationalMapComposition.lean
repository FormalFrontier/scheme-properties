/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents (Hive Task hive-request-d04a528c8fefc542b1e53f2a0d565eecd90fde23,
  UID 94b1be7d-b4fc-4bc6-8fcf-c08d31f48c9e)
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Composition

/-! # Relative composition of partial and rational maps

The native composition of a dominant first map and an arbitrary second map respects a common
base, without requiring the second map to be dominant.
-/

set_option warningAsError true

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X Y Z S : Scheme.{u}} [PreirreducibleSpace X] [Nonempty Y]
variable [X.Over S] [Y.Over S] [Z.Over S]

namespace PartialMap

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Composition of `S`-partial maps preserves the base when the first map is dominant;
no dominance condition is imposed on the second partial map. -/
theorem isOver_comp_of_isDominant_first (f : X.PartialMap Y) [IsDominant f.hom]
    (g : Y.PartialMap Z) [f.IsOver S] [g.IsOver S] : (f.comp g).IsOver S := by
  have hf : f.hom ≫ Y ↘ S = f.domain.ι ≫ X ↘ S := by
    simpa only [compHom_domain, compHom_hom] using (isOver_iff (f := f)).mp ‹f.IsOver S›
  have hg : g.hom ≫ Z ↘ S = g.domain.ι ≫ Y ↘ S := by
    simpa only [compHom_domain, compHom_hom] using (isOver_iff (f := g)).mp ‹g.IsOver S›
  apply isOver_iff.mpr
  dsimp only [compHom_domain, compHom_hom, comp_domain, comp_hom]
  rw [Category.assoc, Category.assoc, hg]
  calc
    _ = ((f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ≫
        ((f.hom ∣_ g.domain) ≫ g.domain.ι)) ≫ Y ↘ S := by simp only [Category.assoc]
    _ = ((f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ≫
        (f.hom ⁻¹ᵁ g.domain).ι ≫ f.hom) ≫ Y ↘ S := by rw [morphismRestrict_ι]
    _ = ((f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ≫
        (f.hom ⁻¹ᵁ g.domain).ι ≫ f.domain.ι) ≫ X ↘ S := by
          simp only [Category.assoc, hf]
    _ = (f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain).ι ≫ X ↘ S := by
          rw [Scheme.Hom.isoImage_inv_ι]

end PartialMap

namespace RationalMap

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Composition of `S`-rational maps preserves the base when the first map is dominant;
the second rational map need not be dominant. -/
theorem isOver_comp_of_isDominant_first (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z)
    [f.IsOver S] [g.IsOver S] : (f.comp g).IsOver S := by
  obtain ⟨first, hfirst, rfl⟩ := f.exists_partialMap_over S
  obtain ⟨second, hsecond, rfl⟩ := g.exists_partialMap_over S
  have : IsDominant first.hom := by
    rwa [← first.isDominant_toRationalMap_iff]
  have : first.IsOver S := hfirst
  have : second.IsOver S := hsecond
  rw [toRationalMap_comp]
  let : (first.comp second).IsOver S := PartialMap.isOver_comp_of_isDominant_first first second
  infer_instance

end RationalMap

end AlgebraicGeometry.Scheme
