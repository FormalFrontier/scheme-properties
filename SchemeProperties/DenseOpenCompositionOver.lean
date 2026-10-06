/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Justus Springer, Formal Frontier Agents
-/
module

public import SchemeProperties.DenseOpenComposition

@[expose] public section

/-!
# Composition of partial and rational maps over a scheme

Dense-open controlled composition preserves a common base for arbitrary schemes.
Neither map needs to be dominant, and no geometric hypotheses on the schemes are needed.

## References

- [Mathlib, `AlgebraicGeometry/Birational/RationalMap.lean`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/AlgebraicGeometry/Birational/RationalMap.lean#L163-L170):
  Andrew Yang's `Scheme.PartialMap.IsOver` and `Scheme.PartialMap.isOver_iff`
  are the native over-base interfaces used here; the relative-composition
  proof is given for the project operation.
- [Mathlib, `AlgebraicGeometry/Birational/Composition.lean`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/AlgebraicGeometry/Birational/Composition.lean#L46-L55):
  Justus Springer's composition and image-isomorphism expression is adapted
  through the controlled composition operation. Preservation of the base
  without dominance is proved for that project operation.
-/

set_option warningAsError true

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X Y Z S : Scheme.{u}} [X.Over S] [Y.Over S] [Z.Over S]

namespace PartialMap

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Dense-open controlled composition of partial maps over `S` remains over `S`. -/
theorem isOver_compOfPullsDenseOpens (f : X.PartialMap Y) (hf : f.PullsDenseOpens)
    (g : Y.PartialMap Z) [f.IsOver S] [g.IsOver S] :
    (f.compOfPullsDenseOpens hf g).IsOver S := by
  have hfOver : f.hom ≫ Y ↘ S = f.domain.ι ≫ X ↘ S := by
    simpa only [compHom_domain, compHom_hom] using (isOver_iff (f := f)).mp ‹f.IsOver S›
  have hgOver : g.hom ≫ Z ↘ S = g.domain.ι ≫ Y ↘ S := by
    simpa only [compHom_domain, compHom_hom] using (isOver_iff (f := g)).mp ‹g.IsOver S›
  apply isOver_iff.mpr
  dsimp only [compHom_domain, compHom_hom, compOfPullsDenseOpens_domain,
    compOfPullsDenseOpens_hom]
  rw [Category.assoc, Category.assoc, hgOver]
  calc
    _ = ((f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ≫
        ((f.hom ∣_ g.domain) ≫ g.domain.ι)) ≫ Y ↘ S := by simp only [Category.assoc]
    _ = ((f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ≫
        (f.hom ⁻¹ᵁ g.domain).ι ≫ f.hom) ≫ Y ↘ S := by rw [morphismRestrict_ι]
    _ = ((f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ≫
        (f.hom ⁻¹ᵁ g.domain).ι ≫ f.domain.ι) ≫ X ↘ S := by
          simp only [Category.assoc, hfOver]
    _ = (f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain).ι ≫ X ↘ S := by
          rw [Scheme.Hom.isoImage_inv_ι]

end PartialMap

namespace RationalMap

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Dense-open controlled composition of rational maps over `S` remains over `S`. -/
theorem isOver_compOfPullsDenseOpens (f : X ⤏ Y) (hf : f.PullsDenseOpens)
    (g : Y ⤏ Z) [f.IsOver S] [g.IsOver S] :
    (f.compOfPullsDenseOpens hf g).IsOver S := by
  obtain ⟨first, hfirst, rfl⟩ := f.exists_partialMap_over S
  obtain ⟨second, hsecond, rfl⟩ := g.exists_partialMap_over S
  have hf' : first.PullsDenseOpens := first.pullsDenseOpens_toRationalMap_iff.mp hf
  let : first.IsOver S := hfirst
  let : second.IsOver S := hsecond
  have hcomp : (first.compOfPullsDenseOpens hf' second).IsOver S :=
    PartialMap.isOver_compOfPullsDenseOpens first hf' second
  rw [toRationalMap_compOfPullsDenseOpens first hf' second]
  exact ⟨first.compOfPullsDenseOpens hf' second, hcomp, rfl⟩

end RationalMap

end AlgebraicGeometry.Scheme
