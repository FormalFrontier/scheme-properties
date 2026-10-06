/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer, Formal Frontier Agents
-/
module

public import SchemeProperties.DenseOpenComposition

@[expose] public section

/-!
# Dense-open pullback under controlled composition

Composing two maps that pull back dense opens densely preserves the property,
without irreducibility, dominance, nonemptiness, or reducedness hypotheses.
The underlying composition operation still requires the first condition only.

## References

- [Mathlib, `AlgebraicGeometry/Birational/Composition.lean`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/AlgebraicGeometry/Birational/Composition.lean#L46-L55):
  the domain normalization used by controlled composition adapts
  `Scheme.PartialMap.comp`. The dense-open pullback closure argument is a
  separate project proof, not an adaptation of a closure theorem there.
-/

set_option warningAsError true

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}}

namespace PartialMap

private lemma compOfPullsDenseOpens_pullback (f : X.PartialMap Y)
    (hf : f.PullsDenseOpens) (g : Y.PartialMap Z) (W : Z.Opens) :
    (f.compOfPullsDenseOpens hf g).domain.ι ''ᵁ
        ((f.compOfPullsDenseOpens hf g).hom ⁻¹ᵁ W) =
      f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ (g.domain.ι ''ᵁ (g.hom ⁻¹ᵁ W))) := by
  change (f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ g.domain)).ι ''ᵁ
    (((f.domain.ι.isoImage _).inv ≫ f.hom ∣_ g.domain ≫ g.hom) ⁻¹ᵁ W) = _
  simp_rw [← Category.assoc, Hom.comp_preimage, Hom.inv_preimage,
    ← Hom.comp_image, Hom.isoImage_hom_ι, Hom.comp_image,
    image_morphismRestrict_preimage]

/-- Both factors pulling back dense opens densely makes their controlled composite do so. -/
theorem pullsDenseOpens_compOfPullsDenseOpens (f : X.PartialMap Y)
    (hf : f.PullsDenseOpens) (g : Y.PartialMap Z) (hg : g.PullsDenseOpens) :
    (f.compOfPullsDenseOpens hf g).PullsDenseOpens := by
  intro W hW
  rw [compOfPullsDenseOpens_pullback]
  exact hf _ (hg W hW)

end PartialMap

namespace RationalMap

/-- The existing quotient composition preserves dense-open pullback when both factors do. -/
theorem pullsDenseOpens_compOfPullsDenseOpens (f : X ⤏ Y)
    (hf : f.PullsDenseOpens) (g : Y ⤏ Z) (hg : g.PullsDenseOpens) :
    (f.compOfPullsDenseOpens hf g).PullsDenseOpens := by
  have hfirst : f.representative.PullsDenseOpens :=
    f.pullsDenseOpens_representative_iff.mpr hf
  have hsecond : g.representative.PullsDenseOpens :=
    g.pullsDenseOpens_representative_iff.mpr hg
  let comp := f.representative.compOfPullsDenseOpens hfirst g.representative
  have hcomp := comp.pullsDenseOpens_toRationalMap_iff.mpr
    (f.representative.pullsDenseOpens_compOfPullsDenseOpens hfirst g.representative hsecond)
  rw [← g.toRationalMap_representative, compOfPullsDenseOpens_def]
  exact hcomp

end RationalMap

end AlgebraicGeometry.Scheme
