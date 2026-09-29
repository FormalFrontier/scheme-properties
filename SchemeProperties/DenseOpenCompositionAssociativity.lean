/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer, Formal Frontier Agents
-/
module

public import SchemeProperties.DenseOpenCompositionClosure

@[expose] public section

/-!
# Associativity of dense-open-controlled composition

The existing partial-map and rational-map composition operations are associative
when the first two maps pull back dense opens densely. No hypothesis is imposed
on the third map.
-/

set_option warningAsError true

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X Y Z T : Scheme.{u}}

namespace PartialMap

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Controlled composition is associative with the first two dense-open pullback conditions. -/
theorem compOfPullsDenseOpens_assoc (f : X.PartialMap Y) (hf : f.PullsDenseOpens)
    (g : Y.PartialMap Z) (hg : g.PullsDenseOpens) (h : Z.PartialMap T) :
    (f.compOfPullsDenseOpens hf g).compOfPullsDenseOpens
      (f.pullsDenseOpens_compOfPullsDenseOpens hf g hg) h =
      f.compOfPullsDenseOpens hf (g.compOfPullsDenseOpens hg h) := by
  ext
  · simp_rw [compOfPullsDenseOpens_domain, compOfPullsDenseOpens_hom, ← Category.assoc,
      Hom.comp_preimage, Hom.inv_preimage, ← Hom.comp_image, Hom.isoImage_hom_ι,
      Hom.comp_image, image_morphismRestrict_preimage]
  · dsimp
    simp_rw [morphismRestrict_comp, morphismRestrict_ι_image_ι_isoImage_inv_assoc,
      Hom.comp_preimage, Category.assoc]
    conv_lhs => rw [← Category.assoc]
    conv_rhs => rw [← Category.assoc, ← Category.assoc, ← Category.assoc]
    congr 1
    simp [← cancel_mono (Opens.ι _)]

end PartialMap

namespace RationalMap

/-- Controlled composition is associative on native rational-map quotients. -/
theorem compOfPullsDenseOpens_assoc (r : X ⤏ Y) (hr : r.PullsDenseOpens)
    (s : Y ⤏ Z) (hs : s.PullsDenseOpens) (t : Z ⤏ T) :
    (r.compOfPullsDenseOpens hr s).compOfPullsDenseOpens
      (r.pullsDenseOpens_compOfPullsDenseOpens hr s hs) t =
      r.compOfPullsDenseOpens hr (s.compOfPullsDenseOpens hs t) := by
  obtain ⟨f, rfl⟩ := PartialMap.toRationalMap_surjective r
  obtain ⟨g, rfl⟩ := PartialMap.toRationalMap_surjective s
  obtain ⟨h, rfl⟩ := PartialMap.toRationalMap_surjective t
  have hf : f.PullsDenseOpens := f.pullsDenseOpens_toRationalMap_iff.mp hr
  have hg : g.PullsDenseOpens := g.pullsDenseOpens_toRationalMap_iff.mp hs
  rw [toRationalMap_compOfPullsDenseOpens g hg h,
    toRationalMap_compOfPullsDenseOpens f hf (g.compOfPullsDenseOpens hg h)]
  conv_lhs =>
    arg 1
    rw [toRationalMap_compOfPullsDenseOpens f hf g]
  rw [toRationalMap_compOfPullsDenseOpens (f.compOfPullsDenseOpens hf g)
    (f.pullsDenseOpens_compOfPullsDenseOpens hf g hg) h,
    f.compOfPullsDenseOpens_assoc hf g hg h]

end RationalMap

end AlgebraicGeometry.Scheme
