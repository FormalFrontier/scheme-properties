/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Composition
public import Mathlib.Topology.Maps.Basic

@[expose] public section

/-!
# Pulling back dense opens along partial and rational maps

The density in `PartialMap.PullsDenseOpens` is measured in the entire source scheme,
not merely in the partial map's domain. No irreducibility or dominance is assumed.
-/

set_option warningAsError true

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

namespace PartialMap

/-- Every dense open in the target pulls back to a dense open in the ambient source. -/
def PullsDenseOpens (f : X.PartialMap Y) : Prop :=
  ∀ V : Y.Opens, Dense (V : Set Y) →
    Dense ((f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ V)) : Set X)

private lemma pullback_restrict (f : X.PartialMap Y) (W : X.Opens)
    (hW : Dense (W : Set X)) (hWf : W ≤ f.domain) (V : Y.Opens) :
    W.ι ''ᵁ ((f.restrict W hW hWf).hom ⁻¹ᵁ V) =
      (f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ V)) ⊓ W := by
  simp only [restrict_hom, Hom.comp_preimage, ι_image_homOfLE_eq_ι_image_inf]

/-- Dense-open pullback is independent of a partial-map representative. -/
theorem pullsDenseOpens_iff_of_equiv (f g : X.PartialMap Y) (h : f.equiv g) :
    f.PullsDenseOpens ↔ g.PullsDenseOpens := by
  obtain ⟨W, hW, hWf, hWg, e⟩ := h
  have heq (V : Y.Opens) :
      (f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ V)) ⊓ W =
        (g.domain.ι ''ᵁ (g.hom ⁻¹ᵁ V)) ⊓ W := by
    calc
      _ = W.ι ''ᵁ ((f.restrict W hW hWf).hom ⁻¹ᵁ V) :=
        (pullback_restrict f W hW hWf V).symm
      _ = W.ι ''ᵁ ((g.restrict W hW hWg).hom ⁻¹ᵁ V) := by rw [e]
      _ = _ := pullback_restrict g W hW hWg V
  constructor
  · intro hf V hV
    have hd : Dense ((((f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ V)) ⊓ W) : X.Opens) : Set X) := by
      simpa only [TopologicalSpace.Opens.coe_inf] using
        (hf V hV).inter_of_isOpen_right hW W.2
    rw [heq V] at hd
    exact hd.mono inf_le_left
  · intro hg V hV
    have hd : Dense ((((g.domain.ι ''ᵁ (g.hom ⁻¹ᵁ V)) ⊓ W) : X.Opens) : Set X) := by
      simpa only [TopologicalSpace.Opens.coe_inf] using
        (hg V hV).inter_of_isOpen_right hW W.2
    rw [← heq V] at hd
    exact hd.mono inf_le_left

/-- Restriction to any dense open preserves the ambient dense-open pullback property. -/
theorem pullsDenseOpens_restrict_iff (f : X.PartialMap Y) (W : X.Opens)
    (hW : Dense (W : Set X)) (hWf : W ≤ f.domain) :
    (f.restrict W hW hWf).PullsDenseOpens ↔ f.PullsDenseOpens :=
  pullsDenseOpens_iff_of_equiv _ _ (f.restrict_equiv W hW hWf)

/-- An open underlying map pulls back every dense open densely, with no dominance assumption. -/
theorem pullsDenseOpens_of_isOpenMap (f : X.PartialMap Y) (hf : IsOpenMap f.hom) :
    f.PullsDenseOpens := by
  intro V hV
  have hdense : DenseRange (f.domain.ι : f.domain → X) := by
    simpa only [DenseRange, f.domain.range_ι] using f.dense_domain
  simpa only [Hom.coe_preimage, Hom.coe_image] using
    (hdense.dense_image f.domain.ι.continuous (hV.preimage hf))

/-- The native hypotheses for composition imply dense pullback of all dense opens. -/
theorem pullsDenseOpens_of_isDominant [PreirreducibleSpace X] [Nonempty Y]
    (f : X.PartialMap Y) [IsDominant f.hom] : f.PullsDenseOpens := by
  intro V hV
  exact (f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ V)).2.dense <| by
    simpa [← Set.nonempty_preimage_iff] using
      f.hom.denseRange.inter_open_nonempty _ V.2 hV.nonempty

end PartialMap

namespace RationalMap

/-- Dense-open pullback for the existing quotient of partial maps. -/
def PullsDenseOpens (r : X ⤏ Y) : Prop :=
  ∃ f : X.PartialMap Y, f.toRationalMap = r ∧ f.PullsDenseOpens

end RationalMap

namespace PartialMap

/-- The quotient property is equivalent to the property of any representative. -/
theorem pullsDenseOpens_toRationalMap_iff (f : X.PartialMap Y) :
    f.toRationalMap.PullsDenseOpens ↔ f.PullsDenseOpens := by
  constructor
  · rintro ⟨g, hg, hp⟩
    exact (pullsDenseOpens_iff_of_equiv g f
      (toRationalMap_eq_iff.mp hg)).mp hp
  · exact fun hp => ⟨f, rfl, hp⟩

end PartialMap

namespace RationalMap

/-- Testing an arbitrary chosen representative is sufficient and necessary. -/
theorem pullsDenseOpens_representative_iff (r : X ⤏ Y) :
    r.representative.PullsDenseOpens ↔ r.PullsDenseOpens := by
  rw [← r.representative.pullsDenseOpens_toRationalMap_iff,
    r.toRationalMap_representative]

end RationalMap

end AlgebraicGeometry.Scheme
