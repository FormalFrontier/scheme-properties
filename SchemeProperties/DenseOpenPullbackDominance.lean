/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.DenseOpenPullback

@[expose] public section

/-!
# Dominance from dense-open pullback

For a partial map with nonempty source and preirreducible target, pulling every
dense target open back densely in the ambient source implies dominance. The
converse uses the existing sufficient condition for a preirreducible source.
-/

set_option warningAsError true

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

namespace PartialMap

/-- A partial map from a nonempty scheme to a preirreducible scheme is dominant
if every dense target open has dense pullback in the ambient source scheme. -/
theorem isDominant_of_pullsDenseOpens [Nonempty X] [PreirreducibleSpace Y]
    (f : X.PartialMap Y) (hf : f.PullsDenseOpens) : IsDominant f.hom := by
  refine ⟨dense_iff_inter_open.mpr ?_⟩
  intro V hV hVne
  let W : Y.Opens := ⟨V, hV⟩
  obtain ⟨x, hx⟩ := (hf W (hV.dense hVne)).nonempty
  rw [Hom.coe_image, Hom.coe_preimage] at hx
  obtain ⟨point, hpoint, _⟩ := hx
  exact ⟨f.hom point, hpoint, ⟨point, rfl⟩⟩

/-- For nonempty preirreducible source and target, dense-open pullback is
equivalent to dominance of the underlying morphism. -/
theorem pullsDenseOpens_iff_isDominant [PreirreducibleSpace X] [Nonempty X]
    [PreirreducibleSpace Y] [Nonempty Y] (f : X.PartialMap Y) :
    f.PullsDenseOpens ↔ IsDominant f.hom := by
  constructor
  · exact f.isDominant_of_pullsDenseOpens
  · exact fun h => @PartialMap.pullsDenseOpens_of_isDominant X Y _ _ f h

end PartialMap

namespace RationalMap

/-- An arbitrary rational map with dense-open pullback is dominant when its
source is nonempty and its target is preirreducible. -/
theorem isDominant_of_pullsDenseOpens [Nonempty X] [PreirreducibleSpace Y]
    (r : X ⤏ Y) (hr : r.PullsDenseOpens) : r.IsDominant := by
  obtain ⟨f, rfl⟩ := r.exists_rep
  exact f.isDominant_toRationalMap_iff.mpr
    (f.isDominant_of_pullsDenseOpens (f.pullsDenseOpens_toRationalMap_iff.mp hr))

/-- For nonempty preirreducible source and target, dense-open pullback of a
rational map is equivalent to its dominance. -/
theorem pullsDenseOpens_iff_isDominant [PreirreducibleSpace X] [Nonempty X]
    [PreirreducibleSpace Y] [Nonempty Y] (r : X ⤏ Y) :
    r.PullsDenseOpens ↔ r.IsDominant := by
  obtain ⟨f, rfl⟩ := r.exists_rep
  rw [f.pullsDenseOpens_toRationalMap_iff, f.isDominant_toRationalMap_iff]
  exact f.pullsDenseOpens_iff_isDominant

end RationalMap

end AlgebraicGeometry.Scheme
