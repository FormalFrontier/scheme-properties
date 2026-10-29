/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.LocallyConstructiblePreimage

/-!
# Interior of a dense preimage of a locally constructible set

A dense continuous preimage of a locally constructible set in a nonempty space
has nonempty interior. This uses the locally closed point of the preimage itself,
not preservation of constructibility by continuous maps.
-/

@[expose] public section

open Set Filter Topology

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

example [Nonempty X] {t : Set Y} (ht : IsLocallyConstructible t) {f : X → Y}
    (hf : Continuous f) (hd : Dense (f ⁻¹' t)) : (interior (f ⁻¹' t)).Nonempty := by
  obtain ⟨x, _, hxLC⟩ :=
    IsLocallyConstructible.exists_isLocallyClosedAt_preimage ht hf (Dense.nonempty hd)
  obtain ⟨U, hU, hsub⟩ := isLocallyClosedAt_iff_exists_inter_closure_subset.mp hxLC
  have hUt : U ⊆ f ⁻¹' t := by
    simpa only [Dense.closure_eq hd, inter_univ] using hsub
  exact ⟨x, mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset hU hUt)⟩
