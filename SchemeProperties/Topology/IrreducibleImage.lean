/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Irreducible

/-!
# Preirreducible images of separately continuous maps

The binary image of two preirreducible sets is preirreducible when each section is
continuous on the corresponding set. Empty input sets are allowed, and no joint
continuity is required.

The proof uses `IsPreirreducible.image` for a pair of sections to synchronize one
coordinate, and then for a single section to synchronize the other coordinate.
-/

@[expose] public section

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {s : Set X} {t : Set Y}

/-- A binary image of preirreducible sets is preirreducible if each section is continuous
on the corresponding set. -/
theorem IsPreirreducible.image2 (hs : IsPreirreducible s) (ht : IsPreirreducible t)
    (f : X → Y → Z) (hfx : ∀ x ∈ s, ContinuousOn (f x) t)
    (hfy : ∀ y ∈ t, ContinuousOn (fun x => f x y) s) :
    IsPreirreducible (Set.image2 f s t) := by
  intro U V hU hV hUmeet hVmeet
  rcases hUmeet with ⟨z, hz, hzU⟩
  rcases Set.mem_image2.mp hz with ⟨a, ha, b, hb, rfl⟩
  rcases hVmeet with ⟨z, hz, hzV⟩
  rcases Set.mem_image2.mp hz with ⟨c, hc, d, hd, rfl⟩
  have hrows : IsPreirreducible ((fun y => (f a y, f c y)) '' t) :=
    ht.image (fun y => (f a y, f c y)) ((hfx a ha).prodMk (hfx c hc))
  obtain ⟨p, hp, hpU, hpV⟩ :=
    hrows (Prod.fst ⁻¹' U) (Prod.snd ⁻¹' V)
      (hU.preimage continuous_fst) (hV.preimage continuous_snd)
      ⟨(f a b, f c b), Set.mem_image_of_mem _ hb, hzU⟩
      ⟨(f a d, f c d), Set.mem_image_of_mem _ hd, hzV⟩
  rcases hp with ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hxyU, hxyV⟩ :=
    (hs.image (fun x => f x y) (hfy y hy)) U V hU hV
      ⟨f a y, Set.mem_image_of_mem _ ha, hpU⟩
      ⟨f c y, Set.mem_image_of_mem _ hc, hpV⟩
  rcases hz with ⟨x, hx, rfl⟩
  exact ⟨f x y, Set.mem_image2_of_mem hx hy, hxyU, hxyV⟩
