/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Constructible
public import Mathlib.Topology.LocallyClosed

/-!
# Locally closed points in continuous preimages

A nonempty continuous preimage of a locally constructible set has a point at which
that same preimage is locally closed. The spaces may have independent universes;
no separation, compactness or Noetherian hypothesis is required.

The proof uses Mathlib's Boolean normal form to express a constructible set as a
finite union of locally closed pieces. Finite unions of locally closed sets need
not be locally closed, but a nonempty such union has a locally closed point.
An open constructibility chart and continuous pullback of its individual pieces
then give the result. This does not assert that arbitrary continuous preimages
preserve constructibility: retrocompact open sets need not pull back to
retrocompact sets.
-/

@[expose] public section

open Set Filter Topology
open scoped Set.Notation

universe u v w

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- A nonempty finite union of locally closed sets has a point at which the union
is locally closed. -/
theorem Set.Finite.exists_isLocallyClosedAt_biUnion {ι : Type w} {I : Set ι}
    (hI : I.Finite) {s : ι → Set X} (hs : ∀ i ∈ I, IsLocallyClosed (s i))
    (hne : (⋃ i ∈ I, s i).Nonempty) :
    ∃ x ∈ ⋃ i ∈ I, s i, IsLocallyClosedAt (⋃ i ∈ I, s i) x := by
  classical
  revert hs hne
  induction I, hI using Set.Finite.induction_on with
  | empty => simp
  | @insert i I hi hI ih =>
    intro hs hne
    have hiLC := hs i (by simp)
    have hILC : ∀ j ∈ I, IsLocallyClosed (s j) := fun j hj ↦ hs j (by simp [hj])
    rw [biUnion_insert] at hne ⊢
    by_cases h : s i ⊆ closure (⋃ j ∈ I, s j)
    · -- The added piece does not enlarge the closure of the previous union.
      have hBne : (⋃ j ∈ I, s j).Nonempty := by
        obtain ⟨x, hx | hx⟩ := hne
        · exact Set.Nonempty.of_closure ⟨x, h hx⟩
        · exact ⟨x, hx⟩
      obtain ⟨x, hx, hxLC⟩ := ih hILC hBne
      refine ⟨x, Or.inr hx, ?_⟩
      obtain ⟨U, hU, hsub⟩ := isLocallyClosedAt_iff_exists_inter_closure_subset.mp hxLC
      apply isLocallyClosedAt_iff_exists_inter_closure_subset.mpr
      refine ⟨U, hU, ?_⟩
      have heq : closure (s i ∪ ⋃ j ∈ I, s j) = closure (⋃ j ∈ I, s j) := by
        rw [closure_union, union_eq_right.mpr (closure_minimal h isClosed_closure)]
      rw [heq]
      exact fun y hy ↦ Or.inr (hsub hy)
    · -- Outside the previous closure, the added locally closed piece is isolated.
      obtain ⟨x, hx, hout⟩ := Set.not_subset.mp h
      exact ⟨x, Or.inl hx,
        (hiLC.isLocallyClosedAt hx).union (.of_notMem_closure hout)⟩

/-- A constructible set is a finite union of locally closed sets. The pieces need
not themselves be constructible. -/
theorem IsConstructible.exists_finite_isLocallyClosed_sUnion {s : Set X}
    (hs : IsConstructible s) :
    ∃ S : Set (Set X), S.Finite ∧ (∀ t ∈ S, IsLocallyClosed t) ∧ s = ⋃₀ S := by
  classical
  let O : Set (Set X) := {U | IsOpen U}
  have hO : IsSublattice O :=
    ⟨fun _ hU _ hV ↦ hU.union hV, fun _ hU _ hV ↦ hU.inter hV⟩
  have hsO : s ∈ BooleanSubalgebra.closure O :=
    BooleanSubalgebra.closure_mono (fun _ hU ↦ hU.1) hs
  obtain ⟨I, hI⟩ :=
    (BooleanSubalgebra.mem_closure_iff_sup_sdiff hO isOpen_empty isOpen_univ).mp hsO
  let d : O × O → Set X := fun p ↦ p.1.1 \ p.2.1
  refine ⟨d '' (I : Set (O × O)), I.finite_toSet.image d, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact p.1.2.isLocallyClosed.inter p.2.2.isClosed_compl.isLocallyClosed
  · simpa [d, Finset.sup_eq_iSup, sUnion_image] using hI

/-- A nonempty continuous preimage of a locally constructible set has a member
at which that same preimage is locally closed. No preservation of constructibility
by the continuous map is assumed or asserted. -/
theorem IsLocallyConstructible.exists_isLocallyClosedAt_preimage {t : Set Y}
    (ht : IsLocallyConstructible t) {f : X → Y} (hf : Continuous f)
    (hne : (f ⁻¹' t).Nonempty) :
    ∃ x ∈ f ⁻¹' t, IsLocallyClosedAt (f ⁻¹' t) x := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨U, hUx, hU, hUt⟩ := ht (f x)
  obtain ⟨S, hS, hSLC, hSeq⟩ :=
    IsConstructible.exists_finite_isLocallyClosed_sUnion hUt
  let g : Set U → Set X := fun A ↦ f ⁻¹' (Subtype.val '' A)
  have heq : (⋃ A ∈ S, g A) = f ⁻¹' t ∩ f ⁻¹' U := by
    ext z
    simp only [mem_iUnion, exists_prop, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨A, hA, y, hy, hyz⟩
      have hyt : y ∈ U ↓∩ t := by
        rw [hSeq]
        exact ⟨A, hA, hy⟩
      exact ⟨by simpa only [mem_preimage, ← hyz] using hyt,
        by simpa only [← hyz] using y.property⟩
    · rintro ⟨hzt, hzU⟩
      have hy : (⟨f z, hzU⟩ : U) ∈ ⋃₀ S := by
        rw [← hSeq]
        exact hzt
      obtain ⟨A, hA, hyA⟩ := hy
      exact ⟨A, hA, ⟨f z, hzU⟩, hyA, rfl⟩
  have hgLC : ∀ A ∈ S, IsLocallyClosed (g A) := by
    intro A hA
    exact ((hSLC A hA).image hU.isOpenEmbedding_subtypeVal.isInducing
      hU.isOpenEmbedding_subtypeVal.isOpen_range.isLocallyClosed).preimage hf
  have hgNonempty : (⋃ A ∈ S, g A).Nonempty := by
    rw [heq]
    exact ⟨x, hx, show f x ∈ U from mem_of_mem_nhds hUx⟩
  obtain ⟨z, hz, hzLC⟩ :=
    Set.Finite.exists_isLocallyClosedAt_biUnion hS hgLC hgNonempty
  have hztU : z ∈ f ⁻¹' t ∩ f ⁻¹' U := heq ▸ hz
  refine ⟨z, hztU.1, hzLC.congr ?_⟩
  filter_upwards [(hU.preimage hf).mem_nhds hztU.2] with y hy
  simp [heq, hy]
