/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.JacobsonSpace
public import SchemeProperties.LocallyConstructiblePreimage

/-!
# Closed-point traces in Jacobson spaces

In a Jacobson space, a locally constructible subset has the same closure as its
closed-point trace. Such traces detect inclusion, equality, and closedness in the
original closed-point subspace. The locally closed closedness criterion is also
available, without identifying local closedness with local constructibility.
No separation, finiteness or nonemptiness assumption is imposed.

The common density statement applies to arbitrary unions of locally closed sets.
For `hS : IsLocallyClosed S`, its singleton-index specialization is exactly
Mathlib's `JacobsonSpace.closure_inter_closedPoints_eq_closure hS`:

```lean
by
  simpa using JacobsonSpace.closure_iUnion_inter_closedPoints_eq_closure
    (A := fun _ : Unit ↦ S) (fun _ ↦ hS)
```

This union statement concerns density only, not trace conservativity. For example,
the closed points of `Spec ℤ` are a union of closed singletons with the same trace
as the whole space, but are not closed. The generic singleton in `Spec ℤ` shows
that trace detection fails for unrestricted subsets. The Jacobson hypothesis is
also essential: the open generic singleton of the Sierpinski space is not closed,
but has empty closed-point trace.

## Implementation notes

Local constructibility uses Mathlib's Boolean algebra of open retrocompact sets
on open-neighborhood subtypes. Its locally closed cover is obtained from
`Topology.IsConstructible.exists_finite_isLocallyClosed_sUnion` on each chart and
`IsLocallyClosed.image` for the open inclusion. Mixed density allows intersection
with an arbitrary locally closed set; a closed ambient set need not itself be
locally constructible.

## References

The density proofs generalize Mathlib's
`JacobsonSpace.closure_inter_closedPoints_eq_closure` by closure monotonicity.
The closedness criteria use Mathlib's `isClosed_preimage_val` for the original
subspace topology. The locally closed proof also uses
`IsLocallyClosed.isOpen_coborder` and `nonempty_inter_closedPoints`.
-/

@[expose] public section

universe u v

/-- A locally closed subset of a Jacobson space is closed exactly when its trace
in the subspace of closed points is closed. -/
theorem IsLocallyClosed.isClosed_iff_isClosed_preimage_closedPoints
    {X : Type u} [TopologicalSpace X] [JacobsonSpace X] {S : Set X}
    (hS : IsLocallyClosed S) :
    IsClosed S ↔ IsClosed ((Subtype.val : closedPoints X → X) ⁻¹' S) := by
  constructor
  · exact fun h ↦ h.preimage continuous_subtype_val
  · intro htrace
    have hcp : closedPoints X ∩ closure S ⊆ S := by
      simpa only [Set.inter_comm (closedPoints X) S,
        JacobsonSpace.closure_inter_closedPoints_eq_closure hS] using
        (isClosed_preimage_val (s := closedPoints X) (t := S)).mp htrace
    -- Local closedness makes the omitted boundary closed in the ambient space.
    have hboundary : IsClosed (closure S \ S) := by
      simpa only [coborder, compl_compl] using hS.isOpen_coborder.isClosed_compl
    apply isClosed_of_closure_subset
    intro x hx
    by_contra hxS
    obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints
      (Z := closure S \ S) ⟨x, hx, hxS⟩ hboundary.isLocallyClosed
    exact hy.2 (hcp ⟨hyc, hy.1⟩)

open Set Filter Topology

variable {X : Type u} [TopologicalSpace X] {S T C Z : Set X}

/-- An arbitrary union of locally closed sets in a Jacobson space has the same
closure as its closed-point trace. This does not assert trace conservativity for
arbitrary unions. -/
theorem JacobsonSpace.closure_iUnion_inter_closedPoints_eq_closure
    [JacobsonSpace X] {ι : Sort v} {A : ι → Set X}
    (hA : ∀ i, IsLocallyClosed (A i)) :
    closure ((⋃ i, A i) ∩ closedPoints X) = closure (⋃ i, A i) := by
  refine (closure_mono inter_subset_left).antisymm (closure_minimal ?_ isClosed_closure)
  intro x hx
  obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
  have hi : closure (A i) ⊆ closure ((⋃ i, A i) ∩ closedPoints X) := by
    rw [← JacobsonSpace.closure_inter_closedPoints_eq_closure (hA i)]
    apply closure_mono
    rintro y ⟨hy, hyc⟩
    exact ⟨mem_iUnion.mpr ⟨i, hy⟩, hyc⟩
  exact hi (subset_closure hxi)

namespace Topology

/-- Local constructibility is invariant under taking complements. -/
@[simp] theorem isLocallyConstructible_compl :
    IsLocallyConstructible Sᶜ ↔ IsLocallyConstructible S := by
  have hcompl : ∀ {T : Set X}, IsLocallyConstructible T → IsLocallyConstructible Tᶜ := by
    intro T hT x
    obtain ⟨U, hxU, hU, hTU⟩ := hT x
    refine ⟨U, hxU, hU, ?_⟩
    simpa only [preimage_compl] using IsConstructible.compl hTU
  exact ⟨fun hS ↦ by simpa only [compl_compl] using hcompl hS, hcompl⟩

alias ⟨IsLocallyConstructible.of_compl, IsLocallyConstructible.compl⟩ :=
  isLocallyConstructible_compl

/-- A locally constructible set is a union of locally closed subsets of the
ambient space, obtained from finite decompositions on open charts. -/
theorem IsLocallyConstructible.exists_isLocallyClosed_sUnion
    (hS : IsLocallyConstructible S) :
    ∃ A : Set (Set X), (∀ U ∈ A, IsLocallyClosed U) ∧ S = ⋃₀ A := by
  refine ⟨{U | IsLocallyClosed U ∧ U ⊆ S}, fun U hU ↦ hU.1, ?_⟩
  apply Subset.antisymm
  · intro x hxS
    obtain ⟨U, hxU, hU, hSU⟩ := hS x
    obtain ⟨A, _, hA, hUA⟩ := IsConstructible.exists_finite_isLocallyClosed_sUnion hSU
    have hxA : (⟨x, mem_of_mem_nhds hxU⟩ : U) ∈ ⋃₀ A := by
      rw [← hUA]
      exact hxS
    obtain ⟨t, ht, hxt⟩ := mem_sUnion.mp hxA
    refine mem_sUnion.mpr ⟨Subtype.val '' t, ⟨?_, ?_⟩, ?_⟩
    · apply IsLocallyClosed.image (hA t ht) IsEmbedding.subtypeVal.isInducing
      simpa only [Subtype.range_coe] using hU.isLocallyClosed
    · rintro y ⟨z, hz, rfl⟩
      have hzS : z ∈ (Subtype.val : U → X) ⁻¹' S := by
        rw [hUA]
        exact mem_sUnion.mpr ⟨t, ht, hz⟩
      exact hzS
    · exact ⟨⟨x, mem_of_mem_nhds hxU⟩, hxt, rfl⟩
  · intro x hx
    obtain ⟨U, hU, hxU⟩ := mem_sUnion.mp hx
    exact hU.2 hxU

/-- A locally constructible subset of a Jacobson space has the same closure as
its closed-point trace. -/
theorem IsLocallyConstructible.closure_inter_closedPoints_eq_closure
    [JacobsonSpace X] (hS : IsLocallyConstructible S) :
    closure (S ∩ closedPoints X) = closure S := by
  obtain ⟨A, hA, hSA⟩ := IsLocallyConstructible.exists_isLocallyClosed_sUnion hS
  rw [hSA, sUnion_eq_iUnion]
  exact JacobsonSpace.closure_iUnion_inter_closedPoints_eq_closure fun U ↦ hA U U.property

/-- Every nonempty locally constructible subset of a Jacobson space contains a
closed point. -/
theorem IsLocallyConstructible.nonempty_inter_closedPoints
    [JacobsonSpace X] (hS : IsLocallyConstructible S)
    (hne : S.Nonempty) : (S ∩ closedPoints X).Nonempty := by
  apply Set.Nonempty.of_closure
  rw [IsLocallyConstructible.closure_inter_closedPoints_eq_closure hS]
  exact hne.closure

/-- Intersecting a locally constructible set with an arbitrary locally closed
set still gives a subset whose closed-point trace is dense in it. The second set
is not assumed locally constructible. -/
theorem IsLocallyConstructible.closure_inter_inter_closedPoints_eq_closure
    [JacobsonSpace X] (hS : IsLocallyConstructible S)
    (hZ : IsLocallyClosed Z) :
    closure ((S ∩ Z) ∩ closedPoints X) = closure (S ∩ Z) := by
  obtain ⟨A, hA, hSA⟩ := IsLocallyConstructible.exists_isLocallyClosed_sUnion hS
  rw [hSA, sUnion_eq_iUnion]
  simpa only [iUnion_inter] using
    JacobsonSpace.closure_iUnion_inter_closedPoints_eq_closure
      (A := fun U : A ↦ (U : Set X) ∩ Z) (fun U ↦ (hA U U.property).inter hZ)

/-- Inclusion between locally constructible subsets of a Jacobson space is
detected on their closed-point traces. -/
theorem IsLocallyConstructible.subset_iff_inter_closedPoints_subset
    [JacobsonSpace X] (hS : IsLocallyConstructible S)
    (hT : IsLocallyConstructible T) :
    S ⊆ T ↔ S ∩ closedPoints X ⊆ T ∩ closedPoints X := by
  constructor
  · exact fun h x hx ↦ ⟨h hx.1, hx.2⟩
  · intro htrace x hxS
    by_contra hxT
    obtain ⟨y, ⟨hyS, hyT⟩, hyc⟩ :=
      IsLocallyConstructible.nonempty_inter_closedPoints
        (IsLocallyConstructible.inter hS (IsLocallyConstructible.compl hT)) ⟨x, hxS, hxT⟩
    exact hyT (htrace ⟨hyS, hyc⟩).1

/-- Equality between locally constructible subsets of a Jacobson space is
detected on their closed-point traces. -/
theorem IsLocallyConstructible.eq_iff_inter_closedPoints_eq
    [JacobsonSpace X] (hS : IsLocallyConstructible S)
    (hT : IsLocallyConstructible T) :
    S = T ↔ S ∩ closedPoints X = T ∩ closedPoints X := by
  constructor
  · rintro rfl
    rfl
  · intro h
    exact Subset.antisymm
      ((IsLocallyConstructible.subset_iff_inter_closedPoints_subset hS hT).mpr h.le)
      ((IsLocallyConstructible.subset_iff_inter_closedPoints_subset hT hS).mpr h.ge)

/-- Inclusion of locally constructible subsets is detected by preimages in the
original closed-point subspace. -/
theorem IsLocallyConstructible.subset_iff_preimage_closedPoints_subset
    [JacobsonSpace X] (hS : IsLocallyConstructible S)
    (hT : IsLocallyConstructible T) :
    S ⊆ T ↔
      (Subtype.val : closedPoints X → X) ⁻¹' S ⊆
        (Subtype.val : closedPoints X → X) ⁻¹' T := by
  rw [IsLocallyConstructible.subset_iff_inter_closedPoints_subset hS hT]
  constructor
  · intro h x hx
    exact (h ⟨hx, x.property⟩).1
  · intro h x hx
    have hx' : (⟨x, hx.2⟩ : closedPoints X) ∈
        (Subtype.val : closedPoints X → X) ⁻¹' S := hx.1
    exact ⟨h hx', hx.2⟩

/-- Equality of locally constructible subsets is detected by preimages in the
original closed-point subspace. -/
theorem IsLocallyConstructible.eq_iff_preimage_closedPoints_eq
    [JacobsonSpace X] (hS : IsLocallyConstructible S)
    (hT : IsLocallyConstructible T) :
    S = T ↔
      (Subtype.val : closedPoints X → X) ⁻¹' S =
        (Subtype.val : closedPoints X → X) ⁻¹' T := by
  constructor
  · rintro rfl
    rfl
  · intro h
    exact Subset.antisymm
      ((IsLocallyConstructible.subset_iff_preimage_closedPoints_subset hS hT).mpr h.le)
      ((IsLocallyConstructible.subset_iff_preimage_closedPoints_subset hT hS).mpr h.ge)

/-- A locally constructible subset of a Jacobson space equals an arbitrary
closed set exactly when their closed-point traces agree. The closed set is not
assumed locally constructible. -/
theorem IsLocallyConstructible.eq_iff_inter_closedPoints_eq_of_isClosed
    [JacobsonSpace X] (hS : IsLocallyConstructible S)
    (hC : IsClosed C) :
    S = C ↔ S ∩ closedPoints X = C ∩ closedPoints X := by
  constructor
  · rintro rfl
    rfl
  · intro htrace
    apply Subset.antisymm
    · apply subset_trans subset_closure
      rw [← IsLocallyConstructible.closure_inter_closedPoints_eq_closure hS]
      refine closure_minimal ?_ hC
      rw [htrace]
      exact inter_subset_left
    · have hempty : (Sᶜ ∩ C) ∩ closedPoints X = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro y ⟨⟨hyS, hyC⟩, hyc⟩
        have hy : y ∈ S ∩ closedPoints X := htrace.symm ▸ ⟨hyC, hyc⟩
        exact hyS hy.1
      have hdensity := IsLocallyConstructible.closure_inter_inter_closedPoints_eq_closure
        (IsLocallyConstructible.compl hS) hC.isLocallyClosed
      rw [hempty, closure_empty] at hdensity
      intro x hxC
      by_contra hxS
      have hx : x ∈ closure (Sᶜ ∩ C) := subset_closure ⟨hxS, hxC⟩
      rw [← hdensity] at hx
      exact hx

/-- A locally constructible subset of a Jacobson space is closed exactly when
its trace in the original closed-point subspace is closed. -/
theorem IsLocallyConstructible.isClosed_iff_isClosed_preimage_closedPoints
    [JacobsonSpace X] (hS : IsLocallyConstructible S) :
    IsClosed S ↔ IsClosed ((Subtype.val : closedPoints X → X) ⁻¹' S) := by
  constructor
  · exact fun h ↦ h.preimage continuous_subtype_val
  · intro htrace
    have hcp : closedPoints X ∩ closure S ⊆ S := by
      simpa only [inter_comm (closedPoints X) S,
        IsLocallyConstructible.closure_inter_closedPoints_eq_closure hS] using
        (isClosed_preimage_val (s := closedPoints X) (t := S)).mp htrace
    have heq : S ∩ closedPoints X = closure S ∩ closedPoints X := by
      apply Subset.antisymm
      · exact fun x hx ↦ ⟨subset_closure hx.1, hx.2⟩
      · exact fun x hx ↦ ⟨hcp ⟨hx.2, hx.1⟩, hx.2⟩
    rw [(IsLocallyConstructible.eq_iff_inter_closedPoints_eq_of_isClosed
      hS isClosed_closure).mpr heq]
    exact isClosed_closure

end Topology
