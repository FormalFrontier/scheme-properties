/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Order.Hom.CompleteLattice

/-!
# Order isomorphisms of opens sites

An order isomorphism of lattices of open sets preserves and reflects covering sieves for the
associated Grothendieck topologies. Thus it exhibits either opens site as a dense subsite of
the other.

The sieve calculation holds for arbitrary-supremum-preserving maps between complete lattices.
The topological bridge identifies covering sieves with families of domains whose supremum is
the open set being covered.

For `e : TopologicalSpace.Opens X ≃o TopologicalSpace.Opens Y`, the local instance
`letI := e.symm.isDenseSubsite_opens` enables Mathlib's `e.equivalence.sheafCongr` for any
value category. Its forward functor precomposes with `e.symm.monotone.functor.op`, and its
unit is the image of `e.equivalence.op.unitIso`. No sheafification or limits on the value
category are required.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory TopologicalSpace

namespace CategoryTheory.Sieve

variable {α : Type u} {β : Type v} [CompleteLattice α] [CompleteLattice β]
  {F : Type w} [FunLike F α β] [sSupHomClass F α β]

/-- The supremum of the domains of the pushforward of a sieve is the image of the supremum
of its domains under an arbitrary-supremum-preserving map. -/
theorem iSup_functorPushforward (f : F) {U : α} (S : Sieve U) :
    (⨆ (V : β) (g : V ⟶ f U)
      (_ : S.functorPushforward (OrderHomClass.monotone f).functor g), V) =
      f (⨆ (V : α) (g : V ⟶ U) (_ : S g), V) := by
  simp_rw [map_iSup]
  apply le_antisymm
  · refine iSup_le fun V ↦ iSup_le fun g ↦ iSup_le fun hg ↦ ?_
    rcases hg with ⟨W, h, k, hh, _⟩
    exact k.le.trans <|
      le_iSup_of_le W <| le_iSup_of_le h <| le_iSup_of_le hh le_rfl
  · refine iSup_le fun V ↦ iSup_le fun g ↦ iSup_le fun hg ↦ ?_
    refine le_iSup_of_le (f V) <|
      le_iSup_of_le ((OrderHomClass.monotone f).functor.map g) ?_
    exact le_iSup_of_le ⟨V, g, 𝟙 _, hg, by simp⟩ le_rfl

end CategoryTheory.Sieve

namespace Opens

variable {X : Type u} [TopologicalSpace X]

/-- A sieve on an open set is covering if and only if the supremum of its domains is that
open set. -/
theorem mem_grothendieckTopology_iff_iSup_eq {U : TopologicalSpace.Opens X} {S : Sieve U} :
    S ∈ grothendieckTopology X U ↔
      (⨆ (V : TopologicalSpace.Opens X) (f : V ⟶ U) (_ : S f), V) = U := by
  constructor
  · intro hS
    apply le_antisymm
    · exact iSup_le fun V ↦ iSup_le fun f ↦ iSup_le fun _ ↦ f.le
    · intro x hx
      obtain ⟨V, f, hf, hxV⟩ := hS x hx
      have hV : V ≤ ⨆ (W : TopologicalSpace.Opens X) (g : W ⟶ U) (_ : S g), W :=
        le_iSup_of_le V <| le_iSup_of_le f <| le_iSup_of_le hf le_rfl
      exact hV hxV
  · intro hS x hx
    have hx' : x ∈ ⨆ (V : TopologicalSpace.Opens X) (f : V ⟶ U) (_ : S f), V := by
      rw [hS]
      exact hx
    simp only [TopologicalSpace.Opens.mem_iSup] at hx'
    obtain ⟨V, f, hf, hxV⟩ := hx'
    exact ⟨V, f, hf, hxV⟩

end Opens

namespace OrderIso

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- An order isomorphism between lattices of open sets preserves and reflects the covering
sieves of their associated Grothendieck topologies. -/
theorem isDenseSubsite_opens (e : TopologicalSpace.Opens X ≃o TopologicalSpace.Opens Y) :
    e.equivalence.functor.IsDenseSubsite (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) where
  functorPushforward_mem_iff {U S} := by
    change (S.functorPushforward e.monotone.functor ∈ Opens.grothendieckTopology Y (e U)) ↔
      S ∈ Opens.grothendieckTopology X U
    rw [Opens.mem_grothendieckTopology_iff_iSup_eq,
      CategoryTheory.Sieve.iSup_functorPushforward e,
      Opens.mem_grothendieckTopology_iff_iSup_eq]
    exact e.injective.eq_iff

end OrderIso
