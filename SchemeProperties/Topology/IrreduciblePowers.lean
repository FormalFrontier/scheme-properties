/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.Topology.IrreducibleImage
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Order.OrderIsoNat
public import Mathlib.Order.RelSeries
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Sets.Closeds

/-!
# Stabilization of closures of preirreducible powers

The closures of the powers of a preirreducible set containing the identity eventually
stabilize when strict ascent of irreducible closed subsets is well-founded. Left
translations are continuous, and right translation by an element of the set need only
be continuous on each power of that set.

The proof forms the increasing sequence of irreducible closed subsets and applies
Mathlib's monotone chain condition. In particular, the result holds in a separately
continuous monoid whose order of irreducible closed subsets is finite-dimensional.
No joint continuity or separation axiom is needed.
-/

@[expose] public section

universe u

open Topology
open scoped Pointwise

/-- The closures of powers of a pointed preirreducible set eventually stabilize when
strict ascent of irreducible closed subsets is well-founded, left translations are
continuous, and right translations by elements of the set are continuous on its powers. -/
theorem IsPreirreducible.exists_closure_pow_eq_of_continuousOn
    {M : Type u} [Monoid M] [TopologicalSpace M] [ContinuousConstSMul M M]
    {S : Set M} (h1 : (1 : M) ∈ S) (hS : IsPreirreducible S)
    (hRight : ∀ (n : ℕ) (s : M), s ∈ S →
      ContinuousOn (fun x : M => x * s) (S ^ n))
    [WellFoundedGT (TopologicalSpace.IrreducibleCloseds M)] :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → _root_.closure (S ^ m) = _root_.closure (S ^ N) := by
  have hpow (n : ℕ) : IsPreirreducible (S ^ n) := by
    induction n with
    | zero =>
      simpa only [pow_zero, ← Set.singleton_one] using
        (isPreirreducible_singleton (x := (1 : M)))
    | succ n ih =>
      simpa only [pow_succ, ← Set.image2_mul] using
        ih.image2 hS (· * ·)
          (fun x _ => (ContinuousConstSMul.continuous_const_smul x).continuousOn)
          (fun s hs => hRight n s hs)
  let C : ℕ →o TopologicalSpace.IrreducibleCloseds M :=
    { toFun := fun n =>
        ⟨_root_.closure (S ^ n),
          IsIrreducible.closure ⟨⟨1, Set.one_mem_pow h1⟩, hpow n⟩,
          isClosed_closure⟩
      monotone' := fun _ _ h => closure_mono (Set.pow_subset_pow_right h1 h) }
  obtain ⟨N, hN⟩ := WellFoundedGT.monotone_chain_condition C
  exact ⟨N, fun m hm => congrArg
    (fun s : TopologicalSpace.IrreducibleCloseds M => (s : Set M)) (hN m hm).symm⟩

/-- The closures of the powers of a preirreducible set containing the identity
stabilize in a separately continuous monoid whose irreducible closed subsets form
a finite-dimensional order. -/
theorem IsPreirreducible.exists_closure_pow_eq
    {M : Type u} [Monoid M] [TopologicalSpace M] [SeparatelyContinuousMul M]
    [FiniteDimensionalOrder (TopologicalSpace.IrreducibleCloseds M)]
    {A : Set M} (hA : IsPreirreducible A) (h1 : (1 : M) ∈ A) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → _root_.closure (A ^ n) = _root_.closure (A ^ N) := by
  have : ContinuousConstSMul M M := ⟨fun s => continuous_const_mul s⟩
  have : WellFoundedGT (TopologicalSpace.IrreducibleCloseds M) :=
    ⟨SetRel.IsWellFounded.inv_of_finiteDimensional
      {(s, t) : TopologicalSpace.IrreducibleCloseds M ×
        TopologicalSpace.IrreducibleCloseds M | s < t}⟩
  exact IsPreirreducible.exists_closure_pow_eq_of_continuousOn h1 hA
    (fun _ s _ => (continuous_mul_const s).continuousOn)
