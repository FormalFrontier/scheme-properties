/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.Topology.IrreducibleImage
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Order.RelSeries
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Sets.Closeds

/-!
# Stabilization of closures of preirreducible powers

In a separately continuous topological monoid, the closures of the powers of a
preirreducible set containing the identity eventually stabilize if the order of
irreducible closed subsets is finite-dimensional.

The proof forms the increasing sequence of irreducible closed subsets and applies
Mathlib's monotone chain condition and the well-foundedness of strict ascent in a
finite-dimensional order. No joint continuity or separation axiom is needed.
-/

@[expose] public section

universe u

open Topology
open scoped Pointwise

/-- The closures of the powers of a preirreducible set containing the identity
stabilize in a separately continuous monoid whose irreducible closed subsets form
a finite-dimensional order. -/
theorem IsPreirreducible.exists_closure_pow_eq
    {M : Type u} [Monoid M] [TopologicalSpace M] [SeparatelyContinuousMul M]
    [FiniteDimensionalOrder (TopologicalSpace.IrreducibleCloseds M)]
    {A : Set M} (hA : IsPreirreducible A) (h1 : (1 : M) ∈ A) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → closure (A ^ n) = closure (A ^ N) := by
  have hpow (n : ℕ) : IsPreirreducible (A ^ n) := by
    induction n with
    | zero =>
      simpa only [pow_zero, ← Set.singleton_one] using
        (isPreirreducible_singleton (x := (1 : M)))
    | succ n ih =>
      simpa only [pow_succ, ← Set.image2_mul] using
        ih.image2 hA (· * ·)
          (fun x _ => (continuous_const_mul x).continuousOn)
          (fun y _ => (continuous_mul_const y).continuousOn)
  let C : ℕ →o TopologicalSpace.IrreducibleCloseds M :=
    { toFun := fun n =>
        ⟨closure (A ^ n),
          IsIrreducible.closure ⟨⟨1, Set.one_mem_pow h1⟩, hpow n⟩,
          isClosed_closure⟩
      monotone' := fun _ _ h => closure_mono (Set.pow_subset_pow_right h1 h) }
  let : WellFoundedGT (TopologicalSpace.IrreducibleCloseds M) :=
    ⟨SetRel.IsWellFounded.inv_of_finiteDimensional
      {(s, t) : TopologicalSpace.IrreducibleCloseds M ×
        TopologicalSpace.IrreducibleCloseds M | s < t}⟩
  obtain ⟨N, hN⟩ := WellFoundedGT.monotone_chain_condition C
  exact ⟨N, fun n hn => congrArg
    (fun s : TopologicalSpace.IrreducibleCloseds M => (s : Set M)) (hN n hn).symm⟩
