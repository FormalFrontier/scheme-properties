/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.Topology.IrreduciblePowers

/-!
# Closure of all finite products

The stabilization theorem identifies the closure of all finite products from a
preirreducible set containing the identity with one finite closed stage.
-/

open Topology
open scoped Pointwise

universe u

example {M : Type u} [Monoid M] [TopologicalSpace M] [SeparatelyContinuousMul M]
    [FiniteDimensionalOrder (TopologicalSpace.IrreducibleCloseds M)]
    {A : Set M} (hA : IsPreirreducible A) (h1 : (1 : M) ∈ A) :
    ∃ N : ℕ, closure (⋃ n : ℕ, A ^ n) = closure (A ^ N) := by
  obtain ⟨N, hN⟩ := hA.exists_closure_pow_eq h1
  refine ⟨N, Set.Subset.antisymm ?_ ?_⟩
  · refine closure_minimal (Set.iUnion_subset fun n => ?_) isClosed_closure
    calc
      A ^ n ⊆ closure (A ^ max N n) :=
        (Set.pow_subset_pow_right h1 (Nat.le_max_right N n)).trans subset_closure
      _ = closure (A ^ N) := hN _ (Nat.le_max_left N n)
  · exact closure_mono (Set.subset_iUnion (fun n : ℕ => A ^ n) N)
