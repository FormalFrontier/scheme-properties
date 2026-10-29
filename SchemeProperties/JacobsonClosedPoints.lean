/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.JacobsonSpace

/-!
# Closedness through closed points of Jacobson spaces

A locally closed subset of a Jacobson space is closed if and only if its trace in
the subspace of closed points is closed. Local closedness is required for the full
subset in the ambient space, not merely for its trace. No separation, finiteness or
nonemptiness assumption is imposed.

Local closedness is essential: for a field `K`, the closed points of `Spec K[t]`
form a dense proper subset whose trace is the whole closed-point subspace. The
Jacobson hypothesis is also essential: the open generic singleton of the
Sierpinski space is not closed, but has empty closed-point trace.

## References

The proof uses Mathlib's `JacobsonSpace.closure_inter_closedPoints_eq_closure`
for density, `isClosed_preimage_val` for the subspace-closedness criterion,
`IsLocallyClosed.isOpen_coborder` for the closed boundary, and
`nonempty_inter_closedPoints` to show that this boundary is empty.
-/

@[expose] public section

universe u

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
