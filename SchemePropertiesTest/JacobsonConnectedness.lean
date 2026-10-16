/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.JacobsonConnectedness
import Mathlib.Algebra.Field.Rat
import Mathlib.RingTheory.Spectrum.Prime.Jacobson

/-!
# Examples of connectedness through closed points

The affine line over the rationals is a connected Jacobson space with a nonclosed
point. Its closed-point subspace is connected by the comparison theorem, without
being the entire spectrum. The empty space is not connected on either side.
-/

open TopologicalSpace Polynomial

namespace SchemePropertiesTest.JacobsonConnectedness

private theorem connectedSpace_closedPoints_affineLine :
    ConnectedSpace ↥(closedPoints (PrimeSpectrum ℚ[X])) ∧
    ∃ x : PrimeSpectrum ℚ[X], x ∉ closedPoints (PrimeSpectrum ℚ[X]) := by
  refine ⟨JacobsonSpace.connectedSpace_closedPoints_iff.mpr inferInstance,
    ⟨⟨⊥, inferInstance⟩, ?_⟩⟩
  rw [mem_closedPoints_iff, PrimeSpectrum.isClosed_singleton_iff_isMaximal]
  exact fun h ↦ Polynomial.not_isField ℚ (Ring.isField_iff_maximal_bot.mpr h)

private theorem not_connectedSpace_closedPoints_empty :
    ¬ ConnectedSpace ↥(closedPoints Empty) ∧ ¬ ConnectedSpace Empty := by
  exact ⟨fun h ↦ h.toNonempty.elim (fun x ↦ Empty.elim x.val),
    fun h ↦ h.toNonempty.elim Empty.elim⟩

end SchemePropertiesTest.JacobsonConnectedness
