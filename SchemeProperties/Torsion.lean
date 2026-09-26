/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Localization.BaseChange

public section

set_option warningAsError true

/-!
# Torsion modules and localization at non-zero-divisors

This file characterizes torsion modules over a commutative ring by vanishing
after localization at the non-zero-divisors. The localization and the module
may live in universes independent of the base ring. For domains, this specializes
to the usual fraction ring.
-/

open TensorProduct

namespace Module

universe u v w

/-- A module over a commutative ring is torsion if and only if its base change
to any localization at the non-zero-divisors is zero. -/
theorem isTorsion_iff_subsingleton_tensorProduct
    {R : Type u} {K : Type v} {M : Type w} [CommRing R]
    [CommRing K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module R M] :
    IsTorsion R M ↔ Subsingleton (K ⊗[R] M) := by
  let _ : IsLocalizedModule (nonZeroDivisors R) (TensorProduct.mk R K M 1) :=
    IsLocalization.tensorProduct_isLocalizedModule (nonZeroDivisors R) K
  rw [IsLocalizedModule.subsingleton_iff (nonZeroDivisors R)
    (TensorProduct.mk R K M 1)]
  constructor
  · intro h m
    obtain ⟨r, hr⟩ := h (x := m)
    exact ⟨r, r.property, hr⟩
  · intro h m
    obtain ⟨r, hr, hm⟩ := h m
    exact ⟨⟨r, hr⟩, hm⟩

/-- A module over a commutative ring is torsion if and only if its base change
to the canonical localization at the non-zero-divisors is zero. For domains,
this is the usual fraction ring. -/
theorem isTorsion_iff_subsingleton_fractionRing_tensorProduct
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    IsTorsion R M ↔ Subsingleton (FractionRing R ⊗[R] M) :=
  isTorsion_iff_subsingleton_tensorProduct

end Module
