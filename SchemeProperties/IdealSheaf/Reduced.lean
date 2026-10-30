/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# Kernels of morphisms from reduced schemes

For a morphism `f : X ⟶ Y` with `X` reduced, `f.ker` is the vanishing ideal sheaf of the
closure of the image of `f`. On every affine open `U` of `Y`, its ideal is the kernel of
`f.app U`, without any quasi-compactness assumption on `f`.

The affine calculation uses the fact that a section on a reduced scheme is zero if its
basic open is empty.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

private theorem app_ker_eq_vanishingIdeal_ideal_of_isReduced
    (f : X ⟶ Y) [IsReduced X] (U : Y.affineOpens) :
    RingHom.ker (f.app U).hom =
      (IdealSheafData.vanishingIdeal (X := Y)
        ⟨closure (Set.range f), isClosed_closure⟩).ideal U := by
  classical
  ext s
  change (f.app U).hom s = 0 ↔
    s ∈ PrimeSpectrum.vanishingIdeal
      (U.2.fromSpec ⁻¹' closure (Set.range f))
  rw [PrimeSpectrum.mem_vanishingIdeal]
  have hb (p : PrimeSpectrum Γ(Y, U)) :
      U.2.fromSpec p ∈ Y.basicOpen s ↔ s ∉ p.asIdeal := by
    have h :
        (U.2.fromSpec ⁻¹' (Y.basicOpen s : Set Y) : Set (PrimeSpectrum Γ(Y, U))) =
          (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum Γ(Y, U))) :=
      congrArg Opens.carrier (U.2.fromSpec_preimage_basicOpen s)
    exact (Set.ext_iff.mp h p).trans (PrimeSpectrum.mem_basicOpen s p)
  constructor
  · intro hs p hp
    by_contra hsp
    have hrange : Set.range f ⊆ ((Y.basicOpen s : Y.Opens) : Set Y)ᶜ := by
      rintro y ⟨x, rfl⟩ hx
      have hxPull : x ∈ X.basicOpen ((f.app U).hom s) := by
        rw [← Scheme.preimage_basicOpen f s]
        exact hx
      rw [hs, Scheme.basicOpen_zero] at hxPull
      exact hxPull
    have hclosure : closure (Set.range f) ⊆
        ((Y.basicOpen s : Y.Opens) : Set Y)ᶜ :=
      closure_minimal hrange (Y.basicOpen s).isOpen.isClosed_compl
    exact hclosure hp ((hb p).mpr hsp)
  · intro hs
    apply _root_.AlgebraicGeometry.eq_zero_of_basicOpen_eq_bot ((f.app U).hom s)
    apply le_antisymm ?_ bot_le
    intro x hx
    rw [← Scheme.preimage_basicOpen f s] at hx
    have hfx : f x ∈ Set.range U.2.fromSpec := by
      rw [U.2.range_fromSpec]
      exact Y.basicOpen_le s hx
    obtain ⟨p, hp⟩ := hfx
    have hpC : U.2.fromSpec p ∈ closure (Set.range f) := by
      rw [hp]
      exact subset_closure ⟨x, rfl⟩
    have hpB : U.2.fromSpec p ∈ Y.basicOpen s := by
      rw [hp]
      exact hx
    exact ((hb p).mp hpB) (hs p hpC)

/-- The kernel ideal sheaf of a morphism from a reduced scheme is the vanishing ideal
sheaf of the closure of its image. -/
theorem Hom.ker_eq_vanishingIdeal_of_isReduced
    (f : X ⟶ Y) [IsReduced X] :
    f.ker = IdealSheafData.vanishingIdeal (X := Y)
      ⟨closure (Set.range f), isClosed_closure⟩ := by
  let I : IdealSheafData Y := IdealSheafData.vanishingIdeal (X := Y)
    ⟨closure (Set.range f), isClosed_closure⟩
  have hfamily :
      (fun U : Y.affineOpens ↦ RingHom.ker (f.app U).hom) = I.ideal := by
    funext U
    exact app_ker_eq_vanishingIdeal_ideal_of_isReduced f U
  change IdealSheafData.ofIdeals
    (fun U : Y.affineOpens ↦ RingHom.ker (f.app U).hom) = I
  rw [hfamily, IdealSheafData.ofIdeals_ideal]

/-- On an affine open, the kernel ideal sheaf of a morphism from a reduced scheme is the
kernel of the induced homomorphism on sections. -/
theorem Hom.ker_apply_of_isReduced
    (f : X ⟶ Y) [IsReduced X] (U : Y.affineOpens) :
    f.ker.ideal U = RingHom.ker (f.app U).hom := by
  rw [Hom.ker_eq_vanishingIdeal_of_isReduced f]
  exact (app_ker_eq_vanishingIdeal_ideal_of_isReduced f U).symm

end AlgebraicGeometry.Scheme
