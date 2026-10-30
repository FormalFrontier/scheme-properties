/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson

/-!
# Finite families covering a Jacobson prime spectrum

A finite family of ring homomorphisms covers a Jacobson prime spectrum if its induced
maps on prime spectra cover all closed points. The rings may be trivial, and the
indexing type may be empty.

The argument uses `PrimeSpectrum.mem_range_comap_iff` to separate a missing prime from
each image. A product of the separating elements defines a nonempty locally closed
subset, and `nonempty_inter_closedPoints` supplies a closed point in that subset.
-/

@[expose] public section

universe u v w

open scoped BigOperators

namespace PrimeSpectrum

/-- A finite family of maps on prime spectra covers a Jacobson prime spectrum as soon
as it covers its closed points. No condition is imposed on the source spectra. -/
theorem iUnion_range_comap_eq_univ_of_closedPoints_subset
    {R : Type u} [CommRing R] {ι : Type w} [Finite ι]
    {A : ι → Type v} [∀ i, CommRing (A i)]
    (f : ∀ i, R →+* A i) [JacobsonSpace (PrimeSpectrum R)]
    (h : closedPoints (PrimeSpectrum R) ⊆ ⋃ i, Set.range (comap (f i))) :
    (⋃ i, Set.range (comap (f i))) = Set.univ := by
  classical
  let := Fintype.ofFinite ι
  apply Set.eq_univ_iff_forall.mpr
  intro p
  by_contra hp
  have hex : ∀ i, ∃ s : R, s ∉ p.asIdeal ∧ f i s ∈ p.asIdeal.map (f i) := by
    intro i
    have hneq : (p.asIdeal.map (f i)).comap (f i) ≠ p.asIdeal := by
      intro heq
      exact hp (Set.mem_iUnion.mpr
        ⟨i, (mem_range_comap_iff (f := f i)).mpr heq⟩)
    by_contra! hno
    apply hneq
    refine le_antisymm ?_ Ideal.le_comap_map
    intro s hs
    by_contra hsp
    exact hno s hsp hs
  choose s hs using hex
  have hprod : (∏ i, s i) ∉ p.asIdeal := by
    intro hprod
    obtain ⟨i, _, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hprod
    exact (hs i).1 hi
  have hZ : (zeroLocus (p.asIdeal : Set R) ∩
      (basicOpen (∏ i, s i) : Set (PrimeSpectrum R))).Nonempty :=
    ⟨p, (mem_zeroLocus _ _).mpr Set.Subset.rfl, (mem_basicOpen _ _).mpr hprod⟩
  obtain ⟨m, hmZ, hmclosed⟩ := nonempty_inter_closedPoints hZ
    ((isClosed_zeroLocus _).isLocallyClosed.inter
      (basicOpen _).isOpen.isLocallyClosed)
  have hpm : p.asIdeal ≤ m.asIdeal := (mem_zeroLocus _ _).mp hmZ.1
  have hmprod : (∏ i, s i) ∉ m.asIdeal := (mem_basicOpen _ _).mp hmZ.2
  obtain ⟨j, q, hq⟩ := Set.mem_iUnion.mp (h hmclosed)
  have hpq : p.asIdeal.map (f j) ≤ q.asIdeal := by
    apply Ideal.map_le_of_le_comap
    simpa only [← hq, comap_asIdeal] using hpm
  have hsj : s j ∈ m.asIdeal := by
    rw [← hq, comap_asIdeal, Ideal.mem_comap]
    exact hpq (hs j).2
  exact hmprod (Ideal.IsPrime.prod_mem_iff.mpr ⟨j, Finset.mem_univ j, hsj⟩)

end PrimeSpectrum
