/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.Topology.Connected.Clopen

public section

set_option warningAsError true

/-!
# Integrality from domain stalks

This file proves that a connected locally Noetherian scheme whose local rings
are domains is integral. The main local step shows that a point with a domain
local ring lies on a unique irreducible component.

The locally Noetherian result applies the Noetherian component argument on
affine neighborhoods, rather than requiring the whole scheme to be Noetherian.

## References

* R. Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21,
  2025 draft), Exercise 5.3.C (the component argument and its locally
  Noetherian extension).
-/

open Set Topology TopologicalSpace CategoryTheory
open AlgebraicGeometry

namespace Ideal

/-- Two minimal primes contained in a prime are equal when the localization at
that prime is a domain. -/
theorem eq_of_mem_minimalPrimes_of_le_of_isDomain_atPrime
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {p q₁ q₂ : Ideal R} [p.IsPrime] [IsLocalization.AtPrime A p]
    (hq₁ : q₁ ∈ minimalPrimes R) (hq₂ : q₂ ∈ minimalPrimes R)
    (h₁ : q₁ ≤ p) (h₂ : q₂ ≤ p) [IsDomain A] :
    q₁ = q₂ := by
  let : q₁.IsPrime := hq₁.isPrime
  let : q₂.IsPrime := hq₂.isPrime
  let f : R →+* A := algebraMap R A
  have hmin : minimalPrimes A = Ideal.under R ⁻¹' minimalPrimes R := by
    simpa only [Ideal.map_bot] using
      (IsLocalization.minimalPrimes_map p.primeCompl A (⊥ : Ideal R))
  have hq₁' : q₁.map f ∈ minimalPrimes A := by
    rw [hmin]
    change Ideal.under R (q₁.map f) ∈ minimalPrimes R
    rwa [Ideal.under_map_of_isLocalizationAtPrime (q := p) (S := A) h₁]
  have hq₂' : q₂.map f ∈ minimalPrimes A := by
    rw [hmin]
    change Ideal.under R (q₂.map f) ∈ minimalPrimes R
    rwa [Ideal.under_map_of_isLocalizationAtPrime (q := p) (S := A) h₂]
  rw [IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff] at hq₁' hq₂'
  rw [← Ideal.under_map_of_isLocalizationAtPrime (q := p) (S := A) h₁,
    ← Ideal.under_map_of_isLocalizationAtPrime (q := p) (S := A) h₂, hq₁', hq₂']

end Ideal

namespace AlgebraicGeometry

/-- A point whose local ring is a domain lies on a unique irreducible
component. -/
theorem eq_irreducibleComponents_of_mem_of_isDomain_stalk
    (X : Scheme) (x : X) [IsDomain (X.presheaf.stalk x)]
    {Z W : Set X} (hZ : Z ∈ irreducibleComponents X)
    (hW : W ∈ irreducibleComponents X) (hxZ : x ∈ Z) (hxW : x ∈ W) :
    Z = W := by
  let P := fun (X : Scheme) (x : X) ↦
    IsDomain (X.presheaf.stalk x) →
      ∀ {Z W : Set X}, Z ∈ irreducibleComponents X → W ∈ irreducibleComponents X →
        x ∈ Z → x ∈ W → Z = W
  apply reduce_to_affine_nbhd P
  · intro R x hD Z W hZ hW hxZ hxW
    change PrimeSpectrum R at x
    change Set (PrimeSpectrum R) at Z W
    change Z ∈ irreducibleComponents (PrimeSpectrum R) at hZ
    change W ∈ irreducibleComponents (PrimeSpectrum R) at hW
    change x ∈ Z at hxZ
    change x ∈ W at hxW
    let : IsDomain ((Spec R).presheaf.stalk x) := hD
    let : x.asIdeal.IsPrime := x.isPrime
    let : Algebra R ((Spec R).presheaf.stalk x) := StructureSheaf.stalkAlgebra R x
    let : IsLocalization.AtPrime ((Spec R).presheaf.stalk x) x.asIdeal :=
      StructureSheaf.IsLocalization.to_stalk R x
    have hZmin : PrimeSpectrum.vanishingIdeal Z ∈ minimalPrimes R := by
      rw [PrimeSpectrum.vanishingIdeal_mem_minimalPrimes,
        (isClosed_of_mem_irreducibleComponents Z hZ).closure_eq]
      exact hZ
    have hWmin : PrimeSpectrum.vanishingIdeal W ∈ minimalPrimes R := by
      rw [PrimeSpectrum.vanishingIdeal_mem_minimalPrimes,
        (isClosed_of_mem_irreducibleComponents W hW).closure_eq]
      exact hW
    have hZle : PrimeSpectrum.vanishingIdeal Z ≤ x.asIdeal := by
      intro r hr
      exact (PrimeSpectrum.mem_vanishingIdeal Z r).mp hr x hxZ
    have hWle : PrimeSpectrum.vanishingIdeal W ≤ x.asIdeal := by
      intro r hr
      exact (PrimeSpectrum.mem_vanishingIdeal W r).mp hr x hxW
    have hZW := Ideal.eq_of_mem_minimalPrimes_of_le_of_isDomain_atPrime
      (A := (Spec R).presheaf.stalk x) (p := x.asIdeal)
      hZmin hWmin hZle hWle
    calc
      Z = closure Z := (isClosed_of_mem_irreducibleComponents Z hZ).closure_eq.symm
      _ = PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal Z) :=
        (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure Z).symm
      _ = PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal W) := by rw [hZW]
      _ = closure W := PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure W
      _ = W := (isClosed_of_mem_irreducibleComponents W hW).closure_eq
  · intro X Y f _ x hX hD Z W hZ hW hxZ hxW
    let : IsDomain (Y.presheaf.stalk (f x)) := hD
    let : IsDomain (X.presheaf.stalk x) :=
      (asIso (f.stalkMap x)).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain
        (Y.presheaf.stalk (f x))
    have hZ' : f ⁻¹' Z ∈ irreducibleComponents X :=
      preimage_mem_irreducibleComponents hZ f.isOpenEmbedding
        ⟨f x, hxZ, x, rfl⟩
    have hW' : f ⁻¹' W ∈ irreducibleComponents X :=
      preimage_mem_irreducibleComponents hW f.isOpenEmbedding
        ⟨f x, hxW, x, rfl⟩
    have hZW : f ⁻¹' Z = f ⁻¹' W := hX inferInstance hZ' hW' hxZ hxW
    calc
      Z = closure (f '' (f ⁻¹' Z)) :=
        (closure_image_preimage_of_isPreirreducible f f.isOpenEmbedding.isOpenMap Z
          ⟨x, hxZ⟩ hZ.1.2 (isClosed_of_mem_irreducibleComponents Z hZ)).symm
      _ = closure (f '' (f ⁻¹' W)) := by rw [hZW]
      _ = W :=
        closure_image_preimage_of_isPreirreducible f f.isOpenEmbedding.isOpenMap W
          ⟨x, hxW⟩ hW.1.2 (isClosed_of_mem_irreducibleComponents W hW)
  · exact (inferInstance : IsDomain (X.presheaf.stalk x))
  · exact hZ
  · exact hW
  · exact hxZ
  · exact hxW

/-- If a Noetherian scheme has domain local rings, then its irreducible
components are open. -/
private theorem isOpen_of_mem_irreducibleComponents_of_isNoetherian_of_stalk_isDomain
    (X : Scheme) [IsNoetherian X] [∀ x : X, IsDomain (X.presheaf.stalk x)]
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) : IsOpen Z := by
  rw [← isClosed_compl_iff]
  have hcompl : Zᶜ = ⋃₀ (irreducibleComponents X \ {Z}) := by
    ext y
    constructor
    · intro hy
      have hy' : y ∈ irreducibleComponent y := mem_irreducibleComponent
      refine Set.mem_sUnion_of_mem hy' ?_
      refine ⟨irreducibleComponent_mem_irreducibleComponents y, ?_⟩
      intro hEq
      apply hy
      exact (Set.mem_singleton_iff.mp hEq) ▸ hy'
    · intro hy hyZ
      obtain ⟨W, hW, hyW⟩ := Set.mem_sUnion.mp hy
      have hWZ := eq_irreducibleComponents_of_mem_of_isDomain_stalk X y
        hZ hW.1 hyZ hyW
      exact hW.2 (by simp [hWZ])
  rw [hcompl]
  exact (finite_irreducibleComponents_of_isNoetherian (X := X)).sdiff.isClosed_sUnion
    fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1

/-- If a locally Noetherian scheme has domain local rings, then its
irreducible components are open. -/
theorem isOpen_of_mem_irreducibleComponents_of_isLocallyNoetherian_of_stalk_isDomain
    (X : Scheme) [IsLocallyNoetherian X]
    [∀ x : X, IsDomain (X.presheaf.stalk x)]
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) : IsOpen Z := by
  rw [isOpen_iff_forall_mem_open]
  intro x hxZ
  obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
  let : IsNoetherian (X.affineCover.X i) :=
    { toIsLocallyNoetherian := inferInstance
      toCompactSpace := inferInstance }
  let : ∀ y : X.affineCover.X i,
      IsDomain ((X.affineCover.X i).presheaf.stalk y) := fun y ↦
    (asIso ((X.affineCover.f i).stalkMap y)).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain
      (X.presheaf.stalk (X.affineCover.f i y))
  have hZ' : (X.affineCover.f i) ⁻¹' Z ∈
      irreducibleComponents (X.affineCover.X i) :=
    preimage_mem_irreducibleComponents hZ (X.affineCover.f i).isOpenEmbedding
      ⟨X.affineCover.f i y, hxZ, y, rfl⟩
  refine ⟨(X.affineCover.f i) '' ((X.affineCover.f i) ⁻¹' Z),
    Set.image_preimage_subset _ _, ?_, ⟨y, hxZ, rfl⟩⟩
  exact (X.affineCover.f i).isOpenEmbedding.isOpenMap _
    (isOpen_of_mem_irreducibleComponents_of_isNoetherian_of_stalk_isDomain
      (X.affineCover.X i) hZ')

/-- A connected locally Noetherian scheme with domain local rings is
irreducible. -/
theorem irreducibleSpace_of_isLocallyNoetherian_of_connectedSpace_of_stalk_isDomain
    (X : Scheme) [IsLocallyNoetherian X] [ConnectedSpace X]
    [∀ x : X, IsDomain (X.presheaf.stalk x)] : IrreducibleSpace X := by
  rw [irreducibleSpace_def]
  let x : X := Nonempty.some inferInstance
  let Z : Set X := irreducibleComponent x
  have hZ : Z ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
  have hZopen : IsOpen Z :=
    isOpen_of_mem_irreducibleComponents_of_isLocallyNoetherian_of_stalk_isDomain X hZ
  have hZuniv : Z = Set.univ := by
    rcases isClopen_iff.mp ⟨isClosed_of_mem_irreducibleComponents Z hZ, hZopen⟩ with h | h
    · exact (hZ.1.1.ne_empty h).elim
    · exact h
  rw [Set.top_eq_univ, ← hZuniv]
  exact isIrreducible_irreducibleComponent

/-- A connected locally Noetherian scheme with domain local rings is
integral. This extends the Noetherian criterion in Vakil, *The Rising Sea*,
Exercise 5.3.C. -/
theorem isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_stalk_isDomain
    (X : Scheme) [IsLocallyNoetherian X] [ConnectedSpace X]
    [∀ x : X, IsDomain (X.presheaf.stalk x)] : IsIntegral X := by
  let := irreducibleSpace_of_isLocallyNoetherian_of_connectedSpace_of_stalk_isDomain X
  let : IsReduced X := isReduced_of_isReduced_stalk X
  exact isIntegral_of_irreducibleSpace_of_isReduced X

/-- A connected Noetherian scheme with domain local rings is irreducible. -/
theorem irreducibleSpace_of_isNoetherian_of_connectedSpace_of_stalk_isDomain
    (X : Scheme) [IsNoetherian X] [ConnectedSpace X]
    [∀ x : X, IsDomain (X.presheaf.stalk x)] : IrreducibleSpace X := by
  exact irreducibleSpace_of_isLocallyNoetherian_of_connectedSpace_of_stalk_isDomain X

/-- A connected Noetherian scheme with domain local rings is integral, as in
Vakil, *The Rising Sea*, Exercise 5.3.C. -/
theorem isIntegral_of_isNoetherian_of_connectedSpace_of_stalk_isDomain
    (X : Scheme) [IsNoetherian X] [ConnectedSpace X]
    [∀ x : X, IsDomain (X.presheaf.stalk x)] : IsIntegral X := by
  exact isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_stalk_isDomain X

end AlgebraicGeometry
