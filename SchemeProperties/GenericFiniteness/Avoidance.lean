/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.Topology.Sober

/-!
# Avoiding a closed subset near a generic point

A closed subset of a quasi-compact scheme over an affine base cannot accumulate at a
minimal point of the base without meeting its fibre. Consequently a quasi-compact
morphism can be restricted near a whole-base generic point so that its whole preimage
lies in any prescribed open containing that fibre.

## References

* Mathlib's prime-spectrum closure formula and minimal-prime lifting theorem.
* Mathlib's affine cover and quasi-compact morphism formalizations.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

private lemma mem_image_of_mem_closure_image_comap_of_minimal
    {R B : Type*} [CommRing R] [CommRing B] (φ : R →+* B)
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R)
    {Z : Set (PrimeSpectrum B)} (hZ : IsClosed Z)
    (h : p ∈ closure (PrimeSpectrum.comap φ '' Z)) :
    p ∈ PrimeSpectrum.comap φ '' Z := by
  obtain ⟨I, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z).mp hZ
  rw [PrimeSpectrum.closure_image_comap_zeroLocus] at h
  have hminimal : p.asIdeal ∈ (I.comap φ).minimalPrimes :=
    ⟨⟨p.isPrime, h⟩, fun q hq hqp ↦ hp.2 ⟨hq.1, bot_le⟩ hqp⟩
  obtain ⟨q, hq, hIq, hqp⟩ :=
    Ideal.exists_comap_eq_of_mem_minimalPrimes φ p.asIdeal hminimal
  exact ⟨⟨q, hq⟩, hIq, PrimeSpectrum.ext hqp⟩

private lemma mem_image_of_mem_closure_image_toSpec_of_minimal
    {X : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Spec R)
    [CompactSpace X] (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R)
    {Z : Set X} (hZ : IsClosed Z) (h : p ∈ closure (f '' Z)) : p ∈ f '' Z := by
  obtain ⟨B, g, hg⟩ := (compactSpace_iff_exists (X := X)).mp inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (g ≫ f)
  have heq : PrimeSpectrum.comap φ.hom '' (g ⁻¹' Z) = f '' Z := by
    change (Spec.map φ) '' (g ⁻¹' Z) = f '' Z
    rw [hφ]
    change (f ∘ g) '' (g ⁻¹' Z) = f '' Z
    rw [Set.image_comp, Set.image_preimage_eq _ hg]
  rw [← heq] at h
  have hmem := mem_image_of_mem_closure_image_comap_of_minimal φ.hom p hp
    (hZ.preimage g.continuous) h
  exact (Set.ext_iff.mp heq p).mp hmem

/-- For a quasi-compact source over an affine target, a closed subset whose image
misses a whole-base generic point has image closure missing that point as well.
No finite-type or reducedness assumption is needed. -/
theorem Scheme.Hom.notMem_closure_image_of_isGenericPoint
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace X] [IsAffine S]
    (η : S) (hη : IsGenericPoint η (Set.univ : Set S))
    {Z : Set X} (hZ : IsClosed Z) (h : η ∉ f '' Z) :
    η ∉ closure (f '' Z) := by
  let e := S.isoSpec
  let p : PrimeSpectrum Γ(S, ⊤) := e.hom η
  have hpgen : IsGenericPoint p (Set.univ : Set (PrimeSpectrum Γ(S, ⊤))) := by
    let e' : S ≃ₜ PrimeSpectrum Γ(S, ⊤) := e.hom.homeomorph
    change IsGenericPoint (e' η) (Set.univ : Set (PrimeSpectrum Γ(S, ⊤)))
    have hrange : Set.range e' = Set.univ := Set.range_eq_univ.mpr e'.surjective
    simpa only [Set.image_univ, hrange, closure_univ] using hη.image e'.continuous
  have hp : p.asIdeal ∈ minimalPrimes Γ(S, ⊤) := by
    apply PrimeSpectrum.isMin_iff.mp
    intro q _
    exact (PrimeSpectrum.le_iff_specializes p q).mpr (hpgen.specializes (Set.mem_univ q))
  intro hclosure
  have hclosure' : p ∈ closure ((f ≫ e.hom) '' Z) := by
    have hcomp : (f ≫ e.hom) '' Z = e.hom '' (f '' Z) := by
      change (e.hom ∘ f) '' Z = e.hom '' (f '' Z)
      exact Set.image_comp e.hom f Z
    rw [hcomp]
    change e.hom η ∈ closure (e.hom '' (f '' Z))
    exact image_closure_subset_closure_image e.hom.continuous ⟨η, hclosure, rfl⟩
  obtain ⟨x, hxZ, hx⟩ :=
    mem_image_of_mem_closure_image_toSpec_of_minimal (f ≫ e.hom) p hp hZ hclosure'
  apply h
  refine ⟨x, hxZ, ?_⟩
  exact e.hom.homeomorph.injective hx

/-- A quasi-compact morphism can be shrunk near a given whole-base generic point
so that its whole preimage lies in a prescribed open containing the fibre.
There is no separation, finite-type, or reducedness hypothesis. -/
theorem Scheme.Hom.exists_open_preimage_subset_of_isGenericPoint
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    (η : S) (hη : IsGenericPoint η (Set.univ : Set S))
    (W : X.Opens) (hW : f ⁻¹' {η} ⊆ W) :
    ∃ U : S.Opens, η ∈ U ∧ f ⁻¹ᵁ U ≤ W := by
  obtain ⟨A, hA, hηA, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := S) (x := η) (U := ⊤) trivial
  have : IsAffine A.toScheme := hA
  let ηA : A.toScheme := ⟨η, hηA⟩
  have hgenA : IsGenericPoint ηA (Set.univ : Set A.toScheme) := by
    apply isGenericPoint_iff_specializes.mpr
    intro y
    simp only [Set.mem_univ, iff_true]
    exact (subtype_specializes_iff ηA y).mpr (hη.specializes (Set.mem_univ y.1))
  let g := f ∣_ A
  let p := (f ⁻¹ᵁ A).ι
  have : CompactSpace (f ⁻¹ᵁ A).toScheme :=
    QuasiCompact.compactSpace_of_compactSpace g
  let Z : Set (f ⁻¹ᵁ A).toScheme := p ⁻¹' (W : Set X)ᶜ
  have hZ : IsClosed Z := W.isOpen.isClosed_compl.preimage p.continuous
  have hmiss : ηA ∉ g '' Z := by
    rintro ⟨x, hxZ, hx⟩
    have hxη : f (p x) = η := by
      have heq := congrArg (fun y : A.toScheme ↦ y.1) hx
      exact (morphismRestrict_base_coe f A x).symm.trans heq
    exact hxZ (hW (show p x ∈ f ⁻¹' {η} from hxη))
  have havoid := g.notMem_closure_image_of_isGenericPoint ηA hgenA hZ hmiss
  let V : A.toScheme.Opens := ⟨(closure (g '' Z))ᶜ, isClosed_closure.isOpen_compl⟩
  refine ⟨A.ι ''ᵁ V, ⟨ηA, havoid, rfl⟩, ?_⟩
  intro x hx
  obtain ⟨y, hy, hyx⟩ := hx
  have hxA : x ∈ f ⁻¹ᵁ A := by
    change f x ∈ A
    rw [← hyx]
    exact y.2
  have hxy : g ⟨x, hxA⟩ = y := by
    apply Subtype.ext
    exact (morphismRestrict_base_coe f A ⟨x, hxA⟩).trans hyx.symm
  by_contra hxW
  apply hy
  apply subset_closure
  refine ⟨⟨x, hxA⟩, hxW, hxy⟩

end AlgebraicGeometry
