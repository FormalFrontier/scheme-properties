/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Topology.JacobsonSpace
public import SchemeProperties.RingTheory.Jacobson.PrimeSpectrum

/-!
# Surjectivity of quasi-compact morphisms to Jacobson schemes

A quasi-compact morphism to a Jacobson scheme is surjective if its image
contains every closed point of the target. Over each affine open of the target,
quasi-compactness supplies a finite affine cover of its entire inverse image.
Affine-coordinate naturality then reduces the assertion to the finite-family
criterion for images of maps of prime spectra.

## References

* "Quasi-compact morphisms onto Jacobson schemes: testing surjectivity on closed points", §3.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A quasi-compact morphism to a Jacobson scheme is surjective whenever every
closed point of the target lies in its image. No Jacobson hypothesis on the
source is required. -/
theorem Scheme.Hom.surjective_of_closedPoints_subset_range
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [JacobsonSpace Y]
    (h : closedPoints Y ⊆ Set.range f) : Function.Surjective f := by
  classical
  intro y
  obtain ⟨U, hU, hy, _⟩ :=
    exists_isAffineOpen_mem_and_subset (show y ∈ (⊤ : Y.Opens) from trivial)
  let e : U ≃ₜ PrimeSpectrum Γ(Y, U) := hU.isoSpec.hom.homeomorph
  let : JacobsonSpace U := JacobsonSpace.of_isOpenEmbedding U.isOpenEmbedding'
  let : JacobsonSpace (PrimeSpectrum Γ(Y, U)) :=
    JacobsonSpace.of_isOpenEmbedding e.symm.isOpenEmbedding
  have hW : IsCompact (f ⁻¹ᵁ U : Set X) :=
    quasiCompact_iff_forall_isAffineOpen.mp (inferInstance : QuasiCompact f) U hU
  obtain ⟨s, hs, hsW⟩ :=
    isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
      ⟨hW, (f ⁻¹ᵁ U).isOpen⟩
  let : Fintype s := hs.fintype
  let V (i : s) : X.Opens := i.1.1
  have hV (i : s) : IsAffineOpen (V i) := i.1.2
  have hVU (i : s) : V i ≤ f ⁻¹ᵁ U := by
    intro x hx
    have hx' : x ∈ ⋃ j ∈ s, (j : Set X) :=
      Set.mem_iUnion.mpr ⟨i.1, Set.mem_iUnion.mpr ⟨i.2, hx⟩⟩
    exact (Set.ext_iff.mp hsW x).mpr hx'
  let φ (i : s) : Γ(Y, U) →+* Γ(X, V i) := (f.appLE U (V i) (hVU i)).hom
  have hclosed : closedPoints (PrimeSpectrum Γ(Y, U)) ⊆
      ⋃ i, Set.range (PrimeSpectrum.comap (φ i)) := by
    intro m hm
    -- A closed point in the affine chart is closed in the ambient Jacobson space.
    have hmU : e.symm m ∈ closedPoints U :=
      (Set.ext_iff.mp e.symm.isOpenEmbedding.preimage_closedPoints m).mpr hm
    have hmY : (e.symm m : U).1 ∈ closedPoints Y :=
      (Set.ext_iff.mp U.isOpenEmbedding'.preimage_closedPoints (e.symm m)).mpr hmU
    obtain ⟨x, hfx⟩ := h hmY
    have hxW : x ∈ (f ⁻¹ᵁ U : Set X) :=
      show f x ∈ U from hfx.symm ▸ (e.symm m).2
    rw [hsW] at hxW
    simp only [Set.mem_iUnion] at hxW
    obtain ⟨i, hi, hxi⟩ := hxW
    let j : s := ⟨i, hi⟩
    have hxu : (⟨f x, hVU j hxi⟩ : U) = e.symm m := Subtype.ext hfx
    refine Set.mem_iUnion.mpr ⟨j, (hV j).primeIdealOf ⟨x, hxi⟩, ?_⟩
    calc
      ((hV j).primeIdealOf ⟨x, hxi⟩).comap (φ j) =
          hU.primeIdealOf ⟨f x, hVU j hxi⟩ :=
        IsAffineOpen.comap_primeIdealOf_appLE U hU (V j) (hV j) (hVU j) hxi
      _ = e (e.symm m) := congrArg hU.primeIdealOf hxu
      _ = m := e.apply_symm_apply m
  have hall :=
    PrimeSpectrum.iUnion_range_comap_eq_univ_of_closedPoints_subset φ hclosed
  have hy' : e ⟨y, hy⟩ ∈ ⋃ i, Set.range (PrimeSpectrum.comap (φ i)) := by
    rw [hall]
    exact Set.mem_univ _
  obtain ⟨i, P, hP⟩ := Set.mem_iUnion.mp hy'
  let v : V i := ((hV i).isoSpec.hom.homeomorph).symm P
  have hv : (hV i).primeIdealOf v = P :=
    ((hV i).isoSpec.hom.homeomorph).apply_symm_apply P
  have hxy : (⟨f v.1, hVU i v.2⟩ : U) = ⟨y, hy⟩ := by
    apply e.injective
    calc
      e ⟨f v.1, hVU i v.2⟩ = ((hV i).primeIdealOf v).comap (φ i) :=
        (IsAffineOpen.comap_primeIdealOf_appLE U hU (V i) (hV i) (hVU i) v.2).symm
      _ = P.comap (φ i) := congrArg (PrimeSpectrum.comap (φ i)) hv
      _ = e ⟨y, hy⟩ := hP
  exact ⟨v.1, congrArg Subtype.val hxy⟩

end AlgebraicGeometry
