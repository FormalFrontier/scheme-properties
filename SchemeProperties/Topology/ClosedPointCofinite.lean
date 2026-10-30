/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Topology
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.Topology.JacobsonSpace

/-!
# Cofinite topology on closed points of curves

In a preirreducible Noetherian space of topological Krull dimension at most one,
the induced topology on `closedPoints X` is cofinite. The characteristic API is
`isClosed_closedPoints_iff_of_topologicalKrullDim_le_one`: a subset of the
closed-point subspace is closed exactly when it is the whole space or finite.

The ambient finiteness statement concerns only the closed-point trace of a
proper closed set. The ambient set itself need not be finite without separation
hypotheses. The proof uses Mathlib's finite irreducible decomposition and
`Order.krullDim_le_one_iff`, applying minimality to individually closed
singletons rather than assuming the ambient space is T1.

The polynomial-line and maximal-spectrum specializations hold over every field,
with their Zariski topologies. In particular, they do not identify closed points
with roots in the base field. The generic theorem also applies to schemes with
Noetherian preirreducible underlying spaces, including nonreduced schemes and
the empty space; no Jacobson or sobriety hypothesis is needed.
-/

public section

open Set TopologicalSpace Topology

universe u

private theorem topologicalSpace_eq_cofinite_of_isClosed_iff {Y : Type*}
    [TopologicalSpace Y]
    (h : ∀ s : Set Y, IsClosed s ↔ s = univ ∨ s.Finite) :
    (inferInstance : TopologicalSpace Y) = TopologicalSpace.cofinite := by
  apply TopologicalSpace.ext_isClosed
  intro s
  rw [h s, ← @isOpen_compl_iff Y s TopologicalSpace.cofinite]
  change (s = univ ∨ s.Finite) ↔ (sᶜ.Nonempty → sᶜᶜ.Finite)
  simp only [compl_compl, Set.nonempty_compl, or_iff_not_imp_left]

variable {X : Type u} [TopologicalSpace X] [PreirreducibleSpace X]

private theorem irreducibleCloseds_eq_singleton_of_mem_closedPoints
    (hdim : topologicalKrullDim X ≤ 1) (C : IrreducibleCloseds X)
    (hC : (C : Set X) ≠ univ) {x : X} (hxC : x ∈ C)
    (hx : x ∈ closedPoints X) : (C : Set X) = {x} := by
  let P : IrreducibleCloseds X := ⟨{x}, isIrreducible_singleton, hx⟩
  let U : IrreducibleCloseds X :=
    ⟨univ, ⟨⟨x, Set.mem_univ x⟩, PreirreducibleSpace.isPreirreducible_univ⟩,
      isClosed_univ⟩
  have hPC : P ≤ C := Set.singleton_subset_iff.mpr hxC
  have hCU : C ≤ U := Set.subset_univ _
  rcases Order.krullDim_le_one_iff.mp hdim C with hmin | hmax
  · exact congrArg (fun A : IrreducibleCloseds X ↦ (A : Set X)) (hmin.eq_of_ge hPC)
  · exact (hC (Set.Subset.antisymm hCU (hmax hCU))).elim

variable [NoetherianSpace X]

/-- A proper closed subset of a preirreducible Noetherian space of dimension at
most one contains only finitely many closed points. The closed subset itself
need not be finite. -/
theorem finite_inter_closedPoints_of_isClosed_of_ne_univ
    (hdim : topologicalKrullDim X ≤ 1) {Z : Set X} (hZ : IsClosed Z)
    (hZproper : Z ≠ univ) : (Z ∩ closedPoints X).Finite := by
  obtain ⟨S, hSf, hSc, hSi, hZS⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  have htrace : ∀ t ∈ S, (t ∩ closedPoints X).Finite := by
    intro t ht
    rcases Set.eq_empty_or_nonempty (t ∩ closedPoints X) with hempty | ⟨x, hxt, hx⟩
    · rw [hempty]
      exact Set.finite_empty
    · have htZ : t ⊆ Z := by
        rw [hZS]
        exact Set.subset_sUnion_of_mem ht
      have htproper : t ≠ univ := by
        intro htu
        apply hZproper
        apply Set.eq_univ_of_forall
        intro y
        apply htZ
        rw [htu]
        trivial
      have heq : t = {x} :=
        irreducibleCloseds_eq_singleton_of_mem_closedPoints hdim
          ⟨t, hSi t ht, hSc t ht⟩ htproper hxt hx
      rw [heq]
      exact (Set.finite_singleton x).subset Set.inter_subset_left
  apply (hSf.biUnion htrace).subset
  intro x hx
  obtain ⟨t, ht, hxt⟩ := Set.mem_sUnion.mp (hZS ▸ hx.1)
  simp only [Set.mem_iUnion]
  exact ⟨t, ht, hxt, hx.2⟩

/-- In the induced topology on the closed points of a preirreducible Noetherian
space of dimension at most one, the closed subsets are exactly the whole space
and the finite subsets. No separation or nonemptiness assumption is required. -/
theorem isClosed_closedPoints_iff_of_topologicalKrullDim_le_one
    (hdim : topologicalKrullDim X ≤ 1) (s : Set (closedPoints X)) :
    IsClosed s ↔ s = univ ∨ s.Finite := by
  classical
  constructor
  · intro hs
    obtain ⟨Z, hZ, rfl⟩ := isClosed_induced_iff.mp hs
    by_cases hZuniv : Z = univ
    · left
      simp only [hZuniv, Set.preimage_univ]
    · right
      apply ((finite_inter_closedPoints_of_isClosed_of_ne_univ hdim hZ hZuniv).preimage
        (f := (Subtype.val : closedPoints X → X)) Subtype.coe_injective.injOn).subset
      intro x hx
      exact ⟨hx, x.property⟩
  · rintro (rfl | hs)
    · exact isClosed_univ
    · rw [← Set.biUnion_of_singleton s]
      apply hs.isClosed_biUnion
      intro x _
      apply isClosed_induced_iff.mpr
      refine ⟨{(x : X)}, x.property, ?_⟩
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff]

/-- The given subtype topology on the closed points of a preirreducible
Noetherian space of dimension at most one equals the cofinite topology. -/
theorem topologicalSpace_closedPoints_eq_cofinite_of_topologicalKrullDim_le_one
    (hdim : topologicalKrullDim X ≤ 1) :
    (inferInstance : TopologicalSpace (closedPoints X)) = TopologicalSpace.cofinite :=
  topologicalSpace_eq_cofinite_of_isClosed_iff
    (isClosed_closedPoints_iff_of_topologicalKrullDim_le_one hdim)

private theorem topologicalKrullDim_primeSpectrum_polynomial_le_one
    (K : Type u) [Field K] : topologicalKrullDim (PrimeSpectrum (Polynomial K)) ≤ 1 := by
  simp only [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
    zero_add, le_refl]

/-- Over any field, the Zariski subspace topology on the closed points of the
polynomial line is cofinite. -/
theorem topologicalSpace_closedPoints_polynomial_eq_cofinite (K : Type u) [Field K] :
    (inferInstance : TopologicalSpace (closedPoints (PrimeSpectrum (Polynomial K)))) =
      TopologicalSpace.cofinite :=
  topologicalSpace_closedPoints_eq_cofinite_of_topologicalKrullDim_le_one
    (topologicalKrullDim_primeSpectrum_polynomial_le_one K)

/-- Over any field, the Zariski topology on the maximal spectrum of the
univariate polynomial ring is cofinite. This uses its existing topology induced
by the inclusion into the prime spectrum. -/
theorem MaximalSpectrum.topologicalSpace_polynomial_eq_cofinite (K : Type u) [Field K] :
    (inferInstance : TopologicalSpace (MaximalSpectrum (Polynomial K))) =
      TopologicalSpace.cofinite := by
  have hmem : ∀ x : MaximalSpectrum (Polynomial K),
      MaximalSpectrum.toPrimeSpectrum x ∈ closedPoints (PrimeSpectrum (Polynomial K)) := by
    intro x
    have hx : MaximalSpectrum.toPrimeSpectrum x ∈
        Set.range (MaximalSpectrum.toPrimeSpectrum (R := Polynomial K)) := ⟨x, rfl⟩
    rw [MaximalSpectrum.toPrimeSpectrum_range] at hx
    exact hx
  let f := (closedPoints (PrimeSpectrum (Polynomial K))).codRestrict
    MaximalSpectrum.toPrimeSpectrum hmem
  have hemb : IsEmbedding (MaximalSpectrum.toPrimeSpectrum (R := Polynomial K)) :=
    ⟨⟨rfl⟩, MaximalSpectrum.toPrimeSpectrum_injective⟩
  have hf : IsEmbedding f := hemb.codRestrict _ hmem
  have hsurj : Function.Surjective f := by
    intro x
    have hx : x.val ∈ Set.range (MaximalSpectrum.toPrimeSpectrum (R := Polynomial K)) := by
      rw [MaximalSpectrum.toPrimeSpectrum_range]
      exact x.property
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, Subtype.ext hy⟩
  have hfclosed : IsClosedEmbedding f := ⟨hf, by rw [hsurj.range_eq]; exact isClosed_univ⟩
  apply topologicalSpace_eq_cofinite_of_isClosed_iff
  intro s
  rw [hfclosed.isClosed_iff_image_isClosed,
    isClosed_closedPoints_iff_of_topologicalKrullDim_le_one
      (topologicalKrullDim_primeSpectrum_polynomial_le_one K)]
  constructor
  · rintro (hs | hs)
    · left
      have hpre := congrArg (fun t ↦ f ⁻¹' t) hs
      simpa only [Set.preimage_image_eq s hf.injective, Set.preimage_univ] using hpre
    · exact Or.inr (hs.of_finite_image hf.injective.injOn)
  · rintro (rfl | hs)
    · exact Or.inl (Set.image_univ_of_surjective hsurj)
    · exact Or.inr (hs.image f)
