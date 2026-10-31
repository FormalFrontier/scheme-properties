/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.GenericFlatness.BasicOpen
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Generic flatness over an integral target

A locally finite type, quasi-compact morphism to an integral scheme is flat over a
nonempty dense open of the target. The restriction has the whole preimage of that
open as its source. Quasi-compactness is used to choose finitely many affine source
opens, whose flatness opens admit a common shrink.

## References

* J. S. Milne, *Algebraic Groups* (2017), for background on generic flatness.
* Mathlib's scheme, localization, and flatness APIs.
* The multivariate-polynomials generic-freeness API
  `Algebra.FiniteType.exists_free_localizationAway`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- A locally finite type, quasi-compact morphism to an integral scheme is flat over
some nonempty dense open of the target, with the whole preimage as its source.
No Noetherianity assumption on the target is required.

For background on generic flatness, see J. S. Milne, *Algebraic Groups* (2017).
The proof uses Mathlib and the multivariate-polynomials generic-freeness API. -/
theorem Scheme.Hom.exists_nonempty_dense_open_flat
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsIntegral Y] :
    ∃ U : Y.Opens,
      (U : Set Y).Nonempty ∧ Dense (U : Set Y) ∧ Flat (f ∣_ U) := by
  classical
  obtain ⟨U₀, hU₀, hη₀, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y) (x := genericPoint Y) (U := ⊤) trivial
  have : Nonempty U₀.toScheme :=
    (Scheme.Opens.nonempty_iff U₀).2 ⟨genericPoint Y, hη₀⟩
  have : IsDomain Γ(Y, U₀) := inferInstance
  obtain ⟨s, hs, hcover⟩ :=
    (isCompact_iff_finite_and_eq_biUnion_affineOpens (X := X)).mp
      (f.isCompact_preimage hU₀.isCompact)
  let := hs.fintype
  let W (i : s) : X.Opens := i.1.1
  have hW (i : s) : IsAffineOpen (W i) := i.1.2
  have e (i : s) : W i ≤ f ⁻¹ᵁ U₀ := by
    rw [hcover]
    exact le_iSup_of_le i.1 (le_iSup_of_le i.2 le_rfl)
  have hchart (i : s) :
      ∃ a : Γ(Y, U₀), a ≠ 0 ∧
        Flat (f.resLE (Y.basicOpen a)
          (W i ⊓ f ⁻¹ᵁ Y.basicOpen a) inf_le_right) :=
    f.exists_flat_resLE_basicOpen hU₀ (hW i) (e i)
      (f.finiteType_appLE hU₀ (hW i) (e i))
  choose a ha hflat using hchart
  have hη (i : s) : genericPoint Y ∈ Y.basicOpen (a i) := by
    apply ((genericPoint_spec Y).mem_open_set_iff (Y.basicOpen (a i)).isOpen).2
    rw [Set.univ_inter, hU₀.basicOpen_nonempty_iff (a i)]
    simpa only [isNilpotent_iff_eq_zero] using ha i
  -- The initial open is retained even when there are no source charts.
  have hcommon (t : Finset s) :
      ∃ U : Y.Opens, genericPoint Y ∈ U ∧ U ≤ U₀ ∧
        ∀ i ∈ t, U ≤ Y.basicOpen (a i) := by
    induction t using Finset.induction_on with
    | empty =>
        exact ⟨U₀, hη₀, le_rfl, by simp⟩
    | @insert i t hi ih =>
        obtain ⟨U, hηU, hUU₀, hUi⟩ := ih
        refine ⟨U ⊓ Y.basicOpen (a i), ⟨hηU, hη i⟩,
          inf_le_left.trans hUU₀, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with hji | hj
        · subst j
          exact inf_le_right
        · exact inf_le_left.trans (hUi j hj)
  obtain ⟨V, hηV, hVU₀, hVi⟩ := hcommon Finset.univ
  obtain ⟨r, hrV, hηU⟩ :=
    hU₀.exists_basicOpen_le (V := V) ⟨genericPoint Y, hηV⟩ hη₀
  let U : Y.Opens := Y.basicOpen r
  have hU : IsAffineOpen U := hU₀.basicOpen r
  have : IsAffine U.toScheme := hU
  have hUU₀ : U ≤ U₀ := hrV.trans hVU₀
  have hUD (i : s) : U ≤ Y.basicOpen (a i) :=
    hrV.trans (hVi i (Finset.mem_univ i))
  refine ⟨U, ⟨genericPoint Y, hηU⟩, U.isOpen.dense ⟨genericPoint Y, hηU⟩, ?_⟩
  have hflatU (i : s) :
      Flat (f.resLE U (W i ⊓ f ⁻¹ᵁ U) inf_le_right) := by
    let D : Y.Opens := Y.basicOpen (a i)
    let T : X.Opens := W i ⊓ f ⁻¹ᵁ D
    let K : X.Opens := W i ⊓ f ⁻¹ᵁ U
    have hUD' : U ≤ D := hUD i
    have hKT : K ≤ T := inf_le_inf_left _ (f.preimage_mono hUD')
    have hK : K = f ⁻¹ᵁ U ⊓ (𝟙 X) ⁻¹ᵁ T := by
      ext x
      constructor
      · rintro ⟨hxW, hxU⟩
        exact ⟨hxU, hxW, f.preimage_mono hUD' hxU⟩
      · rintro ⟨hxU, hxW, _⟩
        exact ⟨hxW, hxU⟩
    have hpb : IsPullback (f.resLE U K inf_le_right)
        (X.homOfLE hKT) (Y.homOfLE hUD') (f.resLE D T inf_le_right) := by
      have hpb' := Scheme.Hom.isPullback_resLE (IsPullback.id_vert f)
        (US := D) (UT := T) (UX := U) (UY := K)
        (show T ≤ f ⁻¹ᵁ D from inf_le_right) (by simpa using hUD') hK
      have hXT : Scheme.Hom.resLE (𝟙 X : X ⟶ X) T K (by simpa using hKT) =
          X.homOfLE hKT :=
        Scheme.Hom.resLE_id hKT
      have hYD : Scheme.Hom.resLE (𝟙 Y : Y ⟶ Y) D U (by simpa using hUD') =
          Y.homOfLE hUD' :=
        Scheme.Hom.resLE_id hUD'
      rw [hXT, hYD] at hpb'
      exact hpb'
    exact MorphismProperty.of_isPullback (P := @Flat.{u}) hpb.flip (hflat i)
  let p := (f ⁻¹ᵁ U).ι
  let Ω (i : s) : (f ⁻¹ᵁ U).toScheme.Opens := p ⁻¹ᵁ W i
  have hΩ : iSup Ω = ⊤ := by
    apply le_antisymm le_top
    intro x _
    have hx : p x ∈ f ⁻¹ᵁ U₀ := f.preimage_mono hUU₀ x.property
    rw [hcover] at hx
    obtain ⟨V, hV⟩ := Opens.mem_iSup.mp hx
    obtain ⟨hVs, hxV⟩ := Opens.mem_iSup.mp hV
    exact Opens.mem_iSup.mpr ⟨⟨V, hVs⟩, hxV⟩
  have hlocal (i : s) : Flat ((Ω i).ι ≫ f ∣_ U) := by
    have himg : p ''ᵁ Ω i = W i ⊓ f ⁻¹ᵁ U := by
      change p ''ᵁ (p ⁻¹ᵁ W i) = W i ⊓ f ⁻¹ᵁ U
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
      simp only [p, Scheme.Opens.opensRange_ι, inf_comm]
    have eJ : p ''ᵁ Ω i ≤ f ⁻¹ᵁ U := by
      rw [himg]
      exact inf_le_right
    have htransport : ∀ (J : X.Opens), J = W i ⊓ f ⁻¹ᵁ U →
        ∀ (eJ : J ≤ f ⁻¹ᵁ U), Flat (f.resLE U J eJ) := by
      rintro J rfl eJ
      exact hflatU i
    have hJflat : Flat (f.resLE U (p ''ᵁ Ω i) eJ) :=
      htransport _ himg eJ
    have heq : (p.isoImage (Ω i)).hom ≫ f.resLE U (p ''ᵁ Ω i) eJ =
        (Ω i).ι ≫ f ∣_ U := by
      apply (cancel_mono U.ι).1
      simp only [Category.assoc, Scheme.Hom.resLE_comp_ι,
        Scheme.Hom.isoImage_hom_ι_assoc, morphismRestrict_ι]
      rfl
    rw [← heq]
    exact Flat.comp _ _ (hg := hJflat)
  let 𝒰 : (f ⁻¹ᵁ U).toScheme.OpenCover :=
    (f ⁻¹ᵁ U).toScheme.openCoverOfIsOpenCover Ω
      (TopologicalSpace.IsOpenCover.mk hΩ)
  let 𝒱 := 𝒰.affineRefinement.openCover
  have hAffine : ∀ (j : 𝒱.I₀), IsAffine (𝒱.X j) := fun j =>
    inferInstanceAs (IsAffine (Spec (𝒰.affineRefinement.X j)))
  let ρ : 𝒱 ⟶ 𝒰 := 𝒰.fromAffineRefinement
  refine HasRingHomProperty.of_source_openCover
    (P := @Flat.{u}) (Q := RingHom.Flat) (f := f ∣_ U) 𝒱 ?_
  intro j
  have hi : Flat (𝒰.f (ρ.s₀ j) ≫ f ∣_ U) := hlocal (ρ.s₀ j)
  have hr : Flat (ρ.h₀ j) := inferInstance
  have hc : Flat (ρ.h₀ j ≫ (𝒰.f (ρ.s₀ j) ≫ f ∣_ U)) :=
    Flat.comp _ _ (hf := hr) (hg := hi)
  have hFlat_refined : Flat (𝒱.f j ≫ f ∣_ U) := by
    simpa only [← Category.assoc, ρ.w₀ j] using hc
  exact HasRingHomProperty.appTop (P := @Flat.{u}) (Q := RingHom.Flat)
    _ hFlat_refined

end AlgebraicGeometry
