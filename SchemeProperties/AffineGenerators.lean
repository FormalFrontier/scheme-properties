/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Mathlib.CategoryTheory.Generator.StrongGenerator
public import Mathlib.Logic.Function.Basic

/-!
# Affine schemes as generators

Affine schemes form a strong generator of the category of schemes. In particular,
a morphism is an isomorphism if every morphism from an affine scheme factors uniquely
through it. Equivalently, postcomposition induces a bijection on `Spec R`-valued points
for every commutative ring `R` in the scheme universe, including the zero ring.

The interfaces use `CategoryTheory.ObjectProperty.IsStrongGenerator` and
`CategoryTheory.ObjectProperty.IsDetecting`. Their separation, subobject and unique-lifting
APIs apply directly; no additional notion of a scheme-valued point is introduced.

## References

- Mathlib, `CategoryTheory.Generator.StrongGenerator`: strong generators from colimit
  presentations, and their subobject and monomorphism APIs.
- Mathlib, `AlgebraicGeometry.Cover.Directed`: the colimit presentation by all affine opens;
  compatibility on overlaps is checked using affine refinements, not affine intersections.
- J. S. Milne, *Algebraic Groups* (2017), §I.1: functor-of-points motivation. The results here
  concern arbitrary schemes and all commutative rings, rather than finite-type field schemes.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Affine schemes form a strong generator of the category of schemes, in the sense of
Mathlib's `ObjectProperty.IsStrongGenerator` and its colimit-presentation criterion. -/
theorem isStrongGenerator_isAffine :
    ObjectProperty.IsStrongGenerator (fun T : Scheme.{u} => IsAffine T) := by
  refine ObjectProperty.IsStrongGenerator.mk_of_exists_colimitsOfShape.{u, u} fun X ↦ ?_
  refine ⟨X.affineOpens, inferInstance, ?_⟩
  exact ⟨{
    diag := X.directedAffineCover.functorOfLocallyDirected
    ι := X.directedAffineCover.functorOfLocallyDirectedHomBase
    isColimit := X.directedAffineCover.isColimitCoconeOfLocallyDirected
    prop_diag_obj U := inferInstanceAs (IsAffine U) }⟩

/-- Affine schemes detect isomorphisms: unique factorization of every affine-source morphism
through a given morphism forces that morphism to be an isomorphism. -/
theorem isDetecting_isAffine :
    ObjectProperty.IsDetecting (fun T : Scheme.{u} => IsAffine T) := by
  intro X Y f hf
  have hStrong := isStrongGenerator_isAffine.{u}
  have : Mono f := (hStrong.isSeparating.mono_iff f).2 (by
    intro G hG g₁ g₂ h
    exact (hf G hG (g₂ ≫ f)).unique h rfl)
  exact hStrong.isIso_of_mono f (fun G hG h => (hf G hG h).exists)

/-- A scheme morphism is an isomorphism precisely when postcomposition is bijective on points
valued in every commutative ring in the scheme universe. The zero ring is included. -/
theorem isIso_iff_bijective_spec {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso f ↔ ∀ (R : Type u) [CommRing R],
      Function.Bijective (fun g : Spec (.of R) ⟶ X => g ≫ f) := by
  constructor
  · intro hf
    let : IsIso f := hf
    intro R _
    constructor
    · intro g₁ g₂ h
      exact (cancel_mono f).mp h
    · intro h
      exact ⟨h ≫ inv f, by simp [Category.assoc]⟩
  · intro hf
    apply isDetecting_isAffine f
    intro G hG h
    let : IsAffine G := hG
    have hR := hf Γ(G, ⊤)
    obtain ⟨g, hg, hg_unique⟩ :=
      (Function.bijective_iff_existsUnique _).mp hR (G.isoSpec.inv ≫ h)
    refine ⟨G.isoSpec.hom ≫ g, ?_, ?_⟩
    · simp only [Category.assoc, hg, Iso.hom_inv_id_assoc]
    · intro g' hg'
      apply (cancel_epi G.isoSpec.inv).mp
      simpa only [Iso.inv_hom_id_assoc] using
        hg_unique (G.isoSpec.inv ≫ g') (by simpa only [Category.assoc, hg'])

end AlgebraicGeometry.Scheme
