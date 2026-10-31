/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.GenericFlatness.Pointed
public import SchemeProperties.Integral

/-!
# Affine flat source opens over reduced schemes

A surjective locally finite type morphism to a nonempty reduced scheme with finitely many
irreducible components has a nonempty affine open in its source on which it is flat. No
quasi-compactness assumption on the source or the morphism is required.

The proof combines `Scheme.exists_nonempty_isIntegral_open` with
`Scheme.Hom.exists_nonempty_isAffineOpen_flat`. Mathlib's open-image and `isoImage` APIs
identify the resulting affine open with an open of the original source scheme.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A surjective locally finite type morphism to a nonempty reduced scheme with finitely
many irreducible components is flat on some nonempty affine open of its source. -/
theorem Scheme.Hom.exists_nonempty_isAffineOpen_flat_of_finite_irreducibleComponents
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Surjective f] [IsReduced Y] [Nonempty Y]
    (hfinite : (irreducibleComponents Y).Finite) :
    ∃ U : X.Opens, (U : Set X).Nonempty ∧ IsAffineOpen U ∧ Flat (U.ι ≫ f) := by
  obtain ⟨V, _, hV⟩ := Y.exists_nonempty_isIntegral_open hfinite
  have : IsIntegral V.toScheme := hV
  let W : X.Opens := f ⁻¹ᵁ V
  let g : W.toScheme ⟶ V.toScheme := f.resLE V W le_rfl
  have hg : g = f ∣_ V := f.resLE_eq_morphismRestrict
  have : LocallyOfFiniteType g := by
    rw [hg]
    infer_instance
  have : Surjective g := by
    rw [hg]
    exact IsZariskiLocalAtTarget.restrict (P := @Surjective) inferInstance V
  obtain ⟨A, hA, hAaff, hAflat⟩ := g.exists_nonempty_isAffineOpen_flat
  let U : X.Opens := W.ι ''ᵁ A
  refine ⟨U, ?_, hAaff.image_of_isOpenImmersion W.ι, ?_⟩
  · obtain ⟨x, hx⟩ := hA
    exact ⟨W.ι x, (Scheme.Hom.apply_mem_image_iff W.ι).2 hx⟩
  · have : Flat (A.ι ≫ g) := hAflat
    have hgι : g ≫ V.ι = W.ι ≫ f := f.resLE_comp_ι le_rfl
    simpa only [Category.assoc, hgι, Scheme.Hom.isoImage_inv_ι_assoc] using
      (inferInstance : Flat ((W.ι.isoImage A).inv ≫ (A.ι ≫ g) ≫ V.ι))

end AlgebraicGeometry
