/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.GenericFlatness.BasicOpen
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Flat affine neighborhoods above the generic point

For a locally finite type morphism to an integral scheme, every point above the generic
point has an affine open neighborhood on which the morphism is flat. In particular, a
surjective locally finite type morphism to an integral scheme has a nonempty affine open
source on which it is flat. Neither statement requires quasi-compactness of the morphism.

## References

* J. S. Milne, *Algebraic Groups* (2017), for background on generic flatness.
* Mathlib's scheme, localization, and flatness APIs.
* The multivariate-polynomials generic-freeness API
  `Algebra.FiniteType.exists_free_localizationAway`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A point above the generic point of an integral scheme has an affine open neighborhood
on which a locally finite type morphism is flat.

For background on generic flatness, see J. S. Milne, *Algebraic Groups* (2017).
The proof uses Mathlib and the multivariate-polynomials generic-freeness API. -/
theorem Scheme.Hom.exists_isAffineOpen_mem_flat_of_map_eq_genericPoint
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsIntegral Y]
    (x : X) (hx : f x = genericPoint Y) :
    ∃ V : X.Opens, x ∈ V ∧ IsAffineOpen V ∧ Flat (V.ι ≫ f) := by
  obtain ⟨U, hU, hηU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint Y ∈ (⊤ : Y.Opens) from trivial)
  have : Nonempty U := ⟨⟨genericPoint Y, hηU⟩⟩
  have hxU : x ∈ f ⁻¹ᵁ U := by
    change f x ∈ U
    rw [hx]
    exact hηU
  obtain ⟨W, hW, hxW, e⟩ := exists_isAffineOpen_mem_and_subset hxU
  obtain ⟨a, ha, hflat⟩ := f.exists_flat_resLE_basicOpen hU hW e
    (f.finiteType_appLE hU hW e)
  have hD : (Y.basicOpen a : Set Y).Nonempty :=
    (hU.basicOpen_nonempty_iff a).mpr (by simpa only [isNilpotent_iff_eq_zero] using ha)
  have hηD : genericPoint Y ∈ Y.basicOpen a := by
    apply ((genericPoint_spec Y).mem_open_set_iff (Y.basicOpen a).isOpen).mpr
    simpa only [Set.univ_inter] using hD
  have hVeq : X.basicOpen (f.appLE U W e a) = W ⊓ f ⁻¹ᵁ (Y.basicOpen a) := by
    exact Scheme.basicOpen_appLE f W U e a
  refine ⟨W ⊓ f ⁻¹ᵁ (Y.basicOpen a), ?_, ?_, ?_⟩
  · refine ⟨hxW, ?_⟩
    change f x ∈ Y.basicOpen a
    rw [hx]
    exact hηD
  · rw [← hVeq]
    exact hW.basicOpen (f.appLE U W e a)
  · have : Flat (f.resLE (Y.basicOpen a)
        (W ⊓ f ⁻¹ᵁ (Y.basicOpen a)) inf_le_right) := hflat
    have hcomp : Flat (f.resLE (Y.basicOpen a)
        (W ⊓ f ⁻¹ᵁ (Y.basicOpen a)) inf_le_right ≫ (Y.basicOpen a).ι) := inferInstance
    simpa only [Scheme.Hom.resLE_comp_ι] using hcomp

/-- A surjective locally finite type morphism to an integral scheme is flat on a nonempty
affine open of its source, without a quasi-compactness assumption.

For background on generic flatness, see J. S. Milne, *Algebraic Groups* (2017).
The proof uses Mathlib and the multivariate-polynomials generic-freeness API. -/
theorem Scheme.Hom.exists_nonempty_isAffineOpen_flat
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Surjective f] [IsIntegral Y] :
    ∃ V : X.Opens,
      (V : Set X).Nonempty ∧ IsAffineOpen V ∧ Flat (V.ι ≫ f) := by
  obtain ⟨x, hx⟩ := f.surjective (genericPoint Y)
  obtain ⟨V, hxV, hV, hflat⟩ :=
    f.exists_isAffineOpen_mem_flat_of_map_eq_genericPoint x hx
  exact ⟨V, ⟨x, hxV⟩, hV, hflat⟩

end AlgebraicGeometry
