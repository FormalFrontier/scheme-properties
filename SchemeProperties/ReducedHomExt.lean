/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Morphisms from reduced schemes and residue-field points

Morphisms from a reduced scheme are determined by their composites with the canonical
maps from the spectra of its residue fields. Equivalently, they are determined by
all field-valued points. The target scheme need not be separated, and neither source
nor target needs to be of finite type or Noetherian. Empty sources are allowed.

The tests concern morphisms from field spectra, not just the underlying maps of
points. Frobenius on the affine line over a prime field fixes its prime spectrum and
its prime-field-valued points, but is not the identity morphism. Reducedness is also
substantive: field-valued points of the dual numbers cannot detect their nilpotents.

## References

* Mathlib, `AlgebraicGeometry.ext_of_fromSpecResidueField_eq`, for the
  dense-residue-point criterion with a separated relative target.
* Mathlib, `AlgebraicGeometry.Scheme.hom_ext_of_forall`, for equality of morphisms
  checked on open neighborhoods.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Morphisms from a reduced scheme are equal if they agree after every canonical
residue-field point. No separatedness hypothesis on the target is required. -/
theorem ext_of_fromSpecResidueField
    {X Y : Scheme.{u}} [IsReduced X] {f g : X ⟶ Y}
    (h : ∀ x : X, X.fromSpecResidueField x ≫ f = X.fromSpecResidueField x ≫ g) :
    f = g := by
  have hpoint (x : X) : f x = g x := by
    simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using
      congrArg (fun k : Spec (X.residueField x) ⟶ Y => k default) (h x)
  apply Scheme.hom_ext_of_forall f g
  intro x
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f x ∈ (⊤ : Y.Opens) from trivial)
  let U : X.Opens := (f ⁻¹ᵁ V) ⊓ (g ⁻¹ᵁ V)
  have hxU : x ∈ U := ⟨hxV, by
    change g x ∈ V
    rw [← hpoint x]
    exact hxV⟩
  let : IsAffine V := hV
  have hf : U ≤ f ⁻¹ᵁ V := inf_le_left
  have hg : U ≤ g ⁻¹ᵁ V := inf_le_right
  let fU : U.toScheme ⟶ V.toScheme := f.resLE V U hf
  let gU : U.toScheme ⟶ V.toScheme := g.resLE V U hg
  have hres (z : U.toScheme) :
      U.toScheme.fromSpecResidueField z ≫ fU =
        U.toScheme.fromSpecResidueField z ≫ gU := by
    apply (cancel_mono V.ι).1
    simpa only [Category.assoc, fU, gU, resLE_comp_ι,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc] using
      congrArg (fun k => Spec.map ((U.ι).residueFieldMap z) ≫ k) (h (U.ι z))
  have hfg : fU = gU := by
    apply AlgebraicGeometry.ext_of_fromSpecResidueField_eq fU gU
      (CategoryTheory.Limits.terminal.from V.toScheme) Set.univ dense_univ
    · intro z _
      exact hres z
    · exact CategoryTheory.Limits.terminal.hom_ext _ _
  refine ⟨U, hxU, ?_⟩
  simpa only [fU, gU, resLE_comp_ι] using
    congrArg (fun k : U.toScheme ⟶ V.toScheme => k ≫ V.ι) hfg

/-- Morphisms from a reduced scheme are determined by all field-valued points in
the common scheme universe. The target is arbitrary. -/
theorem ext_of_field_valued_points
    {X Y : Scheme.{u}} [IsReduced X] {f g : X ⟶ Y}
    (h : ∀ (K : Type u) [Field K] (p : Spec (.of K) ⟶ X), p ≫ f = p ≫ g) :
    f = g := by
  apply ext_of_fromSpecResidueField
  intro x
  exact h (X.residueField x) (X.fromSpecResidueField x)

end AlgebraicGeometry.Scheme.Hom
