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

Two sections of the same morphism over a reduced scheme are already determined
by their entire underlying point maps. The section identities force their residue-field
maps to be inverses of the same transported structural map, so the criterion above applies.

## References

* Mathlib, `AlgebraicGeometry.ext_of_fromSpecResidueField_eq`, for the
  dense-residue-point criterion with a separated relative target.
* Mathlib, `AlgebraicGeometry.Scheme.hom_ext_of_forall`, for equality of morphisms
  checked on open neighborhoods.
* Mathlib, `AlgebraicGeometry.Scheme.Hom.residueFieldMap_congr'` and
  `AlgebraicGeometry.Scheme.residueFieldCongr_fromSpecResidueField`, for canonical
  point transports and the corresponding residue-field points.
* Formal Frontier Agents, for the section criterion via residue-field inverses
  and canonical point transports.
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

/-- Two sections of a morphism over a reduced scheme
are equal if their entire underlying point maps agree. The target is arbitrary,
and the source may be empty. Reducedness and both section equations are essential. -/
theorem ext_of_apply_eq_of_comp_eq_id
    {X Y : Scheme.{u}} [AlgebraicGeometry.IsReduced X]
    (i : Y ⟶ X) {s t : X ⟶ Y}
    (hs : s ≫ i = 𝟙 X) (ht : t ≫ i = 𝟙 X)
    (h : ∀ x : X, s x = t x) :
    s = t := by
  apply ext_of_fromSpecResidueField
  intro x
  have hid : (𝟙 X : X ⟶ X) x = x := by
    rw [Scheme.Hom.id_base, TopCat.id_app]
  have hsx : i (s x) = x :=
    (Scheme.Hom.comp_apply s i x).symm.trans
      ((congrArg (fun f : X ⟶ X => f x) hs).trans hid)
  have htx : i (t x) = x :=
    (Scheme.Hom.comp_apply t i x).symm.trans
      ((congrArg (fun f : X ⟶ X => f x) ht).trans hid)
  -- Keep both point-normalization paths before comparing the section transports.
  have hsection (r : X ⟶ Y) (hr : r ≫ i = 𝟙 X) (e : i (r x) = x) :
      ((X.residueFieldCongr e).inv ≫ i.residueFieldMap (r x)) ≫
        r.residueFieldMap x = 𝟙 (X.residueField x) := by
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecResidueField x)).1
    calc
      Spec.map (((X.residueFieldCongr e).inv ≫ i.residueFieldMap (r x)) ≫
          r.residueFieldMap x) ≫ X.fromSpecResidueField x =
          Spec.map (r.residueFieldMap x) ≫
            Spec.map (i.residueFieldMap (r x)) ≫
              Spec.map (X.residueFieldCongr e).inv ≫
                X.fromSpecResidueField x := by
        simp only [Spec.map_comp, Category.assoc]
      _ = Spec.map (r.residueFieldMap x) ≫
          Spec.map (i.residueFieldMap (r x)) ≫
            X.fromSpecResidueField (i (r x)) := by
        rw [Scheme.residueFieldCongr_inv,
          Scheme.residueFieldCongr_fromSpecResidueField]
      _ = Spec.map (r.residueFieldMap x) ≫
          (Y.fromSpecResidueField (r x) ≫ i) := by
        rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
      _ = X.fromSpecResidueField x ≫ (r ≫ i) := by
        rw [← Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
          Category.assoc]
      _ = Spec.map (𝟙 (X.residueField x)) ≫ X.fromSpecResidueField x := by
        rw [hr, Spec.map_id, Category.comp_id, Category.id_comp]
  let a : X.residueField x ⟶ Y.residueField (s x) :=
    (X.residueFieldCongr hsx).inv ≫ i.residueFieldMap (s x)
  have ha : a ≫ s.residueFieldMap x = 𝟙 (X.residueField x) := hsection s hs hsx
  -- A homomorphism from a field is injective, so the other inverse identity follows.
  let : Mono (s.residueFieldMap x) :=
    ConcreteCategory.mono_of_injective _ (s.residueFieldMap x).hom.injective
  have hsa : s.residueFieldMap x ≫ a = 𝟙 (Y.residueField (s x)) := by
    apply (cancel_mono (s.residueFieldMap x)).1
    simp only [Category.assoc, ha, Category.comp_id, Category.id_comp]
  let : Epi a := epi_of_epi_fac hsa
  -- Canonical equality transports compose; their equality proofs are irrelevant.
  have htransport :
      (X.residueFieldCongr hsx).inv ≫
          (X.residueFieldCongr (congrArg i (h x))).hom =
        (X.residueFieldCongr htx).inv := by
    simp only [Scheme.residueFieldCongr_inv, Scheme.residueFieldCongr_trans_hom]
  have hat : a ≫ (Y.residueFieldCongr (h x)).hom =
      (X.residueFieldCongr htx).inv ≫ i.residueFieldMap (t x) := by
    dsimp only [a]
    rw [Category.assoc, residueFieldMap_congr' (f := i) (h x),
      ← Category.assoc, htransport]
  have hκ : s.residueFieldMap x =
      (Y.residueFieldCongr (h x)).hom ≫ t.residueFieldMap x := by
    apply (cancel_epi a).1
    rw [ha, ← Category.assoc, hat]
    exact (hsection t ht htx).symm
  calc
    X.fromSpecResidueField x ≫ s =
        Spec.map (s.residueFieldMap x) ≫ Y.fromSpecResidueField (s x) :=
      (s.SpecMap_residueFieldMap_fromSpecResidueField x).symm
    _ = Spec.map (t.residueFieldMap x) ≫
        Spec.map (Y.residueFieldCongr (h x)).hom ≫
          Y.fromSpecResidueField (s x) := by
      rw [hκ, Spec.map_comp, Category.assoc]
    _ = X.fromSpecResidueField x ≫ t := by
      rw [Scheme.residueFieldCongr_fromSpecResidueField,
        Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]

end AlgebraicGeometry.Scheme.Hom
