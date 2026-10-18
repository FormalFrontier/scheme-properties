/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Authors: Andrew Yang, Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Sections over a field and equality on closed points

Two sections `f g : Spec ↧K ⟶ Y` of a specified morphism `i : Y ⟶ Spec ↧K`
are equal if they have the same image of the closed point and satisfy both
`f ≫ i = 𝟙 _` and `g ≫ i = 𝟙 _`. This holds for any field `K` and any scheme `Y`:
the field need not be algebraically closed, and the target need not be locally of
finite type, separated, reduced, or affine. The two section identities are essential:
a field-valued point records a residue-field embedding as well as an image point.
The conclusion is equality of scheme morphisms, not only of their image points.

For an algebraically closed field `K`, let `f g : X ⟶ Y` and `i : Y ⟶ Spec ↧K`.
Assume `i` is separated, `X` is reduced, the source structural map `f ≫ i` is locally
of finite type, and `f ≫ i = g ≫ i`. If `S : Set X` is dense and locally closed,
then agreement of `f` and `g` at the closed points lying in `S` implies `f = g`.
No locally finite type assumption on the target structural map `i` is needed.

These results generalize Mathlib's `AlgebraicGeometry.ext_of_apply_closedPoint_eq`
and `AlgebraicGeometry.ext_of_apply_eq`. The proof uses the residue-field classification
`Scheme.SpecToEquivOfField` and Mathlib's dense residue-field-point criterion.
The residue-field, algebraically closed point, and affine-space interfaces are due
to the Mathlib contributors, especially Andrew Yang.

## References

- Andrew Yang and the Mathlib contributors,
  [Schemes over algebraically closed fields](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/AlgebraicGeometry/AlgClosed/Basic.lean):
  closed-point sections, residue-field isomorphisms and dense closed-point criteria.
- Andrew Yang and the Mathlib contributors,
  [Residue fields of points](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/AlgebraicGeometry/ResidueField.lean):
  the classification of field-valued points and the canonical residue-field maps.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- Two sections over a field with the same image of the closed point are equal.
Both composites with the specified structural morphism must be identities. -/
theorem ext_of_apply_closedPoint_eq_of_comp_eq_id
    {K : Type u} [Field K] {Y : Scheme.{u}}
    {f g : Spec ↧K ⟶ Y} (i : Y ⟶ Spec ↧K)
    (hf : f ≫ i = 𝟙 _) (hg : g ≫ i = 𝟙 _)
    (H : f (IsLocalRing.closedPoint K) = g (IsLocalRing.closedPoint K)) : f = g := by
  let x : Y := f (IsLocalRing.closedPoint K)
  let a : Y.residueField x ⟶ ↧K :=
    Y.descResidueField (Scheme.stalkClosedPointTo f)
  let b : Y.residueField x ⟶ ↧K :=
    (Y.residueFieldCongr H).hom ≫ Y.descResidueField (Scheme.stalkClosedPointTo g)
  let c : ↧K ⟶ Y.residueField x :=
    Spec.preimage (Y.fromSpecResidueField x ≫ i)
  have haSpec : Spec.map a ≫ (Y.fromSpecResidueField x ≫ i) = 𝟙 _ := by
    rw [← Category.assoc]
    change (Spec.map (Y.descResidueField (Scheme.stalkClosedPointTo f)) ≫
      Y.fromSpecResidueField (f (IsLocalRing.closedPoint K))) ≫ i = 𝟙 _
    rw [Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField, hf]
  have hbSpec : Spec.map b ≫ (Y.fromSpecResidueField x ≫ i) = 𝟙 _ := by
    calc
      Spec.map b ≫ (Y.fromSpecResidueField x ≫ i) =
          Spec.map (Y.descResidueField (Scheme.stalkClosedPointTo g)) ≫
            (Y.fromSpecResidueField (g (IsLocalRing.closedPoint K)) ≫ i) := by
              dsimp only [b]
              rw [Spec.map_comp, Category.assoc,
                Scheme.residueFieldCongr_fromSpecResidueField_assoc]
      _ = g ≫ i := by
        rw [← Category.assoc,
          Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField]
      _ = 𝟙 _ := hg
  have ha : c ≫ a = 𝟙 _ := by
    apply Spec.map_injective
    simpa only [Spec.map_comp, Spec.map_id, c, Spec.map_preimage] using haSpec
  have hb : c ≫ b = 𝟙 _ := by
    apply Spec.map_injective
    simpa only [Spec.map_comp, Spec.map_id, c, Spec.map_preimage] using hbSpec
  have hac : a ≫ c = 𝟙 _ := by
    ext z
    apply a.hom.injective
    simpa only [CommRingCat.comp_apply, CommRingCat.id_apply, CommRingCat.hom_comp,
      CommRingCat.hom_id, RingHom.comp_apply, RingHom.id_apply] using
      congrArg (fun e : CommRingCat.of K ⟶ CommRingCat.of K => e.hom (a.hom z)) ha
  apply (Scheme.SpecToEquivOfField K Y).injective
  apply Scheme.SpecToEquivOfField_eq_iff.mpr
  refine ⟨H, ?_⟩
  change a = b
  calc
    a = a ≫ (c ≫ b) := by rw [hb, Category.comp_id]
    _ = (a ≫ c) ≫ b := (Category.assoc _ _ _).symm
    _ = b := by rw [hac, Category.id_comp]

set_option backward.isDefEq.respectTransparency.types false in
/-- Morphisms from a reduced scheme locally of finite type over an algebraically
closed field into a separated scheme are determined by their values at the closed
points of a dense locally closed subset. No finite-type assumption on the target
structural morphism is needed. -/
theorem ext_of_apply_eq_on_dense_closedPoints
    {X Y : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
    {f g : X ⟶ Y} (i : Y ⟶ Spec ↧K) [IsSeparated i]
    [IsReduced X] [LocallyOfFiniteType (f ≫ i)]
    (S : Set X) (hS : IsLocallyClosed S) (hS' : Dense S)
    (H : ∀ x ∈ S, IsClosed {x} → f x = g x)
    (H' : f ≫ i = g ≫ i) : f = g := by
  have : JacobsonSpace ↥X := LocallyOfFiniteType.jacobsonSpace (f ≫ i)
  refine AlgebraicGeometry.ext_of_fromSpecResidueField_eq f g i
    (S ∩ closedPoints X) ?_ ?_ H'
  · rwa [dense_iff_closure_eq, JacobsonSpace.closure_inter_closedPoints_eq_closure hS,
      ← dense_iff_closure_eq]
  · intro x ⟨hxS, hx⟩
    rw [← cancel_epi (Spec.map (residueFieldIsoBase (f ≫ i) x hx).hom)]
    refine ext_of_apply_closedPoint_eq_of_comp_eq_id i ?_ ?_
      (by simpa using H x hxS hx) <;>
      simp only [Category.assoc, ← SpecMap_residueFieldIsoBase_inv (f ≫ i) x hx,
        ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, ← H']

end AlgebraicGeometry.Scheme.Hom
