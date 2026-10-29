/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Topology.JacobsonSpace

/-!
# Open sets and closed points of Jacobson spaces

Taking the trace on the existing subspace of closed points gives an order
isomorphism on open sets of a Jacobson space. Its inverse sends an open set
`W` of closed points to the complement of the closure of the image of `Wᶜ`.
This is an order isomorphism of opens, not a homeomorphism of point spaces.

## References

The construction uses Mathlib's `Topology.IsInducing.opensGI` for the
subspace topology and `JacobsonSpace.closure_inter_closedPoints` for
reconstruction from closed points.
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace TopologicalSpace.Opens

variable {X : Type u} [TopologicalSpace X] [JacobsonSpace X]

private theorem closure_image_compl_preimage_closedPoints (U : Opens X) :
    closure ((Subtype.val : closedPoints X → X) ''
      ((Subtype.val : closedPoints X → X) ⁻¹' (U : Set X))ᶜ) = (U : Set X)ᶜ := by
  rw [← Set.preimage_compl, Set.image_preimage_eq_inter_range, Subtype.range_coe]
  exact closure_inter_closedPoints U.isOpen.isClosed_compl

private theorem preimage_closedPoints_injective :
    Function.Injective (fun U : Opens X ↦
      (Subtype.val : closedPoints X → X) ⁻¹' (U : Set X)) := by
  intro U V h
  have hcompl := congrArg
    (fun s : Set (closedPoints X) ↦
      closure ((Subtype.val : closedPoints X → X) '' sᶜ)) h
  rw [closure_image_compl_preimage_closedPoints U,
    closure_image_compl_preimage_closedPoints V] at hcompl
  apply Opens.ext
  simpa only [compl_compl] using congrArg (fun s : Set X ↦ sᶜ) hcompl

/-- Open sets of a Jacobson space correspond, by inverse image along the
subtype inclusion, to open sets of its subspace of closed points. -/
def closedPointsOrderIso (X : Type u) [TopologicalSpace X] [JacobsonSpace X] :
    Opens X ≃o Opens (closedPoints X) := by
  let c : TopCat.of (closedPoints X) ⟶ TopCat.of X :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hc : IsInducing c := IsInducing.subtypeVal
  let e : Opens X ≃ Opens (closedPoints X) :=
    { toFun := (map c).obj
      invFun := hc.functorObj
      left_inv := fun U ↦ by
        apply preimage_closedPoints_injective
        exact congrArg (fun V : Opens (closedPoints X) ↦ (V : Set (closedPoints X)))
          (hc.map_functorObj ((map c).obj U))
      right_inv := hc.map_functorObj }
  exact e.toOrderIso hc.opensGI.gc.monotone_l hc.opensGI.gc.monotone_u

/-- The forward map is the usual inverse-image functor on opens. -/
theorem closedPointsOrderIso_apply (U : Opens X) :
    closedPointsOrderIso X U =
      (map (TopCat.ofHom ⟨(Subtype.val : closedPoints X → X),
        continuous_subtype_val⟩)).obj U := rfl

@[simp]
theorem coe_closedPointsOrderIso_apply (U : Opens X) :
    (closedPointsOrderIso X U : Set (closedPoints X)) =
      (Subtype.val : closedPoints X → X) ⁻¹' (U : Set X) := rfl

@[simp]
theorem mem_closedPointsOrderIso_apply {U : Opens X} {x : closedPoints X} :
    x ∈ closedPointsOrderIso X U ↔ x.val ∈ U := Iff.rfl

/-- Extending an open trace and then taking its trace recovers the open set
of closed points. -/
@[simp]
theorem preimage_closedPointsOrderIso_symm_apply (W : Opens (closedPoints X)) :
    (Subtype.val : closedPoints X → X) ⁻¹'
      ((closedPointsOrderIso X).symm W : Set X) = (W : Set (closedPoints X)) :=
  congrArg (fun V : Opens (closedPoints X) ↦ (V : Set (closedPoints X)))
    ((closedPointsOrderIso X).apply_symm_apply W)

@[simp]
theorem val_mem_closedPointsOrderIso_symm_apply
    {W : Opens (closedPoints X)} {x : closedPoints X} :
    x.val ∈ (closedPointsOrderIso X).symm W ↔ x ∈ W :=
  Set.ext_iff.mp (preimage_closedPointsOrderIso_symm_apply W) x

/-- The extension of an open set of closed points is the complement of the
closure of the image of its complement. -/
theorem coe_closedPointsOrderIso_symm_apply (W : Opens (closedPoints X)) :
    ((closedPointsOrderIso X).symm W : Set X) =
      (closure ((Subtype.val : closedPoints X → X) '' (W : Set (closedPoints X))ᶜ))ᶜ := by
  have hcompl := congrArg
    (fun s : Set (closedPoints X) ↦
      closure ((Subtype.val : closedPoints X → X) '' sᶜ))
    (preimage_closedPointsOrderIso_symm_apply W)
  rw [closure_image_compl_preimage_closedPoints ((closedPointsOrderIso X).symm W)] at hcompl
  simpa only [compl_compl] using congrArg (fun s : Set X ↦ sᶜ) hcompl

/-- Extending the inverse image of an ambient open set recovers that open set. -/
@[simp]
theorem closedPointsOrderIso_symm_map (U : Opens X) :
    (closedPointsOrderIso X).symm
      ((map (TopCat.ofHom ⟨(Subtype.val : closedPoints X → X),
        continuous_subtype_val⟩)).obj U) = U :=
  (closedPointsOrderIso X).symm_apply_apply U

/-- Taking the inverse image of the extension of an open set of closed points
recovers that open set. -/
@[simp]
theorem map_closedPointsOrderIso_symm (W : Opens (closedPoints X)) :
    (map (TopCat.ofHom ⟨(Subtype.val : closedPoints X → X),
      continuous_subtype_val⟩)).obj ((closedPointsOrderIso X).symm W) = W :=
  (closedPointsOrderIso X).apply_symm_apply W

end TopologicalSpace.Opens
