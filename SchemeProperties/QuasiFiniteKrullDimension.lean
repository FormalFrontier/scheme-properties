/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.Order.KrullDimension

/-!
# Krull dimension under locally quasi-finite morphisms

A locally quasi-finite morphism does not increase the Krull dimension of the
underlying schemes, with their specialization orders. Here locally quasi-finite
has Mathlib's residue-field-fiber meaning: affine ring maps have finite-dimensional
fibers over residue fields. Neither local finite type nor quasi-compactness is
required.

## References

* Mathlib's locally quasi-finite discrete-fiber API and specialization order on schemes.
* Mathlib's `IsDiscrete.eq_of_specializes` and `Order.krullDim_le_of_strictMono`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyQuasiFinite

/-- A locally quasi-finite morphism does not increase the Krull dimension of the
underlying schemes. No flatness, local finite type or quasi-compactness is required. -/
theorem krullDim_le {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] :
    Order.krullDim X ≤ Order.krullDim Y := by
  apply Order.krullDim_le_of_strictMono f
  intro x y hxy
  have hspec : y ⤳ x := Scheme.le_iff_specializes.mp hxy.le
  have hmap : f y ⤳ f x := hspec.map f.continuous
  refine lt_iff_le_not_ge.mpr ⟨Scheme.le_iff_specializes.mpr hmap, ?_⟩
  intro hyx
  have heq : f y = f x :=
    (hmap.antisymm (Scheme.le_iff_specializes.mp hyx)).eq
  have hyx' : y = x :=
    (f.isDiscrete_preimage_singleton (f x)).eq_of_specializes hspec heq rfl
  exact hxy.ne hyx'.symm

end AlgebraicGeometry.LocallyQuasiFinite
