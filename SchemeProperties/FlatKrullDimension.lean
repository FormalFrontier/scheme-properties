/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.RingTheory.KrullDimension.GeneralizingMap
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Global Krull dimension under flat surjective morphisms

A flat surjective morphism `X → Y` bounds the global Krull dimension of its
target `Y` by that of its source `X`. These are the dimensions of the whole
schemes, not the dimensions of a chosen pair of stalks. No Noetherianity,
quasi-compactness, finite-type or quasi-finiteness hypothesis is required.

Dimensions take values in `WithBot ℕ∞`, including dimension `⊥` for the empty
scheme. In particular, an infinite-dimensional target forces an
infinite-dimensional source.

## References

* Mathlib's `AlgebraicGeometry.Flat.stalkMap` gives flat local stalk maps, which
  are faithfully flat by `Module.FaithfullyFlat.of_flat_of_isLocalHom`.
* `RingHom.FaithfullyFlat.ringKrullDim_le` bounds the dimensions of these full
  local rings.
* Mathlib's `AlgebraicGeometry.ringKrullDim_stalk_eq_coheight` and
  `Order.krullDim_eq_iSup_coheight` express global dimension as the supremum of
  full stalk dimensions, with the coercions inside the supremum.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Flat

/-- A flat surjective morphism bounds the global Krull dimension of the target
by that of the source, in `WithBot ℕ∞`; this is not a stalk-dimension equality. -/
theorem krullDim_le_of_surjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f] :
    Order.krullDim Y ≤ Order.krullDim X := by
  rw [Order.krullDim_eq_iSup_coheight, Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun y ↦ ?_
  obtain ⟨x, rfl⟩ := f.surjective y
  letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  haveI : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    Flat.stalkMap f x
  haveI : IsLocalHom
      (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) := by
    change IsLocalHom (f.stalkMap x).hom
    infer_instance
  have hf : (f.stalkMap x).hom.FaithfullyFlat := by
    change (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)).FaithfullyFlat
    exact RingHom.faithfullyFlat_algebraMap_iff.mpr
      Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hdim := RingHom.FaithfullyFlat.ringKrullDim_le hf
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at hdim
  exact hdim.trans (le_iSup (fun z : X ↦ (Order.coheight z : WithBot ℕ∞)) x)

end AlgebraicGeometry.Flat
