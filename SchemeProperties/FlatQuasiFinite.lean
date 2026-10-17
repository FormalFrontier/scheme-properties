/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.RingTheory.KrullDimension.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Full stalk dimension under flat quasi-finite maps

Pointwise flatness and quasi-finiteness preserve the Krull dimension of the full
scheme stalks. The statement does not require global flatness or local
quasi-finiteness of the morphism.

## References

* Mathlib's local stalk-map, flatness and pointwise quasi-finiteness APIs.
* The local-ring dimension theorem in
  `SchemeProperties.RingTheory.KrullDimension.QuasiFinite`, using Mathlib's
  order-height and going-down APIs.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Pointwise flatness and quasi-finiteness
of the stalk map preserve full stalk dimension, for schemes in any universe.
For `[Flat f] [LocallyQuasiFinite f]`, the stock inputs are `Flat.stalkMap f x` and
`f.quasiFiniteAt x`; no finiteness or integrality of this localized map is asserted. -/
theorem ringKrullDim_stalk_eq_of_flat_of_quasiFiniteAt
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (hf : (f.stalkMap x).hom.Flat) (hq : f.QuasiFiniteAt x) :
    ringKrullDim (X.presheaf.stalk x) =
      ringKrullDim (Y.presheaf.stalk (f x)) := by
  exact RingHom.Flat.ringKrullDim_eq_of_quasiFinite (f.stalkMap x).hom hf hq

end AlgebraicGeometry.Scheme.Hom
