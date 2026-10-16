/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.KrullDimension.Field
public import SchemeProperties.Normal

/-!
# Fields and valuation stalks in codimension at most one

A Noetherian integrally closed domain stalk at a point of coheight at most one is a
valuation ring. The assumptions are point-local: on a normal locally Noetherian
scheme they follow from the existing normality and Noetherian-stalk instances.
No irreducibility or connectedness of the scheme is required.

The coheight bound controls the prime ideals of the stalk. Noetherianity and
integral closedness then give the valuation-ring property by Mathlib's local-domain
characterizations. Under these assumptions, coheight zero characterizes field
stalks and coheight one characterizes discrete valuation stalks. In particular,
the coheight-at-most-one conclusion includes fields, which are not discrete
valuation rings. The field characterization itself needs only reducedness of
the stalk, not Noetherianity, normality or a domain assumption.

## References

The proofs reuse Mathlib's `ringKrullDim_stalk_eq_coheight`,
`krullDimLE_of_coheight_le`, `Ring.KrullDimLE.isField_of_isReduced`, and
`Ideal.IsPrime.isMaximal_of_ne_bot`, together with the valuation-ring and discrete
valuation ring characterizations in `Mathlib.RingTheory.DiscreteValuationRing.TFAE`.
The geometric normality inputs are the stalk classes of `SchemeProperties.Normal`.
-/

public section

universe u

namespace AlgebraicGeometry

/-- A Noetherian integrally closed domain stalk at a point of coheight at most one
is a valuation ring. In particular, this applies to normal locally Noetherian
schemes, including disconnected schemes and coheight-zero points. -/
theorem valuationRing_stalk_of_coheight_le_one {X : Scheme.{u}} (x : X)
    [_root_.IsDomain (X.presheaf.stalk x)]
    [_root_.IsIntegrallyClosed (X.presheaf.stalk x)]
    [IsNoetherianRing (X.presheaf.stalk x)] (hx : Order.coheight x ≤ 1) :
    ValuationRing (X.presheaf.stalk x) := by
  letI : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx
  apply ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
    (X.presheaf.stalk x)).out 4 2).mp
  refine ⟨inferInstance, fun P hP hPprime ↦ ?_⟩
  exact IsLocalRing.eq_maximalIdeal (hPprime.isMaximal_of_ne_bot hP)

/-- A reduced stalk is a field exactly when its point has coheight zero.
Only reducedness of this stalk is needed; the scheme need not be reduced. -/
theorem isField_stalk_iff_coheight_eq_zero {X : Scheme.{u}} (x : X)
    [_root_.IsReduced (X.presheaf.stalk x)] :
    IsField (X.presheaf.stalk x) ↔ Order.coheight x = 0 := by
  constructor
  · intro h
    have hd := ringKrullDim_eq_zero_of_isField h
    rw [ringKrullDim_stalk_eq_coheight x] at hd
    exact_mod_cast hd
  · intro hx
    let : Ring.KrullDimLE 0 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    exact Ring.KrullDimLE.isField_of_isReduced

/-- A Noetherian integrally closed domain stalk is a discrete valuation ring
exactly when its point has coheight one. Coheight zero is the field case instead. -/
theorem isDiscreteValuationRing_stalk_iff_coheight_eq_one {X : Scheme.{u}} (x : X)
    [_root_.IsDomain (X.presheaf.stalk x)]
    [_root_.IsIntegrallyClosed (X.presheaf.stalk x)]
    [IsNoetherianRing (X.presheaf.stalk x)] :
    IsDiscreteValuationRing (X.presheaf.stalk x) ↔ Order.coheight x = 1 := by
  constructor
  · intro h
    let := h
    have hd := IsDiscreteValuationRing.ringKrullDim_eq_one (X.presheaf.stalk x)
    rw [ringKrullDim_stalk_eq_coheight x] at hd
    exact_mod_cast hd
  · intro hx
    have hvaluation := valuationRing_stalk_of_coheight_le_one x hx.le
    have hnotfield : ¬ IsField (X.presheaf.stalk x) := by
      intro h
      have hz := (isField_stalk_iff_coheight_eq_zero x).mp h
      simp [hx] at hz
    exact ((IsDiscreteValuationRing.TFAE (X.presheaf.stalk x) hnotfield).out 1 2 rfl rfl).mpr
      hvaluation

end AlgebraicGeometry
