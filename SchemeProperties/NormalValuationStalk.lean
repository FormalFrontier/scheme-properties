/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import SchemeProperties.Normal

/-!
# Valuation stalks in codimension at most one

A Noetherian integrally closed domain stalk at a point of coheight at most one is a
valuation ring. The assumptions are point-local: on a normal locally Noetherian
scheme they follow from the existing normality and Noetherian-stalk instances.
No irreducibility or connectedness of the scheme is required.

The coheight bound controls the prime ideals of the stalk. Noetherianity and
integral closedness then give the valuation-ring property by Mathlib's local-domain
characterizations. The conclusion includes the coheight-zero field case; it does
not assert that the stalk is a discrete valuation ring.

## References

The proof reuses Mathlib's `krullDimLE_of_coheight_le`,
`Ideal.IsPrime.isMaximal_of_ne_bot`, and the field-compatible
`tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain` from
`Mathlib.RingTheory.DiscreteValuationRing.TFAE`. The geometric normality inputs
are the stalk classes of `SchemeProperties.Normal`.
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

end AlgebraicGeometry
