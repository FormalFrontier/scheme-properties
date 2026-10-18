/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.RingTheory.KrullDimension.QuasiFinite
import SchemeProperties.QuasiFiniteKrullDimension
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Polynomial.Basic

/-!
# The closed origin of the affine line

Evaluation at zero `ℚ[X] →+* ℚ` is finite and quasi-finite, but not flat. Its
spectrum map is a finite closed immersion. The ring and scheme dimension bounds
apply to these specified maps; independently, their source and target dimensions
are zero and one. Contraction strictness is also applied to evaluation, whose
prime-spectrum source is a singleton: this does not exhibit a nontrivial chain
or assert global injectivity for arbitrary quasi-finite maps.

In the opposite direction, the coefficient inclusion and affine-line projection
are not quasi-finite and locally quasi-finite, respectively. The zero-ring
identity supplies the bottom-dimension boundary. All declarations are private.

## References

Mathlib supplies polynomial evaluation, the finite and closed-immersion spectrum
dictionaries, flat-module torsion-freeness, transcendence of `X`, and the field
and principal-ideal-domain dimension calculations. Its spectrum order isomorphism
and invariance of dimension under order duality compare ring and scheme dimensions.
-/

open AlgebraicGeometry CategoryTheory
open scoped Polynomial

noncomputable section

namespace SchemePropertiesTest.QuasiFiniteKrullDimension

private def evalZero : ℚ[X] →+* ℚ := Polynomial.evalRingHom 0

-- This is the evaluation action of ℚ[X], not the scalar action of ℚ on itself.
private instance evalAlgebra : Algebra ℚ[X] ℚ := evalZero.toAlgebra

private theorem evalZero_surjective : Function.Surjective evalZero :=
  Polynomial.eval_surjective 0

private theorem evalZero_finite : evalZero.Finite :=
  RingHom.Finite.of_surjective evalZero evalZero_surjective

private theorem evalZero_moduleFinite : Module.Finite ℚ[X] ℚ :=
  evalZero_finite

private theorem evalZero_algebraQuasiFinite : Algebra.QuasiFinite ℚ[X] ℚ := by
  letI : Module.Finite ℚ[X] ℚ := evalZero_moduleFinite
  infer_instance

private theorem evalZero_quasiFinite : evalZero.QuasiFinite :=
  evalZero_algebraQuasiFinite

private theorem evalZero_not_flat : ¬ evalZero.Flat := by
  intro h
  letI : Module.Flat ℚ[X] ℚ := h
  have hinj : Function.Injective evalZero :=
    FaithfulSMul.algebraMap_injective ℚ[X] ℚ
  exact Polynomial.X_ne_zero (hinj (by simp [evalZero]))

private theorem evalZero_strictMono_comap : StrictMono (PrimeSpectrum.comap evalZero) :=
  RingHom.QuasiFinite.strictMono_comap evalZero_quasiFinite

private theorem evalZero_dimension_bound : ringKrullDim ℚ ≤ ringKrullDim ℚ[X] :=
  RingHom.QuasiFinite.ringKrullDim_le evalZero_quasiFinite

private theorem rational_dimension : ringKrullDim ℚ = 0 :=
  ringKrullDim_eq_zero_of_field ℚ

private theorem polynomial_dimension : ringKrullDim ℚ[X] = 1 :=
  IsPrincipalIdealRing.ringKrullDim_eq_one ℚ[X] (Polynomial.not_isField ℚ)

-- These values use only stock field and PID results, not the new upper bound.
private theorem evalZero_dimension_drop : ringKrullDim ℚ < ringKrullDim ℚ[X] := by
  rw [rational_dimension, polynomial_dimension]
  exact zero_lt_one

private def closedOrigin : Spec (.of ℚ) ⟶ Spec (.of ℚ[X]) :=
  Spec.map (CommRingCat.ofHom evalZero)

private theorem closedOrigin_closedImmersion : IsClosedImmersion closedOrigin :=
  IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom evalZero) evalZero_surjective

private theorem closedOrigin_finite : IsFinite closedOrigin :=
  (IsFinite.SpecMap_iff (CommRingCat.ofHom evalZero)).mpr evalZero_finite

private theorem closedOrigin_locallyQuasiFinite : LocallyQuasiFinite closedOrigin := by
  letI : IsFinite closedOrigin := closedOrigin_finite
  infer_instance

private theorem closedOrigin_dimension_bound :
    Order.krullDim (Spec (.of ℚ)) ≤ Order.krullDim (Spec (.of ℚ[X])) := by
  letI : LocallyQuasiFinite closedOrigin := closedOrigin_locallyQuasiFinite
  exact AlgebraicGeometry.LocallyQuasiFinite.krullDim_le closedOrigin

private theorem rationalSpectrum_dimension : Order.krullDim (Spec (.of ℚ)) = 0 := by
  rw [Order.krullDim_eq_of_orderIso (specOrderIsoPrimeSpectrum (.of ℚ)),
    Order.krullDim_orderDual]
  exact rational_dimension

private theorem affineLine_dimension : Order.krullDim (Spec (.of ℚ[X])) = 1 := by
  rw [Order.krullDim_eq_of_orderIso (specOrderIsoPrimeSpectrum (.of ℚ[X])),
    Order.krullDim_orderDual]
  exact polynomial_dimension

private theorem closedOrigin_dimension_drop :
    Order.krullDim (Spec (.of ℚ)) < Order.krullDim (Spec (.of ℚ[X])) := by
  rw [rationalSpectrum_dimension, affineLine_dimension]
  exact zero_lt_one

private def coefficientInclusion : ℚ →+* ℚ[X] := algebraMap ℚ ℚ[X]

private theorem coefficientInclusion_not_quasiFinite : ¬ coefficientInclusion.QuasiFinite := by
  intro h
  haveI : Algebra.QuasiFinite ℚ ℚ[X] := RingHom.quasiFinite_algebraMap.mp h
  haveI : Module.Finite ℚ ℚ[X] := Module.Finite.of_quasiFinite
  exact Polynomial.transcendental_X ℚ (Algebra.IsIntegral.isIntegral Polynomial.X).isAlgebraic

private def affineLineProjection : Spec (.of ℚ[X]) ⟶ Spec (.of ℚ) :=
  Spec.map (CommRingCat.ofHom coefficientInclusion)

private theorem affineLineProjection_not_locallyQuasiFinite :
    ¬ LocallyQuasiFinite affineLineProjection := by
  intro h
  exact coefficientInclusion_not_quasiFinite
    ((HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).mp h)

private def zeroIdentity : ZMod 1 →+* ZMod 1 := RingHom.id _

private theorem zeroIdentity_bottom_boundary :
    ringKrullDim (ZMod 1) = ⊥ ∧ ringKrullDim (ZMod 1) ≤ ringKrullDim (ZMod 1) := by
  refine ⟨ringKrullDim_eq_bot_of_subsingleton, ?_⟩
  exact RingHom.QuasiFinite.ringKrullDim_le
    (RingHom.QuasiFinite.of_finite (RingHom.Finite.id (ZMod 1)) : zeroIdentity.QuasiFinite)

end SchemePropertiesTest.QuasiFiniteKrullDimension
