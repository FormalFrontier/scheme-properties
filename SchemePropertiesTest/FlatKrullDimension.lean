/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.FlatKrullDimension
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The affine line and global dimension bounds

The canonical inclusion `ℚ → ℚ[X]` and projection `Spec ℚ[X] → Spec ℚ`
exercise the generalizing-surjection, faithfully flat and scheme bounds.
Faithful flatness comes from the stock nontrivial free polynomial module.
Independently computed dimensions are zero and one, so the bounds are strict.

The canonical fraction-ring map `ℚ[X] → FractionRing (ℚ[X])` is flat but not
faithfully flat: its unit image of `X` cannot be reflected to `ℚ[X]`, as
shown by evaluation at zero. Its spectrum map is not surjective, and its
source and target rings have dimensions one and zero. The identity of the
zero ring supplies the dimension-`⊥` boundary.

All data and declarations are private. Mathlib supplies the free-module,
localization, unit-reflection and spectrum dictionaries, and the dimension
computations; none of the hypotheses or dimension values is assumed.
-/

open AlgebraicGeometry CategoryTheory
open scoped Polynomial

noncomputable section

namespace SchemePropertiesTest.FlatKrullDimension

private def coefficientMap : ℚ →+* ℚ[X] := algebraMap ℚ ℚ[X]

private def affineLineProjection : Spec (.of ℚ[X]) ⟶ Spec (.of ℚ) :=
  Spec.map (CommRingCat.ofHom coefficientMap)

private theorem polynomial_free : Module.Free ℚ ℚ[X] := inferInstance

private theorem polynomial_faithfullyFlat : Module.FaithfullyFlat ℚ ℚ[X] := by
  let : Module.Free ℚ ℚ[X] := polynomial_free
  infer_instance

private theorem coefficientMap_faithfullyFlat : coefficientMap.FaithfullyFlat :=
  RingHom.faithfullyFlat_algebraMap_iff.mpr polynomial_faithfullyFlat

private theorem coefficientMap_flat : coefficientMap.Flat :=
  coefficientMap_faithfullyFlat.flat

private theorem coefficientMap_generalizing : GeneralizingMap (PrimeSpectrum.comap coefficientMap) :=
  coefficientMap_flat.generalizingMap_comap

private theorem coefficientMap_comap_surjective :
    Function.Surjective (PrimeSpectrum.comap coefficientMap) :=
  (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp
    coefficientMap_faithfullyFlat).2

private theorem affineLineProjection_flat_surjective :
    Flat affineLineProjection ∧ Surjective affineLineProjection :=
  (flat_and_surjective_SpecMap_iff _).mpr coefficientMap_faithfullyFlat

-- These three applications use the actual maps above, not abstract hypotheses.
private theorem rational_dimension_bound_via_comap : ringKrullDim ℚ ≤ ringKrullDim ℚ[X] :=
  RingHom.ringKrullDim_le_of_generalizingMap_comap_of_surjective coefficientMap
    coefficientMap_generalizing coefficientMap_comap_surjective

private theorem rational_dimension_bound_via_faithfullyFlat :
    ringKrullDim ℚ ≤ ringKrullDim ℚ[X] :=
  coefficientMap_faithfullyFlat.ringKrullDim_le

private theorem rationalSpectrum_dimension_bound :
    Order.krullDim (Spec (.of ℚ)) ≤ Order.krullDim (Spec (.of ℚ[X])) := by
  let : Flat affineLineProjection := affineLineProjection_flat_surjective.1
  let : Surjective affineLineProjection := affineLineProjection_flat_surjective.2
  exact Flat.krullDim_le_of_surjective affineLineProjection

-- Independent stock computations, without using any of the three bounds.
private theorem rational_dimension : ringKrullDim ℚ = 0 :=
  ringKrullDim_eq_zero_of_field ℚ

private theorem polynomial_dimension : ringKrullDim ℚ[X] = 1 := by
  rw [Polynomial.ringKrullDim_of_isNoetherianRing, rational_dimension, zero_add]

private theorem spectrum_dimension (R : CommRingCat) :
    Order.krullDim (Spec R) = ringKrullDim R :=
  (Order.krullDim_eq_of_orderIso (specOrderIsoPrimeSpectrum R)).trans
    Order.krullDim_orderDual

private theorem rationalSpectrum_dimension : Order.krullDim (Spec (.of ℚ)) = 0 :=
  (spectrum_dimension _).trans rational_dimension

private theorem affineLine_dimension : Order.krullDim (Spec (.of ℚ[X])) = 1 :=
  (spectrum_dimension _).trans polynomial_dimension

private theorem rational_dimension_lt_polynomial : ringKrullDim ℚ < ringKrullDim ℚ[X] := by
  rw [rational_dimension, polynomial_dimension]
  exact WithBot.coe_lt_coe.mpr (show (0 : ℕ∞) < 1 from zero_lt_one)

private theorem rationalSpectrum_dimension_lt_affineLine :
    Order.krullDim (Spec (.of ℚ)) < Order.krullDim (Spec (.of ℚ[X])) := by
  rw [rationalSpectrum_dimension, affineLine_dimension]
  exact WithBot.coe_lt_coe.mpr (show (0 : ℕ∞) < 1 from zero_lt_one)

-- Flatness alone does not give the dimension bound.
private def fractionMap : ℚ[X] →+* FractionRing (ℚ[X]) :=
  algebraMap ℚ[X] (FractionRing (ℚ[X]))

private def fractionMorphism : Spec (.of (FractionRing (ℚ[X]))) ⟶ Spec (.of ℚ[X]) :=
  Spec.map (CommRingCat.ofHom fractionMap)

private theorem fractionMap_flat : fractionMap.Flat :=
  RingHom.flat_algebraMap_iff.mpr
    (IsLocalization.flat (FractionRing (ℚ[X])) (nonZeroDivisors ℚ[X]))

private theorem fractionMorphism_flat : Flat fractionMorphism :=
  Flat.SpecMap_iff.mpr fractionMap_flat

private theorem fractionMap_X_isUnit : IsUnit (fractionMap (Polynomial.X : ℚ[X])) :=
  IsLocalization.map_units (FractionRing (ℚ[X])) (M := nonZeroDivisors ℚ[X])
    ⟨Polynomial.X, mem_nonZeroDivisors_iff_ne_zero.mpr Polynomial.X_ne_zero⟩

private theorem fractionMap_not_faithfullyFlat : ¬ fractionMap.FaithfullyFlat := by
  intro h
  let : Module.FaithfullyFlat ℚ[X] (FractionRing (ℚ[X])) :=
    RingHom.faithfullyFlat_algebraMap_iff.mp h
  have hX : IsUnit (Polynomial.X : ℚ[X]) :=
    (isUnit_map_iff (algebraMap ℚ[X] (FractionRing (ℚ[X]))) Polynomial.X).mp fractionMap_X_isUnit
  have hzero := hX.map (Polynomial.evalRingHom (0 : ℚ))
  simpa using hzero

private theorem fractionMorphism_not_surjective : ¬ Surjective fractionMorphism := by
  intro h
  exact fractionMap_not_faithfullyFlat
    ((flat_and_surjective_SpecMap_iff _).mp ⟨fractionMorphism_flat, h⟩)

private theorem fractionRing_dimension : ringKrullDim (FractionRing (ℚ[X])) = 0 :=
  ringKrullDim_eq_zero_of_field _

private theorem fraction_dimension_drop : ringKrullDim (FractionRing (ℚ[X])) < ringKrullDim ℚ[X] := by
  rw [fractionRing_dimension, polynomial_dimension]
  exact WithBot.coe_lt_coe.mpr (show (0 : ℕ∞) < 1 from zero_lt_one)

private theorem fractionSpectrum_dimension_drop :
    Order.krullDim (Spec (.of (FractionRing (ℚ[X])))) < Order.krullDim (Spec (.of ℚ[X])) := by
  rw [spectrum_dimension, spectrum_dimension]
  exact fraction_dimension_drop

-- One minimal application at the zero-ring/empty-spectrum boundary.
private def zeroMap : ZMod 1 →+* ZMod 1 := RingHom.id _

private def zeroMorphism : Spec (.of (ZMod 1)) ⟶ Spec (.of (ZMod 1)) :=
  Spec.map (CommRingCat.ofHom zeroMap)

private theorem zeroRing_dimension : ringKrullDim (ZMod 1) = ⊥ :=
  ringKrullDim_eq_bot_of_subsingleton

private theorem zeroSpectrum_dimension : Order.krullDim (Spec (.of (ZMod 1))) = ⊥ :=
  (spectrum_dimension _).trans zeroRing_dimension

private theorem zeroMap_faithfullyFlat : zeroMap.FaithfullyFlat :=
  RingHom.FaithfullyFlat.of_bijective ⟨fun _ _ h ↦ h, fun x ↦ ⟨x, rfl⟩⟩

private theorem zeroMorphism_flat_surjective : Flat zeroMorphism ∧ Surjective zeroMorphism :=
  (flat_and_surjective_SpecMap_iff _).mpr zeroMap_faithfullyFlat

private theorem zeroSpectrum_dimension_bound :
    Order.krullDim (Spec (.of (ZMod 1))) ≤ Order.krullDim (Spec (.of (ZMod 1))) := by
  let : Flat zeroMorphism := zeroMorphism_flat_surjective.1
  let : Surjective zeroMorphism := zeroMorphism_flat_surjective.2
  exact Flat.krullDim_le_of_surjective zeroMorphism

end SchemePropertiesTest.FlatKrullDimension
