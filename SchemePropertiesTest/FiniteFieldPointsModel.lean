/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.FiniteFieldPoints
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# The affine line over the field with two elements

The fixed morphism is `Spec (Polynomial (ZMod 2)) ⟶ Spec (ZMod 2)`. Evaluation
at zero and one gives two distinct sections, with their over-category
triangles. The stored pair of sections and the independent local-finite-type
and quasi-compactness witness do not use the finiteness theorem.

The public finite-field theorem proves finiteness for this same morphism. The
supporting algebra theorem also applies directly to `Polynomial (ZMod 2)`,
whose underlying set is infinite. Neither application asserts an exact point
count or a Frobenius description.

## References

* Mathlib's polynomial evaluation and affine-spectrum APIs.
* `SchemeProperties.FiniteAlgHom` and `SchemeProperties.FiniteFieldPoints`.
-/

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace SchemePropertiesTest.FiniteFieldPointsModel

/-- The polynomial affine-line projection over the field with two elements. -/
private def affineLineProjection :
    Spec (CommRingCat.of (Polynomial (ZMod 2))) ⟶ Spec (CommRingCat.of (ZMod 2)) :=
  Spec.algebraMap (ZMod 2) (Polynomial (ZMod 2))

private instance affineLineProjection_locallyOfFiniteType :
    LocallyOfFiniteType affineLineProjection := by
  change LocallyOfFiniteType
    (Spec.map (CommRingCat.ofHom (algebraMap (ZMod 2) (Polynomial (ZMod 2)))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

private instance affineLineProjection_quasiCompact :
    QuasiCompact affineLineProjection := by
  infer_instance

/-- Evaluation at a scalar gives a section of the polynomial affine-line projection. -/
private def affineLineEvalPoint (a : ZMod 2) :
    Over.mk (𝟙 (Spec (CommRingCat.of (ZMod 2)))) ⟶ Over.mk affineLineProjection :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))) (by
    change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (ZMod 2) (Polynomial (ZMod 2)))) = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id (CommRingCat.of (ZMod 2))]
    congr 1
    ext x
    simp [CommRingCat.comp_apply, Polynomial.algebraMap_eq])

private def affineLineZeroPoint :
    Over.mk (𝟙 (Spec (CommRingCat.of (ZMod 2)))) ⟶ Over.mk affineLineProjection :=
  affineLineEvalPoint 0

private def affineLineOnePoint :
    Over.mk (𝟙 (Spec (CommRingCat.of (ZMod 2)))) ⟶ Over.mk affineLineProjection :=
  affineLineEvalPoint 1

private theorem affineLineZeroPoint_ne_onePoint : affineLineZeroPoint ≠ affineLineOnePoint := by
  intro h
  have hMaps := congrArg Over.Hom.left h
  change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : ZMod 2))) =
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (1 : ZMod 2))) at hMaps
  have hEval := Spec.map_injective hMaps
  have hX := congrArg
    (fun f : CommRingCat.of (Polynomial (ZMod 2)) ⟶ CommRingCat.of (ZMod 2) =>
      f.hom Polynomial.X) hEval
  exact (zero_ne_one : (0 : ZMod 2) ≠ 1) (by simpa using hX)

/-- Two named points of the fixed polynomial affine line; this is input data,
not a replacement for the over-category morphism type. -/
private structure AffineLineData where
  zeroPoint :
    Over.mk (𝟙 (Spec (CommRingCat.of (ZMod 2)))) ⟶ Over.mk affineLineProjection
  onePoint :
    Over.mk (𝟙 (Spec (CommRingCat.of (ZMod 2)))) ⟶ Over.mk affineLineProjection

private def affineLineData : AffineLineData where
  zeroPoint := affineLineZeroPoint
  onePoint := affineLineOnePoint

/-- The finite-field and finite-type hypotheses hold, and the stored points are distinct.
This witness does not invoke the finiteness theorem. -/
private theorem affineLineModelWitness :
    Finite (ZMod 2) ∧ LocallyOfFiniteType affineLineProjection ∧
      QuasiCompact affineLineProjection ∧ affineLineData.zeroPoint ≠ affineLineData.onePoint := by
  exact ⟨inferInstance, inferInstance, inferInstance, affineLineZeroPoint_ne_onePoint⟩

/-- The affine line over the field with two elements has finitely many rational points. -/
private theorem affineLine_overHom_finite :
    Finite (Over.mk (𝟙 (Spec (CommRingCat.of (ZMod 2)))) ⟶
      Over.mk affineLineProjection) :=
  finite_overHom_of_finiteField affineLineProjection (𝟙 _)

/-- The polynomial algebra has finitely many algebra maps to the field with two elements. -/
private theorem finitePolynomialF2AlgHom :
    Finite (Polynomial (ZMod 2) →ₐ[ZMod 2] ZMod 2) :=
  Algebra.FiniteType.finite_algHom

end SchemePropertiesTest.FiniteFieldPointsModel
