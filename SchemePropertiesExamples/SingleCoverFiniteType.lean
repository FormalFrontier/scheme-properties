/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.FiniteTypeSingleCover

/-!
# Finite-type single-cover points

These examples compute the base triangle of affine spectra and restriction of
represented points along successive test maps using only the public finite-type
single-cover import.
-/

public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

example (K : Type u) [Field K] {targetTest sourceTest : (FGAlgCat K)ᵒᵖ}
    (testMap : sourceTest ⟶ targetTest) :
    Spec.map (CommRingCat.ofHom testMap.unop.hom.hom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K targetTest.unop.obj)) =
      Spec.map (CommRingCat.ofHom (algebraMap K sourceTest.unop.obj)) := by
  have baseTriangle : ((finiteAlgSpecOver K).map testMap).left ≫
      ((finiteAlgSpecOver K).obj targetTest).hom =
        ((finiteAlgSpecOver K).obj sourceTest).hom :=
    Over.w ((finiteAlgSpecOver K).map testMap).hom
  simpa only [finiteAlgSpecOver_obj_left, finiteAlgSpecOver_map_left,
    finiteAlgSpecOver_obj_hom] using baseTriangle

example (K : Type u) [Field K] (Y : algebraicOver K)
    {targetTest middleTest sourceTest : (FGAlgCat K)ᵒᵖ}
    (firstMap : middleTest ⟶ targetTest) (nextMap : sourceTest ⟶ middleTest)
    (point : ULift.{0} ((finiteAlgSpecOver K).obj targetTest ⟶ Y.obj)) :
    (((algebraicOverPoints K).obj Y).map nextMap.op
      (((algebraicOverPoints K).obj Y).map firstMap.op point)).down.left =
      Spec.map (CommRingCat.ofHom nextMap.unop.hom.hom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom firstMap.unop.hom.hom.toRingHom) ≫ point.down.left := by
  simp only [algebraicOverPoints_map_apply, ULift.down_up,
    MorphismProperty.Comma.comp_left, finiteAlgSpecOver_map_left]
  rfl

end AlgebraicGeometry
