/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.RationalFunctionFieldPullback

public section

set_option warningAsError true

open CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace SchemePropertiesTest.RationalFunctionFieldPullback

open AlgebraicGeometry

variable {X Y Z W : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  [IsIntegral Z] [IsIntegral W]

private theorem generic_image (r : X ⤏ Y) [r.IsDominant] :
    r.fromFunctionField (closedPoint X.functionField) = genericPoint Y :=
  Scheme.RationalMap.fromFunctionField_closedPoint r

private theorem representative (p : X.PartialMap Y) [IsDominant p.hom] :
    p.toRationalMap.functionFieldMap =
      (Y.presheaf.stalkCongr (.of_eq
        (Scheme.RationalMap.fromFunctionField_closedPoint p.toRationalMap).symm)).hom ≫
        Scheme.stalkClosedPointTo p.fromFunctionField := by
  rfl

private theorem dense_restriction (p : X.PartialMap Y) [IsDominant p.hom]
    (U : X.Opens) (hU : Dense (U : Set X)) (hU' : U ≤ p.domain) :
    (p.restrict U hU hU').toRationalMap.functionFieldMap =
      p.toRationalMap.functionFieldMap := by
  apply Scheme.RationalMap.functionFieldMap_eq_of_fromFunctionField_eq
  simpa only [Scheme.RationalMap.fromFunctionField_toRationalMap] using
    p.fromFunctionField_restrict hU hU'

private theorem identity :
    (Scheme.RationalMap.id X).functionFieldMap = 𝟙 X.functionField := by
  exact Scheme.RationalMap.functionFieldMap_id

private theorem reversed_two (r : X ⤏ Y) [r.IsDominant]
    (s : Y ⤏ Z) [s.IsDominant] :
    (r.comp s).functionFieldMap = s.functionFieldMap ≫ r.functionFieldMap := by
  exact Scheme.RationalMap.functionFieldMap_comp r s

private theorem reversed_three (r : X ⤏ Y) [r.IsDominant]
    (s : Y ⤏ Z) [s.IsDominant] (t : Z ⤏ W) [t.IsDominant] :
    ((r.comp s).comp t).functionFieldMap =
      t.functionFieldMap ≫ s.functionFieldMap ≫ r.functionFieldMap := by
  rw [Scheme.RationalMap.functionFieldMap_comp,
    Scheme.RationalMap.functionFieldMap_comp]

variable {A B C : IntegralDominantRationalScheme.{u}}

private theorem category_identity :
    IntegralDominantRationalScheme.functionFieldFunctor.map
      (𝟙 (Opposite.op A)) = 𝟙 A.toScheme.functionField := by
  exact IntegralDominantRationalScheme.functionFieldFunctor.map_id _

private theorem category_arrow (f : A ⟶ B) :
    IntegralDominantRationalScheme.functionFieldFunctor.map f.op =
      f.toRationalMap.functionFieldMap := rfl

private theorem category_composition (f : A ⟶ B) (g : B ⟶ C) :
    IntegralDominantRationalScheme.functionFieldFunctor.map (g.op ≫ f.op) =
      IntegralDominantRationalScheme.functionFieldFunctor.map g.op ≫
        IntegralDominantRationalScheme.functionFieldFunctor.map f.op := by
  exact IntegralDominantRationalScheme.functionFieldFunctor.map_comp _ _

end SchemePropertiesTest.RationalFunctionFieldPullback
