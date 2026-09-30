/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.RationalFunctionFieldPullback

public section

/-!
# Faithfulness of function-field pullback

On integral schemes, the action of a dominant native rational map on function fields
determines the rational map itself. Consequently the existing contravariant
function-field functor on integral schemes and dominant rational maps is faithful.
-/

set_option warningAsError true

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.RationalMap

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

private theorem fromFunctionField_id :
    (RationalMap.id Y).fromFunctionField = Y.fromSpecStalk (genericPoint Y) := by
  change ((𝟙 Y : Y ⟶ Y).toPartialMap).fromSpecStalkOfMem _ = _
  rw [PartialMap.fromSpecStalkOfMem_toPartialMap, Category.comp_id]

private theorem fromFunctionField_eq_specMap (t : X ⤏ Y) [t.IsDominant] :
    t.fromFunctionField =
      Spec.map t.functionFieldMap ≫ Y.fromSpecStalk (genericPoint Y) := by
  calc
    t.fromFunctionField =
        (t.comp (RationalMap.id Y)).fromFunctionField := by rw [RationalMap.comp_id]
    _ = Spec.map t.functionFieldMap ≫ (RationalMap.id Y).fromFunctionField :=
      RationalMap.fromFunctionField_comp t (RationalMap.id Y)
    _ = Spec.map t.functionFieldMap ≫ Y.fromSpecStalk (genericPoint Y) := by
      rw [fromFunctionField_id]

/-- Equality of the function-field homomorphisms induced by independently dominant
native quotient rational maps reflects equality of the rational maps. -/
theorem eq_of_functionFieldMap_eq (r s : X ⤏ Y) [r.IsDominant] [s.IsDominant]
    (h : r.functionFieldMap = s.functionFieldMap) : r = s := by
  apply RationalMap.eq_of_fromFunctionField_eq r s
  calc
    r.fromFunctionField =
        Spec.map r.functionFieldMap ≫ Y.fromSpecStalk (genericPoint Y) :=
      fromFunctionField_eq_specMap r
    _ = Spec.map s.functionFieldMap ≫ Y.fromSpecStalk (genericPoint Y) := by rw [h]
    _ = s.fromFunctionField := (fromFunctionField_eq_specMap s).symm

end AlgebraicGeometry.Scheme.RationalMap

namespace AlgebraicGeometry.IntegralDominantRationalScheme

/-- Pullback on function fields distinguishes dominant rational maps. -/
instance : functionFieldFunctor.{u}.Faithful where
  map_injective := by
    intro A B f g h
    apply Quiver.Hom.unop_inj
    apply hom_ext
    apply Scheme.RationalMap.eq_of_functionFieldMap_eq
    exact h

end AlgebraicGeometry.IntegralDominantRationalScheme
