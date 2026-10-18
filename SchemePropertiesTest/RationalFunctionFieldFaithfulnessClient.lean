/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.RationalFunctionFieldFaithfulness

public section

set_option warningAsError true

open CategoryTheory AlgebraicGeometry

universe u

namespace SchemePropertiesTest.RationalFunctionFieldFaithfulness

example {X Y : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y]
    (r s : X ⤏ Y) [r.IsDominant] [s.IsDominant]
    (h : r.functionFieldMap = s.functionFieldMap) : r = s :=
  AlgebraicGeometry.Scheme.RationalMap.eq_of_functionFieldMap_eq r s h

example
    {A B : AlgebraicGeometry.IntegralDominantRationalScheme.{u}ᵒᵖ}
    (f g : A ⟶ B)
    (h : AlgebraicGeometry.IntegralDominantRationalScheme.functionFieldFunctor.map f =
      AlgebraicGeometry.IntegralDominantRationalScheme.functionFieldFunctor.map g) : f = g :=
  AlgebraicGeometry.IntegralDominantRationalScheme.functionFieldFunctor.map_injective h

end SchemePropertiesTest.RationalFunctionFieldFaithfulness
