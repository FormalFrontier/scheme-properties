/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.RationalFunctionFieldReconstruction

set_option warningAsError true

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace SchemePropertiesTest.RationalFunctionFieldReconstruction

variable {X Y S : AlgebraicGeometry.Scheme.{u}}
variable [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y]

private theorem generic_dominant (sX : X ⟶ S) (sY : Y ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType sY]
    (φ : Y.functionField ⟶ X.functionField)
    (hφ : (AlgebraicGeometry.Spec.map φ ≫
        Y.fromSpecStalk (genericPoint Y)) ≫ sY =
      X.fromSpecStalk (genericPoint X) ≫ sX) :
    (Scheme.RationalMap.ofFunctionFieldMap sX sY φ hφ).IsDominant := inferInstance

private theorem generic_base (sX : X ⟶ S) (sY : Y ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType sY]
    (φ : Y.functionField ⟶ X.functionField)
    (hφ : (AlgebraicGeometry.Spec.map φ ≫
        Y.fromSpecStalk (genericPoint Y)) ≫ sY =
      X.fromSpecStalk (genericPoint X) ≫ sX) :
    (Scheme.RationalMap.ofFunctionFieldMap sX sY φ hφ).compHom sY = sX.toRationalMap :=
  AlgebraicGeometry.Scheme.RationalMap.ofFunctionFieldMap_compHom sX sY φ hφ

private theorem generic_readback (sX : X ⟶ S) (sY : Y ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType sY]
    (φ : Y.functionField ⟶ X.functionField)
    (hφ : (AlgebraicGeometry.Spec.map φ ≫
        Y.fromSpecStalk (genericPoint Y)) ≫ sY =
      X.fromSpecStalk (genericPoint X) ≫ sX) :
    (Scheme.RationalMap.ofFunctionFieldMap sX sY φ hφ).functionFieldMap = φ :=
  AlgebraicGeometry.Scheme.RationalMap.functionFieldMap_ofFunctionFieldMap sX sY φ hφ

private theorem independent_converse (sX : X ⟶ S) (sY : Y ⟶ S)
    (r : X ⤏ Y) [r.IsDominant]
    (h : r.compHom sY = sX.toRationalMap) :
    (AlgebraicGeometry.Spec.map r.functionFieldMap ≫
        Y.fromSpecStalk (genericPoint Y)) ≫ sY =
      X.fromSpecStalk (genericPoint X) ≫ sX :=
  AlgebraicGeometry.Scheme.RationalMap.functionFieldMap_compatible sX sY r h

private theorem independent_reconstruction (sX : X ⟶ S) (sY : Y ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType sY]
    (r : X ⤏ Y) [r.IsDominant]
    (h : r.compHom sY = sX.toRationalMap) :
    Scheme.RationalMap.ofFunctionFieldMap sX sY r.functionFieldMap
      (independent_converse sX sY r h) = r :=
  AlgebraicGeometry.Scheme.RationalMap.ofFunctionFieldMap_functionFieldMap sX sY r h

private theorem independent_uniqueness (sX : X ⟶ S) (sY : Y ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType sY]
    (φ : Y.functionField ⟶ X.functionField)
    (hφ : (AlgebraicGeometry.Spec.map φ ≫
        Y.fromSpecStalk (genericPoint Y)) ≫ sY =
      X.fromSpecStalk (genericPoint X) ≫ sX)
    (r : X ⤏ Y) [r.IsDominant] (hr : r.functionFieldMap = φ) :
    r = Scheme.RationalMap.ofFunctionFieldMap sX sY φ hφ :=
  AlgebraicGeometry.Scheme.RationalMap.eq_of_functionFieldMap_eq r
    (Scheme.RationalMap.ofFunctionFieldMap sX sY φ hφ)
      (hr.trans (generic_readback sX sY φ hφ).symm)

end SchemePropertiesTest.RationalFunctionFieldReconstruction
