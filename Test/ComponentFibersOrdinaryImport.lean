/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.ComponentFibers

set_option warningAsError true

open AlgebraicGeometry CategoryTheory

universe u

namespace ComponentFibersOrdinaryImport

noncomputable example (K : Type u) [Field K]
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (x : (componentScheme X).left) :
    Over (Spec ((componentScheme X).left.residueField x)) :=
  componentSchemeFiber X x

example (K : Type u) [Field K]
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (x : (componentScheme X).left) :
    GeometricallyConnected
      ((toComponentScheme X).left.fiberToSpecResidueField x) :=
  geometricallyConnected_fiber_toComponentScheme X x

end ComponentFibersOrdinaryImport
