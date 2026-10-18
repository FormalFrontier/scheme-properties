/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.ComponentProduct

set_option warningAsError true

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

universe u

namespace ComponentProductOrdinaryImport

attribute [local instance] AlgebraicGeometry.tensorLocallyOfFiniteType
  AlgebraicGeometry.tensorQuasiCompact

noncomputable example (K : Type u) [Field K]
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] :
    componentScheme (X ⊗ Y) ≅ componentScheme X ⊗ componentScheme Y :=
  componentProductIso X Y

end ComponentProductOrdinaryImport
