/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties
import Mathlib.Algebra.DualNumber

/-! # Aggregate-root client checks for component products -/

set_option warningAsError true

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

universe u

namespace AlgebraicGeometry.ComponentProductRootClient

noncomputable section

variable {K : Type u} [Field K]

attribute [local instance] AlgebraicGeometry.tensorLocallyOfFiniteType
  AlgebraicGeometry.tensorQuasiCompact

example (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    componentScheme (X ⊗ Y) ≅ componentScheme X ⊗ componentScheme Y :=
  componentProductIso X Y

example (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    (componentProductIso X Y).hom = componentProductComparison X Y :=
  componentProductIso_hom X Y

example [LocallyOfFiniteType (specOver K (Fin 2 → K)).hom]
    [QuasiCompact (specOver K (Fin 2 → K)).hom]
    [LocallyOfFiniteType (specOver K (DualNumber K)).hom]
    [QuasiCompact (specOver K (DualNumber K)).hom] :
    componentScheme
        (specOver K (Fin 2 → K) ⊗ specOver K (DualNumber K)) ≅
      componentScheme (specOver K (Fin 2 → K)) ⊗
        componentScheme (specOver K (DualNumber K)) :=
  componentProductIso _ _

example {Z : Type u} [CommRing Z] [Algebra K Z] [Subsingleton Z]
    [LocallyOfFiniteType (specOver K Z).hom]
    [QuasiCompact (specOver K Z).hom] :
    componentScheme (specOver K Z ⊗ specOver K Z) ≅
      componentScheme (specOver K Z) ⊗ componentScheme (specOver K Z) :=
  componentProductIso _ _

end

end AlgebraicGeometry.ComponentProductRootClient
