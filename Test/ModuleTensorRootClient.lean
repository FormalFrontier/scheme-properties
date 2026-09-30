/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties

set_option warningAsError true

open CategoryTheory Limits MonoidalCategory TopologicalSpace ZeroObject
open scoped AlgebraicGeometry

#check AlgebraicGeometry.Scheme.Modules.tensorFunctor
#check AlgebraicGeometry.Scheme.Modules.tensor
#check AlgebraicGeometry.Scheme.Modules.tensorFunctor_obj
#check AlgebraicGeometry.Scheme.Modules.tensorUnit
#check AlgebraicGeometry.Scheme.Modules.tmul
#check AlgebraicGeometry.Scheme.Modules.tensorUnit_app_tmul
#check AlgebraicGeometry.Scheme.Modules.zero_tmul
#check AlgebraicGeometry.Scheme.Modules.tmul_zero
#check AlgebraicGeometry.Scheme.Modules.add_tmul
#check AlgebraicGeometry.Scheme.Modules.tmul_add
#check AlgebraicGeometry.Scheme.Modules.smul_tmul
#check AlgebraicGeometry.Scheme.Modules.tmul_smul
#check AlgebraicGeometry.Scheme.Modules.map_tmul
#check AlgebraicGeometry.Scheme.Modules.tensorHomEquiv
#check AlgebraicGeometry.Scheme.Modules.tensorHomEquiv_apply
#check AlgebraicGeometry.Scheme.Modules.tensorHomEquiv_symm_apply_apply
#check AlgebraicGeometry.Scheme.Modules.tensorHomEquiv_apply_symm_apply
#check AlgebraicGeometry.Scheme.Modules.tensorHomEquiv_app_tmul
#check AlgebraicGeometry.Scheme.Modules.tensorHomEquiv_symm_app_tmul
#check AlgebraicGeometry.Scheme.Modules.tensorFunctor_map_app_tmul
#check AlgebraicGeometry.Scheme.Modules.tensorSymm
#check AlgebraicGeometry.Scheme.Modules.tensorSymm_hom_app_tmul
#check AlgebraicGeometry.Scheme.Modules.tensorSymm_naturality

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)

private def check_1 : X.Modules := tensor M N
private def check_2 : X.Modules := tensor (0 : X.Modules) 0
private def check_3 : (Spec (.of PUnit.{u + 1})).Modules :=
  tensor (0 : (Spec (.of PUnit.{u + 1})).Modules) 0
private def check_4 : Scheme.empty.Modules := tensor (0 : Scheme.empty.Modules) 0
private def check_5 (s : Γ(M, (⊥ : X.Opens))) (t : Γ(N, (⊥ : X.Opens))) :
    Γ(tensor M N, (⊥ : X.Opens)) := tmul M N ⊥ s t

end AlgebraicGeometry.Scheme.Modules
