/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties

set_option warningAsError true

open CategoryTheory Limits ZeroObject
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
  (M N : Y.Modules)

example : (tensor M N).restrict f ≅ tensor (M.restrict f) (N.restrict f) :=
  (restrictTensorNatIso f).app (M, N)

example (U : X.Opens) (s : Γ(M.restrict f, U)) (t : Γ(N.restrict f, U)) :
    ((restrictTensorNatIso f).inv.app (M, N)).app U
        (tmul (M.restrict f) (N.restrict f) U s t) =
      ((tensor M N).restrictAppIso f U).inv
        (tmul M N (f ''ᵁ U) ((M.restrictAppIso f U).hom s)
          ((N.restrictAppIso f U).hom t)) :=
  restrictTensorNatIso_inv_app_tmul f M N U s t

example : (tensor (0 : Y.Modules) 0).restrict f ≅
    tensor ((0 : Y.Modules).restrict f) ((0 : Y.Modules).restrict f) :=
  (restrictTensorNatIso f).app (0, 0)

end AlgebraicGeometry.Scheme.Modules
