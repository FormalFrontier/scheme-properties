/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.ModuleTensorRestriction

set_option warningAsError true

open CategoryTheory Limits TopologicalSpace ZeroObject
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
  (M N : Y.Modules)

example : tensorFunctor Y ⋙ restrictFunctor f ≅
    (restrictFunctor f).prod (restrictFunctor f) ⋙ tensorFunctor X :=
  restrictTensorNatIso f

example : (tensor M N).restrict f ≅ tensor (M.restrict f) (N.restrict f) :=
  (restrictTensorNatIso f).app (M, N)

example {M' N' : Y.Modules} (a : M ⟶ M') (b : N ⟶ N') :
    (tensorFunctor Y ⋙ restrictFunctor f).map ((a, b) : (M, N) ⟶ (M', N')) ≫
        (restrictTensorNatIso f).hom.app (M', N') =
      (restrictTensorNatIso f).hom.app (M, N) ≫
        ((restrictFunctor f).prod (restrictFunctor f) ⋙ tensorFunctor X).map
          ((a, b) : (M, N) ⟶ (M', N')) :=
  (restrictTensorNatIso f).hom.naturality ((a, b) : (M, N) ⟶ (M', N'))

example (U : X.Opens) (s : Γ(M.restrict f, U)) (t : Γ(N.restrict f, U)) :
    ((restrictTensorNatIso f).inv.app (M, N)).app U
        (tmul (M.restrict f) (N.restrict f) U s t) =
      ((tensor M N).restrictAppIso f U).inv
        (tmul M N (f ''ᵁ U) ((M.restrictAppIso f U).hom s)
          ((N.restrictAppIso f U).hom t)) :=
  restrictTensorNatIso_inv_app_tmul f M N U s t

example : (tensor M N).restrict (𝟙 Y) ≅
    tensor (M.restrict (𝟙 Y)) (N.restrict (𝟙 Y)) :=
  (restrictTensorNatIso (𝟙 Y)).app (M, N)

-- An arbitrary open immersion, with its dependent section/scalar transports.
example (U : Y.Opens) (V : U.toScheme.Opens)
    (s : Γ(M.restrict U.ι, V)) (t : Γ(N.restrict U.ι, V)) :
    ((restrictTensorNatIso U.ι).inv.app (M, N)).app V
        (tmul (M.restrict U.ι) (N.restrict U.ι) V s t) =
      ((tensor M N).restrictAppIso U.ι V).inv
        (tmul M N (U.ι ''ᵁ V) ((M.restrictAppIso U.ι V).hom s)
          ((N.restrictAppIso U.ι V).hom t)) :=
  restrictTensorNatIso_inv_app_tmul U.ι M N V s t

example (V : (⊥ : Y.Opens).toScheme.Opens)
    (s : Γ(M.restrict (⊥ : Y.Opens).ι, V))
    (t : Γ(N.restrict (⊥ : Y.Opens).ι, V)) :
    ((restrictTensorNatIso (⊥ : Y.Opens).ι).inv.app (M, N)).app V
        (tmul (M.restrict (⊥ : Y.Opens).ι) (N.restrict (⊥ : Y.Opens).ι) V s t) =
      ((tensor M N).restrictAppIso (⊥ : Y.Opens).ι V).inv
        (tmul M N ((⊥ : Y.Opens).ι ''ᵁ V)
          ((M.restrictAppIso (⊥ : Y.Opens).ι V).hom s)
          ((N.restrictAppIso (⊥ : Y.Opens).ι V).hom t)) :=
  restrictTensorNatIso_inv_app_tmul (⊥ : Y.Opens).ι M N V s t

example : (tensor (0 : Y.Modules) 0).restrict f ≅
    tensor ((0 : Y.Modules).restrict f) ((0 : Y.Modules).restrict f) :=
  (restrictTensorNatIso f).app (0, 0)

example : (tensor (0 : Scheme.empty.Modules) 0).restrict (𝟙 _) ≅
    tensor ((0 : Scheme.empty.Modules).restrict (𝟙 _))
      ((0 : Scheme.empty.Modules).restrict (𝟙 _)) :=
  (restrictTensorNatIso (𝟙 Scheme.empty)).app (0, 0)

example : (tensor (0 : (Spec (.of PUnit.{u + 1})).Modules) 0).restrict (𝟙 _) ≅
    tensor ((0 : (Spec (.of PUnit.{u + 1})).Modules).restrict (𝟙 _))
      ((0 : (Spec (.of PUnit.{u + 1})).Modules).restrict (𝟙 _)) :=
  (restrictTensorNatIso (𝟙 (Spec (.of PUnit.{u + 1})))).app (0, 0)

end AlgebraicGeometry.Scheme.Modules
