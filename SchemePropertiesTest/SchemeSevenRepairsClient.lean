/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.GeometricConnectedness
import SchemeProperties.IdealSheafModule
import SchemeProperties.ModuleTensor
import SchemeProperties.NormalEtale
import SchemeProperties.Torsion
import Mathlib.Data.ZMod.Basic

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

universe u

example {K : Type u} [Field K] [IsAlgClosed K]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [ConnectedSpace X] [ConnectedSpace Y] :
    ConnectedSpace ↥(pullback f g) :=
  connectedSpace_pullback_of_isAlgClosed f g

example {K : Type u} [Field K] [IsAlgClosed K]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    [ConnectedSpace X] [ConnectedSpace Y] :
    ConnectedSpace ↥(pullback f g) :=
  connectedSpace_pullback_of_isAlgClosed f g

example {R K M : Type*} [CommRing R]
    [CommRing K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module R M] :
    Module.IsTorsion R M ↔ Subsingleton (K ⊗[R] M) :=
  Module.isTorsion_iff_subsingleton_tensorProduct

example {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] :
    Module.IsTorsion R M ↔ Subsingleton (FractionRing R ⊗[R] M) :=
  Module.isTorsion_iff_subsingleton_fractionRing_tensorProduct

example
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    Module.IsTorsion R M ↔ Subsingleton (FractionRing R ⊗[R] M) :=
  Module.isTorsion_iff_subsingleton_fractionRing_tensorProduct

example :
    Module.IsTorsion (ZMod 6) (ZMod 6) ↔
      Subsingleton (FractionRing (ZMod 6) ⊗[ZMod 6] ZMod 6) :=
  Module.isTorsion_iff_subsingleton_tensorProduct

#check AlgebraicGeometry.Scheme.Modules.pointwiseMonoidalCategoryStruct
#check AlgebraicGeometry.Scheme.Modules.pointwiseMonoidalCategory
#check AlgebraicGeometry.Scheme.Modules.pointwiseSymmetricCategory
#check AlgebraicGeometry.Scheme.nilradicalModuleAffineSections

run_cmd do
  for name in #[``AlgebraicGeometry.Scheme.Modules.pointwiseMonoidalCategoryStruct,
      ``AlgebraicGeometry.Scheme.Modules.pointwiseMonoidalCategory,
      ``AlgebraicGeometry.Scheme.Modules.pointwiseSymmetricCategory] do
    if ← Lean.Elab.Command.liftCoreM (Lean.Meta.isInstance name) then
      throwError "Named local instance registered globally: {name}"
