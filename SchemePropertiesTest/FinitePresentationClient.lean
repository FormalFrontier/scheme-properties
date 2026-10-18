/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.SheafFinitePresentationTransport
public import SchemeProperties.ModuleFinitePresentation
public import Mathlib.Data.ZMod.Basic

public section

set_option warningAsError true

/-!
# Direct-import native finite-presentation clients

The two sites in the generic mapped-presentation test have independent object
and morphism universes. The zero-ring and zero-module clients do not add any
nontriviality or positive-rank premise to the exported results.
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace SheafOfModules

universe u v₁ v₂ u₁ u₂

namespace SchemePropertiesTest.FinitePresentation

theorem mapped_finite_indices
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
    {S : Sheaf K RingCat.{u}}
    [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules.{u} R} (P : M.Presentation) [P.IsFinite]
    (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
    [PreservesColimitsOfSize.{u, u} F] (η : unit S ≅ F.obj (unit R)) :
    (P.map F η).IsFinite :=
  P.isFinite_map F η

theorem global_finite_presentation
    {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules.{u} R} (P : M.Presentation) [P.IsFinite] :
    M.IsFinitePresentation :=
  P.isFinitePresentation

theorem empty_finite_indices
    {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules.{u} R} (P : M.Presentation) [P.IsFinite]
    [IsEmpty P.generators.I] [IsEmpty P.relations.I] :
    M.IsFinitePresentation :=
  P.isFinitePresentation

theorem finite_restriction {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] {M : X.Modules} (P : M.Presentation) [P.IsFinite] :
    (Scheme.Modules.presentationRestrict f P).IsFinite :=
  Scheme.Modules.isFinite_presentationRestrict f P

theorem finite_tilde {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    [Module.FinitePresentation R M] : (tilde M).IsFinitePresentation :=
  isFinitePresentation_tilde M

theorem zero_module_tilde {R : CommRingCat.{u}} :
    (tilde (ModuleCat.of R (Fin 0 →₀ R))).IsFinitePresentation :=
  isFinitePresentation_tilde (ModuleCat.of R (Fin 0 →₀ R))

theorem zero_ring_zero_module_tilde :
    (tilde (ModuleCat.of (CommRingCat.of (ZMod 1)) (Fin 0 →₀ ZMod 1))).IsFinitePresentation :=
  isFinitePresentation_tilde (ModuleCat.of (CommRingCat.of (ZMod 1)) (Fin 0 →₀ ZMod 1))

theorem affine_finite_presentations {X : Scheme.{u}}
    (M : X.Modules) [M.IsFinitePresentation] :
    ∃ (ι : Type u) (U : ι → X.Opens)
      (P : ∀ i, (M.restrict (U i).ι).Presentation),
      IsOpenCover U ∧ (∀ i, IsAffineOpen (U i)) ∧ ∀ i, (P i).IsFinite :=
  Scheme.Modules.exists_isOpenCover_isFinite_presentation M

theorem zero_ring_affine_finite_presentations
    (M : (Spec (CommRingCat.of (ZMod 1))).Modules) [M.IsFinitePresentation] :
    ∃ (ι : Type 0) (U : ι → (Spec (CommRingCat.of (ZMod 1))).Opens)
      (P : ∀ i, (M.restrict (U i).ι).Presentation),
      IsOpenCover U ∧ (∀ i, IsAffineOpen (U i)) ∧ ∀ i, (P i).IsFinite :=
  Scheme.Modules.exists_isOpenCover_isFinite_presentation M

end SchemePropertiesTest.FinitePresentation
