/-
SPDX-License-Identifier: Apache-2.0
Authors: Prism, Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

public section

set_option warningAsError true

/-!
# Finite presentations of sheaves of modules

A finite global presentation supplies the native local finite-presentation
predicate. Mapping a presentation through a colimit-preserving functor with a
unit comparison preserves its finite generator and relation index types.
Neither statement identifies native finite presentation with categorical
finite-presentability.
-/

noncomputable section

open CategoryTheory Limits

universe u v₁ v₂ u₁ u₂

namespace SheafOfModules

section Map

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  {S : Sheaf K RingCat.{u}}
  [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M : SheafOfModules.{u} R}

/-- A colimit-preserving map of a presentation retains its finite generator and
relation indices. The unit comparison is part of the native `Presentation.map`. -/
theorem Presentation.isFinite_map (P : M.Presentation) [P.IsFinite]
    (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
    [PreservesColimitsOfSize.{u, u} F] (η : unit S ≅ F.obj (unit R)) :
    (P.map F η).IsFinite where
  isFiniteType_generators := ⟨by
    simpa only [Presentation.map_generators_I] using
      (inferInstance : Finite P.generators.I)⟩
  isFiniteType_relations := ⟨by
    simpa only [Presentation.map_relations_I] using
      (inferInstance : Finite P.relations.I)⟩

end Map

section Global

variable {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C]
  {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M : SheafOfModules.{u} R}

/-- A supplied finite global presentation gives the native local finite-
presentation predicate. Binary products and sheafification on each over-site
are used by `P.quasicoherentData`; no terminal object is assumed. -/
theorem Presentation.isFinitePresentation (P : M.Presentation) [P.IsFinite] :
    M.IsFinitePresentation := by
  refine ⟨P.quasicoherentData, ?_⟩
  constructor
  intro x
  constructor
  · constructor
    change Finite P.generators.I
    infer_instance
  · constructor
    change Finite P.relations.I
    infer_instance

end Global

end SheafOfModules
