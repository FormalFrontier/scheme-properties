/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.ComponentProduct
import Mathlib.Algebra.DualNumber

/-!
# Client checks for component schemes and binary fibre products

The explicit schemes exercise connected, disconnected, nonreduced, and empty
surfaces.  None of the checks assumes reducedness, connectedness, separation,
nonemptiness, or a restriction on the characteristic.
-/

set_option warningAsError true

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

universe u

namespace AlgebraicGeometry.ComponentProductClient

noncomputable section

variable {K : Type u} [Field K]

local instance tensorLocallyOfFiniteType
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] : LocallyOfFiniteType (X ⊗ Y).hom := by
  rw [← (fst X Y).w]
  let _ : LocallyOfFiniteType (pullback.fst X.hom Y.hom) := inferInstance
  let _ : LocallyOfFiniteType (fst X Y).left := by
    change LocallyOfFiniteType (pullback.fst X.hom Y.hom)
    infer_instance
  infer_instance

local instance tensorQuasiCompact
    (X Y : Over (Spec (.of K))) [QuasiCompact X.hom]
    [QuasiCompact Y.hom] : QuasiCompact (X ⊗ Y).hom := by
  rw [← (fst X Y).w]
  let _ : QuasiCompact (pullback.fst X.hom Y.hom) := inferInstance
  let _ : QuasiCompact (fst X Y).left := by
    change QuasiCompact (pullback.fst X.hom Y.hom)
    infer_instance
  infer_instance

/-- The canonical comparison has its defining projection triangle. -/
private theorem check_1 (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    toComponentScheme (X ⊗ Y) ≫ componentProductComparison X Y =
      lift (fst X Y ≫ toComponentScheme X)
        (snd X Y ≫ toComponentScheme Y) :=
  toComponentScheme_comp_componentProductComparison X Y

/-- The product comparison is an isomorphism over every field. -/
private def check_2 (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    componentScheme (X ⊗ Y) ≅ componentScheme X ⊗ componentScheme Y :=
  componentProductIso X Y

/-- The isomorphism's forward map is literally the canonical comparison. -/
private theorem check_3 (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    (componentProductIso X Y).hom = componentProductComparison X Y :=
  componentProductIso_hom X Y

/-- Functorial component maps preserve composition. -/
private theorem check_4 {X Y Z : Over (Spec (.of K))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    componentSchemeMapOfHom (f ≫ g) =
      componentSchemeMapOfHom f ≫ componentSchemeMapOfHom g :=
  componentSchemeMapOfHom_comp f g

/-- A connected affine point lies on the product surface. -/
private def check_5 [LocallyOfFiniteType (specOver K K).hom]
    [QuasiCompact (specOver K K).hom] :
    componentScheme (specOver K K ⊗ specOver K K) ≅
      componentScheme (specOver K K) ⊗ componentScheme (specOver K K) :=
  componentProductIso _ _

/-- A disconnected finite constant affine scheme is supported. -/
private def check_6 [LocallyOfFiniteType (specOver K (Fin 2 → K)).hom]
    [QuasiCompact (specOver K (Fin 2 → K)).hom] :
    componentScheme
        (specOver K (Fin 2 → K) ⊗ specOver K (Fin 2 → K)) ≅
      componentScheme (specOver K (Fin 2 → K)) ⊗
        componentScheme (specOver K (Fin 2 → K)) :=
  componentProductIso _ _

/-- Nonreduced dual-number factors require no reducedness hypothesis. -/
private def check_7 [LocallyOfFiniteType (specOver K (DualNumber K)).hom]
    [QuasiCompact (specOver K (DualNumber K)).hom] :
    componentScheme
        (specOver K (DualNumber K) ⊗ specOver K (DualNumber K)) ≅
      componentScheme (specOver K (DualNumber K)) ⊗
        componentScheme (specOver K (DualNumber K)) :=
  componentProductIso _ _

/-- A subsingleton coordinate ring has empty spectrum and is also supported. -/
private def check_8 {Z : Type u} [CommRing Z] [Algebra K Z] [Subsingleton Z]
    [LocallyOfFiniteType (specOver K Z).hom]
    [QuasiCompact (specOver K Z).hom] :
    componentScheme (specOver K Z ⊗ specOver K Z) ≅
      componentScheme (specOver K Z) ⊗ componentScheme (specOver K Z) :=
  componentProductIso _ _

end

end AlgebraicGeometry.ComponentProductClient
