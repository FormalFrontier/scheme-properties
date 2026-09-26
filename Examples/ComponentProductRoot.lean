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

private def check_1 (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    componentScheme (X ⊗ Y) ≅ componentScheme X ⊗ componentScheme Y :=
  componentProductIso X Y

private theorem check_2 (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    (componentProductIso X Y).hom = componentProductComparison X Y :=
  componentProductIso_hom X Y

private def check_3 [LocallyOfFiniteType (specOver K (Fin 2 → K)).hom]
    [QuasiCompact (specOver K (Fin 2 → K)).hom]
    [LocallyOfFiniteType (specOver K (DualNumber K)).hom]
    [QuasiCompact (specOver K (DualNumber K)).hom] :
    componentScheme
        (specOver K (Fin 2 → K) ⊗ specOver K (DualNumber K)) ≅
      componentScheme (specOver K (Fin 2 → K)) ⊗
        componentScheme (specOver K (DualNumber K)) :=
  componentProductIso _ _

private def check_4 {Z : Type u} [CommRing Z] [Algebra K Z] [Subsingleton Z]
    [LocallyOfFiniteType (specOver K Z).hom]
    [QuasiCompact (specOver K Z).hom] :
    componentScheme (specOver K Z ⊗ specOver K Z) ≅
      componentScheme (specOver K Z) ⊗ componentScheme (specOver K Z) :=
  componentProductIso _ _

end

end AlgebraicGeometry.ComponentProductRootClient
