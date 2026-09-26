module

import SchemeProperties.ComponentProduct

set_option warningAsError true

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

universe u

namespace ComponentProductOrdinaryImport

private instance tensorLocallyOfFiniteType
    (K : Type u) [Field K]
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] : LocallyOfFiniteType (X ⊗ Y).hom := by
  rw [← (fst X Y).w]
  let _ : LocallyOfFiniteType (pullback.fst X.hom Y.hom) := inferInstance
  let _ : LocallyOfFiniteType (fst X Y).left := by
    change LocallyOfFiniteType (pullback.fst X.hom Y.hom)
    infer_instance
  infer_instance

private instance tensorQuasiCompact
    (K : Type u) [Field K]
    (X Y : Over (Spec (.of K))) [QuasiCompact X.hom]
    [QuasiCompact Y.hom] : QuasiCompact (X ⊗ Y).hom := by
  rw [← (fst X Y).w]
  let _ : QuasiCompact (pullback.fst X.hom Y.hom) := inferInstance
  let _ : QuasiCompact (fst X Y).left := by
    change QuasiCompact (pullback.fst X.hom Y.hom)
    infer_instance
  infer_instance

private noncomputable def checkProduct (K : Type u) [Field K]
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] :
    componentScheme (X ⊗ Y) ≅ componentScheme X ⊗ componentScheme Y :=
  componentProductIso X Y

end ComponentProductOrdinaryImport
