/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.ComponentBaseChange
import Mathlib.Algebra.DualNumber
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Client checks for component schemes under field extension

The arbitrary-extension checks exercise the literal canonical isomorphism and
its compatibility triangle.  The explicit source schemes include a
disconnected affine scheme, a nonreduced affine scheme, and an empty affine
scheme with subsingleton coordinate ring.
-/

set_option warningAsError true

open CategoryTheory Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.ComponentBaseChangeClient

noncomputable section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

attribute [local instance] AlgebraicGeometry.tensorProductRightAlgebra
  AlgebraicGeometry.baseChangeLocallyOfFiniteType
  AlgebraicGeometry.baseChangeQuasiCompact

/-- Ordinary use over an arbitrary field extension has no algebraicity,
finite-dimensionality, separability, or perfectness assumption. -/
example (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    toComponentScheme (schemeBaseChange X (L := K)) ≫
        componentBaseChangeComparison (K := K) X =
      baseChangeMap (L := K) (toComponentScheme X) :=
  toComponentScheme_comp_componentBaseChangeComparison (K := K) X

/-- The underlying canonical algebra comparison is injective for every field
extension. -/
example (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    Function.Injective (componentBaseChangeComparisonAlgHom (K := K) X) :=
  componentBaseChangeComparisonAlgHom_injective (K := K) X

/-- The underlying canonical algebra comparison is also surjective for every
field extension. -/
example (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    Function.Surjective (componentBaseChangeComparisonAlgHom (K := K) X) :=
  componentBaseChangeComparisonAlgHom_surjective (K := K) X

/-- The scalar-extended and newly selected subalgebras are literally equal in
the global-sections ring, not merely abstractly equivalent. -/
example (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    baseChangedComponentSubalgebra (K := K) X =
      componentSubalgebra (schemeBaseChange X (L := K)) :=
  baseChangedComponentSubalgebra_eq (K := K) X

/-- The coordinate-algebra comparison is packaged as an equivalence. -/
example (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    componentSubalgebra X ⊗[k] K ≃ₐ[K]
      componentSubalgebra (schemeBaseChange X (L := K)) :=
  componentBaseChangeComparisonAlgEquiv (K := K) X

/-- The arbitrary-extension isomorphism has exactly the canonical literal
comparison as its forward map. -/
example (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    (componentBaseChangeIso (K := K) X).hom =
      componentBaseChangeComparison (K := K) X :=
  componentBaseChangeIso_hom (K := K) X

/-- The identity extension is included in the arbitrary-extension comparison
surface, without adding separably closedness. -/
example (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    componentScheme (schemeBaseChange X (L := k)) ≅
      schemeBaseChange (componentScheme X) (L := k) :=
  componentBaseChangeIso (K := k) X

/-- A purely inseparable extension is covered without using its additional
field-theoretic structure. -/
example [IsPurelyInseparable k K]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    componentScheme (schemeBaseChange X (L := K)) ≅
      schemeBaseChange (componentScheme X) (L := K) :=
  componentBaseChangeIso (K := K) X

/-- The isomorphism has the literal canonical comparison as its forward map. -/
example [IsPurelyInseparable k K]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    (componentBaseChangeIso (K := K) X).hom =
      componentBaseChangeComparison (K := K) X :=
  componentBaseChangeIso_hom (K := K) X

/-- Passage to a separable closure is covered by the same literal
isomorphism. -/
example (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    componentScheme (schemeBaseChange X (L := SeparableClosure k)) ≅
      schemeBaseChange (componentScheme X) (L := SeparableClosure k) :=
  componentBaseChangeIso (K := SeparableClosure k) X

/-- A disconnected affine source is accepted without a connectedness
hypothesis. -/
example [LocallyOfFiniteType (specOver k (Fin 2 → k)).hom]
    [QuasiCompact (specOver k (Fin 2 → k)).hom] :
    componentScheme (schemeBaseChange (specOver k (Fin 2 → k)) (L := K)) ≅
      schemeBaseChange (componentScheme (specOver k (Fin 2 → k))) (L := K) :=
  componentBaseChangeIso (K := K) _

/-- A nonreduced dual-number source is accepted without a reducedness
hypothesis. -/
example [LocallyOfFiniteType (specOver k (DualNumber k)).hom]
    [QuasiCompact (specOver k (DualNumber k)).hom] :
    componentScheme (schemeBaseChange (specOver k (DualNumber k)) (L := K)) ≅
      schemeBaseChange (componentScheme (specOver k (DualNumber k))) (L := K) :=
  componentBaseChangeIso (K := K) _

/-- A genuinely transcendental extension is covered. -/
example (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    componentScheme (schemeBaseChange X (L := RatFunc k)) ≅
      schemeBaseChange (componentScheme X) (L := RatFunc k) :=
  componentBaseChangeIso (K := RatFunc k) X

/-- A mixed transcendental/algebraic extension is covered. -/
example (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    let _ : Algebra k (AlgebraicClosure (RatFunc k)) :=
      ((algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))).comp
        (algebraMap k (RatFunc k))).toAlgebra
    componentScheme
        (schemeBaseChange X (L := AlgebraicClosure (RatFunc k))) ≅
      schemeBaseChange (componentScheme X)
        (L := AlgebraicClosure (RatFunc k)) := by
  let _ : Algebra k (AlgebraicClosure (RatFunc k)) :=
    ((algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))).comp
      (algebraMap k (RatFunc k))).toAlgebra
  exact componentBaseChangeIso (K := AlgebraicClosure (RatFunc k)) X

/-- A subsingleton coordinate ring has empty spectrum; the construction and
compatibility theorem still apply. -/
example {Z : Type u} [CommRing Z] [Algebra k Z] [Subsingleton Z]
    [LocallyOfFiniteType (specOver k Z).hom]
    [QuasiCompact (specOver k Z).hom] :
    toComponentScheme (schemeBaseChange (specOver k Z) (L := K)) ≫
        componentBaseChangeComparison (K := K) (specOver k Z) =
      baseChangeMap (L := K) (toComponentScheme (specOver k Z)) :=
  toComponentScheme_comp_componentBaseChangeComparison (K := K) _

/-- The empty spectrum also lies on the arbitrary-extension isomorphism
surface. -/
example {Z : Type u} [CommRing Z] [Algebra k Z] [Subsingleton Z]
    [LocallyOfFiniteType (specOver k Z).hom]
    [QuasiCompact (specOver k Z).hom] :
    componentScheme (schemeBaseChange (specOver k Z) (L := K)) ≅
      schemeBaseChange (componentScheme (specOver k Z)) (L := K) :=
  componentBaseChangeIso (K := K) _

end

end AlgebraicGeometry.ComponentBaseChangeClient
