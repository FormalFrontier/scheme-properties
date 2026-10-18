/-
SPDX-License-Identifier: Apache-2.0
Authors: Lintel
-/
module

import SchemeProperties.QuasiFinitePoints
import Mathlib.Algebra.Algebra.Prod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Field-valued fibers of a split finite cover

For any field `k`, the diagonal algebra map `k → k × k` induces a finite morphism
`Spec (k × k) ⟶ Spec k`. The two projections give distinct sections. Its field-valued
postcomposition fibers are finite by Mathlib's `Finite.algHom` and
`Spec.homEquivAlgHom`, independently of the geometric-point criteria.

The examples apply the all-fields forward theorem, the reverse theorem with all
algebraically closed test fields, and the forward direction of the equivalence.
The finite-morphism hypotheses are supplied by Mathlib's product-module and affine
spectrum APIs.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable (k : Type u) [Field k]

private def splitCover :
    Spec (CommRingCat.of (k × k)) ⟶ Spec (CommRingCat.of k) :=
  Spec.algebraMap k (k × k)

private instance splitCover_isFinite : IsFinite (splitCover k) := by
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k (k × k))))
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr (Module.Finite.prod (R := k) (M := k) (N := k))

private theorem splitCover_finite_fiber {K : Type u} [Field K]
    (g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) :
    Set.Finite {q : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (k × k)) |
      q ≫ splitCover k = g} := by
  let _ : Algebra k K := (Spec.homEquivRingHom g).toAlgebra
  have hg : Spec.algebraMap k K = g := by
    exact (Spec.homEquivRingHom (R := k) (S := K)).symm_apply_apply g
  have : Module.Finite k (k × k) := Module.Finite.prod
  rw [← hg]
  exact (Spec.homEquivAlgHom (R := k) (A := k × k) (B := K)).finite_iff.mpr
    (Finite.algHom k (k × k) K)

private def firstLift :
    Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (k × k)) :=
  Spec.map (CommRingCat.ofHom (AlgHom.fst k k k).toRingHom)

private def secondLift :
    Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (k × k)) :=
  Spec.map (CommRingCat.ofHom (AlgHom.snd k k k).toRingHom)

private theorem firstLift_comp_splitCover : firstLift k ≫ splitCover k = 𝟙 _ := by
  simp only [firstLift, splitCover, Spec.algebraMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap,
    Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

private theorem secondLift_comp_splitCover : secondLift k ≫ splitCover k = 𝟙 _ := by
  simp only [secondLift, splitCover, Spec.algebraMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap,
    Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

private theorem firstLift_ne_secondLift : firstLift k ≠ secondLift k := by
  intro h
  have h' : CommRingCat.ofHom (AlgHom.fst k k k).toRingHom =
      CommRingCat.ofHom (AlgHom.snd k k k).toRingHom := Spec.map_injective h
  have h10 : (1 : k) = 0 :=
    congrArg (fun φ : CommRingCat.of (k × k) ⟶ CommRingCat.of k ↦ φ.hom (1, 0)) h'
  exact one_ne_zero h10

example {K : Type u} [Field K]
    (g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) :
    Set.Finite {q : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (k × k)) |
      q ≫ splitCover k = g} := by
  exact Scheme.Hom.finite_field_valued_fiber (splitCover k) g

example : LocallyQuasiFinite (splitCover k) := by
  exact Scheme.Hom.locallyQuasiFinite_of_finite_geometric_point_fibers (splitCover k)
    (fun K _ _ g ↦ splitCover_finite_fiber k g)

example :
    ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)),
      Set.Finite {q : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (k × k)) |
        q ≫ splitCover k = g} := by
  exact (Scheme.Hom.locallyQuasiFinite_iff_finite_geometric_point_fibers
    (splitCover k)).mp (by infer_instance)

end AlgebraicGeometry
