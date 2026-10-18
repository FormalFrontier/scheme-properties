/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.FieldExtensionLifting
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Field-extension lifting for algebraic-closure spectra

For every field `K`, the map `Spec (AlgebraicClosure K) ⟶ Spec K` is surjective.
Independently of the field-extension lifting theorems, every field-valued point of
`Spec K` lifts through this map after extending its supplied field to its algebraic
closure. The scalar structure used for the lift comes from that supplied point.
These two independent inputs exercise each of the three lifting theorems.

Although both spectra have a unique point, this is not an identity-only family:
for `K = ℚ`, the algebraic closure is a proper field extension. Algebraically closed
`K` is also allowed. The use of algebraic closures here is a choice of example,
not an algebraicity restriction on extensions in the general lifting theorems.
No chosen embedding is packaged in a new public construction: `IsAlgClosed.lift`
already supplies the algebra homomorphism used below.
-/

open CategoryTheory

namespace AlgebraicGeometry

universe u

-- Field spectra are inhabited and subsingleton, independently of any lifting theorem.
private instance algebraicClosure_surjective (K : Type u) [Field K] :
    Surjective (Spec.algebraMap K (AlgebraicClosure K)) := by
  have : Nonempty (Spec (CommRingCat.of (AlgebraicClosure K))) := inferInstance
  have : Subsingleton (Spec (CommRingCat.of K)) := inferInstance
  exact ⟨Function.surjective_to_subsingleton _⟩

-- This proof supplies the universal input for the converse, without using a headline.
private theorem algebraicClosure_lifts (K : Type u) [Field K] {R : Type u} [Field R]
    (g : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) :
    ∃ L : CommRingCat.{u}, IsField L ∧
      ∃ (i : CommRingCat.of R ⟶ L) (q : Spec L ⟶ Spec (CommRingCat.of (AlgebraicClosure K))),
        q ≫ Spec.algebraMap K (AlgebraicClosure K) = Spec.map i ≫ g := by
  let α : K →+* R := (Spec.preimage g).hom
  let : Algebra K (AlgebraicClosure R) :=
    ((algebraMap R (AlgebraicClosure R)).comp α).toAlgebra
  let β : AlgebraicClosure K →ₐ[K] AlgebraicClosure R := IsAlgClosed.lift
  refine ⟨CommRingCat.of (AlgebraicClosure R), Field.toIsField (AlgebraicClosure R),
    CommRingCat.ofHom (algebraMap R (AlgebraicClosure R)),
    Spec.map (CommRingCat.ofHom β.toRingHom), ?_⟩
  have hring : β.toRingHom.comp (algebraMap K (AlgebraicClosure K)) =
      (algebraMap R (AlgebraicClosure R)).comp α := by
    calc
      _ = algebraMap K (AlgebraicClosure R) := β.comp_algebraMap
      _ = _ := RingHom.algebraMap_toAlgebra _
  have hcat :
      CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)) ≫
          CommRingCat.ofHom β.toRingHom =
        Spec.preimage g ≫ CommRingCat.ofHom (algebraMap R (AlgebraicClosure R)) := by
    apply CommRingCat.hom_ext
    simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] using hring
  calc
    Spec.map (CommRingCat.ofHom β.toRingHom) ≫
        Spec.algebraMap K (AlgebraicClosure K) =
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)) ≫
        CommRingCat.ofHom β.toRingHom) := (Spec.map_comp _ _).symm
    _ = Spec.map (Spec.preimage g ≫
        CommRingCat.ofHom (algebraMap R (AlgebraicClosure R))) := congrArg Spec.map hcat
    _ = Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure R))) ≫ g := by
      rw [Spec.map_comp, Spec.map_preimage]

private theorem algebraicClosure_lifts_of_surjective (K R : Type u) [Field K] [Field R]
    (g : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) :
    ∃ L : CommRingCat.{u}, IsField L ∧
      ∃ (i : CommRingCat.of R ⟶ L) (q : Spec L ⟶ Spec (CommRingCat.of (AlgebraicClosure K))),
        q ≫ Spec.algebraMap K (AlgebraicClosure K) = Spec.map i ≫ g := by
  exact Scheme.Hom.exists_lift_after_field_extension
    (Spec.algebraMap K (AlgebraicClosure K)) g

private theorem algebraicClosure_surjective_of_lifts (K : Type u) [Field K] :
    Surjective (Spec.algebraMap K (AlgebraicClosure K)) := by
  apply Scheme.Hom.surjective_of_lifts_after_field_extension
    (Spec.algebraMap K (AlgebraicClosure K))
  intro R _ g
  exact algebraicClosure_lifts K g

private theorem algebraicClosure_lifts_via_iff (K R : Type u) [Field K] [Field R]
    (g : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) :
    ∃ L : CommRingCat.{u}, IsField L ∧
      ∃ (i : CommRingCat.of R ⟶ L) (q : Spec L ⟶ Spec (CommRingCat.of (AlgebraicClosure K))),
        q ≫ Spec.algebraMap K (AlgebraicClosure K) = Spec.map i ≫ g := by
  exact ((Scheme.Hom.surjective_iff_lifts_after_field_extension
    (Spec.algebraMap K (AlgebraicClosure K))).mp
      (inferInstance : Surjective (Spec.algebraMap K (AlgebraicClosure K)))) R g

end AlgebraicGeometry
