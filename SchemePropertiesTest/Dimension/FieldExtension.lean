/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.Dimension.FieldExtension
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.FiniteType

/-!
# Examples of dimension preservation under field extension

The spectrum of the zero ring, finite-variable polynomial spectra and their
countable coproduct carry specified scalar structures and structure morphisms.
The polynomial examples have the origin as a section. Local finite type of the
coproduct map follows on its component open cover. The polynomial base-change
comparison with the tensor-product spectrum records both projections.

Each example applies both dimension-preservation theorems from
`SchemeProperties.Dimension.FieldExtension`, using the same canonical pullbacks.
All declarations in this module are private.

## References and credit

Mathlib supplies the scheme, spectrum, pullback, coproduct, finite-type, polynomial
evaluation and PUnit/algebra interfaces. The scheme/Spec formalization is due to
Kim Morrison and Mathlib contributors; the pullback, coproduct and finite-type
interfaces are due to Andrew Yang and Mathlib contributors. The algebra finiteness
interface is due to Johan Commelin; polynomial evaluation credits Johannes Hölzl,
Johan Commelin and Mario Carneiro. PUnit/algebra interfaces credit Kenny Lau and
Yury Kudryashov. The dimension comparisons reuse Scheme Properties, whose proof
combines the tensor-field dimension and open-cover supremum theorems of Minimal
Primes with Mathlib's scheme interfaces.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

-- All subsequent declarations are private mathematical examples and their laws.

private abbrev extensionMap :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K L))

private abbrev emptySpectrum : Scheme.{u} :=
  Spec (CommRingCat.of PUnit.{u + 1})

private abbrev emptyStructure : emptySpectrum.{u} ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K PUnit.{u + 1}))

private instance emptyStructure_locallyOfFiniteType :
    LocallyOfFiniteType (emptyStructure K) := by
  apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
  exact RingHom.FiniteType.of_surjective _ (fun x ↦ ⟨0, Subsingleton.elim _ x⟩)

private theorem emptySpectrum_isEmpty : IsEmpty emptySpectrum.{u} :=
  spec_punit_isEmpty

private abbrev emptyBaseChange : Scheme.{u} :=
  Limits.pullback (emptyStructure K) (extensionMap K L)

private theorem emptyBaseChange_isEmpty : IsEmpty (emptyBaseChange K L) := by
  exact ⟨fun x ↦ isEmptyElim
    (pullback.fst (emptyStructure K) (extensionMap K L) x)⟩

private theorem emptyBaseChange_condition :
    pullback.fst (emptyStructure K) (extensionMap K L) ≫ emptyStructure K =
      pullback.snd (emptyStructure K) (extensionMap K L) ≫ extensionMap K L :=
  pullback.condition

private abbrev polynomialSpectrum (n : ℕ) : Scheme.{u} :=
  Spec (CommRingCat.of (MvPolynomial (Fin n) K))

private abbrev polynomialStructure (n : ℕ) :
    polynomialSpectrum K n ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin n) K)))

private instance polynomialStructure_locallyOfFiniteType (n : ℕ) :
    LocallyOfFiniteType (polynomialStructure K n) := by
  apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
  exact RingHom.finiteType_algebraMap.mpr inferInstance

private def polynomialOrigin (n : ℕ) :
    Spec (CommRingCat.of K) ⟶ polynomialSpectrum K n :=
  Spec.map (CommRingCat.ofHom
    (MvPolynomial.eval₂Hom (RingHom.id K) (fun _ : Fin n ↦ (0 : K))))

private theorem polynomialOrigin_structure (n : ℕ) :
    polynomialOrigin K n ≫ polynomialStructure K n = 𝟙 (Spec (CommRingCat.of K)) := by
  unfold polynomialOrigin polynomialStructure
  rw [← Spec.map_comp]
  have h :
      CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin n) K)) ≫
        CommRingCat.ofHom
          (MvPolynomial.eval₂Hom (RingHom.id K) (fun _ : Fin n ↦ (0 : K))) =
        𝟙 (CommRingCat.of K) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact MvPolynomial.eval₂Hom_C (RingHom.id K) (fun _ : Fin n ↦ (0 : K)) a
  rw [h, Spec.map_id]

private abbrev polynomialBaseChange (n : ℕ) : Scheme.{u} :=
  Limits.pullback (polynomialStructure K n) (extensionMap K L)

private instance polynomialBaseChange_locallyOfFiniteType (n : ℕ) :
    LocallyOfFiniteType (pullback.snd (polynomialStructure K n) (extensionMap K L)) := by
  infer_instance

private def polynomialBaseChangeSpecIso (n : ℕ) :
    polynomialBaseChange K L n ≅
      Spec (CommRingCat.of (MvPolynomial (Fin n) K ⊗[K] L)) :=
  pullbackSpecIso K (MvPolynomial (Fin n) K) L

private theorem polynomialBaseChangeSpecIso_inv_fst (n : ℕ) :
    (polynomialBaseChangeSpecIso K L n).inv ≫
        pullback.fst (polynomialStructure K n) (extensionMap K L) =
      Spec.map (CommRingCat.ofHom
        (algebraMap (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K ⊗[K] L))) :=
  pullbackSpecIso_inv_fst' K (MvPolynomial (Fin n) K) L

private theorem polynomialBaseChangeSpecIso_inv_snd (n : ℕ) :
    (polynomialBaseChangeSpecIso K L n).inv ≫
        pullback.snd (polynomialStructure K n) (extensionMap K L) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight :
          L →ₐ[K] (MvPolynomial (Fin n) K ⊗[K] L)).toRingHom) :=
  pullbackSpecIso_inv_snd K (MvPolynomial (Fin n) K) L

private abbrev polynomialCoproduct : Scheme.{u} :=
  ∐ (fun n : ℕ ↦ polynomialSpectrum K n)

private def polynomialCoproductStructure :
    polynomialCoproduct K ⟶ Spec (CommRingCat.of K) :=
  Sigma.desc (fun n : ℕ ↦ polynomialStructure K n)

private theorem polynomialCoproductStructure_component (n : ℕ) :
    Sigma.ι (fun n : ℕ ↦ polynomialSpectrum K n) n ≫ polynomialCoproductStructure K =
      polynomialStructure K n :=
  Sigma.ι_desc (fun n : ℕ ↦ polynomialStructure K n) n

private instance polynomialCoproductStructure_locallyOfFiniteType :
    LocallyOfFiniteType (polynomialCoproductStructure K) := by
  let : IsZariskiLocalAtSource
      (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource
      (P := (@LocallyOfFiniteType : MorphismProperty Scheme.{u}))
      (Q := RingHom.FiniteType)
      (inferInstanceAs
        (HasRingHomProperty (@LocallyOfFiniteType : MorphismProperty Scheme.{u})
          RingHom.FiniteType))
  change LocallyOfFiniteType (Sigma.desc (fun n : ℕ ↦ polynomialStructure K n))
  exact IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFiniteType)
    (fun (n : ℕ) ↦
      inferInstanceAs (LocallyOfFiniteType (polynomialStructure K n)))

private abbrev polynomialCoproductBaseChange : Scheme.{u} :=
  Limits.pullback (polynomialCoproductStructure K) (extensionMap K L)

-- These comparisons use the specified structure maps and canonical pullbacks.

private theorem empty_dimension_comparison :
    topologicalKrullDim (emptyBaseChange K L) = topologicalKrullDim emptySpectrum.{u} :=
  Scheme.topologicalKrullDim_pullback_field K L (emptyStructure K)

private theorem polynomial_dimension_comparison (n : ℕ) :
    topologicalKrullDim (polynomialBaseChange K L n) =
      topologicalKrullDim (polynomialSpectrum K n) :=
  Scheme.topologicalKrullDim_pullback_field K L (polynomialStructure K n)

private theorem polynomialCoproduct_dimension_comparison :
    topologicalKrullDim (polynomialCoproductBaseChange K L) =
      topologicalKrullDim (polynomialCoproduct K) :=
  Scheme.topologicalKrullDim_pullback_field K L (polynomialCoproductStructure K)

private theorem empty_dimension_comparison_of_isField :
    topologicalKrullDim (emptyBaseChange K L) = topologicalKrullDim emptySpectrum.{u} :=
  Scheme.topologicalKrullDim_pullback_of_isField
    (globalSections_spec_isField K) (globalSections_spec_isField L)
    (emptyStructure K) (extensionMap K L)

private theorem polynomial_dimension_comparison_of_isField (n : ℕ) :
    topologicalKrullDim (polynomialBaseChange K L n) =
      topologicalKrullDim (polynomialSpectrum K n) :=
  Scheme.topologicalKrullDim_pullback_of_isField
    (globalSections_spec_isField K) (globalSections_spec_isField L)
    (polynomialStructure K n) (extensionMap K L)

private theorem polynomialCoproduct_dimension_comparison_of_isField :
    topologicalKrullDim (polynomialCoproductBaseChange K L) =
      topologicalKrullDim (polynomialCoproduct K) :=
  Scheme.topologicalKrullDim_pullback_of_isField
    (globalSections_spec_isField K) (globalSections_spec_isField L)
    (polynomialCoproductStructure K) (extensionMap K L)

end AlgebraicGeometry
