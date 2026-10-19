/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Ring.PUnit
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import SchemeProperties.GlobalSections.Field

/-!
# Global sections over a field: examples

The spectrum of `ULift K`, with its structure map and section induced by
`ULift.ringEquiv`, instantiates both reduced-source global-sections results.
Its reducedness, connectedness, universal closedness and section equation are
established first. The integral-source theorem and the global-sections functor
also give the two conclusions independently. This affine isomorphic example
witnesses inhabitance, not the additional nonaffine or reducible generality.

The spectrum of the zero ring is reduced, preconnected and universally closed
over `K`, but empty. Its sections are not a field, and it has no `K`-section.
Thus preconnectedness alone cannot replace connectedness in the field result;
the section hypothesis excludes this boundary in the pointed result.

## References

The lifted-field and zero-ring examples follow constructions by Formal Frontier
Agents and use Mathlib's lifted-ring, zero-ring, spectrum and global-sections
APIs, notably Andrew Yang's universally closed morphism results.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- On an integral scheme, the reduced connected field criterion agrees with
Mathlib's integral-source criterion. -/
private theorem isField_globalSections_of_universallyClosed_eq_of_isIntegral
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [UniversallyClosed f] :
    isField_globalSections_of_universallyClosed K f =
      isField_of_universallyClosed K f := by
  exact Subsingleton.elim _ _

/-! ## The spectrum of a lifted field -/

private def liftedFieldRingIso (K : Type u) [Field K] :
    CommRingCat.of (ULift.{u} K) ≅ CommRingCat.of K :=
  (ULift.ringEquiv : ULift.{u} K ≃+* K).toCommRingCatIso

private def liftedFieldMap (K : Type u) [Field K] :
    Spec (.of (ULift.{u} K)) ⟶ Spec (.of K) :=
  Spec.map (liftedFieldRingIso K).inv

private def liftedFieldPoint (K : Type u) [Field K] :
    Spec (.of K) ⟶ Spec (.of (ULift.{u} K)) :=
  Spec.map (liftedFieldRingIso K).hom

private theorem liftedField_section (K : Type u) [Field K] :
    liftedFieldPoint K ≫ liftedFieldMap K = 𝟙 _ := by
  change Spec.map (liftedFieldRingIso K).hom ≫
    Spec.map (liftedFieldRingIso K).inv = 𝟙 _
  rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]

private theorem liftedField_integral (K : Type u) [Field K] :
    IsIntegral (Spec (.of (ULift.{u} K))) := by
  infer_instance

private theorem liftedField_reduced (K : Type u) [Field K] :
    AlgebraicGeometry.IsReduced (Spec (.of (ULift.{u} K))) := by
  letI := liftedField_integral K
  infer_instance

private theorem liftedField_connected (K : Type u) [Field K] :
    ConnectedSpace (Spec (.of (ULift.{u} K))) := by
  letI := liftedField_integral K
  infer_instance

private theorem liftedField_isIso (K : Type u) [Field K] :
    IsIso (liftedFieldMap K) :=
  inferInstanceAs (IsIso (Spec.map (liftedFieldRingIso K).inv))

private theorem liftedField_universallyClosed (K : Type u) [Field K] :
    UniversallyClosed (liftedFieldMap K) := by
  letI := liftedField_isIso K
  infer_instance

/-- The lifted spectrum has a field of sections by the integral-source result. -/
private theorem liftedField_sections_isField (K : Type u) [Field K] :
    _root_.IsField Γ(Spec (.of (ULift.{u} K)), ⊤) := by
  letI := liftedField_integral K
  exact isField_of_universallyClosed (ULift.{u} K) (𝟙 _)

/-- The lifted map induces an isomorphism on sections because it is an isomorphism. -/
private theorem liftedField_appTop_isIso (K : Type u) [Field K] :
    IsIso (liftedFieldMap K).appTop := by
  letI := liftedField_isIso K
  rw [← Scheme.Γ_map_op]
  exact Scheme.Γ.map_isIso (liftedFieldMap K).op

/-! ## The spectrum of the zero ring -/

private abbrev zeroSpectrum : Scheme.{u} :=
  Spec (CommRingCat.of.{u} PUnit)

private def zeroRingMap (K : Type u) [Field K] :
    CommRingCat.of K ⟶ CommRingCat.of.{u} PUnit :=
  default

private def zeroStructureMap (K : Type u) [Field K] :
    zeroSpectrum.{u} ⟶ Spec (.of K) :=
  Spec.map (zeroRingMap K)

private theorem zeroRingMap_surjective (K : Type u) [Field K] :
    Function.Surjective (zeroRingMap K) := by
  intro y
  exact ⟨0, Subsingleton.elim _ _⟩

private theorem zeroSpectrum_isEmpty : IsEmpty zeroSpectrum.{u} := by
  infer_instance

private theorem zeroSpectrum_reduced :
    AlgebraicGeometry.IsReduced zeroSpectrum.{u} := by
  infer_instance

private theorem zeroSpectrum_preconnected : PreconnectedSpace zeroSpectrum.{u} := by
  letI := zeroSpectrum_isEmpty.{u}
  infer_instance

private theorem zeroStructureMap_closedImmersion (K : Type u) [Field K] :
    IsClosedImmersion (zeroStructureMap K) :=
  IsClosedImmersion.spec_of_surjective (zeroRingMap K) (zeroRingMap_surjective K)

private theorem zeroStructureMap_universallyClosed (K : Type u) [Field K] :
    UniversallyClosed (zeroStructureMap K) := by
  letI := zeroStructureMap_closedImmersion K
  infer_instance

private theorem zeroSpectrum_sections_subsingleton :
    Subsingleton Γ(zeroSpectrum.{u}, ⊤) := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of.{u} PUnit)).commRingCatIsoToRingEquiv
  exact ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩

private theorem zeroSpectrum_sections_not_isField :
    ¬ _root_.IsField Γ(zeroSpectrum.{u}, ⊤) := by
  letI := zeroSpectrum_sections_subsingleton.{u}
  intro h
  obtain ⟨a, b, hab⟩ := h.exists_pair_ne
  exact hab (Subsingleton.elim _ _)

private theorem zeroStructureMap_no_section (K : Type u) [Field K] :
    ¬ ∃ p : Spec (.of K) ⟶ zeroSpectrum.{u}, p ≫ zeroStructureMap K = 𝟙 _ := by
  letI := zeroSpectrum_isEmpty.{u}
  rintro ⟨p, _⟩
  obtain ⟨x⟩ := (inferInstance : Nonempty (Spec (.of K)))
  exact isEmptyElim (p x)

/-! ## The reduced-source results on the lifted spectrum -/

example (K : Type u) [Field K] :
    _root_.IsField Γ(Spec (.of (ULift.{u} K)), ⊤) := by
  letI := liftedField_reduced K
  letI := liftedField_connected K
  letI := liftedField_universallyClosed K
  exact isField_globalSections_of_universallyClosed K (liftedFieldMap K)

example (K : Type u) [Field K] : IsIso (liftedFieldMap K).appTop := by
  letI := liftedField_reduced K
  letI := liftedField_connected K
  letI := liftedField_universallyClosed K
  exact Scheme.Hom.isIso_appTop_of_isReduced_of_universallyClosed_of_section
    (liftedFieldMap K) (liftedFieldPoint K) (liftedField_section K)

/-! ## Empty preconnected sources do not suffice -/

example (K : Type u) [Field K] :
    AlgebraicGeometry.IsReduced zeroSpectrum.{u} ∧
      PreconnectedSpace zeroSpectrum.{u} ∧
      IsEmpty zeroSpectrum.{u} ∧
      UniversallyClosed (zeroStructureMap K) ∧
      ¬ _root_.IsField Γ(zeroSpectrum.{u}, ⊤) ∧
      ¬ ∃ p : Spec (.of K) ⟶ zeroSpectrum.{u}, p ≫ zeroStructureMap K = 𝟙 _ := by
  exact ⟨zeroSpectrum_reduced, zeroSpectrum_preconnected, zeroSpectrum_isEmpty,
    zeroStructureMap_universallyClosed K, zeroSpectrum_sections_not_isField,
    zeroStructureMap_no_section K⟩

end AlgebraicGeometry
