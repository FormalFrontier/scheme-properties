/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import SchemeProperties.Normal
public import SchemeProperties.NormalSections

/-!
# The affine line and its punctured open set

The spectrum of `ℚ[X]` is normal and integral by unique factorization and the
normal-spectrum criterion. Its canonical section, germ and stalk maps take
values in its function field. The principal open `D(X)` is nonempty, and the
empty open set has an intrinsically integrally closed zero ring of sections.

The model witnesses use the polynomial, spectrum, stalk and localization APIs.
The section-image and normal-section theorems are then applied to this model.
-/

open AlgebraicGeometry
open scoped Polynomial

namespace SchemePropertiesTest.NormalSectionsModel

noncomputable section

private abbrev coordinateRing := ℚ[X]

private abbrev affineLine : Scheme := Spec (.of coordinateRing)

private theorem coordinateRing_isIntegrallyClosed : IsIntegrallyClosed coordinateRing :=
  GCDMonoid.toIsIntegrallyClosed

private theorem affineLine_isNormal : IsNormal affineLine := by
  letI := coordinateRing_isIntegrallyClosed
  infer_instance

private theorem affineLine_isIntegral : IsIntegral affineLine := by
  infer_instance

private theorem topOpen_nonempty : Nonempty (⊤ : affineLine.Opens) :=
  ⟨⟨Classical.choice (inferInstance : Nonempty affineLine), trivial⟩⟩

private theorem topSections_isDomain : IsDomain Γ(affineLine, ⊤) := by
  infer_instance

private theorem topSections_isIntegrallyClosed : IsIntegrallyClosed Γ(affineLine, ⊤) := by
  letI := coordinateRing_isIntegrallyClosed
  exact IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of coordinateRing)).symm.commRingCatIsoToRingEquiv

private def topSectionMap : Γ(affineLine, ⊤) →+* affineLine.functionField :=
  letI := topOpen_nonempty
  algebraMap _ _

private def topGerm (x : affineLine) : Γ(affineLine, ⊤) →+* affineLine.presheaf.stalk x :=
  (affineLine.presheaf.germ ⊤ x trivial).hom

private def stalkMap (x : affineLine) : affineLine.presheaf.stalk x →+* affineLine.functionField :=
  algebraMap _ _

private theorem topSectionMap_germ (x : affineLine) (s : Γ(affineLine, ⊤)) :
    stalkMap x (topGerm x s) = topSectionMap s := by
  letI := topOpen_nonempty
  exact affineLine.algebraMap_germ_eq_germToFunctionField (U := ⊤) (by trivial) s

private abbrev puncturedLine : affineLine.Opens :=
  PrimeSpectrum.basicOpen (Polynomial.X : coordinateRing)

private theorem puncturedLine_nonempty : Nonempty puncturedLine := by
  refine ⟨⟨(⊥ : PrimeSpectrum coordinateRing), ?_⟩⟩
  change (Polynomial.X : coordinateRing) ∉ (⊥ : Ideal coordinateRing)
  simpa only [Ideal.mem_bot] using (Polynomial.X_ne_zero : (Polynomial.X : coordinateRing) ≠ 0)

private theorem puncturedLine_isNormal : IsNormal puncturedLine.toScheme := by
  letI := affineLine_isNormal
  infer_instance

private theorem puncturedLine_isIntegral : IsIntegral puncturedLine.toScheme := by
  letI := puncturedLine_nonempty
  infer_instance

private def puncturedSectionMap : Γ(affineLine, puncturedLine) →+* affineLine.functionField :=
  letI := puncturedLine_nonempty
  algebraMap _ _

private theorem emptySections_isIntegrallyClosed : IsIntegrallyClosed Γ(affineLine, ⊥) := by
  letI : Subsingleton Γ(affineLine, ⊥) :=
    CommRingCat.subsingleton_of_isTerminal affineLine.sheaf.isTerminalOfEmpty
  letI : Unique (FractionRing Γ(affineLine, ⊥)) := FractionRing.unique _
  apply isIntegrallyClosedIn_iff.mpr
  constructor
  · intro a b _
    exact Subsingleton.elim a b
  · intro x _
    exact ⟨0, Subsingleton.elim _ _⟩

private theorem coordinateFunction_mem_stalkMap_range :
    ∀ x : (⊤ : affineLine.Opens),
      topSectionMap ((Scheme.ΓSpecIso (.of coordinateRing)).inv
        (Polynomial.X : coordinateRing)) ∈ Set.range (stalkMap x.1) := by
  letI := affineLine_isIntegral
  letI := topOpen_nonempty
  exact (Scheme.mem_range_algebraMap_functionField_iff (X := affineLine) ⊤
    (topSectionMap ((Scheme.ΓSpecIso (.of coordinateRing)).inv
      (Polynomial.X : coordinateRing)))).mp
    ⟨(Scheme.ΓSpecIso (.of coordinateRing)).inv (Polynomial.X : coordinateRing), rfl⟩

private theorem puncturedSectionMap_preimage_of_integral (f : affineLine.functionField)
    (hf : puncturedSectionMap.IsIntegralElem f) :
    ∃ s : Γ(affineLine, puncturedLine), puncturedSectionMap s = f := by
  letI := affineLine_isNormal
  letI := affineLine_isIntegral
  letI := puncturedLine_nonempty
  exact (isIntegrallyClosedIn_iff.mp
    (IsNormal.isIntegrallyClosedIn_sections (X := affineLine) puncturedLine)).2 hf

private theorem topFraction_preimage_of_integral (f : FractionRing Γ(affineLine, ⊤))
    (hf : _root_.IsIntegral Γ(affineLine, ⊤) f) :
    ∃ s : Γ(affineLine, ⊤), algebraMap Γ(affineLine, ⊤)
      (FractionRing Γ(affineLine, ⊤)) s = f := by
  letI := affineLine_isNormal
  letI := affineLine_isIntegral
  letI : IsIntegrallyClosed Γ(affineLine, ⊤) :=
    IsNormal.isIntegrallyClosed_sections (X := affineLine) ⊤
  exact IsIntegrallyClosed.algebraMap_eq_of_integral hf

private theorem emptyFraction_preimage_of_integral (f : FractionRing Γ(affineLine, ⊥))
    (hf : _root_.IsIntegral Γ(affineLine, ⊥) f) :
    ∃ s : Γ(affineLine, ⊥), algebraMap Γ(affineLine, ⊥)
      (FractionRing Γ(affineLine, ⊥)) s = f := by
  letI := affineLine_isNormal
  letI := affineLine_isIntegral
  exact (isIntegrallyClosedIn_iff.mp
    (IsNormal.isIntegrallyClosed_sections (X := affineLine) ⊥)).2 hf

end

end SchemePropertiesTest.NormalSectionsModel
