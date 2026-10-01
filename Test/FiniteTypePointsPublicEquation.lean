/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.FiniteTypePoints

set_option warningAsError true

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace FiniteTypePointsPublicEquation

private noncomputable def toCompositeObjectIso (K : Type u) [Field K]
    (X : algebraicOver K)
    (F : (((FGAlgCat K)ᵒᵖ)ᵒᵖ ⥤ Type u))
    (e : (algebraicOverPoints K).obj X ≅ F) :
    (algebraicOverInclusion K ⋙
      Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)).obj X ≅ F := by
  rw [← algebraicOverPoints_eq K]
  exact e

private noncomputable def toPublicObjectIso (K : Type u) [Field K]
    (X : algebraicOver K)
    (F : (((FGAlgCat K)ᵒᵖ)ᵒᵖ ⥤ Type u))
    (e : (algebraicOverInclusion K ⋙
      Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)).obj X ≅ F) :
    (algebraicOverPoints K).obj X ≅ F := by
  rw [algebraicOverPoints_eq K]
  exact e

private theorem compositeEssImage_of_public (K : Type u) [Field K]
    (F : (((FGAlgCat K)ᵒᵖ)ᵒᵖ ⥤ Type u))
    (h : (algebraicOverPoints K).essImage F) :
    (algebraicOverInclusion K ⋙
      Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)).essImage F := by
  obtain ⟨X, ⟨e⟩⟩ := h
  exact ⟨X, ⟨toCompositeObjectIso K X F e⟩⟩

private theorem publicEssImage_of_composite (K : Type u) [Field K]
    (F : (((FGAlgCat K)ᵒᵖ)ᵒᵖ ⥤ Type u))
    (h : (algebraicOverInclusion K ⋙
      Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)).essImage F) :
    (algebraicOverPoints K).essImage F := by
  obtain ⟨X, ⟨e⟩⟩ := h
  exact ⟨X, ⟨toPublicObjectIso K X F e⟩⟩

private noncomputable def toUnderlyingObjectIso (K : Type u) [Field K]
    (X : algebraicOver K)
    (F : (((FGAlgCat K)ᵒᵖ)ᵒᵖ ⥤ Type u))
    (e : (algebraicOverPoints K).obj X ≅ F) :
    (Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)).obj X.obj ≅ F := by
  rw [algebraicOverPoints_eq K, Functor.comp_obj, algebraicOverInclusion_obj K X] at e
  exact e

private noncomputable def toPointsObjectIso (K : Type u) [Field K]
    (X : algebraicOver K)
    (F : (((FGAlgCat K)ᵒᵖ)ᵒᵖ ⥤ Type u))
    (e : (Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)).obj X.obj ≅ F) :
    (algebraicOverPoints K).obj X ≅ F := by
  rw [algebraicOverPoints_eq K, Functor.comp_obj, algebraicOverInclusion_obj K X]
  exact e

private theorem underlyingEssImage_of_points (K : Type u) [Field K]
    (F : (((FGAlgCat K)ᵒᵖ)ᵒᵖ ⥤ Type u))
    (h : (algebraicOverPoints K).essImage F) :
    ∃ Y : locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K)),
      QuasiCompact Y.hom ∧
        Nonempty ((Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)).obj Y ≅ F) := by
  obtain ⟨X, ⟨e⟩⟩ := h
  exact ⟨X.obj, X.property, ⟨toUnderlyingObjectIso K X F e⟩⟩

private theorem pointsEssImage_of_underlying (K : Type u) [Field K]
    (F : (((FGAlgCat K)ᵒᵖ)ᵒᵖ ⥤ Type u))
    (h : ∃ Y : locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K)),
      QuasiCompact Y.hom ∧
        Nonempty ((Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)).obj Y ≅ F)) :
    (algebraicOverPoints K).essImage F := by
  obtain ⟨Y, hqc, ⟨e⟩⟩ := h
  let X : algebraicOver K := ⟨Y, hqc⟩
  exact ⟨X, ⟨toPointsObjectIso K X F e⟩⟩

end FiniteTypePointsPublicEquation
