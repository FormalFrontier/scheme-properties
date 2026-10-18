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

noncomputable example (K : Type u) [Field K]
    (X : algebraicOver K)
    (F : (((FGAlgCat K)ᵒᵖ)ᵒᵖ ⥤ Type u))
    (e : (algebraicOverPoints K).obj X ≅ F) :
    (algebraicOverInclusion K ⋙
      Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)).obj X ≅ F := by
  rw [← algebraicOverPoints_eq K]
  exact e

noncomputable example (K : Type u) [Field K]
    (X : algebraicOver K)
    (F : (((FGAlgCat K)ᵒᵖ)ᵒᵖ ⥤ Type u))
    (e : (algebraicOverInclusion K ⋙
      Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)).obj X ≅ F) :
    (algebraicOverPoints K).obj X ≅ F := by
  rw [algebraicOverPoints_eq K]
  exact e

example (K : Type u) [Field K]
    (F : (((FGAlgCat K)ᵒᵖ)ᵒᵖ ⥤ Type u))
    (h : (algebraicOverPoints K).essImage F) :
    (algebraicOverInclusion K ⋙
      Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)).essImage F := by
  obtain ⟨X, ⟨e⟩⟩ := h
  have iso : (algebraicOverInclusion K ⋙
      Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)).obj X ≅ F := by
    rw [← algebraicOverPoints_eq K]
    exact e
  exact ⟨X, ⟨iso⟩⟩

example (K : Type u) [Field K]
    (F : (((FGAlgCat K)ᵒᵖ)ᵒᵖ ⥤ Type u))
    (h : (algebraicOverInclusion K ⋙
      Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)).essImage F) :
    (algebraicOverPoints K).essImage F := by
  obtain ⟨X, ⟨e⟩⟩ := h
  have iso : (algebraicOverPoints K).obj X ≅ F := by
    rw [algebraicOverPoints_eq K]
    exact e
  exact ⟨X, ⟨iso⟩⟩

noncomputable example (K : Type u) [Field K]
    (X : algebraicOver K)
    (F : (((FGAlgCat K)ᵒᵖ)ᵒᵖ ⥤ Type u))
    (e : (algebraicOverPoints K).obj X ≅ F) :
    (Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)).obj X.obj ≅ F := by
  rw [algebraicOverPoints_eq K, Functor.comp_obj, algebraicOverInclusion_obj K X] at e
  exact e

noncomputable example (K : Type u) [Field K]
    (X : algebraicOver K)
    (F : (((FGAlgCat K)ᵒᵖ)ᵒᵖ ⥤ Type u))
    (e : (Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)).obj X.obj ≅ F) :
    (algebraicOverPoints K).obj X ≅ F := by
  rw [algebraicOverPoints_eq K, Functor.comp_obj, algebraicOverInclusion_obj K X]
  exact e

example (K : Type u) [Field K]
    (F : (((FGAlgCat K)ᵒᵖ)ᵒᵖ ⥤ Type u))
    (h : (algebraicOverPoints K).essImage F) :
    ∃ Y : locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K)),
      QuasiCompact Y.hom ∧
        Nonempty ((Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)).obj Y ≅ F) := by
  obtain ⟨X, ⟨e⟩⟩ := h
  have iso : (Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)).obj X.obj ≅ F := by
    rw [algebraicOverPoints_eq K, Functor.comp_obj, algebraicOverInclusion_obj K X] at e
    exact e
  exact ⟨X.obj, X.property, ⟨iso⟩⟩

example (K : Type u) [Field K]
    (F : (((FGAlgCat K)ᵒᵖ)ᵒᵖ ⥤ Type u))
    (h : ∃ Y : locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K)),
      QuasiCompact Y.hom ∧
        Nonempty ((Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)).obj Y ≅ F)) :
    (algebraicOverPoints K).essImage F := by
  obtain ⟨Y, hqc, ⟨e⟩⟩ := h
  let X : algebraicOver K := ⟨Y, hqc⟩
  have iso : (algebraicOverPoints K).obj X ≅ F := by
    rw [algebraicOverPoints_eq K, Functor.comp_obj, algebraicOverInclusion_obj K X]
    exact e
  exact ⟨X, ⟨iso⟩⟩

end FiniteTypePointsPublicEquation
