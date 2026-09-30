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

end FiniteTypePointsPublicEquation
