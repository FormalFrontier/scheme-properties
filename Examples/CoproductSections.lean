module

import SchemeProperties.CoproductSections

/-! # Client checks for sections on coproducts of schemes -/

set_option warningAsError true

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.CoproductSectionsClient

noncomputable section

variable {ι : Type u} (X : ι → Scheme.{u})

private def check_1 (U : (∐ X : Scheme.{u}).Opens) :
    Γ(∐ X, U) ≅ ↧((i : ι) → Γ(X i, Sigma.ι X i ⁻¹ᵁ U)) :=
  Scheme.sigmaPresheafObjIso X U

private theorem check_2 (U : (∐ X : Scheme.{u}).Opens) (s : Γ(∐ X, U)) (i : ι) :
    (Scheme.sigmaPresheafObjIso X U).hom s i = (Sigma.ι X i).app U s := by
  exact Scheme.sigmaPresheafObjIso_hom_apply X U s i

private theorem check_3 {V U : (∐ X : Scheme.{u}).Opens} (hVU : V ≤ U)
    (s : Γ(∐ X, U)) (i : ι) :
    (Scheme.sigmaPresheafObjIso X V).hom
        ((∐ X : Scheme.{u}).presheaf.map (homOfLE hVU).op s) i =
      (X i).presheaf.map (homOfLE ((Sigma.ι X i).preimage_mono hVU)).op
        ((Scheme.sigmaPresheafObjIso X U).hom s i) := by
  exact Scheme.sigmaPresheafObjIso_hom_res_apply X hVU s i

private theorem check_4 (U : (∐ X : Scheme.{u}).Opens) (s : Γ(∐ X, U)) (i : ι) :
    Sigma.ι X i ⁻¹ᵁ (∐ X : Scheme.{u}).basicOpen s =
      (X i).basicOpen ((Scheme.sigmaPresheafObjIso X U).hom s i) := by
  calc
    _ = (X i).basicOpen ((Sigma.ι X i).app U s) :=
      Scheme.preimage_basicOpen (Sigma.ι X i) s
    _ = _ := congrArg ((X i).basicOpen ·)
      (Scheme.sigmaPresheafObjIso_hom_apply X U s i).symm

private theorem check_5 (U : (∐ X : Scheme.{u}).Opens) (s : Γ(∐ X, U)) (i : ι) :
    (Scheme.sigmaPresheafObjIso X ((∐ X : Scheme.{u}).basicOpen s)).hom
        ((∐ X : Scheme.{u}).presheaf.map
          (homOfLE ((∐ X : Scheme.{u}).basicOpen_le s)).op s) i =
      (X i).presheaf.map
        (homOfLE ((Sigma.ι X i).preimage_mono
          ((∐ X : Scheme.{u}).basicOpen_le s))).op
        ((Scheme.sigmaPresheafObjIso X U).hom s i) := by
  exact Scheme.sigmaPresheafObjIso_hom_res_apply X
    ((∐ X : Scheme.{u}).basicOpen_le s) s i

end

end AlgebraicGeometry.CoproductSectionsClient
