module

import SchemeProperties

/-! # Aggregate-root client checks for sections on coproducts -/

set_option warningAsError true

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.CoproductSectionsRootClient

noncomputable section

variable {ι : Type u} (X : ι → Scheme.{u})

private def check_1 (U : (∐ X : Scheme.{u}).Opens) :
    Γ(∐ X, U) ≅ ↧((i : ι) → Γ(X i, Sigma.ι X i ⁻¹ᵁ U)) :=
  Scheme.sigmaPresheafObjIso X U

private theorem check_2 {V U : (∐ X : Scheme.{u}).Opens} (hVU : V ≤ U)
    (s : Γ(∐ X, U)) (i : ι) :
    (Scheme.sigmaPresheafObjIso X V).hom
        ((∐ X : Scheme.{u}).presheaf.map (homOfLE hVU).op s) i =
      (X i).presheaf.map (homOfLE ((Sigma.ι X i).preimage_mono hVU)).op
        ((Scheme.sigmaPresheafObjIso X U).hom s i) := by
  exact Scheme.sigmaPresheafObjIso_hom_res_apply X hVU s i

end

end AlgebraicGeometry.CoproductSectionsRootClient
