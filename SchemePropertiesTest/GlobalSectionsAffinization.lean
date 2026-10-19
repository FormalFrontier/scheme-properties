/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.GlobalSections

/-!
# Morphisms from the affinization to affine schemes

For any scheme `X`, the canonical morphism `X.toSpecΓ : X ⟶ Spec Γ(X, ⊤)` induces
an isomorphism on global sections. Precomposition with this morphism therefore
identifies morphisms from `Spec Γ(X, ⊤)` to an affine scheme `T` with morphisms
from `X` to `T`, without requiring `X` to be affine.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace SchemePropertiesTest.GlobalSectionsAffinization

example (X T : Scheme.{u}) [IsAffine T] :
    Function.Bijective (fun h : Spec Γ(X, ⊤) ⟶ T ↦ X.toSpecΓ ≫ h) := by
  letI : IsIso X.toSpecΓ.appTop := by
    rw [Scheme.toSpecΓ_appTop]
    infer_instance
  exact Scheme.Hom.precomp_bijective_of_isIso_appTop X.toSpecΓ

end SchemePropertiesTest.GlobalSectionsAffinization
