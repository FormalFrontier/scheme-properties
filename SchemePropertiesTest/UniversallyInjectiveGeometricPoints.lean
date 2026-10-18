/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import SchemeProperties.UniversallyInjectiveGeometricPoints

/-!
# Geometric-point injectivity of the origin in the affine line

The canonical origin `Spec k → Spec k[t]` is a closed immersion. The universal
injectivity criterion therefore gives injectivity on algebraically closed
field-valued points. The application uses Mathlib's polynomial evaluation and
closed-immersion APIs, the latter by Amelia Livingston, Christian Merten and
Jonas van der Schaaf.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry

private theorem origin_injective_geometricPoints (k : Type u) [Field k] :
    ∀ (K : Type u) [Field K] [IsAlgClosed K],
      Function.Injective (fun g : Spec (.of K) ⟶ Spec (.of k) ↦
        g ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)))) := by
  haveI : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)))) :=
    IsClosedImmersion.spec_of_surjective _ (Polynomial.eval_surjective (0 : k))
  exact (universallyInjective_iff_injective_geometricPoints _).mp inferInstance

end AlgebraicGeometry
