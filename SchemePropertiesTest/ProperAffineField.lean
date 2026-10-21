/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.ProperAffineField
public import Mathlib.Algebra.Field.ZMod

/-!
# The identity of the two-element field spectrum

The spectrum of the two-element field and its identity morphism give a nonempty proper affine
preconnected example. Its properties come from Mathlib's field-spectrum and identity-morphism
instances, independently of the point criteria. The two criteria are then instantiated separately.

Mathlib's scheme and prime-spectrum constructions are due to Kim Morrison, Johan Commelin,
Filippo A. E. Nuccio and Andrew Yang; its prime residue field instance is due to Chris Hughes.
The morphism and topology interfaces are credited in the imported module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

private abbrev twoElementFieldSpectrum : Scheme := Spec (CommRingCat.of (ZMod 2))

private abbrev twoElementFieldIdentity :
    twoElementFieldSpectrum ⟶ Spec (CommRingCat.of (ZMod 2)) := 𝟙 _

/-- The two-element field spectrum identity satisfies the geometric hypotheses and has a point,
using only field-spectrum and identity-morphism instances. -/
theorem twoElementField_identity_properties :
    IsProper (𝟙 (Spec (CommRingCat.of (ZMod 2)))) ∧ IsAffine (Spec (CommRingCat.of (ZMod 2))) ∧
      PreconnectedSpace (Spec (CommRingCat.of (ZMod 2))) ∧
      Nonempty (Spec (CommRingCat.of (ZMod 2))) := by
  exact ⟨inferInstanceAs (IsProper twoElementFieldIdentity),
    inferInstanceAs (IsAffine twoElementFieldSpectrum),
    inferInstanceAs (PreconnectedSpace twoElementFieldSpectrum),
    inferInstanceAs (Nonempty twoElementFieldSpectrum)⟩

/-- The locally quasi-finite criterion applies to the identity of the two-element field spectrum. -/
theorem twoElementField_locallyQuasiFinite_criterion :
    Subsingleton (Spec (CommRingCat.of (ZMod 2))) :=
  subsingleton_of_locallyQuasiFinite (𝟙 (Spec (CommRingCat.of (ZMod 2))))

/-- The proper affine field criterion applies to the identity of the two-element field spectrum. -/
theorem twoElementField_properAffine_criterion :
    Subsingleton (Spec (CommRingCat.of (ZMod 2))) :=
  subsingleton_of_isProper_of_isAffine (𝟙 (Spec (CommRingCat.of (ZMod 2))))

end AlgebraicGeometry.Scheme.Hom
