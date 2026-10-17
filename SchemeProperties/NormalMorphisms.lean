/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.Normal
public import SchemeProperties.NormalEtale
public import SchemeProperties.NormalFaithfullyFlat
public import SchemeProperties.NormalPolynomial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Stalk

@[expose] public section

/-!
# Normality and scheme morphisms

Normality ascends along smooth morphisms and descends along surjective flat
morphisms. No quasi-compactness assumption is needed for descent. Étale morphisms
are smooth, so smooth ascent includes the étale case without a separate theorem.

## Limitations

Smoothness cannot simply be dropped: `Spec (ℤ/4ℤ) → Spec ℤ` has normal target
but nonnormal source.
Surjectivity cannot be dropped from descent: the empty open subscheme of
`Spec (ℤ/4ℤ)` is normal and its inclusion is flat. Flatness cannot be dropped
either: the quotient map gives a surjective morphism
`Spec ℤ → Spec (ℤ[ε]/(ε²))` with normal source and nonnormal target.

## References

The normality notion and its stalk and affine criteria are from
`SchemeProperties.Normal`. Smooth ascent uses finite-variable polynomial normality
from `SchemeProperties.NormalPolynomial` and étale ascent from
`SchemeProperties.NormalEtale`. Mathlib supplies standard-smooth affine
neighborhoods and their étale factorizations over finite polynomial rings, as well
as the morphism properties and the étale-to-smooth implication. Descent uses
`SchemeProperties.NormalFaithfullyFlat` and Mathlib's local flat stalk maps and
closed-point stalk isomorphism.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The source of a smooth morphism to a normal scheme is normal. -/
theorem isNormal_of_smooth (f : X ⟶ Y) [Smooth f] [IsNormal Y] : IsNormal X := by
  have hstalk (x : X) : _root_.IsDomain (X.presheaf.stalk x) ∧
      _root_.IsIntegrallyClosed (X.presheaf.stalk x) := by
    obtain ⟨U, hU, V, hV, hx, hVU, hf⟩ := Smooth.exists_isStandardSmooth f x
    let _ : IsNormal (Spec Γ(Y, U)) := isNormal_of_isOpenImmersion hU.fromSpec
    let _ : IsLocallyNormalRing Γ(Y, U) :=
      isLocallyNormalRing_of_isNormal_spec Γ(Y, U)
    -- Use the algebra of the étale factor itself, not an arbitrary stalk map.
    obtain ⟨n, g, -, hg⟩ := hf.exists_etale_mvPolynomial
    let _ : Algebra (MvPolynomial (Fin n) Γ(Y, U)) Γ(X, V) := g.toAlgebra
    let _ : Algebra.Etale (MvPolynomial (Fin n) Γ(Y, U)) Γ(X, V) := hg.toAlgebra
    let _ : IsLocallyNormalRing Γ(X, V) :=
      IsLocallyNormalRing.of_etale (R := MvPolynomial (Fin n) Γ(Y, U))
    let _ : IsNormal (V : Scheme) := isNormal_of_isOpenImmersion hV.isoSpec.hom
    let _ : IsDomain ((V : Scheme).presheaf.stalk ⟨x, hx⟩) :=
      IsNormal.stalk_isDomain (X := (V : Scheme)) ⟨x, hx⟩
    let _ : IsIntegrallyClosed ((V : Scheme).presheaf.stalk ⟨x, hx⟩) :=
      IsNormal.stalk_isIntegrallyClosed (X := (V : Scheme)) ⟨x, hx⟩
    constructor
    · exact (V.stalkIso ⟨x, hx⟩).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
    · exact IsIntegrallyClosed.of_equiv (V.stalkIso ⟨x, hx⟩).commRingCatIsoToRingEquiv
  exact ⟨fun x ↦ (hstalk x).1, fun x ↦ (hstalk x).2⟩

/-- The target of a surjective flat morphism from a normal scheme is normal;
no quasi-compactness hypothesis is required. -/
theorem isNormal_of_surjective_of_flat (f : X ⟶ Y) [Surjective f] [Flat f]
    [IsNormal X] : IsNormal Y := by
  have stalk (y : Y) : IsDomain (Y.presheaf.stalk y) ∧
      IsIntegrallyClosed (Y.presheaf.stalk y) := by
    obtain ⟨x, rfl⟩ := f.surjective y
    let _ : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    let _ : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      Flat.stalkMap f x
    have _ : IsLocalHom
        (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
      f.toLRSHom.prop x
    let _ : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    let _ : IsLocallyNormalRing (X.presheaf.stalk x) :=
      isLocallyNormalRing_of_isDomain _
    let _ : IsLocallyNormalRing (Y.presheaf.stalk (f x)) :=
      IsLocallyNormalRing.of_faithfullyFlat (S := X.presheaf.stalk x)
    let R := Y.presheaf.stalk (f x)
    let _ : IsNormal (Spec R) := normalSpec
    let _ : IsDomain ((Spec R).presheaf.stalk (IsLocalRing.closedPoint R)) :=
      IsNormal.stalk_isDomain (X := Spec R) _
    let _ : IsIntegrallyClosed ((Spec R).presheaf.stalk (IsLocalRing.closedPoint R)) :=
      IsNormal.stalk_isIntegrallyClosed (X := Spec R) _
    let e := (stalkClosedPointIso R).commRingCatIsoToRingEquiv
    exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩
  exact ⟨fun y ↦ (stalk y).1, fun y ↦ (stalk y).2⟩

end AlgebraicGeometry
