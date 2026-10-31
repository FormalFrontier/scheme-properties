/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import MultivariatePolynomials.GenericFreeness
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Generic flatness on a principal affine chart

A finite-type homomorphism between the coordinate rings of affine opens, with a domain as its
source, becomes flat after shrinking the target to a nonzero principal open. The source of the
restricted morphism is the intersection of the original source chart with that principal open's
preimage.

The proof applies generic freeness to the coordinate homomorphism and compares its tensor base
change with the coordinate ring of the source principal open. No nonemptiness of the source
chart, or nonvanishing of the image of the element being inverted, is required.

## References

* J. S. Milne, *Algebraic Groups* (2017), for background on generic flatness.
* Mathlib's scheme, localization, and flatness APIs.
* The multivariate-polynomials generic-freeness API
  `Algebra.FiniteType.exists_free_localizationAway`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

/-- A basic open in an affine open is nonempty exactly when its defining section
is not nilpotent. -/
theorem IsAffineOpen.basicOpen_nonempty_iff
    {Y : Scheme.{u}} {U : Y.Opens} (hU : IsAffineOpen U) (a : Γ(Y, U)) :
    (Y.basicOpen a : Set Y).Nonempty ↔ ¬ IsNilpotent a := by
  rw [← TopologicalSpace.Opens.ne_bot_iff_nonempty, ← hU.fromSpec_image_basicOpen a]
  have hbot : hU.fromSpec ''ᵁ ⊥ = ⊥ :=
    TopologicalSpace.Opens.ext (Set.image_empty _)
  rw [← hbot]
  exact (not_congr hU.fromSpec.image_injective.eq_iff).trans
    (not_congr (PrimeSpectrum.basicOpen_eq_bot_iff a))

/-- A finite-type coordinate homomorphism over a domain is flat on a nonzero principal open of
the affine target chart, after restricting the original source chart to its preimage.

For background on generic flatness, see J. S. Milne, *Algebraic Groups* (2017).
The proof uses Mathlib and the multivariate-polynomials generic-freeness API. -/
theorem Scheme.Hom.exists_flat_resLE_basicOpen
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} {W : X.Opens}
    (hU : IsAffineOpen U) (hW : IsAffineOpen W)
    (e : W ≤ f ⁻¹ᵁ U) (hφ : (f.appLE U W e).hom.FiniteType)
    [IsDomain Γ(Y, U)] :
    ∃ a : Γ(Y, U), a ≠ 0 ∧
      Flat (f.resLE (Y.basicOpen a)
        (W ⊓ f ⁻¹ᵁ (Y.basicOpen a)) inf_le_right) := by
  let A := Γ(Y, U)
  let B := Γ(X, W)
  let φ : A →+* B := (f.appLE U W e).hom
  let : Algebra A B := φ.toAlgebra
  have : Algebra.FiniteType A B := hφ
  obtain ⟨a, ha, hfree⟩ :=
    Algebra.FiniteType.exists_free_localizationAway (A := A) (B := B)
  refine ⟨a, ha, ?_⟩
  let D := Y.basicOpen a
  let V := X.basicOpen (φ a)
  have eV : V ≤ f ⁻¹ᵁ D := by
    change X.basicOpen (f.appLE U W e a) ≤ f ⁻¹ᵁ (Y.basicOpen a)
    rw [Scheme.basicOpen_appLE]
    exact inf_le_right
  have : IsAffine D := hU.basicOpen a
  have : IsAffine V := hW.basicOpen (φ a)
  let A' := Γ(Y, D)
  let C := Γ(X, V)
  let ψ : A' →+* C := (f.appLE D V eV).hom
  have : IsLocalization.Away a A' := hU.isLocalization_basicOpen a
  have : IsLocalization.Away (φ a) C := hW.isLocalization_basicOpen (φ a)
  have hsq : ψ.comp (algebraMap A A') = (algebraMap B C).comp φ := by
    change
      (Y.presheaf.map (homOfLE (Y.basicOpen_le a)).op ≫ f.appLE D V eV).hom =
        (f.appLE U W e ≫
          X.presheaf.map (homOfLE (X.basicOpen_le (φ a))).op).hom
    exact congrArg CommRingCat.Hom.hom
      ((Scheme.Hom.map_appLE (f := f) eV
        (homOfLE (Y.basicOpen_le a)).op).trans
        (Scheme.Hom.appLE_map (f := f) e
          (homOfLE (X.basicOpen_le (φ a))).op).symm)
  -- Both scalar towers are induced by the same restriction square.
  let : Algebra A C := ((algebraMap B C).comp φ).toAlgebra
  have : IsScalarTower A B C :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let Aₐ := Localization.Away a
  let α : Aₐ ≃ₐ[A] A' := IsLocalization.algEquiv (Submonoid.powers a) Aₐ A'
  let : Algebra Aₐ C := (ψ.comp α.toRingHom).toAlgebra
  have : IsScalarTower A Aₐ C := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    change algebraMap B C (φ r) = ψ (α (algebraMap A Aₐ r))
    rw [α.commutes]
    exact (congrArg (fun k : A →+* C => k r) hsq).symm
  let T := Aₐ ⊗[A] B
  -- Fix the left-factor scalar actions before comparing the two B-localizations.
  let baseAlgebra : Algebra A T := inferInstance
  let leftAlgebra : Algebra Aₐ T := inferInstance
  let β : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let E_B :=
    @IsLocalization.algEquiv B _ (Submonoid.powers (φ a)) T _ β
      (IsLocalization.Away.tensorRight (R := A) (S := B) a Aₐ)
      C _ inferInstance inferInstance
  let E_A : @AlgEquiv A T C _ _ _ baseAlgebra inferInstance :=
    @AlgEquiv.restrictScalars A B T C _ _ _ _
      inferInstance β inferInstance baseAlgebra inferInstance
      (by infer_instance) inferInstance E_B
  let E : @AlgEquiv Aₐ T C _ _ _ leftAlgebra inferInstance :=
    @AlgEquiv.extendScalarsOfIsLocalization A T C _ _ _ Aₐ _ inferInstance
      (Submonoid.powers a) inferInstance
      baseAlgebra leftAlgebra (by infer_instance)
      inferInstance inferInstance inferInstance E_A
  have : Module.Free Aₐ T := hfree
  have : Module.Flat Aₐ C := Module.Flat.of_linearEquiv E.symm.toLinearEquiv
  have hcomp : (ψ.comp α.toRingHom).Flat := by
    change (algebraMap Aₐ C).Flat
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have hψ : ψ.Flat :=
    (RingHom.Flat.comp_iff_of_bijective_right
      (f := ψ) (g := α.toRingHom) α.bijective).mp hcomp
  have hg : Flat (f.resLE D V eV) := by
    apply (HasRingHomProperty.iff_of_isAffine
      (P := @Flat) (f := f.resLE D V eV)).mpr
    exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso f D V eV)).mpr hψ
  have hV : V = W ⊓ f ⁻¹ᵁ D := Scheme.basicOpen_appLE f W U e a
  change Flat (f.resLE D (W ⊓ f ⁻¹ᵁ D) inf_le_right)
  have hfamily : ∀ e' : V ≤ f ⁻¹ᵁ D, Flat (f.resLE D V e') := fun _ => hg
  exact (hV ▸ hfamily) inf_le_right

end AlgebraicGeometry
