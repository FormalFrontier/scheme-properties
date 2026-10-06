/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.Quasicoherent
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

public section

set_option warningAsError true

/-!
# Qcqs localization of quasicoherent module sections

This file proves the module-valued qcqs lemma: for a quasicoherent module on a
scheme, restriction from a compact quasiseparated open to a basic open is
localization away from the section defining that basic open.

The proof reduces the affine case to Mathlib's `fromTildeΓ` comparison and
basic-open `tilde.toOpen` localization, clears kernels on compact opens using
finite affine covers, and uses compact-open induction and the sheaf condition
for existence.

## References

- Mathlib's `Mathlib/AlgebraicGeometry/Modules/Tilde.lean` supplies the affine
  `fromTildeΓ` comparison and basic-open module-section localization.
- Mathlib's `Mathlib/AlgebraicGeometry/Morphisms/QuasiSeparated.lean` supplies
  the qcqs basic-open ring localization; its
  `Mathlib/AlgebraicGeometry/Morphisms/QuasiCompact.lean` supplies compact-open
  induction.
- Mathlib's `Mathlib/Algebra/Module/LocalizedModule/Away.lean` supplies the
  `IsLocalizedModule.Away` criterion used after the project module argument.
-/

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}}

/-- Restriction of module sections to a basic open, as a linear map over the
ring of sections on the ambient open. -/
@[expose]
noncomputable def basicOpenRestriction (M : X.Modules) {U : X.Opens} (f : Γ(X, U)) :
    letI : Module Γ(X, U) Γ(M, X.basicOpen f) :=
      Module.compHom Γ(M, X.basicOpen f) (algebraMap Γ(X, U) Γ(X, X.basicOpen f))
    Γ(M, U) →ₗ[Γ(X, U)] Γ(M, X.basicOpen f) := by
  letI : Module Γ(X, U) Γ(M, X.basicOpen f) :=
    Module.compHom Γ(M, X.basicOpen f) (algebraMap Γ(X, U) Γ(X, X.basicOpen f))
  exact
    { toFun := M.presheaf.map (homOfLE (X.basicOpen_le f)).op
      map_add' := map_add _
      map_smul' := fun r x ↦ M.map_smul (homOfLE (X.basicOpen_le f)) r x }

set_option backward.isDefEq.respectTransparency false in
private noncomputable def affineTopSectionsLinearEquiv (M : X.Modules) {U : X.Opens}
    (hU : IsAffineOpen U) :
    Γ(M.restrict hU.fromSpec, ⊤) ≃ₗ[Γ(X, U)] Γ(M, U) := by
  let htop : U = hU.fromSpec ''ᵁ ⊤ := by simp [hU.opensRange_fromSpec]
  let l : Γ(M.restrict hU.fromSpec, ⊤) →ₗ[Γ(X, U)] Γ(M, U) :=
    { toFun := fun x ↦ M.presheaf.map (eqToHom htop).op
          ((M.restrictAppIso hU.fromSpec ⊤).hom x)
      map_add' := map_add _
      map_smul' := by
        intro r x
        let r' : Γ(Spec Γ(X, U), ⊤) :=
          (Spec Γ(X, U)).presheaf.map (homOfLE le_top).op
            ((Scheme.ΓSpecIso Γ(X, U)).inv r)
        rw [show r • x = r' • x from smul_Spec_def r x]
        rw [show (M.restrictAppIso hU.fromSpec ⊤).hom (r' • x) =
          (hU.fromSpec.appIso ⊤).inv r' •
            (M.restrictAppIso hU.fromSpec ⊤).hom x from
          smul_restrictAppIso_hom_apply hU.fromSpec M ⊤ r' x]
        rw [M.map_smul]
        congr 1
        dsimp [r']
        let _ : IsIso (hU.fromSpec.app U) :=
          hU.fromSpec.isIso_app U (by rw [hU.opensRange_fromSpec])
        apply (ConcreteCategory.bijective_of_isIso (hU.fromSpec.app U)).1
        rw [← ConcreteCategory.comp_apply, hU.fromSpec.naturality]
        rw [ConcreteCategory.comp_apply]
        rw [Scheme.Hom.appIso_inv_app_apply]
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        rw [hU.fromSpec_app_self_apply]
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        rfl }
  apply LinearEquiv.ofBijective l
  exact (ConcreteCategory.bijective_of_isIso
    (M.presheaf.mapIso (eqToIso htop).op).hom).comp
      (ConcreteCategory.bijective_of_isIso (M.restrictAppIso hU.fromSpec ⊤).hom)

/-- Sections of a module on an affine open agree with the global sections of its
double restriction to the corresponding spectrum. -/
noncomputable def affineOpenSectionsLinearEquiv (M : X.Modules) (U : X.Opens)
    (hU : IsAffineOpen U) :
    (moduleSpecΓFunctor (R := Γ(X, U))).obj
        ((M.restrict U.ι).restrict hU.isoSpec.inv) ≃ₗ[Γ(X, U)] Γ(M, U) :=
  ((moduleSpecΓFunctor (R := Γ(X, U))).mapIso
    ((restrictFunctorComp hU.isoSpec.inv U.ι).app M)).symm.toLinearEquiv.trans
      (affineTopSectionsLinearEquiv M hU)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def affineBasicOpenSectionsLinearEquiv (M : X.Modules) {U : X.Opens}
    (hU : IsAffineOpen U) (f : Γ(X, U)) :
    letI : Module Γ(X, U) Γ(M, X.basicOpen f) :=
      Module.compHom Γ(M, X.basicOpen f) (algebraMap Γ(X, U) Γ(X, X.basicOpen f))
    Γ(M.restrict hU.fromSpec, PrimeSpectrum.basicOpen f) ≃ₗ[Γ(X, U)]
      Γ(M, X.basicOpen f) := by
  letI : Module Γ(X, U) Γ(M, X.basicOpen f) :=
    Module.compHom Γ(M, X.basicOpen f) (algebraMap Γ(X, U) Γ(X, X.basicOpen f))
  let V : (Spec Γ(X, U)).Opens := PrimeSpectrum.basicOpen f
  let hbasic : X.basicOpen f = hU.fromSpec ''ᵁ V :=
    hU.fromSpec_image_basicOpen f |>.symm
  let l : Γ(M.restrict hU.fromSpec, PrimeSpectrum.basicOpen f) →ₗ[Γ(X, U)]
      Γ(M, X.basicOpen f) :=
    { toFun := fun x ↦ M.presheaf.map (eqToHom hbasic).op
          ((M.restrictAppIso hU.fromSpec V).hom x)
      map_add' := map_add _
      map_smul' := by
        intro r x
        let r' : Γ(Spec Γ(X, U), V) :=
          (Spec Γ(X, U)).presheaf.map (homOfLE le_top).op
            ((Scheme.ΓSpecIso Γ(X, U)).inv r)
        rw [show r • x = r' • x from smul_Spec_def r x]
        rw [show (M.restrictAppIso hU.fromSpec V).hom (r' • x) =
          (hU.fromSpec.appIso V).inv r' •
            (M.restrictAppIso hU.fromSpec V).hom x from
          smul_restrictAppIso_hom_apply hU.fromSpec M V r' x]
        rw [M.map_smul]
        congr 1
        dsimp [r']
        let _ : IsIso (hU.fromSpec.app (X.basicOpen f)) :=
          hU.fromSpec.isIso_app _ (by
            rw [hU.opensRange_fromSpec]
            exact X.basicOpen_le f)
        apply (ConcreteCategory.bijective_of_isIso
          (hU.fromSpec.app (X.basicOpen f))).1
        rw [← ConcreteCategory.comp_apply, hU.fromSpec.naturality]
        rw [ConcreteCategory.comp_apply, Scheme.Hom.appIso_inv_app_apply]
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        change _ = hU.fromSpec.app (X.basicOpen f)
          (X.presheaf.map (homOfLE (X.basicOpen_le f)).op r)
        conv_rhs => rw [← ConcreteCategory.comp_apply]
        rw [hU.fromSpec.naturality]
        rw [ConcreteCategory.comp_apply, hU.fromSpec_app_self_apply]
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        rfl }
  apply LinearEquiv.ofBijective l
  exact (ConcreteCategory.bijective_of_isIso
    (M.presheaf.mapIso (eqToIso hbasic).op).hom).comp
      (ConcreteCategory.bijective_of_isIso (M.restrictAppIso hU.fromSpec V).hom)

set_option backward.isDefEq.respectTransparency false in
private theorem isLocalizedModule_basicOpen_of_isAffineOpen
    (M : X.Modules) [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U)) :
    letI : Module Γ(X, U) Γ(M, X.basicOpen f) :=
      Module.compHom Γ(M, X.basicOpen f) (algebraMap Γ(X, U) Γ(X, X.basicOpen f))
    IsLocalizedModule.Away f (basicOpenRestriction M f) := by
  let _ : Module Γ(X, U) Γ(M, X.basicOpen f) :=
    Module.compHom Γ(M, X.basicOpen f) (algebraMap Γ(X, U) Γ(X, X.basicOpen f))
  let N := M.restrict hU.fromSpec
  let V : (Spec Γ(X, U)).Opens := PrimeSpectrum.basicOpen f
  let φ : Γ(N, ⊤) →ₗ[Γ(X, U)] Γ(N, V) :=
    ((modulesSpecToSheaf.obj N).obj.map (homOfLE le_top).op).hom
  have hφ : IsLocalizedModule.Away f φ :=
    (isIso_fromTildeΓ_iff_isLocalizing N).mp (inferInstance : IsIso N.fromTildeΓ) f
  let e₀ := affineTopSectionsLinearEquiv M hU
  let e₁ := affineBasicOpenSectionsLinearEquiv M hU f
  have hcomm (y : Γ(N, ⊤)) :
      e₁ (φ y) = basicOpenRestriction M f (e₀ y) := by
    dsimp [φ, e₀, e₁, affineTopSectionsLinearEquiv,
      affineBasicOpenSectionsLinearEquiv]
    change M.presheaf.map _
      ((M.restrictAppIso hU.fromSpec V).hom
        (N.presheaf.map (homOfLE le_top).op y)) = _
    rw [map_restrictAppIso_hom_apply]
    dsimp [basicOpenRestriction]
    simp only [← ConcreteCategory.comp_apply, Category.assoc]
    congr 1
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  let ψ := e₁.toLinearMap.comp (φ.comp e₀.symm.toLinearMap)
  have hψ : IsLocalizedModule.Away f ψ := by
    let _ : IsLocalizedModule.Away f φ := hφ
    let _ : IsLocalizedModule.Away f (φ.comp e₀.symm.toLinearMap) :=
      IsLocalizedModule.of_linearEquiv_right _ φ e₀.symm
    exact IsLocalizedModule.of_linearEquiv _ (φ.comp e₀.symm.toLinearMap) e₁
  rw [show ψ = basicOpenRestriction M f by
    ext x
    dsimp [ψ]
    change e₁ (φ (e₀.symm x)) = basicOpenRestriction M f x
    simpa using hcomm (e₀.symm x)] at hψ
  exact hψ

private theorem exists_eq_pow_smul_of_isAffineOpen (M : X.Modules) [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))
    (x : Γ(M, X.basicOpen f)) :
    ∃ (n : ℕ) (y : Γ(M, U)),
      M.presheaf.map (homOfLE (X.basicOpen_le f)).op y =
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) ^ n • x := by
  let _ : Module Γ(X, U) Γ(M, X.basicOpen f) :=
    Module.compHom Γ(M, X.basicOpen f) (algebraMap Γ(X, U) Γ(X, X.basicOpen f))
  let _ : IsLocalizedModule.Away f (basicOpenRestriction M f) :=
    isLocalizedModule_basicOpen_of_isAffineOpen M hU f
  obtain ⟨n, y, hy⟩ := IsLocalizedModule.Away.surj (basicOpenRestriction M f) f x
  refine ⟨n, y, hy.symm.trans ?_⟩
  change algebraMap Γ(X, U) Γ(X, X.basicOpen f) (f ^ n) • x = _
  rw [map_pow]
  rfl

private theorem exists_pow_smul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen
    (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)
    (x : Γ(M, U)) (f : Γ(X, U))
    (H : M.presheaf.map (homOfLE (X.basicOpen_le f)).op x = 0) :
    ∃ n : ℕ, f ^ n • x = 0 := by
  let _ : Module Γ(X, U) Γ(M, X.basicOpen f) :=
    Module.compHom Γ(M, X.basicOpen f) (algebraMap Γ(X, U) Γ(X, X.basicOpen f))
  let _ : IsLocalizedModule.Away f (basicOpenRestriction M f) :=
    isLocalizedModule_basicOpen_of_isAffineOpen M hU f
  have H' : basicOpenRestriction M f x = basicOpenRestriction M f 0 := by
    simpa [basicOpenRestriction] using H
  obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq f
    (f := basicOpenRestriction M f) H'
  exact ⟨n, by simpa using hn⟩

private theorem exists_pow_smul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact
    (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens} (hU : IsCompact U.1)
    (x : Γ(M, U)) (f : Γ(X, U))
    (H : M.presheaf.map (homOfLE (X.basicOpen_le f)).op x = 0) :
    ∃ n : ℕ, f ^ n • x = 0 := by
  obtain ⟨s, hs, e⟩ :=
    isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp ⟨hU, U.2⟩
  replace e : U = iSup fun i : s ↦ (i : X.Opens) := by
    ext1
    simpa using e
  have h₁ (i : s) : i.1.1 ≤ U := by
    rw [e]
    exact le_iSup (fun i : s ↦ (i : X.Opens)) i
  have H' := fun i : s ↦ by
    have Hzero :
        M.presheaf.map
            (homOfLE (X.basicOpen_le (X.presheaf.map (homOfLE (h₁ i)).op f))).op
            (M.presheaf.map (homOfLE (h₁ i)).op x) = 0 := by
      have h := congr_arg (M.presheaf.map (homOfLE (by
        exact X.basicOpen_restrict (homOfLE (h₁ i)) f)).op) H
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, map_zero] at h
      convert h using 1
      · rfl
      · simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        exact HEq.rfl
      · rfl
    exact exists_pow_smul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen M i.1.2
      (M.presheaf.map (homOfLE (h₁ i)).op x)
      (X.presheaf.map (homOfLE (h₁ i)).op f) Hzero
  choose n hn using H'
  have := hs.to_subtype
  cases nonempty_fintype s
  use Finset.univ.sup n
  suffices ∀ i : s,
      M.presheaf.map (homOfLE (h₁ i)).op (f ^ Finset.univ.sup n • x) = 0 by
    subst e
    apply TopCat.Sheaf.eq_of_locally_eq ⟨_, M.isSheaf⟩ (fun i : s ↦ (i : X.Opens))
    intro i
    change _ = M.presheaf.map _ 0
    rw [map_zero]
    exact this i
  intro i
  have hni : n i ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ i)
  rw [show Finset.univ.sup n = (Finset.univ.sup n - n i) + n i by omega,
    pow_add, mul_smul, M.map_smul, M.map_smul]
  simp only [map_pow]
  rw [hn i, smul_zero]

set_option backward.isDefEq.respectTransparency false in
private theorem exists_eq_pow_smul_of_isCompact_of_isQuasiSeparated
    (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens} (hU : IsCompact U.1)
    (hU' : IsQuasiSeparated U.1) (f : Γ(X, U)) (x : Γ(M, X.basicOpen f)) :
    ∃ (n : ℕ) (y : Γ(M, U)),
      M.presheaf.map (homOfLE (X.basicOpen_le f)).op y =
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) ^ n • x := by
  revert hU' f x
  refine compact_open_induction_on U hU ?_ ?_
  · intro _ f x
    use 0, 0
    exact @Subsingleton.elim _
      (AddCommGrpCat.subsingleton_of_isZero
        (TopCat.Sheaf.isTerminalOfEqEmpty
          (⟨_, M.isSheaf⟩ : TopCat.Sheaf Ab X) (by
          rw [eq_bot_iff]
          exact X.basicOpen_le f)).isZero) _ _
  · intro S hS V hV hSV f x
    obtain ⟨n₁, y₁, hy₁⟩ :=
      hV (hSV.of_subset Set.subset_union_left)
        (X.presheaf.map (homOfLE le_sup_left).op f)
        (M.presheaf.map (homOfLE (by
          rw [X.basicOpen_res]
          exact inf_le_right)).op x)
    obtain ⟨n₂, y₂, hy₂⟩ :=
      exists_eq_pow_smul_of_isAffineOpen M V.2
        (X.presheaf.map (homOfLE le_sup_right).op f)
        (M.presheaf.map (homOfLE (by
          rw [X.basicOpen_res]
          exact inf_le_right)).op x)
    let T : X.Opens := S ⊓ V.1
    have hT : IsCompact T.1 :=
      hSV _ _ Set.subset_union_left S.2 hS Set.subset_union_right V.1.2 V.2.isCompact
    let fT : Γ(X, T) := X.presheaf.map (homOfLE (by
      dsimp [T]
      exact le_sup_of_le_left inf_le_left)).op f
    let a : Γ(M, T) := M.presheaf.map (homOfLE (by
      dsimp [T]
      exact inf_le_left)).op y₁
    let b : Γ(M, T) := M.presheaf.map (homOfLE (by
      dsimp [T]
      exact inf_le_right)).op y₂
    have hz : M.presheaf.map (homOfLE (X.basicOpen_le fT)).op
        (fT ^ n₂ • a - fT ^ n₁ • b) = 0 := by
      have hDfS : X.basicOpen fT ≤
          X.basicOpen (X.presheaf.map (homOfLE le_sup_left).op f) := by
        convert X.basicOpen_restrict
          (homOfLE (inf_le_left (b := (V : X.Opens))))
          (X.presheaf.map (homOfLE le_sup_left).op f) using 1
        congr 1
        dsimp only [fT]
        change _ = X.presheaf.map _ (X.presheaf.map _ f)
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        rfl
      have hDfV : X.basicOpen fT ≤
          X.basicOpen (X.presheaf.map (homOfLE le_sup_right).op f) := by
        convert X.basicOpen_restrict (homOfLE (inf_le_right (a := S)))
          (X.presheaf.map (homOfLE le_sup_right).op f) using 1
        congr 1
        dsimp only [fT]
        change _ = X.presheaf.map _ (X.presheaf.map _ f)
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        rfl
      have hDf : X.basicOpen fT ≤ X.basicOpen f := by
        convert X.basicOpen_restrict (homOfLE (show T ≤ S ⊔ (V : X.Opens) by
          dsimp only [T]
          exact le_sup_of_le_left inf_le_left)) f using 1
        congr 1
      have h₁ := congr_arg (M.presheaf.map (homOfLE hDfS).op) hy₁
      have h₂ := congr_arg (M.presheaf.map (homOfLE hDfV).op) hy₂
      have h₁' :
          M.presheaf.map (homOfLE (X.basicOpen_le fT)).op a =
            (X.presheaf.map (homOfLE (X.basicOpen_le fT)).op fT) ^ n₁ •
              M.presheaf.map (homOfLE hDf).op x := by
        dsimp only [a]
        simp only [M.map_smul, map_pow, ← ConcreteCategory.comp_apply,
          ← Functor.map_comp] at h₁
        convert h₁ using 1 <;>
          simp only [fT, ← ConcreteCategory.comp_apply, ← Functor.map_comp] <;> rfl
      have h₂' :
          M.presheaf.map (homOfLE (X.basicOpen_le fT)).op b =
            (X.presheaf.map (homOfLE (X.basicOpen_le fT)).op fT) ^ n₂ •
              M.presheaf.map (homOfLE hDf).op x := by
        dsimp only [b]
        simp only [M.map_smul, map_pow, ← ConcreteCategory.comp_apply,
          ← Functor.map_comp] at h₂
        convert h₂ using 1 <;>
          simp only [fT, ← ConcreteCategory.comp_apply, ← Functor.map_comp] <;> rfl
      rw [map_sub, M.map_smul, M.map_smul, map_pow, map_pow, sub_eq_zero]
      rw [h₁', h₂']
      simp only [← mul_smul, ← pow_add, add_comm n₂ n₁]
    obtain ⟨n, hn⟩ :=
      exists_pow_smul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact M hT
        (fT ^ n₂ • a - fT ^ n₁ • b) fT hz
    have hab : fT ^ (n + n₂) • a = fT ^ (n + n₁) • b := by
      rw [smul_sub, sub_eq_zero] at hn
      simpa only [pow_add, mul_smul] using hn
    have hcompat :
        M.presheaf.map (homOfLE (by
          exact inf_le_left (b := (V : X.Opens)))).op
            ((X.presheaf.map (homOfLE le_sup_left).op f) ^ (n + n₂) • y₁) =
          M.presheaf.map (homOfLE (by
            exact inf_le_right (a := S))).op
              ((X.presheaf.map (homOfLE le_sup_right).op f) ^ (n + n₁) • y₂) := by
      dsimp only [a, b]
      simp only [M.map_smul, map_pow]
      dsimp only [a, b] at hab
      convert hab using 1 <;>
        simp only [fT, ← ConcreteCategory.comp_apply, ← Functor.map_comp] <;> rfl
    let yS : Γ(M, S) :=
      (X.presheaf.map (homOfLE le_sup_left).op f) ^ (n + n₂) • y₁
    let yV : Γ(M, (V : X.Opens)) :=
      (X.presheaf.map (homOfLE le_sup_right).op f) ^ (n + n₁) • y₂
    let W : Bool → X.Opens
      | false => (V : X.Opens)
      | true => S
    let yW : (i : Bool) → Γ(M, W i)
      | false => yV
      | true => yS
    let iW : (i : Bool) → W i ⟶ S ⊔ (V : X.Opens)
      | false => homOfLE le_sup_right
      | true => homOfLE le_sup_left
    have hW : TopCat.Presheaf.IsCompatible M.presheaf W yW := by
      intro i j
      cases i <;> cases j
      · rfl
      · dsimp only [W, yW, yS, yV]
        have hh := congr_arg
          (M.presheaf.map (eqToHom (inf_comm (V : X.Opens) S)).op) hcompat.symm
        simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hh
        convert hh using 1
      · dsimp only [W, yW, yS, yV]
        convert hcompat using 1 <;> rfl
      · rfl
    have hcover : S ⊔ (V : X.Opens) ≤ iSup W := by
      rw [sup_le_iff]
      exact ⟨le_iSup W true, le_iSup W false⟩
    obtain ⟨y, hy, -⟩ := TopCat.Sheaf.existsUnique_gluing'
      (⟨_, M.isSheaf⟩ : TopCat.Sheaf Ab X) W (S ⊔ (V : X.Opens)) iW hcover yW hW
    use n + n₁ + n₂, y
    let fS : Γ(X, S) := X.presheaf.map (homOfLE le_sup_left).op f
    let fV : Γ(X, (V : X.Opens)) := X.presheaf.map (homOfLE le_sup_right).op f
    have hDfS : X.basicOpen fS ≤ X.basicOpen f := by
      exact X.basicOpen_restrict (homOfLE le_sup_left) f
    have hDfV : X.basicOpen fV ≤ X.basicOpen f := by
      exact X.basicOpen_restrict (homOfLE le_sup_right) f
    apply TopCat.Sheaf.eq_of_locally_eq₂ (⟨_, M.isSheaf⟩ : TopCat.Sheaf Ab X)
      (homOfLE hDfS) (homOfLE hDfV)
    · rw [show fS = X.presheaf.map (homOfLE le_sup_left).op f by rfl,
        show fV = X.presheaf.map (homOfLE le_sup_right).op f by rfl,
        X.basicOpen_res, X.basicOpen_res, ← inf_sup_right]
      exact le_inf (X.basicOpen_le f) le_rfl
    · have hyS := hy true
      dsimp only [iW, W, yW, yS] at hyS
      have hyS' := congr_arg
        (M.presheaf.map (homOfLE (X.basicOpen_le fS)).op) hyS
      have hy₁clean :
          M.presheaf.map (homOfLE (X.basicOpen_le fS)).op y₁ =
            (X.presheaf.map (homOfLE (X.basicOpen_le fS)).op fS) ^ n₁ •
              M.presheaf.map (homOfLE hDfS).op x := by
        convert hy₁ using 1
      simp only [M.map_smul, map_pow, ← ConcreteCategory.comp_apply,
        ← Functor.map_comp] at hyS' ⊢
      calc
        _ = (X.presheaf.map (homOfLE (X.basicOpen_le fS)).op fS) ^ (n + n₂) •
              M.presheaf.map (homOfLE (X.basicOpen_le fS)).op y₁ := by
            have hscalar :
                X.presheaf.map (homOfLE (X.basicOpen_le fS)).op fS =
                  X.presheaf.map
                    ((homOfLE le_sup_left).op ≫
                      (homOfLE (X.basicOpen_le fS)).op) f := by
              dsimp only [fS]
              rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
            rw [hscalar]
            convert hyS' using 1
        _ = _ := by
          rw [hy₁clean]
          simp only [← mul_smul, ← pow_add]
          have hscalar :
              X.presheaf.map
                  ((homOfLE (X.basicOpen_le f)).op ≫ (homOfLE hDfS).op) f =
                X.presheaf.map (homOfLE (X.basicOpen_le fS)).op fS := by
            dsimp only [fS]
            rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
            rfl
          rw [hscalar]
          congr 2
          omega
    · have hyV := hy false
      dsimp only [iW, W, yW, yV] at hyV
      have hyV' := congr_arg
        (M.presheaf.map (homOfLE (X.basicOpen_le fV)).op) hyV
      have hy₂clean :
          M.presheaf.map (homOfLE (X.basicOpen_le fV)).op y₂ =
            (X.presheaf.map (homOfLE (X.basicOpen_le fV)).op fV) ^ n₂ •
              M.presheaf.map (homOfLE hDfV).op x := by
        convert hy₂ using 1
      simp only [M.map_smul, map_pow, ← ConcreteCategory.comp_apply,
        ← Functor.map_comp] at hyV' ⊢
      calc
        _ = (X.presheaf.map (homOfLE (X.basicOpen_le fV)).op fV) ^ (n + n₁) •
              M.presheaf.map (homOfLE (X.basicOpen_le fV)).op y₂ := by
            have hscalar :
                X.presheaf.map (homOfLE (X.basicOpen_le fV)).op fV =
                  X.presheaf.map
                    ((homOfLE le_sup_right).op ≫
                      (homOfLE (X.basicOpen_le fV)).op) f := by
              dsimp only [fV]
              rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
            rw [hscalar]
            convert hyV' using 1
        _ = _ := by
          rw [hy₂clean]
          simp only [← mul_smul, ← pow_add]
          have hscalar :
              X.presheaf.map
                  ((homOfLE (X.basicOpen_le f)).op ≫ (homOfLE hDfV).op) f =
                X.presheaf.map (homOfLE (X.basicOpen_le fV)).op fV := by
            dsimp only [fV]
            rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
            rfl
          rw [hscalar]

/-- Restriction of sections of a quasicoherent module to a basic open of a
compact quasiseparated open is localization away from the defining section. -/
theorem isLocalizedModule_basicOpen_of_qcqs
    (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens} (hU : IsCompact U.1)
    (hU' : IsQuasiSeparated U.1) (f : Γ(X, U)) :
    letI : Module Γ(X, U) Γ(M, X.basicOpen f) :=
      Module.compHom Γ(M, X.basicOpen f) (algebraMap Γ(X, U) Γ(X, X.basicOpen f))
    IsLocalizedModule.Away f (basicOpenRestriction M f) := by
  let _ : Module Γ(X, U) Γ(M, X.basicOpen f) :=
    Module.compHom Γ(M, X.basicOpen f) (algebraMap Γ(X, U) Γ(X, X.basicOpen f))
  let _ : IsLocalization.Away f Γ(X, X.basicOpen f) :=
    AlgebraicGeometry.isLocalization_basicOpen_of_qcqs hU hU' f
  apply IsLocalizedModule.Away.mk_of_addCommGroup
  · have h := (IsLocalization.Away.algebraMap_isUnit f).map
      (algebraMap Γ(X, X.basicOpen f)
        (Module.End Γ(X, X.basicOpen f) Γ(M, X.basicOpen f)))
    rw [Module.End.isUnit_iff] at h ⊢
    convert h
  · intro x
    obtain ⟨n, y, hy⟩ :=
      exists_eq_pow_smul_of_isCompact_of_isQuasiSeparated M hU hU' f x
    refine ⟨n, y, ?_⟩
    simp only [MulAction.compHom_smul_def, basicOpenRestriction, map_pow,
      RingHom.algebraMap_toAlgebra]
    convert hy.symm using 1
  · intro x hx
    exact exists_pow_smul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact M hU x f
      (by
        dsimp only [basicOpenRestriction] at hx
        exact hx)

/-- The global-sections specialization of
`isLocalizedModule_basicOpen_of_qcqs`. -/
theorem isLocalizedModule_basicOpen_of_qcqs_of_top
    (M : X.Modules) [M.IsQuasicoherent] [CompactSpace X] [QuasiSeparatedSpace X]
    (f : Γ(X, ⊤)) :
    letI : Module Γ(X, ⊤) Γ(M, X.basicOpen f) :=
      Module.compHom Γ(M, X.basicOpen f) (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen f))
    IsLocalizedModule.Away f (basicOpenRestriction M f) :=
  isLocalizedModule_basicOpen_of_qcqs M CompactSpace.isCompact_univ
    isQuasiSeparated_univ f

end AlgebraicGeometry.Scheme.Modules
