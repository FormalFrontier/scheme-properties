module

public import SchemeProperties.PresheafModuleTensorStalk
public import SchemeProperties.ModuleTensor
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Stalks

public section

/-!
# Tensor product comparison on affine schemes

For modules over a commutative ring, sheafification of the pointwise tensor
of their associated sheaves is naturally isomorphic to the associated sheaf
of their algebraic tensor product. The proof cancels the sheafification unit on
stalks, uses the canonical tensor-of-stalks comparison, and identifies the
remaining map via the universal property of module localization.
-/


open CategoryTheory MonoidalCategory TopologicalSpace Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

private noncomputable local instance (X : Scheme.{u}) :
    MonoidalCategoryStruct X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategoryStruct (R := X.sheaf.obj)

private noncomputable local instance (X : Scheme.{u}) :
    MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.sheaf.obj)

private noncomputable local instance (X : Scheme.{u}) :
    SymmetricCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.symmetricCategory (R := X.sheaf.obj)

variable (R : CommRingCat.{u}) (M N : ModuleCat.{u} R)

private noncomputable abbrev PStalk {X : TopCat.{u}}
    (A : X.Presheaf CommRingCat.{u})
    (L : PresheafOfModulesOfCommRing.{u} A) (x : X) :=
  TopCat.Presheaf.stalk L.presheaf x

private noncomputable def tildeTopSection (M : ModuleCat.{u} R) (m : M) :
    Γ(tilde M, ⊤) :=
  (tilde.toOpen M ⊤).hom m

private theorem tildeTopSection_add (M : ModuleCat.{u} R) (m₁ m₂ : M) :
    tildeTopSection R M (m₁ + m₂) =
      tildeTopSection R M m₁ + tildeTopSection R M m₂ := by
  exact (tilde.toOpen M ⊤).hom.map_add m₁ m₂

private theorem tildeTopSection_smul (M : ModuleCat.{u} R) (r : R) (m : M) :
    tildeTopSection R M (r • m) = r • tildeTopSection R M m := by
  exact (tilde.toOpen M ⊤).hom.map_smul r m

private theorem tildeMap_topSection {M' : ModuleCat.{u} R} (f : M ⟶ M') (m : M) :
    (tilde.map f).app ⊤ (tildeTopSection R M m) =
      tildeTopSection R M' (f.hom m) := by
  exact DFunLike.congr_fun
    (congrArg ModuleCat.Hom.hom (tilde.toOpen_map_app f ⊤)) m

private noncomputable def globalPureTensor :
    M ⊗ N ⟶ moduleSpecΓFunctor.obj
      ((tensorFunctor (Spec R)).obj (tilde M, tilde N)) :=
  ModuleCat.MonoidalCategory.tensorLift
    (R := R) (M₁ := M) (M₂ := N)
    (M₃ := moduleSpecΓFunctor.obj (tensor (tilde M) (tilde N)))
    (fun m n ↦ tmul (tilde M) (tilde N) ⊤
      (tildeTopSection R M m) (tildeTopSection R N n))
    (by
      intro m₁ m₂ n
      rw [tildeTopSection_add]
      exact add_tmul (tilde M) (tilde N) ⊤ _ _ _)
    (by
      intro r m n
      rw [tildeTopSection_smul]
      change tmul (tilde M) (tilde N) ⊤
        (r • tildeTopSection R M m) (tildeTopSection R N n) = _
      rw [smul_Spec_def, smul_tmul]
      rfl)
    (by
      intro m n₁ n₂
      rw [tildeTopSection_add]
      exact tmul_add (tilde M) (tilde N) ⊤ _ _ _)
    (by
      intro r m n
      rw [tildeTopSection_smul]
      change tmul (tilde M) (tilde N) ⊤
        (tildeTopSection R M m) (r • tildeTopSection R N n) = _
      rw [smul_Spec_def, tmul_smul]
      rfl)

private theorem globalPureTensor_tmul (m : M) (n : N) :
    (globalPureTensor R M N).hom (m ⊗ₜ[R] n) =
      tmul (tilde M) (tilde N) ⊤
        (tildeTopSection R M m) (tildeTopSection R N n) := by
  unfold globalPureTensor
  apply ModuleCat.MonoidalCategory.tensorLift_tmul

/-- The canonical comparison in the direction supplied by the tilde--global
sections adjunction. -/
private noncomputable def comparisonHom :
    (tilde.functor R).obj (M ⊗ N) ⟶
      (tensorFunctor (Spec R)).obj (tilde M, tilde N) :=
  ((tilde.adjunction (R := R)).homEquiv _ _).symm (globalPureTensor R M N)

private theorem comparisonHom_homEquiv :
    (tilde.adjunction (R := R)).homEquiv _ _ (comparisonHom R M N) =
      globalPureTensor R M N := by
  exact ((tilde.adjunction (R := R)).homEquiv _ _).apply_symm_apply
    (globalPureTensor R M N)

private theorem comparisonHom_adjunct :
    (tilde.adjunction (R := R)).unit.app (M ⊗ N) ≫
        moduleSpecΓFunctor.map (comparisonHom R M N) =
      globalPureTensor R M N := by
  calc
    _ = (tilde.adjunction (R := R)).homEquiv _ _ (comparisonHom R M N) :=
      ((tilde.adjunction (R := R)).homEquiv_unit _ _ _).symm
    _ = globalPureTensor R M N := comparisonHom_homEquiv R M N

private theorem comparisonHom_app_top_tmul (m : M) (n : N) :
    (comparisonHom R M N).app ⊤
        (tildeTopSection R (M ⊗ N) (m ⊗ₜ[R] n)) =
      tmul (tilde M) (tilde N) ⊤
        (tildeTopSection R M m) (tildeTopSection R N n) := by
  have h := congrArg (fun f ↦ f.hom (m ⊗ₜ[R] n))
    (comparisonHom_adjunct R M N)
  change (comparisonHom R M N).app ⊤
      (tildeTopSection R (M ⊗ N) (m ⊗ₜ[R] n)) =
    (globalPureTensor R M N).hom (m ⊗ₜ[R] n) at h
  exact h.trans (globalPureTensor_tmul R M N m n)

private theorem comparisonHom_naturality {M' N' : ModuleCat.{u} R}
    (f : M ⟶ M') (g : N ⟶ N') :
    (tilde.functor R).map (f ⊗ₘ g) ≫ comparisonHom R M' N' =
      comparisonHom R M N ≫
        (tensorFunctor (Spec R)).map (tilde.map f, tilde.map g) := by
  apply ((tilde.adjunction (R := R)).homEquiv _ _).injective
  rw [(tilde.adjunction (R := R)).homEquiv_naturality_left,
    (tilde.adjunction (R := R)).homEquiv_naturality_right,
    comparisonHom_homEquiv, comparisonHom_homEquiv]
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  change (globalPureTensor R M' N').hom ((f ⊗ₘ g).hom (m ⊗ₜ[R] n)) =
    (moduleSpecΓFunctor.map ((tensorFunctor (Spec R)).map
      (tilde.map f, tilde.map g))).hom ((globalPureTensor R M N).hom (m ⊗ₜ[R] n))
  rw [ModuleCat.MonoidalCategory.tensorHom_tmul,
    globalPureTensor_tmul, globalPureTensor_tmul]
  change tmul (tilde M') (tilde N') ⊤
      (tildeTopSection R M' (f.hom m)) (tildeTopSection R N' (g.hom n)) =
    ((tensorFunctor (Spec R)).map (tilde.map f, tilde.map g)).app ⊤
      (tmul (tilde M) (tilde N) ⊤
        (tildeTopSection R M m) (tildeTopSection R N n))
  rw [tensorFunctor_map_app_tmul]
  rw [tildeMap_topSection, tildeMap_topSection]

private theorem comparisonHom_app_top_tmul_toOpen (m : M) (n : N) :
    (comparisonHom R M N).app ⊤
        ((tilde.toOpen (M ⊗ N) ⊤).hom (m ⊗ₜ[R] n)) =
      tmul (tilde M) (tilde N) ⊤
        ((tilde.toOpen M ⊤).hom m) ((tilde.toOpen N ⊤).hom n) := by
  exact comparisonHom_app_top_tmul R M N m n

private noncomputable def comparisonStalk (x : Spec R) :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).map
      (comparisonHom R M N)).hom

private noncomputable def tensorUnitStalk (x : Spec R) :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((PresheafOfModules.toPresheaf (Spec R).ringCatSheaf.obj).map
      (tensorUnit (tilde M) (tilde N)))

private theorem tensorUnitStalk_isIso (x : Spec R) :
    IsIso (tensorUnitStalk R M N x) := by
  unfold tensorUnitStalk tensorUnit
  change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology (Spec R))
      ((tilde M).val ⊗ (tilde N).val).presheaf))
  exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
    x AddCommGrpCat ((tilde M).val ⊗ (tilde N).val).presheaf

private noncomputable def rawStalkComparison (x : Spec R) :=
  comparisonStalk R M N x ≫
    inv (tensorUnitStalk R M N x) (I := tensorUnitStalk_isIso R M N x)

private noncomputable local instance tildeStalkModule (L : ModuleCat.{u} R) (x : Spec R) :
    Module ((Spec R).presheaf.stalk x) ((tilde L).presheaf.stalk x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (tilde L).val x

private noncomputable local instance affinePresheafStalkModule
    (L : PresheafOfModulesOfCommRing.{u} (Spec R).presheaf) (x : Spec R) :
    Module ((Spec R).presheaf.stalk x) (PStalk (Spec R).presheaf L x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier L x

private noncomputable local instance affineStalkAlgebra (x : Spec R) :
    Algebra R ((Spec R).presheaf.stalk x) :=
  (((Spec R).presheaf.germ ⊤ x trivial).hom.comp
    (algebraMap R ((Spec R).presheaf.obj (op ⊤)))).toAlgebra

private local instance affinePointIsPrime (x : Spec R) : x.asIdeal.IsPrime :=
  (show PrimeSpectrum R from x).isPrime

private noncomputable local instance affineStalkIsLocalization (x : Spec R) :
    IsLocalization x.asIdeal.primeCompl ((Spec R).presheaf.stalk x) := by
  let p : PrimeSpectrum R := x
  change IsLocalization p.asIdeal.primeCompl
    ((structurePresheafInCommRingCat R).stalk p)
  infer_instance

private noncomputable local instance tildeStalkModuleRDirect
    (L : ModuleCat.{u} R) (x : Spec R) :
    Module R ((tilde L).presheaf.stalk x) :=
  Module.compHom _ (algebraMap R ((Spec R).presheaf.stalk x))

private noncomputable def rawThenGeneric (x : Spec R) :
    (tilde (M ⊗ N)).presheaf.stalk x →+
      TensorProduct ((Spec R).presheaf.stalk x)
        ((tilde M).presheaf.stalk x) ((tilde N).presheaf.stalk x) :=
  let e := PresheafOfModulesOfCommRing.stalkTensorEquiv (Spec R).presheaf
    (tilde M).val (tilde N).val x
  e.toLinearMap.toAddMonoidHom.comp (rawStalkComparison R M N x).hom

private noncomputable def comparisonStalkLinear (x : Spec R) :=
  PresheafOfModulesOfCommRing.stalkMapLinear (Spec R).presheaf
    (tilde (M ⊗ N)).val ((tensorFunctor (Spec R)).obj (tilde M, tilde N)).val x
      (comparisonHom R M N).val

private noncomputable def tensorUnitStalkLinear (x : Spec R) :=
  PresheafOfModulesOfCommRing.stalkMapLinear (Spec R).presheaf
    ((tilde M).val ⊗ (tilde N).val)
      ((tensorFunctor (Spec R)).obj (tilde M, tilde N)).val x
        (tensorUnit (tilde M) (tilde N))

private theorem comparisonStalkLinear_apply (x : Spec R)
    (z : (tilde (M ⊗ N)).presheaf.stalk x) :
    comparisonStalkLinear R M N x z = (comparisonStalk R M N x).hom z := by
  exact PresheafOfModulesOfCommRing.stalkMapLinear_apply_stalkFunctor
    (Spec R).presheaf _ _ x (comparisonHom R M N).val z

private theorem tensorUnitStalkLinear_apply (x : Spec R)
    (z : PStalk (Spec R).presheaf ((tilde M).val ⊗ (tilde N).val) x) :
    tensorUnitStalkLinear R M N x z = (tensorUnitStalk R M N x).hom z := by
  exact PresheafOfModulesOfCommRing.stalkMapLinear_apply_stalkFunctor
    (Spec R).presheaf _ _ x (tensorUnit (tilde M) (tilde N)) z

private noncomputable def tensorUnitStalkLinearEquiv (x : Spec R) :=
  LinearEquiv.ofBijective (tensorUnitStalkLinear R M N x) (by
    have hmap : (tensorUnitStalkLinear R M N x).toFun =
        (tensorUnitStalk R M N x).hom := by
      funext z
      exact tensorUnitStalkLinear_apply R M N x z
    change Function.Bijective (tensorUnitStalkLinear R M N x).toFun
    rw [hmap]
    exact @ConcreteCategory.bijective_of_isIso _ _ _ _ _ _ _ _
      (tensorUnitStalk R M N x) (tensorUnitStalk_isIso R M N x))

private noncomputable def rawStalkComparisonLinear (x : Spec R) := by
  letI : Module ((Spec R).presheaf.stalk x)
      (PStalk (Spec R).presheaf
        ((tensorFunctor (Spec R)).obj (tilde M, tilde N)).val x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      ((tensorFunctor (Spec R)).obj (tilde M, tilde N)).val x
  exact (tensorUnitStalkLinearEquiv R M N x).symm.toLinearMap.comp
    (comparisonStalkLinear R M N x)

private noncomputable def rawThenGenericLinear (x : Spec R) :=
  (PresheafOfModulesOfCommRing.stalkTensorEquiv (Spec R).presheaf
    (tilde M).val (tilde N).val x).toLinearMap.comp
      (rawStalkComparisonLinear R M N x)

private theorem tensorUnitStalkLinearEquiv_symm_apply (x : Spec R)
    (z : ((tensorFunctor (Spec R)).obj (tilde M, tilde N)).presheaf.stalk x) :
    (tensorUnitStalkLinearEquiv R M N x).symm z =
      inv (tensorUnitStalk R M N x) (I := tensorUnitStalk_isIso R M N x) z := by
  apply (tensorUnitStalkLinearEquiv R M N x).injective
  have hleft : (tensorUnitStalkLinearEquiv R M N x)
      ((tensorUnitStalkLinearEquiv R M N x).symm z) = z :=
    (tensorUnitStalkLinearEquiv R M N x).apply_symm_apply z
  have hright : (tensorUnitStalkLinearEquiv R M N x)
      (inv (tensorUnitStalk R M N x)
        (I := tensorUnitStalk_isIso R M N x) z) = z := by
    rw [show (tensorUnitStalkLinearEquiv R M N x)
        (inv (tensorUnitStalk R M N x)
          (I := tensorUnitStalk_isIso R M N x) z) =
      (tensorUnitStalk R M N x).hom
        (inv (tensorUnitStalk R M N x)
          (I := tensorUnitStalk_isIso R M N x) z) from
      tensorUnitStalkLinear_apply R M N x _]
    exact ConcreteCategory.congr_hom
      (IsIso.inv_hom_id (I := tensorUnitStalk_isIso R M N x)
        (tensorUnitStalk R M N x)) z
  exact hleft.trans hright.symm

private theorem rawStalkComparisonLinear_apply (x : Spec R)
    (z : (tilde (M ⊗ N)).presheaf.stalk x) :
    rawStalkComparisonLinear R M N x z = (rawStalkComparison R M N x).hom z := by
  change (tensorUnitStalkLinearEquiv R M N x).symm
      (comparisonStalkLinear R M N x z) = _
  rw [comparisonStalkLinear_apply]
  change (tensorUnitStalkLinearEquiv R M N x).symm
      ((comparisonStalk R M N x).hom z) =
    inv (tensorUnitStalk R M N x) (I := tensorUnitStalk_isIso R M N x)
      ((comparisonStalk R M N x).hom z)
  exact tensorUnitStalkLinearEquiv_symm_apply R M N x _

private theorem rawThenGenericLinear_apply (x : Spec R)
    (z : (tilde (M ⊗ N)).presheaf.stalk x) :
    rawThenGenericLinear R M N x z = rawThenGeneric R M N x z := by
  change PresheafOfModulesOfCommRing.stalkTensorEquiv (Spec R).presheaf
      (tilde M).val (tilde N).val x (rawStalkComparisonLinear R M N x z) = _
  rw [rawStalkComparisonLinear_apply]
  rfl


private noncomputable def affineTopSection (L : ModuleCat.{u} R) (l : L) :
    Γ(tilde L, ⊤) :=
  (tilde.toOpen L ⊤).hom l

private theorem toStalk_eq_germ_top (L : ModuleCat.{u} R) (x : Spec R) (l : L) :
    (tilde.toStalk L x).hom l =
      TopCat.Presheaf.germ (tilde L).presheaf ⊤ x trivial
        (affineTopSection R L l) := by
  rfl

private theorem toStalk_eq_germ_top_toOpen (L : ModuleCat.{u} R) (x : Spec R) (l : L) :
    (tilde.toStalk L x).hom l =
      TopCat.Presheaf.germ (tilde L).presheaf ⊤ x trivial
        ((tilde.toOpen L ⊤).hom l) := by
  exact toStalk_eq_germ_top R L x l

private theorem rawThenGeneric_tmul (x : Spec R) (m : M) (n : N) :
    rawThenGeneric R M N x ((tilde.toStalk (M ⊗ N) x).hom (m ⊗ₜ[R] n)) =
      (tilde.toStalk M x).hom m ⊗ₜ[(Spec R).presheaf.stalk x]
        (tilde.toStalk N x).hom n := by
  unfold rawThenGeneric
  rw [toStalk_eq_germ_top]
  dsimp [rawStalkComparison, comparisonStalk, tensorUnitStalk]
  change PresheafOfModulesOfCommRing.stalkTensorEquiv (Spec R).presheaf
      (tilde M).val (tilde N).val x
      (inv (tensorUnitStalk R M N x) (I := tensorUnitStalk_isIso R M N x)
        (comparisonStalk R M N x
          (TopCat.Presheaf.germ (tilde (M ⊗ N)).presheaf ⊤ x trivial
            (affineTopSection R (M ⊗ N) (m ⊗ₜ[R] n))))) = _
  rw [show comparisonStalk R M N x
        (TopCat.Presheaf.germ (tilde (M ⊗ N)).presheaf ⊤ x trivial
          (affineTopSection R (M ⊗ N) (m ⊗ₜ[R] n))) = _ from
    TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x trivial
      ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).map
        (comparisonHom R M N)).hom
      (affineTopSection R (M ⊗ N) (m ⊗ₜ[R] n))]
  change PresheafOfModulesOfCommRing.stalkTensorEquiv (Spec R).presheaf
      (tilde M).val (tilde N).val x
      (inv (tensorUnitStalk R M N x) (I := tensorUnitStalk_isIso R M N x)
        (TopCat.Presheaf.germ
          ((tensorFunctor (Spec R)).obj (tilde M, tilde N)).presheaf ⊤ x trivial
            ((comparisonHom R M N).app ⊤
              ((tilde.toOpen (M ⊗ N) ⊤).hom (m ⊗ₜ[R] n))))) = _
  rw [comparisonHom_app_top_tmul_toOpen]
  let sM := (tilde.toOpen M ⊤).hom m
  let sN := (tilde.toOpen N ⊤).hom n
  let s : ((tilde M).val ⊗ (tilde N).val).obj (op ⊤) := sM ⊗ₜ sN
  have hunit := TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x trivial
      ((PresheafOfModules.toPresheaf (Spec R).ringCatSheaf.obj).map
        (tensorUnit (tilde M) (tilde N))) s
  change tensorUnitStalk R M N x
        (TopCat.Presheaf.germ ((tilde M).val ⊗ (tilde N).val).presheaf
          ⊤ x trivial s) =
      TopCat.Presheaf.germ
        ((tensorFunctor (Spec R)).obj (tilde M, tilde N)).presheaf ⊤ x trivial
          (((tensorUnit (tilde M) (tilde N)).app (op ⊤)).hom s) at hunit
  dsimp [s] at hunit
  change tensorUnitStalk R M N x
        (TopCat.Presheaf.germ ((tilde M).val ⊗ (tilde N).val).presheaf
          ⊤ x trivial (sM ⊗ₜ sN)) =
      TopCat.Presheaf.germ
        ((tensorFunctor (Spec R)).obj (tilde M, tilde N)).presheaf ⊤ x trivial
          (tmul (tilde M) (tilde N) ⊤ sM sN) at hunit
  rw [← hunit]
  have hinv : inv (tensorUnitStalk R M N x) (I := tensorUnitStalk_isIso R M N x)
        (tensorUnitStalk R M N x
          (TopCat.Presheaf.germ ((tilde M).val ⊗ (tilde N).val).presheaf
            ⊤ x trivial s)) =
      TopCat.Presheaf.germ ((tilde M).val ⊗ (tilde N).val).presheaf
        ⊤ x trivial s := by
    exact ConcreteCategory.congr_hom
      (IsIso.hom_inv_id (I := tensorUnitStalk_isIso R M N x)
        (tensorUnitStalk R M N x)) _
  rw [hinv]
  dsimp [s, sM, sN]
  calc
    _ = TopCat.Presheaf.germ (tilde M).presheaf ⊤ x trivial
          ((tilde.toOpen M ⊤).hom m) ⊗ₜ[(Spec R).presheaf.stalk x]
        TopCat.Presheaf.germ (tilde N).presheaf ⊤ x trivial
          ((tilde.toOpen N ⊤).hom n) :=
      PresheafOfModulesOfCommRing.stalkTensorEquiv_germ_tmul
        (Spec R).presheaf (tilde M).val (tilde N).val x ⊤ trivial
          ((tilde.toOpen M ⊤).hom m) ((tilde.toOpen N ⊤).hom n)
    _ = _ := by
      rw [← toStalk_eq_germ_top_toOpen, ← toStalk_eq_germ_top_toOpen]


private local instance tildeStalkScalarTower (L : ModuleCat.{u} R) (x : Spec R) :
    IsScalarTower R ((Spec R).presheaf.stalk x) ((tilde L).presheaf.stalk x) :=
  .of_algebraMap_smul fun _ _ ↦ rfl

private noncomputable local instance tensorStalkModuleR (x : Spec R) :
    Module R
      (TensorProduct ((Spec R).presheaf.stalk x)
        ((tilde M).presheaf.stalk x) ((tilde N).presheaf.stalk x)) :=
  Module.compHom _ (algebraMap R ((Spec R).presheaf.stalk x))

private noncomputable def localizedPureTensor (x : Spec R) :
    TensorProduct R M N →ₗ[R]
      TensorProduct ((Spec R).presheaf.stalk x)
        ((tilde M).presheaf.stalk x) ((tilde N).presheaf.stalk x) :=
  (ModuleCat.MonoidalCategory.tensorLift
    (M₁ := M) (M₂ := N)
    (M₃ := ModuleCat.of R
      (TensorProduct ((Spec R).presheaf.stalk x)
        ((tilde M).presheaf.stalk x) ((tilde N).presheaf.stalk x)))
    (fun m n ↦ (tilde.toStalk M x).hom m ⊗ₜ[(Spec R).presheaf.stalk x]
      (tilde.toStalk N x).hom n)
    (by intros; rw [map_add, TensorProduct.add_tmul])
    (by
      intro r m n
      have hM : (tilde.toStalk M x).hom (r • m) =
          r • (tilde.toStalk M x).hom m :=
        (tilde.toStalk M x).hom.map_smul r m
      rw [hM]
      change ((Spec R).presheaf.germ ⊤ x trivial
        (algebraMap R ((Spec R).presheaf.obj (op ⊤)) r) •
          (tilde.toStalk M x).hom m) ⊗ₜ _ = _
      rfl)
    (by intros; rw [map_add, TensorProduct.tmul_add])
    (by
      intro r m n
      have hN : (tilde.toStalk N x).hom (r • n) =
          r • (tilde.toStalk N x).hom n :=
        (tilde.toStalk N x).hom.map_smul r n
      rw [hN]
      change _ ⊗ₜ ((Spec R).presheaf.germ ⊤ x trivial
        (algebraMap R ((Spec R).presheaf.obj (op ⊤)) r) •
        (tilde.toStalk N x).hom n) = _
      rw [TensorProduct.tmul_smul]
      change _ = (Spec R).presheaf.germ ⊤ x trivial
        (algebraMap R ((Spec R).presheaf.obj (op ⊤)) r) • (_ ⊗ₜ _)
      rfl)).hom

private noncomputable local instance tildeToStalk_isLocalized
    (L : ModuleCat.{u} R) (x : Spec R) :
    IsLocalizedModule x.asIdeal.primeCompl (tilde.toStalk L x).hom := by
  let p : PrimeSpectrum R := x
  change IsLocalizedModule p.asIdeal.primeCompl
    (StructureSheaf.toStalkₗ R L p)
  infer_instance

private noncomputable def localizedTensorOverR (x : Spec R) :
    TensorProduct R M N →ₗ[R]
      TensorProduct R ((tilde M).presheaf.stalk x) ((tilde N).presheaf.stalk x) :=
  TensorProduct.map (tilde.toStalk M x).hom (tilde.toStalk N x).hom

private noncomputable local instance localizedTensorOverR_isLocalized (x : Spec R) :
    IsLocalizedModule x.asIdeal.primeCompl (localizedTensorOverR R M N x) := by
  unfold localizedTensorOverR
  exact IsLocalization.instIsLocalizedModuleTensorProductMap
    x.asIdeal.primeCompl (tilde.toStalk M x).hom N
      ((tilde N).presheaf.stalk x) (tilde.toStalk N x).hom

private local instance tensorOverRScalarTower (x : Spec R) :
    IsScalarTower R ((Spec R).presheaf.stalk x)
      (TensorProduct R ((tilde M).presheaf.stalk x) ((tilde N).presheaf.stalk x)) :=
  .of_algebraMap_smul fun r z ↦ by
    induction z using TensorProduct.inductionOn with
    | tmul m n => rfl
    | add a b ha hb => simp [ha, hb]

private local instance tensorOverStalkScalarTower (x : Spec R) :
    IsScalarTower R ((Spec R).presheaf.stalk x)
      (TensorProduct ((Spec R).presheaf.stalk x)
        ((tilde M).presheaf.stalk x) ((tilde N).presheaf.stalk x)) :=
  .of_algebraMap_smul fun _ _ ↦ rfl

private noncomputable def tensorLocalizationEquiv (x : Spec R) :
    TensorProduct R ((tilde M).presheaf.stalk x) ((tilde N).presheaf.stalk x) ≃ₗ[R]
      TensorProduct ((Spec R).presheaf.stalk x)
        ((tilde M).presheaf.stalk x) ((tilde N).presheaf.stalk x) :=
  let e := (IsLocalization.moduleTensorEquiv x.asIdeal.primeCompl
    ((Spec R).presheaf.stalk x) ((tilde M).presheaf.stalk x)
      ((tilde N).presheaf.stalk x)).symm
  { __ := e.toAddEquiv
    map_smul' := fun r z ↦ by
      change e (algebraMap R ((Spec R).presheaf.stalk x) r • z) =
        algebraMap R ((Spec R).presheaf.stalk x) r • e z
      exact e.map_smul _ _ }

private theorem localizedPureTensor_tmul (x : Spec R) (m : M) (n : N) :
    localizedPureTensor R M N x (m ⊗ₜ[R] n) =
      (tilde.toStalk M x).hom m ⊗ₜ[(Spec R).presheaf.stalk x]
        (tilde.toStalk N x).hom n := by
  rfl

private theorem localizedTensorOverR_tmul (x : Spec R) (m : M) (n : N) :
    localizedTensorOverR R M N x (m ⊗ₜ[R] n) =
      (tilde.toStalk M x).hom m ⊗ₜ[R] (tilde.toStalk N x).hom n := by
  rfl

private theorem tensorLocalizationEquiv_tmul (x : Spec R)
    (m : (tilde M).presheaf.stalk x) (n : (tilde N).presheaf.stalk x) :
    tensorLocalizationEquiv R M N x (m ⊗ₜ[R] n) =
      m ⊗ₜ[(Spec R).presheaf.stalk x] n := by
  change TensorProduct.mapOfCompatibleSMul
      ((Spec R).presheaf.stalk x) R ((Spec R).presheaf.stalk x)
        ((tilde M).presheaf.stalk x) ((tilde N).presheaf.stalk x)
          (m ⊗ₜ[R] n) = _
  rfl

private theorem localizedPureTensor_eq (x : Spec R) :
    localizedPureTensor R M N x =
      (tensorLocalizationEquiv R M N x).toLinearMap.comp
        (localizedTensorOverR R M N x) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul m n =>
      rw [localizedPureTensor_tmul, LinearMap.comp_apply,
        localizedTensorOverR_tmul]
      exact (tensorLocalizationEquiv_tmul R M N x _ _).symm
  | add a b ha hb => simp [ha, hb]

private noncomputable local instance localizedPureTensor_isLocalized (x : Spec R) :
    IsLocalizedModule x.asIdeal.primeCompl (localizedPureTensor R M N x) := by
  rw [localizedPureTensor_eq]
  exact IsLocalizedModule.of_linearEquiv x.asIdeal.primeCompl
    (localizedTensorOverR R M N x) (tensorLocalizationEquiv R M N x)

private noncomputable def rawThenGenericRLinear (x : Spec R) :
    (tilde (M ⊗ N)).presheaf.stalk x →ₗ[R]
      TensorProduct ((Spec R).presheaf.stalk x)
        ((tilde M).presheaf.stalk x) ((tilde N).presheaf.stalk x) where
  toFun := rawThenGenericLinear R M N x
  map_add' := map_add (rawThenGenericLinear R M N x)
  map_smul' r z := by
    let _ : Module ((Spec R).presheaf.stalk x)
        (PStalk (Spec R).presheaf (tilde (M ⊗ N)).val x) :=
      affinePresheafStalkModule R (tilde (M ⊗ N)).val x
    change rawThenGenericLinear R M N x
        (algebraMap R ((Spec R).presheaf.stalk x) r • z) =
      algebraMap R ((Spec R).presheaf.stalk x) r •
        rawThenGenericLinear R M N x z
    exact (rawThenGenericLinear R M N x).map_smul _ _

private theorem rawThenGenericRLinear_apply (x : Spec R)
    (z : (tilde (M ⊗ N)).presheaf.stalk x) :
    rawThenGenericRLinear R M N x z = rawThenGeneric R M N x z := by
  exact rawThenGenericLinear_apply R M N x z

private noncomputable def canonicalStalkTensorEquiv (x : Spec R) :
    (tilde (M ⊗ N)).presheaf.stalk x ≃ₗ[R]
      TensorProduct ((Spec R).presheaf.stalk x)
        ((tilde M).presheaf.stalk x) ((tilde N).presheaf.stalk x) :=
  @IsLocalizedModule.linearEquiv (R := R) _ x.asIdeal.primeCompl
    (M := TensorProduct R M N)
    (M' := (tilde (M ⊗ N)).presheaf.stalk x)
    (M'' := TensorProduct ((Spec R).presheaf.stalk x)
      ((tilde M).presheaf.stalk x) ((tilde N).presheaf.stalk x))
    _ _ _ _ _ _
    (tilde.toStalk (M ⊗ N) x).hom (localizedPureTensor R M N x)
      (tildeToStalk_isLocalized R (M ⊗ N) x)
      (localizedPureTensor_isLocalized R M N x)

private theorem rawThenGenericRLinear_eq_canonical (x : Spec R) :
    rawThenGenericRLinear R M N x =
      (canonicalStalkTensorEquiv R M N x).toLinearMap := by
  apply @IsLocalizedModule.linearMap_ext (R := R) _ x.asIdeal.primeCompl
    (M := TensorProduct R M N)
    (M' := (tilde (M ⊗ N)).presheaf.stalk x)
    _ _ _ _
    (tilde.toStalk (M ⊗ N) x).hom
      (tildeToStalk_isLocalized R (M ⊗ N) x)
    (N := TensorProduct R M N)
    (N' := TensorProduct ((Spec R).presheaf.stalk x)
      ((tilde M).presheaf.stalk x) ((tilde N).presheaf.stalk x))
    _ _ _ _
    (localizedPureTensor R M N x)
      (localizedPureTensor_isLocalized R M N x)
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul m n =>
      change rawThenGenericRLinear R M N x
          ((tilde.toStalk (M ⊗ N) x).hom (m ⊗ₜ[R] n)) =
        canonicalStalkTensorEquiv R M N x
          ((tilde.toStalk (M ⊗ N) x).hom (m ⊗ₜ[R] n))
      rw [rawThenGenericRLinear_apply, rawThenGeneric_tmul]
      have hcanonical : canonicalStalkTensorEquiv R M N x
          ((tilde.toStalk (M ⊗ N) x).hom (m ⊗ₜ[R] n)) =
          localizedPureTensor R M N x (m ⊗ₜ[R] n) := by
        unfold canonicalStalkTensorEquiv
        exact @IsLocalizedModule.linearEquiv_apply (R := R) _ x.asIdeal.primeCompl
          (M := TensorProduct R M N)
          (M' := (tilde (M ⊗ N)).presheaf.stalk x)
          (M'' := TensorProduct ((Spec R).presheaf.stalk x)
            ((tilde M).presheaf.stalk x) ((tilde N).presheaf.stalk x))
          _ _ _ _ _ _
          (tilde.toStalk (M ⊗ N) x).hom (localizedPureTensor R M N x)
          (tildeToStalk_isLocalized R (M ⊗ N) x)
          (localizedPureTensor_isLocalized R M N x) (m ⊗ₜ[R] n)
      rw [hcanonical, localizedPureTensor_tmul]
  | add a b ha hb => simp [ha, hb]

private theorem rawThenGeneric_bijective (x : Spec R) :
    Function.Bijective (rawThenGeneric R M N x) := by
  have hcanonical : Function.Bijective
      (canonicalStalkTensorEquiv R M N x) :=
    (canonicalStalkTensorEquiv R M N x).bijective
  have hlin : Function.Bijective (rawThenGenericRLinear R M N x) := by
    have hfun :
        (rawThenGenericRLinear R M N x :
          (tilde (M ⊗ N)).presheaf.stalk x →
            TensorProduct ((Spec R).presheaf.stalk x)
              ((tilde M).presheaf.stalk x) ((tilde N).presheaf.stalk x)) =
        (canonicalStalkTensorEquiv R M N x :
          (tilde (M ⊗ N)).presheaf.stalk x →
            TensorProduct ((Spec R).presheaf.stalk x)
              ((tilde M).presheaf.stalk x) ((tilde N).presheaf.stalk x)) := by
      funext z
      exact LinearMap.congr_fun (rawThenGenericRLinear_eq_canonical R M N x) z
    exact hfun.symm ▸ hcanonical
  have hfun :
      (rawThenGenericRLinear R M N x :
        (tilde (M ⊗ N)).presheaf.stalk x →
          TensorProduct ((Spec R).presheaf.stalk x)
            ((tilde M).presheaf.stalk x) ((tilde N).presheaf.stalk x)) =
      (rawThenGeneric R M N x :
        (tilde (M ⊗ N)).presheaf.stalk x →
          TensorProduct ((Spec R).presheaf.stalk x)
            ((tilde M).presheaf.stalk x) ((tilde N).presheaf.stalk x)) := by
    funext z
    exact rawThenGenericRLinear_apply R M N x z
  exact hfun ▸ hlin

private theorem rawStalkComparison_bijective (x : Spec R) :
    Function.Bijective (rawStalkComparison R M N x) := by
  let e := PresheafOfModulesOfCommRing.stalkTensorEquiv (Spec R).presheaf
    (tilde M).val (tilde N).val x
  apply (Function.Bijective.of_comp_iff' e.bijective
    (rawStalkComparison R M N x)).mp
  change Function.Bijective (rawThenGeneric R M N x)
  exact rawThenGeneric_bijective R M N x

private theorem rawStalkComparison_isIso (x : Spec R) :
    IsIso (rawStalkComparison R M N x) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    (rawStalkComparison_bijective R M N x)


private theorem comparisonStalk_isIso (x : Spec R) :
    IsIso (comparisonStalk R M N x) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  let e := @asIso AddCommGrpCat _ _ _ (tensorUnitStalk R M N x)
    (tensorUnitStalk_isIso R M N x)
  have hinv : Function.Bijective e.inv :=
    ConcreteCategory.bijective_of_isIso e.inv
  apply (Function.Bijective.of_comp_iff' hinv
    (comparisonStalk R M N x)).mp
  change Function.Bijective (rawStalkComparison R M N x)
  exact rawStalkComparison_bijective R M N x

private theorem comparisonHom_isIso : IsIso (comparisonHom R M N) := by
  have hreflect : (SheafOfModules.toSheaf.{u}
      (Spec R).ringCatSheaf).ReflectsIsomorphisms :=
    PresheafOfModules.instReflectsIsomorphismsSheafOfModulesSheafAddCommGrpCatToSheaf_1
  have hmap : IsIso ((SheafOfModules.toSheaf.{u}
      (Spec R).ringCatSheaf).map (comparisonHom R M N)) := by
    apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso
      ((SheafOfModules.toSheaf.{u} (Spec R).ringCatSheaf).map
        (comparisonHom R M N))).mpr
    intro x
    exact comparisonStalk_isIso R M N x
  exact (@isIso_iff_of_reflects_iso
    (C := SheafOfModules.{u} (Spec R).ringCatSheaf) _
    (D := Sheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}) _
    _ _
    (f := comparisonHom R M N)
    (F := SheafOfModules.toSheaf.{u} (Spec R).ringCatSheaf) hreflect).mp hmap

private noncomputable def comparisonNatIso :
    MonoidalCategory.tensor (ModuleCat.{u} R) ⋙ (tilde.functor R) ≅
      (tilde.functor R).prod (tilde.functor R) ⋙ tensorFunctor (Spec R) :=
  NatIso.ofComponents
    (fun P ↦ @asIso _ _ _ _ (comparisonHom R P.1 P.2)
      (comparisonHom_isIso R P.1 P.2))
    (by
      intro P Q f
      exact comparisonHom_naturality R P.1 P.2 f.1 f.2)

/-- On an affine scheme, tensoring the associated sheaves agrees naturally with
associating a sheaf to the tensor product of modules. This compares with the
existing sheafified presheaf tensor, for arbitrary modules and any commutative ring. -/
noncomputable def affineTensorNatIso :
    (tilde.functor R).prod (tilde.functor R) ⋙ tensorFunctor (Spec R) ≅
      MonoidalCategory.tensor (ModuleCat.{u} R) ⋙ (tilde.functor R) :=
  (comparisonNatIso R).symm

/-- On global pure tensors, the inverse affine comparison is the tensor of the
corresponding top-open sections. -/
theorem affineTensorNatIso_inv_app_top_tmul (m : M) (n : N) :
    ((affineTensorNatIso R).inv.app (M, N)).app ⊤
        ((tilde.toOpen (M ⊗ N) ⊤).hom (m ⊗ₜ[R] n)) =
      tmul (tilde M) (tilde N) ⊤
        ((tilde.toOpen M ⊤).hom m) ((tilde.toOpen N ⊤).hom n) := by
  exact comparisonHom_app_top_tmul_toOpen R M N m n

end AlgebraicGeometry.Scheme.Modules
