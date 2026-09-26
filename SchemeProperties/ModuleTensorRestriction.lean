/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.ModuleTensor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

public section

set_option warningAsError true

/-!
# Restriction of tensor products of modules on a scheme

Restriction along an open immersion commutes with the ambient tensor product.
The comparison is natural in both module arguments and agrees with the
sheafification unit on pure tensors under the explicit section/scalar
identifications supplied by `restrictAppIso`.

The construction first compares the presheaf tensors after restriction of
scalars along a ring isomorphism. The universal property of sheafification
then induces the inverse comparison. Local bijectivity of the sheafification
unit is preserved by open restriction, so the induced sheaf morphism is an
isomorphism.

No quasicoherence, finiteness, nonemptiness, or separation hypothesis is used.
-/

open CategoryTheory MonoidalCategory TopologicalSpace
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

section

variable {R S : Type u} [CommRing R] [CommRing S]

private noncomputable def restrictScalarsTensorIso (e : R ≃+* S) (M N : ModuleCat.{u} S) :
    (ModuleCat.restrictScalars e.toRingHom).obj M ⊗
        (ModuleCat.restrictScalars e.toRingHom).obj N ≅
      (ModuleCat.restrictScalars e.toRingHom).obj (M ⊗ N) := by
  let MN : ModuleCat S := M ⊗ N
  letI : Module R M := Module.compHom M e.toRingHom
  letI : Module R N := Module.compHom N e.toRingHom
  letI : Module R MN := Module.compHom MN e.toRingHom
  let T := (ModuleCat.restrictScalars e.toRingHom).obj M ⊗
    (ModuleCat.restrictScalars e.toRingHom).obj N
  letI : Module S T := Module.compHom T e.symm.toRingHom
  let invS : M ⊗ N ⟶ ModuleCat.of S T :=
    ModuleCat.MonoidalCategory.tensorLift (R := S) (M₁ := M) (M₂ := N)
      (M₃ := ModuleCat.of S T) (fun m n ↦ (m ⊗ₜ[R] n : T))
      (by
        intro m₁ m₂ n
        exact TensorProduct.add_tmul m₁ m₂ n)
      (by
        intro s m n
        have hm : s • m = (e.symm s : R) • m := by
          change s • m = e (e.symm s) • m
          rw [e.apply_symm_apply]
        have ht : s • (m ⊗ₜ[R] n : T) = (e.symm s : R) • (m ⊗ₜ[R] n : T) := rfl
        rw [hm, ht]
        exact TensorProduct.smul_tmul' (R := R) (e.symm s) m n)
      (by
        intro m n₁ n₂
        exact TensorProduct.tmul_add m n₁ n₂)
      (by
        intro s m n
        have hn : s • n = (e.symm s : R) • n := by
          change s • n = e (e.symm s) • n
          rw [e.apply_symm_apply]
        have ht : s • (m ⊗ₜ[R] n : T) = (e.symm s : R) • (m ⊗ₜ[R] n : T) := rfl
        rw [hn, ht]
        exact TensorProduct.tmul_smul (R := R) (e.symm s) m n)
  let μ := Functor.LaxMonoidal.μ (ModuleCat.restrictScalars e.toRingHom) M N
  let μS : ModuleCat.of S T ⟶ M ⊗ N :=
    ModuleCat.ofHom
      { toFun := fun x ↦ μ.hom x
        map_add' := fun x y ↦ μ.hom.map_add x y
        map_smul' := by
          intro s x
          change μ.hom ((e.symm s : R) • x) = s • μ.hom x
          rw [μ.hom.map_smul]
          change e (e.symm s) • μ.hom x = s • μ.hom x
          rw [e.apply_symm_apply] }
  let inv : (ModuleCat.restrictScalars e.toRingHom).obj (M ⊗ N) ⟶ T :=
    ModuleCat.ofHom
      { toFun := fun x ↦ invS.hom x
        map_add' := fun x y ↦ map_add invS.hom x y
        map_smul' := by
          intro r x
          calc
            invS.hom (e r • x) = e r • invS.hom x := invS.hom.map_smul (e r) x
            _ = (r • (show T from invS.hom x) : T) := by
              change e.symm (e r) • (show T from invS.hom x) = r • (show T from invS.hom x)
              rw [e.symm_apply_apply] }
  refine ⟨μ, inv, ?_, ?_⟩
  · apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    change inv.hom
      (μ.hom
        (m ⊗ₜ[R] n)) = m ⊗ₜ[R] n
    have hμ := ModuleCat.restrictScalars_μ_tmul e.toRingHom M N m n
    rw [hμ]
    rfl
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hS : invS ≫ μS = 𝟙 (M ⊗ N) := by
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro m n
      change μ.hom (m ⊗ₜ[R] n) = m ⊗ₜ[S] n
      exact ModuleCat.restrictScalars_μ_tmul e.toRingHom M N m n
    change μ.hom (invS.hom x) = x
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hS) x

end

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

private noncomputable def restrictPresheafFunctor :
    Y.PresheafOfModules ⥤ X.PresheafOfModules :=
  let α : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf :=
    { app U := (f.appIso U.unop).inv }
  PresheafOfModules.pushforward
    (Functor.whiskerRight α (forget₂ CommRingCat RingCat))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private noncomputable def restrictPresheafTensorIso (M N : Y.PresheafOfModules) :
    (restrictPresheafFunctor f).obj M ⊗ (restrictPresheafFunctor f).obj N ≅
      (restrictPresheafFunctor f).obj (M ⊗ N) :=
  PresheafOfModulesOfCommRing.isoMk
    (fun U ↦ restrictScalarsTensorIso
      (CategoryTheory.Iso.commRingCatIsoToRingEquiv (f.appIso U.unop).symm)
      (M.obj (f.opensFunctor.op.obj U)) (N.obj (f.opensFunctor.op.obj U)))
    (by
      intro U V i
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro m n
      let m' : M.obj (f.opensFunctor.op.obj V) :=
        (M.map (f.opensFunctor.map i.unop).op).hom m
      let n' : N.obj (f.opensFunctor.op.obj V) :=
        (N.map (f.opensFunctor.map i.unop).op).hom n
      let _ : Module (Y.presheaf.obj (f.opensFunctor.op.obj V))
          (M.obj (f.opensFunctor.op.obj V)) :=
        (M.obj (f.opensFunctor.op.obj V)).isModule
      let _ : Module (Y.presheaf.obj (f.opensFunctor.op.obj V))
          (N.obj (f.opensFunctor.op.obj V)) :=
        (N.obj (f.opensFunctor.op.obj V)).isModule
      dsimp [restrictPresheafFunctor, restrictScalarsTensorIso]
      erw [ModuleCat.comp_apply,
        PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul,
        ModuleCat.restrictScalars_μ_tmul,
        ModuleCat.restrictScalars_μ_tmul,
        PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul]
      rfl)

private noncomputable def restrictedTensorUnitComparison (M N : Y.Modules) :
    (M.restrict f).val ⊗ (N.restrict f).val ⟶
      ((tensor M N).restrict f).val :=
  (restrictPresheafTensorIso f M.val N.val).hom ≫
    (restrictPresheafFunctor f).map (tensorUnit M N)

private noncomputable def restrictTensorHom (M N : Y.Modules) :
    tensor (M.restrict f) (N.restrict f) ⟶ (tensor M N).restrict f :=
  (tensorHomEquiv (M.restrict f) (N.restrict f) ((tensor M N).restrict f)).symm
    (restrictedTensorUnitComparison f M N)

set_option backward.isDefEq.respectTransparency false in
private theorem restrictTensorHom_tmul (M N : Y.Modules) (U : X.Opens)
    (s : Γ(M.restrict f, U)) (t : Γ(N.restrict f, U)) :
    (restrictTensorHom f M N).app U (tmul (M.restrict f) (N.restrict f) U s t) =
      ((tensor M N).restrictAppIso f U).inv
        (tmul M N (f ''ᵁ U) ((M.restrictAppIso f U).hom s)
          ((N.restrictAppIso f U).hom t)) := by
  unfold restrictTensorHom
  erw [tensorHomEquiv_symm_app_tmul]
  change ((tensorUnit M N).app (.op (f ''ᵁ U))).hom
      (((restrictPresheafTensorIso f M.val N.val).hom.app (.op U)).hom
        (s ⊗ₜ[X.sheaf.obj.obj (.op U)] t)) = _
  dsimp [restrictPresheafTensorIso, restrictScalarsTensorIso]
  erw [ModuleCat.restrictScalars_μ_tmul]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma tensorUnit_isLocallyInjective (M N : Y.Modules) :
    PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology Y)
      (tensorUnit M N) := by
  change Presheaf.IsLocallyInjective _
    ((PresheafOfModules.toPresheaf _).map (tensorUnit M N))
  unfold tensorUnit
  change Presheaf.IsLocallyInjective _
    (CategoryTheory.toSheafify (Opens.grothendieckTopology Y) (M.val ⊗ N.val).presheaf)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private lemma tensorUnit_isLocallySurjective (M N : Y.Modules) :
    PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology Y)
      (tensorUnit M N) := by
  change Presheaf.IsLocallySurjective _
    ((PresheafOfModules.toPresheaf _).map (tensorUnit M N))
  unfold tensorUnit
  change Presheaf.IsLocallySurjective _
    (CategoryTheory.toSheafify (Opens.grothendieckTopology Y) (M.val ⊗ N.val).presheaf)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private lemma restrictMap_tensorUnit_isLocallyInjective (M N : Y.Modules) :
    PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X)
      ((restrictPresheafFunctor f).map (tensorUnit M N)) := by
  let _ : Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y)
      ((PresheafOfModules.toPresheaf _).map (tensorUnit M N)) :=
    tensorUnit_isLocallyInjective M N
  change Presheaf.IsLocallyInjective _
    (f.opensFunctor.op.whiskerLeft
      ((PresheafOfModules.toPresheaf _).map (tensorUnit M N)))
  exact Presheaf.isLocallyInjective_whisker
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
    f.opensFunctor ((PresheafOfModules.toPresheaf _).map (tensorUnit M N))

set_option backward.isDefEq.respectTransparency false in
private lemma restrictMap_tensorUnit_isLocallySurjective (M N : Y.Modules) :
    PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X)
      ((restrictPresheafFunctor f).map (tensorUnit M N)) := by
  let _ : Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      ((PresheafOfModules.toPresheaf _).map (tensorUnit M N)) :=
    tensorUnit_isLocallySurjective M N
  change Presheaf.IsLocallySurjective _
    (f.opensFunctor.op.whiskerLeft
      ((PresheafOfModules.toPresheaf _).map (tensorUnit M N)))
  exact Presheaf.isLocallySurjective_whisker
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
    f.opensFunctor ((PresheafOfModules.toPresheaf _).map (tensorUnit M N))

set_option backward.isDefEq.respectTransparency false in
private lemma restrictedTensorUnitComparison_isLocallyInjective (M N : Y.Modules) :
    PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X)
      (restrictedTensorUnitComparison f M N) := by
  let _ : PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X)
      ((restrictPresheafFunctor f).map (tensorUnit M N)) :=
    restrictMap_tensorUnit_isLocallyInjective f M N
  unfold restrictedTensorUnitComparison
  change Presheaf.IsLocallyInjective _
    ((PresheafOfModules.toPresheaf _).map
      ((restrictPresheafTensorIso f M.val N.val).hom ≫
        (restrictPresheafFunctor f).map (tensorUnit M N)))
  rw [Functor.map_comp]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private lemma restrictedTensorUnitComparison_isLocallySurjective (M N : Y.Modules) :
    PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X)
      (restrictedTensorUnitComparison f M N) := by
  let _ : PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X)
      ((restrictPresheafFunctor f).map (tensorUnit M N)) :=
    restrictMap_tensorUnit_isLocallySurjective f M N
  unfold restrictedTensorUnitComparison
  change Presheaf.IsLocallySurjective _
    ((PresheafOfModules.toPresheaf _).map
      ((restrictPresheafTensorIso f M.val N.val).hom ≫
        (restrictPresheafFunctor f).map (tensorUnit M N)))
  rw [Functor.map_comp]
  infer_instance

private lemma tensorUnit_comp_restrictTensorHom (M N : Y.Modules) :
    tensorUnit (M.restrict f) (N.restrict f) ≫
        (SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
            (restrictTensorHom f M N) =
      restrictedTensorUnitComparison f M N := by
  rw [← tensorHomEquiv_apply]
  exact tensorHomEquiv_symm_apply_apply
    (M.restrict f) (N.restrict f) ((tensor M N).restrict f)
      (restrictedTensorUnitComparison f M N)

set_option backward.isDefEq.respectTransparency false in
private lemma restrictTensorHom_isLocallyInjective (M N : Y.Modules) :
    PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X)
      ((SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
          (restrictTensorHom f M N)) := by
  let _ : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map
        (tensorUnit (M.restrict f) (N.restrict f))) :=
    tensorUnit_isLocallyInjective (M.restrict f) (N.restrict f)
  let _ : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map
        (tensorUnit (M.restrict f) (N.restrict f))) :=
    tensorUnit_isLocallySurjective (M.restrict f) (N.restrict f)
  change Presheaf.IsLocallyInjective _
    ((PresheafOfModules.toPresheaf _).map
      ((SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
          (restrictTensorHom f M N)))
  rw [← Presheaf.comp_isLocallyInjective_iff
    (Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf _).map
      (tensorUnit (M.restrict f) (N.restrict f)))]
  rw [← Functor.map_comp, tensorUnit_comp_restrictTensorHom]
  exact restrictedTensorUnitComparison_isLocallyInjective f M N

set_option backward.isDefEq.respectTransparency false in
private lemma restrictTensorHom_isLocallySurjective (M N : Y.Modules) :
    PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X)
      ((SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
          (restrictTensorHom f M N)) := by
  let _ : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map
        (tensorUnit (M.restrict f) (N.restrict f))) :=
    tensorUnit_isLocallySurjective (M.restrict f) (N.restrict f)
  change Presheaf.IsLocallySurjective _
    ((PresheafOfModules.toPresheaf _).map
      ((SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
          (restrictTensorHom f M N)))
  rw [← Presheaf.comp_isLocallySurjective_iff
    (Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf _).map
      (tensorUnit (M.restrict f) (N.restrict f)))]
  rw [← Functor.map_comp, tensorUnit_comp_restrictTensorHom]
  exact restrictedTensorUnitComparison_isLocallySurjective f M N

set_option backward.isDefEq.respectTransparency false in
private theorem restrictTensorHom_isIso (M N : Y.Modules) :
    IsIso (restrictTensorHom f M N) := by
  let _ : (SheafOfModules.toSheaf X.ringCatSheaf).ReflectsIsomorphisms :=
    have : (SheafOfModules.toSheaf X.ringCatSheaf ⋙
        sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat).ReflectsIsomorphisms :=
      inferInstanceAs
        (SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.toPresheaf X.ringCatSheaf.obj).ReflectsIsomorphisms
    reflectsIsomorphisms_of_comp _
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat)
  rw [← isIso_iff_of_reflects_iso (restrictTensorHom f M N)
    (SheafOfModules.toSheaf X.ringCatSheaf)]
  apply (CategoryTheory.Sheaf.isLocallyBijective_iff_isIso _).mp
  constructor
  · change Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map
        ((SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
            (restrictTensorHom f M N)))
    exact restrictTensorHom_isLocallyInjective f M N
  · change Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map
        ((SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
            (restrictTensorHom f M N)))
    exact restrictTensorHom_isLocallySurjective f M N

private noncomputable def restrictTensorIso (M N : Y.Modules) :
    (tensor M N).restrict f ≅ tensor (M.restrict f) (N.restrict f) :=
  let _ := restrictTensorHom_isIso f M N
  (asIso (restrictTensorHom f M N)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem restrictTensorHom_naturality {M M' N N' : Y.Modules}
    (a : M ⟶ M') (b : N ⟶ N') :
    (tensorFunctor X).map
          ((restrictFunctor f).map a, (restrictFunctor f).map b) ≫
        restrictTensorHom f M' N' =
      restrictTensorHom f M N ≫
        (restrictFunctor f).map ((tensorFunctor Y).map (a, b)) := by
  apply (tensorHomEquiv (M.restrict f) (N.restrict f)
    ((tensor M' N').restrict f)).injective
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  erw [tensorHomEquiv_app_tmul, tensorHomEquiv_app_tmul]
  change (restrictTensorHom f M' N').app U.unop
      (((tensorFunctor X).map
        ((restrictFunctor f).map a, (restrictFunctor f).map b)).app U.unop
          (tmul (M.restrict f) (N.restrict f) U.unop s t)) =
    ((restrictFunctor f).map ((tensorFunctor Y).map (a, b))).app U.unop
      ((restrictTensorHom f M N).app U.unop
        (tmul (M.restrict f) (N.restrict f) U.unop s t))
  rw [tensorFunctor_map_app_tmul, restrictTensorHom_tmul,
    restrictTensorHom_tmul]
  change tmul M' N' (f ''ᵁ U.unop) (a.app (f ''ᵁ U.unop) s)
      (b.app (f ''ᵁ U.unop) t) =
    ((tensorFunctor Y).map (a, b)).app (f ''ᵁ U.unop)
      (tmul M N (f ''ᵁ U.unop) s t)
  rw [tensorFunctor_map_app_tmul]

private noncomputable def tensorRestrictNatIso :
    (restrictFunctor f).prod (restrictFunctor f) ⋙ tensorFunctor X ≅
      tensorFunctor Y ⋙ restrictFunctor f :=
  NatIso.ofComponents
    (fun MN ↦ (restrictTensorIso f MN.1 MN.2).symm)
    (fun {_ _} g ↦ restrictTensorHom_naturality f g.1 g.2)

/-- Restriction along an open immersion commutes with the ambient module tensor,
naturally in both module arguments. -/
noncomputable def restrictTensorNatIso :
    tensorFunctor Y ⋙ restrictFunctor f ≅
      (restrictFunctor f).prod (restrictFunctor f) ⋙ tensorFunctor X :=
  (tensorRestrictNatIso f).symm

/-- The inverse tensor-restriction comparison sends a pure tensor to the
restricted pure tensor, with section and scalar identifications explicit.
This is its compatibility with the ambient tensor's sheafification unit. -/
theorem restrictTensorNatIso_inv_app_tmul (M N : Y.Modules) (U : X.Opens)
    (s : Γ(M.restrict f, U)) (t : Γ(N.restrict f, U)) :
    ((restrictTensorNatIso f).inv.app (M, N)).app U
        (tmul (M.restrict f) (N.restrict f) U s t) =
      ((tensor M N).restrictAppIso f U).inv
        (tmul M N (f ''ᵁ U) ((M.restrictAppIso f U).hom s)
          ((N.restrictAppIso f U).hom t)) :=
  restrictTensorHom_tmul f M N U s t

end

end AlgebraicGeometry.Scheme.Modules
