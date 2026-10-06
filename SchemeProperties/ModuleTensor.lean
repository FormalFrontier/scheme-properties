/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

public section

set_option warningAsError true

/-!
# Tensor products of modules on a scheme

This module constructs the ambient tensor product of two modules on a scheme by
sheafifying their pointwise presheaf tensor product. It supplies the bifunctor,
the sheafification unit, pure tensor sections and their elementary laws, the
sheafification Hom equivalence, and the canonical symmetry.

No quasicoherence or finiteness hypothesis is used.

## References

- Mathlib's `Mathlib/Algebra/Category/ModuleCat/Presheaf/Monoidal.lean` supplies
  pointwise tensor products and symmetry for presheaves of modules.
- Mathlib's `Mathlib/Algebra/Category/ModuleCat/Presheaf/Sheafification.lean`
  supplies the module sheafification adjunction and Hom equivalence. The
  scheme-module tensor bifunctor and its pure-tensor API are assembled here.
-/

open CategoryTheory MonoidalCategory BraidedCategory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

/-- The pointwise monoidal tensor structure on presheaves of modules, used
locally to define the ambient sheaf tensor product. -/
noncomputable local instance pointwiseMonoidalCategoryStruct (X : Scheme.{u}) :
    MonoidalCategoryStruct X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategoryStruct (R := X.sheaf.obj)

/-- The pointwise monoidal category on presheaves of modules; its instance
scope is confined to this module. -/
noncomputable local instance pointwiseMonoidalCategory (X : Scheme.{u}) :
    MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.sheaf.obj)

/-- The pointwise symmetric structure on presheaves of modules, registered
locally for the tensor bifunctor and its symmetry. -/
noncomputable local instance pointwiseSymmetricCategory (X : Scheme.{u}) :
    SymmetricCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.symmetricCategory (R := X.sheaf.obj)

/-- The ambient tensor bifunctor on modules over `X`, obtained by pointwise
presheaf tensor followed by sheafification. -/
@[expose]
noncomputable def tensorFunctor (X : Scheme.{u}) :
    X.Modules × X.Modules ⥤ X.Modules := by
  letI : MonoidalCategoryStruct X.PresheafOfModules :=
    PresheafOfModulesOfCommRing.monoidalCategoryStruct (R := X.sheaf.obj)
  letI : MonoidalCategory X.PresheafOfModules :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.sheaf.obj)
  letI : SymmetricCategory X.PresheafOfModules :=
    PresheafOfModulesOfCommRing.symmetricCategory (R := X.sheaf.obj)
  exact (toPresheafOfModules X).prod (toPresheafOfModules X) ⋙
    MonoidalCategory.tensor X.PresheafOfModules ⋙
      PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

private theorem tensorFunctor_eq_oldConstruction (X : Scheme.{u}) :
    tensorFunctor X =
      (toPresheafOfModules X).prod (toPresheafOfModules X) ⋙
        MonoidalCategory.tensor X.PresheafOfModules ⋙
          PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj) := by
  rfl

/-- The ambient tensor product of two modules on a scheme. -/
@[expose]
noncomputable def tensor {X : Scheme.{u}} (M N : X.Modules) : X.Modules :=
  (tensorFunctor X).obj (M, N)

/-- The tensor bifunctor evaluates to `tensor`. -/
@[simp] theorem tensorFunctor_obj {X : Scheme.{u}} (M N : X.Modules) :
    (tensorFunctor X).obj (M, N) = tensor M N := rfl

/-- The sheafification-unit morphism from the pointwise presheaf tensor to the
underlying presheaf of the ambient tensor product. -/
@[expose]
noncomputable def tensorUnit {X : Scheme.{u}} (M N : X.Modules) :
    M.val ⊗ N.val ⟶ (tensor M N).val :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app (M.val ⊗ N.val)

/-- The pure tensor of two sections over the same open. -/
@[expose]
noncomputable def tmul {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) (t : Γ(N, U)) : Γ(tensor M N, U) :=
  ((tensorUnit M N).app (.op U)).hom
    (s ⊗ₜ[X.sheaf.obj.obj (.op U)] t)

/-- The pointwise sheafification unit sends an algebraic pure tensor to `tmul`. -/
@[simp] theorem tensorUnit_app_tmul {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) (t : Γ(N, U)) :
    ((tensorUnit M N).app (.op U)).hom
        (s ⊗ₜ[X.sheaf.obj.obj (.op U)] t) = tmul M N U s t := rfl

/-- A pure tensor with zero on the left is zero. -/
@[simp] theorem zero_tmul {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (t : Γ(N, U)) : tmul M N U 0 t = 0 := by
  unfold tmul
  rw [TensorProduct.zero_tmul, map_zero]

/-- A pure tensor with zero on the right is zero. -/
@[simp] theorem tmul_zero {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) : tmul M N U s 0 = 0 := by
  unfold tmul
  rw [TensorProduct.tmul_zero, map_zero]

/-- Pure tensors are additive in the left variable. -/
@[simp] theorem add_tmul {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (s s' : Γ(M, U)) (t : Γ(N, U)) :
    tmul M N U (s + s') t = tmul M N U s t + tmul M N U s' t := by
  unfold tmul
  rw [TensorProduct.add_tmul, map_add]

/-- Pure tensors are additive in the right variable. -/
@[simp] theorem tmul_add {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) (t t' : Γ(N, U)) :
    tmul M N U s (t + t') = tmul M N U s t + tmul M N U s t' := by
  unfold tmul
  rw [TensorProduct.tmul_add, map_add]

/-- Scalars may be applied to the left factor of a pure tensor. -/
@[simp] theorem smul_tmul {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (r : Γ(X, U)) (s : Γ(M, U)) (t : Γ(N, U)) :
    tmul M N U (r • s) t = r • tmul M N U s t := by
  let _ : Module (X.sheaf.obj.obj (.op U)) Γ(M, U) := (M.val.obj (.op U)).isModule
  let _ : Module (X.sheaf.obj.obj (.op U)) Γ(N, U) := (N.val.obj (.op U)).isModule
  let _ : Module (X.sheaf.obj.obj (.op U)) Γ(tensor M N, U) :=
    ((tensor M N).val.obj (.op U)).isModule
  let r' : X.sheaf.obj.obj (.op U) := r
  unfold tmul
  change ((tensorUnit M N).app (.op U)).hom
    ((r' • s) ⊗ₜ[X.sheaf.obj.obj (.op U)] t) =
      r' • ((tensorUnit M N).app (.op U)).hom
        (s ⊗ₜ[X.sheaf.obj.obj (.op U)] t)
  rw [← TensorProduct.smul_tmul']
  exact LinearMapClass.map_smul _ _ _

/-- Scalars may be applied to the right factor of a pure tensor. -/
@[simp] theorem tmul_smul {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (r : Γ(X, U)) (s : Γ(M, U)) (t : Γ(N, U)) :
    tmul M N U s (r • t) = r • tmul M N U s t := by
  let _ : Module (X.sheaf.obj.obj (.op U)) Γ(M, U) := (M.val.obj (.op U)).isModule
  let _ : Module (X.sheaf.obj.obj (.op U)) Γ(N, U) := (N.val.obj (.op U)).isModule
  let _ : Module (X.sheaf.obj.obj (.op U)) Γ(tensor M N, U) :=
    ((tensor M N).val.obj (.op U)).isModule
  let r' : X.sheaf.obj.obj (.op U) := r
  unfold tmul
  change ((tensorUnit M N).app (.op U)).hom
    (s ⊗ₜ[X.sheaf.obj.obj (.op U)] (r' • t)) =
      r' • ((tensorUnit M N).app (.op U)).hom
        (s ⊗ₜ[X.sheaf.obj.obj (.op U)] t)
  rw [← TensorProduct.smul_tmul r' s t, ← TensorProduct.smul_tmul']
  exact LinearMapClass.map_smul _ _ _

/-- Restriction of sections commutes with pure tensors. -/
@[simp] theorem map_tmul {X : Scheme.{u}} (M N : X.Modules) {U V : X.Opens}
    (i : U ⟶ V) (s : Γ(M, V)) (t : Γ(N, V)) :
    (tensor M N).presheaf.map i.op (tmul M N V s t) =
      tmul M N U (M.presheaf.map i.op s) (N.presheaf.map i.op t) := by
  have h := PresheafOfModules.naturality_apply
    (tensorUnit M N) i.op (s ⊗ₜ[X.sheaf.obj.obj (.op V)] t)
  change tmul M N U (M.presheaf.map i.op s) (N.presheaf.map i.op t) =
    (tensor M N).presheaf.map i.op (tmul M N V s t) at h
  exact h.symm

/-- The sheafification universal property for the ambient tensor product, with
the exact presheaf-morphism codomain of `sheafificationHomEquiv`. -/
noncomputable def tensorHomEquiv {X : Scheme.{u}} (M N P : X.Modules) :
    (tensor M N ⟶ P) ≃
      ((M.val ⊗ N.val) ⟶
        (PresheafOfModules.restrictScalars
          (𝟙 X.ringCatSheaf.obj)).obj P.val) :=
  PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)

/-- The Hom equivalence sends a morphism to the unit followed by its underlying
presheaf morphism. -/
@[simp] theorem tensorHomEquiv_apply {X : Scheme.{u}} (M N P : X.Modules)
    (f : tensor M N ⟶ P) :
    tensorHomEquiv M N P f = tensorUnit M N ≫
      (SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map f := by
  change (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).homEquiv _ _ f = _
  exact (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).homEquiv_unit _ _ f

/-- Applying the Hom equivalence after its inverse returns the original
presheaf morphism. -/
theorem tensorHomEquiv_symm_apply_apply {X : Scheme.{u}} (M N P : X.Modules)
    (g : (M.val ⊗ N.val) ⟶
      (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj P.val) :
    tensorHomEquiv M N P ((tensorHomEquiv M N P).symm g) = g :=
  (tensorHomEquiv M N P).apply_symm_apply g

/-- Applying the inverse Hom equivalence after the Hom equivalence returns the
original sheaf morphism. -/
theorem tensorHomEquiv_apply_symm_apply {X : Scheme.{u}} (M N P : X.Modules)
    (f : tensor M N ⟶ P) :
    (tensorHomEquiv M N P).symm (tensorHomEquiv M N P f) = f :=
  (tensorHomEquiv M N P).symm_apply_apply f

/-- The presheaf morphism corresponding to a sheaf morphism acts on a pure
tensor by first forming `tmul`. -/
theorem tensorHomEquiv_app_tmul {X : Scheme.{u}} (M N P : X.Modules)
    (f : tensor M N ⟶ P) (U : X.Opens) (s : Γ(M, U)) (t : Γ(N, U)) :
    ((tensorHomEquiv M N P f).app (.op U)).hom
        (s ⊗ₜ[X.sheaf.obj.obj (.op U)] t) =
      f.app U (tmul M N U s t) := by
  rw [tensorHomEquiv_apply]
  rfl

/-- The inverse Hom equivalence acts on `tmul` by the supplied presheaf
morphism's action on the algebraic pure tensor. -/
@[simp] theorem tensorHomEquiv_symm_app_tmul {X : Scheme.{u}} (M N P : X.Modules)
    (g : (M.val ⊗ N.val) ⟶
      (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj P.val)
    (U : X.Opens) (s : Γ(M, U)) (t : Γ(N, U)) :
    ((tensorHomEquiv M N P).symm g).app U (tmul M N U s t) =
      (g.app (.op U)).hom (s ⊗ₜ[X.sheaf.obj.obj (.op U)] t) := by
  rw [← tensorHomEquiv_app_tmul M N P, tensorHomEquiv_symm_apply_apply]

/-- The tensor bifunctor applies a pair of morphisms factorwise to pure
tensors. -/
theorem tensorFunctor_map_app_tmul {X : Scheme.{u}}
    {M N M' N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N')
    (U : X.Opens) (s : Γ(M, U)) (t : Γ(N, U)) :
    ((tensorFunctor X).map (f, g)).app U (tmul M N U s t) =
      tmul M' N' U (f.app U s) (g.app U t) := by
  change (show tensor M N ⟶ tensor M' N' from (tensorFunctor X).map (f, g)).app U
    (tmul M N U s t) = _
  rw [← tensorHomEquiv_app_tmul M N (tensor M' N'), tensorHomEquiv_apply]
  change (((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app (M.val ⊗ N.val) ≫
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj) ⋙
        SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
            (f.val ⊗ₘ g.val)).app (.op U)).hom
              (s ⊗ₜ[X.sheaf.obj.obj (.op U)] t) = _
  have h := congrArg (fun k => (k.app (.op U)).hom
      (s ⊗ₜ[X.sheaf.obj.obj (.op U)] t))
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.naturality (f.val ⊗ₘ g.val))
  rw [← h]
  change ((tensorUnit M' N').app (.op U)).hom
    (((f.val ⊗ₘ g.val).app' (.op U)).hom
      (s ⊗ₜ[X.sheaf.obj.obj (.op U)] t)) = _
  let _ : Module (X.sheaf.obj.obj (.op U)) Γ(M', U) := (M'.val.obj (.op U)).isModule
  let _ : Module (X.sheaf.obj.obj (.op U)) Γ(N', U) := (N'.val.obj (.op U)).isModule
  have hfg : (((f.val ⊗ₘ g.val).app' (.op U)).hom
      (s ⊗ₜ[X.sheaf.obj.obj (.op U)] t)) =
        f.app U s ⊗ₜ[X.sheaf.obj.obj (.op U)] g.app U t := by
    change (((f.val.app' (.op U)) ⊗ₘ (g.val.app' (.op U))).hom
      (s ⊗ₜ[X.sheaf.obj.obj (.op U)] t)) = _
    exact ModuleCat.MonoidalCategory.tensorHom_tmul (R := X.sheaf.obj.obj (.op U))
      (f.val.app' (.op U)) (g.val.app' (.op U)) s t
  rw [hfg]
  rfl

/-- The canonical symmetry isomorphism for the ambient tensor product. -/
noncomputable def tensorSymm {X : Scheme.{u}} (M N : X.Modules) :
    tensor M N ≅ tensor N M :=
  (PresheafOfModules.sheafification
    (𝟙 X.ringCatSheaf.obj)).mapIso (braiding M.val N.val)

/-- The symmetry isomorphism exchanges the factors of a pure tensor. -/
@[simp] theorem tensorSymm_hom_app_tmul {X : Scheme.{u}} (M N : X.Modules)
    (U : X.Opens) (s : Γ(M, U)) (t : Γ(N, U)) :
    (tensorSymm M N).hom.app U (tmul M N U s t) = tmul N M U t s := by
  let _ : Module (X.sheaf.obj.obj (.op U)) Γ(M, U) := (M.val.obj (.op U)).isModule
  let _ : Module (X.sheaf.obj.obj (.op U)) Γ(N, U) := (N.val.obj (.op U)).isModule
  rw [← tensorHomEquiv_app_tmul M N (tensor N M), tensorHomEquiv_apply]
  change (((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app (M.val ⊗ N.val) ≫
      (SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
          ((PresheafOfModules.sheafification
            (𝟙 X.ringCatSheaf.obj)).map (braiding M.val N.val).hom)).app
              (.op U)).hom (s ⊗ₜ[X.sheaf.obj.obj (.op U)] t) = _
  have h := congrArg (fun k => (k.app (.op U)).hom
      (s ⊗ₜ[X.sheaf.obj.obj (.op U)] t))
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.naturality (braiding M.val N.val).hom)
  change (((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app (M.val ⊗ N.val) ≫
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj) ⋙
        SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
            (braiding M.val N.val).hom).app (.op U)).hom
              (s ⊗ₜ[X.sheaf.obj.obj (.op U)] t) = _
  rw [← h]
  change ((tensorUnit N M).app (.op U)).hom
    (((braiding M.val N.val).hom.app (.op U)).hom
      (s ⊗ₜ[X.sheaf.obj.obj (.op U)] t)) = _
  change ((tensorUnit N M).app (.op U)).hom
    (((braiding M.val N.val).hom.app' (.op U)).hom
      (s ⊗ₜ[X.sheaf.obj.obj (.op U)] t)) = _
  have hb : (((braiding M.val N.val).hom.app' (.op U)).hom
      (s ⊗ₜ[X.sheaf.obj.obj (.op U)] t)) =
        t ⊗ₜ[X.sheaf.obj.obj (.op U)] s := by
    change ((braiding (M.val.obj (.op U)) (N.val.obj (.op U))).hom).hom
      (s ⊗ₜ[X.sheaf.obj.obj (.op U)] t) = _
    exact ModuleCat.MonoidalCategory.braiding_hom_apply
      (R := X.sheaf.obj.obj (.op U)) s t
  rw [hb]
  rfl

/-- The symmetry is natural with respect to the tensor bifunctor. -/
theorem tensorSymm_naturality {X : Scheme.{u}} {M N M' N' : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N') :
    (tensorFunctor X).map (f, g) ≫ (tensorSymm M' N').hom =
      (tensorSymm M N).hom ≫ (tensorFunctor X).map (g, f) := by
  change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (f.val ⊗ₘ g.val) ≫
        (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
          (braiding M'.val N'.val).hom =
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (braiding M.val N.val).hom ≫
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (g.val ⊗ₘ f.val)
  rw [← Functor.map_comp, ← Functor.map_comp, braiding_naturality]

end AlgebraicGeometry.Scheme.Modules
