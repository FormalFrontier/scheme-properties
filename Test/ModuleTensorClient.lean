module

import SchemeProperties.ModuleTensor

set_option warningAsError true

open CategoryTheory Limits MonoidalCategory TopologicalSpace ZeroObject
open scoped AlgebraicGeometry

universe u

noncomputable section

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

variable {X : Scheme.{u}} (M N P : X.Modules) (U : X.Opens)

private def check_1 : X.Modules × X.Modules ⥤ X.Modules := tensorFunctor X
private def check_2 : X.Modules := tensor M N
private theorem check_3 : (tensorFunctor X).obj (M, N) = tensor M N := tensorFunctor_obj M N
private def check_4 : M.val ⊗ N.val ⟶ (tensor M N).val := tensorUnit M N

private def check_5 (s : Γ(M, U)) (t : Γ(N, U)) : Γ(tensor M N, U) := tmul M N U s t
private theorem check_6 (s : Γ(M, U)) (t : Γ(N, U)) :
    ((tensorUnit M N).app (.op U)).hom
      (s ⊗ₜ[X.sheaf.obj.obj (.op U)] t) = tmul M N U s t :=
  tensorUnit_app_tmul M N U s t
private theorem check_7 (t : Γ(N, U)) : tmul M N U 0 t = 0 := zero_tmul M N U t
private theorem check_8 (s : Γ(M, U)) : tmul M N U s 0 = 0 := tmul_zero M N U s
private theorem check_9 (s s' : Γ(M, U)) (t : Γ(N, U)) :
    tmul M N U (s + s') t = tmul M N U s t + tmul M N U s' t :=
  add_tmul M N U s s' t
private theorem check_10 (s : Γ(M, U)) (t t' : Γ(N, U)) :
    tmul M N U s (t + t') = tmul M N U s t + tmul M N U s t' :=
  tmul_add M N U s t t'
private theorem check_11 (r : Γ(X, U)) (s : Γ(M, U)) (t : Γ(N, U)) :
    tmul M N U (r • s) t = r • tmul M N U s t := smul_tmul M N U r s t
private theorem check_12 (r : Γ(X, U)) (s : Γ(M, U)) (t : Γ(N, U)) :
    tmul M N U s (r • t) = r • tmul M N U s t := tmul_smul M N U r s t
private theorem check_13 {V : X.Opens} (i : U ⟶ V) (s : Γ(M, V)) (t : Γ(N, V)) :
    (tensor M N).presheaf.map i.op (tmul M N V s t) =
      tmul M N U (M.presheaf.map i.op s) (N.presheaf.map i.op t) :=
  map_tmul M N i s t

private def check_14 : (tensor M N ⟶ P) ≃
    ((M.val ⊗ N.val) ⟶
      (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj P.val) :=
  tensorHomEquiv M N P
private theorem check_15 (f : tensor M N ⟶ P) :
    tensorHomEquiv M N P f = tensorUnit M N ≫
      (SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map f :=
  tensorHomEquiv_apply M N P f
private theorem check_16 (g : (M.val ⊗ N.val) ⟶
    (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj P.val) :
    tensorHomEquiv M N P ((tensorHomEquiv M N P).symm g) = g :=
  tensorHomEquiv_symm_apply_apply M N P g
private theorem check_17 (f : tensor M N ⟶ P) :
    (tensorHomEquiv M N P).symm (tensorHomEquiv M N P f) = f :=
  tensorHomEquiv_apply_symm_apply M N P f
private theorem check_18 (f : tensor M N ⟶ P) (s : Γ(M, U)) (t : Γ(N, U)) :
    ((tensorHomEquiv M N P f).app (.op U)).hom
      (s ⊗ₜ[X.sheaf.obj.obj (.op U)] t) = f.app U (tmul M N U s t) :=
  tensorHomEquiv_app_tmul M N P f U s t
private theorem check_19 (g : (M.val ⊗ N.val) ⟶
    (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj P.val)
    (s : Γ(M, U)) (t : Γ(N, U)) :
    ((tensorHomEquiv M N P).symm g).app U (tmul M N U s t) =
      (g.app (.op U)).hom (s ⊗ₜ[X.sheaf.obj.obj (.op U)] t) :=
  tensorHomEquiv_symm_app_tmul M N P g U s t

private theorem check_20 {M' N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N')
    (s : Γ(M, U)) (t : Γ(N, U)) :
    ((tensorFunctor X).map (f, g)).app U (tmul M N U s t) =
      tmul M' N' U (f.app U s) (g.app U t) :=
  tensorFunctor_map_app_tmul f g U s t
private theorem check_21 : (tensorFunctor X).map (𝟙 M, 𝟙 N) =
    𝟙 ((tensorFunctor X).obj (M, N)) := (tensorFunctor X).map_id (M, N)
private theorem check_22 {M' N' M'' N'' : X.Modules} (f : M ⟶ M') (g : N ⟶ N')
    (f' : M' ⟶ M'') (g' : N' ⟶ N'') :
    (tensorFunctor X).map ((f, g) : (M, N) ⟶ (M', N')) ≫
      (tensorFunctor X).map ((f', g') : (M', N') ⟶ (M'', N'')) =
      (tensorFunctor X).map
        (((f, g) : (M, N) ⟶ (M', N')) ≫
          ((f', g') : (M', N') ⟶ (M'', N''))) :=
  ((tensorFunctor X).map_comp
    ((f, g) : (M, N) ⟶ (M', N')) ((f', g') : (M', N') ⟶ (M'', N''))).symm

private def check_23 : tensor M N ≅ tensor N M := tensorSymm M N
private theorem check_24 (s : Γ(M, U)) (t : Γ(N, U)) :
    (tensorSymm M N).hom.app U (tmul M N U s t) = tmul N M U t s :=
  tensorSymm_hom_app_tmul M N U s t
private theorem check_25 {M' N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N') :
    (tensorFunctor X).map (f, g) ≫ (tensorSymm M' N').hom =
      (tensorSymm M N).hom ≫ (tensorFunctor X).map (g, f) :=
  tensorSymm_naturality f g

-- Degenerate cases require no extra hypotheses.
private def check_26 : X.Modules := tensor (0 : X.Modules) 0
private def check_27 : (Spec (.of PUnit.{u + 1})).Modules :=
  tensor (0 : (Spec (.of PUnit.{u + 1})).Modules) 0
private def check_28 : Scheme.empty.Modules := tensor (0 : Scheme.empty.Modules) 0
private def check_29 (s : Γ(M, (⊥ : X.Opens))) (t : Γ(N, (⊥ : X.Opens))) :
    Γ(tensor M N, (⊥ : X.Opens)) := tmul M N ⊥ s t

end AlgebraicGeometry.Scheme.Modules
