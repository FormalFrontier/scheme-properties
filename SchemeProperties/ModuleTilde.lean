/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Andrew Yang
-/
/-
Copyright (c) 2024 Weihong Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Amelia Livingston, Sophie Morel, Jujian Zhang, Weihong Xu,
  Andrew Yang, Brian Nugent
-/
/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Andrew Yang
-/
/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou
-/
/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Topology.Sheaves.Forget
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Basic.UnivLE

/-!
# Associated module sheaves

For a commutative ring `R` and an `R`-module `M`, the associated sheaf consists of
functions into the localizations of `M` which are locally represented by one
numerator and one denominator. The universe of `M` is independent of that of `R`.
Scalars are sections of the structure sheaf of `Spec R`.

## Implementation notes

The local fraction construction generalizes the module-valued construction in
`Mathlib.AlgebraicGeometry.StructureSheaf`. Its ring-valued construction and its
structure sheaf are unchanged. The underlying sheaf of types is obtained from
`TopCat.subsheafToTypes`.

## References

* `Mathlib.AlgebraicGeometry.StructureSheaf`: locally fractional sections and
  their pointwise algebraic operations.
* `Mathlib.AlgebraicGeometry.Modules.Tilde`: assembly into a sheaf of modules.
* `Mathlib.Topology.Sheaves.LocalPredicate`: subsheaves defined by local predicates.
-/

@[expose] public section

noncomputable section

universe u v

open TopCat TopologicalSpace CategoryTheory Opposite
open PrimeSpectrum (basicOpen)

namespace AlgebraicGeometry

/-- Sections of a sheaf of modules carry its given action by sections of the
structure sheaf. -/
instance Scheme.instModuleSections {X : Scheme.{u}}
    (F : SheafOfModules.{v} X.ringCatSheaf) (U : X.Opens) :
    Module Γ(X, U) (F.val.obj (op U)) :=
  (F.val.obj (op U)).isModule

/-- The module structure on sections is the one stored in the underlying module
object. -/
theorem Scheme.moduleSections_eq {X : Scheme.{u}}
    (F : SheafOfModules.{v} X.ringCatSheaf) (U : X.Opens) :
    Scheme.instModuleSections (X := X) F U = (F.val.obj (op U)).isModule := (rfl)

namespace moduleTilde

section Sections

variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

private abbrev Localizations (p : PrimeSpectrum.Top R) : Type (max u v) :=
  LocalizedModule p.asIdeal.primeCompl M

private def IsFraction {U : Opens (PrimeSpectrum.Top R)}
    (f : (p : U) → Localizations M p.1) : Prop :=
  ∃ (m : M) (s : R), ∀ p : U,
    ∃ hs : s ∉ p.1.asIdeal, f p = LocalizedModule.mk m ⟨s, hs⟩

variable (R) in
private def isFractionPrelocal : PrelocalPredicate (Localizations (R := R) M) where
  pred {_} f := IsFraction M f
  res := by
    rintro V U i f ⟨m, s, h⟩
    exact ⟨m, s, fun p ↦ h (i p)⟩

variable (R) in
private def isLocallyFraction : LocalPredicate (Localizations (R := R) M) :=
  (isFractionPrelocal R M).sheafify

private def sectionsSubmodule (U : Opens (PrimeSpectrum.Top R)) :
    Submodule R ((p : U) → Localizations M p.1) where
  carrier := {f | (isLocallyFraction R M).pred f}
  add_mem' {a b} ha hb p := by
    obtain ⟨Va, ma, ia, ra, sa, wa⟩ := ha p
    obtain ⟨Vb, mb, ib, rb, sb, wb⟩ := hb p
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia,
      sb • ra + sa • rb, sa * sb, fun q ↦ ?_⟩
    obtain ⟨hsaq, hsa⟩ := wa ⟨q.1, q.2.1⟩
    obtain ⟨hsbq, hsb⟩ := wb ⟨q.1, q.2.2⟩
    exact ⟨q.1.asIdeal.primeCompl.mul_mem hsaq hsbq,
      congr($hsa + $hsb).trans (LocalizedModule.mk_add_mk ..)⟩
  zero_mem' p :=
    ⟨U, p.2, 𝟙 _, 0, 1, fun q ↦ by simp [Ideal.IsPrime.one_notMem]⟩
  smul_mem' r {a} ha p := by
    obtain ⟨V, m, i, ra, sa, wa⟩ := ha p
    exact ⟨V, m, i, r • ra, sa, fun q ↦ ⟨(wa q).1,
      congr(r • $((wa q).2)).trans (LocalizedModule.smul'_mk ..)⟩⟩

private instance localizationModule (p : PrimeSpectrum.Top R) :
    Module (StructureSheaf.Localizations R p) (Localizations M p) :=
  OreLocalization.instModule (R := R) (S := p.asIdeal.primeCompl) (X := M)

set_option backward.isDefEq.respectTransparency false in
private def sectionsSubalgebraSubmodule (U : Opens (PrimeSpectrum.Top R)) :
    Submodule (StructureSheaf.sectionsSubalgebra R U)
      ((p : U) → Localizations M p.1) where
  __ := sectionsSubmodule M U
  smul_mem' r {a} ha p := by
    obtain ⟨V, hpV, hVU, rx, rs, hr⟩ := r.2 p
    obtain ⟨W, hpW, hWU, ax, as, ha⟩ := ha p
    refine ⟨V ⊓ W, ⟨hpV, hpW⟩, homOfLE (inf_le_left.trans hVU.le),
      rx • ax, as * rs, fun q ↦ ?_⟩
    obtain ⟨hrsq, hrq⟩ := hr ⟨q.1, q.2.1⟩
    obtain ⟨hasq, haq⟩ := ha ⟨q.1, q.2.2⟩
    exact ⟨q.1.asIdeal.primeCompl.mul_mem hasq hrsq, congr($hrq • $haq)⟩

variable (R) in
private def typeSheaf : TopCat.Sheaf (Type (max u v)) (PrimeSpectrum.Top R) :=
  subsheafToTypes (isLocallyFraction R M)

private instance sectionsAddCommGroup (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    AddCommGroup ((typeSheaf R M).obj.obj U) :=
  (sectionsSubmodule M U.unop).toAddSubgroup.toAddCommGroup

private instance sectionsModule (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    Module R ((typeSheaf R M).obj.obj U) :=
  (sectionsSubmodule M U.unop).module

private instance sectionsSectionModule (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    Module ((structureSheafInType R R).obj.obj U) ((typeSheaf R M).obj.obj U) :=
  inferInstanceAs (Module (StructureSheaf.sectionsSubalgebra R U.unop)
    (sectionsSubalgebraSubmodule M U.unop))

private instance sectionsScalarTower (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    IsScalarTower R ((structureSheafInType R R).obj.obj U)
      ((typeSheaf R M).obj.obj U) :=
  .of_algebraMap_smul fun r s ↦ Subtype.ext <| funext fun p ↦
    IsScalarTower.algebraMap_smul (StructureSheaf.Localizations R p.1) r (s.1 p)

variable (R) in
private def additivePresheaf :
    TopCat.Presheaf AddCommGrpCat.{max u v} (PrimeSpectrum.Top R) where
  obj U := AddCommGrpCat.of ((typeSheaf R M).obj.obj U)
  map i := AddCommGrpCat.ofHom
    { toFun := (typeSheaf R M).obj.map i
      map_zero' := rfl
      map_add' _ _ := rfl }
  map_id U := by
    ext s
    rfl
  map_comp i j := by
    ext s
    rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (R) in
private def modulePresheaf :
    PresheafOfModules.{max u v} (structurePresheafInCommRingCat R ⋙ forget₂ _ _) :=
  letI (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
      Module ((structurePresheafInCommRingCat R ⋙ forget₂ CommRingCat RingCat).obj U)
        ((additivePresheaf R M).obj U) := by
    dsimp [additivePresheaf]
    infer_instance
  .ofPresheaf (additivePresheaf R M) fun U V i r s ↦ rfl

variable (R) in
private theorem modulePresheaf_isSheaf :
    TopCat.Presheaf.IsSheaf (modulePresheaf R M).presheaf := by
  let : UnivLE.{u, max u v} := univLE_max
  let : Limits.HasLimitsOfSize.{u, u} AddCommGrpCat.{max u v} :=
    AddCommGrpCat.hasLimitsOfSize
  let : Limits.PreservesLimitsOfSize.{u, u}
      (forget AddCommGrpCat.{max u v}) :=
    AddCommGrpCat.forget_preservesLimitsOfSize
  let : (forget AddCommGrpCat.{max u v}).ReflectsIsomorphisms :=
    AddCommGrpCat.forget_reflects_isos
  exact (TopCat.Presheaf.isSheaf_iff_isSheaf_comp'
    (forget AddCommGrpCat.{max u v}) _).2 (typeSheaf R M).property

variable (R) in
private def numeratorLinear (U : Opens (PrimeSpectrum.Top R)) :
    M →ₗ[R] ((typeSheaf R M).obj.obj (op U)) where
  toFun m := ⟨fun p ↦ LocalizedModule.mk m 1,
    fun p ↦ ⟨U, p.2, 𝟙 _, m, 1, fun q ↦
      ⟨by simp [Ideal.IsPrime.one_notMem], rfl⟩⟩⟩
  map_add' m n := Subtype.ext <| funext fun p ↦
    (LocalizedModule.mkLinearMap p.1.asIdeal.primeCompl M).map_add m n
  map_smul' r m := Subtype.ext <| funext fun p ↦
    (LocalizedModule.mkLinearMap p.1.asIdeal.primeCompl M).map_smul r m

/-- The associated sheaf of a module, with sections given by locally fractional
functions into its localizations at prime ideals. The module and scalar ring
may belong to independent universes. -/
@[no_expose]
def _root_.AlgebraicGeometry.moduleTilde {R : CommRingCat.{u}} (M : ModuleCat.{v} R) :
    SheafOfModules.{max u v} (Spec R).ringCatSheaf where
  val := modulePresheaf R M
  isSheaf := modulePresheaf_isSheaf R M

/-- Evaluation of a section of the associated sheaf at a prime. -/
@[no_expose]
def eval {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (U : (Spec R).Opens) (p : U) :
    (moduleTilde M).val.obj (op U) →+
      LocalizedModule (p.1.asIdeal.primeCompl (hp := p.1.isPrime)) M where
  toFun s := s.1 p
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Sections of the associated sheaf are equal if their evaluations agree. -/
@[ext]
theorem ext {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    {U : (Spec R).Opens} {s t : (moduleTilde M).val.obj (op U)}
    (h : ∀ p : U, eval M U p s = eval M U p t) : s = t :=
  Subtype.ext (funext h)

private theorem local_fraction_at {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (U : (Spec R).Opens)
    (s : (moduleTilde M).val.obj (op U)) (p : U) :
    ∃ (V : (Spec R).Opens) (_hp : p.1 ∈ V) (hVU : V ≤ U) (m : M) (r : R),
      ∀ q : V, ∃ hr : r ∉ q.1.asIdeal,
        eval M U ⟨q.1, hVU q.2⟩ s = LocalizedModule.mk m ⟨r, hr⟩ := by
  obtain ⟨V, hpV, i, m, r, h⟩ := s.2 p
  refine ⟨V, hpV, i.le, m, r, ?_⟩
  intro q
  exact h q

/-- Evaluation commutes with the action of a section of the structure sheaf. -/
@[simp]
theorem eval_smul {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (U : (Spec R).Opens) (p : U) (a : Γ(Spec R, U))
    (s : (moduleTilde M).val.obj (op U)) :
    eval M U p (a • s) = a.1 p • eval M U p s := (rfl)

/-- Evaluation after restriction is evaluation at the same prime. -/
@[simp]
theorem eval_res {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    {U V : (Spec R).Opens} (h : U ≤ V)
    (s : (moduleTilde M).val.obj (op V)) (p : U) :
    eval M U p ((moduleTilde M).val.map (homOfLE h).op s) =
      eval M V ⟨p.1, h p.2⟩ s := (rfl)

/-- The numerator map to sections, viewed as an `R`-linear map by restriction
of scalars along the structure-sheaf algebra map. -/
@[no_expose]
def toOpen {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (U : (Spec R).Opens) :
    M →ₗ[R] (ModuleCat.restrictScalars
      (((Spec R).presheaf.map U.leTop.op).hom.comp
        (Scheme.ΓSpecIso R).inv.hom)).obj ((moduleTilde M).val.obj (op U)) where
  toFun := numeratorLinear R M U
  map_add' m n := (numeratorLinear R M U).map_add m n
  map_smul' r m := by
    change numeratorLinear R M U (r • m) =
      (algebraMap R ((structureSheafInType R R).obj.obj (op U)) r) •
        numeratorLinear R M U m
    rw [IsScalarTower.algebraMap_smul]
    exact (numeratorLinear R M U).map_smul r m

/-- A numerator evaluates to the fraction with denominator one. -/
@[simp]
theorem eval_toOpen {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (U : (Spec R).Opens) (p : U) (m : M) :
    eval M U p (toOpen M U m) = LocalizedModule.mk m 1 := (rfl)

local notation "ΓSpecObj(" R ", " U ")" =>
  CategoryTheory.Functor.obj
    (AlgebraicGeometry.PresheafedSpace.presheaf
      (AlgebraicGeometry.SheafedSpace.toPresheafedSpace
        (AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
          (AlgebraicGeometry.Scheme.toLocallyRingedSpace (AlgebraicGeometry.Spec R)))))
    (Opposite.op U)

local notation "ΓAlg(" R ", " U ")" =>
  AlgebraicGeometry.StructureSheaf.openAlgebra R (Opposite.op U)

local notation "ΓAway(" R ", " f ")" =>
  (@IsLocalization.algEquiv (CommRingCat.carrier R) _
    (Submonoid.powers f) (Localization.Away f) _ _ _
    (CommRingCat.carrier ΓSpecObj(R, (PrimeSpectrum.basicOpen f :
      AlgebraicGeometry.Scheme.Opens (AlgebraicGeometry.Spec R)))) _
    ΓAlg(R, (PrimeSpectrum.basicOpen f :
      AlgebraicGeometry.Scheme.Opens (AlgebraicGeometry.Spec R)))
    (AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen R f))

local notation "ΓAwayRing(" R ", " f ")" =>
  (@AlgEquiv.toRingEquiv (CommRingCat.carrier R) (Localization.Away f)
    (CommRingCat.carrier ΓSpecObj(R, (PrimeSpectrum.basicOpen f :
      AlgebraicGeometry.Scheme.Opens (AlgebraicGeometry.Spec R))))
    _ _ _ _
    ΓAlg(R, (PrimeSpectrum.basicOpen f :
      AlgebraicGeometry.Scheme.Opens (AlgebraicGeometry.Spec R)))
    ΓAway(R, f))

local notation "η(" R ", " U ")" =>
  CommRingCat.Hom.hom
    (CategoryTheory.CategoryStruct.comp
      (CategoryTheory.Iso.inv (Scheme.ΓSpecIso R))
      (CategoryTheory.Functor.map
        (PresheafedSpace.presheaf
          (SheafedSpace.toPresheafedSpace
            (LocallyRingedSpace.toSheafedSpace
              (Scheme.toLocallyRingedSpace (Spec R)))))
        (Quiver.Hom.op (homOfLE (le_top : U ≤ ⊤)))))

/-- The numerator map respects scalar multiplication through the structure-sheaf
algebra map. -/
theorem toOpen_smul {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (U : (Spec R).Opens) (r : R) (m : M) :
    toOpen M U (r • m) =
      AddCommGrpCat.Hom.hom
        (ModuleCat.smul ((moduleTilde M).val.obj (op U)) (η(R, U) r))
        (toOpen M U m) := by
  exact ((toOpen M U).map_smul r m).trans
    ((ModuleCat.restrictScalars.smul_def
      (M := (moduleTilde M).val.obj (op U))
      (algebraMap (CommRingCat.carrier R) (CommRingCat.carrier ΓSpecObj(R, U)))
      r (toOpen M U m)).trans
        (congrArg (fun η : (CommRingCat.carrier R) →+*
            (CommRingCat.carrier ΓSpecObj(R, U)) ↦
          AddCommGrpCat.Hom.hom
            (ModuleCat.smul ((moduleTilde M).val.obj (op U)) (η r))
            (toOpen M U m))
          (AlgebraicGeometry.IsAffineOpen.algebraMap_Spec_obj (R := R) (U := U))))

/-- Restricting a numerator gives the numerator of the same module element. -/
@[simp]
theorem toOpen_res {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    {U V : (Spec R).Opens} (h : U ≤ V) (m : M) :
    (moduleTilde M).val.map (homOfLE h).op (toOpen M V m) =
      toOpen M U m := (rfl)


local notation "S(" M ", " U ")" =>
  PresheafOfModules.obj (SheafOfModules.val (moduleTilde M)) (Opposite.op U)
local notation "Q(" R ", " M ", " U ")" =>
  (CategoryTheory.Functor.obj (ModuleCat.restrictScalars η(R, U)) S(M, U) : ModuleCat R)
local notation "res(" M ", " h ")" =>
  PresheafOfModules.restrictₛₗ (SheafOfModules.val (moduleTilde M))
    (Quiver.Hom.op (homOfLE h))

/-- The section with numerator `m` and denominator `r` on an open where `r` is invertible. -/
@[no_expose]
def fraction {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (U : (Spec R).Opens) (m : M) (r : R) (hr : U ≤ basicOpen r) :
    (moduleTilde M).val.obj (op U) :=
  ⟨fun p ↦ LocalizedModule.mk m ⟨r, hr p.2⟩,
    fun p ↦ ⟨U, p.2, 𝟙 _, m, r, fun q ↦ ⟨hr q.2, rfl⟩⟩⟩

/-- Evaluation of a fraction is the same fraction in the localization at the prime. -/
@[simp]
theorem eval_fraction {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (U : (Spec R).Opens) (m : M) (r : R)
    (hr : U ≤ basicOpen r) (p : U) :
    eval M U p (fraction M U m r hr) = LocalizedModule.mk m ⟨r, hr p.2⟩ := (rfl)

/-- A fraction with denominator one is the numerator section. -/
@[simp]
theorem fraction_one {R : CommRingCat.{u}} (M : ModuleCat.{v} R) (U : (Spec R).Opens) (m : M) :
    fraction M U m 1 (by
      rw [PrimeSpectrum.basicOpen_one]
      exact le_top) = toOpen M U m := (rfl)

/-- Restriction preserves a fraction's numerator and denominator. -/
@[simp]
theorem fraction_res {R : CommRingCat.{u}} (M : ModuleCat.{v} R) {U V : (Spec R).Opens} (h : U ≤ V)
    (m : M) (r : R) (hr : V ≤ basicOpen r) :
    (moduleTilde M).val.map (homOfLE h).op (fraction M V m r hr) =
      fraction M U m r (h.trans hr) := (rfl)

/-- Multiplication by the denominator through the original section ring clears a fraction. -/
theorem smul_fraction {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (U : (Spec R).Opens) (m : M) (r : R)
    (hr : U ≤ basicOpen r) :
    algebraMap R Γ(Spec R, U) r • fraction M U m r hr = toOpen M U m := by
  apply ext M
  intro p
  rw [eval_smul, eval_fraction, eval_toOpen]
  change Localization.mk r
    (1 : p.1.asIdeal.primeCompl (hp := p.1.isPrime)) •
    LocalizedModule.mk m ⟨r, hr p.2⟩ = LocalizedModule.mk m 1
  rw [LocalizedModule.mk_smul_mk, one_mul]
  simpa only [Submonoid.smul_def] using
    (LocalizedModule.mk_cancel
      (⟨r, hr p.2⟩ : p.1.asIdeal.primeCompl (hp := p.1.isPrime)) m)

private lemma restrict_algebraMap {R : CommRingCat.{u}} {U V : (Spec R).Opens} (h : U ≤ V) (r : R) :
    ((Spec R).presheaf.map (homOfLE h).op).hom (algebraMap R Γ(Spec R, V) r) =
      algebraMap R Γ(Spec R, U) r := by
  rw [IsAffineOpen.algebraMap_Spec_obj, IsAffineOpen.algebraMap_Spec_obj]
  change (((Scheme.ΓSpecIso R).inv ≫
    (Spec R).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op ≫
    (Spec R).presheaf.map (homOfLE h).op).hom r) = _
  rw [← Functor.map_comp]
  rfl

private def restrictLinear {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    {U V : (Spec R).Opens} (h : U ≤ V) :
    Q(R, M, V) →ₗ[R] Q(R, M, U) where
  toFun := res(M, h)
  map_add' := (res(M, h)).map_add
  map_smul' r s := by
    have hV := ModuleCat.restrictScalars.smul_def
      (M := S(M, V)) η(R, V) r s
    have hU := ModuleCat.restrictScalars.smul_def
      (M := S(M, U)) η(R, U) r (res(M, h) s)
    have hρ : ((Spec R).presheaf.map (homOfLE h).op).hom (η(R, V) r) =
        η(R, U) r := by
      simpa only [IsAffineOpen.algebraMap_Spec_obj] using restrict_algebraMap h r
    exact (congrArg (res(M, h)) hV).trans
      (((res(M, h)).map_smulₛₗ (η(R, V) r) s).trans
        ((congrArg (fun a : Γ(Spec R, U) ↦
          AddCommGrpCat.Hom.hom ((S(M, U)).smul a) (res(M, h) s)) hρ).trans hU.symm))

private lemma scalarEnd_isUnit {R : CommRingCat.{u}} {A : Type*} [CommRing A] (η : R →+* A)
    (L : ModuleCat A) (r : R) (hr : IsUnit (η r)) :
    IsUnit (algebraMap R
      (Module.End R ((ModuleCat.restrictScalars η).obj L)) r) := by
  have h := hr.map (algebraMap A (Module.End A L))
  rw [Module.End.isUnit_iff] at h ⊢
  change Function.Bijective (fun x : L ↦ η r • x) at h
  change Function.Bijective (fun x : L ↦ η r • x)
  exact h

private theorem isUnit_eta_of_le_basicOpen {R : CommRingCat.{u}}
    (f : R) (U : (Spec R).Opens) (hf : U ≤ basicOpen f) :
    IsUnit (η(R, U) f) := by
  rw [← IsAffineOpen.algebraMap_Spec_obj (R := R) (U := U)]
  rw [← restrict_algebraMap hf f]
  have hunit := @IsLocalization.Away.algebraMap_isUnit (CommRingCat.carrier R) _
    (CommRingCat.carrier ΓSpecObj(R, (PrimeSpectrum.basicOpen f : (Spec R).Opens))) _
    ΓAlg(R, (PrimeSpectrum.basicOpen f : (Spec R).Opens)) f
    (StructureSheaf.IsLocalization.to_basicOpen R f)
  exact hunit.map ((Spec R).presheaf.map (homOfLE hf).op).hom

private lemma scalarEnd_isUnit_of_le_basicOpen {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    {U : (Spec R).Opens}
    (f : R) (hf : U ≤ basicOpen f) :
    IsUnit (algebraMap R (Module.End R Q(R, M, U)) f) := by
  exact scalarEnd_isUnit η(R, U) S(M, U) f
    (isUnit_eta_of_le_basicOpen f U hf)

private lemma powers_scalarEnd_isUnit {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    {U : (Spec R).Opens}
    (f : R) (hf : U ≤ basicOpen f) :
    ∀ s : Submonoid.powers f,
      IsUnit (algebraMap R (Module.End R Q(R, M, U)) s) := by
  rintro ⟨_, n, rfl⟩
  simpa only [map_pow] using (scalarEnd_isUnit_of_le_basicOpen M f hf).pow n

private lemma smul_fraction_restrictScalars {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (U : (Spec R).Opens) (m : M) (r : R) (hr : U ≤ basicOpen r) :
    r • (show Q(R, M, U) from fraction M U m r hr) = toOpen M U m := by
  exact (ModuleCat.restrictScalars.smul_def
    (M := S(M, U))
    (((Scheme.ΓSpecIso R).inv ≫
      (Spec R).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom)
    r (fraction M U m r hr)).trans
      ((congrArg (fun η : R →+* Γ(Spec R, U) ↦
        AddCommGrpCat.Hom.hom ((S(M, U)).smul (η r)) (fraction M U m r hr))
          (IsAffineOpen.algebraMap_Spec_obj (R := R) (U := U))).symm.trans
            (smul_fraction M U m r hr))

/-- A section is a fraction on a basic-open neighborhood of each point. -/
theorem exists_fraction {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (U : (Spec R).Opens) (s : S(M, U)) (p : U) :
    ∃ (g : R) (_hp : p.1 ∈ basicOpen g) (hg : basicOpen g ≤ U) (m : M),
      res(M, hg) s = fraction M (basicOpen g) m g le_rfl := by
  obtain ⟨V, hpV, hVU, m, r, H⟩ := local_fraction_at M U s p
  obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hpg, hgV⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hpV V.2
  have hmul : (basicOpen (g * r) : (Spec R).Opens) =
      (basicOpen g : (Spec R).Opens) ⊓ basicOpen r :=
    PrimeSpectrum.basicOpen_mul g r
  refine ⟨g * r, ?_, ?_, g • m, ?_⟩
  · exact hmul.ge ⟨hpg, (H ⟨p.1, hpV⟩).choose⟩
  · exact hmul.le.trans (inf_le_left.trans (hgV.trans hVU))
  · symm
    apply ext M
    rintro ⟨q, hq⟩
    erw [eval_fraction, eval_res]
    have hqgr : q ∈ ((basicOpen g : (Spec R).Opens) ⊓ basicOpen r) := hmul.le hq
    obtain ⟨hrq, hval⟩ := H ⟨q, hgV hqgr.1⟩
    refine (LocalizedModule.mk_eq.mpr ⟨1, ?_⟩).trans hval.symm
    simp [Submonoid.smul_def, ← smul_assoc]; ring_nf

private lemma le_basicOpen_of_mem_powers {R : CommRingCat.{u}} (f : R) (s : Submonoid.powers f) :
    basicOpen f ≤ basicOpen (s : R) := by
  obtain ⟨_, n, rfl⟩ := s
  exact PrimeSpectrum.le_basicOpen_pow f n

private def toBasicOpenLinear {R : CommRingCat.{u}} (M : ModuleCat.{v} R) (f : R) :
    LocalizedModule (.powers f) M →ₗ[R] Q(R, M, basicOpen f) :=
  IsLocalizedModule.lift (.powers f) (LocalizedModule.mkLinearMap (.powers f) M)
    (toOpen M (basicOpen f)) (powers_scalarEnd_isUnit M f le_rfl)

private lemma toBasicOpenLinear_mk_one {R : CommRingCat.{u}} (M : ModuleCat.{v} R) (f : R) (m : M) :
    toBasicOpenLinear M f (LocalizedModule.mk m 1) = toOpen M (basicOpen f) m := by
  exact IsLocalizedModule.lift_apply (.powers f)
    (LocalizedModule.mkLinearMap (.powers f) M) (toOpen M (basicOpen f))
    (powers_scalarEnd_isUnit M f le_rfl) m

private lemma toBasicOpenLinear_mk {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (f : R) (m : M) (s : Submonoid.powers f) :
    toBasicOpenLinear M f (LocalizedModule.mk m s) =
      fraction M (basicOpen f) m s (le_basicOpen_of_mem_powers f s) := by
  apply ((Module.End.isUnit_iff
    (algebraMap R (Module.End R Q(R, M, basicOpen f)) (s : R))).mp
      (powers_scalarEnd_isUnit M f le_rfl s)).1
  change (s : R) • toBasicOpenLinear M f (LocalizedModule.mk m s) =
    (s : R) • (show Q(R, M, basicOpen f) from fraction M (basicOpen f) m s
      (le_basicOpen_of_mem_powers f s))
  have hraw : (s : R) • LocalizedModule.mk m s = LocalizedModule.mk m 1 := by
    rw [LocalizedModule.smul'_mk]
    simpa only [Submonoid.smul_def] using LocalizedModule.mk_cancel s m
  rw [← map_smul, hraw, toBasicOpenLinear_mk_one]
  exact (smul_fraction_restrictScalars M (basicOpen f) m s
    (le_basicOpen_of_mem_powers f s)).symm

private lemma toBasicOpenLinear_injective {R : CommRingCat.{u}} (M : ModuleCat.{v} R) (f : R) :
    Function.Injective (toBasicOpenLinear M f) := by
  intro s t h_eq
  induction s using LocalizedModule.induction_on with | h a b =>
  induction t using LocalizedModule.induction_on with | h c d =>
  suffices f ∈ ((⊥ : Submodule R M).colon {d • a - b • c}).radical by
    rw [LocalizedModule.mk_eq]
    obtain ⟨n, hn⟩ := this
    exact ⟨⟨f ^ n, n, rfl⟩, by
      simpa [Submonoid.smul_def, sub_eq_zero, smul_sub] using
        Submodule.mem_colon.mp hn _ rfl⟩
  erw [toBasicOpenLinear_mk, toBasicOpenLinear_mk] at h_eq
  rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical,
    PrimeSpectrum.mem_vanishingIdeal]
  intro p hfp
  contrapose hfp
  have he := congrArg (eval M (basicOpen f) ⟨p, hfp⟩) h_eq
  erw [eval_fraction, eval_fraction] at he
  obtain ⟨z, hz⟩ := LocalizedModule.mk_eq.mp he
  rw [PrimeSpectrum.mem_zeroLocus, Set.not_subset]
  exact ⟨z.1, by
    simpa [Submonoid.smul_def, sub_eq_zero, smul_sub] using hz, z.2⟩

private lemma normalized_fraction_cover {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (U : (Spec R).Opens)
    (hU : IsCompact (U : Set (Spec R))) (s : S(M, U)) :
    ∃ (ι : Type u) (_ : Fintype ι) (a : ι → M) (b : ι → R)
      (ibU : ∀ i, basicOpen (b i) ≤ U),
      (U ≤ ⨆ i, basicOpen (b i)) ∧ (∀ i j, b j • a i = b i • a j) ∧
        ∀ i, res(M, ibU i) s = fraction M (basicOpen (b i)) (a i) (b i) le_rfl := by
  choose g hxg igU a H using fun x : U ↦ exists_fraction M U s x
  have hcompat (i j : U) :
      LocalizedModule.mk (g i • a j) ⟨g i * g j, Submonoid.mem_powers _⟩ =
      LocalizedModule.mk (g j • a i) ⟨g i * g j, Submonoid.mem_powers _⟩ := by
    apply toBasicOpenLinear_injective M (g i * g j)
    erw [toBasicOpenLinear_mk, toBasicOpenLinear_mk]
    apply ext M
    intro q
    have hmul : (basicOpen (g i * g j) : (Spec R).Opens) =
        (basicOpen (g i) : (Spec R).Opens) ⊓ basicOpen (g j) :=
      PrimeSpectrum.basicOpen_mul (g i) (g j)
    have hqij : q.1 ∈ ((basicOpen (g i) : (Spec R).Opens) ⊓ basicOpen (g j)) :=
      hmul.le q.2
    have hi := congrArg (eval M (basicOpen (g i)) ⟨q.1, hqij.1⟩) (H i)
    have hj := congrArg (eval M (basicOpen (g j)) ⟨q.1, hqij.2⟩) (H j)
    erw [eval_res, eval_fraction] at hi hj
    erw [eval_fraction, eval_fraction]
    refine Eq.trans ?_ ((hj.symm.trans hi).trans ?_)
    · exact LocalizedModule.mk_eq.mpr ⟨1, by
        simp [Submonoid.smul_def, ← smul_assoc]; ring_nf⟩
    · exact (LocalizedModule.mk_eq.mpr ⟨1, by
        simp [Submonoid.smul_def, ← smul_assoc]⟩).symm
  simp only [LocalizedModule.mk_eq, Submonoid.smul_def, Subtype.exists,
    Submonoid.mem_powers_iff, exists_prop, exists_exists_eq_and, ← mul_smul,
    ← pow_succ, ← mul_assoc _ (_ * _)] at hcompat
  choose n hn using hcompat
  let B : U → (Spec R).Opens := fun i ↦ basicOpen (g i)
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun i ↦ (B i).1)
    (fun i ↦ (B i).isOpen)
    (fun x hx ↦ Set.mem_iUnion_of_mem ⟨x, hx⟩ (hxg _))
  have ht' : U ≤ ⨆ i : t, B i.1 := by
    intro x hx
    obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact (le_iSup (fun i : t ↦ B i.1) ⟨i, hit⟩) hxi
  let N := (t ×ˢ t).sup fun x ↦ n x.1 x.2 + 1
  have hpow (i : U) : (basicOpen (g i ^ (N + 1)) : (Spec R).Opens) = B i :=
    PrimeSpectrum.basicOpen_pow (g i) (N + 1) (Nat.succ_pos N)
  have hcover : U ≤ ⨆ i : t, (basicOpen (g i.1 ^ (N + 1)) : (Spec R).Opens) :=
    ht'.trans (iSup_le fun i ↦ le_iSup_of_le i (hpow i.1).ge)
  refine ⟨t, inferInstance, fun i ↦ g i ^ N • a i,
    fun i ↦ g i ^ (N + 1), fun i ↦ (hpow i.1).le.trans (igU i.1),
    hcover, fun i j ↦ ?_, fun i ↦ ?_⟩
  · dsimp
    convert_to (g i * g ↑j) ^ N • g j • a i =
      (g i * g ↑j) ^ N • g i • a j
    · module
    · module
    have hnN : n i j + 1 ≤ N :=
      (t ×ˢ t).le_sup (f := fun x ↦ n x.1 x.2 + 1) (b := ⟨_, _⟩) (by simp)
    rw [← Nat.sub_add_cancel hnN, pow_add, mul_smul, mul_smul]
    congr 1
    have h := (hn i j).symm
    module_nf at h ⊢
    exact h
  · apply ext M
    intro p
    have hp : p.1 ∈ B i.1 := (hpow i.1).le p.2
    have h := congrArg (eval M (B i.1) ⟨p.1, hp⟩) (H i)
    erw [eval_res, eval_fraction] at h
    erw [eval_res, eval_fraction]
    refine h.trans (LocalizedModule.mk_eq.mpr ⟨1, ?_⟩)
    simp [Submonoid.smul_def, pow_succ', mul_smul]

private lemma toBasicOpenLinear_surjective {R : CommRingCat.{u}} (M : ModuleCat.{v} R) (f : R) :
    Function.Surjective (toBasicOpenLinear M f) := by
  intro s
  obtain ⟨ι, hι, a, b, ibU, iU, hab, H⟩ := normalized_fraction_cover M
    (basicOpen f) (IsAffineOpen.Spec_basicOpen (R := R) f).isCompact s
  let : Fintype ι := hι
  let B : ι → (Spec R).Opens := fun i ↦ basicOpen (b i)
  obtain ⟨n, hn⟩ : f ∈ (Ideal.span (Set.range b)).radical := by
    have iU' : (basicOpen f : Opens (PrimeSpectrum R)) ≤ ⨆ i, basicOpen (b i) := iU
    have h : PrimeSpectrum.zeroLocus (Set.range b) ⊆ PrimeSpectrum.zeroLocus {f} := by
      simpa [← SetLike.coe_subset_coe, ← Set.compl_iInter,
        ← PrimeSpectrum.zeroLocus_iUnion, PrimeSpectrum.Top] using iU'
    rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical,
      PrimeSpectrum.zeroLocus_span, PrimeSpectrum.mem_vanishingIdeal]
    exact fun x hx ↦ by simpa using h hx
  replace hn := Ideal.mul_mem_right f _ hn
  rw [← pow_succ, Ideal.span, Finsupp.mem_span_range_iff_exists_finsupp] at hn
  obtain ⟨c, hc⟩ := hn
  rw [Finsupp.sum_fintype _ _ (by simp)] at hc
  refine ⟨LocalizedModule.mk (∑ i, c i • a i) ⟨f ^ (n + 1), _, rfl⟩, ?_⟩
  apply ext M
  intro p
  have hp : p.1 ∈ ⨆ i, B i := iU p.2
  obtain ⟨i, hi⟩ : ∃ i, p.1 ∈ B i := by simpa using hp
  have hs := congrArg (eval M (B i) ⟨p.1, hi⟩) (H i).symm
  erw [eval_res, eval_fraction] at hs
  erw [toBasicOpenLinear_mk, eval_fraction]
  refine (LocalizedModule.mk_eq.mpr ⟨1, ?_⟩).trans hs
  simp_rw [one_smul, Finset.smul_sum, Submonoid.smul_def, smul_comm (b i),
    hab _ i, ← smul_assoc, ← Finset.sum_smul, hc]

/-- Numerators identify the sections on a basic open with the module localization. -/
instance isLocalizedModule_toOpen {R : CommRingCat.{u}} (M : ModuleCat.{v} R) (f : R) :
    IsLocalizedModule (.powers f) (toOpen M (basicOpen f)) := by
  let e : LocalizedModule (.powers f) M ≃ₗ[R] Q(R, M, basicOpen f) :=
    LinearEquiv.ofBijective (toBasicOpenLinear M f)
      ⟨toBasicOpenLinear_injective M f, toBasicOpenLinear_surjective M f⟩
  have he : e.toLinearMap.comp (LocalizedModule.mkLinearMap (.powers f) M) =
      toOpen M (basicOpen f) := by
    ext m
    exact toBasicOpenLinear_mk_one M f m
  rw [← he]
  exact IsLocalizedModule.of_linearEquiv (.powers f)
    (LocalizedModule.mkLinearMap (.powers f) M) e

private lemma iso_fraction {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (f : R) (m : M) (s : Submonoid.powers f) :
    IsLocalizedModule.iso (.powers f) (toOpen M (basicOpen f))
      (LocalizedModule.mk m s) =
      fraction M (basicOpen f) m s (le_basicOpen_of_mem_powers f s) := by
  let E := IsLocalizedModule.iso (.powers f) (toOpen M (basicOpen f))
  have h := IsLocalizedModule.iso_symm_apply' (.powers f)
    (toOpen M (basicOpen f))
    (fraction M (basicOpen f) m s (le_basicOpen_of_mem_powers f s)) m s
    (by
      change (s : R) • (show Q(R, M, basicOpen f) from
        fraction M (basicOpen f) m s (le_basicOpen_of_mem_powers f s)) =
          toOpen M (basicOpen f) m
      exact smul_fraction_restrictScalars M (basicOpen f) m s _)
  exact (congrArg E h.symm).trans (E.apply_symm_apply _)

private lemma iso_symm_apply_iff {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (f : R) (t : S(M, (basicOpen f : (Spec R).Opens)))
    (m : M) (s : Submonoid.powers f) :
    (IsLocalizedModule.iso (.powers f) (toOpen M (basicOpen f : (Spec R).Opens))).symm t =
        LocalizedModule.mk m s ↔
      AddCommGrpCat.Hom.hom
        ((S(M, (basicOpen f : (Spec R).Opens))).smul
          (η(R, (basicOpen f : (Spec R).Opens)) (s : R))) t =
            toOpen M (basicOpen f : (Spec R).Opens) m := by
  let e := IsLocalizedModule.iso (.powers f)
    (toOpen M (basicOpen f : (Spec R).Opens))
  have he_mk : e (LocalizedModule.mk m s) =
      IsLocalizedModule.mk' (toOpen M (basicOpen f : (Spec R).Opens)) m s := by
    change IsLocalizedModule.iso (.powers f)
      (toOpen M (basicOpen f : (Spec R).Opens)) (LocalizedModule.mk m s) =
      IsLocalizedModule.fromLocalizedModule (.powers f)
        (toOpen M (basicOpen f : (Spec R).Opens)) (LocalizedModule.mk m s)
    exact (IsLocalizedModule.iso_apply_mk (.powers f)
      (toOpen M (basicOpen f : (Spec R).Opens)) m s).trans
      (IsLocalizedModule.fromLocalizedModule_mk (.powers f)
        (toOpen M (basicOpen f : (Spec R).Opens)) m s).symm
  have hmk : e (LocalizedModule.mk m s) = t ↔
      toOpen M (basicOpen f : (Spec R).Opens) m =
        AddCommGrpCat.Hom.hom
          ((S(M, (basicOpen f : (Spec R).Opens))).smul
            (η(R, (basicOpen f : (Spec R).Opens)) (s : R))) t := by
    rw [he_mk]
    let : Algebra R Γ(Spec R, (basicOpen f : (Spec R).Opens)) :=
      StructureSheaf.openAlgebra R (op (basicOpen f : (Spec R).Opens))
    let N := (ModuleCat.restrictScalars
      (algebraMap R Γ(Spec R, (basicOpen f : (Spec R).Opens)))).obj
      ((moduleTilde M).val.obj (op (basicOpen f : (Spec R).Opens)))
    let : @Module R N
        (inferInstance : CommSemiring R).toSemiring
        N.isAddCommGroup.toAddCommMonoid := N.isModule
    have h :
        IsLocalizedModule.mk' (toOpen M (basicOpen f : (Spec R).Opens)) m s = t ↔
          toOpen M (basicOpen f : (Spec R).Opens) m =
            (s : R) • (show N from t) := by
      exact @IsLocalizedModule.mk'_eq_iff
        (CommRingCat.carrier R)
        (inferInstance : CommSemiring (CommRingCat.carrier R))
        (Submonoid.powers f)
        (ModuleCat.carrier M)
        (ModuleCat.carrier N)
        M.isAddCommGroup.toAddCommMonoid
        N.isAddCommGroup.toAddCommMonoid
        M.isModule
        N.isModule
        (toOpen M (basicOpen f : (Spec R).Opens))
        (isLocalizedModule_toOpen M f)
        m
        s
        (show N from t)
    have hs :=
      (ModuleCat.restrictScalars.smul_def
        (M := S(M, (basicOpen f : (Spec R).Opens)))
        (algebraMap (CommRingCat.carrier R)
          (CommRingCat.carrier ΓSpecObj(R, (basicOpen f : (Spec R).Opens))))
        (s : R) (show N from t)).trans
        (congrArg
          (fun η : (CommRingCat.carrier R) →+*
              (CommRingCat.carrier ΓSpecObj(R, (basicOpen f : (Spec R).Opens))) ↦
            AddCommGrpCat.Hom.hom
              (ModuleCat.smul (S(M, (basicOpen f : (Spec R).Opens)))
                (η (s : R))) t)
          (AlgebraicGeometry.IsAffineOpen.algebraMap_Spec_obj
            (R := R) (U := (basicOpen f : (Spec R).Opens))))
    exact h.trans ⟨fun ht => ht.trans hs, fun ht => ht.trans hs.symm⟩
  calc
    e.symm t = LocalizedModule.mk m s ↔ t = e (LocalizedModule.mk m s) :=
      LinearEquiv.symm_apply_eq e
    _ ↔ e (LocalizedModule.mk m s) = t := eq_comm
    _ ↔ AddCommGrpCat.Hom.hom
          ((S(M, (basicOpen f : (Spec R).Opens))).smul
            (η(R, (basicOpen f : (Spec R).Opens)) (s : R))) t =
          toOpen M (basicOpen f : (Spec R).Opens) m := hmk.trans eq_comm

private lemma algebraMap_top_eq_sigma {R : CommRingCat.{u}} :
    algebraMap R Γ(Spec R, (⊤ : (Spec R).Opens)) = (Scheme.ΓSpecIso R).inv.hom := by
  rw [IsAffineOpen.algebraMap_Spec_obj]
  simp

private lemma sigma_tau {R : CommRingCat.{u}} (a : Γ(Spec R, (⊤ : (Spec R).Opens))) :
    (Scheme.ΓSpecIso R).inv.hom ((Scheme.ΓSpecIso R).hom.hom a) = a := by
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso R).hom_inv_id a

private lemma tau_sigma {R : CommRingCat.{u}} (r : R) :
    (Scheme.ΓSpecIso R).hom.hom ((Scheme.ΓSpecIso R).inv.hom r) = r := by
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso R).inv_hom_id r

private lemma toOpen_top_bijective {R : CommRingCat.{u}} (M : ModuleCat.{v} R) :
    Function.Bijective (toOpen M ⊤) := by
  have h : IsLocalizedModule ⊥ (toOpen M ⊤) := by
    convert! (isLocalizedModule_toOpen M (1 : R))
    rw [PrimeSpectrum.basicOpen_one, Submonoid.powers_one]
    rfl
  let : IsLocalizedModule ⊥ (toOpen M ⊤) := h
  refine ⟨fun x y e ↦ by
    simpa using (IsLocalizedModule.eq_iff_exists ⊥ (toOpen M ⊤)).mp e, fun s ↦ ?_⟩
  obtain ⟨⟨m, _, rfl⟩, rfl⟩ := IsLocalizedModule.mk'_surjective ⊥ (toOpen M ⊤) s
  exact ⟨m, (IsLocalizedModule.mk'_one ..).symm⟩

private def toTopLinearMap {R : CommRingCat.{u}} (M : ModuleCat.{v} R) :
    M →ₗ[R] (ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).obj S(M, ⊤) where
  toFun := toOpen M ⊤
  map_add' := (toOpen M ⊤).map_add
  map_smul' r m := by
    have hη := ModuleCat.restrictScalars.smul_def
      (M := S(M, ⊤)) (algebraMap R Γ(Spec R, (⊤ : (Spec R).Opens)))
      r (toOpen M ⊤ m)
    have hσ := ModuleCat.restrictScalars.smul_def
      (M := S(M, ⊤)) (Scheme.ΓSpecIso R).inv.hom r (toOpen M ⊤ m)
    have hησ : AddCommGrpCat.Hom.hom ((S(M, ⊤)).smul
        (algebraMap R Γ(Spec R, (⊤ : (Spec R).Opens)) r)) (toOpen M ⊤ m) =
        AddCommGrpCat.Hom.hom ((S(M, ⊤)).smul
          ((Scheme.ΓSpecIso R).inv.hom r)) (toOpen M ⊤ m) :=
      congrArg (fun η : R →+* Γ(Spec R, (⊤ : (Spec R).Opens)) ↦
        AddCommGrpCat.Hom.hom ((S(M, ⊤)).smul (η r)) (toOpen M ⊤ m))
          algebraMap_top_eq_sigma
    exact ((toOpen M ⊤).map_smul r m).trans (hη.trans (hησ.trans hσ.symm))

/-- The original module is linearly equivalent to the top sections. -/
@[no_expose]
def topLinearEquiv {R : CommRingCat.{u}} (M : ModuleCat.{v} R) :
    M ≃ₗ[R] (ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).obj S(M, ⊤) :=
  LinearEquiv.ofBijective (toTopLinearMap M) (toOpen_top_bijective M)

/-- The top equivalence is the numerator map on the original module. -/
theorem topLinearEquiv_apply {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (m : M) : topLinearEquiv M m = toOpen M ⊤ m := (rfl)

/-- The inverse recovers every original numerator. -/
theorem topLinearEquiv_symm_toOpen {R : CommRingCat.{u}} (M : ModuleCat.{v} R) (m : M) :
    (topLinearEquiv M).symm (toOpen M ⊤ m) = m :=
  (topLinearEquiv M).symm_apply_apply m

/-- Every top section is recovered from its inverse numerator. -/
theorem toOpen_topLinearEquiv_symm {R : CommRingCat.{u}} (M : ModuleCat.{v} R) (s : S(M, ⊤)) :
    toOpen M ⊤ ((topLinearEquiv M).symm s) = s :=
  (topLinearEquiv M).apply_symm_apply s

/-- The forward map is semilinear for the original Spec scalar isomorphism. -/
theorem topLinearEquiv_smul {R : CommRingCat.{u}} (M : ModuleCat.{v} R) (r : R) (m : M) :
    topLinearEquiv M (r • m) =
      AddCommGrpCat.Hom.hom ((S(M, ⊤)).smul ((Scheme.ΓSpecIso R).inv.hom r))
        (topLinearEquiv M m) := by
  exact ((topLinearEquiv M).map_smul r m).trans
    (ModuleCat.restrictScalars.smul_def
      (M := S(M, ⊤)) (Scheme.ΓSpecIso R).inv.hom r (topLinearEquiv M m))

/-- The inverse is semilinear for the inverse Spec scalar isomorphism. -/
theorem topLinearEquiv_symm_smul {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (a : Γ(Spec R, (⊤ : (Spec R).Opens)))
    (s : S(M, ⊤)) :
    (topLinearEquiv M).symm (AddCommGrpCat.Hom.hom ((S(M, ⊤)).smul a) s) =
      (Scheme.ΓSpecIso R).hom.hom a • (topLinearEquiv M).symm s := by
  apply (topLinearEquiv M).injective
  have h := topLinearEquiv_smul M ((Scheme.ΓSpecIso R).hom.hom a)
    ((topLinearEquiv M).symm s)
  have h' : topLinearEquiv M
      ((Scheme.ΓSpecIso R).hom.hom a • (topLinearEquiv M).symm s) =
      AddCommGrpCat.Hom.hom ((S(M, ⊤)).smul a) s :=
    h.trans (congrArg₂
      (fun (b : Γ(Spec R, (⊤ : (Spec R).Opens))) (t : S(M, ⊤)) ↦
        AddCommGrpCat.Hom.hom ((S(M, ⊤)).smul b) t)
      (sigma_tau a) ((topLinearEquiv M).apply_symm_apply s))
  exact ((topLinearEquiv M).apply_symm_apply _).trans h'.symm

universe x r z i

private def homMkOfBasis
    {X : TopCat.{x}} {O : TopCat.Sheaf RingCat.{r} X}
    (F : PresheafOfModules.{max x z} O.obj)
    (G : SheafOfModules.{max x z} O)
    {ι : Type i} (B : ι → Opens X) (hB : Opens.IsBasis (Set.range B))
    (α : (inducedFunctor B).op ⋙ F.presheaf ⟶
      (inducedFunctor B).op ⋙ G.val.presheaf)
    (hα : ∀ (j : ι) (a : O.obj.obj (.op (B j))) (s : F.obj (.op (B j))),
      α.app (.op j) (AddCommGrpCat.Hom.hom ((F.obj (.op (B j))).smul a) s) =
        AddCommGrpCat.Hom.hom ((G.val.obj (.op (B j))).smul a) (α.app (.op j) s)) :
    F ⟶ G.val := by
  let : UnivLE.{x, max x z} := univLE_max
  let : Limits.HasLimitsOfSize.{x, x} AddCommGrpCat.{max x z} :=
    AddCommGrpCat.hasLimitsOfSize
  let : Limits.PreservesLimitsOfSize.{x, x} (forget AddCommGrpCat.{max x z}) :=
    AddCommGrpCat.forget_preservesLimitsOfSize
  let : (forget AddCommGrpCat.{max x z}).ReflectsIsomorphisms :=
    AddCommGrpCat.forget_reflects_isos
  let GAb : TopCat.Sheaf AddCommGrpCat.{max x z} X := ⟨G.val.presheaf, G.isSheaf⟩
  let φ : F.presheaf ⟶ G.val.presheaf :=
    TopCat.Sheaf.restrictHomEquivHom F.presheaf GAb hB α
  refine PresheafOfModules.homMk φ ?_
  intro U a s
  change φ.app U (AddCommGrpCat.Hom.hom ((F.obj U).smul a) s) =
    AddCommGrpCat.Hom.hom ((G.val.obj U).smul a) (φ.app U s)
  let J := {j : ι // B j ≤ U.unop}
  have hcover : U.unop ≤ ⨆ j : J, B j.1 := by
    intro p hp
    obtain ⟨V, ⟨j, rfl⟩, hpj, hjU⟩ := (Opens.isBasis_iff_nbhd.mp hB) hp
    exact Opens.mem_iSup.mpr ⟨⟨j, hjU⟩, hpj⟩
  refine TopCat.Sheaf.eq_of_locally_eq' GAb (fun j : J ↦ B j.1) U.unop
    (fun j ↦ homOfLE j.2) hcover _ _ ?_
  intro j
  let k : U ⟶ op (B j.1) := (homOfLE j.2).op
  have hn (t : F.obj U) :
      G.val.restrictₛₗ k (φ.app U t) =
        φ.app (op (B j.1)) (F.restrictₛₗ k t) :=
    (CategoryTheory.congr_fun (φ.naturality k) t).symm
  change G.val.restrictₛₗ k (φ.app U
      (AddCommGrpCat.Hom.hom ((F.obj U).smul a) s)) =
    G.val.restrictₛₗ k (AddCommGrpCat.Hom.hom ((G.val.obj U).smul a) (φ.app U s))
  have hF : F.restrictₛₗ k
      (AddCommGrpCat.Hom.hom ((F.obj U).smul a) s) =
      AddCommGrpCat.Hom.hom ((F.obj (op (B j.1))).smul (O.obj.map k a))
        (F.restrictₛₗ k s) :=
    (F.restrictₛₗ k).map_smulₛₗ a s
  have hG : G.val.restrictₛₗ k
      (AddCommGrpCat.Hom.hom ((G.val.obj U).smul a) (φ.app U s)) =
      AddCommGrpCat.Hom.hom ((G.val.obj (op (B j.1))).smul (O.obj.map k a))
        (G.val.restrictₛₗ k (φ.app U s)) :=
    (G.val.restrictₛₗ k).map_smulₛₗ a (φ.app U s)
  have hlin : φ.app (op (B j.1))
      (AddCommGrpCat.Hom.hom ((F.obj (op (B j.1))).smul (O.obj.map k a))
        (F.restrictₛₗ k s)) =
      AddCommGrpCat.Hom.hom ((G.val.obj (op (B j.1))).smul (O.obj.map k a))
        (φ.app (op (B j.1)) (F.restrictₛₗ k s)) := by
    simpa only [φ, TopCat.Sheaf.extend_hom_app] using
      hα j.1 (O.obj.map k a) (F.restrictₛₗ k s)
  exact (hn _).trans
    ((congrArg (fun t : F.obj (op (B j.1)) ↦ φ.app (op (B j.1)) t) hF).trans
      (hlin.trans
        ((congrArg (fun t : G.val.obj (op (B j.1)) ↦
          AddCommGrpCat.Hom.hom ((G.val.obj (op (B j.1))).smul (O.obj.map k a)) t)
            (hn s).symm).trans hG.symm)))

private theorem homMkOfBasis_app
    {X : TopCat.{x}} {O : TopCat.Sheaf RingCat.{r} X}
    (F : PresheafOfModules.{max x z} O.obj)
    (G : SheafOfModules.{max x z} O)
    {ι : Type i} (B : ι → Opens X) (hB : Opens.IsBasis (Set.range B))
    (α : (inducedFunctor B).op ⋙ F.presheaf ⟶
      (inducedFunctor B).op ⋙ G.val.presheaf)
    (hα : ∀ (j : ι) (a : O.obj.obj (.op (B j))) (s : F.obj (.op (B j))),
      α.app (.op j) (AddCommGrpCat.Hom.hom ((F.obj (.op (B j))).smul a) s) =
        AddCommGrpCat.Hom.hom ((G.val.obj (.op (B j))).smul a) (α.app (.op j) s))
    (j : ι) (s : F.obj (.op (B j))) :
    (homMkOfBasis F G B hB α hα).app (.op (B j)) s =
      α.app (.op j) s := by
  have hnative
      (L : F.obj (.op (B j)) →ₗ[O.obj.obj (.op (B j))]
        G.val.obj (.op (B j))) :
      ConcreteCategory.hom (ModuleCat.ofHom L) s = L s :=
    LinearMap.congr_fun (ModuleCat.hom_ofHom L) s
  have happ :
      ConcreteCategory.hom
          ((homMkOfBasis F G B hB α hα).app (.op (B j))) s =
        AddCommGrpCat.Hom.hom
          ((TopCat.Sheaf.restrictHomEquivHom F.presheaf
            (⟨G.val.presheaf, G.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{max x z} X)
            hB α).app (.op (B j))) s := by
    simp only [homMkOfBasis, PresheafOfModules.homMk, hnative]
    rfl
  exact happ.trans
    (ConcreteCategory.congr_hom
      (TopCat.Sheaf.extend_hom_app F.presheaf
        (⟨G.val.presheaf, G.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{max x z} X)
        hB α j) s)

private theorem homTopAlgebraMap {R : CommRingCat.{u}} :
    algebraMap R Γ(Spec R, ⊤) = (Scheme.ΓSpecIso R).inv.hom :=
  algebraMap_top_eq_sigma

private theorem homAlgebraMap_restrict {R : CommRingCat.{u}}
    (U V : (Spec R).Opens) (h : U ≤ V) (a : R) :
    ((Spec R).presheaf.map (homOfLE h).op).hom (algebraMap R Γ(Spec R, V) a) =
      algebraMap R Γ(Spec R, U) a :=
  restrict_algebraMap h a

private theorem homUnitsOfLE {R : CommRingCat.{u}}
    (G : SheafOfModules.{max u v} (Spec R).ringCatSheaf)
    (f : R) (U : (Spec R).Opens) (hf : U ≤ PrimeSpectrum.basicOpen f) :
    ∀ s : Submonoid.powers f,
      IsUnit (algebraMap R (Module.End R
        ((ModuleCat.restrictScalars (algebraMap R Γ(Spec R, U))).obj
          (G.val.obj (.op U)))) s) := by
  have hu : IsUnit (η(R, U) f) := isUnit_eta_of_le_basicOpen f U hf
  rintro ⟨_, n, rfl⟩
  apply scalarEnd_isUnit (algebraMap R Γ(Spec R, U)) (G.val.obj (.op U)) (f ^ n)
  simpa only [IsAffineOpen.algebraMap_Spec_obj, map_pow] using hu.pow n

private def homRestrictLinear {R : CommRingCat.{u}}
    (F : PresheafOfModules.{z} (Spec R).ringCatSheaf.obj)
    {U V : (Spec R).Opens} (h : U ≤ V)
    (ηV : R →+* Γ(Spec R, V)) (ηU : R →+* Γ(Spec R, U))
    (hη : ηU = ((Spec R).ringCatSheaf.obj.map (homOfLE h).op).hom.comp ηV) :
    (ModuleCat.restrictScalars ηV).obj (F.obj (op V)) →ₗ[R]
      (ModuleCat.restrictScalars ηU).obj (F.obj (op U)) :=
  (((ModuleCat.restrictScalars ηV).map (F.map (homOfLE h).op)) ≫
    (ModuleCat.restrictScalarsComp'App ηV
      ((Spec R).ringCatSheaf.obj.map (homOfLE h).op).hom ηU hη
      (F.obj (op U))).inv).hom

private theorem homRestrictLinear_apply {R : CommRingCat.{u}}
    (F : PresheafOfModules.{z} (Spec R).ringCatSheaf.obj)
    {U V : (Spec R).Opens} (h : U ≤ V)
    (ηV : R →+* Γ(Spec R, V)) (ηU : R →+* Γ(Spec R, U))
    (hη : ηU = ((Spec R).ringCatSheaf.obj.map (homOfLE h).op).hom.comp ηV)
    (s : (ModuleCat.restrictScalars ηV).obj (F.obj (op V))) :
    homRestrictLinear F h ηV ηU hη s = F.restrictₛₗ (homOfLE h).op s := rfl

private def homTopRestrictLinear {R : CommRingCat.{u}}
    (F : PresheafOfModules.{z} (Spec R).ringCatSheaf.obj) (U : (Spec R).Opens) :
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).obj (F.obj (op ⊤)) →ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R Γ(Spec R, U))).obj (F.obj (op U)) :=
  homRestrictLinear F (show U ≤ ⊤ from le_top) (Scheme.ΓSpecIso R).inv.hom
    (algebraMap R Γ(Spec R, U)) IsAffineOpen.algebraMap_Spec_obj

private theorem homTopRestrictLinear_apply {R : CommRingCat.{u}}
    (F : PresheafOfModules.{z} (Spec R).ringCatSheaf.obj) (U : (Spec R).Opens)
    (s : (ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).obj (F.obj (op ⊤))) :
    homTopRestrictLinear F U s = F.restrictₛₗ U.leTop.op s := rfl

private def homForward {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (G : SheafOfModules.{max u v} (Spec R).ringCatSheaf)
    (φ : moduleTilde M ⟶ G) :
    M →ₗ[R] (ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).obj
      (G.val.obj (.op ⊤)) :=
  (((ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).map
    (φ.val.app (.op ⊤))).hom).comp (toTopLinearMap M)

private def basicLift {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (G : SheafOfModules.{max u v} (Spec R).ringCatSheaf)
    (q : M →ₗ[R] (ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).obj
      (G.val.obj (.op ⊤))) (f : R) :
    (moduleTilde M).val.obj (.op (PrimeSpectrum.basicOpen f)) →ₗ[
      (Spec R).ringCatSheaf.obj.obj (.op (PrimeSpectrum.basicOpen f))]
      G.val.obj (.op (PrimeSpectrum.basicOpen f)) := by
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen f
  let A : CommRingCat.{u} := Γ(Spec R, U)
  let P := (ModuleCat.restrictScalars (algebraMap R A)).obj
    ((moduleTilde M).val.obj (.op U))
  let N := (ModuleCat.restrictScalars (algebraMap R A)).obj (G.val.obj (.op U))
  let : Module A P := ((moduleTilde M).val.obj (.op U)).isModule
  let : Module A N := (G.val.obj (.op U)).isModule
  let : IsScalarTower R A P := .of_algebraMap_smul fun _ _ ↦ rfl
  let : IsScalarTower R A N := .of_algebraMap_smul fun _ _ ↦ rfl
  letI : IsLocalizedModule (.powers f)
      (show M →ₗ[R] P from toOpen M U) :=
    isLocalizedModule_toOpen M f
  let qU : M →ₗ[R] N := (homTopRestrictLinear G.val U).comp q
  let eR : P →ₗ[R] N := IsLocalizedModule.lift (.powers f)
    (toOpen M U) qU (homUnitsOfLE G f U le_rfl)
  exact eR.extendScalarsOfIsLocalization (.powers f) A

private theorem basicLift_toOpen {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (G : SheafOfModules.{max u v} (Spec R).ringCatSheaf)
    (q : M →ₗ[R] (ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).obj
      (G.val.obj (.op ⊤))) (f : R) (m : M) :
    basicLift M G q f (toOpen M (PrimeSpectrum.basicOpen f) m) =
      G.val.map (PrimeSpectrum.basicOpen f).leTop.op (q m) := by
  let : IsLocalizedModule (.powers f)
      (toOpen M (PrimeSpectrum.basicOpen f)) :=
    isLocalizedModule_toOpen M f
  exact IsLocalizedModule.lift_apply (.powers f)
    (toOpen M (PrimeSpectrum.basicOpen f))
    ((homTopRestrictLinear G.val (PrimeSpectrum.basicOpen f)).comp q)
    (homUnitsOfLE G f (PrimeSpectrum.basicOpen f) le_rfl) m

private theorem hom_app_toOpen_top {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (G : SheafOfModules.{max u v} (Spec R).ringCatSheaf)
    (φ : moduleTilde M ⟶ G) (U : (Spec R).Opens) (m : M) :
    φ.val.app (op U) (toOpen M U m) =
      G.val.restrictₛₗ U.leTop.op (φ.val.app (op ⊤) (toOpen M ⊤ m)) := by
  have hr : (moduleTilde M).val.restrictₛₗ U.leTop.op (toOpen M ⊤ m) =
      toOpen M U m := toOpen_res M (show U ≤ ⊤ from le_top) m
  have hn : φ.val.app (op U)
        ((moduleTilde M).val.restrictₛₗ U.leTop.op (toOpen M ⊤ m)) =
      G.val.restrictₛₗ U.leTop.op (φ.val.app (op ⊤) (toOpen M ⊤ m)) :=
    PresheafOfModules.naturality_apply φ.val U.leTop.op (toOpen M ⊤ m)
  exact (congrArg (fun t : (moduleTilde M).val.obj (op U) ↦
    φ.val.app (op U) t) hr.symm).trans hn

/-- Morphisms from the associated sheaf are determined by their values on
numerators over the whole spectrum. -/
theorem hom_ext {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (G : SheafOfModules.{max u v} (Spec R).ringCatSheaf)
    {φ ψ : moduleTilde M ⟶ G}
    (h : ∀ m : M, φ.val.app (.op ⊤) (toOpen M ⊤ m) =
      ψ.val.app (.op ⊤) (toOpen M ⊤ m)) : φ = ψ := by
  apply SheafOfModules.hom_ext
  apply (PresheafOfModules.toPresheaf (Spec R).ringCatSheaf.obj).map_injective
  apply TopCat.Sheaf.hom_ext (moduleTilde M).val.presheaf
    (⟨G.val.presheaf, G.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{max u v} (Spec R))
    PrimeSpectrum.isBasis_basic_opens
  intro f
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen f
  let η := algebraMap R Γ(Spec R, U)
  have he : ((ModuleCat.restrictScalars η).map (φ.val.app (.op U))).hom =
      ((ModuleCat.restrictScalars η).map (ψ.val.app (.op U))).hom := by
    apply IsLocalizedModule.ext (.powers f) (toOpen M U) (homUnitsOfLE G f U le_rfl)
    apply LinearMap.ext
    intro m
    change φ.val.app (.op U) (toOpen M U m) =
      ψ.val.app (.op U) (toOpen M U m)
    exact (hom_app_toOpen_top M G φ U m).trans
      ((congrArg (fun t : G.val.obj (op ⊤) ↦ G.val.restrictₛₗ U.leTop.op t)
        (h m)).trans (hom_app_toOpen_top M G ψ U m).symm)
  ext s
  exact LinearMap.congr_fun he s

private theorem basicLift_naturality {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (G : SheafOfModules.{max u v} (Spec R).ringCatSheaf)
    (q : M →ₗ[R] (ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).obj
      (G.val.obj (.op ⊤)))
    (f g : R) (h : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f)
    (s : (moduleTilde M).val.obj (.op (PrimeSpectrum.basicOpen f))) :
    basicLift M G q g ((moduleTilde M).val.map (homOfLE h).op s) =
      G.val.map (homOfLE h).op (basicLift M G q f s) := by
  let F := moduleTilde M
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen f
  let V : (Spec R).Opens := PrimeSpectrum.basicOpen g
  let ηU := algebraMap R Γ(Spec R, U)
  let ηV := algebraMap R Γ(Spec R, V)
  have hη : ηV = ((Spec R).ringCatSheaf.obj.map (homOfLE h).op).hom.comp ηU := by
    ext a
    exact (homAlgebraMap_restrict V U h a).symm
  let rF := homRestrictLinear F.val h ηU ηV hη
  let rG := homRestrictLinear G.val h ηU ηV hη
  let aU := ((ModuleCat.restrictScalars ηU).map
    (ModuleCat.ofHom (X := F.val.obj (op U)) (Y := G.val.obj (op U))
      (basicLift M G q f))).hom
  let aV := ((ModuleCat.restrictScalars ηV).map
    (ModuleCat.ofHom (X := F.val.obj (op V)) (Y := G.val.obj (op V))
      (basicLift M G q g))).hom
  have he : aV.comp rF = rG.comp aU := by
    apply IsLocalizedModule.ext (.powers f) (toOpen M U) (homUnitsOfLE G f V h)
    ext m
    change basicLift M G q g
        ((moduleTilde M).val.restrictₛₗ (homOfLE h).op (toOpen M U m)) =
      G.val.restrictₛₗ (homOfLE h).op (basicLift M G q f (toOpen M U m))
    have hc : G.val.restrictₛₗ (homOfLE h).op
          (G.val.restrictₛₗ U.leTop.op (q m)) =
        G.val.restrictₛₗ V.leTop.op (q m) := by
      have hi : U.leTop.op ≫ (homOfLE h).op = V.leTop.op := Subsingleton.elim _ _
      exact (G.val.map_comp_apply U.leTop.op (homOfLE h).op (q m)).symm.trans
        (G.val.congr_map_apply hi (q m))
    exact ((congrArg (basicLift M G q g) (toOpen_res M h m)).trans
      (basicLift_toOpen M G q g m)).trans
        (hc.symm.trans
          (congrArg (fun t : G.val.obj (op U) ↦ G.val.restrictₛₗ (homOfLE h).op t)
            (basicLift_toOpen M G q f m)).symm)
  exact LinearMap.congr_fun he s

private def homInverse {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (G : SheafOfModules.{max u v} (Spec R).ringCatSheaf)
    (q : M →ₗ[R] (ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).obj
      (G.val.obj (.op ⊤))) : moduleTilde M ⟶ G := by
  let B : R → (Spec R).Opens := PrimeSpectrum.basicOpen
  let β : (inducedFunctor B).op ⋙ (moduleTilde M).val.presheaf ⟶
      (inducedFunctor B).op ⋙ G.val.presheaf :=
    { app f := AddCommGrpCat.ofHom (basicLift M G q f.unop).toAddMonoidHom
      naturality {f g} i := by
        ext s
        exact basicLift_naturality M G q f.unop g.unop i.1.hom.le s }
  exact ⟨homMkOfBasis (moduleTilde M).val G B
    PrimeSpectrum.isBasis_basic_opens β
    (fun f a s ↦ (basicLift M G q f).map_smul a s)⟩

private theorem homInverse_toOpen_basic {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (G : SheafOfModules.{max u v} (Spec R).ringCatSheaf)
    (q : M →ₗ[R] (ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).obj
      (G.val.obj (.op ⊤))) (f : R) (m : M) :
    (homInverse M G q).val.app (.op (PrimeSpectrum.basicOpen f))
        (toOpen M (PrimeSpectrum.basicOpen f) m) =
      G.val.map (PrimeSpectrum.basicOpen f).leTop.op (q m) := by
  refine Eq.trans ?_ (basicLift_toOpen M G q f m)
  unfold homInverse
  exact homMkOfBasis_app (moduleTilde M).val G
    (PrimeSpectrum.basicOpen : R → (Spec R).Opens)
    PrimeSpectrum.isBasis_basic_opens
    _ (fun j a s ↦ (basicLift M G q j).map_smul a s) f
    (toOpen M (PrimeSpectrum.basicOpen f) m)

private theorem homInverse_toOpen_top {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (G : SheafOfModules.{max u v} (Spec R).ringCatSheaf)
    (q : M →ₗ[R] (ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).obj
      (G.val.obj (Opposite.op ⊤))) (m : M) :
    (homInverse M G q).val.app (Opposite.op ⊤) (toOpen M ⊤ m) = q m := by
  have h := homInverse_toOpen_basic M G q (1 : R) m
  rw [PrimeSpectrum.basicOpen_one] at h
  refine h.trans ?_
  change G.val.presheaf.map
    (homOfLE (show (⊤ : (Spec R).Opens) ≤ ⊤ from le_top)).op (q m) = q m
  have hi : (homOfLE (show (⊤ : (Spec R).Opens) ≤ ⊤ from le_top)).op =
      𝟙 (Opposite.op (⊤ : (Spec R).Opens)) := Subsingleton.elim _ _
  rw [hi]
  exact ConcreteCategory.congr_hom
    (G.val.presheaf.map_id (Opposite.op (⊤ : (Spec R).Opens))) (q m)

private theorem homInverse_toOpen {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (G : SheafOfModules.{max u v} (Spec R).ringCatSheaf)
    (q : M →ₗ[R] (ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).obj
      (G.val.obj (.op ⊤))) (U : (Spec R).Opens) (m : M) :
    (homInverse M G q).val.app (.op U) (toOpen M U m) =
      G.val.map U.leTop.op (q m) := by
  exact (hom_app_toOpen_top M G (homInverse M G q) U m).trans
    (congrArg (fun t : G.val.obj (op ⊤) ↦ G.val.restrictₛₗ U.leTop.op t)
      (homInverse_toOpen_top M G q m))

/-- Morphisms from the associated sheaf to a sheaf of modules correspond to
linear maps from the original module into the top sections of the target,
with scalars restricted along the structure-sheaf isomorphism. -/
@[no_expose]
def homEquiv {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (G : SheafOfModules.{max u v} (Spec R).ringCatSheaf) :
    (moduleTilde M ⟶ G) ≃
      (M →ₗ[R] (ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).obj
        (G.val.obj (.op ⊤))) where
  toFun := homForward M G
  invFun := homInverse M G
  left_inv φ := by
    apply hom_ext M G
    intro m
    exact homInverse_toOpen_top M G (homForward M G φ) m
  right_inv q := by
    apply LinearMap.ext
    intro m
    exact homInverse_toOpen_top M G q m

/-- The Hom correspondence evaluates a morphism on the top numerator. -/
@[simp]
theorem homEquiv_apply {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (G : SheafOfModules.{max u v} (Spec R).ringCatSheaf)
    (φ : moduleTilde M ⟶ G) (m : M) :
    homEquiv M G φ m = φ.val.app (.op ⊤) (toOpen M ⊤ m) := (rfl)

/-- The inverse Hom correspondence sends a numerator on an open set to the
restriction of the specified top section. -/
@[simp]
theorem homEquiv_symm_toOpen {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (G : SheafOfModules.{max u v} (Spec R).ringCatSheaf)
    (q : M →ₗ[R] (ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).obj
      (G.val.obj (.op ⊤))) (U : (Spec R).Opens) (m : M) :
    ((homEquiv M G).symm q).val.app (.op U) (toOpen M U m) =
      G.val.map U.leTop.op (q m) :=
  homInverse_toOpen M G q U m

private def diagonalSectionEquiv {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (U : (Spec R).Opens) :
    (moduleTilde M).val.obj (.op U) ≃ₗ[(Spec R).ringCatSheaf.obj.obj (.op U)]
      (AlgebraicGeometry.tilde M).val.obj (.op U) where
  toFun s := ⟨s.1, s.2⟩
  invFun s := ⟨s.1, s.2⟩
  left_inv _s := Subtype.ext rfl
  right_inv _s := Subtype.ext rfl
  map_add' _s _t := Subtype.ext rfl
  map_smul' _a _s := Subtype.ext rfl

/-- The associated sheaf agrees with the usual associated sheaf when the module
and scalar ring have the same universe; the section functions are unchanged. -/
@[no_expose]
def isoTilde {R : CommRingCat.{u}} (M : ModuleCat.{u} R) :
    moduleTilde M ≅ AlgebraicGeometry.tilde M where
  hom :=
    ⟨{ app := fun U ↦ (diagonalSectionEquiv M U.unop).toModuleIso.hom
       naturality := fun {U V} h ↦ by
         ext s
         apply Subtype.ext
         funext p
         rfl }⟩
  inv :=
    ⟨{ app := fun U ↦ (diagonalSectionEquiv M U.unop).toModuleIso.inv
       naturality := fun {U V} h ↦ by
         ext s
         apply Subtype.ext
         funext p
         rfl }⟩
  hom_inv_id := by
    ext U s
    exact (diagonalSectionEquiv M U.unop).left_inv s
  inv_hom_id := by
    ext U s
    exact (diagonalSectionEquiv M U.unop).right_inv s

private def stockOpenRComparison {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (U : (Spec R).Opens) :
    (ModuleCat.restrictScalars (algebraMap R Γ(Spec R, U))).obj
      ((AlgebraicGeometry.tilde M).val.obj (.op U)) ≅
      (AlgebraicGeometry.structurePresheafInModuleCat R M).obj (.op U) := by
  let σ := (Scheme.ΓSpecIso R).inv.hom
  let ρ := ((Spec R).ringCatSheaf.obj.map U.leTop.op).hom
  let η := algebraMap R Γ(Spec R, U)
  have hη : η = ρ.comp σ :=
    IsAffineOpen.algebraMap_Spec_obj
  exact (ModuleCat.restrictScalarsComp'App σ ρ η hη
    ((AlgebraicGeometry.tilde M).val.obj (.op U))) ≪≫
    ((AlgebraicGeometry.tilde.modulesSpecToSheafIso M).app (.op U))

/-- The diagonal comparison leaves the value of a section at every prime unchanged. -/
theorem isoTilde_eval {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (U : (Spec R).Opens) (s : (moduleTilde M).val.obj (.op U)) (p : U) :
    ((isoTilde M).hom.val.app (.op U) s).1 p = eval M U p s := (rfl)

/-- The inverse diagonal comparison leaves section values unchanged. -/
theorem isoTilde_inv_eval {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (U : (Spec R).Opens) (s : (AlgebraicGeometry.tilde M).val.obj (.op U)) (p : U) :
    eval M U p ((isoTilde M).inv.val.app (.op U) s) = s.1 p := (rfl)

/-- The diagonal comparison sends each numerator to the usual numerator. -/
theorem isoTilde_toOpen {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (U : (Spec R).Opens) (m : M) :
    (isoTilde M).hom.val.app (.op U) (toOpen M U m) =
      (AlgebraicGeometry.tilde.toOpen M U).hom m := by
  apply (stockOpenRComparison M U).toLinearEquiv.injective
  apply Subtype.ext
  funext p
  rfl

/-- The inverse diagonal comparison sends the usual numerator to its numerator. -/
theorem isoTilde_inv_toOpen {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (U : (Spec R).Opens) (m : M) :
    (isoTilde M).inv.val.app (.op U) ((AlgebraicGeometry.tilde.toOpen M U).hom m) =
      toOpen M U m := by
  apply Subtype.ext
  funext p
  rfl

/-- The diagonal comparison preserves a fraction on every open on which its
specified denominator is invertible. -/
theorem isoTilde_fraction {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (U : (Spec R).Opens) (m : M) (s : R) (h : U ≤ PrimeSpectrum.basicOpen s) :
    (isoTilde M).hom.val.app (.op U) (fraction M U m s h) =
      StructureSheaf.const m s U h := by
  apply Subtype.ext
  funext p
  rfl

/-- The inverse diagonal comparison preserves a fraction with its given numerator
and denominator. -/
theorem isoTilde_inv_fraction {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (U : (Spec R).Opens) (m : M) (s : R) (h : U ≤ PrimeSpectrum.basicOpen s) :
    (isoTilde M).inv.val.app (.op U) (StructureSheaf.const m s U h) =
      fraction M U m s h := by
  apply Subtype.ext
  funext p
  rfl

/-- On numerators the top equivalence agrees with the usual top-section
isomorphism under the diagonal comparison. -/
theorem isoTilde_topLinearEquiv {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (m : M) :
    (isoTilde M).hom.val.app (.op ⊤) (topLinearEquiv M m) =
      (AlgebraicGeometry.tilde.isoTop M).hom m := by
  rw [topLinearEquiv_apply, isoTilde_toOpen]
  rfl

/-- The inverse top equivalence agrees with the usual inverse top-section
isomorphism under the diagonal comparison. -/
theorem isoTilde_topLinearEquiv_symm {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (s : (AlgebraicGeometry.tilde M).val.obj (.op ⊤)) :
    (topLinearEquiv M).symm ((isoTilde M).inv.val.app (.op ⊤) s) =
      (AlgebraicGeometry.tilde.isoTop M).inv s := by
  have hs : s = (AlgebraicGeometry.tilde.toOpen M ⊤).hom
      ((AlgebraicGeometry.tilde.isoTop M).inv s) :=
    (ConcreteCategory.congr_hom (AlgebraicGeometry.tilde.isoTop M).inv_hom_id s).symm
  calc
    (topLinearEquiv M).symm ((isoTilde M).inv.val.app (.op ⊤) s) =
        (topLinearEquiv M).symm ((isoTilde M).inv.val.app (.op ⊤)
          ((AlgebraicGeometry.tilde.toOpen M ⊤).hom
            ((AlgebraicGeometry.tilde.isoTop M).inv s))) :=
      congrArg (fun t ↦ (topLinearEquiv M).symm
        ((isoTilde M).inv.val.app (.op ⊤) t)) hs
    _ = (AlgebraicGeometry.tilde.isoTop M).inv s := by
      rw [isoTilde_inv_toOpen, topLinearEquiv_symm_toOpen]

/-- The associated-sheaf morphism determined by a module map on numerators. -/
def map {R : CommRingCat.{u}} {M N : ModuleCat.{v} R} (a : M ⟶ N) :
    moduleTilde M ⟶ moduleTilde N :=
  (homEquiv M (moduleTilde N)).symm
    ((topLinearEquiv N).toLinearMap.comp a.hom)

/-- A module map acts on the numerator of a section by its original linear map. -/
@[simp]
theorem toOpen_map_app {R : CommRingCat.{u}} {M N : ModuleCat.{v} R}
    (a : M ⟶ N) (U : (Spec R).Opens) (m : M) :
    (map a).val.app (.op U) (toOpen M U m) = toOpen N U (a.hom m) := by
  change ((homEquiv M (moduleTilde N)).symm
    ((topLinearEquiv N).toLinearMap.comp a.hom)).val.app (.op U)
      (toOpen M U m) = _
  rw [homEquiv_symm_toOpen]
  change (moduleTilde N).val.map U.leTop.op
    (topLinearEquiv N (a.hom m)) = _
  rw [topLinearEquiv_apply]
  exact toOpen_res N le_top (a.hom m)

/-- The associated-sheaf map of the identity module map is the identity. -/
@[simp]
theorem map_id {R : CommRingCat.{u}} (M : ModuleCat.{v} R) :
    map (𝟙 M) = 𝟙 (moduleTilde M) := by
  apply hom_ext M (moduleTilde M)
  intro m
  change (map (𝟙 M)).val.app (.op ⊤) (toOpen M ⊤ m) = toOpen M ⊤ m
  rw [toOpen_map_app]
  rfl

/-- Associated-sheaf maps preserve composition of module maps. -/
@[simp]
theorem map_comp {R : CommRingCat.{u}} {M N P : ModuleCat.{v} R}
    (a : M ⟶ N) (b : N ⟶ P) : map (a ≫ b) = map a ≫ map b := by
  apply hom_ext M (moduleTilde P)
  intro m
  change (map (a ≫ b)).val.app (.op ⊤) (toOpen M ⊤ m) =
    (map b).val.app (.op ⊤) ((map a).val.app (.op ⊤) (toOpen M ⊤ m))
  rw [toOpen_map_app, toOpen_map_app, toOpen_map_app]
  rfl

/-- The associated-sheaf functor for a fixed coefficient-module universe. -/
def functor (R : CommRingCat.{u}) :
    ModuleCat.{v} R ⥤ SheafOfModules.{max u v} (Spec R).ringCatSheaf where
  obj := moduleTilde
  map := map
  map_id := map_id
  map_comp := map_comp

/-- The Hom correspondence is natural in maps of the coefficient module. -/
theorem homEquiv_naturality {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    {N : ModuleCat.{v} R}
    (G : SheafOfModules.{max u v} (Spec R).ringCatSheaf)
    (a : M ⟶ N) (φ : moduleTilde N ⟶ G) :
    homEquiv M G (map a ≫ φ) = (homEquiv N G φ).comp a.hom := by
  apply LinearMap.ext
  intro m
  change φ.val.app (.op ⊤) ((map a).val.app (.op ⊤) (toOpen M ⊤ m)) =
    φ.val.app (.op ⊤) (toOpen N ⊤ (a.hom m))
  rw [toOpen_map_app]

/-- The Hom correspondence is natural in maps of the target sheaf of modules. -/
theorem homEquiv_naturality_right {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (G H : SheafOfModules.{max u v} (Spec R).ringCatSheaf)
    (φ : moduleTilde M ⟶ G) (b : G ⟶ H) :
    homEquiv M H (φ ≫ b) =
      (((ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).map
        (b.val.app (.op ⊤))).hom).comp (homEquiv M G φ) := by
  apply LinearMap.ext
  intro m
  rfl

/-- The diagonal comparison commutes with morphisms of coefficient modules. -/
theorem isoTilde_naturality {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    {N : ModuleCat.{u} R} (a : M ⟶ N) :
    map a ≫ (isoTilde N).hom = (isoTilde M).hom ≫ AlgebraicGeometry.tilde.map a := by
  apply hom_ext M (AlgebraicGeometry.tilde N)
  intro m
  change (isoTilde N).hom.val.app (.op ⊤)
      ((map a).val.app (.op ⊤) (toOpen M ⊤ m)) =
    (AlgebraicGeometry.tilde.map a).val.app (.op ⊤)
      ((isoTilde M).hom.val.app (.op ⊤) (toOpen M ⊤ m))
  rw [toOpen_map_app, isoTilde_toOpen, isoTilde_toOpen]
  exact (ConcreteCategory.congr_hom
    (AlgebraicGeometry.tilde.toOpen_map_app a ⊤) m).symm

universe t

/-- The principal-open scalar isomorphism and its inverse form an inverse pair. -/
instance awayRingHomInvPair (R : CommRingCat.{u}) (f : R) :
    RingHomInvPair
      (ΓAwayRing(R, f)).toRingHom
      (ΓAwayRing(R, f)).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv
    (ΓAwayRing(R, f))

/-- The inverse principal-open scalar isomorphism forms the reverse inverse pair. -/
instance awayRingHomInvPair_symm (R : CommRingCat.{u}) (f : R) :
    RingHomInvPair
      (ΓAwayRing(R, f)).symm.toRingHom
      (ΓAwayRing(R, f)).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm
    (ΓAwayRing(R, f))

/- The target retains its given section-ring action. The temporary action on
localization fractions occurs only on the source. -/
private noncomputable def awayEquivOfIsLocalizedModule
    (R : CommRingCat.{u}) (L : ModuleCat.{v} R) (f : R) {T : Type t}
    [AddCommGroup T] [Module R T]
    [Module Γ(Spec R, (PrimeSpectrum.basicOpen f : (Spec R).Opens)) T]
    [@IsScalarTower R Γ(Spec R, (PrimeSpectrum.basicOpen f : (Spec R).Opens)) T
      (@Algebra.toSMul (CommRingCat.carrier R)
        (CommRingCat.carrier
          (Γ(Spec R, (PrimeSpectrum.basicOpen f : (Spec R).Opens)) : CommRingCat.{u}))
        _ _ ΓAlg(R, (PrimeSpectrum.basicOpen f : (Spec R).Opens))) _ _]
    (ι : L →ₗ[R] T) [IsLocalizedModule (.powers f) ι] :
    LinearEquiv
      (σ' := (ΓAwayRing(R, f)).symm.toRingHom)
      (ΓAwayRing(R, f)).toRingHom
      (LocalizedModule (.powers f) L) T := by
  let : Algebra R Γ(Spec R, (PrimeSpectrum.basicOpen f : (Spec R).Opens)) :=
    ΓAlg(R, (PrimeSpectrum.basicOpen f : (Spec R).Opens))
  let : IsLocalization.Away f
      Γ(Spec R, (PrimeSpectrum.basicOpen f : (Spec R).Opens)) :=
    StructureSheaf.IsLocalization.to_basicOpen R f
  let : Module Γ(Spec R, (PrimeSpectrum.basicOpen f : (Spec R).Opens))
      (LocalizedModule (.powers f) L) := LocalizedModule.moduleOfIsLocalization
  have hsmul (r : Localization.Away f) (x : LocalizedModule (.powers f) L) :
      r • x = ΓAwayRing(R, f) r • x := by
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (.powers f) r
    induction x using LocalizedModule.induction_on with
    | h m t =>
      have hΓ :
          ΓAwayRing(R, f) (IsLocalization.mk' (Localization.Away f) a s) =
            IsLocalization.mk'
              Γ(Spec R, (PrimeSpectrum.basicOpen f : (Spec R).Opens)) a s :=
        IsLocalization.algEquiv_mk' a s
      calc
        IsLocalization.mk' (Localization.Away f) a s • LocalizedModule.mk m t =
            Localization.mk a s • LocalizedModule.mk m t :=
          congrArg (fun z : Localization.Away f ↦ z • LocalizedModule.mk m t)
            (Localization.mk_eq_mk'_apply a s).symm
        _ = LocalizedModule.mk (a • m) (s * t) :=
          LocalizedModule.mk_smul_mk a m s t
        _ = IsLocalization.mk'
              Γ(Spec R, (PrimeSpectrum.basicOpen f : (Spec R).Opens)) a s •
                LocalizedModule.mk m t :=
          (LocalizedModule.mk'_smul_mk
            (T := Γ(Spec R, (PrimeSpectrum.basicOpen f : (Spec R).Opens)))
            a m s t).symm
        _ = ΓAwayRing(R, f) (IsLocalization.mk' (Localization.Away f) a s) •
              LocalizedModule.mk m t :=
          congrArg
            (fun z : Γ(Spec R, (PrimeSpectrum.basicOpen f : (Spec R).Opens)) ↦
              z • LocalizedModule.mk m t) hΓ.symm
  let e : LocalizedModule (.powers f) L ≃ₗ[R] T :=
    IsLocalizedModule.iso (.powers f) ι
  let eS : LocalizedModule (.powers f) L ≃ₗ[
      Γ(Spec R, (PrimeSpectrum.basicOpen f : (Spec R).Opens))] T :=
    e.extendScalarsOfIsLocalization (.powers f)
      Γ(Spec R, (PrimeSpectrum.basicOpen f : (Spec R).Opens))
  exact
    { e.toAddEquiv with
      map_smul' := fun r x ↦ by
        change eS (r • x) = ΓAwayRing(R, f) r • eS x
        rw [hsmul r x, eS.map_smul] }

/-- Canonical equivalence from the localized module over `Localization.Away f`
to sections on `D(f)`. It is semilinear over the
`IsLocalization.algEquiv` from `Away f` to `Γ(Spec R, D(f))`. -/
@[no_expose]
noncomputable def _root_.AlgebraicGeometry.Scheme.Modules.awayModuleEquiv
    (R : CommRingCat.{u}) (L : ModuleCat.{u} R) (f : R) :
    letI : RingHomInvPair
        (ΓAwayRing(R, f)).toRingHom
        (ΓAwayRing(R, f)).symm.toRingHom :=
      awayRingHomInvPair R f
    letI : RingHomInvPair
        (ΓAwayRing(R, f)).symm.toRingHom
        (ΓAwayRing(R, f)).toRingHom :=
      awayRingHomInvPair_symm R f
    letI : Module Γ(Spec R, (PrimeSpectrum.basicOpen f : (Spec R).Opens))
        Γ(tilde L, (PrimeSpectrum.basicOpen f : (Spec R).Opens)) :=
      ((AlgebraicGeometry.tilde L).val.obj
        (.op (PrimeSpectrum.basicOpen f : (Spec R).Opens))).isModule
    LinearEquiv (σ' := (ΓAwayRing(R, f)).symm.toRingHom)
      (ΓAwayRing(R, f)).toRingHom
      (LocalizedModule (.powers f) L)
      Γ(tilde L, (PrimeSpectrum.basicOpen f : (Spec R).Opens)) := by
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen f
  let : Algebra R Γ(Spec R, U) := ΓAlg(R, U)
  let : IsLocalization.Away f Γ(Spec R, U) :=
    StructureSheaf.IsLocalization.to_basicOpen R f
  let T : ModuleCat.{u} R :=
    (modulesSpecToSheaf.obj (AlgebraicGeometry.tilde L)).presheaf.obj (.op U)
  let : Module Γ(Spec R, U) T :=
    ((AlgebraicGeometry.tilde L).val.obj (.op U)).isModule
  let : IsScalarTower R Γ(Spec R, U) T :=
    IsScalarTower.of_algebraMap_smul fun r t ↦ by
      have hη :
          (@algebraMap (CommRingCat.carrier R)
            (CommRingCat.carrier (Γ(Spec R, U) : CommRingCat.{u})) _ _
            ΓAlg(R, U)) = η(R, U) :=
        AlgebraicGeometry.IsAffineOpen.algebraMap_Spec_obj (R := R) (U := U)
      exact (congrArg (fun a : Γ(Spec R, U) ↦ a • t)
        (RingHom.congr_fun hη r)).trans
          (Scheme.Modules.smul_Spec_def
            (M := AlgebraicGeometry.tilde L) (U := U) r t).symm
  letI : IsLocalizedModule (.powers f) (AlgebraicGeometry.tilde.toOpen L U).hom :=
    inferInstanceAs
      (IsLocalizedModule (.powers f)
        (AlgebraicGeometry.tilde.toOpen L
          (PrimeSpectrum.basicOpen f : (Spec R).Opens)).hom)
  exact awayEquivOfIsLocalizedModule R L f (T := T)
    (AlgebraicGeometry.tilde.toOpen L U).hom

/-- The principal-open comparison sends a localized numerator to its section. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.awayModuleEquiv_mk
    (R : CommRingCat.{u}) (L : ModuleCat.{u} R) (f : R) (m : L) :
    (_root_.AlgebraicGeometry.Scheme.Modules.awayModuleEquiv R L f).toFun (LocalizedModule.mk m 1) =
      (tilde.toOpen L (PrimeSpectrum.basicOpen f)).hom m := by
  exact IsLocalizedModule.iso_mk_one (.powers f)
    (tilde.toOpen L (PrimeSpectrum.basicOpen f)).hom m

private theorem tilde_awayModuleEquiv_apply_eq_iso
    (R : CommRingCat.{u}) (L : ModuleCat.{u} R) (f : R)
    (x : LocalizedModule (.powers f) L) :
    (_root_.AlgebraicGeometry.Scheme.Modules.awayModuleEquiv R L f).toFun x =
      IsLocalizedModule.iso (.powers f)
        (tilde.toOpen L (PrimeSpectrum.basicOpen f)).hom x := (rfl)

private theorem tilde_awayModuleEquiv_symm_eq_iso_symm
    (R : CommRingCat.{u}) (L : ModuleCat.{u} R) (f : R)
    (s : Γ(tilde L, (PrimeSpectrum.basicOpen f : (Spec R).Opens))) :
    (_root_.AlgebraicGeometry.Scheme.Modules.awayModuleEquiv R L f).symm.toFun s =
      (IsLocalizedModule.iso (.powers f)
        (tilde.toOpen L (PrimeSpectrum.basicOpen f)).hom).symm s := (rfl)

/-- Sections of the associated sheaf on `D(f)` are semilinearly equivalent to
its localized module, along the canonical isomorphism from `Away f` to the
structure-sheaf section ring. -/
@[no_expose]
noncomputable def awayModuleEquiv {R : CommRingCat.{u}} (M : ModuleCat.{v} R) (f : R) :
    letI : Module Γ(Spec R, (PrimeSpectrum.basicOpen f : (Spec R).Opens))
        ((moduleTilde M).val.obj (.op (PrimeSpectrum.basicOpen f))) :=
      ((moduleTilde M).val.obj
        (.op (PrimeSpectrum.basicOpen f : (Spec R).Opens))).isModule
    LinearEquiv (σ' := (ΓAwayRing(R, f)).symm.toRingHom)
      (ΓAwayRing(R, f)).toRingHom
      (LocalizedModule (.powers f) M)
      ((moduleTilde M).val.obj (.op (PrimeSpectrum.basicOpen f))) := by
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen f
  let : Algebra R Γ(Spec R, U) := ΓAlg(R, U)
  let : IsLocalization.Away f Γ(Spec R, U) :=
    StructureSheaf.IsLocalization.to_basicOpen R f
  let T : ModuleCat.{max u v} R := Q(R, M, U)
  let : Module Γ(Spec R, U) T :=
    ((moduleTilde M).val.obj (.op U)).isModule
  let : IsScalarTower R Γ(Spec R, U) T :=
    IsScalarTower.of_algebraMap_smul fun r t ↦ by
      have hη :
          (@algebraMap (CommRingCat.carrier R)
            (CommRingCat.carrier (Γ(Spec R, U) : CommRingCat.{u})) _ _
            ΓAlg(R, U)) = η(R, U) :=
        AlgebraicGeometry.IsAffineOpen.algebraMap_Spec_obj (R := R) (U := U)
      exact (congrArg (fun a : Γ(Spec R, U) ↦ a • t)
        (RingHom.congr_fun hη r)).trans
          (ModuleCat.restrictScalars.smul_def
            (M := S(M, U)) η(R, U) r t).symm
  let ι : M →ₗ[R] T := toOpen M U
  letI : IsLocalizedModule (.powers f) ι := isLocalizedModule_toOpen M f
  exact awayEquivOfIsLocalizedModule R M f (T := T) ι

private lemma awayModuleEquiv_apply_eq_iso {R : CommRingCat.{u}} (M : ModuleCat.{v} R) (f : R)
    (x : LocalizedModule (.powers f) M) :
    (awayModuleEquiv M f).toFun x =
      IsLocalizedModule.iso (.powers f) (toOpen M (basicOpen f)) x := rfl

private lemma awayModuleEquiv_symm_eq_iso_symm {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (f : R) (s : S(M, basicOpen f)) :
    (awayModuleEquiv M f).symm.toFun s =
      (IsLocalizedModule.iso (.powers f) (toOpen M (basicOpen f))).symm s := rfl

private lemma localizedModule_iso_naturality
    {A : Type*} [CommSemiring A]
    {N₀ : Type*} {N₁ : Type*} {N₂ : Type*}
    [AddCommMonoid N₀] [Module A N₀]
    [AddCommMonoid N₁] [Module A N₁]
    [AddCommMonoid N₂] [Module A N₂]
    (S : Submonoid A) (ι₁ : N₀ →ₗ[A] N₁) (ι₂ : N₀ →ₗ[A] N₂)
    [IsLocalizedModule S ι₁] [IsLocalizedModule S ι₂]
    (h : N₁ →ₗ[A] N₂) (hι : h.comp ι₁ = ι₂)
    (x : LocalizedModule S N₀) :
    IsLocalizedModule.iso S ι₂ x = h (IsLocalizedModule.iso S ι₁ x) := by
  subst ι₂
  have hx := LinearMap.congr_fun
    (IsLocalizedModule.linearEquiv_of_isLocalizedModule_comp S ι₁ h)
    (IsLocalizedModule.iso S ι₁ x)
  change IsLocalizedModule.iso S (h.comp ι₁)
      ((IsLocalizedModule.iso S ι₁).symm (IsLocalizedModule.iso S ι₁ x)) =
    h (IsLocalizedModule.iso S ι₁ x) at hx
  simpa only [LinearEquiv.symm_apply_apply] using hx

private noncomputable def specModulesSectionsLinearMap {R : CommRingCat.{u}}
    {F G : (Spec R).Modules} (a : F ⟶ G) (U : (Spec R).Opens) :
    (ModuleCat.restrictScalars η(R, U)).obj (F.val.obj (.op U)) →ₗ[R]
      (modulesSpecToSheaf.obj G).presheaf.obj (.op U) := by
  let : Algebra R Γ(Spec R, U) := ΓAlg(R, U)
  let c : (ModuleCat.restrictScalars η(R, U)).obj (F.val.obj (.op U)) ≅
      (modulesSpecToSheaf.obj F).presheaf.obj (.op U) :=
    ModuleCat.restrictScalarsComp'App
      (Scheme.ΓSpecIso R).inv.hom
      ((Spec R).presheaf.map U.leTop.op).hom
      η(R, U) (by rfl) (F.val.obj (.op U))
  exact (((modulesSpecToSheaf.map a).hom.app (.op U)).hom).comp c.hom.hom

private lemma specModulesSectionsLinearMap_apply {R : CommRingCat.{u}}
    {F G : (Spec R).Modules} (a : F ⟶ G) (U : (Spec R).Opens)
    (s : (ModuleCat.restrictScalars η(R, U)).obj (F.val.obj (.op U))) :
    specModulesSectionsLinearMap a U s = a.val.app (.op U) s := by
  have hc := ModuleCat.restrictScalarsComp'App_hom_apply
    (Scheme.ΓSpecIso R).inv.hom
    ((Spec R).presheaf.map U.leTop.op).hom
    η(R, U) (by rfl) (F.val.obj (.op U)) s
  exact congrArg (((modulesSpecToSheaf.map a).hom.app (.op U)).hom) hc

private noncomputable def isoTildeSectionsLinearMap {R : CommRingCat.{u}}
    (M : ModuleCat.{u} R) (U : (Spec R).Opens) :
    Q(R, M, U) →ₗ[R]
      (modulesSpecToSheaf.obj (AlgebraicGeometry.tilde M)).presheaf.obj (.op U) :=
  specModulesSectionsLinearMap (R := R)
    (F := moduleTilde M) (G := AlgebraicGeometry.tilde M) (isoTilde M).hom U

private lemma isoTildeSectionsLinearMap_apply {R : CommRingCat.{u}}
    (M : ModuleCat.{u} R) (U : (Spec R).Opens) (s : Q(R, M, U)) :
    isoTildeSectionsLinearMap M U s = (isoTilde M).hom.val.app (.op U) s :=
  specModulesSectionsLinearMap_apply (R := R)
    (F := moduleTilde M) (G := AlgebraicGeometry.tilde M) (isoTilde M).hom U s

private lemma isoTildeSectionsLinearMap_comp_toOpen {R : CommRingCat.{u}}
    (M : ModuleCat.{u} R) (U : (Spec R).Opens) :
    (isoTildeSectionsLinearMap M U).comp (toOpen M U) =
      (AlgebraicGeometry.tilde.toOpen M U).hom := by
  apply LinearMap.ext
  intro m
  exact (isoTildeSectionsLinearMap_apply M U (toOpen M U m)).trans
    (isoTilde_toOpen M U m)

/-- On the diagonal, the principal-open comparison agrees with the usual one
under the canonical comparison of associated sheaves. -/
theorem awayModuleEquiv_isoTilde {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (f : R) (x : LocalizedModule (.powers f) M) :
    (_root_.AlgebraicGeometry.Scheme.Modules.awayModuleEquiv R M f).toFun x =
      (isoTilde M).hom.val.app (.op (PrimeSpectrum.basicOpen f))
        ((awayModuleEquiv M f).toFun x) := by
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen f
  let : Algebra R Γ(Spec R, U) := ΓAlg(R, U)
  let cR : Q(R, M, U) →ₗ[R]
      (modulesSpecToSheaf.obj (AlgebraicGeometry.tilde M)).presheaf.obj (.op U) :=
    isoTildeSectionsLinearMap M U
  let hlocal₂ : IsLocalizedModule (.powers f) (AlgebraicGeometry.tilde.toOpen M U).hom :=
    inferInstanceAs
      (IsLocalizedModule (.powers f)
        (AlgebraicGeometry.tilde.toOpen M
          (PrimeSpectrum.basicOpen f : (Spec R).Opens)).hom)
  let hlocal₁ : IsLocalizedModule (.powers f) (toOpen M U) :=
    isLocalizedModule_toOpen M f
  have hnum :
      cR.comp (toOpen M U) = (AlgebraicGeometry.tilde.toOpen M U).hom :=
    isoTildeSectionsLinearMap_comp_toOpen M U
  have hcomparison :
      IsLocalizedModule.iso (.powers f) (AlgebraicGeometry.tilde.toOpen M U).hom x =
        cR (IsLocalizedModule.iso (.powers f) (toOpen M U) x) :=
    @localizedModule_iso_naturality
      R (inferInstanceAs (CommSemiring R))
      M (Q(R, M, U))
      ((modulesSpecToSheaf.obj (AlgebraicGeometry.tilde M)).presheaf.obj (.op U))
      (ModuleCat.isAddCommGroup M).toAddCommMonoid (ModuleCat.isModule M)
      (ModuleCat.isAddCommGroup (Q(R, M, U))).toAddCommMonoid
      (ModuleCat.isModule (Q(R, M, U)))
      (ModuleCat.isAddCommGroup
        ((modulesSpecToSheaf.obj (AlgebraicGeometry.tilde M)).presheaf.obj
          (.op U))).toAddCommMonoid
      (ModuleCat.isModule
        ((modulesSpecToSheaf.obj (AlgebraicGeometry.tilde M)).presheaf.obj
          (.op U)))
      (.powers f) (toOpen M U) (AlgebraicGeometry.tilde.toOpen M U).hom
      hlocal₁ hlocal₂ cR hnum x
  exact (tilde_awayModuleEquiv_apply_eq_iso R M f x).trans
    (hcomparison.trans
      ((isoTildeSectionsLinearMap_apply M U _).trans
        (congrArg ((isoTilde M).hom.val.app (.op U))
          (awayModuleEquiv_apply_eq_iso M f x).symm)))

/-- The inverse principal-open comparison also agrees under the diagonal
comparison of associated sheaves. -/
theorem awayModuleEquiv_symm_isoTilde {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (f : R) (s : (moduleTilde M).val.obj (.op (PrimeSpectrum.basicOpen f))) :
    (_root_.AlgebraicGeometry.Scheme.Modules.awayModuleEquiv R M f).symm.toFun
        ((isoTilde M).hom.val.app (.op (PrimeSpectrum.basicOpen f)) s) =
      (awayModuleEquiv M f).symm.toFun s := by
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen f
  let Eold := _root_.AlgebraicGeometry.Scheme.Modules.awayModuleEquiv R M f
  let Enew := awayModuleEquiv M f
  let c := fun t : (moduleTilde M).val.obj (.op U) ↦
    (isoTilde M).hom.val.app (.op U) t
  change Eold.symm.toFun (c s) = Enew.symm.toFun s
  exact Eold.injective <|
    (Eold.apply_symm_apply (c s)).trans
      (((congrArg c (Enew.apply_symm_apply s)).symm).trans
        (awayModuleEquiv_isoTilde M f (Enew.symm.toFun s)).symm)

/-- The comparison sends a localized numerator to its numerator section. -/
theorem awayModuleEquiv_mk {R : CommRingCat.{u}} (M : ModuleCat.{v} R) (f : R) (m : M) :
    (awayModuleEquiv M f).toFun (LocalizedModule.mk m 1) = toOpen M (basicOpen f) m := by
  exact IsLocalizedModule.iso_mk_one (.powers f) (toOpen M (basicOpen f)) m

/-- Fractions have the same numerator and denominator under the comparison. -/
theorem awayModuleEquiv_fraction {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (f : R) (m : M) (s : Submonoid.powers f) :
    (awayModuleEquiv M f).toFun (LocalizedModule.mk m s) =
      fraction M (basicOpen f) m s (by
        obtain ⟨_, n, rfl⟩ := s
        exact PrimeSpectrum.le_basicOpen_pow f n) :=
  iso_fraction M f m s

/-- The inverse comparison recovers the displayed fraction. -/
theorem awayModuleEquiv_symm_fraction {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (f : R) (m : M) (s : Submonoid.powers f) :
    (awayModuleEquiv M f).symm.toFun
      (fraction M (basicOpen f) m s (by
        obtain ⟨_, n, rfl⟩ := s
        exact PrimeSpectrum.le_basicOpen_pow f n)) =
      LocalizedModule.mk m s := by
  rw [← awayModuleEquiv_fraction M f m s]
  exact (awayModuleEquiv M f).symm_apply_apply _

/-- A section is the specified fraction exactly when its denominator clears. -/
theorem awayModuleEquiv_symm_apply_iff {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    (f : R) (t : S(M, basicOpen f))
    (m : M) (s : Submonoid.powers f) :
    (awayModuleEquiv M f).symm.toFun t = LocalizedModule.mk m s ↔
      ((S(M, basicOpen f)).smul
        ((@algebraMap (CommRingCat.carrier R)
          (CommRingCat.carrier (Γ(Spec R, basicOpen f) : CommRingCat.{u})) _ _
          ΓAlg(R, basicOpen f)) (s : R))).hom t =
        toOpen M (basicOpen f) m := by
  have hη :
      (@algebraMap (CommRingCat.carrier R)
        (CommRingCat.carrier (Γ(Spec R, basicOpen f) : CommRingCat.{u})) _ _
        ΓAlg(R, basicOpen f)) = η(R, basicOpen f) :=
    AlgebraicGeometry.IsAffineOpen.algebraMap_Spec_obj
      (R := R) (U := basicOpen f)
  have hscalar :
      AddCommGrpCat.Hom.hom
        ((S(M, basicOpen f)).smul
          ((@algebraMap (CommRingCat.carrier R)
            (CommRingCat.carrier (Γ(Spec R, basicOpen f) : CommRingCat.{u})) _ _
            ΓAlg(R, basicOpen f)) (s : R))) t =
        AddCommGrpCat.Hom.hom
          ((S(M, basicOpen f)).smul (η(R, basicOpen f) (s : R))) t :=
    congrArg
      (fun a : Γ(Spec R, (basicOpen f : (Spec R).Opens)) ↦
        AddCommGrpCat.Hom.hom ((S(M, basicOpen f)).smul a) t)
      (RingHom.congr_fun hη (s : R))
  constructor
  · intro h
    have h' :
        (IsLocalizedModule.iso (.powers f) (toOpen M (basicOpen f))).symm t =
          LocalizedModule.mk m s :=
      (awayModuleEquiv_symm_eq_iso_symm M f t).symm.trans h
    exact hscalar.trans ((iso_symm_apply_iff M f t m s).mp h')
  · intro h
    have h' :
        AddCommGrpCat.Hom.hom
          ((S(M, basicOpen f)).smul (η(R, basicOpen f) (s : R))) t =
            toOpen M (basicOpen f) m :=
      hscalar.symm.trans h
    exact (awayModuleEquiv_symm_eq_iso_symm M f t).trans
      ((iso_symm_apply_iff M f t m s).mpr h')

private lemma raw_restriction_units {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    {f g : R} (h : basicOpen g ≤ basicOpen f) :
    ∀ s : Submonoid.powers f,
      IsUnit (algebraMap R (Module.End R (LocalizedModule (.powers g) M)) s) := by
  have hf : IsUnit (algebraMap R (Localization.Away g) f) :=
    (PrimeSpectrum.basicOpen_le_basicOpen_iff_algebraMap_isUnit
      (S := Localization.Away g)).mp h
  have hfe : IsUnit (algebraMap R
      (Module.End R (LocalizedModule (.powers g) M)) f) := by
    have h := hf.map (algebraMap (Localization.Away g)
      (Module.End (Localization.Away g) (LocalizedModule (.powers g) M)))
    rw [Module.End.isUnit_iff] at h ⊢
    have hfun :
        (algebraMap R (Module.End R (LocalizedModule (.powers g) M)) f :
          LocalizedModule (.powers g) M → LocalizedModule (.powers g) M) =
        (algebraMap (Localization.Away g)
          (Module.End (Localization.Away g) (LocalizedModule (.powers g) M))
          (algebraMap R (Localization.Away g) f) :
          LocalizedModule (.powers g) M → LocalizedModule (.powers g) M) := by
      funext x
      induction x using LocalizedModule.induction_on with
      | h m t =>
        change f • LocalizedModule.mk m t =
          algebraMap R (Localization.Away g) f • LocalizedModule.mk m t
        rw [← Localization.mk_one_eq_algebraMap (M := .powers g) f,
          LocalizedModule.mk_smul_mk, LocalizedModule.smul'_mk, one_mul]
    rw [hfun]
    exact h
  rintro ⟨_, n, rfl⟩
  simpa only [map_pow] using hfe.pow n

/-- The canonical localization map associated to an arbitrary inclusion of principal opens.
It is the `R`-linear localization lift preserving numerators. -/
@[no_expose]
def localizationTransition {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    {f g : R} (h : basicOpen g ≤ basicOpen f) :
    LocalizedModule (.powers f) M →ₗ[R] LocalizedModule (.powers g) M :=
  IsLocalizedModule.lift (.powers f) (LocalizedModule.mkLinearMap (.powers f) M)
    (LocalizedModule.mkLinearMap (.powers g) M) (raw_restriction_units M h)

/-- The transition between localizations preserves numerators. -/
@[simp]
theorem localizationTransition_mk_one {R : CommRingCat.{u}} (M : ModuleCat.{v} R) {f g : R}
    (h : basicOpen g ≤ basicOpen f) (m : M) :
    localizationTransition M h (LocalizedModule.mk m 1) = LocalizedModule.mk m 1 := by
  exact IsLocalizedModule.lift_apply (.powers f)
    (LocalizedModule.mkLinearMap (.powers f) M)
    (LocalizedModule.mkLinearMap (.powers g) M) (raw_restriction_units M h) m

/-- The transition associated to an identity inclusion is the identity. -/
@[simp]
theorem localizationTransition_id {R : CommRingCat.{u}} (M : ModuleCat.{v} R) (f : R) :
    localizationTransition M (le_rfl : basicOpen f ≤ basicOpen f) = LinearMap.id := by
  apply IsLocalizedModule.ext (.powers f) (LocalizedModule.mkLinearMap (.powers f) M)
    (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap (.powers f) M))
  ext m
  simp only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply,
    localizationTransition_mk_one, LinearMap.id_apply]

/-- Successive localization transitions compose in restriction order. -/
theorem localizationTransition_comp {R : CommRingCat.{u}} (M : ModuleCat.{v} R) {f g k : R}
    (hgf : basicOpen g ≤ basicOpen f) (hkg : basicOpen k ≤ basicOpen g) :
    (localizationTransition M hkg).comp (localizationTransition M hgf) =
      localizationTransition M (hkg.trans hgf) := by
  apply IsLocalizedModule.ext (.powers f) (LocalizedModule.mkLinearMap (.powers f) M)
    (raw_restriction_units M (hkg.trans hgf))
  ext m
  simp only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply,
    localizationTransition_mk_one]

private lemma iso_restrict {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    {f g : R} (h : basicOpen g ≤ basicOpen f)
    (x : LocalizedModule (.powers f) M) :
    res(M, h) (IsLocalizedModule.iso (.powers f) (toOpen M (basicOpen f)) x) =
      IsLocalizedModule.iso (.powers g) (toOpen M (basicOpen g))
        (localizationTransition M h x) := by
  have he : (restrictLinear M h).comp
        (IsLocalizedModule.iso (.powers f) (toOpen M (basicOpen f))).toLinearMap =
      (IsLocalizedModule.iso (.powers g) (toOpen M (basicOpen g))).toLinearMap.comp
        (localizationTransition M h) :=
    IsLocalizedModule.ext (.powers f)
      (LocalizedModule.mkLinearMap (.powers f) M) (powers_scalarEnd_isUnit M f h)
      (LinearMap.ext fun m ↦
        ((congrArg (fun t : S(M, basicOpen f) ↦ res(M, h) t)
          (IsLocalizedModule.iso_mk_one (.powers f) (toOpen M (basicOpen f)) m)).trans
          (toOpen_res M h m)).trans
            (((congrArg (fun y : LocalizedModule (.powers g) M ↦
              IsLocalizedModule.iso (.powers g) (toOpen M (basicOpen g)) y)
              (localizationTransition_mk_one M h m)).trans
              (IsLocalizedModule.iso_mk_one (.powers g) (toOpen M (basicOpen g)) m)).symm))
  exact LinearMap.congr_fun he x

/-- Restriction along any inclusion of principal opens is the localization lift. -/
theorem awayModuleEquiv_restrict {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    {f g : R} (h : basicOpen g ≤ basicOpen f)
    (x : LocalizedModule (.powers f) M) :
    res(M, h) ((awayModuleEquiv M f).toFun x) =
      (awayModuleEquiv M g).toFun (localizationTransition M h x) := by
  exact (congrArg (fun t : S(M, basicOpen f) ↦ res(M, h) t)
    (awayModuleEquiv_apply_eq_iso M f x)).trans
      ((iso_restrict M h x).trans
        (awayModuleEquiv_apply_eq_iso M g (localizationTransition M h x)).symm)

/-- The inverse comparison commutes with restriction along any principal inclusion. -/
theorem awayModuleEquiv_symm_restrict {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    {f g : R} (h : basicOpen g ≤ basicOpen f)
    (t : S(M, basicOpen f)) :
    (awayModuleEquiv M g).symm.toFun (res(M, h) t) =
      localizationTransition M h ((awayModuleEquiv M f).symm.toFun t) := by
  let Ef := IsLocalizedModule.iso (.powers f) (toOpen M (basicOpen f))
  let Eg := IsLocalizedModule.iso (.powers g) (toOpen M (basicOpen g))
  have hsymm : Eg.symm (res(M, h) t) = localizationTransition M h (Ef.symm t) :=
    Eg.injective ((Eg.apply_symm_apply (res(M, h) t)).trans
      ((congrArg (fun z : S(M, basicOpen f) ↦ res(M, h) z)
        (Ef.apply_symm_apply t)).symm.trans
          (iso_restrict M h (Ef.symm t))))
  exact (awayModuleEquiv_symm_eq_iso_symm M g (res(M, h) t)).trans
    (hsymm.trans (congrArg (localizationTransition M h)
      (awayModuleEquiv_symm_eq_iso_symm M f t).symm))

/-- In scalar coordinates the localization transition is semilinear for the original
structure-sheaf restriction. -/
theorem localizationTransition_smul {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    {f g : R} (h : basicOpen g ≤ basicOpen f)
    (a : Localization.Away f) (x : LocalizedModule (.powers f) M) :
    localizationTransition M h (a • x) =
      ((ΓAwayRing(R, g)).symm.toRingHom.comp
        (((Spec R).presheaf.map (homOfLE h).op).hom.comp
          (ΓAwayRing(R, f)).toRingHom)) a •
        localizationTransition M h x := by
  let : Module Γ(Spec R, (basicOpen f : (Spec R).Opens))
      S(M, basicOpen f) := (S(M, basicOpen f)).isModule
  let : Module Γ(Spec R, (basicOpen g : (Spec R).Opens))
      S(M, basicOpen g) := (S(M, basicOpen g)).isModule
  let αf := ΓAwayRing(R, f)
  let αg := ΓAwayRing(R, g)
  let ρ : Γ(Spec R, (basicOpen f : (Spec R).Opens)) →+*
      Γ(Spec R, (basicOpen g : (Spec R).Opens)) :=
    ((Spec R).presheaf.map (homOfLE h).op).hom
  let β := αg.symm.toRingHom.comp (ρ.comp αf.toRingHom)
  change localizationTransition M h (a • x) = β a • localizationTransition M h x
  have hb : αg (β a) = ρ (αf a) := αg.apply_symm_apply _
  have ha : (awayModuleEquiv M f).toFun (a • x) =
      AddCommGrpCat.Hom.hom ((S(M, basicOpen f)).smul (αf a))
        ((awayModuleEquiv M f).toFun x) :=
    (awayModuleEquiv M f).map_smul' a x
  have hres : res(M, h)
      (AddCommGrpCat.Hom.hom ((S(M, basicOpen f)).smul (αf a))
        ((awayModuleEquiv M f).toFun x)) =
      AddCommGrpCat.Hom.hom ((S(M, basicOpen g)).smul (ρ (αf a)))
        (res(M, h) ((awayModuleEquiv M f).toFun x)) :=
    (res(M, h)).map_smulₛₗ (αf a) ((awayModuleEquiv M f).toFun x)
  apply (awayModuleEquiv M g).injective
  calc
    (awayModuleEquiv M g).toFun (localizationTransition M h (a • x)) =
        res(M, h) ((awayModuleEquiv M f).toFun (a • x)) :=
      (awayModuleEquiv_restrict M h _).symm
    _ = res(M, h)
        (AddCommGrpCat.Hom.hom ((S(M, basicOpen f)).smul (αf a))
          ((awayModuleEquiv M f).toFun x)) :=
      congrArg (fun t : S(M, basicOpen f) ↦ res(M, h) t) ha
    _ = AddCommGrpCat.Hom.hom ((S(M, basicOpen g)).smul (ρ (αf a)))
        (res(M, h) ((awayModuleEquiv M f).toFun x)) := hres
    _ = AddCommGrpCat.Hom.hom ((S(M, basicOpen g)).smul (αg (β a)))
        ((awayModuleEquiv M g).toFun (localizationTransition M h x)) :=
      congrArg₂ (fun (b : Γ(Spec R, (basicOpen g : (Spec R).Opens)))
        (t : S(M, basicOpen g)) ↦
          AddCommGrpCat.Hom.hom ((S(M, basicOpen g)).smul b) t)
        hb.symm (awayModuleEquiv_restrict M h x)
    _ = (awayModuleEquiv M g).toFun (β a • localizationTransition M h x) :=
      ((awayModuleEquiv M g).map_smul' _ _).symm

private def mapLinear {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    {N : ModuleCat.{v} R} (a : M ⟶ N) (U : (Spec R).Opens) :
    Q(R, M, U) →ₗ[R] Q(R, N, U) :=
  ((ModuleCat.restrictScalars η(R, U)).map
    ((map a).val.app (.op U))).hom

/-- The localization comparison is natural in maps of the original modules. -/
theorem awayModuleEquiv_map {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    {N : ModuleCat.{v} R} (a : M ⟶ N) (f : R)
    (x : LocalizedModule (.powers f) M) :
    (map a).val.app (.op (basicOpen f)) ((awayModuleEquiv M f).toFun x) =
      (awayModuleEquiv N f).toFun
        (IsLocalizedModule.map (.powers f)
          (LocalizedModule.mkLinearMap (.powers f) M)
          (LocalizedModule.mkLinearMap (.powers f) N) a.hom x) := by
  have he : (mapLinear M a (basicOpen f)).comp
        (IsLocalizedModule.iso (.powers f) (toOpen M (basicOpen f))).toLinearMap =
      (IsLocalizedModule.iso (.powers f) (toOpen N (basicOpen f))).toLinearMap.comp
        (IsLocalizedModule.map (.powers f)
          (LocalizedModule.mkLinearMap (.powers f) M)
          (LocalizedModule.mkLinearMap (.powers f) N) a.hom) :=
    IsLocalizedModule.ext (.powers f)
      (LocalizedModule.mkLinearMap (.powers f) M)
      (IsLocalizedModule.map_units (toOpen N (basicOpen f)))
      (LinearMap.ext fun m ↦
        ((congrArg (fun t : S(M, basicOpen f) ↦
          (map a).val.app (.op (basicOpen f)) t)
          (IsLocalizedModule.iso_mk_one (.powers f) (toOpen M (basicOpen f)) m)).trans
          (toOpen_map_app a (basicOpen f) m)).trans
            (((congrArg (fun y : LocalizedModule (.powers f) N ↦
              IsLocalizedModule.iso (.powers f) (toOpen N (basicOpen f)) y)
              (IsLocalizedModule.map_apply (.powers f)
                (LocalizedModule.mkLinearMap (.powers f) M)
                (LocalizedModule.mkLinearMap (.powers f) N) a.hom m)).trans
              (IsLocalizedModule.iso_mk_one (.powers f) (toOpen N (basicOpen f))
                (a.hom m))).symm))
  exact (congrArg (fun t : S(M, basicOpen f) ↦
    (map a).val.app (.op (basicOpen f)) t)
    (awayModuleEquiv_apply_eq_iso M f x)).trans
      ((LinearMap.congr_fun he x).trans
        (awayModuleEquiv_apply_eq_iso N f
          (IsLocalizedModule.map (.powers f)
            (LocalizedModule.mkLinearMap (.powers f) M)
            (LocalizedModule.mkLinearMap (.powers f) N) a.hom x)).symm)

/-- The inverse localization comparison is natural in module maps. -/
theorem awayModuleEquiv_symm_map {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    {N : ModuleCat.{v} R} (a : M ⟶ N) (f : R)
    (s : S(M, basicOpen f)) :
    (awayModuleEquiv N f).symm.toFun ((map a).val.app (.op (basicOpen f)) s) =
      IsLocalizedModule.map (.powers f)
        (LocalizedModule.mkLinearMap (.powers f) M)
        (LocalizedModule.mkLinearMap (.powers f) N) a.hom
        ((awayModuleEquiv M f).symm.toFun s) := by
  let EM := IsLocalizedModule.iso (.powers f) (toOpen M (basicOpen f))
  let EN := IsLocalizedModule.iso (.powers f) (toOpen N (basicOpen f))
  let L := IsLocalizedModule.map (.powers f)
    (LocalizedModule.mkLinearMap (.powers f) M)
    (LocalizedModule.mkLinearMap (.powers f) N) a.hom
  have hforward (x : LocalizedModule (.powers f) M) :
      (map a).val.app (.op (basicOpen f)) (EM x) = EN (L x) :=
    (congrArg (fun t : S(M, basicOpen f) ↦
      (map a).val.app (.op (basicOpen f)) t)
      (awayModuleEquiv_apply_eq_iso M f x)).symm.trans
        ((awayModuleEquiv_map M a f x).trans
          (awayModuleEquiv_apply_eq_iso N f (L x)))
  have hsymm : EN.symm ((map a).val.app (.op (basicOpen f)) s) = L (EM.symm s) :=
    EN.injective ((EN.apply_symm_apply
      ((map a).val.app (.op (basicOpen f)) s)).trans
        ((congrArg (fun t : S(M, basicOpen f) ↦
          (map a).val.app (.op (basicOpen f)) t)
          (EM.apply_symm_apply s)).symm.trans
            (hforward (EM.symm s))))
  exact (awayModuleEquiv_symm_eq_iso_symm N f
    ((map a).val.app (.op (basicOpen f)) s)).trans
      (hsymm.trans (congrArg L (awayModuleEquiv_symm_eq_iso_symm M f s).symm))

/-- The top equivalence is natural in morphisms of the original modules. -/
theorem topLinearEquiv_naturality {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    {N : ModuleCat.{v} R} (a : M ⟶ N) (m : M) :
    (map a).val.app (.op ⊤) (topLinearEquiv M m) = topLinearEquiv N (a.hom m) := by
  rw [topLinearEquiv_apply, topLinearEquiv_apply]
  exact toOpen_map_app a ⊤ m

/-- The inverse top equivalence is natural in morphisms of the original modules. -/
theorem topLinearEquiv_symm_naturality {R : CommRingCat.{u}} (M : ModuleCat.{v} R)
    {N : ModuleCat.{v} R} (a : M ⟶ N)
    (s : S(M, ⊤)) :
    (topLinearEquiv N).symm ((map a).val.app (.op ⊤) s) =
      a.hom ((topLinearEquiv M).symm s) := by
  have h := topLinearEquiv_naturality M a ((topLinearEquiv M).symm s)
  exact (congrArg (fun t : S(M, ⊤) ↦
    (topLinearEquiv N).symm ((map a).val.app (.op ⊤) t))
    ((topLinearEquiv M).apply_symm_apply s)).symm.trans
      ((congrArg (fun t : S(N, ⊤) ↦ (topLinearEquiv N).symm t) h).trans
        ((topLinearEquiv N).symm_apply_apply (a.hom ((topLinearEquiv M).symm s))))

/-- A map of coefficient modules preserves every fraction on an open where its
specified denominator is invertible, changing only the numerator. -/
@[simp]
theorem map_fraction {R : CommRingCat.{u}} {M N : ModuleCat.{v} R}
    (a : M ⟶ N) (U : (Spec R).Opens) (m : M) (r : R)
    (hr : U ≤ basicOpen r) :
    (map a).val.app (op U) (fraction M U m r hr) =
      fraction N U (a.hom m) r hr := by
  let F : Q(R, M, U) →ₗ[R] Q(R, N, U) := mapLinear M a U
  let c : Module.End R Q(R, N, U) :=
    algebraMap R (Module.End R Q(R, N, U)) r
  have hc : Function.Injective c :=
    ((Module.End.isUnit_iff c).mp (scalarEnd_isUnit_of_le_basicOpen N r hr)).1
  apply hc
  change c (F (fraction M U m r hr)) =
    c (fraction N U (a.hom m) r hr)
  have hM := smul_fraction_restrictScalars M U m r hr
  have hN := smul_fraction_restrictScalars N U (a.hom m) r hr
  exact ((F.map_smul r _).symm.trans (congrArg F hM)).trans
    ((toOpen_map_app a U m).trans hN.symm)

/-- Evaluation of the associated-sheaf map at any prime is the canonical map
between the localizations of the original coefficient modules at that prime. -/
@[simp]
theorem map_eval {R : CommRingCat.{u}} {M N : ModuleCat.{v} R}
    (a : M ⟶ N) (U : (Spec R).Opens) (p : U)
    (s : (moduleTilde M).val.obj (op U)) :
    eval N U p ((map a).val.app (op U) s) =
      IsLocalizedModule.map (p.1.asIdeal.primeCompl (hp := p.1.isPrime))
        (LocalizedModule.mkLinearMap
          (p.1.asIdeal.primeCompl (hp := p.1.isPrime)) M)
        (LocalizedModule.mkLinearMap
          (p.1.asIdeal.primeCompl (hp := p.1.isPrime)) N)
        a.hom (eval M U p s) := by
  obtain ⟨f, hpf, hfU, m, hs⟩ := exists_fraction M U s p
  let q : (basicOpen f : (Spec R).Opens) := ⟨p.1, hpf⟩
  let P : Submonoid R := p.1.asIdeal.primeCompl (hp := p.1.isPrime)
  let d : P := ⟨f, hpf⟩
  let L : LocalizedModule P M →ₗ[R] LocalizedModule P N :=
    IsLocalizedModule.map P (LocalizedModule.mkLinearMap P M)
      (LocalizedModule.mkLinearMap P N) a.hom
  have hs_eval : eval M U p s = LocalizedModule.mk m d :=
    (eval_res M hfU s q).symm.trans
      ((congrArg (eval M (basicOpen f : (Spec R).Opens) q) hs).trans
        (eval_fraction M (basicOpen f : (Spec R).Opens) m f le_rfl q))
  have hmap : (moduleTilde N).val.restrictₛₗ (homOfLE hfU).op
      ((map a).val.app (op U) s) =
      fraction N (basicOpen f : (Spec R).Opens) (a.hom m) f le_rfl :=
    (PresheafOfModules.naturality_apply (map a).val (homOfLE hfU).op s).symm.trans
      ((congrArg (fun t : S(M, basicOpen f) ↦
        (map a).val.app (op (basicOpen f : (Spec R).Opens)) t) hs).trans
          (map_fraction a (basicOpen f : (Spec R).Opens) m f le_rfl))
  have hleft : eval N U p ((map a).val.app (op U) s) =
      LocalizedModule.mk (a.hom m) d :=
    (eval_res N hfU ((map a).val.app (op U) s) q).symm.trans
      ((congrArg (eval N (basicOpen f : (Spec R).Opens) q) hmap).trans
        (eval_fraction N (basicOpen f : (Spec R).Opens) (a.hom m) f le_rfl q))
  have hright : L (eval M U p s) = LocalizedModule.mk (a.hom m) d :=
    (congrArg L hs_eval).trans
      (IsLocalizedModule.map_LocalizedModules P a.hom m d)
  exact hleft.trans hright.symm

end Sections

end moduleTilde

end AlgebraicGeometry
