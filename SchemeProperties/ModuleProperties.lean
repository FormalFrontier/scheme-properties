/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.Torsion
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Topology.Sheaves.Abelian

public section

set_option warningAsError true

/-!
# Torsion-free and generically vanishing scheme modules

This file defines two stalkwise properties of modules on a scheme:
torsion-freeness at every point and vanishing at every component generic point.
They do not require quasicoherence, reducedness, or finiteness hypotheses.

For a module associated to a module over an integral domain, generic vanishing
is identified with torsion and with vanishing after fraction-ring base change.
-/

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicGeometry
open TensorProduct
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} {M N : X.Modules}

/-- The stalk of a module on a scheme is a module over the scheme's stalk. -/
noncomputable instance stalkModule (P : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (P.presheaf.stalk x) :=
  _root_.PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    P.val x

private lemma germ_smul (P : X.Modules) (x : X) (U : X.Opens) (hxU : x ∈ U)
    (r : Γ(X, U)) (m : Γ(P, U)) :
    P.presheaf.germ U x hxU (r • m) =
      X.presheaf.germ U x hxU r • P.presheaf.germ U x hxU m := by
  exact P.val.germ_smul x U hxU r m

private noncomputable def Hom.stalkAddHom (f : M ⟶ N) (x : X) :
    M.presheaf.stalk x →+ N.presheaf.stalk x :=
  ((TopCat.Presheaf.stalkFunctor Ab x).map f.mapPresheaf).hom

@[simp]
private lemma Hom.stalkAddHom_apply_germ (f : M ⟶ N) (x : X)
    (U : X.Opens) (hxU : x ∈ U) (m : Γ(M, U)) :
    f.stalkAddHom x (M.presheaf.germ U x hxU m) =
      N.presheaf.germ U x hxU (f.app U m) := by
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU f.mapPresheaf m

private noncomputable def Hom.stalk (f : M ⟶ N) (x : X) :
    M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N.presheaf.stalk x where
  toFun := f.stalkAddHom x
  map_add' := map_add _
  map_smul' r m := by
    obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨V, hVU, hxV, m, rfl⟩ := M.presheaf.exists_le_germ_eq m hxU
    rw [← X.presheaf.germ_res_apply (homOfLE hVU) x hxV r]
    rw [← germ_smul M x V hxV]
    rw [Hom.stalkAddHom_apply_germ, Hom.app_smul]
    rw [germ_smul N]
    rw [Hom.stalkAddHom_apply_germ]
    simp

private lemma Hom.stalk_injective (f : M ⟶ N) [IsIso f] (x : X) :
    Function.Injective (f.stalk x) := by
  let _ : IsIso f.mapPresheaf := by
    change IsIso ((toPresheaf X).map f)
    infer_instance
  let _ : IsIso ((TopCat.Presheaf.stalkFunctor Ab x).map f.mapPresheaf) :=
    Functor.map_isIso _ _
  change Function.Injective ((TopCat.Presheaf.stalkFunctor Ab x).map f.mapPresheaf)
  exact (ConcreteCategory.bijective_of_isIso _).1

/-- A module on a scheme is torsion-free if each stalk is torsion-free over the
corresponding stalk of the structure sheaf. -/
class IsTorsionFree (P : X.Modules) : Prop where
  stalk (x : X) : Module.IsTorsionFree (X.presheaf.stalk x) (P.presheaf.stalk x)

attribute [instance] IsTorsionFree.stalk

/-- Torsion-freeness is preserved by isomorphisms of modules on a scheme. -/
theorem IsTorsionFree.ofIso {P Q : X.Modules} (e : P ≅ Q)
    (hP : IsTorsionFree P) : IsTorsionFree Q where
  stalk x := by
    let _ : Module.IsTorsionFree (X.presheaf.stalk x) (P.presheaf.stalk x) :=
      hP.stalk x
    apply Function.Injective.moduleIsTorsionFree (e.inv.stalk x)
      (e.inv.stalk_injective x)
    exact (e.inv.stalk x).map_smul

/-- Isomorphic modules on a scheme are simultaneously torsion-free. -/
theorem isTorsionFree_iff_of_iso {P Q : X.Modules} (e : P ≅ Q) :
    IsTorsionFree P ↔ IsTorsionFree Q :=
  ⟨IsTorsionFree.ofIso e, IsTorsionFree.ofIso e.symm⟩

/-- A module on a scheme vanishes at generic points if its stalk is zero at the
generic point of every irreducible component. -/
class VanishesAtGenericPoints (P : X.Modules) : Prop where
  stalk (x : genericPoints X) : Subsingleton (P.presheaf.stalk x.1)

attribute [instance] VanishesAtGenericPoints.stalk

/-- Vanishing at generic points is preserved by isomorphisms of modules. -/
theorem VanishesAtGenericPoints.ofIso {P Q : X.Modules} (e : P ≅ Q)
    (hP : VanishesAtGenericPoints P) : VanishesAtGenericPoints Q where
  stalk x := by
    let _ : Subsingleton (P.presheaf.stalk x.1) := hP.stalk x
    exact (e.inv.stalk_injective x).subsingleton

/-- Isomorphic modules simultaneously vanish at all component generic points. -/
theorem vanishesAtGenericPoints_iff_of_iso {P Q : X.Modules} (e : P ≅ Q) :
    VanishesAtGenericPoints P ↔ VanishesAtGenericPoints Q :=
  ⟨VanishesAtGenericPoints.ofIso e,
    VanishesAtGenericPoints.ofIso e.symm⟩

/-- Generic-point vanishing can equivalently be indexed by irreducible
components. -/
theorem vanishesAtGenericPoints_iff_irreducibleComponents (P : X.Modules) :
    VanishesAtGenericPoints P ↔
      ∀ Z : irreducibleComponents X,
        Subsingleton (P.presheaf.stalk (genericPoints.ofComponent Z).1) := by
  constructor
  · intro h Z
    exact h.stalk (genericPoints.ofComponent Z)
  · intro h
    refine ⟨fun x ↦ ?_⟩
    simpa only [genericPoints.ofComponent_component] using
      h (genericPoints.component x)

/-- Every module on an empty scheme is torsion-free. -/
instance (priority := low) empty_isTorsionFree [IsEmpty X] (P : X.Modules) :
    IsTorsionFree P where
  stalk x := isEmptyElim x

/-- Every module on an empty scheme vanishes at all generic points. -/
instance (priority := low) empty_vanishesAtGenericPoints [IsEmpty X]
    (P : X.Modules) : VanishesAtGenericPoints P where
  stalk x := isEmptyElim x.1

/-- Every stalk of the zero module on a scheme is zero. -/
noncomputable instance zeroStalkSubsingleton (x : X) :
    Subsingleton ((0 : X.Modules).presheaf.stalk x) := by
  have h₀ : IsZero ((toPresheaf X).obj (0 : X.Modules)) :=
    (toPresheaf X).map_isZero (isZero_zero X.Modules)
  have h₁ : IsZero
      ((TopCat.Presheaf.stalkFunctor Ab x).obj
        ((toPresheaf X).obj (0 : X.Modules))) :=
    (TopCat.Presheaf.stalkFunctor Ab x).map_isZero h₀
  exact _root_.AddCommGrpCat.subsingleton_of_isZero h₁

/-- The zero module on a scheme is torsion-free. -/
noncomputable instance zeroIsTorsionFree : IsTorsionFree (0 : X.Modules) where
  stalk _ := inferInstance

/-- The zero module on a scheme vanishes at every component generic point. -/
noncomputable instance zeroVanishesAtGenericPoints :
    VanishesAtGenericPoints (0 : X.Modules) where
  stalk _ := inferInstance

/-- For a module over an integral domain, its associated module on the affine
spectrum vanishes at the generic point exactly when the original module is
torsion. -/
theorem tilde_vanishesAtGenericPoints_iff_isTorsion
    {R : CommRingCat.{u}} [IsDomain R] (P : ModuleCat R) :
    VanishesAtGenericPoints (tilde P) ↔ Module.IsTorsion R P := by
  have hgeneric :
      VanishesAtGenericPoints (tilde P) ↔
        Subsingleton ((tilde P).presheaf.stalk (genericPoint (Spec R))) := by
    constructor
    · intro h
      exact h.stalk ⟨genericPoint (Spec R), by rw [genericPoints_eq_singleton]; rfl⟩
    · intro h
      refine ⟨fun x ↦ ?_⟩
      obtain ⟨x, hx⟩ := x
      rw [genericPoints_eq_singleton] at hx
      simpa only [Set.mem_singleton_iff] using hx ▸ h
  let _ : Module R ((tilde P).presheaf.stalk (genericPoint (Spec R))) :=
    tilde.instModuleCarrierCarrierStalkAbPresheaf P (genericPoint (Spec R))
  rw [hgeneric]
  let _ : (genericPoint (Spec R)).asIdeal.IsPrime :=
    (genericPoint (Spec R)).isPrime
  have hS : (genericPoint (Spec R)).asIdeal.primeCompl = nonZeroDivisors R := by
    have hbot : (genericPoint (Spec R)).asIdeal = (⊥ : Ideal R) := by
      simp [genericPoint_eq_bot_of_affine R]
    ext r
    simp only [Ideal.mem_primeCompl_iff, hbot, Ideal.mem_bot,
      mem_nonZeroDivisors_iff_ne_zero]
  let _ : IsLocalizedModule (genericPoint (Spec R)).asIdeal.primeCompl
      (tilde.toStalk P (genericPoint (Spec R))).hom :=
    tilde.instIsLocalizedModuleCarrierCarrierOfCarrierStalkAbPresheafPrimeComplAsIdealHomToStalk
      P (genericPoint (Spec R))
  rw [IsLocalizedModule.subsingleton_iff
    (genericPoint (Spec R)).asIdeal.primeCompl
    (tilde.toStalk P (genericPoint (Spec R))).hom]
  rw [hS]
  constructor
  · intro h m
    obtain ⟨r, hr, hm⟩ := h m
    exact ⟨⟨r, hr⟩, hm⟩
  · intro h m
    obtain ⟨r, hr⟩ := h (x := m)
    exact ⟨r, r.property, hr⟩

/-- For a module over an integral domain, its associated module on the affine
spectrum vanishes at the generic point exactly when its fraction-ring base
change is zero. -/
theorem tilde_vanishesAtGenericPoints_iff_subsingleton_fractionRing_tensorProduct
    {R : CommRingCat.{u}} [IsDomain R] (P : ModuleCat R) :
    VanishesAtGenericPoints (tilde P) ↔
      Subsingleton (FractionRing R ⊗[R] P) :=
  (tilde_vanishesAtGenericPoints_iff_isTorsion P).trans
    Module.isTorsion_iff_subsingleton_fractionRing_tensorProduct

end AlgebraicGeometry.Scheme.Modules
