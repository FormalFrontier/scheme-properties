/-
Copyright (c) 2024 Weihong Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors of the adapted mathlib affine-cover construction: Kevin Buzzard, Johan Commelin,
  Amelia Livingston, Sophie Morel, Jujian Zhang, Weihong Xu, Andrew Yang, Brian Nugent.
Finite-witness refinement: Prism, 2026. Native API adaptation: Worker B, 2026.
-/
module

public import SchemeProperties.SheafFinitePresentationTransport
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Module.FinitePresentation

public section

set_option warningAsError true

/-!
# Finite presentations of modules on schemes

Finite presentations restrict along open immersions. A finitely presented module
over a commutative ring gives a natively finitely presented associated sheaf.
Every natively finitely presented sheaf on a scheme admits finite presentations
on an affine open cover; the cover itself need not be finite.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Open restriction preserves both finite indices of a supplied presentation. -/
theorem isFinite_presentationRestrict {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] {M : X.Modules} (P : M.Presentation) [hP : P.IsFinite] :
    (presentationRestrict f P).IsFinite where
  isFiniteType_generators := ⟨by
    change Finite P.generators.I
    exact hP.isFiniteType_generators.finite⟩
  isFiniteType_relations := ⟨by
    change Finite P.relations.I
    exact hP.isFiniteType_relations.finite⟩

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

private theorem isFinite_presentationTilde (s : Set M) [Finite s]
    (hs : Submodule.span R s = ⊤) (t : Set (s →₀ R)) [Finite t]
    (ht : Submodule.span R t = LinearMap.ker (Finsupp.linearCombination R ((↑) : s → M))) :
    (presentationTilde M s hs t ht).IsFinite where
  isFiniteType_generators := ⟨by change Finite s; infer_instance⟩
  isFiniteType_relations := ⟨by change Finite t; infer_instance⟩

/-- A finitely presented module has a natively finitely presented associated
sheaf, without an additional coherence or projectivity hypothesis. -/
theorem isFinitePresentation_tilde [Module.FinitePresentation R M] :
    (tilde M).IsFinitePresentation := by
  obtain ⟨s, hs, t, ht⟩ := Module.FinitePresentation.out (R := R) (M := M)
  let P := presentationTilde M (s : Set M) hs (t : Set ((s : Set M) →₀ R)) ht
  let : P.IsFinite := isFinite_presentationTilde M _ hs _ ht
  exact P.isFinitePresentation.{u, u, u}

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- A locally finitely presented sheaf has finite generator and relation
presentations on affine opens. The affine cover is not required to be finite;
its finite presentations come from the same finite quasicoherent datum. -/
theorem exists_isOpenCover_isFinite_presentation {X : Scheme.{u}}
    (M : X.Modules) [M.IsFinitePresentation] :
    ∃ (ι : Type u) (U : ι → X.Opens)
      (P : ∀ i, (M.restrict (U i).ι).Presentation),
      IsOpenCover U ∧ (∀ i, IsAffineOpen (U i)) ∧ ∀ i, (P i).IsFinite := by
  classical
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  let : q.IsFinitePresentation := hq
  choose κ hsub heq using fun i ↦ Opens.isBasis_iff_cover.mp X.isBasis_affineOpens (q.X i)
  let P (i : Σ (j : q.I), κ j) :
      (M.restrict (Scheme.Opens.ι i.2.1)).Presentation := by
    let f := X.homOfLE (U := i.2) (V := q.X i.1) (by simp [heq, le_sSup])
    have : PreservesColimitsOfSize.{u, u} (restrictFunctor f) := inferInstance
    let F := (overEquiv (q.X i.1)).functor ⋙ restrictFunctor f
    let iso : SheafOfModules.overFunctor X.ringCatSheaf _ ⋙ F ≅ restrictFunctor
        (Scheme.Opens.ι i.2.1) := (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv _) _ ≪≫
          (restrictFunctorComp _ _).symm ≪≫ (restrictFunctorCongr (by simp [f]))
    exact SheafOfModules.Presentation.ofIsIso.{u, u, u} (iso.app M).hom <|
      (q.presentation i.1).map F (Scheme.Modules.restrictUnitIso _).symm
  refine ⟨Σ (i : q.I), κ i, fun j ↦ j.2, P, ?_, ?_, ?_⟩
  · have cov := q.coversTop
    rw [Opens.coversTop_iff, IsOpenCover] at cov
    rw [IsOpenCover, iSup_sigma, ← cov]
    refine iSup_congr fun i ↦ ?_
    rw [heq i, sSup_eq_iSup']
  · intro i
    exact hsub _ i.2.2
  · intro i
    constructor
    · constructor
      change Finite (q.presentation i.1).generators.I
      infer_instance
    · constructor
      change Finite (q.presentation i.1).relations.I
      infer_instance

end AlgebraicGeometry.Scheme.Modules
