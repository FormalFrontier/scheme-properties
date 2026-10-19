/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Sections and stalk images in the function field

A rational function on an integral scheme comes from a section on a nonempty
open set exactly when it belongs to the image of every stalk on that open set.
The maps are the canonical algebra maps to the function field.

Nonemptiness is required for the canonical map from sections to the function
field. Normality is not required for the section-image criterion.
-/

public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

private lemma germToFunctionField_res {X : Scheme.{u}} [IrreducibleSpace X]
    {U V : X.Opens} [Nonempty U] [Nonempty V] (i : V ⟶ U) (s : Γ(X, U)) :
    X.germToFunctionField V (X.presheaf.map i.op s) = X.germToFunctionField U s := by
  exact X.presheaf.germ_res_apply i (genericPoint X)
    (((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by
      simpa using (inferInstance : Nonempty V))) s

/-- A fixed rational function comes from a section on a nonempty open set if
and only if it comes from every stalk on that open set. -/
theorem mem_range_algebraMap_functionField_iff {X : Scheme.{u}} [IsIntegral X]
    (U : X.Opens) [Nonempty U] (f : X.functionField) :
    f ∈ Set.range (algebraMap Γ(X, U) X.functionField) ↔
      ∀ x : U, f ∈ Set.range (algebraMap (X.presheaf.stalk x.1) X.functionField) := by
  classical
  constructor
  · rintro ⟨s, rfl⟩ x
    exact ⟨X.presheaf.germ U x.1 x.2 s,
      X.algebraMap_germ_eq_germToFunctionField x.2 s⟩
  · intro h
    have hlocal (x : U) :
        ∃ (V : X.Opens) (_ : V ≤ U) (hxV : x.1 ∈ V) (s : Γ(X, V)),
          algebraMap (X.presheaf.stalk x.1) X.functionField
            (X.presheaf.germ V x.1 hxV s) = f := by
      obtain ⟨t, ht⟩ := h x
      obtain ⟨V, hVU, hxV, s, hs⟩ := X.presheaf.exists_le_germ_eq t x.2
      refine ⟨V, hVU, hxV, s, ?_⟩
      rwa [hs]
    choose V hVU hxV s hs using hlocal
    have (x : U) : Nonempty (V x) := ⟨⟨x.1, hxV x⟩⟩
    have hs' (x : U) : X.germToFunctionField (V x) (s x) = f :=
      (X.algebraMap_germ_eq_germToFunctionField (hxV x) (s x)).symm.trans (hs x)
    have hcompat : TopCat.Presheaf.IsCompatible X.presheaf V s := by
      intro x y
      obtain ⟨z, hzx, hzy⟩ := nonempty_preirreducible_inter (V x).isOpen (V y).isOpen
        ⟨x.1, hxV x⟩ ⟨y.1, hxV y⟩
      have : Nonempty (V x ⊓ V y : X.Opens) := ⟨⟨z, hzx, hzy⟩⟩
      apply X.germToFunctionField_injective (V x ⊓ V y)
      rw [germToFunctionField_res, germToFunctionField_res, hs' x, hs' y]
    have hcover : U ≤ iSup V := by
      intro x hx
      simp only [Opens.mem_iSup]
      exact ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
    obtain ⟨sU, hsU, -⟩ := X.sheaf.existsUnique_gluing' V U
      (fun x => homOfLE (hVU x)) hcover s hcompat
    refine ⟨sU, ?_⟩
    let x : U := Classical.choice ‹Nonempty U›
    have : Nonempty (V x) := ⟨⟨x.1, hxV x⟩⟩
    calc
      algebraMap Γ(X, U) X.functionField sU =
          X.germToFunctionField (V x) (X.presheaf.map (homOfLE (hVU x)).op sU) :=
        (germToFunctionField_res (homOfLE (hVU x)) sU).symm
      _ = X.germToFunctionField (V x) (s x) := congrArg _ (hsU x)
      _ = f := hs' x

end AlgebraicGeometry.Scheme
