/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Topology.Connected.LocallyConnected

/-!
# Schemes as coproducts of connected components

The connected components of a locally connected scheme are open. This file
packages each component as an open subscheme and identifies the original
scheme with the coproduct of those open subschemes.

The construction is independent of group schemes and does not require the
scheme to be nonempty, quasicompact, or locally of finite type. Finiteness of
the component set is likewise not needed.
-/

public section

open CategoryTheory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

universe u

/-- The open subscheme underlying one connected component of a locally
connected scheme. It is defined canonically as the inverse image of the
corresponding singleton under the connected-component quotient map. -/
@[expose]
def Scheme.connectedComponentOpen (X : Scheme.{u}) [LocallyConnectedSpace X]
    (c : ConnectedComponents X) : X.Opens :=
  ⟨ConnectedComponents.mk ⁻¹' {c},
    (isOpen_discrete {c}).preimage ConnectedComponents.continuous_coe⟩

@[simp]
lemma Scheme.mem_connectedComponentOpen (X : Scheme.{u}) [LocallyConnectedSpace X]
    (c : ConnectedComponents X) (x : X) :
    x ∈ X.connectedComponentOpen c ↔ ConnectedComponents.mk x = c := by
  rfl

/-- The component open indexed by a point has the expected underlying set. -/
lemma Scheme.connectedComponentOpen_mk (X : Scheme.{u}) [LocallyConnectedSpace X]
    (x : X) :
    (X.connectedComponentOpen (ConnectedComponents.mk x) : Set X) =
      connectedComponent x := by
  exact connectedComponents_preimage_singleton

/-- The connected-component opens cover a locally connected scheme. -/
lemma Scheme.iSup_connectedComponentOpen (X : Scheme.{u}) [LocallyConnectedSpace X] :
    ⨆ c : ConnectedComponents X, X.connectedComponentOpen c = ⊤ := by
  ext x
  simp

/-- Distinct connected components give disjoint open subschemes. -/
lemma Scheme.connectedComponentOpen_disjoint (X : Scheme.{u})
    [LocallyConnectedSpace X] {c d : ConnectedComponents X} (h : c ≠ d) :
    Disjoint (X.connectedComponentOpen c) (X.connectedComponentOpen d) := by
  rw [disjoint_iff]
  ext x
  change (ConnectedComponents.mk x = c ∧ ConnectedComponents.mk x = d) ↔ False
  constructor
  · rintro ⟨hc, hd⟩
    exact h (hc.symm.trans hd)
  · exact False.elim

/-- A locally connected scheme is canonically the coproduct of the open
subschemes carried by its connected components. -/
@[expose]
def Scheme.connectedComponentSigmaIso (X : Scheme.{u}) [LocallyConnectedSpace X] :
    (∐ fun c : ConnectedComponents X ↦ (X.connectedComponentOpen c).toScheme) ≅ X := by
  let f := fun c : ConnectedComponents X ↦ (X.connectedComponentOpen c).ι
  have hcol : Nonempty (IsColimit (Cofan.mk X f)) :=
    nonempty_isColimit_cofanMk_of f
      (by simpa only [f, Scheme.Opens.opensRange_ι] using X.iSup_connectedComponentOpen)
      (by
        intro c d hcd
        simpa only [f, Scheme.Opens.opensRange_ι] using
          X.connectedComponentOpen_disjoint hcd)
  letI : IsIso (Sigma.desc f) :=
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk X f)).mp hcol
  exact asIso (Sigma.desc f)

/-- On each coproduct summand, the component decomposition isomorphism is the
canonical open immersion. -/
@[reassoc]
lemma Scheme.connectedComponentSigmaIso_hom_ι (X : Scheme.{u})
    [LocallyConnectedSpace X] (c : ConnectedComponents X) :
    Sigma.ι (fun c : ConnectedComponents X ↦ (X.connectedComponentOpen c).toScheme) c ≫
      X.connectedComponentSigmaIso.hom = (X.connectedComponentOpen c).ι := by
  change Sigma.ι _ c ≫ Sigma.desc (fun c => (X.connectedComponentOpen c).ι) = _
  exact Sigma.ι_desc _ _

/-- A morphism out of a locally connected scheme, separated into one copy of
the target for every connected component of the source. -/
@[expose]
def Scheme.toConnectedComponentCoproduct {X S : Scheme.{u}}
    [LocallyConnectedSpace X] (f : X ⟶ S) :
    X ⟶ ∐ fun _ : ConnectedComponents X ↦ S :=
  X.connectedComponentSigmaIso.inv ≫
    Limits.Sigma.map (fun c ↦ (X.connectedComponentOpen c).ι ≫ f)

/-- On one connected component, `toConnectedComponentCoproduct` is the
original morphism followed by the corresponding coproduct inclusion. -/
@[reassoc]
lemma Scheme.connectedComponentOpen_ι_toConnectedComponentCoproduct
    {X S : Scheme.{u}} [LocallyConnectedSpace X] (f : X ⟶ S)
    (c : ConnectedComponents X) :
    (X.connectedComponentOpen c).ι ≫ X.toConnectedComponentCoproduct f =
      (X.connectedComponentOpen c).ι ≫ f ≫
        Sigma.ι (fun _ : ConnectedComponents X ↦ S) c := by
  rw [← X.connectedComponentSigmaIso_hom_ι c]
  simp [Scheme.toConnectedComponentCoproduct]
  rw [X.connectedComponentSigmaIso_hom_ι_assoc c]

end AlgebraicGeometry
