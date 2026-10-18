/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.CoproductTopology

/-! # Direct-import client checks for coproduct topology -/

set_option warningAsError true

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.CoproductTopologyClient

noncomputable section

variable {ι : Type u} (X : ι → Scheme.{u})

example [∀ i, QuasiSeparatedSpace (X i)] :
    QuasiSeparatedSpace (∐ X : Scheme.{u}) := inferInstance

example [Infinite ι] [∀ i, Nonempty (X i)] :
    ¬ CompactSpace (∐ X : Scheme.{u}) :=
  not_compactSpace_sigma X

-- Empty indexing families are covered by the quasiseparated instance.
example :
    QuasiSeparatedSpace
      (∐ (fun _ : Empty ↦ (∅ : Scheme.{0})) : Scheme.{0}) := by
  let X₀ : Empty → Scheme.{0} := fun _ ↦ ∅
  change QuasiSeparatedSpace (∐ X₀ : Scheme.{0})
  exact @quasiSeparatedSpace_sigma Empty X₀ (fun i ↦ i.elim)

-- Empty components require no artificial nonemptiness hypothesis.
example :
    QuasiSeparatedSpace
      (∐ (fun _ : ι ↦ (∅ : Scheme.{u})) : Scheme.{u}) := inferInstance

-- A concrete infinite family exercises the literal nonemptiness boundary.
example :
    ¬ CompactSpace
      (∐ (fun _ : ℕ ↦ Spec (.of ℤ)) : Scheme.{0}) :=
  not_compactSpace_sigma _

end

end AlgebraicGeometry.CoproductTopologyClient
