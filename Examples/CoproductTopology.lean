module

import SchemeProperties.CoproductTopology

/-! # Direct-import client checks for coproduct topology -/

set_option warningAsError true

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.CoproductTopologyClient

noncomputable section

variable {ι : Type u} (X : ι → Scheme.{u})

private theorem check_1 [∀ i, QuasiSeparatedSpace (X i)] :
    QuasiSeparatedSpace (∐ X : Scheme.{u}) := inferInstance

private theorem check_2 [Infinite ι] [∀ i, Nonempty (X i)] :
    ¬ CompactSpace (∐ X : Scheme.{u}) :=
  not_compactSpace_sigma X

-- Empty indexing families are covered by the quasiseparated instance.
private theorem check_3 :
    QuasiSeparatedSpace
      (∐ (fun _ : Empty ↦ (∅ : Scheme.{0})) : Scheme.{0}) := by
  let X₀ : Empty → Scheme.{0} := fun _ ↦ ∅
  change QuasiSeparatedSpace (∐ X₀ : Scheme.{0})
  exact @quasiSeparatedSpace_sigma Empty X₀ (fun i ↦ i.elim)

-- Empty components require no artificial nonemptiness hypothesis.
private theorem check_4 :
    QuasiSeparatedSpace
      (∐ (fun _ : ι ↦ (∅ : Scheme.{u})) : Scheme.{u}) := inferInstance

-- A concrete infinite family exercises the literal nonemptiness boundary.
private theorem check_5 :
    ¬ CompactSpace
      (∐ (fun _ : ℕ ↦ Spec (.of ℤ)) : Scheme.{0}) :=
  not_compactSpace_sigma _

end

end AlgebraicGeometry.CoproductTopologyClient
