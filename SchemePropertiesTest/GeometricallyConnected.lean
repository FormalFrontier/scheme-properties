/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.GeometricallyConnected

/-!
# Geometric connectedness of identity morphisms

The identity of the spectrum of any field is geometrically irreducible, hence geometrically
connected. Both geometric predicates also hold for the empty identity: its target has no
field-valued points. This does not assert connectedness of the empty topological space.
-/

open CategoryTheory AlgebraicGeometry

namespace SchemePropertiesTest.GeometricallyConnected

universe u

private theorem geometricallyConnected_id_spec (K : Type u) [Field K] :
    GeometricallyConnected (𝟙 (Spec (.of K))) := by
  have : GeometricallyIrreducible (𝟙 (Spec (.of K))) := by
    constructor
    intro L _ y Z fst snd h
    let : IsIso snd := h.isIso_snd_of_isIso
    exact snd.homeomorph.irreducibleSpace_iff.mpr inferInstance
  exact GeometricallyIrreducible.geometricallyConnected _

private theorem geometricallyIrreducible_and_geometricallyConnected_id_empty :
    GeometricallyIrreducible (𝟙 (∅ : Scheme.{u})) ∧
      GeometricallyConnected (𝟙 (∅ : Scheme.{u})) := by
  have : GeometricallyIrreducible (𝟙 (∅ : Scheme.{u})) := by
    constructor
    intro K _ y
    exact isEmptyElim (y (Nonempty.some inferInstance))
  exact ⟨inferInstance, inferInstance⟩

end SchemePropertiesTest.GeometricallyConnected
