/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties

/-! # Aggregate-root client checks for coproduct topology -/

set_option warningAsError true

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.CoproductTopologyRootClient

variable {ι : Type u} (X : ι → Scheme.{u})

example [∀ i, QuasiSeparatedSpace (X i)] :
    QuasiSeparatedSpace (∐ X : Scheme.{u}) := inferInstance

example [Infinite ι] [∀ i, Nonempty (X i)] :
    ¬ CompactSpace (∐ X : Scheme.{u}) :=
  not_compactSpace_sigma X

end AlgebraicGeometry.CoproductTopologyRootClient
