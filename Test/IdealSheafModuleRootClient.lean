/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties

set_option warningAsError true

open scoped AlgebraicGeometry

universe u

private theorem check_1 (X : AlgebraicGeometry.Scheme.{u}) :
    X.nilradicalModule.IsQuasicoherent :=
  X.nilradicalModule_isQuasicoherent
