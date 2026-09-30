/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.FactorialNormal

set_option warningAsError true

namespace AlgebraicGeometry.FactorialNormalOrdinaryImport

universe u

private theorem checkInstance (X : Scheme.{u}) [IsFactorial X] : IsNormal X :=
  inferInstance

end AlgebraicGeometry.FactorialNormalOrdinaryImport
