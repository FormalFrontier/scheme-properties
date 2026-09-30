/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.CoherentQuasicoherentLocality

set_option warningAsError true

open AlgebraicGeometry CategoryTheory

universe u

namespace CoherentLocalityOrdinaryImport

private def checkProperty (X : Scheme.{u}) :
    ObjectProperty
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  Scheme.Modules.isCoherentQuasicoherent X

end CoherentLocalityOrdinaryImport
