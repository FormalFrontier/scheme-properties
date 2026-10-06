/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.StructureSheaf

universe u

example (X : AlgebraicGeometry.Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
  AlgebraicGeometry.Scheme.Modules.unit_isQuasicoherent X
