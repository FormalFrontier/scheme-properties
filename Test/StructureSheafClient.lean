module

import SchemeProperties.StructureSheaf

universe u

private theorem check_1 (X : AlgebraicGeometry.Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
  AlgebraicGeometry.Scheme.Modules.unit_isQuasicoherent X
