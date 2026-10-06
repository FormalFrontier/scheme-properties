/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties

set_option warningAsError true

open CategoryTheory Limits ZeroObject

namespace QuasicoherentAbelianClient

open AlgebraicGeometry

noncomputable section

universe u

variable (X : Scheme.{u})

#synth (SheafOfModules.isQuasicoherent X.ringCatSheaf).ContainsZero
#synth (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderFiniteProducts
#synth (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderKernels
#synth (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderCokernels
#synth Abelian ((SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)

example : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory := 0

example (M N : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory := M ⨯ N

example {M N : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory}
    (f : M ⟶ N) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory := kernel f

example {M N : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory}
    (f : M ⟶ N) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory := cokernel f

example (M N : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory := kernel (0 : M ⟶ N)

example (M N : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory := cokernel (0 : M ⟶ N)

end

end QuasicoherentAbelianClient
