module

import SchemeProperties

set_option warningAsError true

open CategoryTheory Limits ZeroObject

namespace QuasicoherentAbelianClient

open AlgebraicGeometry

noncomputable section

universe u

variable (X : Scheme.{u})

abbrev QCoh :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory

#synth (SheafOfModules.isQuasicoherent X.ringCatSheaf).ContainsZero
#synth (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderFiniteProducts
#synth (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderKernels
#synth (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderCokernels
#synth Abelian (QCoh X)

private def check_1 : QCoh X := 0

private def check_2 (M N : QCoh X) : QCoh X := M ⨯ N

private def check_3 {M N : QCoh X} (f : M ⟶ N) : QCoh X := kernel f

private def check_4 {M N : QCoh X} (f : M ⟶ N) : QCoh X := cokernel f

private def check_5 (M N : QCoh X) : QCoh X := kernel (0 : M ⟶ N)

private def check_6 (M N : QCoh X) : QCoh X := cokernel (0 : M ⟶ N)

end

end QuasicoherentAbelianClient
