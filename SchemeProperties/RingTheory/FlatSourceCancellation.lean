/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Flatness cancellation in a ring tower

For commutative ring maps `A → B → C`, faithful flatness of `B → C` and flatness
of `A → C` imply flatness of `A → B`. The three rings may have independent
universes. Faithful flatness of the composite is not required.

The proof tests injectivity after tensoring with `B`, extends scalars to `C`,
and uses tensor cancellation to compare with tensoring directly with `C`.

## References

* Mathlib's tensor-injectivity criterion for flat modules and faithful-flat
  reflection of injectivity in `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`.
* Mathlib's `TensorProduct.AlgebraTensorModule.cancelBaseChange` and its
  naturality theorem `lTensor_comp_cancelBaseChange`.
-/

@[expose] public section

open TensorProduct

universe uA uB uC

namespace RingHom.Flat

/-- Flatness of a composite ring map descends through a faithfully flat second
map. No faithful flatness of the composite is required. -/
theorem of_comp_of_faithfullyFlat
    {A : Type uA} {B : Type uB} {C : Type uC}
    [CommRing A] [CommRing B] [CommRing C]
    {a : A →+* B} {b : B →+* C}
    (hb : b.FaithfullyFlat) (hac : (b.comp a).Flat) : a.Flat := by
  let : Algebra A B := a.toAlgebra
  let : Algebra B C := b.toAlgebra
  let : Algebra A C := (b.comp a).toAlgebra
  have : IsScalarTower A B C := .of_algebraMap_eq fun _ ↦ rfl
  have : Module.FaithfullyFlat B C := hb
  have : Module.Flat A C := hac
  apply RingHom.flat_algebraMap_iff.mpr
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro M N _ _ _ _ v hv
  let vB : B ⊗[A] M →ₗ[B] B ⊗[A] N :=
    TensorProduct.AlgebraTensorModule.lTensor B B v
  have hvC : Function.Injective (vB.lTensor C) := by
    intro s t hst
    apply (TensorProduct.AlgebraTensorModule.cancelBaseChange A B B C M).injective
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := C) v hv
    have hnat (z : C ⊗[B] (B ⊗[A] M)) :
        v.lTensor C (TensorProduct.AlgebraTensorModule.cancelBaseChange A B B C M z) =
          TensorProduct.AlgebraTensorModule.cancelBaseChange A B B C N (vB.lTensor C z) :=
      DFunLike.congr_fun
        (TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange
          (R := A) (A := B) (B := B) (M := C) v) z
    exact (hnat s).trans ((congrArg
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A B B C N) hst).trans
        (hnat t).symm)
  exact (Module.FaithfullyFlat.lTensor_injective_iff_injective B C vB).mp hvC

end RingHom.Flat
