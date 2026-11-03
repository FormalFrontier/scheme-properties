/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.ModuleTilde
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Finsupp.SMul

/-!
# Augmentation modules and their associated sheaves

The augmentation action of `MvPolynomial I ℤ` on `J →₀ ℤ` sends every variable
to zero. Its associated sheaf has only zero sections on `D(X i)`, a nonempty
proper open, but has a nonzero global section whenever a coordinate is specified.
The two index types may belong to independent universes.

## References

* `Mathlib.Algebra.Module.LocalizedModule.Basic`: the annihilator criterion
  `IsLocalizedModule.subsingleton_iff`.
* `Mathlib.Algebra.MvPolynomial.Eval`: evaluation of multivariate polynomials.
-/

@[expose] public section

noncomputable section

universe u v

open Opposite

namespace AlgebraicGeometry.moduleTilde

/-- If `f` annihilates the coefficient module, its associated sheaf has only
zero sections on `D(f)`. -/
theorem subsingleton_basicOpen_of_smul_eq_zero
    {R : CommRingCat.{u}} (M : ModuleCat.{v} R) (f : R)
    (hf : ∀ m : M, f • m = 0) :
    Subsingleton ((moduleTilde M).val.obj (op (PrimeSpectrum.basicOpen f))) := by
  let : IsLocalizedModule (Submonoid.powers f)
      (toOpen M (PrimeSpectrum.basicOpen f)) :=
    isLocalizedModule_toOpen M f
  exact (IsLocalizedModule.subsingleton_iff (Submonoid.powers f)
    (toOpen M (PrimeSpectrum.basicOpen f))).2
      (fun m ↦ ⟨f, Submonoid.mem_powers f, hf m⟩)

/-- The module `J →₀ ℤ` over `MvPolynomial I ℤ` with action through evaluation
of every variable at zero. -/
def augmentationModule (I : Type u) (J : Type v) :
    ModuleCat.{v} (CommRingCat.of (MvPolynomial I ℤ)) := by
  letI : Module (MvPolynomial I ℤ) (J →₀ ℤ) :=
    Module.compHom (J →₀ ℤ) (MvPolynomial.eval (fun _ : I ↦ (0 : ℤ)))
  exact ModuleCat.of (MvPolynomial I ℤ) (J →₀ ℤ)

/-- Scalar multiplication in the augmentation module is integer scalar
multiplication by the value of the polynomial at zero. -/
theorem augmentationModule_smul (I : Type u) (J : Type v)
    (r : MvPolynomial I ℤ) (m : augmentationModule I J) :
    (r • m : augmentationModule I J) =
      MvPolynomial.eval (fun _ : I ↦ (0 : ℤ)) r • (m : J →₀ ℤ) := (rfl)

/-- The augmentation module has zero sections on the nonempty proper open
`D(X i)`, but the numerator of `Finsupp.single j 1` is a nonzero global section. -/
theorem augmentation_support_basicOpen (I : Type u) (J : Type v) (i : I) (j : J) :
    Subsingleton ((moduleTilde (augmentationModule I J)).val.obj
      (op (PrimeSpectrum.basicOpen (MvPolynomial.X (R := ℤ) i)))) ∧
    toOpen (augmentationModule I J) ⊤ (Finsupp.single j (1 : ℤ)) ≠ 0 ∧
    (∃ p : PrimeSpectrum (MvPolynomial I ℤ),
      p ∈ PrimeSpectrum.basicOpen (MvPolynomial.X (R := ℤ) i)) ∧
    PrimeSpectrum.basicOpen (MvPolynomial.X (R := ℤ) i) ≠ ⊤ := by
  classical
  have hkill : ∀ m : augmentationModule I J,
      MvPolynomial.X (R := ℤ) i • m = 0 := by
    intro m
    rw [augmentationModule_smul]
    simp
  have hloc := subsingleton_basicOpen_of_smul_eq_zero
    (augmentationModule I J) (MvPolynomial.X (R := ℤ) i) hkill
  let e : augmentationModule I J := Finsupp.single j 1
  have he : e ≠ 0 := by
    change (Finsupp.single j (1 : ℤ) : J →₀ ℤ) ≠ 0
    simp
  have hglobal : toOpen (augmentationModule I J) ⊤ e ≠ 0 := by
    intro h
    have hzero :
        (topLinearEquiv (augmentationModule I J)).toFun
          (0 : augmentationModule I J) = 0 :=
      map_zero ((topLinearEquiv (augmentationModule I J)).toLinearMap)
    have htop :
        (topLinearEquiv (augmentationModule I J)).toFun e =
          (topLinearEquiv (augmentationModule I J)).toFun
            (0 : augmentationModule I J) :=
      Eq.trans (topLinearEquiv_apply (augmentationModule I J) e)
        (Eq.trans h hzero.symm)
    exact he ((topLinearEquiv (augmentationModule I J)).injective htop)
  let p0 : PrimeSpectrum ℤ := ⟨⊥, inferInstance⟩
  let pIn : PrimeSpectrum (MvPolynomial I ℤ) :=
    PrimeSpectrum.comap
      (MvPolynomial.eval (fun k : I ↦ if k = i then (1 : ℤ) else 0)) p0
  let pOut : PrimeSpectrum (MvPolynomial I ℤ) :=
    PrimeSpectrum.comap (MvPolynomial.eval (fun _ : I ↦ (0 : ℤ))) p0
  have hin : pIn ∈ PrimeSpectrum.basicOpen (MvPolynomial.X (R := ℤ) i) := by
    simp [pIn, p0, PrimeSpectrum.mem_basicOpen, Ideal.mem_comap]
  have hout : pOut ∉ PrimeSpectrum.basicOpen (MvPolynomial.X (R := ℤ) i) := by
    simp [pOut, p0, PrimeSpectrum.mem_basicOpen, Ideal.mem_comap]
  refine ⟨hloc, hglobal, ⟨pIn, hin⟩, ?_⟩
  intro htop
  apply hout
  rw [htop]
  trivial

end AlgebraicGeometry.moduleTilde
