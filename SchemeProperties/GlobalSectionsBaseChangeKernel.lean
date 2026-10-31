/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.GlobalSectionsBaseChange
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.Equalizer

@[expose] public section

/-!
# Kernels on global sections after flat base change

For a morphism of schemes over `Spec R`, flat scalar extension from `R` to `S`
extends the kernel of the induced map on global sections. Both schemes need
only be quasicompact and quasiseparated. Faithfully flat scalar extension
contracts the changed kernel to the original one; for contraction only the
source scheme needs to be quasicompact and quasiseparated.

The comparison is `Scheme.globalSectionsBaseChangeEquiv`, with `S` on the left
of the tensor product. Linearity and naturality are derived from the structure
morphisms and the two pullback projections.

## References

* `Scheme.globalSectionsBaseChangeEquiv` and its generator formulas supply
  the comparison between the tensor product and global sections.
* Coherent Modules' algebra-kernel base-change argument, expressed using
  Mathlib's `Module.Flat.ker_lTensor_eq` and
  `TensorProduct.AlgebraTensorModule.range_lTensor_idealMap`.
* Mathlib, `Module.FaithfullyFlat.tensorProduct_mk_injective`, supplies
  injectivity on an arbitrary module under faithfully flat scalar extension.
-/

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- Flat scalar extension extends the kernel of the map on global sections
of a morphism between quasicompact quasiseparated schemes over `Spec R`.
The proof transports Mathlib's preservation of kernels by flat tensor products
through `globalSectionsBaseChangeEquiv`. -/
theorem map_ker_appTop_baseChange
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (pX : X ⟶ Spec (.of R)) (pY : Y ⟶ Spec (.of R))
    (f : X ⟶ Y) (hf : f ≫ pY = pX) :
    let s : Spec (.of S) ⟶ Spec (.of R) :=
      Spec.map (CommRingCat.ofHom (algebraMap R S));
    let fS := pullback.map pX s pY s f (𝟙 _) (𝟙 _)
      ((Category.comp_id pX).trans hf.symm)
      ((Category.comp_id s).trans (Category.id_comp s).symm);
    Ideal.map (pullback.fst pY s).appTop.hom (RingHom.ker f.appTop.hom) =
      RingHom.ker fS.appTop.hom := by
  let s : Spec (.of S) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R S))
  let fS := pullback.map pX s pY s f (𝟙 _) (𝟙 _)
    ((Category.comp_id pX).trans hf.symm)
    ((Category.comp_id s).trans (Category.id_comp s).symm)
  let : Algebra R Γ(X, ⊤) := pX.globalSectionsAlgebra R
  let : Algebra R Γ(Y, ⊤) := pY.globalSectionsAlgebra R
  let : Algebra S Γ(pullback pX s, ⊤) := pX.baseChangeGlobalSectionsAlgebra R S
  let : Algebra S Γ(pullback pY s, ⊤) := pY.baseChangeGlobalSectionsAlgebra R S
  let fR : Γ(Y, ⊤) →ₐ[R] Γ(X, ⊤) :=
    { toRingHom := f.appTop.hom
      commutes' r := by
        change (pY.appTop ≫ f.appTop) ((ΓSpecIso (.of R)).inv r) =
          pX.appTop ((ΓSpecIso (.of R)).inv r)
        rw [← Hom.comp_appTop f pY, hf] }
  let eX := globalSectionsBaseChangeEquiv R S pX
  let eY := globalSectionsBaseChangeEquiv R S pY
  let eXR : S ⊗[R] Γ(X, ⊤) →+* Γ(pullback pX s, ⊤) := eX
  let eYR : S ⊗[R] Γ(Y, ⊤) →+* Γ(pullback pY s, ⊤) := eY
  let t : S ⊗[R] Γ(Y, ⊤) →+* S ⊗[R] Γ(X, ⊤) :=
    Algebra.TensorProduct.map (AlgHom.id R S) fR
  let iY : Γ(Y, ⊤) →+* S ⊗[R] Γ(Y, ⊤) :=
    (Algebra.TensorProduct.includeRight : Γ(Y, ⊤) →ₐ[R] S ⊗[R] Γ(Y, ⊤))
  have hfst : fS ≫ pullback.fst pY s = pullback.fst pX s ≫ f :=
    pullback.lift_fst _ _ _
  have hsnd : fS ≫ pullback.snd pY s = pullback.snd pX s := by
    simp only [fS, pullback.map, pullback.lift_snd, Category.comp_id]
  have hfstΓ (y : Γ(Y, ⊤)) :
      fS.appTop ((pullback.fst pY s).appTop y) =
        (pullback.fst pX s).appTop (f.appTop y) := by
    change (fS ≫ pullback.fst pY s).appTop y =
      (pullback.fst pX s ≫ f).appTop y
    rw [hfst]
  have hsndΓ (z : Γ(Spec (.of S), ⊤)) :
      fS.appTop ((pullback.snd pY s).appTop z) =
        (pullback.snd pX s).appTop z := by
    change (fS ≫ pullback.snd pY s).appTop z = _
    rw [hsnd]
  have hnat : fS.appTop.hom.comp eYR = eXR.comp t := by
    apply RingHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul r y =>
      change fS.appTop (globalSectionsBaseChangeEquiv R S pY (r ⊗ₜ[R] y)) =
        globalSectionsBaseChangeEquiv R S pX
          (Algebra.TensorProduct.map (AlgHom.id R S) fR (r ⊗ₜ[R] y))
      rw [Algebra.TensorProduct.map_tmul]
      change fS.appTop (globalSectionsBaseChangeEquiv R S pY (r ⊗ₜ[R] y)) =
        globalSectionsBaseChangeEquiv R S pX (r ⊗ₜ[R] f.appTop y)
      rw [globalSectionsBaseChangeEquiv_tmul R S pY,
        globalSectionsBaseChangeEquiv_tmul R S pX, map_mul, hfstΓ, hsndΓ]
    | add z w hz hw => simp only [map_add, hz, hw]
  have hiY : eYR.comp iY = (pullback.fst pY s).appTop.hom := by
    ext y
    exact globalSectionsBaseChangeEquiv_one_tmul R S pY y
  change (RingHom.ker fR).map (pullback.fst pY s).appTop.hom =
    RingHom.ker fS.appTop.hom
  calc
    (RingHom.ker fR).map (pullback.fst pY s).appTop.hom =
        ((RingHom.ker fR).map iY).map eYR := by
      rw [Ideal.map_map, hiY]
    _ = (RingHom.ker t).map eYR := by
      apply congrArg (Ideal.map eYR)
      symm
      apply (Submodule.restrictScalars_injective R _ _)
      exact (Module.Flat.ker_lTensor_eq R S fR.toLinearMap).trans
        (_root_.TensorProduct.AlgebraTensorModule.range_lTensor_idealMap
          (R := R) (A := S) R (RingHom.ker fR))
    _ = (RingHom.ker (fS.appTop.hom.comp eYR)).map eYR := by
      apply congrArg (Ideal.map eYR)
      rw [hnat]
      exact (RingHom.ker_comp_of_injective t eX.injective).symm
    _ = RingHom.ker fS.appTop.hom := by
      rw [← RingHom.comap_ker]
      exact Ideal.map_comap_of_surjective eYR eY.surjective _

/-- Faithfully flat scalar extension contracts the kernel of the changed map
on global sections. Only the source is required to be quasicompact and
quasiseparated; the target is arbitrary. Injectivity of the source projection
comes from `Module.FaithfullyFlat.tensorProduct_mk_injective` and
`globalSectionsBaseChangeEquiv_one_tmul`. -/
theorem comap_ker_appTop_baseChange
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (pX : X ⟶ Spec (.of R)) (pY : Y ⟶ Spec (.of R))
    (f : X ⟶ Y) (hf : f ≫ pY = pX) :
    let s : Spec (.of S) ⟶ Spec (.of R) :=
      Spec.map (CommRingCat.ofHom (algebraMap R S));
    let fS := pullback.map pX s pY s f (𝟙 _) (𝟙 _)
      ((Category.comp_id pX).trans hf.symm)
      ((Category.comp_id s).trans (Category.id_comp s).symm);
    Ideal.comap (pullback.fst pY s).appTop.hom (RingHom.ker fS.appTop.hom) =
      RingHom.ker f.appTop.hom := by
  let s : Spec (.of S) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R S))
  let fS := pullback.map pX s pY s f (𝟙 _) (𝟙 _)
    ((Category.comp_id pX).trans hf.symm)
    ((Category.comp_id s).trans (Category.id_comp s).symm)
  let : Algebra R Γ(X, ⊤) := pX.globalSectionsAlgebra R
  let : Algebra S Γ(pullback pX s, ⊤) := pX.baseChangeGlobalSectionsAlgebra R S
  have hinj : Function.Injective (pullback.fst pX s).appTop.hom := by
    intro x y hxy
    apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := S) Γ(X, ⊤)
    change (1 : S) ⊗ₜ[R] x = (1 : S) ⊗ₜ[R] y
    apply (globalSectionsBaseChangeEquiv R S pX).injective
    simpa only [globalSectionsBaseChangeEquiv_one_tmul] using hxy
  have hfst : fS ≫ pullback.fst pY s = pullback.fst pX s ≫ f :=
    pullback.lift_fst _ _ _
  have hfirst : fS.appTop.hom.comp (pullback.fst pY s).appTop.hom =
      (pullback.fst pX s).appTop.hom.comp f.appTop.hom := by
    change (fS ≫ pullback.fst pY s).appTop.hom =
      (pullback.fst pX s ≫ f).appTop.hom
    rw [hfst]
  change Ideal.comap (pullback.fst pY s).appTop.hom (RingHom.ker fS.appTop.hom) =
    RingHom.ker f.appTop.hom
  rw [RingHom.comap_ker, hfirst]
  exact RingHom.ker_comp_of_injective f.appTop.hom hinj

end AlgebraicGeometry.Scheme
