/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.GlobalSectionsBaseChangeKernel

/-!
# Reflecting global-section kernel inclusions

Kernel inclusion after faithfully flat base change implies the original kernel
inclusion. Only the second source scheme is required to be quasicompact and
quasiseparated; the first source and the common target are arbitrary. Naturality
sends membership in the first kernel to membership after base change, while
faithfully flat contraction reflects membership in the second kernel.
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

example (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] {X Y Z : Scheme.{u}}
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (pX : X ⟶ Spec (.of R)) (pY : Y ⟶ Spec (.of R))
    (pZ : Z ⟶ Spec (.of R)) (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : f ≫ pY = pX) (hg : g ≫ pY = pZ) :
    let s : Spec (.of S) ⟶ Spec (.of R) :=
      Spec.map (CommRingCat.ofHom (algebraMap R S));
    let fS := pullback.map pX s pY s f (𝟙 _) (𝟙 _)
      ((Category.comp_id pX).trans hf.symm)
      ((Category.comp_id s).trans (Category.id_comp s).symm);
    let gS := pullback.map pZ s pY s g (𝟙 _) (𝟙 _)
      ((Category.comp_id pZ).trans hg.symm)
      ((Category.comp_id s).trans (Category.id_comp s).symm);
    RingHom.ker fS.appTop.hom ≤ RingHom.ker gS.appTop.hom →
      RingHom.ker f.appTop.hom ≤ RingHom.ker g.appTop.hom := by
  dsimp only
  intro h a ha
  let s : Spec (.of S) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R S))
  let fS := pullback.map pX s pY s f (𝟙 _) (𝟙 _)
    ((Category.comp_id pX).trans hf.symm)
    ((Category.comp_id s).trans (Category.id_comp s).symm)
  have hfst : fS ≫ pullback.fst pY s = pullback.fst pX s ≫ f :=
    pullback.lift_fst _ _ _
  have happ := congrArg (fun k : pullback pX s ⟶ Y => k.appTop.hom a) hfst
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at happ
  change fS.appTop.hom ((pullback.fst pY s).appTop.hom a) =
    (pullback.fst pX s).appTop.hom (f.appTop.hom a) at happ
  have haS : (pullback.fst pY s).appTop.hom a ∈ RingHom.ker fS.appTop.hom := by
    change fS.appTop.hom ((pullback.fst pY s).appTop.hom a) = 0
    rw [happ, show f.appTop.hom a = 0 from ha, map_zero]
  rw [← comap_ker_appTop_baseChange R S pZ pY g hg]
  exact h haS

end AlgebraicGeometry.Scheme
