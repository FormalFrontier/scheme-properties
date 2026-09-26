module

import SchemeProperties.GlobalSectionsBaseChange

set_option warningAsError true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.GlobalSectionsBaseChangeOrdinaryImport

private theorem oldPushout
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [CompactSpace X] [QuasiSeparatedSpace X] :
    letI := p.globalSectionsAlgebra k
    IsPushout
      (CommRingCat.ofHom (algebraMap k Γ(X, ⊤)))
      (CommRingCat.ofHom (algebraMap k K))
      (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop
      ((ΓSpecIso (.of K)).inv ≫
        (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop) := by
  let _ := p.globalSectionsAlgebra k
  let s : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let H : IsPullback (pullback.fst p s) (pullback.snd p s) p s :=
    IsPullback.of_hasPullback p s
  let _ : Flat s := Flat.SpecMap_iff.mpr
    (RingHom.Flat.of_isField (R := k) (S := K) (Field.toIsField k) (algebraMap k K))
  let US : (Spec (.of k)).Opens := ⊤
  let UT : (Spec (.of K)).Opens := ⊤
  let UX : X.Opens := ⊤
  let UY : (pullback p s).Opens := ⊤
  have hs : IsIso (pushoutSection H (US := US) (UT := UT) (UX := UX) (UY := UY)
      (by simp [US, UT, s]) (by simp [US, UX]) (by simp [UY, UX, UT])) :=
    isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H
      (by simp [US, UT, s]) (by simp [US, UX]) (by simp [UY, UX, UT])
      (isAffineOpen_top _) (isAffineOpen_top _)
      CompactSpace.isCompact_univ isQuasiSeparated_univ
  have h₀ : IsPushout p.appTop s.appTop (pullback.fst p s).appTop
      (pullback.snd p s).appTop := by
    have := hs
    let hh :=
      (isIso_pushoutSection_iff H (US := US) (UT := UT) (UX := UX) (UY := UY)
        (by simp [US, UT, s]) (by simp [US, UX]) (by simp [UY, UX, UT])).mp this
    simpa only [US, UT, UX, UY, s, H, Hom.app_eq_appLE, Hom.preimage_top,
      inf_idem] using hh
  have h : IsPushout
      (CommRingCat.ofHom (algebraMap k Γ(X, ⊤)))
      (CommRingCat.ofHom (algebraMap k K))
      (pullback.fst p s).appTop
      ((ΓSpecIso (.of K)).inv ≫ (pullback.snd p s).appTop) := by
    apply h₀.of_iso (ΓSpecIso (.of k)) (Iso.refl _) (ΓSpecIso (.of K)) (Iso.refl _)
    · rw [← cancel_epi (ΓSpecIso (.of k)).inv]
      simp only [Iso.inv_hom_id_assoc]
      change (ΓSpecIso (.of k)).inv ≫ p.appTop =
        CommRingCat.ofHom (p.appTop.hom.comp (ΓSpecIso (.of k)).inv.hom)
      rfl
    · exact ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap k K))
    · simp
    · simp
  simpa only [s] using h

private theorem checkEquivOldConstruction
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [CompactSpace X] [QuasiSeparatedSpace X] :
    letI := p.globalSectionsAlgebra k
    letI := p.baseChangeGlobalSectionsAlgebra k K
    globalSectionsBaseChangeEquiv k K p =
      let h := oldPushout k K p
      let hTensor := (CommRingCat.isPushout_tensorProduct k K Γ(X, ⊤)).flip
      let e := hTensor.isoIsPushout (CommRingCat.of Γ(X, ⊤)) (CommRingCat.of K) h
      { toRingEquiv := e.commRingCatIsoToRingEquiv
        commutes' r := by
          change (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ e.hom) r =
            ((ΓSpecIso (.of K)).inv ≫
              (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop) r
          exact congr($(hTensor.inr_isoIsPushout_hom
            (CommRingCat.of Γ(X, ⊤)) (CommRingCat.of K) h) r) } := by
  rfl

private theorem oldPullback
    (k K L : Type u) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) : IsPullback
      (pullback.fst
          (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≫
        pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (pullback.snd
        (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (Spec.map (CommRingCat.ofHom (algebraMap K L))))
      p (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
  let sK := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let sL := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have h := (IsPullback.of_hasPullback (pullback.snd p sK) sL).paste_horiz
    (IsPullback.of_hasPullback p sK)
  have hs : sL ≫ sK = Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    simp [IsScalarTower.algebraMap_apply k K L]
  rw [hs] at h
  exact h

private theorem checkTowerOldConstruction
    (k K L : Type u) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) :
    baseChangeTowerIso k K L p =
      (oldPullback k K L p).isoIsPullback X (Spec (.of L))
        (IsPullback.of_hasPullback p (Spec.map (CommRingCat.ofHom (algebraMap k L)))) := by
  rfl

end AlgebraicGeometry.Scheme.GlobalSectionsBaseChangeOrdinaryImport
