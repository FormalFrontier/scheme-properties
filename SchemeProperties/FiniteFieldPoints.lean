/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.FiniteAlgHom
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Basic.Finite.Sigma
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Finite-field points of a finite-type scheme morphism

For a finite field `K`, a locally-finite-type, quasi-compact morphism `p : X ⟶ S`
has finitely many lifts of any point `q : Spec K ⟶ S`. These lifts are the
morphisms `Over.mk q ⟶ Over.mk p` in the over category; the base scheme is
arbitrary. No properness, separatedness, reducedness, integrality or group
structure is needed.

The proof pulls back to `Spec K`, takes a finite affine subcover, and uses
`Algebra.FiniteType.finite_algHom` on each chart. Mathlib's `Spec.homEquivAlgHom`
applies after the chart's canonical `isoSpec`, with the algebra structure
induced by its structure map. Since `Spec K` has one point, every section
lands in one chart. The pullback adjunction then returns lifts over the original
base. No alternative notion of a rational point is introduced.

The finite-field and quasi-compactness assumptions cannot simply be dropped:
the affine line over an infinite field has infinitely many evaluation sections,
and an infinite disjoint union of copies of `Spec K` has infinitely many
sections while remaining locally of finite type over `K`.

## References

* `SchemeProperties.FiniteAlgHom`: finite-target algebra homomorphisms.
* Mathlib's finite affine subcovers, `Scheme.isoSpec`, `Spec.homEquivAlgHom`,
  open-immersion lifting and `Over.mapPullbackAdj` supply the geometric APIs.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Over a finite field, a locally-finite-type, quasi-compact scheme morphism has
finitely many lifts of each field-valued point of its base. The base is arbitrary;
no properness, separatedness, reducedness, integrality, or group structure is assumed. -/
theorem finite_overHom_of_finiteField
    {K : Type u} [Field K] [Finite K] {X S : Scheme.{u}}
    (p : X ⟶ S) [LocallyOfFiniteType p] [QuasiCompact p]
    (q : Spec (CommRingCat.of K) ⟶ S) :
    Finite (Over.mk q ⟶ Over.mk p) := by
  classical
  let T := Spec (CommRingCat.of K)
  let Y := Limits.pullback p q
  let r : Y ⟶ T := Limits.pullback.snd p q
  let 𝒰 := Y.affineCover.finiteSubcover
  letI : ∀ i, Finite (Over.mk (𝟙 T) ⟶ Over.mk (𝒰.f i ≫ r)) := by
    intro i
    let A := Γ(𝒰.X i, ⊤)
    let e := (𝒰.X i).isoSpec
    let s : Spec A ⟶ T := e.inv ≫ 𝒰.f i ≫ r
    let φ : CommRingCat.of K ⟶ A := Spec.preimage s
    have hs : LocallyOfFiniteType s := by
      dsimp only [s, r]
      infer_instance
    have hφ : φ.hom.FiniteType := by
      apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
      simpa only [φ, Spec.map_preimage] using hs
    letI : Algebra K A := φ.hom.toAlgebra
    letI : Algebra.FiniteType K A := hφ
    letI : Finite (A →ₐ[K] K) :=
      Algebra.FiniteType.finite_algHom (R := K) (A := A) (B := K)
    have hmap : Spec.algebraMap K A = s := by
      change Spec.map (CommRingCat.ofHom φ.hom) = s
      exact Spec.map_preimage s
    let F : (Over.mk (𝟙 T) ⟶ Over.mk (𝒰.f i ≫ r)) → (A →ₐ[K] K) :=
      fun a => Spec.homEquivAlgHom (R := K) ⟨a.left ≫ e.hom, by
        rw [hmap]
        simpa [s, Category.assoc, Spec.algebraMap] using Over.w a⟩
    apply Finite.of_injective F
    intro a b hab
    apply Over.OverMorphism.ext
    have h := (Spec.homEquivAlgHom (R := K) (A := A) (B := K)).injective hab
    exact (cancel_mono e.hom).mp (congrArg Subtype.val h)
  let compose : (Σ i, Over.mk (𝟙 T) ⟶ Over.mk (𝒰.f i ≫ r)) →
      (Over.mk (𝟙 T) ⟶ Over.mk r) :=
    fun a => Over.homMk (a.2.left ≫ 𝒰.f a.1)
      (by simpa [Category.assoc] using Over.w a.2)
  haveI : Finite (Over.mk (𝟙 T) ⟶ Over.mk r) :=
    Finite.of_surjective compose (by
      intro a
      let x : T := default
      let i := 𝒰.idx (a.left x)
      have h : Set.range a.left ⊆ Set.range (𝒰.f i) := by
        rintro _ ⟨z, rfl⟩
        have hz : z = x := Subsingleton.elim (α := PrimeSpectrum K) _ _
        simpa only [hz] using 𝒰.covers (a.left x)
      let b := IsOpenImmersion.lift (𝒰.f i) a.left h
      have hb : b ≫ (𝒰.f i ≫ r) = 𝟙 T := by
        rw [← Category.assoc, IsOpenImmersion.lift_fac]
        exact Over.w a
      refine ⟨⟨i, Over.homMk b hb⟩, ?_⟩
      apply Over.OverMorphism.ext
      change b ≫ 𝒰.f i = a.left
      exact IsOpenImmersion.lift_fac _ _ h)
  haveI : Finite ((Over.map q).obj (Over.mk (𝟙 T)) ⟶ Over.mk p) :=
    Finite.of_equiv (Over.mk (𝟙 T) ⟶ Over.mk r)
      ((Over.mapPullbackAdj q).homEquiv (Over.mk (𝟙 T)) (Over.mk p)).symm
  let e : (Over.map q).obj (Over.mk (𝟙 T)) ≅ Over.mk q :=
    Over.isoMk (Iso.refl T) (by simp)
  exact Finite.of_injective (fun a => e.hom ≫ a)
    (fun a b h => (cancel_epi e.hom).mp h)

end AlgebraicGeometry
