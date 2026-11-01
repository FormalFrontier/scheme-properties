/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.RingTheory.Adjoin.FG
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Descent of scheme points to finitely generated subalgebras

Let `K → R → S` be a tower of commutative rings with its given `K`-algebra structures.
If `X` is locally of finite presentation over `Spec K`, every `S`-point of `X` over
`Spec K` comes from a point over a finitely generated `R`-subalgebra of `S`.
The forward map is `algSpec` applied to the subalgebra inclusion, and its
composite with the descended point equals the original point in the over category.
Neither the map `R → S` nor `K → R` is required to be injective or of finite type.
There are no affineness or quasi-compactness assumptions on `X`.

The private construction uses the inclusion preorder of finitely generated subalgebras.
Its ring cocone has vertex the original `S` and legs the subtype inclusions. Singleton
coverage and injectivity of those legs give a type colimit by the filtered-colimit
criterion; reflection by the forgetful functor gives a colimit of the same ring cocone.
The `Γ-Spec` adjunction then gives a limit with vertex the original `Spec S`.
The locally finite-presentation factorization theorem supplies the stage point and
its factorization equation.

## Main result

* `Scheme.exists_algSpec_map_subalgebra_val_comp_eq_of_locallyOfFinitePresentation`

## References

* Mathlib, `Mathlib.AlgebraicGeometry.AffineTransitionLimit`, especially
  `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

section RingDiagram

variable (R : Type v) (S : Type u) [CommRing R] [CommRing S] [Algebra R S]

private abbrev FGSubalgebra := { A : Subalgebra R S // A.FG }

private instance : Nonempty (FGSubalgebra R S) :=
  ⟨⟨⊥, Subalgebra.fg_bot⟩⟩

private instance : IsDirectedOrder (FGSubalgebra R S) where
  directed A B :=
    ⟨⟨A.1 ⊔ B.1, A.2.sup B.2⟩,
      (show A.1 ≤ A.1 ⊔ B.1 from le_sup_left),
      (show B.1 ≤ A.1 ⊔ B.1 from le_sup_right)⟩

private def fgSubalgebraDiagram : FGSubalgebra R S ⥤ CommRingCat.{u} where
  obj A := CommRingCat.of A.1
  map f := CommRingCat.ofHom (Subalgebra.inclusion (leOfHom f)).toRingHom
  map_id A := by ext a; rfl
  map_comp f g := by ext a; rfl

private def fgSubalgebraCocone : Cocone (fgSubalgebraDiagram R S) where
  pt := CommRingCat.of S
  ι :=
    { app A := CommRingCat.ofHom A.1.val.toRingHom
      naturality {A B} f := by ext a; rfl }

private noncomputable def fgSubalgebraTypesIsColimit :
    IsColimit ((forget CommRingCat).mapCocone (fgSubalgebraCocone R S)) := by
  classical
  apply Types.FilteredColimit.isColimitOf'
  · intro s
    change S at s
    refine ⟨⟨Algebra.adjoin R (↑({s} : Finset S) : Set S),
      Subalgebra.fg_adjoin_finset _⟩,
      ⟨s, Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_singleton_self s))⟩,
      rfl⟩
  · intro A a b h
    change A.1 at a b
    change (a : S) = (b : S) at h
    have hab : a = b := Subtype.ext h
    refine ⟨A, 𝟙 A, ?_⟩
    change a = b
    exact hab

private noncomputable def fgSubalgebraIsColimit :
    IsColimit (fgSubalgebraCocone R S) := by
  letI : ReflectsColimit (fgSubalgebraDiagram R S) (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  exact isColimitOfReflects (forget CommRingCat) (fgSubalgebraTypesIsColimit R S)

private noncomputable def fgSubalgebraSpecDiagram : (FGSubalgebra R S)ᵒᵖ ⥤ Scheme.{u} :=
  (fgSubalgebraDiagram R S).op ⋙ Scheme.Spec

private noncomputable def fgSubalgebraSpecCone : Cone (fgSubalgebraSpecDiagram R S) :=
  Scheme.Spec.mapCone (fgSubalgebraCocone R S).op

private noncomputable def fgSubalgebraSpecIsLimit :
    IsLimit (fgSubalgebraSpecCone R S) :=
  isLimitOfPreserves Scheme.Spec (fgSubalgebraIsColimit R S).op

end RingDiagram

section ScalarTower

variable (K : Type u) {R : Type v} {S : Type u} [CommRing K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]

/-- The spectrum of a subalgebra inclusion respects the given `K`-structure.
The `K`-algebra structure on the stage is the inherited `Subalgebra.algebra'` structure. -/
private lemma Scheme.specMap_subalgebra_val_comp (A : Subalgebra R S) :
    Spec.map (CommRingCat.ofHom A.val.toRingHom) ≫ (Spec (.of A) ↘ Spec (.of K)) =
      (Spec (.of S) ↘ Spec (.of K)) := by
  simpa only [AlgHom.coe_restrictScalars, AlgHom.toRingHom_eq_coe, specOverSpec_over,
    CommRingCat.ofHom_comp, Spec.map_comp] using
    congrArg (fun h : K →+* S ↦ Spec.map (CommRingCat.ofHom h))
      (A.val.restrictScalars K).comp_algebraMap

private noncomputable def fgSubalgebraSpecBase : fgSubalgebraSpecDiagram R S ⟶
    (Functor.const (FGSubalgebra R S)ᵒᵖ).obj (Spec (.of K)) where
  app A := Spec.map (CommRingCat.ofHom (algebraMap K A.unop.1))
  naturality {A B} f := by
    change Spec.map (CommRingCat.ofHom
      (Subalgebra.inclusion (leOfHom f.unop)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K B.unop.1)) =
      Spec.map (CommRingCat.ofHom (algebraMap K A.unop.1)) ≫ 𝟙 _
    simpa only [AlgHom.coe_restrictScalars, AlgHom.toRingHom_eq_coe, Category.comp_id,
      CommRingCat.ofHom_comp, Spec.map_comp] using
      congrArg (fun h : K →+* A.unop.1 ↦ Spec.map (CommRingCat.ofHom h))
        ((Subalgebra.inclusion (leOfHom f.unop)).restrictScalars K).comp_algebraMap

/-- A point of a scheme locally of finite presentation over `Spec K` descends to a
finitely generated `R`-subalgebra of its coefficient algebra `S`.

The coefficient data are the given tower `K → R → S`: the stage inherits its
`K`-structure from the original `S`. The forward map is the `algSpec` map of
`A.val.restrictScalars K`, whose underlying ring map is the original inclusion `A → S`.
The equality is in the original over category, with the original point `x` on the right.
In particular, `algSpec_map_left` reads it back as
`Spec.map (CommRingCat.ofHom A.val.toRingHom) ≫ xA.left = x.left`.

Only the structural morphism of `X` is assumed locally of finite presentation;
`X` need not be affine or quasi-compact, and `R` need not be finitely generated over `K`. -/
theorem Scheme.exists_algSpec_map_subalgebra_val_comp_eq_of_locallyOfFinitePresentation
    (X : Scheme.{u}) [X.Over (Spec (.of K))]
    [LocallyOfFinitePresentation (X ↘ Spec (.of K))]
    (x : (Spec (.of S)).asOver (Spec (.of K)) ⟶ X.asOver (Spec (.of K))) :
    ∃ (A : Subalgebra R S), A.FG ∧
      ∃ (xA : (Spec (.of A)).asOver (Spec (.of K)) ⟶ X.asOver (Spec (.of K))),
        (algSpec (.of K)).map (CommAlgCat.ofHom (A.val.restrictScalars K)).op ≫ xA = x := by
  let : ∀ A, IsAffine ((fgSubalgebraSpecDiagram R S).obj A) := fun A ↦ by
    dsimp [fgSubalgebraSpecDiagram, fgSubalgebraDiagram]
    infer_instance
  let : ∀ A, CompactSpace ((fgSubalgebraSpecDiagram R S).obj A) := fun A ↦ inferInstance
  let : ∀ A, QuasiSeparatedSpace ((fgSubalgebraSpecDiagram R S).obj A) :=
    fun A ↦ inferInstance
  let : ∀ {A B} (f : A ⟶ B), IsAffineHom ((fgSubalgebraSpecDiagram R S).map f) :=
    fun {_ _} f ↦ inferInstance
  have hx : x.left ≫ (X ↘ Spec (.of K)) = (Spec (.of S) ↘ Spec (.of K)) := by
    simpa only [OverClass.asOver_hom] using x.w
  have hbase : (fgSubalgebraSpecCone R S).π ≫ fgSubalgebraSpecBase K =
      (Functor.const _).map (x.left ≫ (X ↘ Spec (.of K))) := by
    ext A
    exact (Scheme.specMap_subalgebra_val_comp K A.unop.1).trans hx.symm
  obtain ⟨A, g, hg, hgbase⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      (fgSubalgebraSpecDiagram R S) (fgSubalgebraSpecBase K) (X ↘ Spec (.of K))
      (fgSubalgebraSpecCone R S) (fgSubalgebraSpecIsLimit R S) x.left hbase
  refine ⟨A.unop.1, A.unop.2, Over.homMk g ?_, ?_⟩
  · exact hgbase
  · apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom A.unop.1.val.toRingHom) ≫ g = x.left
    exact hg

end ScalarTower

end AlgebraicGeometry
