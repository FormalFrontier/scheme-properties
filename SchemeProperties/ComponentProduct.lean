/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.ComponentBaseChange

public section

/-!
# Component schemes and binary products

This file constructs the functorial map on finite-etale component schemes and
the canonical comparison from the component scheme of a binary fibre product
to the fibre product of the component schemes, and proves that comparison is
an isomorphism.

Over a separably closed field, products of the connected-component
opens give the component-pair equivalence, with the empty scheme included.
Over an arbitrary field, the rank calculation is transported to a separable
closure; pullback preserves the cartesian product, and the component-
algebra rank formula identifies the two finite-etale algebras.

The public API uses the cartesian tensor product in `Over (Spec (.of K))`, whose
underlying scheme is definitionally the fibre product over `Spec K`.  All
schemes and rings remain in the same universe, and
no reducedness, connectedness, separatedness, or nonemptiness assumption is
made.

## References

- J. S. Milne, *Algebraic Groups* (2017), Proposition 1.30(b), together with
  the preceding component-scheme canonical-map paragraph: the canonical
  comparison identifies the component scheme of a binary fibre product over
  the field with the fibre product of the two component schemes.
-/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

noncomputable section

variable {K : Type u} [Field K]

local instance tensorLocallyOfFiniteType
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] : LocallyOfFiniteType (X ⊗ Y).hom := by
  rw [← (fst X Y).w]
  let _ : LocallyOfFiniteType (pullback.fst X.hom Y.hom) := inferInstance
  let _ : LocallyOfFiniteType (fst X Y).left := by
    change LocallyOfFiniteType (pullback.fst X.hom Y.hom)
    infer_instance
  infer_instance

local instance tensorQuasiCompact
    (X Y : Over (Spec (.of K))) [QuasiCompact X.hom]
    [QuasiCompact Y.hom] : QuasiCompact (X ⊗ Y).hom := by
  rw [← (fst X Y).w]
  let _ : QuasiCompact (pullback.fst X.hom Y.hom) := inferInstance
  let _ : QuasiCompact (fst X Y).left := by
    change QuasiCompact (pullback.fst X.hom Y.hom)
    infer_instance
  infer_instance

/-- The map on finite-etale component schemes induced by a morphism of
quasi-compact schemes locally of finite type over a field. -/
noncomputable def componentSchemeMapOfHom
    {X Y : Over (Spec (.of K))} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) : componentScheme X ⟶ componentScheme Y :=
  componentFactor X (componentSubalgebra_isFiniteEtale Y)
    (f ≫ toComponentScheme Y)

/-- The map on component schemes makes the canonical triangle commute. -/
@[reassoc]
theorem toComponentScheme_comp_componentSchemeMapOfHom
    {X Y : Over (Spec (.of K))} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) :
    toComponentScheme X ≫ componentSchemeMapOfHom f =
      f ≫ toComponentScheme Y :=
  toComponentScheme_comp_componentFactor X
    (componentSubalgebra_isFiniteEtale Y) (f ≫ toComponentScheme Y)

/-- The component-scheme map of an identity is the identity. -/
@[simp]
theorem componentSchemeMapOfHom_id
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    componentSchemeMapOfHom (𝟙 X) = 𝟙 (componentScheme X) := by
  apply (componentScheme_universal X (componentSubalgebra_isFiniteEtale X)
    (toComponentScheme X)).unique
  · simpa using toComponentScheme_comp_componentSchemeMapOfHom (𝟙 X)
  · simp

/-- Component-scheme maps preserve composition. -/
@[reassoc]
theorem componentSchemeMapOfHom_comp
    {X Y Z : Over (Spec (.of K))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    componentSchemeMapOfHom (f ≫ g) =
      componentSchemeMapOfHom f ≫ componentSchemeMapOfHom g := by
  apply (componentScheme_universal X (componentSubalgebra_isFiniteEtale Z)
    (f ≫ g ≫ toComponentScheme Z)).unique
  · simpa using toComponentScheme_comp_componentSchemeMapOfHom (f ≫ g)
  · rw [toComponentScheme_comp_componentSchemeMapOfHom_assoc,
      toComponentScheme_comp_componentSchemeMapOfHom]

/-- The canonical comparison from the component scheme of a binary product
to the binary product of the component schemes. It is the forward comparison
of J. S. Milne, *Algebraic Groups* (2017), Proposition 1.30(b), for the
fibre product over the base field. -/
noncomputable def componentProductComparison
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    componentScheme (X ⊗ Y) ⟶ componentScheme X ⊗ componentScheme Y :=
  lift (componentSchemeMapOfHom (fst X Y)) (componentSchemeMapOfHom (snd X Y))

/-- The product comparison is characterized by its canonical triangle with
the two product projections. This specifies the canonical comparison of
J. S. Milne, *Algebraic Groups* (2017), Proposition 1.30(b). -/
theorem toComponentScheme_comp_componentProductComparison
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    toComponentScheme (X ⊗ Y) ≫ componentProductComparison X Y =
      lift
        (fst X Y ≫ toComponentScheme X)
        (snd X Y ≫ toComponentScheme Y) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [componentProductComparison,
      toComponentScheme_comp_componentSchemeMapOfHom]
  · simp [componentProductComparison,
      toComponentScheme_comp_componentSchemeMapOfHom]

/-! ## Products of connected-component opens -/

local instance sourceCompactSpace (Z : Over (Spec (.of K)))
    [QuasiCompact Z.hom] : CompactSpace Z.left :=
  QuasiCompact.compactSpace_of_compactSpace Z.hom

local instance sourceIsLocallyNoetherian (Z : Over (Spec (.of K)))
    [LocallyOfFiniteType Z.hom] : IsLocallyNoetherian Z.left :=
  LocallyOfFiniteType.isLocallyNoetherian Z.hom

local instance sourceIsNoetherian (Z : Over (Spec (.of K)))
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] : IsNoetherian Z.left := ⟨⟩

private abbrev componentOpenOver (X : Over (Spec (.of K)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (c : ConnectedComponents X.left) : Over (Spec (.of K)) :=
  Over.mk ((X.left.connectedComponentOpen c).ι ≫ X.hom)

private def componentOpenιOver (X : Over (Spec (.of K)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (c : ConnectedComponents X.left) : componentOpenOver X c ⟶ X :=
  Over.homMk (X.left.connectedComponentOpen c).ι rfl

private theorem componentOpen_isClopen (X : Over (Spec (.of K)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (c : ConnectedComponents X.left) :
    IsClopen (X.left.connectedComponentOpen c : Set X.left) := by
  constructor
  · obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [X.left.connectedComponentOpen_mk x]
    exact isClosed_connectedComponent
  · obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [X.left.connectedComponentOpen_mk x]
    exact NoetherianSpace.isOpen_connectedComponent x

private def componentProductSet
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (p : ConnectedComponents X.left × ConnectedComponents Y.left) :
    Set (X ⊗ Y).left :=
  (fst X Y).left ⁻¹' (X.left.connectedComponentOpen p.1 : Set X.left) ∩
    (snd X Y).left ⁻¹' (Y.left.connectedComponentOpen p.2 : Set Y.left)

private theorem componentProductSet_isClopen
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (p : ConnectedComponents X.left × ConnectedComponents Y.left) :
    IsClopen (componentProductSet X Y p) :=
  (componentOpen_isClopen X p.1).preimage (fst X Y).left.continuous |>.inter
    ((componentOpen_isClopen Y p.2).preimage (snd X Y).left.continuous)

private theorem componentProductSet_pairwise
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    Pairwise (Function.onFun Disjoint (componentProductSet X Y)) := by
  rintro p q hpq
  change Disjoint (componentProductSet X Y p) (componentProductSet X Y q)
  rw [Set.disjoint_left]
  intro z hzp hzq
  apply hpq
  apply Prod.ext
  · exact ((X.left.mem_connectedComponentOpen _ _).mp hzp.1).symm.trans
      ((X.left.mem_connectedComponentOpen _ _).mp hzq.1)
  · exact ((Y.left.mem_connectedComponentOpen _ _).mp hzp.2).symm.trans
      ((Y.left.mem_connectedComponentOpen _ _).mp hzq.2)

private theorem iUnion_componentProductSet
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    ⋃ p, componentProductSet X Y p = Set.univ := by
  apply Set.iUnion_eq_univ_iff.mpr
  intro z
  refine ⟨(ConnectedComponents.mk ((fst X Y).left z),
    ConnectedComponents.mk ((snd X Y).left z)), ?_⟩
  constructor
  · exact (X.left.mem_connectedComponentOpen _ _).mpr rfl
  · exact (Y.left.mem_connectedComponentOpen _ _).mpr rfl

private theorem componentProductSet_eq_range
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (p : ConnectedComponents X.left × ConnectedComponents Y.left) :
    componentProductSet X Y p = Set.range
      ((componentOpenιOver X p.1 ⊗ₘ componentOpenιOver Y p.2).left) := by
  rw [Over.tensorHom_left, Scheme.Pullback.range_map]
  change componentProductSet X Y p =
    (pullback.fst X.hom Y.hom) ⁻¹'
        Set.range (X.left.connectedComponentOpen p.1).ι ∩
      (pullback.snd X.hom Y.hom) ⁻¹'
        Set.range (Y.left.connectedComponentOpen p.2).ι
  rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
  rfl

private theorem componentProductSet_isConnected [IsSepClosed K]
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (p : ConnectedComponents X.left × ConnectedComponents Y.left) :
    _root_.IsConnected (componentProductSet X Y p) := by
  let _ : LocallyOfFiniteType (componentOpenOver X p.1).hom := by
    dsimp only [componentOpenOver, Over.mk_hom]
    infer_instance
  let _ : LocallyOfFiniteType (componentOpenOver Y p.2).hom := by
    dsimp only [componentOpenOver, Over.mk_hom]
    infer_instance
  let _ : ConnectedSpace (componentOpenOver X p.1).left := by
    change ConnectedSpace (X.left.connectedComponentOpen p.1)
    infer_instance
  let _ : ConnectedSpace (componentOpenOver Y p.2).left := by
    change ConnectedSpace (Y.left.connectedComponentOpen p.2)
    infer_instance
  let _ : GeometricallyConnected (componentOpenOver X p.1).hom :=
    geometricallyConnected_of_isSepClosed (k := K) _
  let _ : ConnectedSpace
      ((componentOpenOver X p.1 ⊗ componentOpenOver Y p.2).left) := by
    rw [Over.tensorObj_left]
    infer_instance
  rw [componentProductSet_eq_range X Y p]
  exact isConnected_range
    (componentOpenιOver X p.1 ⊗ₘ componentOpenιOver Y p.2).left.continuous

private noncomputable def componentProductEquiv [IsSepClosed K]
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    ConnectedComponents (X ⊗ Y).left ≃
      ConnectedComponents X.left × ConnectedComponents Y.left :=
  ConnectedComponents.equivOfIsClopenOfIsConnected
    (componentProductSet_isClopen X Y) (componentProductSet_pairwise X Y)
      (iUnion_componentProductSet X Y) (componentProductSet_isConnected X Y)

/-- The component equivalence records the two projection labels. -/
private theorem componentProductEquiv_mk [IsSepClosed K]
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (z : (X ⊗ Y).left) :
    componentProductEquiv X Y (ConnectedComponents.mk z) =
      (ConnectedComponents.mk ((fst X Y).left z),
        ConnectedComponents.mk ((snd X Y).left z)) := by
  apply ConnectedComponents.equivOfIsClopenOfIsConnected_mk
  constructor
  · exact (X.left.mem_connectedComponentOpen _ _).mpr rfl
  · exact (Y.left.mem_connectedComponentOpen _ _).mpr rfl

/-! ## The affine tensor-product model -/

private abbrev componentProductModel
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :=
  specOver K (componentSubalgebra X ⊗[K] componentSubalgebra Y)

private noncomputable def componentProductModelIso
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    componentScheme X ⊗ componentScheme Y ≅ componentProductModel X Y :=
  Over.isoMk (pullbackSpecIso K (componentSubalgebra X)
    (componentSubalgebra Y)) (by
      rw [Over.tensorObj_hom]
      change (pullbackSpecIso K (componentSubalgebra X)
          (componentSubalgebra Y)).hom ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap K (componentSubalgebra X ⊗[K] componentSubalgebra Y))) = _
      rw [show Spec.map (CommRingCat.ofHom
          (algebraMap K (componentSubalgebra X ⊗[K] componentSubalgebra Y))) =
        Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeftRingHom :
              componentSubalgebra X →+* _)) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap K (componentSubalgebra X))) by
          rw [← Spec.map_comp]
          rfl]
      rw [← Category.assoc, pullbackSpecIso_hom_fst]
      rfl)

private theorem componentProductModel_isFiniteEtale
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    Algebra.IsFiniteEtale K
      (componentSubalgebra X ⊗[K] componentSubalgebra Y) := by
  let _ : Module.Finite K (componentSubalgebra X) :=
    (componentSubalgebra_isFiniteEtale X).1
  let _ : Algebra.Etale K (componentSubalgebra X) :=
    (componentSubalgebra_isFiniteEtale X).2
  let _ : Module.Finite K (componentSubalgebra Y) :=
    (componentSubalgebra_isFiniteEtale Y).1
  let _ : Algebra.Etale K (componentSubalgebra Y) :=
    (componentSubalgebra_isFiniteEtale Y).2
  let _ : Algebra (componentSubalgebra X)
      (componentSubalgebra X ⊗[K] componentSubalgebra Y) :=
    Algebra.TensorProduct.leftAlgebra
  let _ : Algebra.Etale (componentSubalgebra X)
      (componentSubalgebra X ⊗[K] componentSubalgebra Y) := inferInstance
  let _ : IsScalarTower K (componentSubalgebra X)
      (componentSubalgebra X ⊗[K] componentSubalgebra Y) := inferInstance
  exact ⟨inferInstance, Algebra.Etale.comp K (componentSubalgebra X) _⟩

private noncomputable def productToModel
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    X ⊗ Y ⟶ componentProductModel X Y :=
  (toComponentScheme X ⊗ₘ toComponentScheme Y) ≫
    (componentProductModelIso X Y).hom

private theorem tensor_toComponentScheme_surjective
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    Function.Surjective (toComponentScheme X ⊗ₘ toComponentScheme Y).left := by
  rw [← Set.range_eq_univ, Over.tensorHom_left, Scheme.Pullback.range_map]
  have hX : Set.range (toComponentScheme X).left = Set.univ :=
    Set.range_eq_univ.mpr (surjective_toComponentScheme X).surj
  have hY : Set.range (toComponentScheme Y).left = Set.univ :=
    Set.range_eq_univ.mpr (surjective_toComponentScheme Y).surj
  rw [hX, hY]
  simp

private theorem productToModel_surjective
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    Function.Surjective (productToModel X Y).left := by
  change Function.Surjective
    ((componentProductModelIso X Y).hom.left ∘
      (toComponentScheme X ⊗ₘ toComponentScheme Y).left)
  exact (Scheme.homeoOfIso ((Over.forget _).mapIso
      (componentProductModelIso X Y))).surjective.comp
    (tensor_toComponentScheme_surjective X Y)

private theorem productComparison_model_triangle
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    toComponentScheme (X ⊗ Y) ≫
        (componentProductComparison X Y ≫
          (componentProductModelIso X Y).hom) =
      productToModel X Y := by
  rw [← Category.assoc,
    toComponentScheme_comp_componentProductComparison]
  apply congrArg (fun f ↦ f ≫ (componentProductModelIso X Y).hom)
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · simp

private theorem componentProductComparison_model_eq_factor
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    componentProductComparison X Y ≫ (componentProductModelIso X Y).hom =
      componentFactor (X ⊗ Y) (componentProductModel_isFiniteEtale X Y)
        (productToModel X Y) := by
  apply (componentScheme_universal (X ⊗ Y)
    (componentProductModel_isFiniteEtale X Y) (productToModel X Y)).unique
  · exact productComparison_model_triangle X Y
  · exact toComponentScheme_comp_componentFactor (X ⊗ Y)
      (componentProductModel_isFiniteEtale X Y) (productToModel X Y)

private theorem algebraMapOfProductToModel_injective
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    Function.Injective
      (algebraMapOfToSpec (X ⊗ Y) (productToModel X Y)) := by
  let A := componentSubalgebra X ⊗[K] componentSubalgebra Y
  let hA := componentProductModel_isFiniteEtale X Y
  let _ : Module.Finite K A := hA.1
  let _ : Algebra.Etale K A := hA.2
  let _ : _root_.IsReduced A :=
    Algebra.FormallyUnramified.isReduced_of_field K A
  let f := (productToModel X Y).left
  let _ : IsReduced (componentProductModel X Y).left := by
    change IsReduced (Spec (.of A))
    infer_instance
  let _ : QuasiSeparatedSpace (componentProductModel X Y).left := by
    change QuasiSeparatedSpace (Spec (.of A))
    infer_instance
  let _ : Surjective f := ⟨productToModel_surjective X Y⟩
  let _ : IsSchemeTheoreticallyDominant f :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  have hf : Function.Injective f.appTop := Scheme.Hom.app_injective f ⊤
  intro a b hab
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of A)).inv).injective
  apply hf
  exact hab

private theorem productFactorAlgHom_injective
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    Function.Injective
      (componentFactorAlgHom (X ⊗ Y)
        (componentProductModel_isFiniteEtale X Y) (productToModel X Y)) := by
  intro a b hab
  apply algebraMapOfProductToModel_injective X Y
  exact congrArg Subtype.val hab

private theorem productFactorAlgHom_surjective_of_isSepClosed [IsSepClosed K]
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    Function.Surjective
      (componentFactorAlgHom (X ⊗ Y)
        (componentProductModel_isFiniteEtale X Y) (productToModel X Y)) := by
  let A := componentSubalgebra X
  let B := componentSubalgebra Y
  let C := componentSubalgebra (X ⊗ Y)
  let f := componentFactorAlgHom (X ⊗ Y)
    (componentProductModel_isFiniteEtale X Y) (productToModel X Y)
  let _ : Module.Finite K A := (componentSubalgebra_isFiniteEtale X).1
  let _ : Module.Finite K B := (componentSubalgebra_isFiniteEtale Y).1
  let _ : Module.Finite K C := (componentSubalgebra_isFiniteEtale (X ⊗ Y)).1
  have hfinrank : Module.finrank K (A ⊗[K] B) = Module.finrank K C := by
    rw [Module.finrank_tensorProduct,
      componentSubalgebra_finrank_eq_natCard_connectedComponents X,
      componentSubalgebra_finrank_eq_natCard_connectedComponents Y,
      componentSubalgebra_finrank_eq_natCard_connectedComponents (X ⊗ Y),
      ← Nat.card_prod]
    exact (Nat.card_congr (componentProductEquiv X Y)).symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := f.toLinearMap) hfinrank).mp (productFactorAlgHom_injective X Y)

private noncomputable def productFactorAlgEquivOfIsSepClosed [IsSepClosed K]
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    componentSubalgebra X ⊗[K] componentSubalgebra Y ≃ₐ[K]
      componentSubalgebra (X ⊗ Y) :=
  AlgEquiv.ofBijective
    (componentFactorAlgHom (X ⊗ Y)
      (componentProductModel_isFiniteEtale X Y) (productToModel X Y))
    ⟨productFactorAlgHom_injective X Y,
      productFactorAlgHom_surjective_of_isSepClosed X Y⟩

private noncomputable def specOverIsoOfAlgEquiv
    {A B : Type u} [CommRing A] [Algebra K A]
    [CommRing B] [Algebra K B] (e : A ≃ₐ[K] B) :
    specOver K B ≅ specOver K A :=
  Over.isoMk (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op) (by
    change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K A)) =
      Spec.map (CommRingCat.ofHom (algebraMap K B))
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact e.commutes x)

private theorem specOverIsoOfAlgEquiv_hom
    {A B : Type u} [CommRing A] [Algebra K A]
    [CommRing B] [Algebra K B] (e : A ≃ₐ[K] B) :
    (specOverIsoOfAlgEquiv e).hom = specOverMap e.toAlgHom := rfl

private noncomputable def componentProductIsoOfIsSepClosed [IsSepClosed K]
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    componentScheme (X ⊗ Y) ≅ componentScheme X ⊗ componentScheme Y :=
  (specOverIsoOfAlgEquiv (productFactorAlgEquivOfIsSepClosed X Y)).trans
    (componentProductModelIso X Y).symm

private theorem componentProductIsoOfIsSepClosed_hom [IsSepClosed K]
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    (componentProductIsoOfIsSepClosed X Y).hom =
      componentProductComparison X Y := by
  rw [componentProductIsoOfIsSepClosed, Iso.trans_hom,
    specOverIsoOfAlgEquiv_hom]
  change componentFactor (X ⊗ Y) (componentProductModel_isFiniteEtale X Y)
      (productToModel X Y) ≫ (componentProductModelIso X Y).inv = _
  rw [← componentProductComparison_model_eq_factor X Y,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-! ## Passage back to the ground field -/

local instance baseChangeLocallyOfFiniteTypeProduct
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] :
    LocallyOfFiniteType (schemeBaseChange X (L := L)).hom := by
  change LocallyOfFiniteType
    (pullback.snd X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k L))))
  infer_instance

local instance baseChangeQuasiCompactProduct
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    (X : Over (Spec (.of k))) [QuasiCompact X.hom] :
    QuasiCompact (schemeBaseChange X (L := L)).hom := by
  change QuasiCompact
    (pullback.snd X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k L))))
  infer_instance

/-- Pullback along a field extension preserves the chosen cartesian product
in the over category. -/
private noncomputable def baseChangeTensorIso
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    (X Y : Over (Spec (.of k))) :
    schemeBaseChange (X ⊗ Y) (L := L) ≅
      schemeBaseChange X (L := L) ⊗ schemeBaseChange Y (L := L) := by
  let g : Spec (.of L) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k L))
  exact prodComparisonIso (Over.pullback g) X Y

private noncomputable def connectedComponentsEquivOfSchemeIso
    {X Y : Scheme.{u}} (e : X ≅ Y) :
    ConnectedComponents X ≃ ConnectedComponents Y where
  toFun := (Scheme.homeoOfIso e).continuous.connectedComponentsMap
  invFun := (Scheme.homeoOfIso e).symm.continuous.connectedComponentsMap
  left_inv c := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    simp
  right_inv c := by
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
    simp

private theorem productFactorAlgHom_surjective
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    Function.Surjective
      (componentFactorAlgHom (X ⊗ Y)
        (componentProductModel_isFiniteEtale X Y) (productToModel X Y)) := by
  let L := SeparableClosure K
  let XL := schemeBaseChange X (L := L)
  let YL := schemeBaseChange Y (L := L)
  let P := X ⊗ Y
  let PL := schemeBaseChange P (L := L)
  let e : PL ≅ XL ⊗ YL := baseChangeTensorIso X Y
  let eScheme : PL.left ≅ (XL ⊗ YL).left :=
    (Over.forget (Spec (.of L))).mapIso e
  have hcard : Nat.card (ConnectedComponents PL.left) =
      Nat.card (ConnectedComponents XL.left) *
        Nat.card (ConnectedComponents YL.left) := by
    calc
      Nat.card (ConnectedComponents PL.left) =
          Nat.card (ConnectedComponents (XL ⊗ YL).left) :=
        Nat.card_congr (connectedComponentsEquivOfSchemeIso eScheme)
      _ = Nat.card
          (ConnectedComponents XL.left × ConnectedComponents YL.left) :=
        Nat.card_congr (componentProductEquiv XL YL)
      _ = Nat.card (ConnectedComponents XL.left) *
          Nat.card (ConnectedComponents YL.left) := Nat.card_prod _ _
  let A := componentSubalgebra X
  let B := componentSubalgebra Y
  let C := componentSubalgebra P
  let f := componentFactorAlgHom P
    (componentProductModel_isFiniteEtale X Y) (productToModel X Y)
  let _ : Module.Finite K A := (componentSubalgebra_isFiniteEtale X).1
  let _ : Module.Finite K B := (componentSubalgebra_isFiniteEtale Y).1
  let _ : Module.Finite K C := (componentSubalgebra_isFiniteEtale P).1
  have hfinrank : Module.finrank K (A ⊗[K] B) = Module.finrank K C := by
    rw [Module.finrank_tensorProduct,
      componentSubalgebra_finrank_eq_natCard_separableClosure X,
      componentSubalgebra_finrank_eq_natCard_separableClosure Y,
      componentSubalgebra_finrank_eq_natCard_separableClosure P]
    exact hcard.symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := f.toLinearMap) hfinrank).mp (productFactorAlgHom_injective X Y)

private noncomputable def productFactorAlgEquiv
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    componentSubalgebra X ⊗[K] componentSubalgebra Y ≃ₐ[K]
      componentSubalgebra (X ⊗ Y) :=
  AlgEquiv.ofBijective
    (componentFactorAlgHom (X ⊗ Y)
      (componentProductModel_isFiniteEtale X Y) (productToModel X Y))
    ⟨productFactorAlgHom_injective X Y, productFactorAlgHom_surjective X Y⟩

/-- The canonical component scheme of a binary fibre product is the fibre
product of the component schemes, as in J. S. Milne, *Algebraic Groups*
(2017), Proposition 1.30(b). -/
noncomputable def componentProductIso
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    componentScheme (X ⊗ Y) ≅ componentScheme X ⊗ componentScheme Y :=
  (specOverIsoOfAlgEquiv (productFactorAlgEquiv X Y)).trans
    (componentProductModelIso X Y).symm

/-- The forward map of `componentProductIso` is exactly the canonical product
comparison of J. S. Milne, *Algebraic Groups* (2017), Proposition 1.30(b). -/
theorem componentProductIso_hom
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    (componentProductIso X Y).hom = componentProductComparison X Y := by
  rw [componentProductIso, Iso.trans_hom, specOverIsoOfAlgEquiv_hom]
  change componentFactor (X ⊗ Y) (componentProductModel_isFiniteEtale X Y)
      (productToModel X Y) ≫ (componentProductModelIso X Y).inv = _
  rw [← componentProductComparison_model_eq_factor X Y,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

end

end AlgebraicGeometry

#lint- only unusedArguments docBlame
