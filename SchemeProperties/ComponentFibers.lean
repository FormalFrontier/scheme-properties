/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.ComponentBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

public section

/-!
# Fibres of the component scheme

For a quasi-compact scheme locally of finite type over a field, the fibres of
the canonical map to its finite-etale component scheme are precisely its
connected components and are geometrically connected over their residue
fields.

Consequently, a connected such scheme whose structure morphism has a section
is geometrically connected over the base field.

The fibre statements use the scheme-theoretic residue-field fibre and impose
no reducedness, separatedness, connectedness, nonemptiness, or rational-point
hypothesis on the source. The whole-scheme consequence assumes only
connectedness and the displayed section in addition to the finiteness
hypotheses of the component construction.

The geometric-connectedness proof uses component-scheme base change first and
then derives the fibre's component-algebra identity. Milne's proof instead
uses that identity to obtain geometric connectedness.

## References

- J. S. Milne, *Algebraic Groups* (2017), Proposition 1.31(a,b): the
  scheme-theoretic fibres over points of the component scheme are connected
  components and are geometrically connected over the corresponding residue
  fields. The proof here also uses the canonical base-change comparison for
  component schemes.
- J. S. Milne, *Algebraic Groups* (2017), Corollary 1.32(a): the
  geometric-connectedness conclusion for a connected finite-type scheme with
  a rational point, expressed here as a section over the base field.
-/

set_option warningAsError true

open CategoryTheory Limits Opposite Set Topology TopologicalSpace

universe u

namespace AlgebraicGeometry

noncomputable section

variable {K : Type u} [Field K]

/-- The scalar algebra structure on global sections used by the component
construction. -/
local instance componentFibersGlobalSectionsAlgebra
    {F : Type u} [Field F] (X : Over (Spec (.of F))) :
    Algebra F Γ(X.left, ⊤) :=
  X.hom.globalSectionsAlgebra F

/-- The split finite-etale quotient by connected components separates two
points exactly when they belong to distinct connected components. -/
private theorem toConnectedComponentsSpec_apply_eq_iff
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (x y : X.left) :
    (toConnectedComponentsSpec X).left x =
        (toConnectedComponentsSpec X).left y ↔
      ConnectedComponents.mk x = ConnectedComponents.mk y := by
  let _ : CompactSpace X.left :=
    QuasiCompact.compactSpace_of_compactSpace X.hom
  let _ : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.hom
  let _ : IsNoetherian X.left := ⟨⟩
  let S := fun _ : ConnectedComponents X.left ↦ Spec (.of K)
  let q := X.left.toConnectedComponentCoproduct X.hom
  have hq (z : X.left) :
      q z = Sigma.ι S (ConnectedComponents.mk z) (X.hom z) := by
    let c := ConnectedComponents.mk z
    let zc : X.left.connectedComponentOpen c :=
      ⟨z, X.left.mem_connectedComponentOpen c z |>.mpr rfl⟩
    have h := congrArg
      (fun f : (X.left.connectedComponentOpen c).toScheme ⟶ ∐ S ↦ f zc)
      (X.left.connectedComponentOpen_ι_toConnectedComponentCoproduct X.hom c)
    exact h
  constructor
  · intro h
    have hsigma : q x = q y := by
      exact (sigmaSpec
        (fun _ : ConnectedComponents X.left ↦ .of K)).homeomorph.injective h
    rw [hq x, hq y, ← sigmaMk_mk, ← sigmaMk_mk] at hsigma
    exact (Sigma.mk.inj_iff.mp ((sigmaMk S).injective hsigma)).1
  · intro h
    apply congrArg
      (sigmaSpec (fun _ : ConnectedComponents X.left ↦ .of K))
    change q x = q y
    rw [hq x, hq y, ← sigmaMk_mk, ← sigmaMk_mk]
    apply congrArg (sigmaMk S)
    apply Sigma.ext h
    exact heq_of_eq (Subsingleton.elim (X.hom x) (X.hom y))

/-- The underlying range of the scheme-theoretic fibre of the canonical map
to the component scheme is the connected component containing any point that
maps to the chosen target point. This is J. S. Milne, *Algebraic Groups*
(2017), Proposition 1.31(a); the point must map to the specified component
point. -/
theorem range_fiberι_toComponentScheme_eq_connectedComponent
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (x : (componentScheme X).left)
    (y : X.left) (hy : (toComponentScheme X).left y = x) :
    Set.range ((toComponentScheme X).left.fiberι x) =
      connectedComponent y := by
  let _ : CompactSpace X.left :=
    QuasiCompact.compactSpace_of_compactSpace X.hom
  let _ : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.hom
  let _ : IsNoetherian X.left := ⟨⟩
  let C := ConnectedComponents X.left → K
  have hC : Algebra.IsFiniteEtale K C := ⟨inferInstance, inferInstance⟩
  let g := componentFactor X hC (toConnectedComponentsSpec X)
  have htriangle : toComponentScheme X ≫ g =
      toConnectedComponentsSpec X :=
    toComponentScheme_comp_componentFactor X hC (toConnectedComponentsSpec X)
  have hinj : Function.Injective g.left := by
    intro a b hab
    obtain ⟨a', ha'⟩ := (surjective_toComponentScheme X).surj a
    obtain ⟨b', hb'⟩ := (surjective_toComponentScheme X).surj b
    have hcc : ConnectedComponents.mk a' = ConnectedComponents.mk b' := by
      apply (toConnectedComponentsSpec_apply_eq_iff X a' b').mp
      rw [← htriangle]
      change g.left ((toComponentScheme X).left a') =
        g.left ((toComponentScheme X).left b')
      simpa [ha', hb'] using hab
    have ht : (toComponentScheme X).left a' =
        (toComponentScheme X).left b' := by
      let _ : Module.Finite K (componentSubalgebra X) :=
        (componentSubalgebra_isFiniteEtale X).1
      let _ : Algebra.Etale K (componentSubalgebra X) :=
        (componentSubalgebra_isFiniteEtale X).2
      let _ : DiscreteTopology (componentScheme X).left := by
        change DiscreteTopology (Spec (.of (componentSubalgebra X)))
        exact Algebra.QuasiFinite.discreteTopology_primeSpectrum K
          (componentSubalgebra X)
      have himage : _root_.IsPreconnected
          ((toComponentScheme X).left '' connectedComponent a') :=
        isPreconnected_connectedComponent.image _
          (toComponentScheme X).left.continuous.continuousOn
      apply himage.subsingleton
      · exact ⟨a', mem_connectedComponent, rfl⟩
      · refine ⟨b', ?_, rfl⟩
        exact connectedComponent_eq_iff_mem.mp
          (ConnectedComponents.coe_eq_coe.mp hcc).symm
    exact ha'.symm.trans (ht.trans hb')
  rw [(toComponentScheme X).left.range_fiberι]
  ext z
  rw [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hz
    apply connectedComponent_eq_iff_mem.mp
    apply ConnectedComponents.coe_eq_coe.mp
    apply (toConnectedComponentsSpec_apply_eq_iff X z y).mp
    rw [← htriangle]
    change g.left ((toComponentScheme X).left z) =
      g.left ((toComponentScheme X).left y)
    rw [hz, hy]
  · intro hz
    have hconn : ConnectedComponents.mk z = ConnectedComponents.mk y :=
      ConnectedComponents.coe_eq_coe.mpr
        (connectedComponent_eq_iff_mem.mpr hz)
    have hf : (toConnectedComponentsSpec X).left z =
        (toConnectedComponentsSpec X).left y :=
      (toConnectedComponentsSpec_apply_eq_iff X z y).mpr hconn
    rw [← htriangle] at hf
    change g.left ((toComponentScheme X).left z) =
      g.left ((toComponentScheme X).left y) at hf
    rw [hy] at hf
    exact hinj hf

/-- A scheme-theoretic fibre of the component map is connected. -/
private theorem connectedSpace_fiber_toComponentScheme
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (x : (componentScheme X).left) :
    ConnectedSpace ((toComponentScheme X).left.fiber x) := by
  obtain ⟨y, hy⟩ := (surjective_toComponentScheme X).surj x
  rw [((toComponentScheme X).left.fiberHomeo x).connectedSpace_iff]
  apply Subtype.connectedSpace
  rw [← (toComponentScheme X).left.range_fiberι,
    range_fiberι_toComponentScheme_eq_connectedComponent X x y hy]
  exact isConnected_connectedComponent

/-- The canonical map to the component scheme is locally of finite type. -/
instance toComponentSchemeLocallyOfFiniteType
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] : LocallyOfFiniteType (toComponentScheme X).left := by
  have h := (toComponentScheme X).w
  let _ : LocallyOfFiniteType
      ((toComponentScheme X).left ≫ (componentScheme X).hom) :=
    h.symm ▸ inferInstance
  exact locallyOfFiniteType_of_comp _ (componentScheme X).hom

/-- The canonical map to the component scheme is quasi-compact. -/
instance toComponentSchemeQuasiCompact
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] : QuasiCompact (toComponentScheme X).left := by
  let _ : CompactSpace X.left :=
    QuasiCompact.compactSpace_of_compactSpace X.hom
  let _ : IsAffine (componentScheme X).left := by
    change IsAffine (Spec (.of (componentSubalgebra X)))
    infer_instance
  let _ : QuasiSeparatedSpace (componentScheme X).left := inferInstance
  infer_instance

/-- The scheme-theoretic fibre of the component map, regarded over the
residue field of the selected component point. -/
@[expose]
def componentSchemeFiber
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (x : (componentScheme X).left) :
    Over (Spec ((componentScheme X).left.residueField x)) :=
  Over.mk ((toComponentScheme X).left.fiberToSpecResidueField x)

/-- A component-scheme fibre is locally of finite type over its residue
field. -/
instance fiberToComponentSchemeLocallyOfFiniteType
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (x : (componentScheme X).left) :
    LocallyOfFiniteType (componentSchemeFiber X x).hom := by
  change LocallyOfFiniteType (pullback.snd (toComponentScheme X).left
    ((componentScheme X).left.fromSpecResidueField x))
  infer_instance

/-- A component-scheme fibre is quasi-compact over its residue field. -/
instance fiberToComponentSchemeQuasiCompact
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (x : (componentScheme X).left) :
    QuasiCompact (componentSchemeFiber X x).hom := by
  change QuasiCompact (pullback.snd (toComponentScheme X).left
    ((componentScheme X).left.fromSpecResidueField x))
  infer_instance

/-- A surjective etale map of affine coordinate rings induces an open
immersion on spectra. -/
private theorem isOpenImmersion_specMap_of_etale_of_surjective
    {A E : Type u} [CommRing A] [Field E] (f : A →+* E)
    (hf : Function.Surjective f) (het : f.Etale) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom f)) := by
  let _ : Algebra A E := f.toAlgebra
  let _ : Algebra.Etale A E := het
  rw [isOpenImmersion_SpecMap_iff_of_surjective _ hf]
  apply (Ideal.isIdempotentElem_iff_of_fg _
    (Algebra.FinitePresentation.ker_fG_of_surjective
      (Algebra.ofId A E) hf)).mp
  exact (Algebra.FormallyEtale.iff_of_surjective hf).mp inferInstance

/-- A section of an etale map between affine spectra, with field source, is an
open immersion. -/
private theorem isOpenImmersion_of_etale_of_section
    {A E : Type u} [CommRing A] [Field E]
    (q : Spec (.of E) ⟶ Spec (.of A))
    (g : Spec (.of A) ⟶ Spec (.of E))
    [Etale q] (hq : q ≫ g = 𝟙 _) : IsOpenImmersion q := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective q
  have hφsurj : Function.Surjective φ.hom := by
    intro z
    let ψ := Spec.preimage g
    refine ⟨ψ.hom z, ?_⟩
    have hmaps : ψ ≫ φ = 𝟙 _ := by
      apply Spec.map_injective
      rw [Spec.map_comp, hφ]
      rw [Spec.map_preimage, hq]
      simp
    exact congrArg (fun r : CommRingCat.of E ⟶ CommRingCat.of E ↦ r.hom z) hmaps
  have hφetale : φ.hom.Etale := by
    rw [← HasRingHomProperty.Spec_iff (P := @Etale)]
    rw [hφ]
    infer_instance
  rw [← hφ]
  exact isOpenImmersion_specMap_of_etale_of_surjective φ.hom hφsurj hφetale

/-- Pulling the component map back along a field-valued open point produces a
connected scheme. -/
private theorem connectedSpace_pullback_toComponentScheme
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] {E : Type u} [Field E]
    (q : Spec (.of E) ⟶ (componentScheme X).left) [IsOpenImmersion q] :
    ConnectedSpace ↥(Limits.pullback (toComponentScheme X).left q) := by
  let x := q (IsLocalRing.closedPoint E)
  obtain ⟨y, hy⟩ := (surjective_toComponentScheme X).surj x
  rw [(pullback.fst (toComponentScheme X).left q).isOpenEmbedding.isEmbedding.toHomeomorph
    |>.connectedSpace_iff]
  apply Subtype.connectedSpace
  rw [Scheme.Pullback.range_fst]
  have hq : Set.range q = {x} := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact Set.mem_singleton_iff.mpr (congrArg q (Subsingleton.elim _ _))
    · intro hz
      exact ⟨IsLocalRing.closedPoint E, Set.mem_singleton_iff.mp hz |>.symm⟩
  rw [hq, ← (toComponentScheme X).left.range_fiberι,
    range_fiberι_toComponentScheme_eq_connectedComponent X x y hy]
  exact isConnected_connectedComponent

/-- A scheme-theoretic fibre of the component map is geometrically connected
over its residue field, as in J. S. Milne, *Algebraic Groups* (2017),
Proposition 1.31(b). -/
theorem geometricallyConnected_fiber_toComponentScheme
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (x : (componentScheme X).left) :
    GeometricallyConnected
      ((toComponentScheme X).left.fiberToSpecResidueField x) := by
  let C := componentScheme X
  let f := (toComponentScheme X).left
  let L := C.left.residueField x
  let a : CommRingCat.of K ⟶ CommRingCat.of L :=
    Spec.preimage (C.left.fromSpecResidueField x ≫ C.hom)
  refine ⟨?_⟩
  rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro E _ hLE
  let _ : Algebra L E := hLE
  let _ : Algebra K E := ((algebraMap L E).comp a.hom).toAlgebra
  let XL := schemeBaseChange X (L := E)
  let CE := schemeBaseChange C (L := E)
  let _ : LocallyOfFiniteType XL.hom := by
    change LocallyOfFiniteType
      (pullback.snd X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap K E))))
    infer_instance
  let _ : QuasiCompact XL.hom := by
    change QuasiCompact
      (pullback.snd X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap K E))))
    infer_instance
  let gLE := Spec.map (CommRingCat.ofHom (algebraMap L E))
  let gKE := Spec.map (CommRingCat.ofHom (algebraMap K E))
  let q₀ : Spec (.of E) ⟶ pullback C.hom gKE := pullback.lift
    (gLE ≫ C.left.fromSpecResidueField x) (𝟙 _) (by
      dsimp only [gLE, gKE, a]
      rw [Category.assoc, ← Spec.map_preimage
        (C.left.fromSpecResidueField x ≫ C.hom)]
      simp only [← Spec.map_comp, Category.id_comp]
      rfl)
  let e := componentBaseChangeIso (K := E) X
  let q : Spec (.of E) ⟶ (componentScheme XL).left := q₀ ≫ e.inv.left
  have hq₀ : q₀ ≫ CE.hom = 𝟙 _ := by
    exact pullback.lift_snd _ _ _
  have hq : q ≫ (componentScheme XL).hom = 𝟙 _ := by
    dsimp only [q]
    rw [Category.assoc, e.inv.w]
    exact hq₀
  let A := componentSubalgebra XL
  let _ : Module.Finite E A := (componentSubalgebra_isFiniteEtale XL).1
  let _ : Algebra.Etale E A := (componentSubalgebra_isFiniteEtale XL).2
  have hpEtale : Etale (componentScheme XL).hom := by
    change Etale (Spec.map (CommRingCat.ofHom (algebraMap E A)))
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  let _ : Etale (componentScheme XL).hom := hpEtale
  have hcompEtale : Etale (q ≫ (componentScheme XL).hom) := by
    rw [hq]
    infer_instance
  let _ : Etale (q ≫ (componentScheme XL).hom) := hcompEtale
  have hqEtale : Etale q := Etale.of_comp q (componentScheme XL).hom
  let _ : Etale q := hqEtale
  obtain ⟨φ, hφ⟩ := Spec.map_surjective q
  have hφsurj : Function.Surjective φ.hom := by
    intro z
    let ψ := Spec.preimage (componentScheme XL).hom
    refine ⟨ψ.hom z, ?_⟩
    have hmaps : ψ ≫ φ = 𝟙 _ := by
      apply Spec.map_injective
      rw [Spec.map_comp, hφ]
      rw [Spec.map_preimage, hq]
      simp
    exact congrArg (fun r : CommRingCat.of E ⟶ CommRingCat.of E ↦ r.hom z) hmaps
  have hφetale : φ.hom.Etale := by
    rw [← HasRingHomProperty.Spec_iff (P := @Etale)]
    rw [hφ]
    exact hqEtale
  have hqOpen : IsOpenImmersion q := by
    rw [← hφ]
    exact isOpenImmersion_specMap_of_etale_of_surjective φ.hom hφsurj hφetale
  let _ : IsOpenImmersion q := hqOpen
  let Z := pullback (f.fiberToSpecResidueField x) gLE
  let j : Z ⟶ pullback X.hom gKE := pullback.lift
    (pullback.fst (f.fiberToSpecResidueField x) gLE ≫ f.fiberι x)
    (pullback.snd (f.fiberToSpecResidueField x) gLE) (by
      rw [← (toComponentScheme X).w, Category.assoc, f.fiber_fac_assoc,
        pullback.condition_assoc]
      dsimp only [gLE, a]
      rw [← Spec.map_preimage (C.left.fromSpecResidueField x ≫ C.hom)]
      simp only [← Spec.map_comp]
      rfl)
  have hj_fst : j ≫ pullback.fst X.hom gKE =
      pullback.fst (f.fiberToSpecResidueField x) gLE ≫ f.fiberι x := by
    exact pullback.lift_fst _ _ _
  let m := (baseChangeMap (L := E) (toComponentScheme X)).left
  have hm_fst : m ≫ pullback.fst C.hom gKE =
      pullback.fst X.hom gKE ≫ f := by
    change (pullback.lift _ _ _) ≫ pullback.fst C.hom gKE = _
    rw [pullback.lift_fst]
  have hm_snd : m ≫ pullback.snd C.hom gKE =
      pullback.snd X.hom gKE := by
    change (pullback.lift _ _ _) ≫ pullback.snd C.hom gKE = _
    rw [pullback.lift_snd]
  have hjm : j ≫ m = pullback.snd (f.fiberToSpecResidueField x) gLE ≫ q₀ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hm_fst, ← Category.assoc, pullback.lift_fst,
        Category.assoc, f.fiber_fac, pullback.condition_assoc,
        Category.assoc, pullback.lift_fst]
    · calc
        (j ≫ m) ≫ pullback.snd C.hom gKE =
            j ≫ (m ≫ pullback.snd C.hom gKE) := Category.assoc _ _ _
        _ = j ≫ pullback.snd X.hom gKE := by rw [hm_snd]
        _ = pullback.snd (f.fiberToSpecResidueField x) gLE := by
          exact pullback.lift_snd _ _ _
        _ = (pullback.snd (f.fiberToSpecResidueField x) gLE ≫ q₀) ≫
            pullback.snd C.hom gKE := by
          dsimp only [q₀]
          rw [Category.assoc, pullback.lift_snd, Category.comp_id]
  have hbase : IsPullback (pullback.fst X.hom gKE) m f
      (pullback.fst C.hom gKE) := by
    have houterBase : IsPullback (pullback.fst X.hom gKE)
        (m ≫ pullback.snd C.hom gKE) (f ≫ C.hom) gKE := by
      rw [hm_snd, (toComponentScheme X).w]
      exact IsPullback.of_hasPullback X.hom gKE
    exact houterBase.of_bot hm_fst.symm
      (IsPullback.of_hasPullback C.hom gKE)
  have houter : IsPullback
      (j ≫ pullback.fst X.hom gKE)
      (pullback.snd (f.fiberToSpecResidueField x) gLE) f
      (q₀ ≫ pullback.fst C.hom gKE) := by
    convert (IsPullback.of_hasPullback (f.fiberToSpecResidueField x) gLE).paste_horiz
      (IsPullback.of_hasPullback f (C.left.fromSpecResidueField x)) using 1
    · exact hj_fst
    · exact pullback.lift_fst _ _ _
  have hCE : IsPullback j
      (pullback.snd (f.fiberToSpecResidueField x) gLE) m q₀ :=
    houter.of_right hjm hbase
  have hcomponent : (toComponentScheme XL).left ≫ e.hom.left = m := by
    rw [componentBaseChangeIso_hom]
    exact congrArg Over.Hom.left
      (toComponentScheme_comp_componentBaseChangeComparison (K := E) X)
  have hfinal : IsPullback j
      (pullback.snd (f.fiberToSpecResidueField x) gLE)
      (toComponentScheme XL).left q := by
    apply hCE.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (Comma.leftIso e.symm)
    · simp
    · simp
    · change m ≫ e.inv.left = (toComponentScheme XL).left
      apply (cancel_mono e.hom.left).mp
      have he : e.inv.left ≫ e.hom.left = 𝟙 _ :=
        congrArg Over.Hom.left e.inv_hom_id
      calc
        (m ≫ e.inv.left) ≫ e.hom.left =
            m ≫ (e.inv.left ≫ e.hom.left) := Category.assoc _ _ _
        _ = m := by rw [he, Category.comp_id]
        _ = (toComponentScheme XL).left ≫ e.hom.left := hcomponent.symm
    · rfl
  change ConnectedSpace Z
  rw [(Scheme.homeoOfIso hfinal.isoPullback).connectedSpace_iff]
  exact connectedSpace_pullback_toComponentScheme XL q

/-- A connected scheme, locally of finite type and quasi-compact over a field,
is geometrically connected if its structure morphism has a section. This is
the geometric-connectedness conclusion of J. S. Milne, *Algebraic Groups*
(2017), Corollary 1.32(a). -/
theorem geometricallyConnected_of_connectedSpace_of_section
    {K : Type u} [Field K]
    (X : Over (Spec (.of K)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [ConnectedSpace X.left]
    (p : Over.mk (𝟙 (Spec (.of K))) ⟶ X) :
    GeometricallyConnected X.hom := by
  let C := componentScheme X
  let q : Over.mk (𝟙 (Spec (.of K))) ⟶ C := p ≫ toComponentScheme X
  let A := componentSubalgebra X
  let _ : Module.Finite K A := (componentSubalgebra_isFiniteEtale X).1
  let _ : Algebra.Etale K A := (componentSubalgebra_isFiniteEtale X).2
  have hC_etale : Etale C.hom := by
    change Etale (Spec.map (CommRingCat.ofHom (algebraMap K A)))
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  let _ : Etale C.hom := hC_etale
  have hqcomp_etale : Etale (q.left ≫ C.hom) := by
    rw [q.w]
    change Etale (𝟙 (Spec (.of K)))
    infer_instance
  let _ : Etale (q.left ≫ C.hom) := hqcomp_etale
  have hq_etale : Etale q.left := Etale.of_comp q.left C.hom
  let _ : Etale q.left := hq_etale
  have hq_open : IsOpenImmersion q.left :=
    isOpenImmersion_of_etale_of_section q.left C.hom q.w
  let _ : IsOpenImmersion q.left := hq_open
  let _ : ConnectedSpace C.left :=
    (surjective_toComponentScheme X).surj.connectedSpace
      (toComponentScheme X).left.continuous
  let _ : DiscreteTopology C.left := by
    change DiscreteTopology (Spec (.of A))
    exact Algebra.QuasiFinite.discreteTopology_primeSpectrum K A
  let _ : Subsingleton C.left :=
    subsingleton_of_preconnected_totallyDisconnected
  have hq_surjective : Surjective q.left := ⟨by
    intro y
    exact ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  let _ : Surjective q.left := hq_surjective
  have hq_iso : IsIso q.left :=
    (isIso_iff_isOpenImmersion_and_surjective q.left).mpr
      ⟨hq_open, hq_surjective⟩
  let _ : IsIso q.left := hq_iso
  have hq_w : q.left ≫ C.hom = 𝟙 _ := by
    exact q.w
  have hC_iso : IsIso C.hom := IsIso.of_isIso_fac_left hq_w
  let _ : IsIso C.hom := hC_iso
  have hcomponent : GeometricallyConnected (toComponentScheme X).left :=
    (GeometricallyConnected.iff_geometricallyConnected_fiber _).mpr
      (geometricallyConnected_fiber_toComponentScheme X)
  let _ : MorphismProperty.RespectsIso @GeometricallyConnected := by
    rw [GeometricallyConnected.eq_geometrically]
    infer_instance
  have hcomp : GeometricallyConnected
      ((toComponentScheme X).left ≫ C.hom) :=
    MorphismProperty.RespectsIso.postcomp @GeometricallyConnected C.hom
      (toComponentScheme X).left hcomponent
  rw [(toComponentScheme X).w] at hcomp
  exact hcomp

/-- The greatest finite-etale subalgebra of the global functions on a
component-map fibre is exactly the scalar subalgebra. This is the identity
used in J. S. Milne, *Algebraic Groups* (2017), in the proof of Proposition
1.31; here it follows from geometric connectedness of the fibre. -/
theorem componentSubalgebra_fiber_eq_bot
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (x : (componentScheme X).left) :
    letI : Algebra ((componentScheme X).left.residueField x)
        Γ((toComponentScheme X).left.fiber x, ⊤) :=
      ((toComponentScheme X).left.fiberToSpecResidueField x).globalSectionsAlgebra _
    @componentSubalgebra ((componentScheme X).left.residueField x) _
        (componentSchemeFiber X x)
        (fiberToComponentSchemeLocallyOfFiniteType X x)
        (fiberToComponentSchemeQuasiCompact X x) =
      (⊥ : Subalgebra ((componentScheme X).left.residueField x)
        Γ((toComponentScheme X).left.fiber x, ⊤)) := by
  let _ : LocallyOfFiniteType (componentSchemeFiber X x).hom :=
    fiberToComponentSchemeLocallyOfFiniteType X x
  let _ : QuasiCompact (componentSchemeFiber X x).hom :=
    fiberToComponentSchemeQuasiCompact X x
  let _ : Algebra ((componentScheme X).left.residueField x)
      Γ((componentSchemeFiber X x).left, ⊤) :=
    (componentSchemeFiber X x).hom.globalSectionsAlgebra _
  let _ : GeometricallyConnected (componentSchemeFiber X x).hom :=
    geometricallyConnected_fiber_toComponentScheme X x
  let _ : Algebra
      (IsLocalRing.ResidueField ((componentScheme X).left.presheaf.stalk x))
      (SeparableClosure ((componentScheme X).left.residueField x)) := by
    change Algebra ((componentScheme X).left.residueField x)
      (SeparableClosure ((componentScheme X).left.residueField x))
    infer_instance
  let _ : ConnectedSpace
      (schemeBaseChange (componentSchemeFiber X x)
        (L := SeparableClosure ((componentScheme X).left.residueField x))).left := by
    exact GeometricallyConnected.geometrically_connectedSpace
      (f := (componentSchemeFiber X x).hom) _ _ _
      (IsPullback.of_hasPullback _ _)
  have hcard : Nat.card (ConnectedComponents
      (schemeBaseChange (componentSchemeFiber X x)
        (L := SeparableClosure ((componentScheme X).left.residueField x))).left) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  apply Subalgebra.eq_bot_of_finrank_one
  rw [componentSubalgebra_finrank_eq_natCard_separableClosure
    (k := ((componentScheme X).left.residueField x))
    (componentSchemeFiber X x)]
  exact hcard

end

end AlgebraicGeometry

#lint- only unusedArguments docBlame
