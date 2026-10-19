/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import MinimalPrimes.RingTheory.KrullDimension.FieldExtension
public import MinimalPrimes.Topology.KrullDimension.OpenCover

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.FiniteType

/-!
# Krull dimension of schemes after extending a field

Base change between affine schemes whose global section rings are fields preserves
the topological Krull dimension of every scheme locally of finite type over the
base. The field assumptions are ordinary `IsField` witnesses for the canonical
section rings. In particular, extending a ground field preserves dimension. Both
spaces carry their original Zariski topologies, and base change is the categorical
pullback of the specified morphisms. Dimensions take values in `WithBot ℕ∞`, allowing
both the empty scheme and unbounded dimension. There is no quasi-compactness,
quasi-separatedness, Noetherianity or global-sections finite-type hypothesis on the
source scheme.

`SchemePropertiesTest.Dimension.FieldExtension` supplies private zero-ring,
polynomial-spectrum and countable-coproduct examples, with their specified scalar
structures, structure maps, sections, local-finite-type laws and both tensor-product
projections.

## References

* Mathlib at `83abb3e776bdefcbc447a1e44d0debe4010039e5`:
  `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Pullbacks`,
  `AlgebraicGeometry.Limits`, `AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.Morphisms.RingHomProperties`, `RingTheory.FiniteType`,
  and `Topology.KrullDimension`.
* Minimal Primes: `Algebra.ringKrullDim_tensorProduct_of_finiteType` in
  `RingTheory.KrullDimension.FieldExtension` and
  `topologicalKrullDim_eq_iSup_of_isOpenEmbedding_cover` in
  `Topology.KrullDimension.OpenCover`.
-/

/-!
## Proof outline

An arbitrary affine open cover of `X` pulls back to an open cover of the fibre
product. On each chart, the canonical tensor-product pushout gives a spectrum
square; naturality of `isoSpec` identifies it with the original affine square,
including both projections. Local finite type supplies finite generation of the
chart algebra, so the tensor-product dimension theorem applies. The dimension of
each space is then the supremum of the dimensions of its open charts.

## Implementation notes

All schemes in a diagram and the fields in the field-spectrum corollary share one
universe. Transport between differently sized scheme presentations is not supplied
here. The examples are in `SchemePropertiesTest.Dimension.FieldExtension`; separate
polynomial and coproduct dimension calculations are not needed for the comparison
theorem.

## Credit

The scheme/Spec formalization is due to Kim Morrison and Mathlib contributors;
the pullback and finite-type interfaces used here are due to Andrew Yang and
Mathlib contributors. The algebra finiteness interface is due to Johan Commelin;
algebra interfaces credit Kenny Lau and Yury Kudryashov. Topological dimension
credits Jujian Zhang, Fangming Li and Alessandro D'Angelo. The tensor-field
dimension theorem and arbitrary open-cover supremum theorem are reused from Minimal
Primes. The proof uses these constructors and exported laws, not their implementations.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- The global section ring of the spectrum of a field is a field, via the canonical
global-sections isomorphism `Scheme.ΓSpecIso`. -/
public theorem globalSections_spec_isField (F : Type u) [Field F] :
    IsField Γ(Spec (CommRingCat.of F), ⊤) := by
  exact MulEquiv.isField (Field.toIsField F)
    (CategoryTheory.Iso.commRingCatIsoToRingEquiv
      (Scheme.ΓSpecIso (CommRingCat.of F))).toMulEquiv

namespace Scheme

private theorem topologicalKrullDim_spec (R : CommRingCat.{u}) :
    topologicalKrullDim (Spec R) = ringKrullDim R := by
  exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim R

private theorem topologicalKrullDim_eq_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) :
    topologicalKrullDim X = topologicalKrullDim Y :=
  IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph

private theorem topologicalKrullDim_affine (X : Scheme.{u}) [IsAffine X] :
    topologicalKrullDim X = ringKrullDim Γ(X, ⊤) := by
  calc
    topologicalKrullDim X = topologicalKrullDim (Spec Γ(X, ⊤)) :=
      topologicalKrullDim_eq_of_iso X.isoSpec
    _ = ringKrullDim Γ(X, ⊤) := topologicalKrullDim_spec _

-- The chart ring may be the zero ring. Only the two base section rings are fields.
private theorem topologicalKrullDim_eq_of_isPullback_of_isField
    {S T U W : Scheme.{u}} [IsAffine S] [IsAffine T] [IsAffine U]
    {a : W ⟶ U} {b : W ⟶ T}
    (hS : IsField Γ(S, ⊤)) (hT : IsField Γ(T, ⊤))
    (p : U ⟶ S) (q : T ⟶ S) [LocallyOfFiniteType p]
    (h : IsPullback a b p q) : topologicalKrullDim W = topologicalKrullDim U := by
  let K : Type u := Γ(S, ⊤)
  let L : Type u := Γ(T, ⊤)
  let A : Type u := Γ(U, ⊤)
  let : Field K := hS.toField
  let : Field L := hT.toField
  let : Algebra K A := p.appTop.hom.toAlgebra
  let : Algebra K L := q.appTop.hom.toAlgebra
  have hp : (algebraMap K A).FiniteType := by
    simpa only [RingHom.algebraMap_toAlgebra] using
      (HasRingHomProperty.appTop (P := @LocallyOfFiniteType) p inferInstance)
  let : Algebra.FiniteType K A := RingHom.finiteType_algebraMap.mp hp
  let E : Scheme.{u} := Spec (CommRingCat.of (A ⊗[K] L))
  let jA : CommRingCat.of A ⟶ CommRingCat.of (A ⊗[K] L) :=
    CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  let jL : CommRingCat.of L ⟶ CommRingCat.of (A ⊗[K] L) :=
    CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
  have ht : IsPullback (Spec.map jA) (Spec.map jL)
      (Spec.map p.appTop) (Spec.map q.appTop) := by
    -- Normalize both the bundled section rings and their specified ring maps.
    simpa only [RingHom.algebraMap_toAlgebra, CommRingCat.of_carrier,
      CommRingCat.ofHom_hom] using
      (isPullback_SpecMap_of_isPushout
        (CommRingCat.ofHom (algebraMap K A))
        (CommRingCat.ofHom (algebraMap K L)) jA jL
        (CommRingCat.isPushout_tensorProduct K A L))
  let kU : E ⟶ U := Spec.map jA ≫ U.isoSpec.inv
  let kT : E ⟶ T := Spec.map jL ≫ T.isoSpec.inv
  have he : IsPullback kU kT p q :=
    ht.of_iso (Iso.refl _) U.isoSpec.symm T.isoSpec.symm S.isoSpec.symm
      (by simp only [Iso.refl_hom, Category.id_comp]; rfl)
      (by simp only [Iso.refl_hom, Category.id_comp]; rfl)
      (isoSpec_inv_naturality p) (isoSpec_inv_naturality q)
  let e : W ≅ E := h.isoIsPullback U T he
  -- The universal comparison identifies the specified maps in both directions.
  have e_hom_fst : e.hom ≫ kU = a :=
    IsPullback.isoIsPullback_hom_fst (X := U) (Y := T) h he
  have e_hom_snd : e.hom ≫ kT = b :=
    IsPullback.isoIsPullback_hom_snd (X := U) (Y := T) h he
  have e_inv_fst : e.inv ≫ a = kU :=
    IsPullback.isoIsPullback_inv_fst (X := U) (Y := T) h he
  have e_inv_snd : e.inv ≫ b = kT :=
    IsPullback.isoIsPullback_inv_snd (X := U) (Y := T) h he
  calc
    topologicalKrullDim W = topologicalKrullDim E :=
      topologicalKrullDim_eq_of_iso e
    _ = ringKrullDim (A ⊗[K] L) := topologicalKrullDim_spec _
    _ = ringKrullDim A := Algebra.ringKrullDim_tensorProduct_of_finiteType K L A
    _ = topologicalKrullDim U := (topologicalKrullDim_affine U).symm

/-- Base change between affine schemes whose global section rings are fields preserves
Zariski Krull dimension for every scheme locally of finite type over the base. The
pullback is the categorical pullback of the specified morphisms, with the original
Zariski topologies. The field assumptions are ordinary witnesses for the canonical
global section rings. Empty source schemes and unbounded dimension are allowed.
The proof combines `Algebra.ringKrullDim_tensorProduct_of_finiteType` with
`topologicalKrullDim_eq_iSup_of_isOpenEmbedding_cover`. -/
public theorem topologicalKrullDim_pullback_of_isField
    {S T X : Scheme.{u}} [IsAffine S] [IsAffine T]
    (hS : IsField Γ(S, ⊤)) (hT : IsField Γ(T, ⊤))
    (p : X ⟶ S) (q : T ⟶ S) [LocallyOfFiniteType p] :
    topologicalKrullDim (Limits.pullback (C := Scheme.{u}) p q) = topologicalKrullDim X := by
  let r : Limits.pullback (C := Scheme.{u}) p q ⟶ X := pullback.fst p q
  let W (i : X.affineCover.I₀) : Scheme.{u} := pullback (X.affineCover.f i) r
  let b (i : X.affineCover.I₀) : W i ⟶ Limits.pullback (C := Scheme.{u}) p q :=
    pullback.snd (X.affineCover.f i) r
  have hb (i : X.affineCover.I₀) : Topology.IsOpenEmbedding (b i) :=
    (b i).isOpenEmbedding
  have hcov (y : Limits.pullback (C := Scheme.{u}) p q) :
      ∃ i, ∃ z : W i, b i z = y := by
    obtain ⟨i, x, hx⟩ := X.affineCover.exists_eq (r y)
    have hy : y ∈ Set.range (pullback.snd (X.affineCover.f i) r) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      exact Hom.mem_opensRange.mpr ⟨x, hx⟩
    obtain ⟨z, hz⟩ := hy
    exact ⟨i, z, hz⟩
  have hdim (i : X.affineCover.I₀) :
      topologicalKrullDim (W i) = topologicalKrullDim (X.affineCover.X i) :=
    topologicalKrullDim_eq_of_isPullback_of_isField hS hT (X.affineCover.f i ≫ p) q
      ((IsPullback.of_hasPullback (X.affineCover.f i) r).paste_vert
        (IsPullback.of_hasPullback p q))
  calc
    topologicalKrullDim (Limits.pullback (C := Scheme.{u}) p q) =
        ⨆ i, topologicalKrullDim (W i) :=
      topologicalKrullDim_eq_iSup_of_isOpenEmbedding_cover
        (fun i ↦ b i) hb hcov
    _ = ⨆ i, topologicalKrullDim (X.affineCover.X i) := iSup_congr hdim
    _ = topologicalKrullDim X :=
      (topologicalKrullDim_eq_iSup_of_isOpenEmbedding_cover
        (fun i ↦ X.affineCover.f i) (fun i ↦ (X.affineCover.f i).isOpenEmbedding)
        X.affineCover.exists_eq).symm

/-- Extending the ground field preserves the Zariski Krull dimension of a scheme
locally of finite type over that field, including empty schemes and schemes of
unbounded dimension. This specializes `topologicalKrullDim_pullback_of_isField`
using the canonical global-sections isomorphisms for field spectra. -/
public theorem topologicalKrullDim_pullback_field {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f] :
    topologicalKrullDim
        (Limits.pullback (C := Scheme.{u}) f
          (Spec.map (CommRingCat.ofHom (algebraMap K L)))) =
      topologicalKrullDim X := by
  exact topologicalKrullDim_pullback_of_isField
    (globalSections_spec_isField K) (globalSections_spec_isField L)
    f (Spec.map (CommRingCat.ofHom (algebraMap K L)))

end Scheme

end AlgebraicGeometry
