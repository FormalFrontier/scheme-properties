/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.ResidueFieldAlgebra
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Residue degrees in the real–complex spectrum

The coproduct `Spec ℝ ⨿ Spec ℂ` has its canonical structure morphism to `Spec ℝ`.
Its two field-spectrum points are distinct and closed. Their original residue
algebras, with the actions induced by this structure morphism, are canonically
isomorphic to the standard real algebras `ℝ` and `ℂ`, and have dimensions one
and two.

The equivalences use the residue maps of the coproduct inclusions and the
canonical residue-algebra equivalences of field spectra. Closedness uses the
closed embeddings of the summands in their topological disjoint union.

## References

* Mathlib's scheme coproducts and their underlying disjoint-union homeomorphism.
* Mathlib's open-immersion residue maps and `Complex.finrank_real_complex`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.RealComplexSpectrum

/-- The coproduct of the real and complex field spectra. -/
def scheme : Scheme :=
  Spec (CommRingCat.of ℝ) ⨿ Spec (CommRingCat.of ℂ)

/-- The structure morphism induced by the identity of `Spec ℝ` and the standard
real-algebra structure on `ℂ`. -/
def toRealSpectrum : scheme ⟶ Spec (CommRingCat.of ℝ) :=
  coprod.desc (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ)))

/-- The zero-ideal point of the real summand. -/
def realPoint : scheme :=
  (coprod.inl : Spec (CommRingCat.of ℝ) ⟶ scheme) (⊥ : PrimeSpectrum ℝ)

/-- The zero-ideal point of the complex summand. -/
def complexPoint : scheme :=
  (coprod.inr : Spec (CommRingCat.of ℂ) ⟶ scheme) (⊥ : PrimeSpectrum ℂ)

/-- The real point is the image of the zero ideal under the left inclusion. -/
theorem realPoint_eq_inl :
    realPoint = (coprod.inl : Spec (CommRingCat.of ℝ) ⟶ scheme)
      (⊥ : PrimeSpectrum ℝ) :=
  rfl

/-- The complex point is the image of the zero ideal under the right inclusion. -/
theorem complexPoint_eq_inr :
    complexPoint = (coprod.inr : Spec (CommRingCat.of ℂ) ⟶ scheme)
      (⊥ : PrimeSpectrum ℂ) :=
  rfl

/-- The structure morphism is the identity on the real summand. -/
@[simp]
theorem inl_toRealSpectrum :
    (coprod.inl : Spec (CommRingCat.of ℝ) ⟶ scheme) ≫ toRealSpectrum = 𝟙 _ :=
  coprod.inl_desc _ _

/-- The structure morphism on the complex summand is induced by the standard
inclusion of the reals in the complexes. -/
@[simp]
theorem inr_toRealSpectrum :
    (coprod.inr : Spec (CommRingCat.of ℂ) ⟶ scheme) ≫ toRealSpectrum =
      Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ)) :=
  coprod.inr_desc _ _

/-- The identity restriction on the real summand is also the spectrum map of
its standard real-algebra structure. -/
theorem inl_toRealSpectrum_specMap :
    (coprod.inl : Spec (CommRingCat.of ℝ) ⟶ scheme) ≫ toRealSpectrum =
      Spec.map (CommRingCat.ofHom (algebraMap ℝ ℝ)) :=
  inl_toRealSpectrum.trans (Scheme.Spec.map_id (Opposite.op (CommRingCat.of ℝ))).symm

/-- The two field-spectrum points lie in disjoint coproduct components. -/
theorem realPoint_ne_complexPoint : realPoint ≠ complexPoint :=
  AlgebraicGeometry.inl_ne_inr _ _ _ _

/-- The point of the real component is closed in the coproduct. -/
theorem isClosed_realPoint : IsClosed ({realPoint} : Set scheme) := by
  have h : IsClosed ({Sum.inl (⊥ : PrimeSpectrum ℝ)} :
      Set (Spec (CommRingCat.of ℝ) ⊕ Spec (CommRingCat.of ℂ))) :=
    (Set.image_singleton
      (f := (Sum.inl : Spec (CommRingCat.of ℝ) →
        Spec (CommRingCat.of ℝ) ⊕ Spec (CommRingCat.of ℂ)))
      (a := (⊥ : PrimeSpectrum ℝ))) ▸
        isClosedMap_inl ({(⊥ : PrimeSpectrum ℝ)} : Set (Spec (CommRingCat.of ℝ)))
          isClosed_singleton
  have himage :
      (coprodMk (Spec (CommRingCat.of ℝ)) (Spec (CommRingCat.of ℂ))) ''
        ({Sum.inl (⊥ : PrimeSpectrum ℝ)} :
          Set (Spec (CommRingCat.of ℝ) ⊕ Spec (CommRingCat.of ℂ))) =
        ({realPoint} : Set scheme) :=
    Set.image_singleton.trans
      (congrArg (fun x : scheme => ({x} : Set scheme))
        (coprodMk_inl (Spec (CommRingCat.of ℝ)) (Spec (CommRingCat.of ℂ))
          (⊥ : PrimeSpectrum ℝ)))
  exact himage ▸
    (coprodMk (Spec (CommRingCat.of ℝ)) (Spec (CommRingCat.of ℂ))).isClosedMap _ h

/-- The point of the complex component is closed in the coproduct. -/
theorem isClosed_complexPoint : IsClosed ({complexPoint} : Set scheme) := by
  have h : IsClosed ({Sum.inr (⊥ : PrimeSpectrum ℂ)} :
      Set (Spec (CommRingCat.of ℝ) ⊕ Spec (CommRingCat.of ℂ))) :=
    (Set.image_singleton
      (f := (Sum.inr : Spec (CommRingCat.of ℂ) →
        Spec (CommRingCat.of ℝ) ⊕ Spec (CommRingCat.of ℂ)))
      (a := (⊥ : PrimeSpectrum ℂ))) ▸
        isClosedMap_inr ({(⊥ : PrimeSpectrum ℂ)} : Set (Spec (CommRingCat.of ℂ)))
          isClosed_singleton
  have himage :
      (coprodMk (Spec (CommRingCat.of ℝ)) (Spec (CommRingCat.of ℂ))) ''
        ({Sum.inr (⊥ : PrimeSpectrum ℂ)} :
          Set (Spec (CommRingCat.of ℝ) ⊕ Spec (CommRingCat.of ℂ))) =
        ({complexPoint} : Set scheme) :=
    Set.image_singleton.trans
      (congrArg (fun x : scheme => ({x} : Set scheme))
        (coprodMk_inr (Spec (CommRingCat.of ℝ)) (Spec (CommRingCat.of ℂ))
          (⊥ : PrimeSpectrum ℂ)))
  exact himage ▸
    (coprodMk (Spec (CommRingCat.of ℝ)) (Spec (CommRingCat.of ℂ))).isClosedMap _ h

/-- The original residue real algebra at the real point is canonically `ℝ`. -/
def realResidueFieldAlgEquiv :
    @AlgEquiv ℝ (scheme.residueField realPoint) ℝ _ _ _
      (((scheme.Γevaluation realPoint).hom.comp
        (@algebraMap ℝ Γ(scheme, ⊤) _ _
          (toRealSpectrum.globalSectionsAlgebra ℝ))).toAlgebra) inferInstance := by
  letI realResidueAlgebra : Algebra ℝ (scheme.residueField realPoint) :=
    (((scheme.Γevaluation realPoint).hom.comp
      (@algebraMap ℝ Γ(scheme, ⊤) _ _
        (toRealSpectrum.globalSectionsAlgebra ℝ))).toAlgebra)
  letI specResidueAlgebra :
      Algebra ℝ ((Spec (CommRingCat.of ℝ)).residueField (⊥ : PrimeSpectrum ℝ)) :=
    ((((Spec (CommRingCat.of ℝ)).Γevaluation (⊥ : PrimeSpectrum ℝ)).hom.comp
      (@algebraMap ℝ Γ(Spec (CommRingCat.of ℝ), ⊤) _ _
        ((Spec.map (CommRingCat.ofHom (algebraMap ℝ ℝ))).globalSectionsAlgebra ℝ))).toAlgebra)
  have hOpen : IsOpenImmersion (coprod.inl : Spec (CommRingCat.of ℝ) ⟶ scheme) :=
    inferInstanceAs (IsOpenImmersion (coprod.inl : Spec (CommRingCat.of ℝ) ⟶
      Spec (CommRingCat.of ℝ) ⨿ Spec (CommRingCat.of ℂ)))
  have hIso : IsIso ((coprod.inl : Spec (CommRingCat.of ℝ) ⟶ scheme).residueFieldMap
      (⊥ : PrimeSpectrum ℝ)) :=
    @Scheme.Hom.isIso_residueFieldMap_of_isOpenImmersion
      (Spec (CommRingCat.of ℝ)) scheme coprod.inl hOpen (⊥ : PrimeSpectrum ℝ)
  exact @AlgEquiv.trans ℝ (scheme.residueField realPoint)
    ((Spec (CommRingCat.of ℝ)).residueField (⊥ : PrimeSpectrum ℝ)) ℝ _ _ _ _
    realResidueAlgebra specResidueAlgebra inferInstance
    (@Scheme.Hom.residueFieldAlgEquiv ℝ _ (Spec (CommRingCat.of ℝ)) scheme
      coprod.inl (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℝ))) toRealSpectrum
      inl_toRealSpectrum_specMap (⊥ : PrimeSpectrum ℝ) hIso)
    (Scheme.Spec.residueFieldAlgEquiv ℝ ℝ (⊥ : PrimeSpectrum ℝ))

/-- The original residue real algebra at the complex point is canonically the
standard real algebra `ℂ`. -/
def complexResidueFieldAlgEquiv :
    @AlgEquiv ℝ (scheme.residueField complexPoint) ℂ _ _ _
      (((scheme.Γevaluation complexPoint).hom.comp
        (@algebraMap ℝ Γ(scheme, ⊤) _ _
          (toRealSpectrum.globalSectionsAlgebra ℝ))).toAlgebra) inferInstance := by
  letI complexResidueAlgebra : Algebra ℝ (scheme.residueField complexPoint) :=
    (((scheme.Γevaluation complexPoint).hom.comp
      (@algebraMap ℝ Γ(scheme, ⊤) _ _
        (toRealSpectrum.globalSectionsAlgebra ℝ))).toAlgebra)
  letI specResidueAlgebra :
      Algebra ℝ ((Spec (CommRingCat.of ℂ)).residueField (⊥ : PrimeSpectrum ℂ)) :=
    ((((Spec (CommRingCat.of ℂ)).Γevaluation (⊥ : PrimeSpectrum ℂ)).hom.comp
      (@algebraMap ℝ Γ(Spec (CommRingCat.of ℂ), ⊤) _ _
        ((Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ))).globalSectionsAlgebra ℝ))).toAlgebra)
  have hOpen : IsOpenImmersion (coprod.inr : Spec (CommRingCat.of ℂ) ⟶ scheme) :=
    inferInstanceAs (IsOpenImmersion (coprod.inr : Spec (CommRingCat.of ℂ) ⟶
      Spec (CommRingCat.of ℝ) ⨿ Spec (CommRingCat.of ℂ)))
  have hIso : IsIso ((coprod.inr : Spec (CommRingCat.of ℂ) ⟶ scheme).residueFieldMap
      (⊥ : PrimeSpectrum ℂ)) :=
    @Scheme.Hom.isIso_residueFieldMap_of_isOpenImmersion
      (Spec (CommRingCat.of ℂ)) scheme coprod.inr hOpen (⊥ : PrimeSpectrum ℂ)
  exact @AlgEquiv.trans ℝ (scheme.residueField complexPoint)
    ((Spec (CommRingCat.of ℂ)).residueField (⊥ : PrimeSpectrum ℂ)) ℂ _ _ _ _
    complexResidueAlgebra specResidueAlgebra inferInstance
    (@Scheme.Hom.residueFieldAlgEquiv ℝ _ (Spec (CommRingCat.of ℂ)) scheme
      coprod.inr (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ))) toRealSpectrum
      inr_toRealSpectrum (⊥ : PrimeSpectrum ℂ) hIso)
    (Scheme.Spec.residueFieldAlgEquiv ℝ ℂ (⊥ : PrimeSpectrum ℂ))

/-- The ring map at the real point is inclusion pullback followed by the
canonical field-spectrum residue equivalence. -/
theorem realResidueFieldAlgEquiv_toRingHom :
    (realResidueFieldAlgEquiv : scheme.residueField realPoint →+* ℝ) =
      (Scheme.Spec.residueFieldAlgEquiv ℝ ℝ (⊥ : PrimeSpectrum ℝ) :
        (Spec (CommRingCat.of ℝ)).residueField (⊥ : PrimeSpectrum ℝ) →+* ℝ).comp
          ((coprod.inl : Spec (CommRingCat.of ℝ) ⟶ scheme).residueFieldMap
            (⊥ : PrimeSpectrum ℝ)).hom := by
  apply RingHom.ext
  intro a
  exact congrArg (Scheme.Spec.residueFieldAlgEquiv ℝ ℝ (⊥ : PrimeSpectrum ℝ))
    (@Scheme.Hom.residueFieldAlgEquiv_apply ℝ _ (Spec (CommRingCat.of ℝ)) scheme
      coprod.inl (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℝ))) toRealSpectrum
      inl_toRealSpectrum_specMap (⊥ : PrimeSpectrum ℝ)
      (@Scheme.Hom.isIso_residueFieldMap_of_isOpenImmersion
        (Spec (CommRingCat.of ℝ)) scheme coprod.inl
        (inferInstanceAs (IsOpenImmersion (coprod.inl : Spec (CommRingCat.of ℝ) ⟶
          Spec (CommRingCat.of ℝ) ⨿ Spec (CommRingCat.of ℂ))))
        (⊥ : PrimeSpectrum ℝ)) a)

/-- The ring map at the complex point is inclusion pullback followed by the
canonical field-spectrum residue equivalence. -/
theorem complexResidueFieldAlgEquiv_toRingHom :
    (complexResidueFieldAlgEquiv : scheme.residueField complexPoint →+* ℂ) =
      (Scheme.Spec.residueFieldAlgEquiv ℝ ℂ (⊥ : PrimeSpectrum ℂ) :
        (Spec (CommRingCat.of ℂ)).residueField (⊥ : PrimeSpectrum ℂ) →+* ℂ).comp
          ((coprod.inr : Spec (CommRingCat.of ℂ) ⟶ scheme).residueFieldMap
            (⊥ : PrimeSpectrum ℂ)).hom := by
  apply RingHom.ext
  intro a
  exact congrArg (Scheme.Spec.residueFieldAlgEquiv ℝ ℂ (⊥ : PrimeSpectrum ℂ))
    (@Scheme.Hom.residueFieldAlgEquiv_apply ℝ _ (Spec (CommRingCat.of ℂ)) scheme
      coprod.inr (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ))) toRealSpectrum
      inr_toRealSpectrum (⊥ : PrimeSpectrum ℂ)
      (@Scheme.Hom.isIso_residueFieldMap_of_isOpenImmersion
        (Spec (CommRingCat.of ℂ)) scheme coprod.inr
        (inferInstanceAs (IsOpenImmersion (coprod.inr : Spec (CommRingCat.of ℂ) ⟶
          Spec (CommRingCat.of ℝ) ⨿ Spec (CommRingCat.of ℂ))))
        (⊥ : PrimeSpectrum ℂ)) a)

/-- Elementwise description of the real residue-algebra equivalence. -/
@[simp]
theorem realResidueFieldAlgEquiv_apply (a : scheme.residueField realPoint) :
    realResidueFieldAlgEquiv a =
      (⊥ : PrimeSpectrum ℝ).asIdeal.algEquivResidueFieldOfField.symm
        ((Scheme.Spec.residueFieldIso (CommRingCat.of ℝ) (⊥ : PrimeSpectrum ℝ)).hom
          ((coprod.inl : Spec (CommRingCat.of ℝ) ⟶ scheme).residueFieldMap
            (⊥ : PrimeSpectrum ℝ) a)) := by
  exact (congrArg (fun f : scheme.residueField realPoint →+* ℝ => f a)
    realResidueFieldAlgEquiv_toRingHom).trans
      (Scheme.Spec.residueFieldAlgEquiv_apply ℝ ℝ (⊥ : PrimeSpectrum ℝ) _)

/-- Elementwise description of the complex residue-algebra equivalence. -/
@[simp]
theorem complexResidueFieldAlgEquiv_apply (a : scheme.residueField complexPoint) :
    complexResidueFieldAlgEquiv a =
      (⊥ : PrimeSpectrum ℂ).asIdeal.algEquivResidueFieldOfField.symm
        ((Scheme.Spec.residueFieldIso (CommRingCat.of ℂ) (⊥ : PrimeSpectrum ℂ)).hom
          ((coprod.inr : Spec (CommRingCat.of ℂ) ⟶ scheme).residueFieldMap
            (⊥ : PrimeSpectrum ℂ) a)) := by
  exact (congrArg (fun f : scheme.residueField complexPoint →+* ℂ => f a)
    complexResidueFieldAlgEquiv_toRingHom).trans
      (Scheme.Spec.residueFieldAlgEquiv_apply ℝ ℂ (⊥ : PrimeSpectrum ℂ) _)

/-- The real equivalence preserves the scalar map induced by the structure
morphism of the coproduct. -/
theorem realResidueFieldAlgEquiv_algebraMap (r : ℝ) :
    realResidueFieldAlgEquiv
        ((@algebraMap ℝ (scheme.residueField realPoint) _ _
          (((scheme.Γevaluation realPoint).hom.comp
            (@algebraMap ℝ Γ(scheme, ⊤) _ _
              (toRealSpectrum.globalSectionsAlgebra ℝ))).toAlgebra)) r) = r := by
  let : Algebra ℝ (scheme.residueField realPoint) :=
    (((scheme.Γevaluation realPoint).hom.comp
      (@algebraMap ℝ Γ(scheme, ⊤) _ _
        (toRealSpectrum.globalSectionsAlgebra ℝ))).toAlgebra)
  exact realResidueFieldAlgEquiv.commutes r

/-- The complex equivalence preserves the scalar map induced by the structure
morphism of the coproduct, with the standard real action on `ℂ`. -/
theorem complexResidueFieldAlgEquiv_algebraMap (r : ℝ) :
    complexResidueFieldAlgEquiv
        ((@algebraMap ℝ (scheme.residueField complexPoint) _ _
          (((scheme.Γevaluation complexPoint).hom.comp
            (@algebraMap ℝ Γ(scheme, ⊤) _ _
              (toRealSpectrum.globalSectionsAlgebra ℝ))).toAlgebra)) r) =
      algebraMap ℝ ℂ r := by
  let : Algebra ℝ (scheme.residueField complexPoint) :=
    (((scheme.Γevaluation complexPoint).hom.comp
      (@algebraMap ℝ Γ(scheme, ⊤) _ _
        (toRealSpectrum.globalSectionsAlgebra ℝ))).toAlgebra)
  exact complexResidueFieldAlgEquiv.commutes r

/-- The original residue field at the real point has real dimension one. -/
theorem finrank_realPoint :
    @Module.finrank ℝ (scheme.residueField realPoint) _ _
      ((@Algebra.toModule ℝ (scheme.residueField realPoint) _ _
        (((scheme.Γevaluation realPoint).hom.comp
          (@algebraMap ℝ Γ(scheme, ⊤) _ _
            (toRealSpectrum.globalSectionsAlgebra ℝ))).toAlgebra))) = 1 := by
  let : Algebra ℝ (scheme.residueField realPoint) :=
    (((scheme.Γevaluation realPoint).hom.comp
    (@algebraMap ℝ Γ(scheme, ⊤) _ _
      (toRealSpectrum.globalSectionsAlgebra ℝ))).toAlgebra)
  calc
    Module.finrank ℝ (scheme.residueField realPoint) = Module.finrank ℝ ℝ :=
      realResidueFieldAlgEquiv.toLinearEquiv.finrank_eq
    _ = 1 := Module.finrank_self ℝ

/-- The original residue field at the complex point has real dimension two. -/
theorem finrank_complexPoint :
    @Module.finrank ℝ (scheme.residueField complexPoint) _ _
      ((@Algebra.toModule ℝ (scheme.residueField complexPoint) _ _
        (((scheme.Γevaluation complexPoint).hom.comp
          (@algebraMap ℝ Γ(scheme, ⊤) _ _
            (toRealSpectrum.globalSectionsAlgebra ℝ))).toAlgebra))) = 2 := by
  let : Algebra ℝ (scheme.residueField complexPoint) :=
    (((scheme.Γevaluation complexPoint).hom.comp
    (@algebraMap ℝ Γ(scheme, ⊤) _ _
      (toRealSpectrum.globalSectionsAlgebra ℝ))).toAlgebra)
  calc
    Module.finrank ℝ (scheme.residueField complexPoint) = Module.finrank ℝ ℂ :=
      complexResidueFieldAlgEquiv.toLinearEquiv.finrank_eq
    _ = 2 := Complex.finrank_real_complex

end AlgebraicGeometry.RealComplexSpectrum
