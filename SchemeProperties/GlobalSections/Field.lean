/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import MinimalPrimes.RingTheory.KrullDimension.Integral
public import MinimalPrimes.RingTheory.Spectrum.Prime.ZeroDimensional
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.RingHom.Integral
import Mathlib.RingTheory.SimpleRing.Field

/-!
# Fields of global sections

A reduced connected scheme universally closed over a field has a field of global
sections. With a given section, preconnectedness suffices to make the canonical
map on global sections an isomorphism, whose inverse is induced by that section.

The field criterion combines integrality of the original scalar map with the
zero-dimensional, reduced, preconnected-spectrum criterion. No field structure
on the global-sections ring is an input.

## References

* Mathlib's universally closed global-sections and canonical spectrum-map APIs,
  in particular work of Andrew Yang.
* Minimal Primes' integral dimension bound and reduced zero-dimensional field
  criterion.
* J. S. Milne, *Abelian Varieties*, Chapter I, Theorem 1.1, for the integral
  pointed affine-target constancy step generalized by the section isomorphism.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A reduced connected scheme universally closed over a field has a field of
global sections. This generalizes `isField_of_universallyClosed` from integral
schemes without changing the global-sections ring or its scalar map. -/
theorem isField_globalSections_of_universallyClosed
    (K : Type u) [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [UniversallyClosed f]
    [IsReduced X] [ConnectedSpace X] : _root_.IsField Γ(X, ⊤) := by
  classical
  letI : Nontrivial Γ(X, ⊤) :=
    @LocallyRingedSpace.component_nontrivial X.toLocallyRingedSpace ⊤
      ⟨⟨Classical.choice (inferInstance : Nonempty X), by trivial⟩⟩
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  letI : PreconnectedSpace (PrimeSpectrum Γ(X, ⊤)) :=
    X.toSpecΓ.denseRange.preconnectedSpace X.toSpecΓ.continuous
  -- Transport integrality across Γ(Spec K) ≅ K, retaining the canonical scalar map.
  have hρ : (f.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).IsIntegral :=
    (RingHom.isIntegral_respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (.of K)).inv f.appTop).2
        (isIntegral_appTop_of_universallyClosed f)
  letI : Ring.KrullDimLE 0 Γ(X, ⊤) := Ring.krullDimLE_iff.mpr (by
    simpa only [ringKrullDim_eq_zero_of_field K, Nat.cast_zero] using hρ.ringKrullDim_le)
  exact PrimeSpectrum.isField_of_isReduced_of_preconnectedSpace Γ(X, ⊤)

namespace Scheme.Hom

/-- For a reduced preconnected scheme universally closed over a field, a given
section makes the canonical map on global sections an isomorphism. The section
supplies the nonemptiness needed for the field criterion. This generalizes the
integral pointed affine-target constancy step in Milne, *Abelian Varieties*,
Chapter I, Theorem 1.1, without finite-type or separatedness assumptions. -/
theorem isIso_appTop_of_isReduced_of_universallyClosed_of_section
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsReduced X]
    [PreconnectedSpace X] [UniversallyClosed f]
    (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) : IsIso f.appTop := by
  letI : Nonempty X := Nonempty.map p inferInstance
  letI : ConnectedSpace X :=
    { toPreconnectedSpace := inferInstance, toNonempty := inferInstance }
  letI : IsSimpleRing Γ(X, ⊤) :=
    (isSimpleRing_iff_isField Γ(X, ⊤)).2
      (isField_globalSections_of_universallyClosed K f)
  letI : Nontrivial Γ(Spec (.of K), ⊤) :=
    (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  letI : Mono p.appTop :=
    ConcreteCategory.mono_of_injective p.appTop p.appTop.hom.injective
  have hfp : f.appTop ≫ p.appTop = 𝟙 _ := by
    rw [← comp_appTop, hp, id_appTop]
  -- Store this given section, rather than choosing a splitting from an existence proof.
  let s : SplitMono f.appTop := { retraction := p.appTop, id := hfp }
  exact IsIso.of_mono_retraction' s

end Scheme.Hom

end AlgebraicGeometry
