/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Maps.Basic

/-!
# The open of fibres contained in an open subscheme

For a closed scheme morphism `π`, `π.kernImage hπ W` is the largest base open whose
preimage is contained in `W`. Closedness is an explicit hypothesis; universal
closedness and hypotheses on the source or target are not needed.

This bundles Mathlib's `Set.kernImage`, using `isClosedMap_iff_kernImage` for
openness and `Set.subset_kernImage_iff` for the characteristic property. The
scheme morphism on restricted opens is already Mathlib's `Scheme.Hom.resLE`;
no new restriction constructor is introduced here.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

variable {E B Z : Scheme.{u}} (π : E ⟶ B) (hπ : IsClosedMap π)

/-- The base open consisting of the points whose whole `π`-fibre lies in `W`. -/
def kernImage (W : E.Opens) : B.Opens :=
  ⟨Set.kernImage π W, (isClosedMap_iff_kernImage.mp hπ) W.isOpen⟩

@[simp]
theorem coe_kernImage (W : E.Opens) :
    (π.kernImage hπ W : Set B) = Set.kernImage π W := rfl

/-- Membership means that every point of the fibre belongs to the given open.
In particular, empty fibres are included. -/
@[simp]
theorem mem_kernImage (W : E.Opens) (b : B) :
    b ∈ π.kernImage hπ W ↔ ∀ ⦃e : E⦄, π e = b → e ∈ W := Iff.rfl

/-- The characteristic property, inherited from `Set.subset_kernImage_iff`. -/
theorem le_kernImage_iff (V : B.Opens) (W : E.Opens) :
    V ≤ π.kernImage hπ W ↔ π ⁻¹ᵁ V ≤ W :=
  Set.subset_kernImage_iff

/-- Preimage of opens is left adjoint to the open of good fibres. -/
theorem kernImage_gc :
    GaloisConnection (fun V : B.Opens ↦ π ⁻¹ᵁ V) (π.kernImage hπ) :=
  fun V W ↦ (π.le_kernImage_iff hπ V W).symm

/-- Every point above the open of good fibres lies in the original open. -/
theorem preimage_kernImage_le (W : E.Opens) :
    π ⁻¹ᵁ (π.kernImage hπ W) ≤ W :=
  (π.le_kernImage_iff hπ _ W).mp le_rfl

/-- Enlarging the source open enlarges the open of good fibres. -/
theorem kernImage_mono : Monotone (π.kernImage hπ) :=
  fun _ _ h ↦ Set.kernImage_mono h

@[simp]
theorem kernImage_top : π.kernImage hπ ⊤ = ⊤ :=
  (π.kernImage_gc hπ).u_top

/-- A base open lies in the open of fibres mapping into `U` exactly when the
restriction to its preimage factors uniquely through the open subscheme `U`.
The source is the open subscheme of the original `E`, and `U` is arbitrary. -/
theorem le_kernImage_preimage_iff_existsUnique
    (f : E ⟶ Z) (U : Z.Opens) (V : B.Opens) :
    V ≤ π.kernImage hπ (f ⁻¹ᵁ U) ↔
      ∃! g : (π ⁻¹ᵁ V).toScheme ⟶ U.toScheme,
        g ≫ U.ι = (π ⁻¹ᵁ V).ι ≫ f := by
  rw [π.le_kernImage_iff hπ V (f ⁻¹ᵁ U)]
  constructor
  · intro h
    refine ⟨f.resLE U (π ⁻¹ᵁ V) h, f.resLE_comp_ι h, ?_⟩
    intro g hg
    apply (cancel_mono U.ι).mp
    exact hg.trans (f.resLE_comp_ι h).symm
  · rintro ⟨g, hg, _⟩
    intro x hx
    rw [Scheme.Hom.mem_preimage]
    let y : (π ⁻¹ᵁ V).toScheme := ⟨x, hx⟩
    have heq : (g y).1 = f x :=
      calc
        (g y).1 = U.ι (g y) := (Scheme.Opens.ι_apply U (g y)).symm
        _ = (g ≫ U.ι) y := (Scheme.Hom.comp_apply g U.ι y).symm
        _ = ((π ⁻¹ᵁ V).ι ≫ f) y :=
          congrArg (fun k : (π ⁻¹ᵁ V).toScheme ⟶ Z ↦ k y) hg
        _ = f ((π ⁻¹ᵁ V).ι y) := Scheme.Hom.comp_apply (π ⁻¹ᵁ V).ι f y
        _ = f x := congrArg f (Scheme.Opens.ι_apply (π ⁻¹ᵁ V) y)
    rw [← heq]
    exact (g y).property

end AlgebraicGeometry.Scheme.Hom
