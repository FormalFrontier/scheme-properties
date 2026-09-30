# Native finite presentations of sheaves of modules

Direct-import clients can import
`SchemeProperties.SheafFinitePresentationTransport` for site-generic results
and `SchemeProperties.ModuleFinitePresentation` for schemes and tilde.
The example client is `Test/FinitePresentationClient.lean` (namespace
`SchemePropertiesTest.FinitePresentation`).

## Site-generic API

* `SheafOfModules.Presentation.isFinite_map` transports finite generator and
  relation indices through the native `Presentation.map`. Its functor must
  preserve the specified colimits and carry the supplied comparison
  `unit S ≅ F.obj (unit R)`; both sites retain their native sheafification and
  locally-bijective hypotheses. The site universes are independent.
* `SheafOfModules.Presentation.isFinitePresentation` turns a **supplied finite
  global** presentation `P : M.Presentation` into native local
  `M.IsFinitePresentation`. It uses binary products on the site and native
  sheafification/locally-bijective hypotheses on the site and each over-site.
  It assumes no terminal object, coherence or categorical finite-presentability.

## Scheme API

* `AlgebraicGeometry.Scheme.Modules.isFinite_presentationRestrict` retains both
  finite indices for the native presentation restricted along an open immersion.
* `AlgebraicGeometry.isFinitePresentation_tilde` takes
  `[Module.FinitePresentation R M]` for `M : ModuleCat R` and gives the native
  `(tilde M).IsFinitePresentation`. It does not assume projectivity or coherence.
* `AlgebraicGeometry.Scheme.Modules.exists_isOpenCover_isFinite_presentation`
  constructs an **affine open cover** and presentations of each restriction,
  with finite generator **and** relation indices. It refines the same native
  finite quasicoherent datum extracted from `M.IsFinitePresentation`; the
  cover need not be finite, nor the presentations nonempty or constant-rank.

For example, this direct-import application uses the finite local presentations,
without adding a finite-cover assumption:

```lean
import SchemeProperties.ModuleFinitePresentation

open AlgebraicGeometry TopologicalSpace
universe u

example {X : Scheme.{u}} (M : X.Modules) [M.IsFinitePresentation] :
    ∃ (ι : Type u) (U : ι → X.Opens)
      (P : ∀ i, (M.restrict (U i).ι).Presentation),
      IsOpenCover U ∧ (∀ i, IsAffineOpen (U i)) ∧ ∀ i, (P i).IsFinite :=
  Scheme.Modules.exists_isOpenCover_isFinite_presentation M
```

The index types of a presentation may be empty. The zero module and zero ring
are permitted; neither quasi-compactness nor nontriviality is required. This
API does not reflect finite presentation from an arbitrary affine global-section
module, identify a restriction with a tilde module, or identify native finite
presentation with `Module.IsCoherent` or categorical finite-presentability. It
does not imply projectivity, positive rank, nonzero ring or a finite affine cover.

The finite-index and tilde constructions adapt Prism's original Formal
Frontier proof. The affine-chart construction adapts mathlib's
`Scheme.Modules.exists_isOpenCover_presentation`, retaining Weihong Xu's
2024 notice and the eight original authors in the Lean header. The native
interface and clients are Formal Frontier contributions; see [Credits](CREDITS.md).
