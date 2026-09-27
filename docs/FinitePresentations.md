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

The generic finite-index/global proof and tilde presentation proof adapt Prism's
native construction. The affine-chart construction adapts the pinned mathlib
`Scheme.Modules.exists_isOpenCover_presentation` (2024 Weihong Xu copyright;
original file authors Kevin Buzzard, Johan Commelin, Amelia Livingston, Sophie
Morel, Jujian Zhang, Weihong Xu, Andrew Yang and Brian Nugent, Apache-2.0).
Prism supplied the finite-witness refinement; the API, clients and guide were
adapted by Worker B Hive Task
`hive-request-889e4f46f3bdf27bdedb362ee6259c9d0564e57e`, UID
`21a872d7-a565-4f28-b2f8-5eae65e02474`. Mathlib supplies the native
presentations, quasi-coherent data, open refinement and tilde construction.
Worker B Hive Task `hive-request-c188a7b61cec0b11919933ddbae7367b7e535918`,
UID `91c509cb-33b1-46e1-a20f-46a2fd73ac50`, transferred the reviewed
incubator APIs into the scheme-properties modules, adapting imports and clients.
Source-specific mathematical correspondence and coverage are separate from
this reusable API.
