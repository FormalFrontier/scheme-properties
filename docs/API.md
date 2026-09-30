# Historical API reference (navigation-adjusted)

This is the historical 73-module native reference from the original
[generated API page](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/docs/API.md)
at published revision `6b204a3e49f022e51d78a9f93e77513b99a87e00`.
Only this page's historical navigation links and explanatory text have been
adjusted; its native signatures, docstrings, API notes and source ranges were
not regenerated. It is not a current 114-module API census or byte-identical
generated output. Access to the linked published repository currently requires
authorization; public visibility is a separate decision.

This reference contains 381 native display sites in 36 library modules:
230 theorems, 99 definitions, 42 instances, five classes and five constructors.
The aggregate, 15 example modules and 21 test modules have zero display sites;
that does not mean they contain no mathematical bodies or generated declarations.
Import `SchemeProperties` for the library; examples and tests are separate targets.

These are native doc-gen4 display signatures, not complete declarations with proof bodies.
All visible tokens, including implicit binders and noncomputable modifiers, are preserved;
only whitespace is normalized. Pretty-printing uses source namespaces, notation and
inference; consult the source for suppressed inferred types and universe conventions.
Displayed fragments need not elaborate alone in a fresh namespace.

Display counts are not a raw/private declaration census or proof certification.
This documentation generator does not determine release or source-coverage acceptance.
Source-range links refer to the matching original published source, **not**
the source lines in this checkout, where later headers have moved some ranges.
For current modules and usage, use the local [reader guide](Guide.md) and
[README](../README.md); the original generated page remains linked above.
See [generation instructions](README.md), the [mathematical guide](Guide.md) and
[exact input manifest](api-manifest.json). Authored notes are labeled separately from source docstrings.

## Complete module inventory

| Module | Scope | Display sites |
| --- | --- | --- |
| `Examples.ComponentBaseChange` | example | 0 |
| `Examples.ComponentBaseChangeAxiomAudit` | example | 0 |
| `Examples.ComponentBaseChangeRoot` | example | 0 |
| `Examples.ComponentProduct` | example | 0 |
| `Examples.ComponentProductAxiomAudit` | example | 0 |
| `Examples.ComponentProductRoot` | example | 0 |
| `Examples.ComponentScheme` | example | 0 |
| `Examples.ComponentSchemeAxiomAudit` | example | 0 |
| `Examples.ComponentSchemeRoot` | example | 0 |
| `Examples.CoproductSections` | example | 0 |
| `Examples.CoproductSectionsAxiomAudit` | example | 0 |
| `Examples.CoproductSectionsRoot` | example | 0 |
| `Examples.CoproductTopology` | example | 0 |
| `Examples.CoproductTopologyAxiomAudit` | example | 0 |
| `Examples.CoproductTopologyRoot` | example | 0 |
| `SchemeProperties` | aggregate | 0 |
| `SchemeProperties.CoherentQuasicoherent` | library | 7 |
| `SchemeProperties.CoherentQuasicoherentLocality` | library | 3 |
| `SchemeProperties.ComponentBaseChange` | library | 25 |
| `SchemeProperties.ComponentFibers` | library | 10 |
| `SchemeProperties.ComponentProduct` | library | 17 |
| `SchemeProperties.ComponentScheme` | library | 31 |
| `SchemeProperties.ConnectedComponents` | library | 11 |
| `SchemeProperties.CoproductSections` | library | 3 |
| `SchemeProperties.CoproductTopology` | library | 2 |
| `SchemeProperties.Factorial` | library | 16 |
| `SchemeProperties.FactorialNormal` | library | 1 |
| `SchemeProperties.FiniteTypePoints` | library | 35 |
| `SchemeProperties.GeometricConnectedness` | library | 11 |
| `SchemeProperties.GlobalSectionsBaseChange` | library | 31 |
| `SchemeProperties.IdealSheafModule` | library | 14 |
| `SchemeProperties.Integral` | library | 7 |
| `SchemeProperties.ModuleProperties` | library | 19 |
| `SchemeProperties.ModuleTensor` | library | 26 |
| `SchemeProperties.ModuleTensorAffine` | library | 2 |
| `SchemeProperties.ModuleTensorLocalization` | library | 31 |
| `SchemeProperties.ModuleTensorRestriction` | library | 2 |
| `SchemeProperties.NoetherianComponents` | library | 8 |
| `SchemeProperties.Normal` | library | 25 |
| `SchemeProperties.NormalEtale` | library | 3 |
| `SchemeProperties.NormalLocalization` | library | 2 |
| `SchemeProperties.NormalPolynomial` | library | 2 |
| `SchemeProperties.NormalSeparable` | library | 3 |
| `SchemeProperties.NormalSeparableScheme` | library | 1 |
| `SchemeProperties.PresheafModuleTensorStalk` | library | 6 |
| `SchemeProperties.QcqsModuleLocalization` | library | 4 |
| `SchemeProperties.Quasicoherent` | library | 7 |
| `SchemeProperties.QuasicoherentAbelian` | library | 9 |
| `SchemeProperties.Reduced` | library | 3 |
| `SchemeProperties.SheafFinitePresentation` | library | 1 |
| `SchemeProperties.StructureSheaf` | library | 1 |
| `SchemeProperties.Torsion` | library | 2 |
| `Test.CoherentLocalityOrdinaryImport` | test | 0 |
| `Test.CoherentQuasicoherentAxioms` | test | 0 |
| `Test.CoherentQuasicoherentClient` | test | 0 |
| `Test.ComponentFibersOrdinaryImport` | test | 0 |
| `Test.ComponentProductOrdinaryImport` | test | 0 |
| `Test.FactorialNormalOrdinaryImport` | test | 0 |
| `Test.GlobalSectionsBaseChangeOrdinaryImport` | test | 0 |
| `Test.IdealSheafModuleAxioms` | test | 0 |
| `Test.IdealSheafModuleClient` | test | 0 |
| `Test.IdealSheafModuleRootClient` | test | 0 |
| `Test.ModuleTensorAxioms` | test | 0 |
| `Test.ModuleTensorClient` | test | 0 |
| `Test.ModuleTensorRestrictionAxioms` | test | 0 |
| `Test.ModuleTensorRestrictionClient` | test | 0 |
| `Test.ModuleTensorRestrictionRootClient` | test | 0 |
| `Test.ModuleTensorRootClient` | test | 0 |
| `Test.QuasicoherentAbelianAxioms` | test | 0 |
| `Test.QuasicoherentAbelianClient` | test | 0 |
| `Test.SchemeSevenRepairsClient` | test | 0 |
| `Test.StructureSheafAxioms` | test | 0 |
| `Test.StructureSheafClient` | test | 0 |

## SchemeProperties.CoherentQuasicoherent

<a id="api-0e33a5b022150b6c"></a>

### `AlgebraicGeometry.Scheme.Modules.isCoherent_basicOpen_of_qcqs`

```lean
theorem AlgebraicGeometry.Scheme.Modules.isCoherent_basicOpen_of_qcqs {X : Scheme} (M : X.Modules) [SheafOfModules.IsQuasicoherent M] {U : X.Opens} (hU : IsCompact U.carrier) (hU' : IsQuasiSeparated U.carrier) (f : ↑(X.presheaf.obj (Opposite.op U))) (hM : Module.IsCoherent ↑(X.presheaf.obj (Opposite.op U)) ↑(M.presheaf.obj (Opposite.op U))) : Module.IsCoherent ↑(X.presheaf.obj (Opposite.op (X.basicOpen f))) ↑(M.presheaf.obj (Opposite.op (X.basicOpen f)))
```

Coherence of quasicoherent sections is preserved by restriction to a basic
open of a compact quasiseparated open.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/CoherentQuasicoherent.lean#L40-L59) (native source range).

<a id="api-4a4619ae4eda4de6"></a>

### `AlgebraicGeometry.Scheme.Modules.isCoherent_basicOpen_of_qcqs_of_top`

```lean
theorem AlgebraicGeometry.Scheme.Modules.isCoherent_basicOpen_of_qcqs_of_top {X : Scheme} (M : X.Modules) [SheafOfModules.IsQuasicoherent M] [CompactSpace ↥X] [QuasiSeparatedSpace ↥X] (f : ↑(X.presheaf.obj (Opposite.op ⊤))) (hM : Module.IsCoherent ↑(X.presheaf.obj (Opposite.op ⊤)) ↑(M.presheaf.obj (Opposite.op ⊤))) : Module.IsCoherent ↑(X.presheaf.obj (Opposite.op (X.basicOpen f))) ↑(M.presheaf.obj (Opposite.op (X.basicOpen f)))
```

The global-sections specialization of `isCoherent_basicOpen_of_qcqs`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/CoherentQuasicoherent.lean#L61-L67) (native source range).

<a id="api-9393a71217e6d95d"></a>

### `AlgebraicGeometry.Scheme.Modules.isCoherent_of_span_basicOpen_of_qcqs`

```lean
theorem AlgebraicGeometry.Scheme.Modules.isCoherent_of_span_basicOpen_of_qcqs {X : Scheme} (M : X.Modules) [SheafOfModules.IsQuasicoherent M] {U : X.Opens} (hU : IsCompact U.carrier) (hU' : IsQuasiSeparated U.carrier) (s : Set ↑(X.presheaf.obj (Opposite.op U))) (hs : Ideal.span s = ⊤) (h : ∀ (g : ↑s), Module.IsCoherent ↑(X.presheaf.obj (Opposite.op (X.basicOpen ↑g))) ↑(M.presheaf.obj (Opposite.op (X.basicOpen ↑g)))) : Module.IsCoherent ↑(X.presheaf.obj (Opposite.op U)) ↑(M.presheaf.obj (Opposite.op U))
```

Coherence of the section module on a compact quasiseparated open descends
from any set-indexed spanning family of its basic opens.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/CoherentQuasicoherent.lean#L69-L89) (native source range).

<a id="api-240a655468577efb"></a>

### `AlgebraicGeometry.Scheme.Modules.isCoherent_of_span_basicOpen_of_qcqs_of_top`

```lean
theorem AlgebraicGeometry.Scheme.Modules.isCoherent_of_span_basicOpen_of_qcqs_of_top {X : Scheme} (M : X.Modules) [SheafOfModules.IsQuasicoherent M] [CompactSpace ↥X] [QuasiSeparatedSpace ↥X] (s : Set ↑(X.presheaf.obj (Opposite.op ⊤))) (hs : Ideal.span s = ⊤) (h : ∀ (g : ↑s), Module.IsCoherent ↑(X.presheaf.obj (Opposite.op (X.basicOpen ↑g))) ↑(M.presheaf.obj (Opposite.op (X.basicOpen ↑g)))) : Module.IsCoherent ↑(X.presheaf.obj (Opposite.op ⊤)) ↑(M.presheaf.obj (Opposite.op ⊤))
```

The global-sections specialization of
`isCoherent_of_span_basicOpen_of_qcqs`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/CoherentQuasicoherent.lean#L91-L100) (native source range).

<a id="api-81d2de6251c02297"></a>

### `AlgebraicGeometry.isCoherentOnSpec`

```lean
def AlgebraicGeometry.isCoherentOnSpec (R : CommRingCat) : CategoryTheory.ObjectProperty (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory
```

The same-universe coherent-module property on the native category of
quasicoherent modules over an affine spectrum.

This is literally the inverse image of `ModuleCat.isCoherent` under the inverse
of `tildeEquiv`; it does not introduce a new notion of quasicoherence or identify
coherence with finite presentation.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/CoherentQuasicoherent.lean#L108-L117) (native source range).

<a id="api-11b895ff8c0278ab"></a>

### `AlgebraicGeometry.isCoherentOnSpec_iff`

```lean
theorem AlgebraicGeometry.isCoherentOnSpec_iff (R : CommRingCat) (Q : (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory) : isCoherentOnSpec R Q ↔ Module.IsCoherent ↑R ↑(tildeEquiv.inverse.obj Q)
```

Membership in `isCoherentOnSpec` is literally coherence of the module
obtained from affine global sections by `tildeEquiv.inverse`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/CoherentQuasicoherent.lean#L119-L126) (native source range).

<a id="api-7256cd2d800e8811"></a>

### `AlgebraicGeometry.isCoherentOnSpec_tilde_iff`

```lean
theorem AlgebraicGeometry.isCoherentOnSpec_tilde_iff (R : CommRingCat) (M : ModuleCat ↑R) : isCoherentOnSpec R { obj := tilde M, property := ⋯ } ↔ Module.IsCoherent ↑R ↑M
```

A literal affine sheaf `tilde M` has the coherent affine property exactly
when `M` is a coherent module.  The statement follows the same-universe
boundary of mathlib's `tildeEquiv`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/CoherentQuasicoherent.lean#L128-L143) (native source range).


## SchemeProperties.CoherentQuasicoherentLocality

<a id="api-3dd4dfac069e8497"></a>

### `AlgebraicGeometry.Scheme.Modules.isCoherentOnSpec_restrict_affineOpen_iff`

```lean
theorem AlgebraicGeometry.Scheme.Modules.isCoherentOnSpec_restrict_affineOpen_iff {X : Scheme} (M : X.Modules) [SheafOfModules.IsQuasicoherent M] (V : X.Opens) (hV : IsAffineOpen V) : isCoherentOnSpec (X.presheaf.obj (Opposite.op V)) { obj := (M.restrict V.ι).restrict hV.isoSpec.inv, property := ⋯ } ↔ Module.IsCoherent ↑(X.presheaf.obj (Opposite.op V)) ↑(M.presheaf.obj (Opposite.op V))
```

On an affine open, the native affine coherent property is equivalent to
coherence of the module of sections on that open.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/CoherentQuasicoherentLocality.lean#L33-L45) (native source range).

<a id="api-325935b00ff57402"></a>

### `AlgebraicGeometry.Scheme.Modules.isCoherentQuasicoherent`

```lean
def AlgebraicGeometry.Scheme.Modules.isCoherentQuasicoherent (X : Scheme) : CategoryTheory.ObjectProperty (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory
```

The object property of being a coherent quasicoherent module on a scheme.

The definition uses the existing native category of quasicoherent modules and
requires the corresponding affine module to be coherent on every affine open.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/CoherentQuasicoherentLocality.lean#L47-L63) (native source range).

<a id="api-ffd69c3a5dc28510"></a>

### `AlgebraicGeometry.Scheme.Modules.isCoherentQuasicoherent_iff_affineOpenCover`

```lean
theorem AlgebraicGeometry.Scheme.Modules.isCoherentQuasicoherent_iff_affineOpenCover (X : Scheme) (Q : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) {I : Type u} (U : I → X.Opens) (hU : TopologicalSpace.IsOpenCover U) (hUaff : ∀ (i : I), IsAffineOpen (U i)) : let M := Q.obj; have x := ⋯; isCoherentQuasicoherent X Q ↔ ∀ (i : I), isCoherentOnSpec (X.presheaf.obj (Opposite.op (U i))) { obj := (M.restrict (U i).ι).restrict ⋯.isoSpec.inv, property := ⋯ }
```

Coherence of a quasicoherent module can be checked on any fixed affine open
cover.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/CoherentQuasicoherentLocality.lean#L65-L109) (native source range).


## SchemeProperties.ComponentBaseChange

<a id="api-6e0d3d47a73fd343"></a>

### `AlgebraicGeometry.componentGlobalSectionsAlgebra`

```lean
noncomputable def AlgebraicGeometry.componentGlobalSectionsAlgebra {F : Type u} [Field F] (X : CategoryTheory.Over (Spec ↧F)) : Algebra F ↑(X.left.presheaf.obj (Opposite.op ⊤))
```

The structure algebra on global sections used throughout this module.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentBaseChange.lean#L43-L47) (native source range).

<a id="api-558d7571d1f7caf1"></a>

### `AlgebraicGeometry.tensorProductRightAlgebra`

```lean
def AlgebraicGeometry.tensorProductRightAlgebra {k K : Type u} [Field k] [Field K] [Algebra k K] (A : Type u) [CommRing A] [Algebra k A] : Algebra K (TensorProduct k A K)
```

The algebra structure on the right-oriented tensor model.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentBaseChange.lean#L49-L53) (native source range).

<a id="api-d065cde2bc6c6dee"></a>

### `AlgebraicGeometry.baseChangeLocallyOfFiniteType`

```lean
theorem AlgebraicGeometry.baseChangeLocallyOfFiniteType {k K : Type u} [Field k] [Field K] [Algebra k K] (X : CategoryTheory.Over (Spec ↧k)) [LocallyOfFiniteType X.hom] : LocallyOfFiniteType (schemeBaseChange X).hom
```

**API note (not a source docstring):** The local instance `AlgebraicGeometry.baseChangeLocallyOfFiniteType` in `ComponentBaseChange` provides `LocallyOfFiniteType` for the structure morphism of `schemeBaseChange X` over `K`, from the corresponding assumption on `X.hom` over `k`. This is a field-extension pullback stability input for component schemes, not a finite-type assertion about an unrelated map.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentBaseChange.lean#L55-L61) (native source range).

<a id="api-f8b052a9ed163b2c"></a>

### `AlgebraicGeometry.baseChangeQuasiCompact`

```lean
theorem AlgebraicGeometry.baseChangeQuasiCompact {k K : Type u} [Field k] [Field K] [Algebra k K] (X : CategoryTheory.Over (Spec ↧k)) [QuasiCompact X.hom] : QuasiCompact (schemeBaseChange X).hom
```

**API note (not a source docstring):** The local instance `AlgebraicGeometry.baseChangeQuasiCompact` in `ComponentBaseChange` makes the structure morphism of a field-base-changed `X` quasi-compact when `X.hom` was quasi-compact over `k`. Its proof identifies the new structure morphism with a pullback projection and invokes preservation under base change; it supplies an input for the component-scheme comparisons in the first part of this module.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentBaseChange.lean#L63-L69) (native source range).

<a id="api-ac7eb03c8de48de5"></a>

### `AlgebraicGeometry.componentScalarExtensionAlgHom`

```lean
noncomputable def AlgebraicGeometry.componentScalarExtensionAlgHom {k K : Type u} [Field k] [Field K] [Algebra k K] (X : CategoryTheory.Over (Spec ↧k)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] : TensorProduct k (↥(componentSubalgebra X)) K →ₐ[K] ↑((schemeBaseChange X).left.presheaf.obj (Opposite.op ⊤))
```

The literal scalar-extension map from the coordinate algebra of the
base-changed component scheme to the global sections of the base-changed
source scheme.

The source is `componentSubalgebra X ⊗[k] K`, matching
`baseChangeSpecOverIso`; internally the accepted global-sections equivalence
uses the factor-reversed tensor product.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentBaseChange.lean#L98-L113) (native source range).

<a id="api-cf8e032278bb966b"></a>

### `AlgebraicGeometry.baseChangedComponentSubalgebra`

```lean
noncomputable abbrev AlgebraicGeometry.baseChangedComponentSubalgebra {k K : Type u} [Field k] [Field K] [Algebra k K] (X : CategoryTheory.Over (Spec ↧k)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] : Subalgebra K ↑((schemeBaseChange X).left.presheaf.obj (Opposite.op ⊤))
```

The literal range of the scalar-extended selected component algebra.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentBaseChange.lean#L115-L120) (native source range).

<a id="api-81e2ab06b08495d8"></a>

### `AlgebraicGeometry.componentBaseChangeComparisonAlgHom`

```lean
noncomputable def AlgebraicGeometry.componentBaseChangeComparisonAlgHom {k K : Type u} [Field k] [Field K] [Algebra k K] (X : CategoryTheory.Over (Spec ↧k)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] : TensorProduct k (↥(componentSubalgebra X)) K →ₐ[K] ↥(componentSubalgebra (schemeBaseChange X))
```

The contravariant algebra map defining the canonical comparison of
component schemes.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentBaseChange.lean#L257-L267) (native source range).

<a id="api-573d085dd1c5cda5"></a>

### `AlgebraicGeometry.componentBaseChangeComparisonAlgHom_injective`

```lean
theorem AlgebraicGeometry.componentBaseChangeComparisonAlgHom_injective {k K : Type u} [Field k] [Field K] [Algebra k K] (X : CategoryTheory.Over (Spec ↧k)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] : Function.Injective ⇑(componentBaseChangeComparisonAlgHom X)
```

The contravariant algebra comparison is always injective.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentBaseChange.lean#L295-L302) (native source range).

<a id="api-c5bd2e29d22de645"></a>

### `AlgebraicGeometry.componentBaseChangeComparison`

```lean
noncomputable def AlgebraicGeometry.componentBaseChangeComparison {k K : Type u} [Field k] [Field K] [Algebra k K] (X : CategoryTheory.Over (Spec ↧k)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] : componentScheme (schemeBaseChange X) ⟶ schemeBaseChange (componentScheme X)
```

The literal comparison from the selected component scheme of the
base-changed source to the categorical base change of the selected component
scheme.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentBaseChange.lean#L557-L566) (native source range).

<a id="api-446f30095ff32d87"></a>

### `AlgebraicGeometry.toComponentScheme_comp_componentBaseChangeComparison`

```lean
theorem AlgebraicGeometry.toComponentScheme_comp_componentBaseChangeComparison {k K : Type u} [Field k] [Field K] [Algebra k K] (X : CategoryTheory.Over (Spec ↧k)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] : CategoryTheory.CategoryStruct.comp (toComponentScheme (schemeBaseChange X)) (componentBaseChangeComparison X) = baseChangeMap (toComponentScheme X)
```

The literal comparison commutes with the base-changed canonical map.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentBaseChange.lean#L591-L601) (native source range).

<a id="api-b02eb45c66f5256c"></a>

### `AlgebraicGeometry.componentGlobalSectionsAlgebra'`

```lean
noncomputable def AlgebraicGeometry.componentGlobalSectionsAlgebra' {F : Type u} [Field F] (X : CategoryTheory.Over (Spec ↧F)) : Algebra F ↑(X.left.presheaf.obj (Opposite.op ⊤))
```

The base-field algebra structure on global sections used in this module.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentBaseChange.lean#L612-L616) (native source range).

<a id="api-2cab626c5010d593"></a>

### `AlgebraicGeometry.tensorProductRightAlgebra'`

```lean
def AlgebraicGeometry.tensorProductRightAlgebra' {F L A : Type u} [CommRing F] [CommRing L] [Algebra F L] [CommRing A] [Algebra F A] : Algebra L (TensorProduct F A L)
```

The extension-field algebra structure on a right-oriented tensor product.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentBaseChange.lean#L618-L623) (native source range).

<a id="api-526ff2b3c8f4c6a4"></a>

### `AlgebraicGeometry.baseChangeLocallyOfFiniteType'`

```lean
theorem AlgebraicGeometry.baseChangeLocallyOfFiniteType' {k K : Type u} [Field k] [Field K] [Algebra k K] (X : CategoryTheory.Over (Spec ↧k)) [LocallyOfFiniteType X.hom] : LocallyOfFiniteType (schemeBaseChange X).hom
```

**API note (not a source docstring):** The local instance `AlgebraicGeometry.baseChangeLocallyOfFiniteType'` in `ComponentBaseChange` retains local finite type for the structure morphism of `schemeBaseChange X` along a field extension `k → K`, assuming the original structure morphism has that property. Its implementation recognizes the new map as the second projection of a pullback; the instance is local to the later connected-component construction.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentBaseChange.lean#L625-L631) (native source range).

<a id="api-05ed23177b299572"></a>

### `AlgebraicGeometry.baseChangeQuasiCompact'`

```lean
theorem AlgebraicGeometry.baseChangeQuasiCompact' {k K : Type u} [Field k] [Field K] [Algebra k K] (X : CategoryTheory.Over (Spec ↧k)) [QuasiCompact X.hom] : QuasiCompact (schemeBaseChange X).hom
```

**API note (not a source docstring):** The local instance `AlgebraicGeometry.baseChangeQuasiCompact'` in `ComponentBaseChange` supplies quasi-compactness of the structure morphism of `schemeBaseChange X` to the extension field `K`, provided the structure morphism of `X` over `k` is quasi-compact. It applies the pullback stability of quasi-compact morphisms; this is a statement about the base-changed morphism, not an assertion about arbitrary schemes without the original quasi-compactness hypothesis.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentBaseChange.lean#L633-L639) (native source range).

<a id="api-1044698a71b0cc41"></a>

### `AlgebraicGeometry.toConnectedComponentsSpec`

```lean
noncomputable def AlgebraicGeometry.toConnectedComponentsSpec {k : Type u} [Field k] (X : CategoryTheory.Over (Spec ↧k)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] : X ⟶ specOver k (ConnectedComponents ↥X.left → k)
```

A qc locally-finite-type scheme maps canonically to one copy of the base
point for each of its connected components.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentBaseChange.lean#L643-L678) (native source range).

<a id="api-05e03eae10c5f26f"></a>

### `AlgebraicGeometry.toConnectedComponentsSpec_surjective`

```lean
theorem AlgebraicGeometry.toConnectedComponentsSpec_surjective {k : Type u} [Field k] (X : CategoryTheory.Over (Spec ↧k)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] : Function.Surjective ⇑(CategoryTheory.Over.Hom.left (toConnectedComponentsSpec X))
```

The map to the split finite-etale scheme of connected components is
surjective on the underlying spaces.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentBaseChange.lean#L680-L718) (native source range).

<a id="api-dcf2ea33c01ad4ea"></a>

### `AlgebraicGeometry.componentSubalgebra_finrank_eq_natCard_connectedComponents`

```lean
theorem AlgebraicGeometry.componentSubalgebra_finrank_eq_natCard_connectedComponents {k : Type u} [Field k] [IsSepClosed k] (X : CategoryTheory.Over (Spec ↧k)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] : Module.finrank k ↥(componentSubalgebra X) = Nat.card (ConnectedComponents ↥X.left)
```

Over a separably closed field, the selected component algebra has exactly
one basis vector for each connected component.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentBaseChange.lean#L754-L784) (native source range).

<a id="api-415631cd0c717635"></a>

### `AlgebraicGeometry.natCard_connectedComponents_schemeBaseChange_eq_of_isSepClosed`

```lean
theorem AlgebraicGeometry.natCard_connectedComponents_schemeBaseChange_eq_of_isSepClosed {k K : Type u} [Field k] [Field K] [Algebra k K] [IsSepClosed k] (X : CategoryTheory.Over (Spec ↧k)) : Nat.card (ConnectedComponents ↥(schemeBaseChange X).left) = Nat.card (ConnectedComponents ↥X.left)
```

Base change from a separably closed field preserves the connected-component
set, including for arbitrary transcendental extensions.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentBaseChange.lean#L788-L800) (native source range).

<a id="api-681ed4eee8afc4bb"></a>

### `AlgebraicGeometry.componentSubalgebra_finrank_eq_natCard_separableClosure`

```lean
theorem AlgebraicGeometry.componentSubalgebra_finrank_eq_natCard_separableClosure {k : Type u} [Field k] (X : CategoryTheory.Over (Spec ↧k)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] : Module.finrank k ↥(componentSubalgebra X) = Nat.card (ConnectedComponents ↥(schemeBaseChange X).left)
```

The rank of the selected component algebra over an arbitrary field is the
number of connected components after passage to its separable closure.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentBaseChange.lean#L1045-L1076) (native source range).

<a id="api-deff7d65eb653370"></a>

### `AlgebraicGeometry.natCard_connectedComponents_separableClosures_eq`

```lean
theorem AlgebraicGeometry.natCard_connectedComponents_separableClosures_eq {k K : Type u} [Field k] [Field K] [Algebra k K] (X : CategoryTheory.Over (Spec ↧k)) : Nat.card (ConnectedComponents ↥(schemeBaseChange X).left) = Nat.card (ConnectedComponents ↥(schemeBaseChange (schemeBaseChange X)).left)
```

Geometric connected-component counts are unchanged by an arbitrary field
extension.  Both separable closures are compared inside an algebraic closure
of the larger field.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentBaseChange.lean#L1078-L1119) (native source range).

<a id="api-c2948c5ba61807bd"></a>

### `AlgebraicGeometry.componentBaseChangeComparisonAlgHom_surjective`

```lean
theorem AlgebraicGeometry.componentBaseChangeComparisonAlgHom_surjective {k K : Type u} [Field k] [Field K] [Algebra k K] (X : CategoryTheory.Over (Spec ↧k)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] : Function.Surjective ⇑(componentBaseChangeComparisonAlgHom X)
```

The canonical component-algebra comparison is surjective for every field
extension, with no algebraicity or separability assumption.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentBaseChange.lean#L1162-L1197) (native source range).

<a id="api-b060e7dabc241483"></a>

### `AlgebraicGeometry.baseChangedComponentSubalgebra_eq`

```lean
theorem AlgebraicGeometry.baseChangedComponentSubalgebra_eq {k K : Type u} [Field k] [Field K] [Algebra k K] (X : CategoryTheory.Over (Spec ↧k)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] : baseChangedComponentSubalgebra X = componentSubalgebra (schemeBaseChange X)
```

The scalar-extended and newly selected component subalgebras are literally
equal in the global-sections ring.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentBaseChange.lean#L1213-L1221) (native source range).

<a id="api-a7720945cb24691d"></a>

### `AlgebraicGeometry.componentBaseChangeComparisonAlgEquiv`

```lean
noncomputable def AlgebraicGeometry.componentBaseChangeComparisonAlgEquiv {k K : Type u} [Field k] [Field K] [Algebra k K] (X : CategoryTheory.Over (Spec ↧k)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] : TensorProduct k (↥(componentSubalgebra X)) K ≃ₐ[K] ↥(componentSubalgebra (schemeBaseChange X))
```

The canonical algebra equivalence for arbitrary field extension.  Its
forward map is definitionally the accepted literal comparison.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentBaseChange.lean#L1223-L1232) (native source range).

<a id="api-1f8fc7a54fc15064"></a>

### `AlgebraicGeometry.componentBaseChangeIso`

```lean
noncomputable def AlgebraicGeometry.componentBaseChangeIso {k K : Type u} [Field k] [Field K] [Algebra k K] (X : CategoryTheory.Over (Spec ↧k)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] : componentScheme (schemeBaseChange X) ≅ schemeBaseChange (componentScheme X)
```

The literal categorical base-change isomorphism for arbitrary field
extension.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentBaseChange.lean#L1253-L1261) (native source range).

<a id="api-17c2a7137108f26f"></a>

### `AlgebraicGeometry.componentBaseChangeIso_hom`

```lean
theorem AlgebraicGeometry.componentBaseChangeIso_hom {k K : Type u} [Field k] [Field K] [Algebra k K] (X : CategoryTheory.Over (Spec ↧k)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] : (componentBaseChangeIso X).hom = componentBaseChangeComparison X
```

The forward map of the categorical base-change isomorphism is exactly the
canonical `componentBaseChangeComparison`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentBaseChange.lean#L1263-L1272) (native source range).


## SchemeProperties.ComponentFibers

<a id="api-0dedc18cae9d7b0d"></a>

### `AlgebraicGeometry.componentFibersGlobalSectionsAlgebra`

```lean
noncomputable def AlgebraicGeometry.componentFibersGlobalSectionsAlgebra {F : Type u} [Field F] (X : CategoryTheory.Over (Spec ↧F)) : Algebra F ↑(X.left.presheaf.obj (Opposite.op ⊤))
```

The scalar algebra structure on global sections used by the component
construction.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentFibers.lean#L42-L47) (native source range).

<a id="api-420ee64a59dff856"></a>

### `AlgebraicGeometry.range_fiberι_toComponentScheme_eq_connectedComponent`

```lean
theorem AlgebraicGeometry.range_fiberι_toComponentScheme_eq_connectedComponent {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (x : ↥(componentScheme X).left) (y : ↥X.left) (hy : (CategoryTheory.Over.Hom.left (toComponentScheme X)) y = x) : Set.range ⇑(Scheme.Hom.fiberι (CategoryTheory.Over.Hom.left (toComponentScheme X)) x) = connectedComponent y
```

The underlying range of the scheme-theoretic fibre of the canonical map
to the component scheme is the connected component containing any point that
maps to the chosen target point.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentFibers.lean#L89-L162) (native source range).

<a id="api-ccd08ea141519870"></a>

### `AlgebraicGeometry.toComponentSchemeLocallyOfFiniteType`

```lean
instance AlgebraicGeometry.toComponentSchemeLocallyOfFiniteType {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] : LocallyOfFiniteType (CategoryTheory.Over.Hom.left (toComponentScheme X))
```

The canonical map to the component scheme is locally of finite type.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentFibers.lean#L176-L184) (native source range).

<a id="api-a96c98432e59bf5d"></a>

### `AlgebraicGeometry.toComponentSchemeQuasiCompact`

```lean
instance AlgebraicGeometry.toComponentSchemeQuasiCompact {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] : QuasiCompact (CategoryTheory.Over.Hom.left (toComponentScheme X))
```

The canonical map to the component scheme is quasi-compact.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentFibers.lean#L186-L196) (native source range).

<a id="api-a39495f1b3164f5f"></a>

### `AlgebraicGeometry.componentSchemeFiber`

```lean
noncomputable def AlgebraicGeometry.componentSchemeFiber {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (x : ↥(componentScheme X).left) : CategoryTheory.Over (Spec ((componentScheme X).left.residueField x))
```

The scheme-theoretic fibre of the component map, regarded over the
residue field of the selected component point.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentFibers.lean#L198-L205) (native source range).

<a id="api-789e83bbd8f843d0"></a>

### `AlgebraicGeometry.fiberToComponentSchemeLocallyOfFiniteType`

```lean
instance AlgebraicGeometry.fiberToComponentSchemeLocallyOfFiniteType {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (x : ↥(componentScheme X).left) : LocallyOfFiniteType (componentSchemeFiber X x).hom
```

A component-scheme fibre is locally of finite type over its residue
field.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentFibers.lean#L207-L215) (native source range).

<a id="api-2814f250436df743"></a>

### `AlgebraicGeometry.fiberToComponentSchemeQuasiCompact`

```lean
instance AlgebraicGeometry.fiberToComponentSchemeQuasiCompact {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (x : ↥(componentScheme X).left) : QuasiCompact (componentSchemeFiber X x).hom
```

A component-scheme fibre is quasi-compact over its residue field.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentFibers.lean#L217-L224) (native source range).

<a id="api-4e20f51b5d8a0992"></a>

### `AlgebraicGeometry.geometricallyConnected_fiber_toComponentScheme`

```lean
theorem AlgebraicGeometry.geometricallyConnected_fiber_toComponentScheme {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (x : ↥(componentScheme X).left) : GeometricallyConnected (Scheme.Hom.fiberToSpecResidueField (CategoryTheory.Over.Hom.left (toComponentScheme X)) x)
```

A scheme-theoretic fibre of the component map is geometrically connected
over its residue field.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentFibers.lean#L289-L447) (native source range).

<a id="api-3285b9940b346ccd"></a>

### `AlgebraicGeometry.geometricallyConnected_of_connectedSpace_of_section`

```lean
theorem AlgebraicGeometry.geometricallyConnected_of_connectedSpace_of_section {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [ConnectedSpace ↥X.left] (p : CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id (Spec ↧K)) ⟶ X) : GeometricallyConnected X.hom
```

A connected scheme, locally of finite type and quasi-compact over a field,
is geometrically connected if its structure morphism has a section.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentFibers.lean#L449-L509) (native source range).

<a id="api-df53c8dd6c62d9f8"></a>

### `AlgebraicGeometry.componentSubalgebra_fiber_eq_bot`

```lean
theorem AlgebraicGeometry.componentSubalgebra_fiber_eq_bot {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (x : ↥(componentScheme X).left) : componentSubalgebra (componentSchemeFiber X x) = ⊥
```

The greatest finite-etale subalgebra of the global functions on a
component-map fibre is exactly the scalar subalgebra.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentFibers.lean#L511-L554) (native source range).


## SchemeProperties.ComponentProduct

<a id="api-d287d35975cb44bc"></a>

### `AlgebraicGeometry.tensorLocallyOfFiniteType`

```lean
theorem AlgebraicGeometry.tensorLocallyOfFiniteType {K : Type u} [Field K] (X Y : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] : LocallyOfFiniteType (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y).hom
```

**API note (not a source docstring):** The local instance `AlgebraicGeometry.tensorLocallyOfFiniteType` in `ComponentProduct` establishes local finite type for the structure map of the fibre product `X ⊗ Y` over `Spec K`, assuming local finite type of both factor structure maps. It uses the first pullback projection and closure under composition, not a claim that all products of arbitrary over-field schemes have this property.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentProduct.lean#L43-L51) (native source range).

<a id="api-486c9f4b7091dd52"></a>

### `AlgebraicGeometry.tensorQuasiCompact`

```lean
theorem AlgebraicGeometry.tensorQuasiCompact {K : Type u} [Field K] (X Y : CategoryTheory.Over (Spec ↧K)) [QuasiCompact X.hom] [QuasiCompact Y.hom] : QuasiCompact (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y).hom
```

**API note (not a source docstring):** The local instance `AlgebraicGeometry.tensorQuasiCompact` in `ComponentProduct` gives a quasi-compact structure morphism for the fibre product `X ⊗ Y` in `Over (Spec K)` when each factor's structure morphism is quasi-compact. It factors the product map through a pullback projection and uses quasi-compactness under pullback and composition; both factor assumptions are material.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentProduct.lean#L53-L61) (native source range).

<a id="api-43093b00c10b7622"></a>

### `AlgebraicGeometry.componentSchemeMapOfHom`

```lean
noncomputable def AlgebraicGeometry.componentSchemeMapOfHom {K : Type u} [Field K] {X Y : CategoryTheory.Over (Spec ↧K)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] (f : X ⟶ Y) : componentScheme X ⟶ componentScheme Y
```

The map on finite-etale component schemes induced by a morphism of
quasi-compact schemes locally of finite type over a field.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentProduct.lean#L63-L70) (native source range).

<a id="api-099d1d8fa39177ad"></a>

### `AlgebraicGeometry.toComponentScheme_comp_componentSchemeMapOfHom`

```lean
theorem AlgebraicGeometry.toComponentScheme_comp_componentSchemeMapOfHom {K : Type u} [Field K] {X Y : CategoryTheory.Over (Spec ↧K)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] (f : X ⟶ Y) : CategoryTheory.CategoryStruct.comp (toComponentScheme X) (componentSchemeMapOfHom f) = CategoryTheory.CategoryStruct.comp f (toComponentScheme Y)
```

The map on component schemes makes the canonical triangle commute.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentProduct.lean#L72-L81) (native source range).

<a id="api-1d04258d1c7bdcc7"></a>

### `AlgebraicGeometry.toComponentScheme_comp_componentSchemeMapOfHom_assoc`

```lean
theorem AlgebraicGeometry.toComponentScheme_comp_componentSchemeMapOfHom_assoc {K : Type u} [Field K] {X Y : CategoryTheory.Over (Spec ↧K)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] (f : X ⟶ Y) {Z : CategoryTheory.Over (Spec ↧K)} (h : componentScheme Y ⟶ Z) : CategoryTheory.CategoryStruct.comp (toComponentScheme X) (CategoryTheory.CategoryStruct.comp (componentSchemeMapOfHom f) h) = CategoryTheory.CategoryStruct.comp f (CategoryTheory.CategoryStruct.comp (toComponentScheme Y) h)
```

The map on component schemes makes the canonical triangle commute.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentProduct.lean#L73-L73) (native source range).

<a id="api-4d06cdfe7c90d1a4"></a>

### `AlgebraicGeometry.componentSchemeMapOfHom_id`

```lean
theorem AlgebraicGeometry.componentSchemeMapOfHom_id {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] : componentSchemeMapOfHom (CategoryTheory.CategoryStruct.id X) = CategoryTheory.CategoryStruct.id (componentScheme X)
```

The component-scheme map of an identity is the identity.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentProduct.lean#L83-L92) (native source range).

<a id="api-9f35483b30e626fc"></a>

### `AlgebraicGeometry.componentSchemeMapOfHom_comp`

```lean
theorem AlgebraicGeometry.componentSchemeMapOfHom_comp {K : Type u} [Field K] {X Y Z : CategoryTheory.Over (Spec ↧K)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) : componentSchemeMapOfHom (CategoryTheory.CategoryStruct.comp f g) = CategoryTheory.CategoryStruct.comp (componentSchemeMapOfHom f) (componentSchemeMapOfHom g)
```

Component-scheme maps preserve composition.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentProduct.lean#L94-L108) (native source range).

<a id="api-0e7c473f98309295"></a>

### `AlgebraicGeometry.componentSchemeMapOfHom_comp_assoc`

```lean
theorem AlgebraicGeometry.componentSchemeMapOfHom_comp_assoc {K : Type u} [Field K] {X Y Z : CategoryTheory.Over (Spec ↧K)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) {Z✝ : CategoryTheory.Over (Spec ↧K)} (h : componentScheme Z ⟶ Z✝) : CategoryTheory.CategoryStruct.comp (componentSchemeMapOfHom (CategoryTheory.CategoryStruct.comp f g)) h = CategoryTheory.CategoryStruct.comp (componentSchemeMapOfHom f) (CategoryTheory.CategoryStruct.comp (componentSchemeMapOfHom g) h)
```

Component-scheme maps preserve composition.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentProduct.lean#L95-L95) (native source range).

<a id="api-d0215d466a5b59f6"></a>

### `AlgebraicGeometry.componentProductComparison`

```lean
noncomputable def AlgebraicGeometry.componentProductComparison {K : Type u} [Field K] (X Y : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] : componentScheme (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) ⟶ CategoryTheory.MonoidalCategoryStruct.tensorObj (componentScheme X) (componentScheme Y)
```

The canonical comparison from the component scheme of a binary product
to the binary product of the component schemes.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentProduct.lean#L110-L116) (native source range).

<a id="api-50794f209cf99756"></a>

### `AlgebraicGeometry.toComponentScheme_comp_componentProductComparison`

```lean
theorem AlgebraicGeometry.toComponentScheme_comp_componentProductComparison {K : Type u} [Field K] (X Y : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] : CategoryTheory.CategoryStruct.comp (toComponentScheme (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y)) (componentProductComparison X Y) = CategoryTheory.CartesianMonoidalCategory.lift (CategoryTheory.CategoryStruct.comp (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) (toComponentScheme X)) (CategoryTheory.CategoryStruct.comp (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) (toComponentScheme Y))
```

The product comparison is characterized by its canonical triangle with
the two product projections.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentProduct.lean#L118-L131) (native source range).

<a id="api-e21408224b579bd6"></a>

### `AlgebraicGeometry.sourceCompactSpace`

```lean
theorem AlgebraicGeometry.sourceCompactSpace {K : Type u} [Field K] (Z : CategoryTheory.Over (Spec ↧K)) [QuasiCompact Z.hom] : CompactSpace ↥Z.left
```

**API note (not a source docstring):** The local instance `AlgebraicGeometry.sourceCompactSpace` in `ComponentProduct` equips the underlying topological space of `Z.left` with `CompactSpace` when its structure morphism to `Spec K` is quasi-compact. It uses compactness of the spectrum of a field; it does not independently establish local Noetherianity or finite type.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentProduct.lean#L135-L137) (native source range).

<a id="api-cc194a9687f0c5f6"></a>

### `AlgebraicGeometry.sourceIsLocallyNoetherian`

```lean
theorem AlgebraicGeometry.sourceIsLocallyNoetherian {K : Type u} [Field K] (Z : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType Z.hom] : IsLocallyNoetherian Z.left
```

**API note (not a source docstring):** The local instance `AlgebraicGeometry.sourceIsLocallyNoetherian` in `ComponentProduct` derives local Noetherianity of `Z.left` from `LocallyOfFiniteType Z.hom` over the spectrum of a field `K`. The field base matters, and unlike `sourceIsNoetherian`, this instance does not assume quasi-compactness or assert global Noetherianity.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentProduct.lean#L139-L141) (native source range).

<a id="api-4b7d6b6e888397e7"></a>

### `AlgebraicGeometry.sourceIsNoetherian`

```lean
theorem AlgebraicGeometry.sourceIsNoetherian {K : Type u} [Field K] (Z : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] : IsNoetherian Z.left
```

**API note (not a source docstring):** The local instance `AlgebraicGeometry.sourceIsNoetherian` in `ComponentProduct` makes the underlying scheme `Z.left` Noetherian when its map to `Spec K` is both locally of finite type and quasi-compact, with `K` a field. It combines the neighboring local-Noetherian and compactness instances; it is not a Noetherianity theorem for arbitrary base schemes or locally-finite-type maps alone.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentProduct.lean#L143-L144) (native source range).

<a id="api-376636fe7f2ead36"></a>

### `AlgebraicGeometry.baseChangeLocallyOfFiniteTypeProduct`

```lean
theorem AlgebraicGeometry.baseChangeLocallyOfFiniteTypeProduct {k L : Type u} [Field k] [Field L] [Algebra k L] (X : CategoryTheory.Over (Spec ↧k)) [LocallyOfFiniteType X.hom] : LocallyOfFiniteType (schemeBaseChange X).hom
```

**API note (not a source docstring):** The local instance `AlgebraicGeometry.baseChangeLocallyOfFiniteTypeProduct` in `ComponentProduct` transports local finite type of an over-field scheme's structure morphism from `k` to `L` through pullback. This hypothesis is used when applying product/component-scheme constructions to base-changed over-category objects; it does not replace the original local-finite-type assumption.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentProduct.lean#L495-L502) (native source range).

<a id="api-dbe24f110d7ec2a1"></a>

### `AlgebraicGeometry.baseChangeQuasiCompactProduct`

```lean
theorem AlgebraicGeometry.baseChangeQuasiCompactProduct {k L : Type u} [Field k] [Field L] [Algebra k L] (X : CategoryTheory.Over (Spec ↧k)) [QuasiCompact X.hom] : QuasiCompact (schemeBaseChange X).hom
```

**API note (not a source docstring):** The local instance `AlgebraicGeometry.baseChangeQuasiCompactProduct` in `ComponentProduct` preserves quasi-compactness of `X.hom` under base change from a field `k` to a field `L`. It identifies the base-changed structure morphism with the pullback's second projection; the result supplies the quasi-compactness hypothesis required by product and component-scheme comparisons after extension.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentProduct.lean#L504-L511) (native source range).

<a id="api-b1960fd59ca497cd"></a>

### `AlgebraicGeometry.componentProductIso`

```lean
noncomputable def AlgebraicGeometry.componentProductIso {K : Type u} [Field K] (X Y : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] : componentScheme (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) ≅ CategoryTheory.MonoidalCategoryStruct.tensorObj (componentScheme X) (componentScheme Y)
```

The canonical component scheme of a binary fibre product is the fibre
product of the component schemes.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentProduct.lean#L589-L596) (native source range).

<a id="api-88789c40a83ab134"></a>

### `AlgebraicGeometry.componentProductIso_hom`

```lean
theorem AlgebraicGeometry.componentProductIso_hom {K : Type u} [Field K] (X Y : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] : (componentProductIso X Y).hom = componentProductComparison X Y
```

The forward map of `componentProductIso` is exactly the canonical product
comparison.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentProduct.lean#L598-L608) (native source range).


## SchemeProperties.ComponentScheme

<a id="api-364f692f24dc0705"></a>

### `AlgebraicGeometry.globalSectionsAlgebraInstance`

```lean
noncomputable def AlgebraicGeometry.globalSectionsAlgebraInstance {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) : Algebra K ↑(X.left.presheaf.obj (Opposite.op ⊤))
```

The algebra of global sections of a scheme over `K`, inferred locally
from its structure morphism.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L47-L51) (native source range).

<a id="api-37885db0d6a4a5fd"></a>

### `AlgebraicGeometry.specOver`

```lean
noncomputable abbrev AlgebraicGeometry.specOver (K A : Type u) [CommRing K] [CommRing A] [Algebra K A] : CategoryTheory.Over (Spec ↧K)
```

The affine scheme over `Spec K` associated to a `K`-algebra.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L53-L56) (native source range).

<a id="api-716bc5c9185a33b6"></a>

### `AlgebraicGeometry.toSpecOver`

```lean
noncomputable def AlgebraicGeometry.toSpecOver {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) {A : Type u} [CommRing A] [Algebra K A] (f : A →ₐ[K] ↑(X.left.presheaf.obj (Opposite.op ⊤))) : X ⟶ specOver K A
```

The map to an affine scheme over `K` corresponding to an algebra map into
global sections.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L58-L82) (native source range).

<a id="api-1e3f5ba9cdbba8ca"></a>

### `AlgebraicGeometry.specOverMap`

```lean
noncomputable def AlgebraicGeometry.specOverMap {K : Type u} [Field K] {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] (g : B →ₐ[K] A) : specOver K A ⟶ specOver K B
```

The contravariant map of affine schemes over `K` induced by an algebra
homomorphism.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L84-L97) (native source range).

<a id="api-60fa5e3287108c9e"></a>

### `AlgebraicGeometry.schemeBaseChange`

```lean
noncomputable abbrev AlgebraicGeometry.schemeBaseChange {K L : Type u} [CommRing K] [CommRing L] [Algebra K L] (X : CategoryTheory.Over (Spec ↧K)) : CategoryTheory.Over (Spec ↧L)
```

Scalar extension of a scheme over `Spec K` along `K → L`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L99-L103) (native source range).

<a id="api-9d0d0ffbedce75f3"></a>

### `AlgebraicGeometry.baseChangeSpecIso`

```lean
noncomputable def AlgebraicGeometry.baseChangeSpecIso (K A L : Type u) [CommRing K] [CommRing A] [CommRing L] [Algebra K A] [Algebra K L] : (schemeBaseChange ((Spec ↧A).asOver (Spec ↧K))).left ≅ Spec ↧(TensorProduct K A L)
```

The standard affine identification of the scalar extension of `Spec A`
with the spectrum of `A ⊗[K] L`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L105-L113) (native source range).

<a id="api-589e14984521bea2"></a>

### `AlgebraicGeometry.baseChangeSpecOverIso`

```lean
noncomputable def AlgebraicGeometry.baseChangeSpecOverIso (K A L : Type u) [CommRing K] [CommRing A] [CommRing L] [Algebra K A] [Algebra K L] : schemeBaseChange ((Spec ↧A).asOver (Spec ↧K)) ≅ CategoryTheory.Over.mk (Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom))
```

The standard affine scalar-extension identification in the over category.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L115-L124) (native source range).

<a id="api-feac77067a1a87ca"></a>

### `AlgebraicGeometry.baseChangeMap`

```lean
noncomputable abbrev AlgebraicGeometry.baseChangeMap {K L : Type u} [CommRing K] [CommRing L] [Algebra K L] {X Y : CategoryTheory.Over (Spec ↧K)} (f : X ⟶ Y) : schemeBaseChange X ⟶ schemeBaseChange Y
```

Scalar extension of a morphism over `Spec K`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L126-L131) (native source range).

<a id="api-ae2ac0cb11474be7"></a>

### `AlgebraicGeometry.surjective_toSpecOver`

```lean
theorem AlgebraicGeometry.surjective_toSpecOver {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) [CompactSpace ↥X.left] {A : Type u} [CommRing A] [Algebra K A] [Module.Finite K A] (f : A →ₐ[K] ↑(X.left.presheaf.obj (Opposite.op ⊤))) (hf : Function.Injective ⇑f) : Surjective (CategoryTheory.Over.Hom.left (toSpecOver X f))
```

If `A` is finite over a field, an injective algebra map from `A` into
global sections induces a surjective map to `Spec A`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L146-L161) (native source range).

<a id="api-fcdb9d18e5de7e65"></a>

### `AlgebraicGeometry.surjective_baseChangeMap`

```lean
theorem AlgebraicGeometry.surjective_baseChangeMap {K L : Type u} [CommRing K] [CommRing L] [Algebra K L] {X Y : CategoryTheory.Over (Spec ↧K)} (f : X ⟶ Y) (hf : Surjective (CategoryTheory.Over.Hom.left f)) : Surjective (CategoryTheory.Over.Hom.left (baseChangeMap f))
```

Surjectivity is preserved by scalar extension in the over category.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L163-L168) (native source range).

<a id="api-738b472003d3e42a"></a>

### `AlgebraicGeometry.surjective_baseChangeMap_comp_baseChangeSpecIso`

```lean
theorem AlgebraicGeometry.surjective_baseChangeMap_comp_baseChangeSpecIso {K A L : Type u} [CommRing K] [CommRing A] [CommRing L] [Algebra K A] [Algebra K L] {X : CategoryTheory.Over (Spec ↧K)} (f : X ⟶ (Spec ↧A).asOver (Spec ↧K)) (hf : Surjective (CategoryTheory.Over.Hom.left f)) : Surjective (CategoryTheory.CategoryStruct.comp (CategoryTheory.Over.Hom.left (baseChangeMap f)) (baseChangeSpecIso K A L).hom)
```

After the standard affine identification, a surjective base-changed map
still is surjective.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L170-L181) (native source range).

<a id="api-0ecd58cb033a8fe8"></a>

### `AlgebraicGeometry.surjective_scalarExtension_toSpecOver`

```lean
theorem AlgebraicGeometry.surjective_scalarExtension_toSpecOver {K : Type u} [Field K] {A L : Type u} [CommRing A] [CommRing L] [Algebra K A] [Module.Finite K A] [Algebra K L] (X : CategoryTheory.Over (Spec ↧K)) [CompactSpace ↥X.left] (f : A →ₐ[K] ↑(X.left.presheaf.obj (Opposite.op ⊤))) (hf : Function.Injective ⇑f) : Surjective (CategoryTheory.CategoryStruct.comp (CategoryTheory.Over.Hom.left (baseChangeMap (toSpecOver X f))) (baseChangeSpecIso K A L).hom)
```

A finite-algebra spectrum map remains surjective after scalar extension.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L183-L193) (native source range).

<a id="api-75cfd05a4d704f50"></a>

### `AlgebraicGeometry.finrank_le_natCard_connectedComponents_scalarExtension`

```lean
theorem AlgebraicGeometry.finrank_le_natCard_connectedComponents_scalarExtension {K : Type u} [Field K] {A L : Type u} [CommRing A] [Field L] [IsSepClosed L] [Algebra K A] [Module.Finite K A] [Algebra.Etale K A] [Algebra K L] (X : CategoryTheory.Over (Spec ↧K)) [CompactSpace ↥X.left] [TopologicalSpace.NoetherianSpace ↥(schemeBaseChange X).left] (f : A →ₐ[K] ↑(X.left.presheaf.obj (Opposite.op ⊤))) (hf : Function.Injective ⇑f) : Module.finrank K A ≤ Nat.card (ConnectedComponents ↥(schemeBaseChange X).left)
```

After extension to a separably closed field, the rank of a finite-etale
subalgebra of global sections is bounded by the number of connected components
of the base-changed scheme.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L195-L228) (native source range).

<a id="api-3d06c5983fd6151e"></a>

### `AlgebraicGeometry.exists_greatest_isFiniteEtaleSubalgebra_globalSections`

```lean
theorem AlgebraicGeometry.exists_greatest_isFiniteEtaleSubalgebra_globalSections {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] : ∃ (A : Subalgebra K ↑(X.left.presheaf.obj (Opposite.op ⊤))), A.IsFiniteEtale ∧ ∀ (B : Subalgebra K ↑(X.left.presheaf.obj (Opposite.op ⊤))), B.IsFiniteEtale → B ≤ A
```

The global sections have a greatest finite-etale `K`-subalgebra.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L244-L268) (native source range).

<a id="api-9fa80089085bbd6b"></a>

### `AlgebraicGeometry.componentSubalgebra`

```lean
noncomputable def AlgebraicGeometry.componentSubalgebra {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] : Subalgebra K ↑(X.left.presheaf.obj (Opposite.op ⊤))
```

A selected greatest finite-etale subalgebra of the global sections.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L270-L275) (native source range).

<a id="api-da907bde866d0584"></a>

### `AlgebraicGeometry.componentSubalgebra_isFiniteEtale`

```lean
theorem AlgebraicGeometry.componentSubalgebra_isFiniteEtale {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] : (componentSubalgebra X).IsFiniteEtale
```

The selected component subalgebra is finite etale.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L277-L282) (native source range).

<a id="api-31c1abb633ac10a2"></a>

### `AlgebraicGeometry.isFiniteEtaleSubalgebra_le_componentSubalgebra`

```lean
theorem AlgebraicGeometry.isFiniteEtaleSubalgebra_le_componentSubalgebra {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (A : Subalgebra K ↑(X.left.presheaf.obj (Opposite.op ⊤))) (hA : A.IsFiniteEtale) : A ≤ componentSubalgebra X
```

Every finite-etale subalgebra of global sections lies in the selected one.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L284-L290) (native source range).

<a id="api-2bb3a7e6fefcadf3"></a>

### `AlgebraicGeometry.componentSubalgebra_eq_of_isGreatest`

```lean
theorem AlgebraicGeometry.componentSubalgebra_eq_of_isGreatest {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (A : Subalgebra K ↑(X.left.presheaf.obj (Opposite.op ⊤))) (hA : A.IsFiniteEtale) (hgreatest : ∀ (B : Subalgebra K ↑(X.left.presheaf.obj (Opposite.op ⊤))), B.IsFiniteEtale → B ≤ A) : componentSubalgebra X = A
```

The selected subalgebra agrees with any other greatest finite-etale
subalgebra.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L292-L303) (native source range).

<a id="api-b3888993b52517bc"></a>

### `AlgebraicGeometry.componentScheme`

```lean
noncomputable abbrev AlgebraicGeometry.componentScheme {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] : CategoryTheory.Over (Spec ↧K)
```

The affine finite-etale component object selected from global sections.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L305-L309) (native source range).

<a id="api-c489d5959c93a82a"></a>

### `AlgebraicGeometry.toComponentScheme`

```lean
noncomputable def AlgebraicGeometry.toComponentScheme {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] : X ⟶ componentScheme X
```

The canonical map from a scheme to its finite-etale component scheme.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L311-L316) (native source range).

<a id="api-c91c5e098b62e33a"></a>

### `AlgebraicGeometry.surjective_toComponentScheme`

```lean
theorem AlgebraicGeometry.surjective_toComponentScheme {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] : Surjective (CategoryTheory.Over.Hom.left (toComponentScheme X))
```

The canonical map to the component scheme is surjective.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L318-L327) (native source range).

<a id="api-8dea64cb5b64360c"></a>

### `AlgebraicGeometry.flat_toComponentScheme`

```lean
instance AlgebraicGeometry.flat_toComponentScheme {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] : Flat (CategoryTheory.Over.Hom.left (toComponentScheme X))
```

The canonical map to the component scheme is flat.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L329-L364) (native source range).

<a id="api-1392770cb201df54"></a>

### `AlgebraicGeometry.algebraMapOfToSpec`

```lean
noncomputable def AlgebraicGeometry.algebraMapOfToSpec {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) {B : Type u} [CommRing B] [Algebra K B] (f : X ⟶ specOver K B) : B →ₐ[K] ↑(X.left.presheaf.obj (Opposite.op ⊤))
```

The algebra map on global sections induced by a map to an affine scheme
over `K`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L366-L380) (native source range).

<a id="api-66b38ec20fd52db1"></a>

### `AlgebraicGeometry.toSpecOver_algebraMapOfToSpec`

```lean
theorem AlgebraicGeometry.toSpecOver_algebraMapOfToSpec {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) {B : Type u} [CommRing B] [Algebra K B] (f : X ⟶ specOver K B) : toSpecOver X (algebraMapOfToSpec X f) = f
```

Recovering an affine-target map from its map on global sections gives the
original map.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L382-L395) (native source range).

<a id="api-ae16e2628441a44c"></a>

### `AlgebraicGeometry.toSpecOver_comp_specOverMap`

```lean
theorem AlgebraicGeometry.toSpecOver_comp_specOverMap {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] (f : A →ₐ[K] ↑(X.left.presheaf.obj (Opposite.op ⊤))) (g : B →ₐ[K] A) : CategoryTheory.CategoryStruct.comp (toSpecOver X f) (specOverMap g) = toSpecOver X (f.comp g)
```

Composition with a contravariant `Spec` map corresponds to composition of
algebra maps.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L397-L409) (native source range).

<a id="api-f9255011718c5a7f"></a>

### `AlgebraicGeometry.range_algebraMapOfToSpec_isFiniteEtale`

```lean
theorem AlgebraicGeometry.range_algebraMapOfToSpec_isFiniteEtale {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) {B : Type u} [CommRing B] [Algebra K B] (hB : Algebra.IsFiniteEtale K B) (f : X ⟶ specOver K B) : (algebraMapOfToSpec X f).range.IsFiniteEtale
```

The range of the algebra map induced by a finite-etale target is finite
etale.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L411-L419) (native source range).

<a id="api-cea8f6e540a73ba4"></a>

### `AlgebraicGeometry.range_algebraMapOfToSpec_le_componentSubalgebra`

```lean
theorem AlgebraicGeometry.range_algebraMapOfToSpec_le_componentSubalgebra {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] {B : Type u} [CommRing B] [Algebra K B] (hB : Algebra.IsFiniteEtale K B) (f : X ⟶ specOver K B) : (algebraMapOfToSpec X f).range ≤ componentSubalgebra X
```

The range of a map from a finite-etale algebra lies in the selected
component subalgebra.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L421-L429) (native source range).

<a id="api-8220f9652cf8e34e"></a>

### `AlgebraicGeometry.componentFactorAlgHom`

```lean
noncomputable def AlgebraicGeometry.componentFactorAlgHom {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] {B : Type u} [CommRing B] [Algebra K B] (hB : Algebra.IsFiniteEtale K B) (f : X ⟶ specOver K B) : B →ₐ[K] ↥(componentSubalgebra X)
```

The algebra map defining the universal factor.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L431-L440) (native source range).

<a id="api-126ecf9abda87bb5"></a>

### `AlgebraicGeometry.componentFactor`

```lean
noncomputable def AlgebraicGeometry.componentFactor {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] {B : Type u} [CommRing B] [Algebra K B] (hB : Algebra.IsFiniteEtale K B) (f : X ⟶ specOver K B) : componentScheme X ⟶ specOver K B
```

The factor from the component scheme to a finite-etale affine target.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L442-L449) (native source range).

<a id="api-b69c9440b2dc6ac2"></a>

### `AlgebraicGeometry.toComponentScheme_comp_componentFactor`

```lean
theorem AlgebraicGeometry.toComponentScheme_comp_componentFactor {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] {B : Type u} [CommRing B] [Algebra K B] (hB : Algebra.IsFiniteEtale K B) (f : X ⟶ specOver K B) : CategoryTheory.CategoryStruct.comp (toComponentScheme X) (componentFactor X hB f) = f
```

The universal factor makes the canonical triangle commute.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L451-L463) (native source range).

<a id="api-eb1f76c1239f843e"></a>

### `AlgebraicGeometry.componentScheme_universal`

```lean
theorem AlgebraicGeometry.componentScheme_universal {K : Type u} [Field K] (X : CategoryTheory.Over (Spec ↧K)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] {B : Type u} [CommRing B] [Algebra K B] (hB : Algebra.IsFiniteEtale K B) (f : X ⟶ specOver K B) : ∃! g : componentScheme X ⟶ specOver K B, CategoryTheory.CategoryStruct.comp (toComponentScheme X) g = f
```

Every map to a finite-etale affine scheme factors uniquely through the
component scheme.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ComponentScheme.lean#L472-L499) (native source range).


## SchemeProperties.ConnectedComponents

<a id="api-03c1ab8086b4d9c0"></a>

### `AlgebraicGeometry.Scheme.connectedComponentOpen`

```lean
def AlgebraicGeometry.Scheme.connectedComponentOpen (X : Scheme) [LocallyConnectedSpace ↥X] (c : ConnectedComponents ↥X) : X.Opens
```

The open subscheme underlying one connected component of a locally
connected scheme. It is defined canonically as the inverse image of the
corresponding singleton under the connected-component quotient map.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ConnectedComponents.lean#L32-L39) (native source range).

<a id="api-ba7b90fd7e968415"></a>

### `AlgebraicGeometry.Scheme.mem_connectedComponentOpen`

```lean
theorem AlgebraicGeometry.Scheme.mem_connectedComponentOpen (X : Scheme) [LocallyConnectedSpace ↥X] (c : ConnectedComponents ↥X) (x : ↥X) : x ∈ X.connectedComponentOpen c ↔ ConnectedComponents.mk x = c
```

**API note (not a source docstring):** The simplification lemma `AlgebraicGeometry.Scheme.mem_connectedComponentOpen` characterizes membership of a point `x` in the component open indexed by `c`: precisely `ConnectedComponents.mk x = c`. Its source owner `ConnectedComponents` defines that open as the inverse image of a singleton under the component quotient, requiring `LocallyConnectedSpace X` so it is open; the lemma unfolds that specific construction.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ConnectedComponents.lean#L41-L45) (native source range).

<a id="api-70180cfd6287ef74"></a>

### `AlgebraicGeometry.Scheme.connectedComponentOpen_mk`

```lean
theorem AlgebraicGeometry.Scheme.connectedComponentOpen_mk (X : Scheme) [LocallyConnectedSpace ↥X] (x : ↥X) : ↑(X.connectedComponentOpen (ConnectedComponents.mk x)) = connectedComponent x
```

The component open indexed by a point has the expected underlying set.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ConnectedComponents.lean#L47-L52) (native source range).

<a id="api-786d88f09f0bd17c"></a>

### `AlgebraicGeometry.Scheme.iSup_connectedComponentOpen`

```lean
theorem AlgebraicGeometry.Scheme.iSup_connectedComponentOpen (X : Scheme) [LocallyConnectedSpace ↥X] : ⨆ (c : ConnectedComponents ↥X), X.connectedComponentOpen c = ⊤
```

The connected-component opens cover a locally connected scheme.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ConnectedComponents.lean#L54-L58) (native source range).

<a id="api-ad6b6f136ab13b2d"></a>

### `AlgebraicGeometry.Scheme.connectedComponentOpen_disjoint`

```lean
theorem AlgebraicGeometry.Scheme.connectedComponentOpen_disjoint (X : Scheme) [LocallyConnectedSpace ↥X] {c d : ConnectedComponents ↥X} (h : c ≠ d) : Disjoint (X.connectedComponentOpen c) (X.connectedComponentOpen d)
```

Distinct connected components give disjoint open subschemes.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ConnectedComponents.lean#L60-L70) (native source range).

<a id="api-cb3f9931f8edbcab"></a>

### `AlgebraicGeometry.Scheme.connectedComponentSigmaIso`

```lean
noncomputable def AlgebraicGeometry.Scheme.connectedComponentSigmaIso (X : Scheme) [LocallyConnectedSpace ↥X] : (∐ fun (c : ConnectedComponents ↥X) => ↑(X.connectedComponentOpen c)) ≅ X
```

A locally connected scheme is canonically the coproduct of the open
subschemes carried by its connected components.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ConnectedComponents.lean#L72-L87) (native source range).

<a id="api-254104d49276973d"></a>

### `AlgebraicGeometry.Scheme.connectedComponentSigmaIso_hom_ι`

```lean
theorem AlgebraicGeometry.Scheme.connectedComponentSigmaIso_hom_ι (X : Scheme) [LocallyConnectedSpace ↥X] (c : ConnectedComponents ↥X) : CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.Sigma.ι (fun (c : ConnectedComponents ↥X) => ↑(X.connectedComponentOpen c)) c) X.connectedComponentSigmaIso.hom = (X.connectedComponentOpen c).ι
```

On each coproduct summand, the component decomposition isomorphism is the
canonical open immersion.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ConnectedComponents.lean#L89-L97) (native source range).

<a id="api-bb780ae49b3ab4f7"></a>

### `AlgebraicGeometry.Scheme.connectedComponentSigmaIso_hom_ι_assoc`

```lean
theorem AlgebraicGeometry.Scheme.connectedComponentSigmaIso_hom_ι_assoc (X : Scheme) [LocallyConnectedSpace ↥X] (c : ConnectedComponents ↥X) {Z : Scheme} (h : X ⟶ Z) : CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.Sigma.ι (fun (c : ConnectedComponents ↥X) => ↑(X.connectedComponentOpen c)) c) (CategoryTheory.CategoryStruct.comp X.connectedComponentSigmaIso.hom h) = CategoryTheory.CategoryStruct.comp (X.connectedComponentOpen c).ι h
```

On each coproduct summand, the component decomposition isomorphism is the
canonical open immersion.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ConnectedComponents.lean#L91-L91) (native source range).

<a id="api-3484c63eddb57210"></a>

### `AlgebraicGeometry.Scheme.toConnectedComponentCoproduct`

```lean
noncomputable def AlgebraicGeometry.Scheme.toConnectedComponentCoproduct {X S : Scheme} [LocallyConnectedSpace ↥X] (f : X ⟶ S) : X ⟶ ∐ fun (x : ConnectedComponents ↥X) => S
```

A morphism out of a locally connected scheme, separated into one copy of
the target for every connected component of the source.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ConnectedComponents.lean#L99-L106) (native source range).

<a id="api-69bf6e5bfee24242"></a>

### `AlgebraicGeometry.Scheme.connectedComponentOpen_ι_toConnectedComponentCoproduct`

```lean
theorem AlgebraicGeometry.Scheme.connectedComponentOpen_ι_toConnectedComponentCoproduct {X S : Scheme} [LocallyConnectedSpace ↥X] (f : X ⟶ S) (c : ConnectedComponents ↥X) : CategoryTheory.CategoryStruct.comp (X.connectedComponentOpen c).ι (toConnectedComponentCoproduct f) = CategoryTheory.CategoryStruct.comp (X.connectedComponentOpen c).ι (CategoryTheory.CategoryStruct.comp f (CategoryTheory.Limits.Sigma.ι (fun (x : ConnectedComponents ↥X) => S) c))
```

On one connected component, `toConnectedComponentCoproduct` is the
original morphism followed by the corresponding coproduct inclusion.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ConnectedComponents.lean#L108-L119) (native source range).

<a id="api-9043955b32f496da"></a>

### `AlgebraicGeometry.Scheme.connectedComponentOpen_ι_toConnectedComponentCoproduct_assoc`

```lean
theorem AlgebraicGeometry.Scheme.connectedComponentOpen_ι_toConnectedComponentCoproduct_assoc {X S : Scheme} [LocallyConnectedSpace ↥X] (f : X ⟶ S) (c : ConnectedComponents ↥X) {Z : Scheme} (h : (∐ fun (x : ConnectedComponents ↥X) => S) ⟶ Z) : CategoryTheory.CategoryStruct.comp (X.connectedComponentOpen c).ι (CategoryTheory.CategoryStruct.comp (toConnectedComponentCoproduct f) h) = CategoryTheory.CategoryStruct.comp (X.connectedComponentOpen c).ι (CategoryTheory.CategoryStruct.comp f (CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.Sigma.ι (fun (x : ConnectedComponents ↥X) => S) c) h))
```

On one connected component, `toConnectedComponentCoproduct` is the
original morphism followed by the corresponding coproduct inclusion.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ConnectedComponents.lean#L110-L110) (native source range).


## SchemeProperties.CoproductSections

<a id="api-b636b7735f8cc606"></a>

### `AlgebraicGeometry.Scheme.sigmaPresheafObjIso`

```lean
noncomputable def AlgebraicGeometry.Scheme.sigmaPresheafObjIso {ι : Type u} (X : ι → Scheme) (U : (∐ X).Opens) : (∐ X).presheaf.obj (Opposite.op U) ≅ ↧((i : ι) → ↑((X i).presheaf.obj (Opposite.op ((TopologicalSpace.Opens.map (CategoryTheory.Limits.Sigma.ι X i).base).obj U))))
```

Sections on an indexed coproduct of schemes are the dependent product of
the sections over the component preimages.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/CoproductSections.lean#L94-L148) (native source range).

<a id="api-7f8d60aabdb9dff0"></a>

### `AlgebraicGeometry.Scheme.sigmaPresheafObjIso_hom_apply`

```lean
theorem AlgebraicGeometry.Scheme.sigmaPresheafObjIso_hom_apply {ι : Type u} (X : ι → Scheme) (U : (∐ X).Opens) (s : ↑((∐ X).presheaf.obj (Opposite.op U))) (i : ι) : (CategoryTheory.ConcreteCategory.hom (sigmaPresheafObjIso X U).hom) s i = (CategoryTheory.ConcreteCategory.hom (Hom.app (CategoryTheory.Limits.Sigma.ι X i) U)) s
```

The `i`-th coordinate of `sigmaPresheafObjIso` is pullback to the `i`-th
summand.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/CoproductSections.lean#L157-L163) (native source range).

<a id="api-d5599ed546e4a54b"></a>

### `AlgebraicGeometry.Scheme.sigmaPresheafObjIso_hom_res_apply`

```lean
theorem AlgebraicGeometry.Scheme.sigmaPresheafObjIso_hom_res_apply {ι : Type u} (X : ι → Scheme) {V U : (∐ X).Opens} (hVU : V ≤ U) (s : ↑((∐ X).presheaf.obj (Opposite.op U))) (i : ι) : (CategoryTheory.ConcreteCategory.hom (sigmaPresheafObjIso X V).hom) ((CategoryTheory.ConcreteCategory.hom ((∐ X).presheaf.map (CategoryTheory.homOfLE hVU).op)) s) i = (CategoryTheory.ConcreteCategory.hom ((X i).presheaf.map (CategoryTheory.homOfLE ⋯).op)) ((CategoryTheory.ConcreteCategory.hom (sigmaPresheafObjIso X U).hom) s i)
```

Restriction of a coproduct section is coordinatewise restriction on every
summand.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/CoproductSections.lean#L165-L176) (native source range).


## SchemeProperties.CoproductTopology

<a id="api-aaa74f7b16074df1"></a>

### `AlgebraicGeometry.quasiSeparatedSpace_sigma`

```lean
instance AlgebraicGeometry.quasiSeparatedSpace_sigma {ι : Type u} (X : ι → Scheme) [∀ (i : ι), QuasiSeparatedSpace ↥(X i)] : QuasiSeparatedSpace ↥(∐ X)
```

An indexed coproduct of quasiseparated schemes is quasiseparated.

The empty family and families with empty components are included.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/CoproductTopology.lean#L35-L59) (native source range).

<a id="api-f1c8d4895097e02b"></a>

### `AlgebraicGeometry.not_compactSpace_sigma`

```lean
theorem AlgebraicGeometry.not_compactSpace_sigma {ι : Type u} (X : ι → Scheme) [Infinite ι] [∀ (i : ι), Nonempty ↥(X i)] : ¬CompactSpace ↥(∐ X)
```

An infinite indexed coproduct of nonempty schemes is not compact.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/CoproductTopology.lean#L61-L73) (native source range).


## SchemeProperties.Factorial

<a id="api-a381fab20f5e6fa4"></a>

### `IsLocalization.AtPrime.uniqueFactorizationMonoid_of_le`

```lean
theorem IsLocalization.AtPrime.uniqueFactorizationMonoid_of_le {R : Type u} (S : Type v) (T : Type w) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] {p q : Ideal R} [p.IsPrime] [q.IsPrime] [IsLocalization.AtPrime S q] [IsLocalization.AtPrime T p] (hpq : p ≤ q) [UniqueFactorizationMonoid S] : UniqueFactorizationMonoid T
```

Let `S` and `T` be localizations of `R` at prime ideals `q` and `p`
respectively. If `p ≤ q` and `S` has unique factorization, then so does `T`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Factorial.lean#L26-L48) (native source range).

<a id="api-133c35fe5d29eda1"></a>

### `AlgebraicGeometry.IsFactorial`

```lean
class AlgebraicGeometry.IsFactorial (X : Scheme) : Prop
```

A scheme is factorial if every local ring has unique factorization.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Factorial.lean#L56-L59) (native source range).

<a id="api-9c1cc89ae84f4b5a"></a>

### `AlgebraicGeometry.IsFactorial.mk`

```lean
constructor AlgebraicGeometry.IsFactorial.mk : ∀ {X : AlgebraicGeometry.Scheme}, autoParam (∀ (x : ↥X), UniqueFactorizationMonoid ↑(X.presheaf.stalk x)) AlgebraicGeometry.IsFactorial.stalk_uniqueFactorizationMonoid._autoParam → AlgebraicGeometry.IsFactorial X
```

**API note (not a source docstring):** The class constructor `AlgebraicGeometry.IsFactorial.mk` in `Factorial` packages a proof assigning `UniqueFactorizationMonoid (X.presheaf.stalk x)` to each point `x` into `IsFactorial X`. Its sole supplied field is this stalkwise property; the constructor does not need a separate connectedness, global UFD, or quasi-compactness hypothesis.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Factorial.lean#L56-L59) (native source range).

<a id="api-c2a69d1589e20cb7"></a>

### `AlgebraicGeometry.IsFactorial.stalk_uniqueFactorizationMonoid`

```lean
theorem AlgebraicGeometry.IsFactorial.stalk_uniqueFactorizationMonoid {X : Scheme} [self : IsFactorial X] (x : ↥X) : UniqueFactorizationMonoid ↑(X.presheaf.stalk x)
```

**API note (not a source docstring):** The field `AlgebraicGeometry.IsFactorial.stalk_uniqueFactorizationMonoid` extracts a `UniqueFactorizationMonoid` structure on the local ring `X.presheaf.stalk x` for every point of an `IsFactorial X` scheme. Declared in `Factorial` and registered as a typeclass instance, it is stalkwise and gives no direct unique-factorization instance for `Γ(X, ⊤)`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Factorial.lean#L58-L58) (native source range).

<a id="api-34b3682486f23959"></a>

### `AlgebraicGeometry.IsFactorial.stalk_isDomain`

```lean
instance AlgebraicGeometry.IsFactorial.stalk_isDomain (X : Scheme) [IsFactorial X] (x : ↥X) : IsDomain ↑(X.presheaf.stalk x)
```

Every stalk of a factorial scheme is a domain.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Factorial.lean#L63-L66) (native source range).

<a id="api-cfa4fed30d24eb7d"></a>

### `AlgebraicGeometry.isFactorial_of_stalk`

```lean
theorem AlgebraicGeometry.isFactorial_of_stalk (X : Scheme) [∀ (x : ↥X), UniqueFactorizationMonoid ↑(X.presheaf.stalk x)] : IsFactorial X
```

Factoriality can be proved directly on all stalks.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Factorial.lean#L68-L72) (native source range).

<a id="api-fef952bf8949823f"></a>

### `AlgebraicGeometry.instIsFactorialOfIsEmptyCarrierCarrierCommRingCat`

```lean
instance AlgebraicGeometry.instIsFactorialOfIsEmptyCarrierCarrierCommRingCat (X : Scheme) [IsEmpty ↥X] : IsFactorial X
```

Empty schemes are factorial.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Factorial.lean#L74-L76) (native source range).

<a id="api-675337d22eceeba1"></a>

### `AlgebraicGeometry.isFactorial_of_isOpenImmersion`

```lean
theorem AlgebraicGeometry.isFactorial_of_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] [IsFactorial Y] : IsFactorial X
```

Factoriality is preserved by open immersions.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Factorial.lean#L78-L84) (native source range).

<a id="api-9fb7b7eb99c214b5"></a>

### `AlgebraicGeometry.instIsFactorialToScheme`

```lean
instance AlgebraicGeometry.instIsFactorialToScheme {X : Scheme} {U : X.Opens} [IsFactorial X] : IsFactorial ↑U
```

**API note (not a source docstring):** The generated open-subscheme instance `AlgebraicGeometry.instIsFactorialToScheme` in `Factorial` inherits factoriality from `X` to a specified open `U : X.Opens`. The proof applies `isFactorial_of_isOpenImmersion` to `U.ι`, since its stalks agree with stalks in `X`; this does not assert factoriality of arbitrary closed subschemes.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Factorial.lean#L86-L87) (native source range).

<a id="api-574f0ab575ce5465"></a>

### `AlgebraicGeometry.instIsFactorialXScheme`

```lean
instance AlgebraicGeometry.instIsFactorialXScheme (X : Scheme) {𝒰 : X.OpenCover} [IsFactorial X] (i : 𝒰.I₀) : IsFactorial (𝒰.X i)
```

**API note (not a source docstring):** The generated open-cover instance `AlgebraicGeometry.instIsFactorialXScheme` in `Factorial` gives `IsFactorial (𝒰.X i)` for an indexed member of `X.OpenCover 𝒰` when `X` is factorial. It specializes preservation under the cover map's open immersion; factoriality is asserted of that particular open subscheme, not of every source over `X`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Factorial.lean#L89-L91) (native source range).

<a id="api-19a0405b966671ea"></a>

### `AlgebraicGeometry.instIsClosedUnderIsomorphismsSchemeIsFactorial`

```lean
instance AlgebraicGeometry.instIsClosedUnderIsomorphismsSchemeIsFactorial : CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms fun (x : Scheme) => IsFactorial x
```

**API note (not a source docstring):** The `ObjectProperty.IsClosedUnderIsomorphisms` instance `AlgebraicGeometry.instIsClosedUnderIsomorphismsSchemeIsFactorial` says factoriality of schemes is invariant under isomorphism. Its source owner `Factorial` establishes the property via the inverse isomorphism as an open immersion and the induced stalk isomorphisms; this concerns factorial scheme stalks, not UFDs of arbitrary global-section rings.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Factorial.lean#L93-L95) (native source range).

<a id="api-892b01bcb243ecb5"></a>

### `AlgebraicGeometry.IsFactorial.of_openCover`

```lean
theorem AlgebraicGeometry.IsFactorial.of_openCover (X : Scheme) (𝒰 : X.OpenCover) [∀ (i : 𝒰.I₀), IsFactorial (𝒰.X i)] : IsFactorial X
```

Factoriality is local on an open cover.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Factorial.lean#L97-L104) (native source range).

<a id="api-ea1510f939fdc6a1"></a>

### `AlgebraicGeometry.IsFactorial.iff_of_openCover`

```lean
theorem AlgebraicGeometry.IsFactorial.iff_of_openCover (X : Scheme) (𝒰 : X.OpenCover) : IsFactorial X ↔ ∀ (i : 𝒰.I₀), IsFactorial (𝒰.X i)
```

**API note (not a source docstring):** For an open cover `𝒰` of a scheme `X`, `AlgebraicGeometry.IsFactorial.iff_of_openCover` identifies factoriality of `X` with factoriality of every cover member `𝒰.X i`. The forward direction restricts to open subschemes; the converse transfers stalkwise unique factorization across the cover's open immersions. No finite or nonempty cover condition is added.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Factorial.lean#L106-L108) (native source range).

<a id="api-c825b324a4dfa7e1"></a>

### `AlgebraicGeometry.factorialSpec`

```lean
instance AlgebraicGeometry.factorialSpec {R : CommRingCat} [UniqueFactorizationMonoid ↑R] : IsFactorial (Spec R)
```

**API note (not a source docstring):** The instance `AlgebraicGeometry.factorialSpec` makes `Spec R` factorial when the commutative ring `R` has `UniqueFactorizationMonoid`. Factoriality here means unique factorization in every scheme stalk; the proof localizes `R` at each prime and transfers the property across the canonical stalk isomorphism. It does not conclude that an arbitrary coordinate ring is a UFD from factoriality of its spectrum.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Factorial.lean#L111-L118) (native source range).

<a id="api-ab8ccb320d1c667a"></a>

### `AlgebraicGeometry.factorialSpec_of_isDedekindDomain`

```lean
theorem AlgebraicGeometry.factorialSpec_of_isDedekindDomain {R : CommRingCat} [IsDedekindDomain ↑R] : IsFactorial (Spec R)
```

The spectrum of a Dedekind domain is factorial, even when the domain itself
does not have unique factorization.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Factorial.lean#L121-L132) (native source range).

<a id="api-69c4e8c762e27d1b"></a>

### `AlgebraicGeometry.uniqueFactorizationMonoid_stalk_of_specializes`

```lean
theorem AlgebraicGeometry.uniqueFactorizationMonoid_stalk_of_specializes (X : Scheme) {x y : ↥X} (hxy : x ⤳ y) [UniqueFactorizationMonoid ↑(X.presheaf.stalk y)] : UniqueFactorizationMonoid ↑(X.presheaf.stalk x)
```

Unique factorization of stalks is preserved under generalization.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Factorial.lean#L136-L163) (native source range).


## SchemeProperties.FactorialNormal

<a id="api-de36e929f195f241"></a>

### `AlgebraicGeometry.isNormal_of_isFactorial`

```lean
instance AlgebraicGeometry.isNormal_of_isFactorial (X : Scheme) [IsFactorial X] : IsNormal X
```

Every factorial scheme is normal.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FactorialNormal.lean#L27-L29) (native source range).


## SchemeProperties.FiniteTypePoints

<a id="api-f47eee2a6edd25e3"></a>

### `CategoryTheory.Functor.isDense_of_isCoverDense_of_subcanonical`

```lean
theorem CategoryTheory.Functor.isDense_of_isCoverDense_of_subcanonical {C : Type u₁} {D : Type u₂} [Category.{v₁, u₁} C] [Category.{v₂, u₂} D] (G : Functor C D) (J : GrothendieckTopology D) [G.Full] [G.IsCoverDense J] [G.IsLocallyFull J] [J.Subcanonical] : G.IsDense
```

A fully faithful, locally full, cover-dense functor into a subcanonical site is dense.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L49-L67) (native source range).

<a id="api-d45bfa3bb58c464c"></a>

### `AlgebraicGeometry.locallyFiniteTypeMorphism`

```lean
abbrev AlgebraicGeometry.locallyFiniteTypeMorphism : CategoryTheory.MorphismProperty Scheme
```

The morphism property of being locally of finite type, with its universe made explicit.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L75-L77) (native source range).

<a id="api-53fd047ed93612bd"></a>

### `AlgebraicGeometry.openImmersionMorphism`

```lean
abbrev AlgebraicGeometry.openImmersionMorphism : CategoryTheory.MorphismProperty Scheme
```

The morphism property of being an open immersion, with its universe made explicit.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L79-L81) (native source range).

<a id="api-551b3aa2d51965ac"></a>

### `AlgebraicGeometry.openImmersionMorphism_le_locallyFiniteTypeMorphism`

```lean
theorem AlgebraicGeometry.openImmersionMorphism_le_locallyFiniteTypeMorphism : openImmersionMorphism ≤ locallyFiniteTypeMorphism
```

An open immersion is locally of finite type.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L83-L88) (native source range).

<a id="api-8970580df93ece8b"></a>

### `AlgebraicGeometry.instHasOfPostcompPropertySchemeLocallyFiniteTypeMorphism`

```lean
instance AlgebraicGeometry.instHasOfPostcompPropertySchemeLocallyFiniteTypeMorphism : locallyFiniteTypeMorphism.HasOfPostcompProperty locallyFiniteTypeMorphism
```

Local finite type can be cancelled from a composite on the right.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L90-L94) (native source range).

<a id="api-807a0ec593c597e4"></a>

### `AlgebraicGeometry.lftAffineOver`

```lean
abbrev AlgebraicGeometry.lftAffineOver (K : Type u) [Field K] : Type (u + 1)
```

Affine schemes locally of finite type over a field.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L96-L98) (native source range).

<a id="api-d75e93262a6d4aa9"></a>

### `AlgebraicGeometry.lftZariskiTopology`

```lean
noncomputable abbrev AlgebraicGeometry.lftZariskiTopology (K : Type u) [Field K] : CategoryTheory.GrothendieckTopology (locallyFiniteTypeMorphism.Over ⊤ (Spec ↧K))
```

The small Zariski topology on schemes locally of finite type over a field.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L100-L104) (native source range).

<a id="api-061eff8f761d8246"></a>

### `AlgebraicGeometry.finiteAlgSpec`

```lean
noncomputable def AlgebraicGeometry.finiteAlgSpec (K : Type u) [Field K] : CategoryTheory.Functor (FGAlgCat K)ᵒᵖ (CategoryTheory.Over (Spec ↧K))
```

The affine spectrum over a field, restricted to finitely generated algebras.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L106-L109) (native source range).

<a id="api-a20c2d0174351e5b"></a>

### `AlgebraicGeometry.finiteAlgSpecFullyFaithful`

```lean
noncomputable def AlgebraicGeometry.finiteAlgSpecFullyFaithful (K : Type u) [Field K] : (finiteAlgSpec K).FullyFaithful
```

The affine spectrum functor on finitely generated algebras is fully faithful.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L111-L114) (native source range).

<a id="api-742c56933397845d"></a>

### `AlgebraicGeometry.finiteAlgSpecOver`

```lean
noncomputable def AlgebraicGeometry.finiteAlgSpecOver (K : Type u) [Field K] : CategoryTheory.Functor (FGAlgCat K)ᵒᵖ (locallyFiniteTypeMorphism.Over ⊤ (Spec ↧K))
```

The spectrum of a finitely generated algebra as a locally-finite-type scheme over its field.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L116-L125) (native source range).

<a id="api-5c7a0bd37ad9a106"></a>

### `AlgebraicGeometry.finiteAlgSpecOverFullyFaithful`

```lean
noncomputable def AlgebraicGeometry.finiteAlgSpecOverFullyFaithful (K : Type u) [Field K] : (finiteAlgSpecOver K).FullyFaithful
```

The locally-finite-type refinement of finite-algebra spectrum is fully faithful.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L127-L135) (native source range).

<a id="api-2a17db77f84c5f01"></a>

### `AlgebraicGeometry.lftAffineInclusion`

```lean
noncomputable def AlgebraicGeometry.lftAffineInclusion (K : Type u) [Field K] : CategoryTheory.Functor (lftAffineOver K) (locallyFiniteTypeMorphism.Over ⊤ (Spec ↧K))
```

The inclusion of affine locally-finite-type schemes into all locally-finite-type schemes over a
field.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L137-L143) (native source range).

<a id="api-e253606390b55d55"></a>

### `AlgebraicGeometry.lftAffineInclusionFullyFaithful`

```lean
noncomputable def AlgebraicGeometry.lftAffineInclusionFullyFaithful (K : Type u) [Field K] : (lftAffineInclusion K).FullyFaithful
```

The inclusion of affine locally-finite-type schemes is fully faithful.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L145-L160) (native source range).

<a id="api-6b740bf6119d220e"></a>

### `AlgebraicGeometry.instFullLftAffineOverOverSchemeLocallyFiniteTypeMorphismTopMorphismPropertySpecOfLftAffineInclusion`

```lean
theorem AlgebraicGeometry.instFullLftAffineOverOverSchemeLocallyFiniteTypeMorphismTopMorphismPropertySpecOfLftAffineInclusion (K : Type u) [Field K] : (lftAffineInclusion K).Full
```

**API note (not a source docstring):** The generated `Full` instance for `lftAffineInclusion K` in `FiniteTypePoints` says morphisms in the locally-finite-type over-category between affine objects lift through the affine inclusion. It uses the full half of `lftAffineInclusionFullyFaithful K`, itself based on full faithfulness of the affine spectrum; this remains a statement over the field `K` and on the indicated subcategory. Its elaborated name is `AlgebraicGeometry.instFullLftAffineOverOverSchemeLocallyFiniteTypeMorphismTopMorphismPropertySpecOfLftAffineInclusion`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L162-L163) (native source range).

<a id="api-e2a2f450441d774c"></a>

### `AlgebraicGeometry.instFaithfulLftAffineOverOverSchemeLocallyFiniteTypeMorphismTopMorphismPropertySpecOfLftAffineInclusion`

```lean
theorem AlgebraicGeometry.instFaithfulLftAffineOverOverSchemeLocallyFiniteTypeMorphismTopMorphismPropertySpecOfLftAffineInclusion (K : Type u) [Field K] : (lftAffineInclusion K).Faithful
```

**API note (not a source docstring):** The generated `Faithful` instance for `lftAffineInclusion K` in `FiniteTypePoints` says its map on morphisms between affine locally-finite-type schemes over `Spec K` is injective. It extracts the faithful half of the specifically constructed `lftAffineInclusionFullyFaithful K`; the inclusion is not asserted faithful for an unspecified category or base ring. Its elaborated name is `AlgebraicGeometry.instFaithfulLftAffineOverOverSchemeLocallyFiniteTypeMorphismTopMorphismPropertySpecOfLftAffineInclusion`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L165-L166) (native source range).

<a id="api-40311727d4eb068d"></a>

### `AlgebraicGeometry.lftAffineInclusion_isCoverDense`

```lean
instance AlgebraicGeometry.lftAffineInclusion_isCoverDense (K : Type u) [Field K] : (lftAffineInclusion K).IsCoverDense (lftZariskiTopology K)
```

Affine locally-finite-type schemes are cover-dense for the small Zariski topology.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L168-L190) (native source range).

<a id="api-a0c8444de0ecb6a4"></a>

### `AlgebraicGeometry.lftOver_locallyCoverDense`

```lean
theorem AlgebraicGeometry.lftOver_locallyCoverDense (K : Type u) [Field K] : (CategoryTheory.MorphismProperty.Over.forget locallyFiniteTypeMorphism ⊤ (Spec ↧K)).LocallyCoverDense (Scheme.overGrothendieckTopology openImmersionMorphism (Spec ↧K))
```

**API note (not a source docstring):** The local instance `AlgebraicGeometry.lftOver_locallyCoverDense` in `FiniteTypePoints` makes the functor forgetting locally finite type over `Spec K` locally cover-dense for the ambient open-immersion Zariski topology. Its construction uses that open immersions are locally of finite type; it does not assert that every scheme over a field is globally locally of finite type.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L192-L197) (native source range).

<a id="api-40acafd9c31820a0"></a>

### `AlgebraicGeometry.lftOver_representablyFlat`

```lean
theorem AlgebraicGeometry.lftOver_representablyFlat (K : Type u) [Field K] : CategoryTheory.RepresentablyFlat (CategoryTheory.MorphismProperty.Over.forget locallyFiniteTypeMorphism ⊤ (Spec ↧K))
```

**API note (not a source docstring):** The local instance `AlgebraicGeometry.lftOver_representablyFlat` in `FiniteTypePoints` supplies `RepresentablyFlat` for the functor forgetting the locally-finite-type morphism property over `Spec K`. The proof derives it from preservation of finite limits for that functor; the claim is about a functor of over-categories, not flatness of every individual locally-finite-type scheme morphism.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L199-L203) (native source range).

<a id="api-28ca2542a072de03"></a>

### `AlgebraicGeometry.lftOver_isContinuous`

```lean
theorem AlgebraicGeometry.lftOver_isContinuous (K : Type u) [Field K] : (CategoryTheory.MorphismProperty.Over.forget locallyFiniteTypeMorphism ⊤ (Spec ↧K)).IsContinuous (lftZariskiTopology K) (Scheme.overGrothendieckTopology openImmersionMorphism (Spec ↧K))
```

**API note (not a source docstring):** The local instance `AlgebraicGeometry.lftOver_isContinuous` in `FiniteTypePoints` makes the forgetful functor from locally-finite-type schemes over `Spec K` to all schemes over `Spec K` continuous for the restricted small Zariski topology and the ambient over-Zariski topology. It uses preservation of covering families by that particular restricted-topology construction; continuity here is categorical, not continuity of a point-set map.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L205-L213) (native source range).

<a id="api-577928c3d2c3b523"></a>

### `AlgebraicGeometry.lftZariskiTopology_subcanonical`

```lean
theorem AlgebraicGeometry.lftZariskiTopology_subcanonical (K : Type u) [Field K] : (lftZariskiTopology K).Subcanonical
```

**API note (not a source docstring):** The local instance `AlgebraicGeometry.lftZariskiTopology_subcanonical` in `FiniteTypePoints` states that the small Zariski topology restricted to schemes locally of finite type over the field `K` is subcanonical. Representable presheaves on that restricted over-category are sheaves; the proof uses the full and faithful forgetful functor and subcanonicity of the ambient open-immersion topology, not a statement about arbitrary Grothendieck topologies.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L215-L222) (native source range).

<a id="api-378e9a328a198d23"></a>

### `AlgebraicGeometry.lftAffineInclusion_isDense`

```lean
theorem AlgebraicGeometry.lftAffineInclusion_isDense (K : Type u) [Field K] : (lftAffineInclusion K).IsDense
```

Affine locally-finite-type schemes are categorically dense among locally-finite-type schemes
over a field.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L224-L229) (native source range).

<a id="api-1b75687af93d1a4e"></a>

### `AlgebraicGeometry.finiteAlgSpecOver_mem_lftAffineInclusion`

```lean
theorem AlgebraicGeometry.finiteAlgSpecOver_mem_lftAffineInclusion (K : Type u) [Field K] (A : (FGAlgCat K)ᵒᵖ) : (lftAffineInclusion K).essImage ((finiteAlgSpecOver K).obj A)
```

Each finite-algebra spectrum belongs to the essential image of the affine inclusion.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L231-L237) (native source range).

<a id="api-42eefd1da0b6da06"></a>

### `AlgebraicGeometry.fgAlgToLftAffine`

```lean
noncomputable def AlgebraicGeometry.fgAlgToLftAffine (K : Type u) [Field K] : CategoryTheory.Functor (FGAlgCat K)ᵒᵖ (lftAffineOver K)
```

The factorization of finite-algebra spectrum through affine locally-finite-type schemes.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L239-L243) (native source range).

<a id="api-8c8ff33271a2026f"></a>

### `AlgebraicGeometry.fgAlgToLftAffineCompIso`

```lean
noncomputable def AlgebraicGeometry.fgAlgToLftAffineCompIso (K : Type u) [Field K] : (fgAlgToLftAffine K).comp (lftAffineInclusion K) ≅ finiteAlgSpecOver K
```

Factoring through affine locally-finite-type schemes recovers finite-algebra spectrum.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L245-L250) (native source range).

<a id="api-30bddb98e47f33ad"></a>

### `AlgebraicGeometry.fgAlgToLftAffineFullyFaithful`

```lean
noncomputable def AlgebraicGeometry.fgAlgToLftAffineFullyFaithful (K : Type u) [Field K] : (fgAlgToLftAffine K).FullyFaithful
```

The factorization of finite-algebra spectrum is fully faithful.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L252-L259) (native source range).

<a id="api-7412205b5be8e41b"></a>

### `AlgebraicGeometry.finiteAlgSpecOver_covers_affine`

```lean
theorem AlgebraicGeometry.finiteAlgSpecOver_covers_affine (K : Type u) [Field K] (U : lftAffineOver K) : (finiteAlgSpecOver K).essImage ((CategoryTheory.MorphismProperty.CostructuredArrow.toOver locallyFiniteTypeMorphism Scheme.Spec (Spec ↧K)).obj U)
```

Every affine locally-finite-type scheme over a field is the spectrum of a finitely generated
algebra.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L261-L285) (native source range).

<a id="api-5828e9fa3cf45cf9"></a>

### `AlgebraicGeometry.fgAlgToLftAffineEssSurj`

```lean
theorem AlgebraicGeometry.fgAlgToLftAffineEssSurj (K : Type u) [Field K] : (fgAlgToLftAffine K).EssSurj
```

The factorization of finite-algebra spectrum is essentially surjective.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L287-L293) (native source range).

<a id="api-6f0b11d6d4deedf7"></a>

### `AlgebraicGeometry.fgAlgCatOpEquivLftAffineOver`

```lean
noncomputable def AlgebraicGeometry.fgAlgCatOpEquivLftAffineOver (K : Type u) [Field K] : (FGAlgCat K)ᵒᵖ ≌ lftAffineOver K
```

Finitely generated algebras over a field, oppositely, are equivalent to affine
locally-finite-type schemes over that field.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L295-L305) (native source range).

<a id="api-91e3a14dc1ffc21e"></a>

### `AlgebraicGeometry.finiteAlgSpecOver_isDense`

```lean
theorem AlgebraicGeometry.finiteAlgSpecOver_isDense (K : Type u) [Field K] : (finiteAlgSpecOver K).IsDense
```

Spectra of finitely generated algebras are dense among locally-finite-type schemes over a
field.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L307-L319) (native source range).

<a id="api-b8b7b0eb8f8cc6bc"></a>

### `AlgebraicGeometry.algebraicOver`

```lean
abbrev AlgebraicGeometry.algebraicOver (K : Type u) [Field K] : Type (u + 1)
```

Finite-type schemes over a field, expressed as locally-finite-type schemes with quasi-compact
structure morphism.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L321-L325) (native source range).

<a id="api-e75b880b501a2442"></a>

### `AlgebraicGeometry.algebraicOverInclusion`

```lean
noncomputable def AlgebraicGeometry.algebraicOverInclusion (K : Type u) [Field K] : CategoryTheory.Functor (algebraicOver K) (locallyFiniteTypeMorphism.Over ⊤ (Spec ↧K))
```

The inclusion of finite-type schemes into locally-finite-type schemes over a field.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L327-L331) (native source range).

<a id="api-362658bf3008870d"></a>

### `AlgebraicGeometry.algebraicOverPoints`

```lean
noncomputable def AlgebraicGeometry.algebraicOverPoints (K : Type u) [Field K] : CategoryTheory.Functor (algebraicOver K) (CategoryTheory.Functor (FGAlgCat K)ᵒᵖᵒᵖ (Type u))
```

The set-valued functor of points of a finite-type scheme on finitely generated algebras.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L333-L337) (native source range).

<a id="api-99ec5f4f6c85312f"></a>

### `AlgebraicGeometry.algebraicOverPointsFullyFaithful`

```lean
noncomputable def AlgebraicGeometry.algebraicOverPointsFullyFaithful (K : Type u) [Field K] : (algebraicOverPoints K).FullyFaithful
```

The functor of points on finitely generated algebras is fully faithful on finite-type schemes.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L339-L345) (native source range).

<a id="api-7e28eecdb91abcb8"></a>

### `AlgebraicGeometry.lftPointsFullyFaithful`

```lean
noncomputable def AlgebraicGeometry.lftPointsFullyFaithful (K : Type u) [Field K] : (CategoryTheory.Presheaf.restrictedULiftYoneda (finiteAlgSpecOver K)).FullyFaithful
```

The functor of points on finitely generated algebras is fully faithful on locally-finite-type
schemes.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L347-L353) (native source range).

<a id="api-635fcb987f86026a"></a>

### `AlgebraicGeometry.lftPointsPreservesFiniteLimits`

```lean
theorem AlgebraicGeometry.lftPointsPreservesFiniteLimits (K : Type u) [Field K] : CategoryTheory.Limits.PreservesFiniteLimits (CategoryTheory.Presheaf.restrictedULiftYoneda (finiteAlgSpecOver K))
```

The functor of points on finitely generated algebras preserves finite limits.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/FiniteTypePoints.lean#L355-L365) (native source range).


## SchemeProperties.GeometricConnectedness

<a id="api-68fa0bb4215e3f9a"></a>

### `connectedSpace_of_isOpenMap_of_closedPoint_fibers`

```lean
theorem connectedSpace_of_isOpenMap_of_closedPoint_fibers {X : Type u_1} {Y : Type u_2} [TopologicalSpace X] [TopologicalSpace Y] [ConnectedSpace Y] [JacobsonSpace Y] (f : X → Y) (hopen : IsOpenMap f) (hsurj : Function.Surjective f) (hfib : ∀ (y : Y), IsClosed {y} → IsConnected (f ⁻¹' {y})) : ConnectedSpace X
```

An open surjection onto a connected Jacobson space is connected when its
closed-point fibers are connected.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GeometricConnectedness.lean#L35-L75) (native source range).

<a id="api-71e8fff56cb6cfe0"></a>

### `AlgebraicGeometry.connectedSpace_pullback_of_isAlgClosed`

```lean
theorem AlgebraicGeometry.connectedSpace_pullback_of_isAlgClosed {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme} (f : X ⟶ Spec ↧K) (g : Y ⟶ Spec ↧K) [LocallyOfFiniteType f] [ConnectedSpace ↥X] [ConnectedSpace ↥Y] : ConnectedSpace ↥(CategoryTheory.Limits.pullback f g)
```

The fiber product of a connected scheme locally of finite type over an algebraically
closed field with any connected scheme over that field is connected.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GeometricConnectedness.lean#L129-L140) (native source range).

<a id="api-a2735c43e8ebffdc"></a>

### `Algebra.TensorProduct.baseChangeTensorProductEquiv`

```lean
noncomputable def Algebra.TensorProduct.baseChangeTensorProductEquiv (k K A B : Type u) [Field k] [Field K] [Algebra k K] [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] : TensorProduct K (TensorProduct k K A) (TensorProduct k K B) ≃ₐ[K] TensorProduct k K (TensorProduct k A B)
```

Base change commutes with tensor products.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GeometricConnectedness.lean#L148-L155) (native source range).

<a id="api-1629b7c5f7a34a17"></a>

### `PrimeSpectrum.eq_zero_or_eq_one_of_isIdempotentElem`

```lean
theorem PrimeSpectrum.eq_zero_or_eq_one_of_isIdempotentElem {R : Type u} [CommRing R] [ConnectedSpace (PrimeSpectrum R)] {e : R} (he : IsIdempotentElem e) : e = 0 ∨ e = 1
```

Idempotents are trivial when the prime spectrum is connected.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GeometricConnectedness.lean#L171-L187) (native source range).

<a id="api-2cf891f03b2b49c0"></a>

### `PrimeSpectrum.connectedSpace_tensorProduct_left_iff_of_isPurelyInseparable`

```lean
theorem PrimeSpectrum.connectedSpace_tensorProduct_left_iff_of_isPurelyInseparable (k : Type u) [Field k] (K R : Type u) [Field K] [Algebra k K] [IsPurelyInseparable k K] [CommRing R] [Algebra k R] : ConnectedSpace (PrimeSpectrum (TensorProduct k K R)) ↔ ConnectedSpace (PrimeSpectrum R)
```

Purely inseparable scalar extension does not change connectedness of an affine spectrum.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GeometricConnectedness.lean#L189-L197) (native source range).

<a id="api-4cb766a6ec4e77f5"></a>

### `PrimeSpectrum.connectedSpace_tensorProduct_of_isAlgClosed`

```lean
theorem PrimeSpectrum.connectedSpace_tensorProduct_of_isAlgClosed (k A B : Type u) [Field k] [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [IsAlgClosed k] [Algebra.FiniteType k A] [Algebra.FiniteType k B] [ConnectedSpace (PrimeSpectrum A)] [ConnectedSpace (PrimeSpectrum B)] : ConnectedSpace (PrimeSpectrum (TensorProduct k A B))
```

Tensor products of connected finite-type algebras over an algebraically closed field have
connected spectrum.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GeometricConnectedness.lean#L199-L217) (native source range).

<a id="api-d9e086ff8878a8bb"></a>

### `PrimeSpectrum.connectedSpace_tensorProduct_of_isSepClosed_of_finiteType`

```lean
theorem PrimeSpectrum.connectedSpace_tensorProduct_of_isSepClosed_of_finiteType (k A B : Type u) [Field k] [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [IsSepClosed k] [IsDomain A] [IsDomain B] [Algebra.FiniteType k A] [Algebra.FiniteType k B] : ConnectedSpace (PrimeSpectrum (TensorProduct k A B))
```

Tensor products of finite-type domains over a separably closed field have connected
spectrum. The scalar extensions may be nonreduced when the base field is imperfect.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GeometricConnectedness.lean#L219-L242) (native source range).

<a id="api-ea093f42942d2041"></a>

### `PrimeSpectrum.eq_zero_or_eq_one_of_isIdempotentElem_tensorProduct_fields`

```lean
theorem PrimeSpectrum.eq_zero_or_eq_one_of_isIdempotentElem_tensorProduct_fields (k : Type u) [Field k] [IsSepClosed k] (K L : Type u) [Field K] [Field L] [Algebra k K] [Algebra k L] {x : TensorProduct k K L} (hx : IsIdempotentElem x) : x = 0 ∨ x = 1
```

Every idempotent in the tensor product of two extension fields of a separably closed field is
trivial. The extension fields may be arbitrary, including transcendental extensions.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GeometricConnectedness.lean#L244-L284) (native source range).

<a id="api-9d25b170584e4c80"></a>

### `PrimeSpectrum.connectedSpace_tensorProduct_fields`

```lean
theorem PrimeSpectrum.connectedSpace_tensorProduct_fields (k : Type u) [Field k] [IsSepClosed k] (K L : Type u) [Field K] [Field L] [Algebra k K] [Algebra k L] : ConnectedSpace (PrimeSpectrum (TensorProduct k K L))
```

The tensor product of any two extension fields of a separably closed field has connected
prime spectrum. No algebraicity or finite-generation hypothesis is required.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GeometricConnectedness.lean#L286-L314) (native source range).

<a id="api-cd04a7edb852c3ff"></a>

### `AlgebraicGeometry.geometricallyConnected_SpecMap_of_isSepClosed`

```lean
theorem AlgebraicGeometry.geometricallyConnected_SpecMap_of_isSepClosed (k K : Type u) [Field k] [Field K] [Algebra k K] [IsSepClosed k] : GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k K)))
```

The spectrum of an arbitrary extension field of a separably closed field is geometrically
connected over the base.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GeometricConnectedness.lean#L324-L333) (native source range).

<a id="api-14a7d0504a072df0"></a>

### `AlgebraicGeometry.geometricallyConnected_of_isSepClosed`

```lean
theorem AlgebraicGeometry.geometricallyConnected_of_isSepClosed (k : Type u) [Field k] {X : Scheme} (f : X ⟶ Spec ↧k) [IsSepClosed k] [ConnectedSpace ↥X] : GeometricallyConnected f
```

Every connected scheme over a separably closed field is geometrically connected.

No finite-type, reducedness, irreducibility, separation, properness, algebraicity or
rational-point hypothesis is required. The statement uses the same universe for the base field,
its extension fields and the scheme, following mathlib's current geometric API.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GeometricConnectedness.lean#L337-L349) (native source range).


## SchemeProperties.GlobalSectionsBaseChange

<a id="api-d1bedea47d2c6671"></a>

### `AlgebraicGeometry.Scheme.Hom.globalSectionsAlgebra`

```lean
noncomputable def AlgebraicGeometry.Scheme.Hom.globalSectionsAlgebra (k : Type u) [CommRing k] {X : Scheme} (p : X ⟶ Spec ↧k) : Algebra k ↑(X.presheaf.obj (Opposite.op ⊤))
```

The `k`-algebra structure on the global sections of a scheme over `k`.

This is kept as an explicit definition because the structure morphism is data,
not a typeclass parameter of the scheme.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L32-L39) (native source range).

<a id="api-64ad1aa8387e4e65"></a>

### `AlgebraicGeometry.Scheme.Hom.baseChangeGlobalSectionsAlgebra`

```lean
noncomputable def AlgebraicGeometry.Scheme.Hom.baseChangeGlobalSectionsAlgebra (k K : Type u) [CommRing k] [CommRing K] [Algebra k K] {X : Scheme} (p : X ⟶ Spec ↧k) : Algebra K ↑((CategoryTheory.Limits.pullback p (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.obj (Opposite.op ⊤))
```

The `K`-algebra structure on the global sections of the base change of a
scheme along `k → K`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L41-L48) (native source range).

<a id="api-637864e0dac4c094"></a>

### `AlgebraicGeometry.Scheme.globalSectionsBaseChangeEquiv`

```lean
noncomputable def AlgebraicGeometry.Scheme.globalSectionsBaseChangeEquiv (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme} (p : X ⟶ Spec ↧k) [CompactSpace ↥X] [QuasiSeparatedSpace ↥X] : TensorProduct k K ↑(X.presheaf.obj (Opposite.op ⊤)) ≃ₐ[K] ↑((CategoryTheory.Limits.pullback p (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.obj (Opposite.op ⊤))
```

Global sections of a quasicompact quasiseparated scheme commute with
extension of the base field.

The source is oriented with the extension field on the left.  The algebra
structures occurring in the type are the canonical structures defined by the
structure morphism and the second pullback projection.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L101-L169) (native source range).

<a id="api-6b0c7fc234dca7fd"></a>

### `AlgebraicGeometry.Scheme.globalSectionsBaseChangeEquiv_tmul_one`

```lean
theorem AlgebraicGeometry.Scheme.globalSectionsBaseChangeEquiv_tmul_one (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme} (p : X ⟶ Spec ↧k) [CompactSpace ↥X] [QuasiSeparatedSpace ↥X] (r : K) : (globalSectionsBaseChangeEquiv k K p) (r ⊗ₜ[k] 1) = (CategoryTheory.ConcreteCategory.hom (Hom.appTop (CategoryTheory.Limits.pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))))) ((CategoryTheory.ConcreteCategory.hom (ΓSpecIso ↧K).inv) r)
```

On the scalar generator, the base-change equivalence is the map induced by
the projection to `Spec K`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L190-L210) (native source range).

<a id="api-8efb41f3078948d4"></a>

### `AlgebraicGeometry.Scheme.globalSectionsBaseChangeEquiv_one_tmul`

```lean
theorem AlgebraicGeometry.Scheme.globalSectionsBaseChangeEquiv_one_tmul (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme} (p : X ⟶ Spec ↧k) [CompactSpace ↥X] [QuasiSeparatedSpace ↥X] (x : ↑(X.presheaf.obj (Opposite.op ⊤))) : (globalSectionsBaseChangeEquiv k K p) (1 ⊗ₜ[k] x) = (CategoryTheory.ConcreteCategory.hom (Hom.appTop (CategoryTheory.Limits.pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K)))))) x
```

On the global-section generator, the base-change equivalence is the map
induced by the projection to `X`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L212-L230) (native source range).

<a id="api-601b3845d5a6bc19"></a>

### `AlgebraicGeometry.Scheme.globalSectionsBaseChangeEquiv_tmul`

```lean
theorem AlgebraicGeometry.Scheme.globalSectionsBaseChangeEquiv_tmul (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme} (p : X ⟶ Spec ↧k) [CompactSpace ↥X] [QuasiSeparatedSpace ↥X] (r : K) (x : ↑(X.presheaf.obj (Opposite.op ⊤))) : (globalSectionsBaseChangeEquiv k K p) (r ⊗ₜ[k] x) = (CategoryTheory.ConcreteCategory.hom (Hom.appTop (CategoryTheory.Limits.pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))))) ((CategoryTheory.ConcreteCategory.hom (ΓSpecIso ↧K).inv) r) * (CategoryTheory.ConcreteCategory.hom (Hom.appTop (CategoryTheory.Limits.pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K)))))) x
```

Formula for the canonical base-change equivalence on an arbitrary pure
tensor.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L232-L249) (native source range).

<a id="api-10aa74861c5d2f73"></a>

### `AlgebraicGeometry.Scheme.baseChangeIdentityIso`

```lean
noncomputable def AlgebraicGeometry.Scheme.baseChangeIdentityIso (k : Type u) [Field k] {X : Scheme} (p : X ⟶ Spec ↧k) : CategoryTheory.Limits.pullback p (Spec.map (CommRingCat.ofHom (algebraMap k k))) ≅ X
```

Base change along the identity extension is canonically isomorphic to the
original scheme.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L251-L260) (native source range).

<a id="api-022575ef1a51f4b9"></a>

### `AlgebraicGeometry.Scheme.baseChangeIdentityIso_hom`

```lean
theorem AlgebraicGeometry.Scheme.baseChangeIdentityIso_hom (k : Type u) [Field k] {X : Scheme} (p : X ⟶ Spec ↧k) : (baseChangeIdentityIso k p).hom = CategoryTheory.Limits.pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k k)))
```

**API note (not a source docstring):** The projection equation `AlgebraicGeometry.Scheme.baseChangeIdentityIso_hom` identifies the forward morphism of the canonical identity-base-change isomorphism with the first pullback projection to `X`. Its input is a scheme map `p : X ⟶ Spec k` for a field `k`; the equality holds without compactness or quasi-separatedness, conditions needed elsewhere for the tensor global-sections comparison.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L262-L267) (native source range).

<a id="api-e36b3603ff011ebb"></a>

### `AlgebraicGeometry.Scheme.baseChangeIdentityIso_hom_assoc`

```lean
theorem AlgebraicGeometry.Scheme.baseChangeIdentityIso_hom_assoc (k : Type u) [Field k] {X : Scheme} (p : X ⟶ Spec ↧k) {Z : Scheme} (h : X ⟶ Z) : CategoryTheory.CategoryStruct.comp (baseChangeIdentityIso k p).hom h = CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k k)))) h
```

**API note (not a source docstring):** The generated reassociation theorem `AlgebraicGeometry.Scheme.baseChangeIdentityIso_hom_assoc` says that after composing with any `h : X ⟶ Z`, the forward identity-base-change isomorphism followed by `h` is the pullback's first projection followed by `h`. This `@[reassoc]` form is owned by `baseChangeIdentityIso_hom` in `GlobalSectionsBaseChange`, not an additional geometric isomorphism.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L262-L262) (native source range).

<a id="api-a0222b4436cdca25"></a>

### `AlgebraicGeometry.Scheme.baseChangeIdentityIso_inv_fst`

```lean
theorem AlgebraicGeometry.Scheme.baseChangeIdentityIso_inv_fst (k : Type u) [Field k] {X : Scheme} (p : X ⟶ Spec ↧k) : CategoryTheory.CategoryStruct.comp (baseChangeIdentityIso k p).inv (CategoryTheory.Limits.pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k k)))) = CategoryTheory.CategoryStruct.id X
```

**API note (not a source docstring):** The equation `AlgebraicGeometry.Scheme.baseChangeIdentityIso_inv_fst` says that the inverse identity-field-base-change isomorphism followed by the first pullback projection to `X` is `𝟙 X`. The scheme isomorphism is constructed because base change along `k → k` is a pullback along an isomorphism; no quasi-compactness or quasi-separatedness is needed for this projection identity.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L271-L277) (native source range).

<a id="api-68297503433617d5"></a>

### `AlgebraicGeometry.Scheme.baseChangeIdentityIso_inv_fst_assoc`

```lean
theorem AlgebraicGeometry.Scheme.baseChangeIdentityIso_inv_fst_assoc (k : Type u) [Field k] {X : Scheme} (p : X ⟶ Spec ↧k) {Z : Scheme} (h : X ⟶ Z) : CategoryTheory.CategoryStruct.comp (baseChangeIdentityIso k p).inv (CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k k)))) h) = h
```

**API note (not a source docstring):** The generated reassociation theorem `AlgebraicGeometry.Scheme.baseChangeIdentityIso_inv_fst_assoc` appends a morphism `h : X ⟶ Z` to the first-projection inverse identity. The inverse identity-base-change isomorphism followed by the first projection and then `h` is simply `h`; `GlobalSectionsBaseChange` generates this from `baseChangeIdentityIso_inv_fst` for any scheme over the field `k`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L271-L271) (native source range).

<a id="api-4e9ca947cc66c99a"></a>

### `AlgebraicGeometry.Scheme.baseChangeIdentityIso_inv_snd`

```lean
theorem AlgebraicGeometry.Scheme.baseChangeIdentityIso_inv_snd (k : Type u) [Field k] {X : Scheme} (p : X ⟶ Spec ↧k) : CategoryTheory.CategoryStruct.comp (baseChangeIdentityIso k p).inv (CategoryTheory.Limits.pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k k)))) = p
```

**API note (not a source docstring):** The equation `AlgebraicGeometry.Scheme.baseChangeIdentityIso_inv_snd` says that the inverse of the identity-field-base-change isomorphism, followed by the pullback's projection to `Spec k`, equals the original structure morphism `p : X ⟶ Spec k`. It is a projection identity for the identity pullback, not a global-sections base-change claim requiring qcqs.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L279-L291) (native source range).

<a id="api-224d0cab05d542fd"></a>

### `AlgebraicGeometry.Scheme.baseChangeIdentityIso_inv_snd_assoc`

```lean
theorem AlgebraicGeometry.Scheme.baseChangeIdentityIso_inv_snd_assoc (k : Type u) [Field k] {X : Scheme} (p : X ⟶ Spec ↧k) {Z : Scheme} (h : Spec ↧k ⟶ Z) : CategoryTheory.CategoryStruct.comp (baseChangeIdentityIso k p).inv (CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k k)))) h) = CategoryTheory.CategoryStruct.comp p h
```

**API note (not a source docstring):** The generated reassociation theorem `AlgebraicGeometry.Scheme.baseChangeIdentityIso_inv_snd_assoc` in `GlobalSectionsBaseChange` appends `h : Spec k ⟶ Z` to the second-projection equation. From `X`, the inverse identity-base-change isomorphism followed by the pullback's second projection and `h` is `p ≫ h`; the extension is the identity on the field `k`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L279-L279) (native source range).

<a id="api-fff991eaa5abf57e"></a>

### `AlgebraicGeometry.Scheme.baseChangeIdentityIso_inv_appTop_fst`

```lean
theorem AlgebraicGeometry.Scheme.baseChangeIdentityIso_inv_appTop_fst (k : Type u) [Field k] {X : Scheme} (p : X ⟶ Spec ↧k) (x : ↑(X.presheaf.obj (Opposite.op ⊤))) : (CategoryTheory.ConcreteCategory.hom (Hom.appTop (baseChangeIdentityIso k p).inv)) ((CategoryTheory.ConcreteCategory.hom (Hom.appTop (CategoryTheory.Limits.pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k k)))))) x) = x
```

**API note (not a source docstring):** The section-level equation `AlgebraicGeometry.Scheme.baseChangeIdentityIso_inv_appTop_fst` says the inverse of the identity-base-change isomorphism sends a top-open section originally pulled from `X` along the first pullback projection back to that original section. This is the induced top-open consequence of `baseChangeIdentityIso_inv_fst`, for a scheme over a field `k` without a qcqs condition.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L293-L301) (native source range).

<a id="api-21c5a781d1111336"></a>

### `AlgebraicGeometry.Scheme.baseChangeIdentityIso_inv_appTop_snd`

```lean
theorem AlgebraicGeometry.Scheme.baseChangeIdentityIso_inv_appTop_snd (k : Type u) [Field k] {X : Scheme} (p : X ⟶ Spec ↧k) (x : ↑((Spec ↧k).presheaf.obj (Opposite.op ⊤))) : (CategoryTheory.ConcreteCategory.hom (Hom.appTop (baseChangeIdentityIso k p).inv)) ((CategoryTheory.ConcreteCategory.hom (Hom.appTop (CategoryTheory.Limits.pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k k)))))) x) = (CategoryTheory.ConcreteCategory.hom (Hom.appTop p)) x
```

**API note (not a source docstring):** The section-level equation `AlgebraicGeometry.Scheme.baseChangeIdentityIso_inv_appTop_snd` sends a section `x` of `Spec k` first along the identity-base-change second projection and then through the inverse scheme isomorphism; the result is `p.appTop x` on `X`. It follows from `baseChangeIdentityIso_inv_snd` and applies to an arbitrary scheme map `p : X ⟶ Spec k` with `k` a field.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L303-L311) (native source range).

<a id="api-2856899d971572ec"></a>

### `AlgebraicGeometry.Scheme.globalSectionsBaseChangeIdentityEquiv`

```lean
noncomputable def AlgebraicGeometry.Scheme.globalSectionsBaseChangeIdentityEquiv (k : Type u) [Field k] {X : Scheme} (p : X ⟶ Spec ↧k) : ↑((CategoryTheory.Limits.pullback p (Spec.map (CommRingCat.ofHom (algebraMap k k)))).presheaf.obj (Opposite.op ⊤)) ≃ₐ[k] ↑(X.presheaf.obj (Opposite.op ⊤))
```

Transport of global sections along identity base change.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L313-L337) (native source range).

<a id="api-36b82553d2c54201"></a>

### `AlgebraicGeometry.Scheme.globalSectionsBaseChangeIdentityEquiv_apply`

```lean
theorem AlgebraicGeometry.Scheme.globalSectionsBaseChangeIdentityEquiv_apply (k : Type u) [Field k] {X : Scheme} (p : X ⟶ Spec ↧k) (x : ↑((CategoryTheory.Limits.pullback p (Spec.map (CommRingCat.ofHom (algebraMap k k)))).presheaf.obj (Opposite.op ⊤))) : (globalSectionsBaseChangeIdentityEquiv k p) x = (CategoryTheory.ConcreteCategory.hom (Hom.appTop (baseChangeIdentityIso k p).inv)) x
```

**API note (not a source docstring):** The evaluation rule `AlgebraicGeometry.Scheme.globalSectionsBaseChangeIdentityEquiv_apply` says that transporting a top-open section of the identity field-base-changed scheme back to `X` uses `(baseChangeIdentityIso k p).inv.appTop`. The underlying equivalence is of `k`-algebras induced by the identity pullback isomorphism; unlike the tensor base-change theorem, this transport does not require `X` to be qcqs.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L339-L346) (native source range).

<a id="api-6596d781f89c53ad"></a>

### `AlgebraicGeometry.Scheme.globalSectionsBaseChangeEquiv_identity`

```lean
theorem AlgebraicGeometry.Scheme.globalSectionsBaseChangeEquiv_identity (k : Type u) [Field k] {X : Scheme} (p : X ⟶ Spec ↧k) [CompactSpace ↥X] [QuasiSeparatedSpace ↥X] : (globalSectionsBaseChangeEquiv k k p).trans (globalSectionsBaseChangeIdentityEquiv k p) = Algebra.TensorProduct.lid k ↑(X.presheaf.obj (Opposite.op ⊤))
```

The canonical global-sections equivalence for the identity field extension
is the tensor-product left unitor after transporting along
`baseChangeIdentityIso`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L348-L370) (native source range).

<a id="api-6d53ddb199d4b9a3"></a>

### `AlgebraicGeometry.Scheme.baseChangeTowerIso`

```lean
noncomputable def AlgebraicGeometry.Scheme.baseChangeTowerIso (k K L : Type u) [Field k] [Field K] [Field L] [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L] {X : Scheme} (p : X ⟶ Spec ↧k) : CategoryTheory.Limits.pullback (CategoryTheory.Limits.pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≅ CategoryTheory.Limits.pullback p (Spec.map (CommRingCat.ofHom (algebraMap k L)))
```

The canonical identification between successive base change through
`k → K → L` and direct base change from `k` to `L`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L396-L427) (native source range).

<a id="api-094a757b4253588a"></a>

### `AlgebraicGeometry.Scheme.baseChangeTowerIso_hom_fst`

```lean
theorem AlgebraicGeometry.Scheme.baseChangeTowerIso_hom_fst (k K L : Type u) [Field k] [Field K] [Field L] [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L] {X : Scheme} (p : X ⟶ Spec ↧k) : CategoryTheory.CategoryStruct.comp (baseChangeTowerIso k K L p).hom (CategoryTheory.Limits.pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k L)))) = CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (Spec.map (CommRingCat.ofHom (algebraMap K L)))) (CategoryTheory.Limits.pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K))))
```

**API note (not a source docstring):** The projection identity `AlgebraicGeometry.Scheme.baseChangeTowerIso_hom_fst` says the forward isomorphism between successive and direct field base change, followed by the direct first projection to `X`, equals the composition of first projections of the two successive pullbacks. It belongs to `GlobalSectionsBaseChange` and assumes compatible `k → K → L` algebra structures; no qcqs assumption occurs in this scheme-level identity.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L438-L450) (native source range).

<a id="api-b4fea25aeca23e46"></a>

### `AlgebraicGeometry.Scheme.baseChangeTowerIso_hom_fst_assoc`

```lean
theorem AlgebraicGeometry.Scheme.baseChangeTowerIso_hom_fst_assoc (k K L : Type u) [Field k] [Field K] [Field L] [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L] {X : Scheme} (p : X ⟶ Spec ↧k) {Z : Scheme} (h : X ⟶ Z) : CategoryTheory.CategoryStruct.comp (baseChangeTowerIso k K L p).hom (CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k L)))) h) = CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (Spec.map (CommRingCat.ofHom (algebraMap K L)))) (CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K)))) h)
```

**API note (not a source docstring):** The generated reassociation lemma `AlgebraicGeometry.Scheme.baseChangeTowerIso_hom_fst_assoc` appends a morphism `h : X ⟶ Z` to the equation for the forward tower isomorphism and first projections. Its left path goes through the direct `k → L` projection to `X`; the right path goes through both successive first projections to `X`, then `h`. It is generated from `baseChangeTowerIso_hom_fst` under the field scalar-tower hypotheses.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L438-L438) (native source range).

<a id="api-978992ba9cb93386"></a>

### `AlgebraicGeometry.Scheme.baseChangeTowerIso_hom_snd`

```lean
theorem AlgebraicGeometry.Scheme.baseChangeTowerIso_hom_snd (k K L : Type u) [Field k] [Field K] [Field L] [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L] {X : Scheme} (p : X ⟶ Spec ↧k) : CategoryTheory.CategoryStruct.comp (baseChangeTowerIso k K L p).hom (CategoryTheory.Limits.pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k L)))) = CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (Spec.map (CommRingCat.ofHom (algebraMap K L)))
```

**API note (not a source docstring):** The projection identity `AlgebraicGeometry.Scheme.baseChangeTowerIso_hom_snd` says the forward tower isomorphism from successive `k → K → L` base change to direct `k → L` base change, followed by the direct second projection, is the iterated pullback's final projection to `Spec L`. Only the fields, their algebra structures, `IsScalarTower`, and the original structure map are needed.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L452-L463) (native source range).

<a id="api-f1f15ac20fa36187"></a>

### `AlgebraicGeometry.Scheme.baseChangeTowerIso_hom_snd_assoc`

```lean
theorem AlgebraicGeometry.Scheme.baseChangeTowerIso_hom_snd_assoc (k K L : Type u) [Field k] [Field K] [Field L] [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L] {X : Scheme} (p : X ⟶ Spec ↧k) {Z : Scheme} (h : Spec ↧L ⟶ Z) : CategoryTheory.CategoryStruct.comp (baseChangeTowerIso k K L p).hom (CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k L)))) h) = CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (Spec.map (CommRingCat.ofHom (algebraMap K L)))) h
```

**API note (not a source docstring):** The generated reassociation lemma `AlgebraicGeometry.Scheme.baseChangeTowerIso_hom_snd_assoc` states the `baseChangeTowerIso_hom_snd` equation after right-composition with `h : Spec L ⟶ Z`. Thus the forward isomorphism followed by the direct `Spec L` projection and `h` equals the iterated pullback's final projection and `h`; it is owned by `GlobalSectionsBaseChange` and assumes a compatible field tower.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L452-L452) (native source range).

<a id="api-9d3b46dc76ca8a3a"></a>

### `AlgebraicGeometry.Scheme.baseChangeTowerIso_inv_snd`

```lean
theorem AlgebraicGeometry.Scheme.baseChangeTowerIso_inv_snd (k K L : Type u) [Field k] [Field K] [Field L] [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L] {X : Scheme} (p : X ⟶ Spec ↧k) : CategoryTheory.CategoryStruct.comp (baseChangeTowerIso k K L p).inv (CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (Spec.map (CommRingCat.ofHom (algebraMap K L)))) = CategoryTheory.Limits.pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k L)))
```

**API note (not a source docstring):** The equation `AlgebraicGeometry.Scheme.baseChangeTowerIso_inv_snd` identifies the inverse tower isomorphism followed by the second projection of successive base change `k → K → L` with the second projection of direct base change `k → L`, both landing in `Spec L`. It uses the compatible field algebras and `IsScalarTower k K L`, not a compactness or separatedness condition on `X`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L465-L475) (native source range).

<a id="api-125bbc45f185dab3"></a>

### `AlgebraicGeometry.Scheme.baseChangeTowerIso_inv_snd_assoc`

```lean
theorem AlgebraicGeometry.Scheme.baseChangeTowerIso_inv_snd_assoc (k K L : Type u) [Field k] [Field K] [Field L] [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L] {X : Scheme} (p : X ⟶ Spec ↧k) {Z : Scheme} (h : Spec ↧L ⟶ Z) : CategoryTheory.CategoryStruct.comp (baseChangeTowerIso k K L p).inv (CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (Spec.map (CommRingCat.ofHom (algebraMap K L)))) h) = CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k L)))) h
```

**API note (not a source docstring):** The generated reassociation lemma `AlgebraicGeometry.Scheme.baseChangeTowerIso_inv_snd_assoc` extends `baseChangeTowerIso_inv_snd` in `GlobalSectionsBaseChange` by a morphism `h : Spec L ⟶ Z` composed on the right. Following the inverse tower isomorphism and the final iterated second projection, then `h`, agrees with the direct second projection followed by `h`; it uses the field scalar-tower assumptions.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L465-L465) (native source range).

<a id="api-5e723d61b7123853"></a>

### `AlgebraicGeometry.Scheme.baseChangeTowerIso_inv_fst`

```lean
theorem AlgebraicGeometry.Scheme.baseChangeTowerIso_inv_fst (k K L : Type u) [Field k] [Field K] [Field L] [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L] {X : Scheme} (p : X ⟶ Spec ↧k) : CategoryTheory.CategoryStruct.comp (baseChangeTowerIso k K L p).inv (CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (Spec.map (CommRingCat.ofHom (algebraMap K L)))) (CategoryTheory.Limits.pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K))))) = CategoryTheory.Limits.pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k L)))
```

**API note (not a source docstring):** The equation `AlgebraicGeometry.Scheme.baseChangeTowerIso_inv_fst` says that the inverse of the canonical tower isomorphism, followed by the first projection from the iterated pullback and then the first `k → K` projection, equals the first projection from the direct `k → L` pullback to `X`. Its owner is the tower construction in `GlobalSectionsBaseChange`, under compatible field algebras and `IsScalarTower`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L477-L489) (native source range).

<a id="api-fb0c69a49011dad8"></a>

### `AlgebraicGeometry.Scheme.baseChangeTowerIso_inv_fst_assoc`

```lean
theorem AlgebraicGeometry.Scheme.baseChangeTowerIso_inv_fst_assoc (k K L : Type u) [Field k] [Field K] [Field L] [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L] {X : Scheme} (p : X ⟶ Spec ↧k) {Z : Scheme} (h : X ⟶ Z) : CategoryTheory.CategoryStruct.comp (baseChangeTowerIso k K L p).inv (CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (Spec.map (CommRingCat.ofHom (algebraMap K L)))) (CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K)))) h)) = CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k L)))) h
```

**API note (not a source docstring):** The generated reassociation lemma `AlgebraicGeometry.Scheme.baseChangeTowerIso_inv_fst_assoc` comes from `baseChangeTowerIso_inv_fst` in `GlobalSectionsBaseChange`. After composing both sides on the right with a morphism `h : X ⟶ Z`, the inverse tower isomorphism followed by both successive first projections agrees with the direct first projection followed by `h`; it assumes a compatible field tower, not qcqs.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L477-L477) (native source range).

<a id="api-74fc248581100a5f"></a>

### `AlgebraicGeometry.Scheme.baseChangeTowerIso_inv_appTop_fst_fst`

```lean
theorem AlgebraicGeometry.Scheme.baseChangeTowerIso_inv_appTop_fst_fst (k K L : Type u) [Field k] [Field K] [Field L] [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L] {X : Scheme} (p : X ⟶ Spec ↧k) (x : ↑(X.presheaf.obj (Opposite.op ⊤))) : (CategoryTheory.ConcreteCategory.hom (Hom.appTop (baseChangeTowerIso k K L p).inv)) ((CategoryTheory.ConcreteCategory.hom (Hom.appTop (CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (Spec.map (CommRingCat.ofHom (algebraMap K L)))))) ((CategoryTheory.ConcreteCategory.hom (Hom.appTop (CategoryTheory.Limits.pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K)))))) x)) = (CategoryTheory.ConcreteCategory.hom (Hom.appTop (CategoryTheory.Limits.pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k L)))))) x
```

**API note (not a source docstring):** The simplification lemma `AlgebraicGeometry.Scheme.baseChangeTowerIso_inv_appTop_fst_fst` evaluates the inverse tower isomorphism on a global section of `X` pulled back by both first projections: it equals pullback of that section by the direct `k → L` first projection. It is the section-level form of `baseChangeTowerIso_inv_fst`, assuming compatible field algebras and `IsScalarTower k K L`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L491-L504) (native source range).

<a id="api-942eff84cfdb2851"></a>

### `AlgebraicGeometry.Scheme.globalSectionsBaseChangeTowerEquiv`

```lean
noncomputable def AlgebraicGeometry.Scheme.globalSectionsBaseChangeTowerEquiv (k K L : Type u) [Field k] [Field K] [Field L] [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L] {X : Scheme} (p : X ⟶ Spec ↧k) : have q := CategoryTheory.Limits.pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K))); ↑((CategoryTheory.Limits.pullback q (Spec.map (CommRingCat.ofHom (algebraMap K L)))).presheaf.obj (Opposite.op ⊤)) ≃ₐ[L] ↑((CategoryTheory.Limits.pullback p (Spec.map (CommRingCat.ofHom (algebraMap k L)))).presheaf.obj (Opposite.op ⊤))
```

Transport of global sections along `baseChangeTowerIso`, as an
`L`-algebra equivalence.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L506-L535) (native source range).

<a id="api-68a0478247a2e487"></a>

### `AlgebraicGeometry.Scheme.globalSectionsBaseChangeTowerEquiv_apply`

```lean
theorem AlgebraicGeometry.Scheme.globalSectionsBaseChangeTowerEquiv_apply (k K L : Type u) [Field k] [Field K] [Field L] [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L] {X : Scheme} (p : X ⟶ Spec ↧k) (x : ↑((CategoryTheory.Limits.pullback (CategoryTheory.Limits.pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (Spec.map (CommRingCat.ofHom (algebraMap K L)))).presheaf.obj (Opposite.op ⊤))) : have q := CategoryTheory.Limits.pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K))); (globalSectionsBaseChangeTowerEquiv k K L p) x = (CategoryTheory.ConcreteCategory.hom (Hom.appTop (baseChangeTowerIso k K L p).inv)) x
```

**API note (not a source docstring):** The evaluation rule `AlgebraicGeometry.Scheme.globalSectionsBaseChangeTowerEquiv_apply` identifies the transport of a global section from successive field base change `k → K → L` to direct base change `k → L` with the map on top-open sections induced by the inverse of `baseChangeTowerIso`. The fields carry a compatible `IsScalarTower`; this transport rule itself imposes no qcqs hypothesis.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L537-L550) (native source range).

<a id="api-be09e74402e150e9"></a>

### `AlgebraicGeometry.Scheme.globalSectionsBaseChangeEquiv_tower`

```lean
theorem AlgebraicGeometry.Scheme.globalSectionsBaseChangeEquiv_tower (k K L : Type u) [Field k] [Field K] [Field L] [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L] {X : Scheme} (p : X ⟶ Spec ↧k) [CompactSpace ↥X] [QuasiSeparatedSpace ↥X] : let q := CategoryTheory.Limits.pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K))); (Algebra.TensorProduct.congr AlgEquiv.refl (globalSectionsBaseChangeEquiv k K p)).trans ((globalSectionsBaseChangeEquiv K L q).trans (globalSectionsBaseChangeTowerEquiv k K L p)) = (Algebra.TensorProduct.cancelBaseChange k K L L ↑(X.presheaf.obj (Opposite.op ⊤))).trans (globalSectionsBaseChangeEquiv k L p)
```

Base change of global sections is compatible with a tower of field
extensions.  The left side performs the two extensions successively; the
right side first uses the canonical tensor cancellation and then extends
directly from `k` to `L`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/GlobalSectionsBaseChange.lean#L552-L603) (native source range).


## SchemeProperties.IdealSheafModule

<a id="api-7fbb00fae6705ef7"></a>

### `AlgebraicGeometry.Scheme.IdealSheafData.toSubmodule`

```lean
noncomputable def AlgebraicGeometry.Scheme.IdealSheafData.toSubmodule {X : Scheme} (I : X.IdealSheafData) : (SheafOfModules.unit X.ringCatSheaf).Submodule
```

An ideal sheaf as a submodule of the structure sheaf.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/IdealSheafModule.lean#L65-L95) (native source range).

<a id="api-c47995698d057cd6"></a>

### `AlgebraicGeometry.Scheme.IdealSheafData.toModule`

```lean
noncomputable def AlgebraicGeometry.Scheme.IdealSheafData.toModule {X : Scheme} (I : X.IdealSheafData) : X.Modules
```

The sheaf of modules underlying an ideal sheaf.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/IdealSheafModule.lean#L102-L105) (native source range).

<a id="api-b013e8a3eecab144"></a>

### `AlgebraicGeometry.Scheme.IdealSheafData.toModuleι`

```lean
noncomputable def AlgebraicGeometry.Scheme.IdealSheafData.toModuleι {X : Scheme} (I : X.IdealSheafData) : I.toModule ⟶ SheafOfModules.unit X.ringCatSheaf
```

The canonical inclusion of an ideal sheaf module into the structure sheaf.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/IdealSheafModule.lean#L107-L111) (native source range).

<a id="api-be081c221a863c63"></a>

### `AlgebraicGeometry.Scheme.IdealSheafData.toModuleι_mono`

```lean
instance AlgebraicGeometry.Scheme.IdealSheafData.toModuleι_mono {X : Scheme} (I : X.IdealSheafData) : CategoryTheory.Mono I.toModuleι
```

The canonical inclusion of an ideal sheaf module is a monomorphism.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/IdealSheafModule.lean#L113-L121) (native source range).

<a id="api-6855d111720cea9d"></a>

### `AlgebraicGeometry.Scheme.IdealSheafData.toModuleSubobject`

```lean
noncomputable def AlgebraicGeometry.Scheme.IdealSheafData.toModuleSubobject {X : Scheme} (I : X.IdealSheafData) : CategoryTheory.Subobject (SheafOfModules.unit X.ringCatSheaf)
```

An ideal sheaf as a subobject of the structure sheaf.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/IdealSheafModule.lean#L123-L129) (native source range).

<a id="api-05ece5f346be5ca1"></a>

### `AlgebraicGeometry.Scheme.IdealSheafData.affineSectionsEquiv`

```lean
noncomputable def AlgebraicGeometry.Scheme.IdealSheafData.affineSectionsEquiv {X : Scheme} (I : X.IdealSheafData) (U : ↑X.affineOpens) : ↑(I.toModule.presheaf.obj (Opposite.op ↑U)) ≃ₗ[↑(X.presheaf.obj (Opposite.op ↑U))] ↥(I.ideal U)
```

On an affine open, sections of the ideal sheaf module are the specified ideal.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/IdealSheafModule.lean#L132-L148) (native source range).

<a id="api-6e6609f669741107"></a>

### `AlgebraicGeometry.Scheme.IdealSheafData.affineSectionsEquiv_apply`

```lean
theorem AlgebraicGeometry.Scheme.IdealSheafData.affineSectionsEquiv_apply {X : Scheme} (I : X.IdealSheafData) (U : ↑X.affineOpens) (s : ↑(I.toModule.presheaf.obj (Opposite.op ↑U))) : ↑((I.affineSectionsEquiv U) s) = (CategoryTheory.ConcreteCategory.hom (Modules.Hom.app I.toModuleι ↑U)) s
```

The affine-sections equivalence is literally compatible with inclusion into
the structure sheaf.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/IdealSheafModule.lean#L150-L156) (native source range).

<a id="api-372552781b67938e"></a>

### `AlgebraicGeometry.Scheme.IdealSheafData.toModule_isLocalizedModule_basicOpen`

```lean
theorem AlgebraicGeometry.Scheme.IdealSheafData.toModule_isLocalizedModule_basicOpen {X : Scheme} (I : X.IdealSheafData) (U : ↑X.affineOpens) (f : ↑(X.presheaf.obj (Opposite.op ↑U))) : IsLocalizedModule.Away f (I.toModule.basicOpenRestriction f)
```

Restriction of an ideal sheaf module from an affine open to a basic open is
localization away from the section defining the basic open.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/IdealSheafModule.lean#L159-L227) (native source range).

<a id="api-8584359b3185c0f2"></a>

### `AlgebraicGeometry.Scheme.IdealSheafData.toModule_isQuasicoherent`

```lean
theorem AlgebraicGeometry.Scheme.IdealSheafData.toModule_isQuasicoherent {X : Scheme} (I : X.IdealSheafData) : SheafOfModules.IsQuasicoherent I.toModule
```

The module associated to any ideal sheaf data is quasicoherent.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/IdealSheafModule.lean#L321-L380) (native source range).

<a id="api-66fbe13a25d9737b"></a>

### `AlgebraicGeometry.Scheme.nilradicalModule`

```lean
noncomputable def AlgebraicGeometry.Scheme.nilradicalModule (X : Scheme) : X.Modules
```

The nilradical ideal sheaf as a module over the structure sheaf.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/IdealSheafModule.lean#L384-L387) (native source range).

<a id="api-57d0c086f71c524c"></a>

### `AlgebraicGeometry.Scheme.nilradicalModuleι`

```lean
noncomputable def AlgebraicGeometry.Scheme.nilradicalModuleι (X : Scheme) : X.nilradicalModule ⟶ SheafOfModules.unit X.ringCatSheaf
```

The inclusion of the nilradical module into the structure sheaf.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/IdealSheafModule.lean#L389-L392) (native source range).

<a id="api-da987c0fb151745c"></a>

### `AlgebraicGeometry.Scheme.nilradicalModuleSubobject`

```lean
noncomputable def AlgebraicGeometry.Scheme.nilradicalModuleSubobject (X : Scheme) : CategoryTheory.Subobject (SheafOfModules.unit X.ringCatSheaf)
```

The nilradical ideal sheaf as a subobject of the structure sheaf.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/IdealSheafModule.lean#L394-L398) (native source range).

<a id="api-1363676451c3eb79"></a>

### `AlgebraicGeometry.Scheme.nilradicalModule_isQuasicoherent`

```lean
theorem AlgebraicGeometry.Scheme.nilradicalModule_isQuasicoherent (X : Scheme) : SheafOfModules.IsQuasicoherent X.nilradicalModule
```

The nilradical module is quasicoherent.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/IdealSheafModule.lean#L400-L403) (native source range).

<a id="api-271ae3296c2b2099"></a>

### `AlgebraicGeometry.Scheme.nilradicalModuleAffineSections`

```lean
noncomputable def AlgebraicGeometry.Scheme.nilradicalModuleAffineSections (X : Scheme) (U : ↑X.affineOpens) : ↑(X.nilradicalModule.presheaf.obj (Opposite.op ↑U)) ≃ₗ[↑(X.presheaf.obj (Opposite.op ↑U))] ↥(_root_.nilradical ↑(X.presheaf.obj (Opposite.op ↑U)))
```

Sections of the nilradical module on an affine open are the nilradical of
the ring of functions on that open.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/IdealSheafModule.lean#L405-L410) (native source range).


## SchemeProperties.Integral

<a id="api-ea194abf91b09e0b"></a>

### `Ideal.eq_of_mem_minimalPrimes_of_le_of_isDomain_atPrime`

```lean
theorem Ideal.eq_of_mem_minimalPrimes_of_le_of_isDomain_atPrime {R : Type u_1} {A : Type u_2} [CommRing R] [CommRing A] [Algebra R A] {p q₁ q₂ : Ideal R} [p.IsPrime] [IsLocalization.AtPrime A p] (hq₁ : q₁ ∈ minimalPrimes R) (hq₂ : q₂ ∈ minimalPrimes R) (h₁ : q₁ ≤ p) (h₂ : q₂ ≤ p) [IsDomain A] : q₁ = q₂
```

Two minimal primes contained in a prime are equal when the localization at
that prime is a domain.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Integral.lean#L25-L49) (native source range).

<a id="api-f9f39edeb7e66999"></a>

### `AlgebraicGeometry.eq_irreducibleComponents_of_mem_of_isDomain_stalk`

```lean
theorem AlgebraicGeometry.eq_irreducibleComponents_of_mem_of_isDomain_stalk (X : Scheme) (x : ↥X) [IsDomain ↑(X.presheaf.stalk x)] {Z W : Set ↥X} (hZ : Z ∈ irreducibleComponents ↥X) (hW : W ∈ irreducibleComponents ↥X) (hxZ : x ∈ Z) (hxW : x ∈ W) : Z = W
```

A point whose local ring is a domain lies on a unique irreducible
component.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Integral.lean#L55-L127) (native source range).

<a id="api-b45adb154610679c"></a>

### `AlgebraicGeometry.isOpen_of_mem_irreducibleComponents_of_isLocallyNoetherian_of_stalk_isDomain`

```lean
theorem AlgebraicGeometry.isOpen_of_mem_irreducibleComponents_of_isLocallyNoetherian_of_stalk_isDomain (X : Scheme) [IsLocallyNoetherian X] [∀ (x : ↥X), IsDomain ↑(X.presheaf.stalk x)] {Z : Set ↥X} (hZ : Z ∈ irreducibleComponents ↥X) : IsOpen Z
```

If a locally Noetherian scheme has domain local rings, then its
irreducible components are open.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Integral.lean#L154-L178) (native source range).

<a id="api-3207f341141a1b01"></a>

### `AlgebraicGeometry.irreducibleSpace_of_isLocallyNoetherian_of_connectedSpace_of_stalk_isDomain`

```lean
theorem AlgebraicGeometry.irreducibleSpace_of_isLocallyNoetherian_of_connectedSpace_of_stalk_isDomain (X : Scheme) [IsLocallyNoetherian X] [ConnectedSpace ↥X] [∀ (x : ↥X), IsDomain ↑(X.presheaf.stalk x)] : IrreducibleSpace ↥X
```

A connected locally Noetherian scheme with domain local rings is
irreducible.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Integral.lean#L180-L196) (native source range).

<a id="api-a325dcddba1638f1"></a>

### `AlgebraicGeometry.isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_stalk_isDomain`

```lean
theorem AlgebraicGeometry.isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_stalk_isDomain (X : Scheme) [IsLocallyNoetherian X] [ConnectedSpace ↥X] [∀ (x : ↥X), IsDomain ↑(X.presheaf.stalk x)] : IsIntegral X
```

A connected locally Noetherian scheme with domain local rings is
integral.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Integral.lean#L198-L205) (native source range).

<a id="api-5a79f2f5b8cb7e8a"></a>

### `AlgebraicGeometry.irreducibleSpace_of_isNoetherian_of_connectedSpace_of_stalk_isDomain`

```lean
theorem AlgebraicGeometry.irreducibleSpace_of_isNoetherian_of_connectedSpace_of_stalk_isDomain (X : Scheme) [IsNoetherian X] [ConnectedSpace ↥X] [∀ (x : ↥X), IsDomain ↑(X.presheaf.stalk x)] : IrreducibleSpace ↥X
```

A connected Noetherian scheme with domain local rings is irreducible.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Integral.lean#L207-L211) (native source range).

<a id="api-6d8c5e1d65e4a575"></a>

### `AlgebraicGeometry.isIntegral_of_isNoetherian_of_connectedSpace_of_stalk_isDomain`

```lean
theorem AlgebraicGeometry.isIntegral_of_isNoetherian_of_connectedSpace_of_stalk_isDomain (X : Scheme) [IsNoetherian X] [ConnectedSpace ↥X] [∀ (x : ↥X), IsDomain ↑(X.presheaf.stalk x)] : IsIntegral X
```

A connected Noetherian scheme with domain local rings is integral.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Integral.lean#L213-L217) (native source range).


## SchemeProperties.ModuleProperties

<a id="api-a4ca41374083a1d7"></a>

### `AlgebraicGeometry.Scheme.Modules.stalkModule`

```lean
noncomputable instance AlgebraicGeometry.Scheme.Modules.stalkModule {X : Scheme} (P : X.Modules) (x : ↥X) : Module ↑(X.presheaf.stalk x) ↑(P.presheaf.stalk x)
```

The stalk of a module on a scheme is a module over the scheme's stalk.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleProperties.lean#L40-L44) (native source range).

<a id="api-48b7bbf3909f0906"></a>

### `AlgebraicGeometry.Scheme.Modules.IsTorsionFree`

```lean
class AlgebraicGeometry.Scheme.Modules.IsTorsionFree {X : Scheme} (P : X.Modules) : Prop
```

A module on a scheme is torsion-free if each stalk is torsion-free over the
corresponding stalk of the structure sheaf.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleProperties.lean#L87-L90) (native source range).

<a id="api-7edee59480f4bb86"></a>

### `AlgebraicGeometry.Scheme.Modules.IsTorsionFree.mk`

```lean
constructor AlgebraicGeometry.Scheme.Modules.IsTorsionFree.mk : ∀ {X : AlgebraicGeometry.Scheme} {P : X.Modules}, (∀ (x : ↥X), Module.IsTorsionFree ↑(X.presheaf.stalk x) ↑(P.presheaf.stalk x)) → P.IsTorsionFree
```

**API note (not a source docstring):** The constructor `AlgebraicGeometry.Scheme.Modules.IsTorsionFree.mk` in `ModuleProperties` builds a stalkwise torsion-free scheme-module instance from a proof of `Module.IsTorsionFree` at every point over its structure-sheaf stalk. Its input ranges over the points of a fixed scheme `X` and an arbitrary `X.Modules` object `P`; it does not require an integral scheme or global-sections torsion-freeness.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleProperties.lean#L87-L90) (native source range).

<a id="api-7bb70d69d555b804"></a>

### `AlgebraicGeometry.Scheme.Modules.IsTorsionFree.stalk`

```lean
theorem AlgebraicGeometry.Scheme.Modules.IsTorsionFree.stalk {X : Scheme} {P : X.Modules} [self : P.IsTorsionFree] (x : ↥X) : Module.IsTorsionFree ↑(X.presheaf.stalk x) ↑(P.presheaf.stalk x)
```

**API note (not a source docstring):** The registered field `AlgebraicGeometry.Scheme.Modules.IsTorsionFree.stalk` retrieves `Module.IsTorsionFree` for `P.presheaf.stalk x` over the corresponding local ring `X.presheaf.stalk x` at every point `x`. Its owner `ModuleProperties` defines the scheme-module class stalkwise; the property is not stated for every open's section module, and no integral or quasicoherent assumption is implicit.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleProperties.lean#L90-L90) (native source range).

<a id="api-10415feccd871ecd"></a>

### `AlgebraicGeometry.Scheme.Modules.IsTorsionFree.ofIso`

```lean
theorem AlgebraicGeometry.Scheme.Modules.IsTorsionFree.ofIso {X : Scheme} {P Q : X.Modules} (e : P ≅ Q) (hP : P.IsTorsionFree) : Q.IsTorsionFree
```

Torsion-freeness is preserved by isomorphisms of modules on a scheme.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleProperties.lean#L94-L102) (native source range).

<a id="api-b36f14be6f61dac9"></a>

### `AlgebraicGeometry.Scheme.Modules.isTorsionFree_iff_of_iso`

```lean
theorem AlgebraicGeometry.Scheme.Modules.isTorsionFree_iff_of_iso {X : Scheme} {P Q : X.Modules} (e : P ≅ Q) : P.IsTorsionFree ↔ Q.IsTorsionFree
```

Isomorphic modules on a scheme are simultaneously torsion-free.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleProperties.lean#L104-L107) (native source range).

<a id="api-ab8cb70de4bffa15"></a>

### `AlgebraicGeometry.Scheme.Modules.VanishesAtGenericPoints`

```lean
class AlgebraicGeometry.Scheme.Modules.VanishesAtGenericPoints {X : Scheme} (P : X.Modules) : Prop
```

A module on a scheme vanishes at generic points if its stalk is zero at the
generic point of every irreducible component.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleProperties.lean#L109-L112) (native source range).

<a id="api-00e65520555931d7"></a>

### `AlgebraicGeometry.Scheme.Modules.VanishesAtGenericPoints.mk`

```lean
constructor AlgebraicGeometry.Scheme.Modules.VanishesAtGenericPoints.mk : ∀ {X : AlgebraicGeometry.Scheme} {P : X.Modules}, (∀ (x : ↑(genericPoints ↥X)), Subsingleton ↑(P.presheaf.stalk ↑x)) → P.VanishesAtGenericPoints
```

**API note (not a source docstring):** The constructor `AlgebraicGeometry.Scheme.Modules.VanishesAtGenericPoints.mk` in `ModuleProperties` packages a `Subsingleton` proof for each module stalk indexed by `genericPoints X` into `VanishesAtGenericPoints P`. Its own field is the generic-point stalk condition, not vanishing of every section or every stalk; the associated module need not be quasicoherent.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleProperties.lean#L109-L112) (native source range).

<a id="api-7651b720e1a0cd5c"></a>

### `AlgebraicGeometry.Scheme.Modules.VanishesAtGenericPoints.stalk`

```lean
theorem AlgebraicGeometry.Scheme.Modules.VanishesAtGenericPoints.stalk {X : Scheme} {P : X.Modules} [self : P.VanishesAtGenericPoints] (x : ↑(genericPoints ↥X)) : Subsingleton ↑(P.presheaf.stalk ↑x)
```

**API note (not a source docstring):** The field `AlgebraicGeometry.Scheme.Modules.VanishesAtGenericPoints.stalk` of the class in `ModuleProperties` supplies `Subsingleton (P.presheaf.stalk x.1)` at every `x : genericPoints X`, i.e. the module stalk at each irreducible-component generic point is zero. It is registered as an instance and requires neither quasicoherence nor finiteness; it says nothing about stalks at arbitrary nongeneric points.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleProperties.lean#L112-L112) (native source range).

<a id="api-a2abd4df30ac5923"></a>

### `AlgebraicGeometry.Scheme.Modules.VanishesAtGenericPoints.ofIso`

```lean
theorem AlgebraicGeometry.Scheme.Modules.VanishesAtGenericPoints.ofIso {X : Scheme} {P Q : X.Modules} (e : P ≅ Q) (hP : P.VanishesAtGenericPoints) : Q.VanishesAtGenericPoints
```

Vanishing at generic points is preserved by isomorphisms of modules.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleProperties.lean#L116-L121) (native source range).

<a id="api-8a8992f3c4f12bed"></a>

### `AlgebraicGeometry.Scheme.Modules.vanishesAtGenericPoints_iff_of_iso`

```lean
theorem AlgebraicGeometry.Scheme.Modules.vanishesAtGenericPoints_iff_of_iso {X : Scheme} {P Q : X.Modules} (e : P ≅ Q) : P.VanishesAtGenericPoints ↔ Q.VanishesAtGenericPoints
```

Isomorphic modules simultaneously vanish at all component generic points.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleProperties.lean#L123-L127) (native source range).

<a id="api-e0b8c8e670d604e3"></a>

### `AlgebraicGeometry.Scheme.Modules.vanishesAtGenericPoints_iff_irreducibleComponents`

```lean
theorem AlgebraicGeometry.Scheme.Modules.vanishesAtGenericPoints_iff_irreducibleComponents {X : Scheme} (P : X.Modules) : P.VanishesAtGenericPoints ↔ ∀ (Z : ↑(irreducibleComponents ↥X)), Subsingleton ↑(P.presheaf.stalk ↑(genericPoints.ofComponent Z))
```

Generic-point vanishing can equivalently be indexed by irreducible
components.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleProperties.lean#L129-L141) (native source range).

<a id="api-019a0449c7a6c0a9"></a>

### `AlgebraicGeometry.Scheme.Modules.empty_isTorsionFree`

```lean
instance AlgebraicGeometry.Scheme.Modules.empty_isTorsionFree {X : Scheme} [IsEmpty ↥X] (P : X.Modules) : P.IsTorsionFree
```

Every module on an empty scheme is torsion-free.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleProperties.lean#L143-L146) (native source range).

<a id="api-100b4aa3387d4dd3"></a>

### `AlgebraicGeometry.Scheme.Modules.empty_vanishesAtGenericPoints`

```lean
instance AlgebraicGeometry.Scheme.Modules.empty_vanishesAtGenericPoints {X : Scheme} [IsEmpty ↥X] (P : X.Modules) : P.VanishesAtGenericPoints
```

Every module on an empty scheme vanishes at all generic points.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleProperties.lean#L148-L151) (native source range).

<a id="api-14f9ad628362bfaf"></a>

### `AlgebraicGeometry.Scheme.Modules.zeroStalkSubsingleton`

```lean
instance AlgebraicGeometry.Scheme.Modules.zeroStalkSubsingleton {X : Scheme} (x : ↥X) : Subsingleton ↑((presheaf 0).stalk x)
```

Every stalk of the zero module on a scheme is zero.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleProperties.lean#L153-L162) (native source range).

<a id="api-5694dcb8c147dbd2"></a>

### `AlgebraicGeometry.Scheme.Modules.zeroIsTorsionFree`

```lean
instance AlgebraicGeometry.Scheme.Modules.zeroIsTorsionFree {X : Scheme} : IsTorsionFree 0
```

The zero module on a scheme is torsion-free.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleProperties.lean#L164-L166) (native source range).

<a id="api-f74739007dbd9c00"></a>

### `AlgebraicGeometry.Scheme.Modules.zeroVanishesAtGenericPoints`

```lean
instance AlgebraicGeometry.Scheme.Modules.zeroVanishesAtGenericPoints {X : Scheme} : VanishesAtGenericPoints 0
```

The zero module on a scheme vanishes at every component generic point.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleProperties.lean#L168-L171) (native source range).

<a id="api-b5dfe63f74131881"></a>

### `AlgebraicGeometry.Scheme.Modules.tilde_vanishesAtGenericPoints_iff_isTorsion`

```lean
theorem AlgebraicGeometry.Scheme.Modules.tilde_vanishesAtGenericPoints_iff_isTorsion {R : CommRingCat} [IsDomain ↑R] (P : ModuleCat ↑R) : (tilde P).VanishesAtGenericPoints ↔ Module.IsTorsion ↑R ↑P
```

For a module over an integral domain, its associated module on the affine
spectrum vanishes at the generic point exactly when the original module is
torsion.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleProperties.lean#L173-L215) (native source range).

<a id="api-fb04beeb8b91eae7"></a>

### `AlgebraicGeometry.Scheme.Modules.tilde_vanishesAtGenericPoints_iff_subsingleton_fractionRing_tensorProduct`

```lean
theorem AlgebraicGeometry.Scheme.Modules.tilde_vanishesAtGenericPoints_iff_subsingleton_fractionRing_tensorProduct {R : CommRingCat} [IsDomain ↑R] (P : ModuleCat ↑R) : (tilde P).VanishesAtGenericPoints ↔ Subsingleton (TensorProduct (↑R) (FractionRing ↑R) ↑P)
```

For a module over an integral domain, its associated module on the affine
spectrum vanishes at the generic point exactly when its fraction-ring base
change is zero.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleProperties.lean#L217-L225) (native source range).


## SchemeProperties.ModuleTensor

<a id="api-8e6421f0b4a00ecc"></a>

### `AlgebraicGeometry.Scheme.Modules.pointwiseMonoidalCategoryStruct`

```lean
noncomputable def AlgebraicGeometry.Scheme.Modules.pointwiseMonoidalCategoryStruct (X : Scheme) : CategoryTheory.MonoidalCategoryStruct X.PresheafOfModules
```

The pointwise monoidal tensor structure on presheaves of modules, used
locally to define the ambient sheaf tensor product.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensor.lean#L34-L38) (native source range).

<a id="api-b274e6c533256b51"></a>

### `AlgebraicGeometry.Scheme.Modules.pointwiseMonoidalCategory`

```lean
noncomputable def AlgebraicGeometry.Scheme.Modules.pointwiseMonoidalCategory (X : Scheme) : CategoryTheory.MonoidalCategory X.PresheafOfModules
```

The pointwise monoidal category on presheaves of modules; its instance
scope is confined to this module.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensor.lean#L40-L44) (native source range).

<a id="api-3a240690627995fd"></a>

### `AlgebraicGeometry.Scheme.Modules.pointwiseSymmetricCategory`

```lean
noncomputable def AlgebraicGeometry.Scheme.Modules.pointwiseSymmetricCategory (X : Scheme) : CategoryTheory.SymmetricCategory X.PresheafOfModules
```

The pointwise symmetric structure on presheaves of modules, registered
locally for the tensor bifunctor and its symmetry.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensor.lean#L46-L50) (native source range).

<a id="api-aee925729455a4db"></a>

### `AlgebraicGeometry.Scheme.Modules.tensorFunctor`

```lean
noncomputable def AlgebraicGeometry.Scheme.Modules.tensorFunctor (X : Scheme) : CategoryTheory.Functor (X.Modules × X.Modules) X.Modules
```

The ambient tensor bifunctor on modules over `X`, obtained by pointwise
presheaf tensor followed by sheafification.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensor.lean#L52-L65) (native source range).

<a id="api-3be40cb6015090de"></a>

### `AlgebraicGeometry.Scheme.Modules.tensor`

```lean
noncomputable def AlgebraicGeometry.Scheme.Modules.tensor {X : Scheme} (M N : X.Modules) : X.Modules
```

The ambient tensor product of two modules on a scheme.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensor.lean#L74-L77) (native source range).

<a id="api-4d494ddc916bade1"></a>

### `AlgebraicGeometry.Scheme.Modules.tensorFunctor_obj`

```lean
theorem AlgebraicGeometry.Scheme.Modules.tensorFunctor_obj {X : Scheme} (M N : X.Modules) : (tensorFunctor X).obj (M, N) = M.tensor N
```

The tensor bifunctor evaluates to `tensor`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensor.lean#L79-L81) (native source range).

<a id="api-8c061f4b26587b69"></a>

### `AlgebraicGeometry.Scheme.Modules.tensorUnit`

```lean
noncomputable def AlgebraicGeometry.Scheme.Modules.tensorUnit {X : Scheme} (M N : X.Modules) : CategoryTheory.MonoidalCategoryStruct.tensorObj M.val N.val ⟶ (M.tensor N).val
```

The sheafification-unit morphism from the pointwise presheaf tensor to the
underlying presheaf of the ambient tensor product.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensor.lean#L83-L89) (native source range).

<a id="api-5fe8b91ff9416af9"></a>

### `AlgebraicGeometry.Scheme.Modules.tmul`

```lean
noncomputable def AlgebraicGeometry.Scheme.Modules.tmul {X : Scheme} (M N : X.Modules) (U : X.Opens) (s : ↑(M.presheaf.obj (Opposite.op U))) (t : ↑(N.presheaf.obj (Opposite.op U))) : ↑((M.tensor N).presheaf.obj (Opposite.op U))
```

The pure tensor of two sections over the same open.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensor.lean#L91-L96) (native source range).

<a id="api-4d6216248686d568"></a>

### `AlgebraicGeometry.Scheme.Modules.tensorUnit_app_tmul`

```lean
theorem AlgebraicGeometry.Scheme.Modules.tensorUnit_app_tmul {X : Scheme} (M N : X.Modules) (U : X.Opens) (s : ↑(M.presheaf.obj (Opposite.op U))) (t : ↑(N.presheaf.obj (Opposite.op U))) : (ModuleCat.Hom.hom ((M.tensorUnit N).app (Opposite.op U))) (s ⊗ₜ[↑(X.sheaf.obj.obj (Opposite.op U))] t) = M.tmul N U s t
```

The pointwise sheafification unit sends an algebraic pure tensor to `tmul`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensor.lean#L98-L102) (native source range).

<a id="api-0e7939f2c76f35b2"></a>

### `AlgebraicGeometry.Scheme.Modules.zero_tmul`

```lean
theorem AlgebraicGeometry.Scheme.Modules.zero_tmul {X : Scheme} (M N : X.Modules) (U : X.Opens) (t : ↑(N.presheaf.obj (Opposite.op U))) : M.tmul N U 0 t = 0
```

A pure tensor with zero on the left is zero.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensor.lean#L104-L108) (native source range).

<a id="api-54231bd77a066e0e"></a>

### `AlgebraicGeometry.Scheme.Modules.tmul_zero`

```lean
theorem AlgebraicGeometry.Scheme.Modules.tmul_zero {X : Scheme} (M N : X.Modules) (U : X.Opens) (s : ↑(M.presheaf.obj (Opposite.op U))) : M.tmul N U s 0 = 0
```

A pure tensor with zero on the right is zero.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensor.lean#L110-L114) (native source range).

<a id="api-a9d03cabb4bbd3b1"></a>

### `AlgebraicGeometry.Scheme.Modules.add_tmul`

```lean
theorem AlgebraicGeometry.Scheme.Modules.add_tmul {X : Scheme} (M N : X.Modules) (U : X.Opens) (s s' : ↑(M.presheaf.obj (Opposite.op U))) (t : ↑(N.presheaf.obj (Opposite.op U))) : M.tmul N U (s + s') t = M.tmul N U s t + M.tmul N U s' t
```

Pure tensors are additive in the left variable.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensor.lean#L116-L121) (native source range).

<a id="api-2780bfc53db139f9"></a>

### `AlgebraicGeometry.Scheme.Modules.tmul_add`

```lean
theorem AlgebraicGeometry.Scheme.Modules.tmul_add {X : Scheme} (M N : X.Modules) (U : X.Opens) (s : ↑(M.presheaf.obj (Opposite.op U))) (t t' : ↑(N.presheaf.obj (Opposite.op U))) : M.tmul N U s (t + t') = M.tmul N U s t + M.tmul N U s t'
```

Pure tensors are additive in the right variable.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensor.lean#L123-L128) (native source range).

<a id="api-da2b7a93306d5cf6"></a>

### `AlgebraicGeometry.Scheme.Modules.smul_tmul`

```lean
theorem AlgebraicGeometry.Scheme.Modules.smul_tmul {X : Scheme} (M N : X.Modules) (U : X.Opens) (r : ↑(X.presheaf.obj (Opposite.op U))) (s : ↑(M.presheaf.obj (Opposite.op U))) (t : ↑(N.presheaf.obj (Opposite.op U))) : M.tmul N U (r • s) t = r • M.tmul N U s t
```

Scalars may be applied to the left factor of a pure tensor.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensor.lean#L130-L145) (native source range).

<a id="api-763a9bd17aaad8a2"></a>

### `AlgebraicGeometry.Scheme.Modules.tmul_smul`

```lean
theorem AlgebraicGeometry.Scheme.Modules.tmul_smul {X : Scheme} (M N : X.Modules) (U : X.Opens) (r : ↑(X.presheaf.obj (Opposite.op U))) (s : ↑(M.presheaf.obj (Opposite.op U))) (t : ↑(N.presheaf.obj (Opposite.op U))) : M.tmul N U s (r • t) = r • M.tmul N U s t
```

Scalars may be applied to the right factor of a pure tensor.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensor.lean#L147-L162) (native source range).

<a id="api-5d51b11d3b478307"></a>

### `AlgebraicGeometry.Scheme.Modules.map_tmul`

```lean
theorem AlgebraicGeometry.Scheme.Modules.map_tmul {X : Scheme} (M N : X.Modules) {U V : X.Opens} (i : U ⟶ V) (s : ↑(M.presheaf.obj (Opposite.op V))) (t : ↑(N.presheaf.obj (Opposite.op V))) : (CategoryTheory.ConcreteCategory.hom ((M.tensor N).presheaf.map i.op)) (M.tmul N V s t) = M.tmul N U ((CategoryTheory.ConcreteCategory.hom (M.presheaf.map i.op)) s) ((CategoryTheory.ConcreteCategory.hom (N.presheaf.map i.op)) t)
```

Restriction of sections commutes with pure tensors.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensor.lean#L164-L173) (native source range).

<a id="api-8040b993f1ea91a5"></a>

### `AlgebraicGeometry.Scheme.Modules.tensorHomEquiv`

```lean
noncomputable def AlgebraicGeometry.Scheme.Modules.tensorHomEquiv {X : Scheme} (M N P : X.Modules) : (M.tensor N ⟶ P) ≃ (CategoryTheory.MonoidalCategoryStruct.tensorObj M.val N.val ⟶ (PresheafOfModules.restrictScalars (CategoryTheory.CategoryStruct.id X.ringCatSheaf.obj)).obj P.val)
```

The sheafification universal property for the ambient tensor product, with
the exact presheaf-morphism codomain of `sheafificationHomEquiv`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensor.lean#L175-L182) (native source range).

<a id="api-4566c4b632b14ea0"></a>

### `AlgebraicGeometry.Scheme.Modules.tensorHomEquiv_apply`

```lean
theorem AlgebraicGeometry.Scheme.Modules.tensorHomEquiv_apply {X : Scheme} (M N P : X.Modules) (f : M.tensor N ⟶ P) : (M.tensorHomEquiv N P) f = CategoryTheory.CategoryStruct.comp (M.tensorUnit N) (((SheafOfModules.forget X.ringCatSheaf).comp (PresheafOfModules.restrictScalars (CategoryTheory.CategoryStruct.id X.ringCatSheaf.obj))).map f)
```

The Hom equivalence sends a morphism to the unit followed by its underlying
presheaf morphism.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensor.lean#L184-L194) (native source range).

<a id="api-c3175837d07cd81d"></a>

### `AlgebraicGeometry.Scheme.Modules.tensorHomEquiv_symm_apply_apply`

```lean
theorem AlgebraicGeometry.Scheme.Modules.tensorHomEquiv_symm_apply_apply {X : Scheme} (M N P : X.Modules) (g : CategoryTheory.MonoidalCategoryStruct.tensorObj M.val N.val ⟶ (PresheafOfModules.restrictScalars (CategoryTheory.CategoryStruct.id X.ringCatSheaf.obj)).obj P.val) : (M.tensorHomEquiv N P) ((M.tensorHomEquiv N P).symm g) = g
```

Applying the Hom equivalence after its inverse returns the original
presheaf morphism.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensor.lean#L196-L202) (native source range).

<a id="api-604bbd004d72ff87"></a>

### `AlgebraicGeometry.Scheme.Modules.tensorHomEquiv_apply_symm_apply`

```lean
theorem AlgebraicGeometry.Scheme.Modules.tensorHomEquiv_apply_symm_apply {X : Scheme} (M N P : X.Modules) (f : M.tensor N ⟶ P) : (M.tensorHomEquiv N P).symm ((M.tensorHomEquiv N P) f) = f
```

Applying the inverse Hom equivalence after the Hom equivalence returns the
original sheaf morphism.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensor.lean#L204-L209) (native source range).

<a id="api-b73eab73af0604f7"></a>

### `AlgebraicGeometry.Scheme.Modules.tensorHomEquiv_app_tmul`

```lean
theorem AlgebraicGeometry.Scheme.Modules.tensorHomEquiv_app_tmul {X : Scheme} (M N P : X.Modules) (f : M.tensor N ⟶ P) (U : X.Opens) (s : ↑(M.presheaf.obj (Opposite.op U))) (t : ↑(N.presheaf.obj (Opposite.op U))) : (ModuleCat.Hom.hom (((M.tensorHomEquiv N P) f).app (Opposite.op U))) (s ⊗ₜ[↑(X.sheaf.obj.obj (Opposite.op U))] t) = (CategoryTheory.ConcreteCategory.hom (Hom.app f U)) (M.tmul N U s t)
```

The presheaf morphism corresponding to a sheaf morphism acts on a pure
tensor by first forming `tmul`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensor.lean#L211-L219) (native source range).

<a id="api-c8d26faa5d9719a0"></a>

### `AlgebraicGeometry.Scheme.Modules.tensorHomEquiv_symm_app_tmul`

```lean
theorem AlgebraicGeometry.Scheme.Modules.tensorHomEquiv_symm_app_tmul {X : Scheme} (M N P : X.Modules) (g : CategoryTheory.MonoidalCategoryStruct.tensorObj M.val N.val ⟶ (PresheafOfModules.restrictScalars (CategoryTheory.CategoryStruct.id X.ringCatSheaf.obj)).obj P.val) (U : X.Opens) (s : ↑(M.presheaf.obj (Opposite.op U))) (t : ↑(N.presheaf.obj (Opposite.op U))) : (CategoryTheory.ConcreteCategory.hom (Hom.app ((M.tensorHomEquiv N P).symm g) U)) (M.tmul N U s t) = (ModuleCat.Hom.hom (g.app (Opposite.op U))) (s ⊗ₜ[↑(X.sheaf.obj.obj (Opposite.op U))] t)
```

The inverse Hom equivalence acts on `tmul` by the supplied presheaf
morphism's action on the algebraic pure tensor.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensor.lean#L221-L229) (native source range).

<a id="api-821eed53337c8bf3"></a>

### `AlgebraicGeometry.Scheme.Modules.tensorFunctor_map_app_tmul`

```lean
theorem AlgebraicGeometry.Scheme.Modules.tensorFunctor_map_app_tmul {X : Scheme} {M N M' N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N') (U : X.Opens) (s : ↑(M.presheaf.obj (Opposite.op U))) (t : ↑(N.presheaf.obj (Opposite.op U))) : (CategoryTheory.ConcreteCategory.hom (Hom.app ((tensorFunctor X).map (f, g)) U)) (M.tmul N U s t) = M'.tmul N' U ((CategoryTheory.ConcreteCategory.hom (Hom.app f U)) s) ((CategoryTheory.ConcreteCategory.hom (Hom.app g U)) t)
```

The tensor bifunctor applies a pair of morphisms factorwise to pure
tensors.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensor.lean#L231-L266) (native source range).

<a id="api-f0c5f9f026d4ded2"></a>

### `AlgebraicGeometry.Scheme.Modules.tensorSymm`

```lean
noncomputable def AlgebraicGeometry.Scheme.Modules.tensorSymm {X : Scheme} (M N : X.Modules) : M.tensor N ≅ N.tensor M
```

The canonical symmetry isomorphism for the ambient tensor product.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensor.lean#L268-L272) (native source range).

<a id="api-849fe575b6340c90"></a>

### `AlgebraicGeometry.Scheme.Modules.tensorSymm_hom_app_tmul`

```lean
theorem AlgebraicGeometry.Scheme.Modules.tensorSymm_hom_app_tmul {X : Scheme} (M N : X.Modules) (U : X.Opens) (s : ↑(M.presheaf.obj (Opposite.op U))) (t : ↑(N.presheaf.obj (Opposite.op U))) : (CategoryTheory.ConcreteCategory.hom (Hom.app (M.tensorSymm N).hom U)) (M.tmul N U s t) = N.tmul M U t s
```

The symmetry isomorphism exchanges the factors of a pure tensor.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensor.lean#L274-L314) (native source range).

<a id="api-51f0003c1386d8b8"></a>

### `AlgebraicGeometry.Scheme.Modules.tensorSymm_naturality`

```lean
theorem AlgebraicGeometry.Scheme.Modules.tensorSymm_naturality {X : Scheme} {M N M' N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N') : CategoryTheory.CategoryStruct.comp ((tensorFunctor X).map (f, g)) (M'.tensorSymm N').hom = CategoryTheory.CategoryStruct.comp (M.tensorSymm N).hom ((tensorFunctor X).map (g, f))
```

The symmetry is natural with respect to the tensor bifunctor.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensor.lean#L316-L329) (native source range).


## SchemeProperties.ModuleTensorAffine

<a id="api-0b00fe8fea65df7a"></a>

### `AlgebraicGeometry.Scheme.Modules.affineTensorNatIso`

```lean
noncomputable def AlgebraicGeometry.Scheme.Modules.affineTensorNatIso (R : CommRingCat) : ((tilde.functor R).prod (tilde.functor R)).comp (tensorFunctor (Spec R)) ≅ (CategoryTheory.MonoidalCategory.tensor (ModuleCat ↑R)).comp (tilde.functor R)
```

On an affine scheme, tensoring the associated sheaves agrees naturally with
associating a sheaf to the tensor product of modules. This compares with the
existing sheafified presheaf tensor, for arbitrary modules and any commutative ring.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorAffine.lean#L706-L712) (native source range).

<a id="api-a5b024ca1c92b464"></a>

### `AlgebraicGeometry.Scheme.Modules.affineTensorNatIso_inv_app_top_tmul`

```lean
theorem AlgebraicGeometry.Scheme.Modules.affineTensorNatIso_inv_app_top_tmul (R : CommRingCat) (M N : ModuleCat ↑R) (m : ↑M) (n : ↑N) : (CategoryTheory.ConcreteCategory.hom (Hom.app ((affineTensorNatIso R).inv.app (M, N)) ⊤)) ((ModuleCat.Hom.hom (tilde.toOpen (CategoryTheory.MonoidalCategoryStruct.tensorObj M N) ⊤)) (m ⊗ₜ[↑R] n)) = (tilde M).tmul (tilde N) ⊤ ((ModuleCat.Hom.hom (tilde.toOpen M ⊤)) m) ((ModuleCat.Hom.hom (tilde.toOpen N ⊤)) n)
```

On global pure tensors, the inverse affine comparison is the tensor of the
corresponding top-open sections.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorAffine.lean#L714-L721) (native source range).


## SchemeProperties.ModuleTensorLocalization

<a id="api-7423209fccc12c80"></a>

### `AlgebraicGeometry.Scheme.Modules.locTensor`

```lean
noncomputable def AlgebraicGeometry.Scheme.Modules.locTensor (R : CommRingCat) (M N : ModuleCat ↑R) (f : ↑R) : TensorProduct ↑R ↑M ↑N →ₗ[↑R] TensorProduct ↑((Spec R).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen f))) ↑((tilde M).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen f))) ↑((tilde N).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen f)))
```

The canonical `R`-linear localization map from `M ⊗[R] N` to the tensor of
associated-module sections over `Γ(Spec R, D(f))`. It uses native module
localization rather than a chosen inverse of the sheaf-tensor comparison.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L76-L88) (native source range).

<a id="api-1445b23fe97ead74"></a>

### `AlgebraicGeometry.Scheme.Modules.locTensor_tmul`

```lean
theorem AlgebraicGeometry.Scheme.Modules.locTensor_tmul (R : CommRingCat) (M N : ModuleCat ↑R) (f : ↑R) (m : ↑M) (n : ↑N) : (locTensor R M N f) (m ⊗ₜ[↑R] n) = (ModuleCat.Hom.hom (tilde.toOpen M (PrimeSpectrum.basicOpen f))) m ⊗ₜ[↑((Spec R).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen f)))] (ModuleCat.Hom.hom (tilde.toOpen N (PrimeSpectrum.basicOpen f))) n
```

**API note (not a source docstring):** The generator formula `AlgebraicGeometry.Scheme.Modules.locTensor_tmul` says `locTensor R M N f` sends `m ⊗ₜ[R] n` to the tensor, over `Γ(Spec R,D(f))`, of the canonical `tilde M` and `tilde N` sections induced by `m` and `n` on `D(f)`. The ambient map is `R`-linear; this result addresses principal-open localization of affine associated modules.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L90-L97) (native source range).

<a id="api-0bfc87b4ca2fc854"></a>

### `AlgebraicGeometry.Scheme.Modules.locTensor_isLocalized`

```lean
theorem AlgebraicGeometry.Scheme.Modules.locTensor_isLocalized (R : CommRingCat) (M N : ModuleCat ↑R) (f : ↑R) : IsLocalizedModule (Submonoid.powers f) (locTensor R M N f)
```

The native section tensor is a localization of `M ⊗[R] N` at powers of
`f`, establishing the universal-property uniqueness of `locTensor`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L99-L106) (native source range).

<a id="api-69550bf32373b33b"></a>

### `AlgebraicGeometry.Scheme.Modules.tensorUnit_basicOpen_isIso`

```lean
theorem AlgebraicGeometry.Scheme.Modules.tensorUnit_basicOpen_isIso (R : CommRingCat) (M N : ModuleCat ↑R) (f : ↑R) : CategoryTheory.IsIso (((tilde M).tensorUnit (tilde N)).app (Opposite.op (PrimeSpectrum.basicOpen f)))
```

**API note (not a source docstring):** The instance-level theorem `AlgebraicGeometry.Scheme.Modules.tensorUnit_basicOpen_isIso` says the component of the sheafification tensor-unit map at `D(f)` is an isomorphism for `tilde M` and `tilde N` on `Spec R`. It obtains bijectivity via the affine tensor comparison and the localization universal property; the hypothesis is this affine associated-module situation, not arbitrary modules or arbitrary opens.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L152-L164) (native source range).

<a id="api-d6fb265f087d7290"></a>

### `AlgebraicGeometry.Scheme.Modules.basicTensorEquiv`

```lean
noncomputable def AlgebraicGeometry.Scheme.Modules.basicTensorEquiv (R : CommRingCat) (M N : ModuleCat ↑R) (f : ↑R) : TensorProduct ↑((Spec R).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen f))) ↑((tilde M).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen f))) ↑((tilde N).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen f))) ≃ₗ[↑((Spec R).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen f)))] ↑(((tilde M).tensor (tilde N)).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen f)))
```

The canonical equivalence whose forward map **is** the actual `tensorUnit`
component at `D(f)`, over the native section ring `Γ(Spec R, D(f))`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L166-L175) (native source range).

<a id="api-f6329d18b0c623a5"></a>

### `AlgebraicGeometry.Scheme.Modules.basicTensorEquiv_tmul`

```lean
theorem AlgebraicGeometry.Scheme.Modules.basicTensorEquiv_tmul (R : CommRingCat) (M N : ModuleCat ↑R) (f : ↑R) (m : ↑((tilde M).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen f)))) (n : ↑((tilde N).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen f)))) : (basicTensorEquiv R M N f) (m ⊗ₜ[↑((Spec R).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen f)))] n) = (tilde M).tmul (tilde N) (PrimeSpectrum.basicOpen f) m n
```

The forward basic-open equivalence sends pure section tensors by the
actual `tensorUnit` component, not by an independently chosen comparison.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L177-L187) (native source range).

<a id="api-e83c2f29ff50aa45"></a>

### `AlgebraicGeometry.Scheme.Modules.topTensorEquiv`

```lean
noncomputable def AlgebraicGeometry.Scheme.Modules.topTensorEquiv (R : CommRingCat) (M N : ModuleCat ↑R) : ↑(((tilde M).tensor (tilde N)).presheaf.obj (Opposite.op ⊤)) ≃ₗ[↑R] TensorProduct ↑R ↑M ↑N
```

The global affine tensor comparison, followed by the inverse of the actual
top-open `tilde.isoTop`; this takes sheaf-tensor sections to `M ⊗[R] N`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L189-L194) (native source range).

<a id="api-9b8a2211fb5354aa"></a>

### `AlgebraicGeometry.Scheme.Modules.resTop`

```lean
noncomputable def AlgebraicGeometry.Scheme.Modules.resTop (R : CommRingCat) (M N : ModuleCat ↑R) (f : ↑R) : ↑(((tilde M).tensor (tilde N)).presheaf.obj (Opposite.op ⊤)) →ₗ[↑R] ↑(((tilde M).tensor (tilde N)).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen f)))
```

Restriction of sheaf-tensor sections from `⊤` to `D(f)`, made `R`-linear
using the native `R`-action and `map_smul_Spec`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L196-L204) (native source range).

<a id="api-3b5df10daa77e8c6"></a>

### `AlgebraicGeometry.Scheme.Modules.topTensorEquiv_symm_tmul`

```lean
theorem AlgebraicGeometry.Scheme.Modules.topTensorEquiv_symm_tmul (R : CommRingCat) (M N : ModuleCat ↑R) (m : ↑M) (n : ↑N) : (topTensorEquiv R M N).symm (m ⊗ₜ[↑R] n) = (tilde M).tmul (tilde N) ⊤ ((ModuleCat.Hom.hom (tilde.toOpen M ⊤)) m) ((ModuleCat.Hom.hom (tilde.toOpen N ⊤)) n)
```

**API note (not a source docstring):** The generator formula `AlgebraicGeometry.Scheme.Modules.topTensorEquiv_symm_tmul` sends `m ⊗ₜ[R] n` through the inverse global affine equivalence `topTensorEquiv R M N` to the top-open pure section tensor of `tilde M` and `tilde N`. The proof uses the affine `tilde` tensor isomorphism on `Spec R`; it does not extend the formula to modules on an unrelated scheme.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L206-L210) (native source range).

<a id="api-223a86e742dd8946"></a>

### `AlgebraicGeometry.Scheme.Modules.basicTensorEquiv_locTensor`

```lean
theorem AlgebraicGeometry.Scheme.Modules.basicTensorEquiv_locTensor (R : CommRingCat) (M N : ModuleCat ↑R) (f : ↑R) (m : ↑M) (n : ↑N) : (basicTensorEquiv R M N f) ((locTensor R M N f) (m ⊗ₜ[↑R] n)) = (tilde M).tmul (tilde N) (PrimeSpectrum.basicOpen f) ((ModuleCat.Hom.hom (tilde.toOpen M (PrimeSpectrum.basicOpen f))) m) ((ModuleCat.Hom.hom (tilde.toOpen N (PrimeSpectrum.basicOpen f))) n)
```

**API note (not a source docstring):** The compatibility equation `AlgebraicGeometry.Scheme.Modules.basicTensorEquiv_locTensor` evaluates the basic-open tensor equivalence on `locTensor` of a pure `R`-tensor `m ⊗ n`. It yields the native pure sheaf-tensor section on `D(f)` formed from `(tilde.toOpen M D(f)) m` and `(tilde.toOpen N D(f)) n`. This is specific to associated modules over the affine spectrum and its principal open.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L212-L217) (native source range).

<a id="api-222e5d010a2d2a5a"></a>

### `AlgebraicGeometry.Scheme.Modules.actual_restriction_square`

```lean
theorem AlgebraicGeometry.Scheme.Modules.actual_restriction_square (R : CommRingCat) (M N : ModuleCat ↑R) (f : ↑R) : ↑↑R ↑(basicTensorEquiv R M N f).symm ∘ₗ resTop R M N f = locTensor R M N f ∘ₗ ↑(topTensorEquiv R M N)
```

Equality of **actual** `R`-linear maps: inverse tensor-unit equivalence
after top-to-`D(f)` restriction equals native module localization after the
accepted top-open affine comparison.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L240-L252) (native source range).

<a id="api-150db665d3404b2b"></a>

### `AlgebraicGeometry.Scheme.Modules.sectionTensorRes`

```lean
noncomputable def AlgebraicGeometry.Scheme.Modules.sectionTensorRes (R : CommRingCat) (M N : ModuleCat ↑R) {U V : (Spec R).Opens} (i : U ⟶ V) : TensorProduct ↑((Spec R).presheaf.obj (Opposite.op V)) ↑((tilde M).presheaf.obj (Opposite.op V)) ↑((tilde N).presheaf.obj (Opposite.op V)) →ₛₗ[CommRingCat.Hom.hom ((Spec R).presheaf.map i.op)] TensorProduct ↑((Spec R).presheaf.obj (Opposite.op U)) ↑((tilde M).presheaf.obj (Opposite.op U)) ↑((tilde N).presheaf.obj (Opposite.op U))
```

Tensor restriction from `V` to `U` is semilinear along the actual
structure-sheaf map `Γ(Spec R, V) → Γ(Spec R, U)`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L254-L262) (native source range).

<a id="api-91385b8535a42e7d"></a>

### `AlgebraicGeometry.Scheme.Modules.sectionTensorRes_tmul`

```lean
theorem AlgebraicGeometry.Scheme.Modules.sectionTensorRes_tmul (R : CommRingCat) (M N : ModuleCat ↑R) {U V : (Spec R).Opens} (i : U ⟶ V) (m : ↑((tilde M).presheaf.obj (Opposite.op V))) (n : ↑((tilde N).presheaf.obj (Opposite.op V))) : (sectionTensorRes R M N i) (m ⊗ₜ[↑((Spec R).presheaf.obj (Opposite.op V))] n) = (CategoryTheory.ConcreteCategory.hom ((tilde M).presheaf.map i.op)) m ⊗ₜ[↑((Spec R).presheaf.obj (Opposite.op U))] (CategoryTheory.ConcreteCategory.hom ((tilde N).presheaf.map i.op)) n
```

**API note (not a source docstring):** The generator rule `AlgebraicGeometry.Scheme.Modules.sectionTensorRes_tmul` for an inclusion `U ⊆ V` of affine-spectrum opens sends the pure tensor of sections `m ⊗ n` over `Γ(Spec R,V)` to the tensor of their separate restrictions over `Γ(Spec R,U)`. Its map is semilinear along the actual structure-sheaf restriction, and the formula concerns the tensor of sections, not an arbitrary-open sheaf-tensor equivalence.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L264-L268) (native source range).

<a id="api-b5b98464632131e5"></a>

### `AlgebraicGeometry.Scheme.Modules.basicTensorEquiv_restriction`

```lean
theorem AlgebraicGeometry.Scheme.Modules.basicTensorEquiv_restriction (R : CommRingCat) (M N : ModuleCat ↑R) {f g : ↑R} (i : PrimeSpectrum.basicOpen g ⟶ PrimeSpectrum.basicOpen f) (x : TensorProduct ↑((Spec R).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen f))) ↑((tilde M).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen f))) ↑((tilde N).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen f)))) : (basicTensorEquiv R M N g) ((sectionTensorRes R M N i) x) = (CategoryTheory.ConcreteCategory.hom (((tilde M).tensor (tilde N)).presheaf.map i.op)) ((basicTensorEquiv R M N f) x)
```

The actual tensor-unit equivalence commutes with *every* inclusion
`D(g) ≤ D(f)`, not only multiplication or divisibility inclusions.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L270-L279) (native source range).

<a id="api-5ec783b0c22dadbf"></a>

### `AlgebraicGeometry.Scheme.Modules.basicTensorEquiv_symm_restriction`

```lean
theorem AlgebraicGeometry.Scheme.Modules.basicTensorEquiv_symm_restriction (R : CommRingCat) (M N : ModuleCat ↑R) {f g : ↑R} (i : PrimeSpectrum.basicOpen g ⟶ PrimeSpectrum.basicOpen f) (x : ↑(((tilde M).tensor (tilde N)).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen f)))) : (basicTensorEquiv R M N g).symm ((CategoryTheory.ConcreteCategory.hom (((tilde M).tensor (tilde N)).presheaf.map i.op)) x) = (sectionTensorRes R M N i) ((basicTensorEquiv R M N f).symm x)
```

**API note (not a source docstring):** For an inclusion `D(g) ⊆ D(f)` and a tensor-sheaf section on `D(f)`, `AlgebraicGeometry.Scheme.Modules.basicTensorEquiv_symm_restriction` says applying the inverse basic-open comparison after sheaf restriction equals first applying the inverse comparison on `D(f)` and then semilinearly restricting the tensor of associated-module sections. It is the inverse counterpart of naturality of `tensorUnit` on principal opens.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L281-L289) (native source range).

<a id="api-fd95c33486babc28"></a>

### `AlgebraicGeometry.Scheme.Modules.sectionTensorRes_id`

```lean
theorem AlgebraicGeometry.Scheme.Modules.sectionTensorRes_id (R : CommRingCat) (M N : ModuleCat ↑R) (U : (Spec R).Opens) (x : TensorProduct ↑((Spec R).presheaf.obj (Opposite.op U)) ↑((tilde M).presheaf.obj (Opposite.op U)) ↑((tilde N).presheaf.obj (Opposite.op U))) : (sectionTensorRes R M N (CategoryTheory.CategoryStruct.id U)) x = x
```

**API note (not a source docstring):** The identity law `AlgebraicGeometry.Scheme.Modules.sectionTensorRes_id` says semilinear restriction of a tensor of `tilde M,tilde N` sections along the identity of any open `U` of `Spec R` fixes every tensor section. Its source owner `ModuleTensorLocalization` defines `sectionTensorRes` using the pointwise tensor presheaf; this law does not identify that presheaf with a tensor sheaf on every open.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L291-L296) (native source range).

<a id="api-a5d081774712d73d"></a>

### `AlgebraicGeometry.Scheme.Modules.sectionTensorRes_comp`

```lean
theorem AlgebraicGeometry.Scheme.Modules.sectionTensorRes_comp (R : CommRingCat) (M N : ModuleCat ↑R) {U V W : (Spec R).Opens} (i : U ⟶ V) (j : V ⟶ W) (x : TensorProduct ↑((Spec R).presheaf.obj (Opposite.op W)) ↑((tilde M).presheaf.obj (Opposite.op W)) ↑((tilde N).presheaf.obj (Opposite.op W))) : (sectionTensorRes R M N (CategoryTheory.CategoryStruct.comp i j)) x = (sectionTensorRes R M N i) ((sectionTensorRes R M N j) x)
```

**API note (not a source docstring):** For composable inclusions of opens `U → V → W` in `Spec R`, `AlgebraicGeometry.Scheme.Modules.sectionTensorRes_comp` equates restriction of a tensor of associated-module sections from `W` directly to `U` with restriction via `V`. This is functoriality of the semilinear tensor-section restriction map on arbitrary opens; it is not a claim that `basicTensorEquiv` exists on all such opens.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L298-L304) (native source range).

<a id="api-da8fef5ec568cee4"></a>

### `AlgebraicGeometry.Scheme.Modules.sectionTensorRes_locTensor`

```lean
theorem AlgebraicGeometry.Scheme.Modules.sectionTensorRes_locTensor (R : CommRingCat) (M N : ModuleCat ↑R) {f g : ↑R} (i : PrimeSpectrum.basicOpen g ⟶ PrimeSpectrum.basicOpen f) (m : ↑M) (n : ↑N) : (sectionTensorRes R M N i) ((locTensor R M N f) (m ⊗ₜ[↑R] n)) = (locTensor R M N g) (m ⊗ₜ[↑R] n)
```

**API note (not a source docstring):** The pure-tensor rule `AlgebraicGeometry.Scheme.Modules.sectionTensorRes_locTensor` says that restricting `locTensor R M N f (m ⊗ₜ[R] n)` from `D(f)` to an included `D(g)` agrees with localizing the same pure tensor directly at `g`. It relies on the natural restriction maps for `tilde M` and `tilde N` and does not require divisibility of `f` and `g` beyond the specified open inclusion.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L306-L319) (native source range).

<a id="api-f62048ae4ea7a318"></a>

### `AlgebraicGeometry.Scheme.Modules.sectionTensorRes_locTensor_apply`

```lean
theorem AlgebraicGeometry.Scheme.Modules.sectionTensorRes_locTensor_apply (R : CommRingCat) (M N : ModuleCat ↑R) {f g : ↑R} (i : PrimeSpectrum.basicOpen g ⟶ PrimeSpectrum.basicOpen f) (x : TensorProduct ↑R ↑M ↑N) : (sectionTensorRes R M N i) ((locTensor R M N f) x) = (locTensor R M N g) x
```

**API note (not a source docstring):** For every `x : M ⊗[R] N` and inclusion `D(g) ⊆ D(f)`, `AlgebraicGeometry.Scheme.Modules.sectionTensorRes_locTensor_apply` says restricting `locTensor R M N f x` along that inclusion gives `locTensor R M N g x`. This extends the earlier pure-tensor rule by tensor-product induction, with the tensor of sections taken over each principal open's own structure-sheaf ring.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L321-L327) (native source range).

<a id="api-0502c21dfbdc9fdf"></a>

### `AlgebraicGeometry.Scheme.Modules.basicTensorEquiv_restriction_square`

```lean
theorem AlgebraicGeometry.Scheme.Modules.basicTensorEquiv_restriction_square (R : CommRingCat) (M N : ModuleCat ↑R) {f g : ↑R} (i : PrimeSpectrum.basicOpen g ⟶ PrimeSpectrum.basicOpen f) : ↑(basicTensorEquiv R M N g).symm ∘ₛₗ ((tilde M).tensor (tilde N)).val.restrictₛₗ i.op = sectionTensorRes R M N i ∘ₛₗ ↑(basicTensorEquiv R M N f).symm
```

**API note (not a source docstring):** The map equality `AlgebraicGeometry.Scheme.Modules.basicTensorEquiv_restriction_square` states that for any inclusion `D(g) ⊆ D(f)`, restricting a tensor-sheaf section and then applying `basicTensorEquiv g` backward equals first applying `basicTensorEquiv f` backward and then the semilinear `sectionTensorRes`. The two composites have their native section-ring scalar map; it is the inverse-comparison square for these principal opens.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L329-L336) (native source range).

<a id="api-6ab699bdac444812"></a>

### `AlgebraicGeometry.Scheme.Modules.basicTensorEquiv_product_paths`

```lean
theorem AlgebraicGeometry.Scheme.Modules.basicTensorEquiv_product_paths (R : CommRingCat) (M N : ModuleCat ↑R) (f g : ↑R) (x : ↑(((tilde M).tensor (tilde N)).presheaf.obj (Opposite.op ⊤))) : (sectionTensorRes R M N (CategoryTheory.homOfLE ⋯)) ((basicTensorEquiv R M N f).symm ((resTop R M N f) x)) = (sectionTensorRes R M N (CategoryTheory.homOfLE ⋯)) ((basicTensorEquiv R M N g).symm ((resTop R M N g) x))
```

**API note (not a source docstring):** The compatibility rule `AlgebraicGeometry.Scheme.Modules.basicTensorEquiv_product_paths` starts with a top-open tensor-sheaf section, restricts separately to `D(f)` and `D(g)`, applies the inverse basic tensor comparisons, and then restricts both results to `D(fg)`; the resulting native section tensors agree. It uses the two principal-open inclusions and naturality, not an equivalence on arbitrary opens.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L338-L352) (native source range).

<a id="api-2c3ab6444c06b645"></a>

### `AlgebraicGeometry.Scheme.Modules.basicTensorEquiv_naturality`

```lean
theorem AlgebraicGeometry.Scheme.Modules.basicTensorEquiv_naturality (R : CommRingCat) (M N : ModuleCat ↑R) {M' N' : ModuleCat ↑R} (a : M ⟶ M') (b : N ⟶ N') (f : ↑R) (x : TensorProduct ↑((Spec R).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen f))) ↑((tilde M).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen f))) ↑((tilde N).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen f)))) : (basicTensorEquiv R M' N' f) ((TensorProduct.map (ModuleCat.Hom.hom ((tilde.map a).val.app (Opposite.op (PrimeSpectrum.basicOpen f)))) (ModuleCat.Hom.hom ((tilde.map b).val.app (Opposite.op (PrimeSpectrum.basicOpen f))))) x) = (CategoryTheory.ConcreteCategory.hom (Hom.app ((tensorFunctor (Spec R)).map (tilde.map a, tilde.map b)) (PrimeSpectrum.basicOpen f))) ((basicTensorEquiv R M N f) x)
```

The canonical basic-open comparison is natural in both module maps.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L354-L369) (native source range).

<a id="api-6689c4787ecfc9af"></a>

### `AlgebraicGeometry.Scheme.Modules.awayModuleEquiv`

```lean
noncomputable def AlgebraicGeometry.Scheme.Modules.awayModuleEquiv (R : CommRingCat) (L : ModuleCat ↑R) (f : ↑R) : LocalizedModule (Submonoid.powers f) ↑L ≃ₛₗ[(IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f) ↑((Spec R).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen f)))).toRingEquiv.toRingHom] ↑((tilde L).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen f)))
```

Canonical equivalence from the localized module over `Localization.Away f`
to native sections on `D(f)`. It is semilinear over the native
`IsLocalization.algEquiv` from `Away f` to `Γ(Spec R, D(f))`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L406-L443) (native source range).

<a id="api-67a719b8ec6c8e10"></a>

### `AlgebraicGeometry.Scheme.Modules.awayModuleEquiv_mk`

```lean
theorem AlgebraicGeometry.Scheme.Modules.awayModuleEquiv_mk (R : CommRingCat) (L : ModuleCat ↑R) (f : ↑R) (m : ↑L) : (awayModuleEquiv R L f) (LocalizedModule.mk m 1) = (ModuleCat.Hom.hom (tilde.toOpen L (PrimeSpectrum.basicOpen f))) m
```

**API note (not a source docstring):** For an `R`-module `L`, `AlgebraicGeometry.Scheme.Modules.awayModuleEquiv_mk` evaluates the semilinear equivalence from `L` localized at powers of `f` to sections of `tilde L` on `D(f)` at `LocalizedModule.mk m 1`. The image is the canonical section `(tilde.toOpen L D(f)).hom m`, with scalars transported from `Localization.Away f` to the native section ring.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L445-L449) (native source range).

<a id="api-f316ca4122898162"></a>

### `AlgebraicGeometry.Scheme.Modules.awayTensorEquiv`

```lean
noncomputable def AlgebraicGeometry.Scheme.Modules.awayTensorEquiv (R : CommRingCat) (M N : ModuleCat ↑R) (f : ↑R) : TensorProduct (Localization.Away f) (LocalizedModule (Submonoid.powers f) ↑M) (LocalizedModule (Submonoid.powers f) ↑N) ≃ₛₗ[(IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f) ↑((Spec R).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen f)))).toRingEquiv.toRingHom] TensorProduct ↑((Spec R).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen f))) ↑((tilde M).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen f))) ↑((tilde N).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen f)))
```

The semilinear comparison from the tensor of explicit localized modules
over `Localization.Away f` to the tensor of native sections over
`Γ(Spec R, D(f))`, along the native `IsLocalization.algEquiv`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L451-L479) (native source range).

<a id="api-a5436d1ce7c6a564"></a>

### `AlgebraicGeometry.Scheme.Modules.awayTensorEquiv_mk_tmul`

```lean
theorem AlgebraicGeometry.Scheme.Modules.awayTensorEquiv_mk_tmul (R : CommRingCat) (M N : ModuleCat ↑R) (f : ↑R) (m : ↑M) (n : ↑N) : (awayTensorEquiv R M N f) (LocalizedModule.mk m 1 ⊗ₜ[Localization.Away f] LocalizedModule.mk n 1) = (locTensor R M N f) (m ⊗ₜ[↑R] n)
```

**API note (not a source docstring):** Under the semilinear `awayTensorEquiv` comparing explicit `Away f` tensors to tensors of associated-module sections on `D(f)`, `AlgebraicGeometry.Scheme.Modules.awayTensorEquiv_mk_tmul` sends `mk m 1 ⊗ mk n 1` to `locTensor R M N f (m ⊗ₜ[R] n)`. The proof uses the `awayModuleEquiv_mk` and `locTensor_tmul` generator formulas over the affine spectrum of `R`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L481-L487) (native source range).

<a id="api-b368adcaf53912a5"></a>

### `AlgebraicGeometry.Scheme.Modules.awayLocTensor`

```lean
noncomputable def AlgebraicGeometry.Scheme.Modules.awayLocTensor (R : CommRingCat) (M N : ModuleCat ↑R) (f : ↑R) : TensorProduct ↑R ↑M ↑N →ₗ[↑R] TensorProduct (Localization.Away f) (LocalizedModule (Submonoid.powers f) ↑M) (LocalizedModule (Submonoid.powers f) ↑N)
```

Canonical `R`-linear tensor localization in the explicit `Away f`
presentation, built from native `LocalizedModule.mkLinearMap` and
`IsLocalization.moduleTensorEquiv`, independently of the restriction square.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L489-L501) (native source range).

<a id="api-429b2f1a7ff7e856"></a>

### `AlgebraicGeometry.Scheme.Modules.awayLocTensor_tmul`

```lean
theorem AlgebraicGeometry.Scheme.Modules.awayLocTensor_tmul (R : CommRingCat) (M N : ModuleCat ↑R) (f : ↑R) (m : ↑M) (n : ↑N) : (awayLocTensor R M N f) (m ⊗ₜ[↑R] n) = LocalizedModule.mk m 1 ⊗ₜ[Localization.Away f] LocalizedModule.mk n 1
```

**API note (not a source docstring):** The generator rule `AlgebraicGeometry.Scheme.Modules.awayLocTensor_tmul` maps `m ⊗ₜ[R] n` under the canonical `R`-linear localization to `LocalizedModule.mk m 1 ⊗ₜ[Localization.Away f] LocalizedModule.mk n 1`. Its owner `ModuleTensorLocalization` uses the explicit away-localization of the two modules on the principal open `D(f)`; it is not a formula for arbitrary sheaf modules on an arbitrary scheme.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L503-L505) (native source range).

<a id="api-f407285ed032b996"></a>

### `AlgebraicGeometry.Scheme.Modules.awayLocTensor_isLocalized`

```lean
theorem AlgebraicGeometry.Scheme.Modules.awayLocTensor_isLocalized (R : CommRingCat) (M N : ModuleCat ↑R) (f : ↑R) : IsLocalizedModule (Submonoid.powers f) (awayLocTensor R M N f)
```

The explicit Away tensor localization has the native module-localization
universal property, in addition to its pure-tensor generator law.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L507-L514) (native source range).

<a id="api-08fd41f1c3d0e6ac"></a>

### `AlgebraicGeometry.Scheme.Modules.awayTensorEquiv_awayLocTensor`

```lean
theorem AlgebraicGeometry.Scheme.Modules.awayTensorEquiv_awayLocTensor (R : CommRingCat) (M N : ModuleCat ↑R) (f : ↑R) (x : TensorProduct ↑R ↑M ↑N) : (awayTensorEquiv R M N f) ((awayLocTensor R M N f) x) = (locTensor R M N f) x
```

**API note (not a source docstring):** The equation `AlgebraicGeometry.Scheme.Modules.awayTensorEquiv_awayLocTensor` says that localizing any `x : M ⊗[R] N` into the explicit `Away f` tensor and then applying `awayTensorEquiv` equals the native-section localization `locTensor R M N f x`. In `ModuleTensorLocalization` it extends the pure-tensor generator equation additively; the native section ring is `Γ(Spec R, D(f))`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L516-L520) (native source range).

<a id="api-e8c7f5d3fd67e4fa"></a>

### `AlgebraicGeometry.Scheme.Modules.away_actual_restriction_square`

```lean
theorem AlgebraicGeometry.Scheme.Modules.away_actual_restriction_square (R : CommRingCat) (M N : ModuleCat ↑R) (f : ↑R) (x : ↑(((tilde M).tensor (tilde N)).presheaf.obj (Opposite.op ⊤))) : (awayTensorEquiv R M N f).symm ((basicTensorEquiv R M N f).symm ((resTop R M N f) x)) = (awayLocTensor R M N f) ((topTensorEquiv R M N) x)
```

**API note (not a source docstring):** For a top-open section `x` of the tensor sheaf associated to `M,N` on `Spec R`, `AlgebraicGeometry.Scheme.Modules.away_actual_restriction_square` identifies two paths to a tensor over `Localization.Away f`: first restrict to `D(f)` and invert the native basic-open tensor comparison, then apply `awayTensorEquiv.symm`; or first use `topTensorEquiv` and then `awayLocTensor`. This square concerns a principal affine open, not arbitrary scheme opens.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorLocalization.lean#L522-L529) (native source range).


## SchemeProperties.ModuleTensorRestriction

<a id="api-0574b4816c6a1732"></a>

### `AlgebraicGeometry.Scheme.Modules.restrictTensorNatIso`

```lean
noncomputable def AlgebraicGeometry.Scheme.Modules.restrictTensorNatIso {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] : (tensorFunctor Y).comp (restrictFunctor f) ≅ ((restrictFunctor f).prod (restrictFunctor f)).comp (tensorFunctor X)
```

Restriction along an open immersion commutes with the ambient module tensor,
naturally in both module arguments.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorRestriction.lean#L412-L417) (native source range).

<a id="api-fc660dd17ca5f361"></a>

### `AlgebraicGeometry.Scheme.Modules.restrictTensorNatIso_inv_app_tmul`

```lean
theorem AlgebraicGeometry.Scheme.Modules.restrictTensorNatIso_inv_app_tmul {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules) (U : X.Opens) (s : ↑((M.restrict f).presheaf.obj (Opposite.op U))) (t : ↑((N.restrict f).presheaf.obj (Opposite.op U))) : (CategoryTheory.ConcreteCategory.hom (Hom.app ((restrictTensorNatIso f).inv.app (M, N)) U)) ((M.restrict f).tmul (N.restrict f) U s t) = (CategoryTheory.ConcreteCategory.hom (restrictAppIso f (M.tensor N) U).inv) (M.tmul N ((Hom.opensFunctor f).obj U) ((CategoryTheory.ConcreteCategory.hom (restrictAppIso f M U).hom) s) ((CategoryTheory.ConcreteCategory.hom (restrictAppIso f N U).hom) t))
```

The inverse tensor-restriction comparison sends a pure tensor to the
restricted pure tensor, with section and scalar identifications explicit.
This is its compatibility with the ambient tensor's sheafification unit.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/ModuleTensorRestriction.lean#L419-L429) (native source range).


## SchemeProperties.NoetherianComponents

<a id="api-a0c72996e72c52f5"></a>

### `NoetherianSpace.isOpen_connectedComponent`

```lean
theorem NoetherianSpace.isOpen_connectedComponent {X : Type u} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] (x : X) : IsOpen (connectedComponent x)
```

Connected components of a Noetherian space are open.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/NoetherianComponents.lean#L38-L64) (native source range).

<a id="api-de8b55c2ed14e619"></a>

### `isIrreducible_connectedComponent_of_closedPoints_homogeneous`

```lean
theorem isIrreducible_connectedComponent_of_closedPoints_homogeneous {X : Type u} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [JacobsonSpace X] (hhom : ∀ (x y : ↑(closedPoints X)), ∃ (e : X ≃ₜ X), e ↑x = ↑y) (x : X) : IsIrreducible (connectedComponent x)
```

Every connected component of a closed-point homogeneous Noetherian Jacobson
space is irreducible.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/NoetherianComponents.lean#L66-L140) (native source range).

<a id="api-fa72d6ee93e52ea8"></a>

### `NoetherianSpace.toLocallyConnectedSpace`

```lean
instance NoetherianSpace.toLocallyConnectedSpace {X : Type u} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] : LocallyConnectedSpace X
```

Every Noetherian topological space is locally connected.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/NoetherianComponents.lean#L142-L149) (native source range).

<a id="api-33acea4533caaab5"></a>

### `AlgebraicGeometry.Scheme.connectedComponentOpen.connectedSpace`

```lean
instance AlgebraicGeometry.Scheme.connectedComponentOpen.connectedSpace (X : Scheme) [IsNoetherian X] (c : ConnectedComponents ↥X) : ConnectedSpace ↥↑(X.connectedComponentOpen c)
```

A connected-component open subscheme of a Noetherian scheme is connected.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/NoetherianComponents.lean#L153-L162) (native source range).

<a id="api-02fdfc9788334ef9"></a>

### `AlgebraicGeometry.Scheme.connectedComponentOpen.isNoetherian`

```lean
instance AlgebraicGeometry.Scheme.connectedComponentOpen.isNoetherian (X : Scheme) [IsNoetherian X] (c : ConnectedComponents ↥X) : IsNoetherian ↑(X.connectedComponentOpen c)
```

A connected-component open subscheme of a Noetherian scheme is Noetherian.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/NoetherianComponents.lean#L164-L172) (native source range).

<a id="api-a644d3c7120638b0"></a>

### `AlgebraicGeometry.Scheme.connectedComponentOpenCover`

```lean
def AlgebraicGeometry.Scheme.connectedComponentOpenCover (X : Scheme) [IsNoetherian X] : X.OpenCover
```

The open cover of a Noetherian scheme by its connected components.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/NoetherianComponents.lean#L174-L184) (native source range).

<a id="api-212d9350ffe801a5"></a>

### `AlgebraicGeometry.IsNormal.iff_connectedComponentOpen`

```lean
theorem AlgebraicGeometry.IsNormal.iff_connectedComponentOpen (X : Scheme) [IsNoetherian X] : IsNormal X ↔ ∀ (c : ConnectedComponents ↥X), IsNormal ↑(X.connectedComponentOpen c)
```

A Noetherian scheme is normal if and only if all its connected-component
open subschemes are normal.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/NoetherianComponents.lean#L186-L199) (native source range).

<a id="api-f9a347c03f004fd1"></a>

### `AlgebraicGeometry.Scheme.connectedComponentOpen.isIntegral`

```lean
instance AlgebraicGeometry.Scheme.connectedComponentOpen.isIntegral (X : Scheme) [IsNoetherian X] [IsNormal X] (c : ConnectedComponents ↥X) : IsIntegral ↑(X.connectedComponentOpen c)
```

Every connected component of a normal Noetherian scheme is integral.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/NoetherianComponents.lean#L201-L205) (native source range).


## SchemeProperties.Normal

<a id="api-d35992e9af513087"></a>

### `IsLocalization.AtPrime.isDomain_of_le`

```lean
theorem IsLocalization.AtPrime.isDomain_of_le {R : Type u} (S : Type v) (T : Type w) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] {p q : Ideal R} [p.IsPrime] [q.IsPrime] [IsLocalization.AtPrime S q] [IsLocalization.AtPrime T p] (hpq : p ≤ q) [IsDomain S] : IsDomain T
```

Let `S` and `T` be localizations of `R` at prime ideals `q` and `p`
respectively. If `p ≤ q` and `S` is a domain, then `T` is a domain.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Normal.lean#L25-L54) (native source range).

<a id="api-cc8d160cdf339a5d"></a>

### `IsLocalization.AtPrime.isIntegrallyClosed_of_le`

```lean
theorem IsLocalization.AtPrime.isIntegrallyClosed_of_le {R : Type u} (S : Type v) (T : Type w) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] {p q : Ideal R} [p.IsPrime] [q.IsPrime] [IsLocalization.AtPrime S q] [IsLocalization.AtPrime T p] (hpq : p ≤ q) [IsDomain S] [IsIntegrallyClosed S] : IsIntegrallyClosed T
```

Let `S` and `T` be localizations of `R` at prime ideals `q` and `p`
respectively. If `p ≤ q` and `S` is an integrally closed domain, then `T` is
integrally closed.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Normal.lean#L56-L86) (native source range).

<a id="api-ca0e0011509ab912"></a>

### `IsLocallyNormalRing`

```lean
class IsLocallyNormalRing (R : Type u) [CommRing R] : Prop
```

A commutative ring is locally normal if every localization at a prime ideal
is a domain and integrally closed. Unlike the conjunction of `IsDomain` and
`IsIntegrallyClosed`, this interface also accommodates disconnected rings.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Normal.lean#L90-L96) (native source range).

<a id="api-f785d154b0e9d022"></a>

### `IsLocallyNormalRing.mk`

```lean
constructor IsLocallyNormalRing.mk : ∀ {R : Type u} [inst : CommRing R], (∀ (p : PrimeSpectrum R), IsDomain (Localization.AtPrime p.asIdeal)) → (∀ (p : PrimeSpectrum R), IsIntegrallyClosed (Localization.AtPrime p.asIdeal)) → IsLocallyNormalRing R
```

**API note (not a source docstring):** The constructor `IsLocallyNormalRing.mk` in `Normal` assembles local normality of a commutative ring from two per-prime proofs: each `Localization.AtPrime p.asIdeal` is a domain and is integrally closed. Because it quantifies over prime localizations rather than requiring `IsDomain R`, it accommodates disconnected rings; the corresponding scheme statement is `IsNormal (Spec R)`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Normal.lean#L90-L96) (native source range).

<a id="api-e12ee61e96d82cb9"></a>

### `IsLocallyNormalRing.isDomain_atPrime`

```lean
theorem IsLocallyNormalRing.isDomain_atPrime {R : Type u} {inst✝ : CommRing R} [self : IsLocallyNormalRing R] (p : PrimeSpectrum R) : IsDomain (Localization.AtPrime p.asIdeal)
```

**API note (not a source docstring):** The field `IsLocallyNormalRing.isDomain_atPrime` in `Normal` gives an integral-domain instance for the localization of a fixed commutative ring `R` at each prime-spectrum point `p`. The companion field requires integral closedness of each localization; the pointwise condition permits a disconnected original ring and is not a global `IsDomain R` assertion.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Normal.lean#L94-L94) (native source range).

<a id="api-e8dc80aa2290ff19"></a>

### `IsLocallyNormalRing.isIntegrallyClosed_atPrime`

```lean
theorem IsLocallyNormalRing.isIntegrallyClosed_atPrime {R : Type u} {inst✝ : CommRing R} [self : IsLocallyNormalRing R] (p : PrimeSpectrum R) : IsIntegrallyClosed (Localization.AtPrime p.asIdeal)
```

**API note (not a source docstring):** The field `IsLocallyNormalRing.isIntegrallyClosed_atPrime` in `Normal` supplies an integrally closed localization `Localization.AtPrime p.asIdeal` for each `p : PrimeSpectrum R` of the fixed commutative ring `R`. The class also requires that each localization be a domain; this field does not by itself make a disconnected `R` an integrally closed domain.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Normal.lean#L95-L95) (native source range).

<a id="api-5d3d6c89e308e90c"></a>

### `isLocallyNormalRing_of_isDomain`

```lean
instance isLocallyNormalRing_of_isDomain (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] : IsLocallyNormalRing R
```

An integrally closed domain is locally normal.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Normal.lean#L101-L107) (native source range).

<a id="api-e8ea9142c28f68e2"></a>

### `IsLocallyNormalRing.of_ringEquiv`

```lean
theorem IsLocallyNormalRing.of_ringEquiv {R : Type u} {S : Type v} [CommRing R] [CommRing S] (e : R ≃+* S) [IsLocallyNormalRing R] : IsLocallyNormalRing S
```

Local normality is preserved by ring equivalences.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Normal.lean#L109-L125) (native source range).

<a id="api-15d1371f2e27f45a"></a>

### `AlgebraicGeometry.IsNormal`

```lean
class AlgebraicGeometry.IsNormal (X : Scheme) : Prop
```

A scheme is normal if every local ring is a domain and integrally closed.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Normal.lean#L131-L135) (native source range).

<a id="api-0f1e42fbc10c9ac1"></a>

### `AlgebraicGeometry.IsNormal.mk`

```lean
constructor AlgebraicGeometry.IsNormal.mk : ∀ {X : AlgebraicGeometry.Scheme}, autoParam (∀ (x : ↥X), IsDomain ↑(X.presheaf.stalk x)) AlgebraicGeometry.IsNormal.stalk_isDomain._autoParam → autoParam (∀ (x : ↥X), IsIntegrallyClosed ↑(X.presheaf.stalk x)) AlgebraicGeometry.IsNormal.stalk_isIntegrallyClosed._autoParam → AlgebraicGeometry.IsNormal X
```

**API note (not a source docstring):** The constructor `AlgebraicGeometry.IsNormal.mk` in `Normal` packages two indexed families into normality of a scheme `X`: every structure-sheaf stalk is a domain and every such stalk is integrally closed. No global irreducibility or connectedness requirement appears, so the conditions must be understood pointwise, including the vacuous empty-scheme case.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Normal.lean#L131-L135) (native source range).

<a id="api-3a5577388941cd2a"></a>

### `AlgebraicGeometry.IsNormal.stalk_isDomain`

```lean
theorem AlgebraicGeometry.IsNormal.stalk_isDomain {X : Scheme} [self : IsNormal X] (x : ↥X) : IsDomain ↑(X.presheaf.stalk x)
```

**API note (not a source docstring):** The registered field `AlgebraicGeometry.IsNormal.stalk_isDomain` of the `IsNormal X` class in `Normal` provides an integral-domain structure on the structure-sheaf stalk at every point `x : X`. Scheme normality also requires integrally closed stalks via its other field; this result is local to each point rather than a global-domain conclusion for a possibly disconnected scheme.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Normal.lean#L133-L133) (native source range).

<a id="api-6510d7eb92d5bfd8"></a>

### `AlgebraicGeometry.IsNormal.stalk_isIntegrallyClosed`

```lean
theorem AlgebraicGeometry.IsNormal.stalk_isIntegrallyClosed {X : Scheme} [self : IsNormal X] (x : ↥X) : IsIntegrallyClosed ↑(X.presheaf.stalk x)
```

**API note (not a source docstring):** The registered field `AlgebraicGeometry.IsNormal.stalk_isIntegrallyClosed` of the `IsNormal X` class in `Normal` supplies integral closedness of `X.presheaf.stalk x` at each scheme point `x`. The companion field supplies that same stalk's domain condition; one must not read this field alone as asserting that `Γ(X, ⊤)` is an integrally closed domain.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Normal.lean#L134-L134) (native source range).

<a id="api-862b0663b5487542"></a>

### `AlgebraicGeometry.isNormal_of_stalk`

```lean
theorem AlgebraicGeometry.isNormal_of_stalk (X : Scheme) [∀ (x : ↥X), IsDomain ↑(X.presheaf.stalk x)] [∀ (x : ↥X), IsIntegrallyClosed ↑(X.presheaf.stalk x)] : IsNormal X
```

Normality can be proved directly on all stalks.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Normal.lean#L139-L143) (native source range).

<a id="api-95114a078cdf1a8f"></a>

### `AlgebraicGeometry.isNormal_of_isOpenImmersion`

```lean
theorem AlgebraicGeometry.isNormal_of_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] [IsNormal Y] : IsNormal X
```

Normality is preserved by open immersions.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Normal.lean#L145-L153) (native source range).

<a id="api-ad3e3580870e5972"></a>

### `AlgebraicGeometry.instIsNormalToScheme`

```lean
instance AlgebraicGeometry.instIsNormalToScheme {X : Scheme} {U : X.Opens} [IsNormal X] : IsNormal ↑U
```

**API note (not a source docstring):** The generated open-subscheme instance `AlgebraicGeometry.instIsNormalToScheme` in `Normal` inherits `IsNormal U` for a chosen open `U : X.Opens` from `IsNormal X`. It invokes `isNormal_of_isOpenImmersion` for the canonical inclusion `U.ι`, whose stalk maps are isomorphisms. It does not assert normality of closed subschemes.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Normal.lean#L155-L156) (native source range).

<a id="api-7146027550098ba9"></a>

### `AlgebraicGeometry.instIsNormalXScheme`

```lean
instance AlgebraicGeometry.instIsNormalXScheme (X : Scheme) {𝒰 : X.OpenCover} [IsNormal X] (i : 𝒰.I₀) : IsNormal (𝒰.X i)
```

**API note (not a source docstring):** The generated instance `AlgebraicGeometry.instIsNormalXScheme` gives `IsNormal (𝒰.X i)` to each member of an open cover `𝒰` of a normal scheme `X`. The source owner `Normal` applies stalkwise preservation along the member's open immersion into `X`; normality need not descend along an arbitrary scheme morphism.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Normal.lean#L158-L159) (native source range).

<a id="api-0803ef1870a8cf7d"></a>

### `AlgebraicGeometry.instIsClosedUnderIsomorphismsSchemeIsNormal`

```lean
instance AlgebraicGeometry.instIsClosedUnderIsomorphismsSchemeIsNormal : CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms fun (x : Scheme) => IsNormal x
```

**API note (not a source docstring):** The object-property instance `AlgebraicGeometry.instIsClosedUnderIsomorphismsSchemeIsNormal` in `Normal` says normality of schemes is invariant under scheme isomorphisms. It uses preservation under open immersions applied to the inverse isomorphism, transferring both the domain and integrally-closed conditions on corresponding stalks; it is not an assertion about all morphisms.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Normal.lean#L161-L162) (native source range).

<a id="api-9a037bfdc6a1db80"></a>

### `AlgebraicGeometry.IsNormal.of_openCover`

```lean
theorem AlgebraicGeometry.IsNormal.of_openCover (X : Scheme) (𝒰 : X.OpenCover) [∀ (i : 𝒰.I₀), IsNormal (𝒰.X i)] : IsNormal X
```

Normality is local on an open cover.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Normal.lean#L164-L174) (native source range).

<a id="api-13728f133fe848f1"></a>

### `AlgebraicGeometry.IsNormal.iff_of_openCover`

```lean
theorem AlgebraicGeometry.IsNormal.iff_of_openCover (X : Scheme) (𝒰 : X.OpenCover) : IsNormal X ↔ ∀ (i : 𝒰.I₀), IsNormal (𝒰.X i)
```

**API note (not a source docstring):** For any open cover `𝒰` of `X`, `AlgebraicGeometry.IsNormal.iff_of_openCover` says `X` is normal precisely when every open-cover member is normal. Its source `Normal` defines scheme normality by integral-domain and integrally-closed stalks; these transfer through the cover's open immersions. It adds no finite-cover condition and does not equate normality with global integrally closedness of disconnected rings.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Normal.lean#L176-L178) (native source range).

<a id="api-205641b9cb2e599f"></a>

### `AlgebraicGeometry.normalSpec`

```lean
instance AlgebraicGeometry.normalSpec {R : CommRingCat} [IsLocallyNormalRing ↑R] : IsNormal (Spec R)
```

**API note (not a source docstring):** The instance `AlgebraicGeometry.normalSpec` in `Normal` proves `IsNormal (Spec R)` from `IsLocallyNormalRing R`, meaning that every prime localization of the commutative ring is a domain and integrally closed. It transfers those two properties across the canonical stalk isomorphism. The ring `R` itself need not be globally an integral domain; locally normal disconnected rings are allowed.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Normal.lean#L181-L192) (native source range).

<a id="api-81b0934edf4c4d2d"></a>

### `AlgebraicGeometry.isLocallyNormalRing_of_isNormal_spec`

```lean
theorem AlgebraicGeometry.isLocallyNormalRing_of_isNormal_spec (R : CommRingCat) [IsNormal (Spec R)] : IsLocallyNormalRing ↑R
```

If an affine spectrum is normal, then its coordinate ring is locally
normal. This is deliberately a theorem rather than an instance, to avoid a
typeclass loop with `normalSpec`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Normal.lean#L194-L208) (native source range).

<a id="api-5749b1ea38be65d9"></a>

### `AlgebraicGeometry.isNormal_spec_iff_isLocallyNormalRing`

```lean
theorem AlgebraicGeometry.isNormal_spec_iff_isLocallyNormalRing (R : CommRingCat) : IsNormal (Spec R) ↔ IsLocallyNormalRing ↑R
```

A commutative ring is locally normal exactly when its affine spectrum is a
normal scheme.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Normal.lean#L210-L220) (native source range).

<a id="api-0aa925c3138f8d8d"></a>

### `AlgebraicGeometry.isReduced_of_isNormal`

```lean
instance AlgebraicGeometry.isReduced_of_isNormal (X : Scheme) [IsNormal X] : IsReduced X
```

**API note (not a source docstring):** The instance `AlgebraicGeometry.isReduced_of_isNormal` in `Normal` makes a normal scheme reduced: normality supplies integral-domain, integrally-closed local rings at every point, and reducedness is checked stalkwise. This is the one-way implication for `IsNormal X` and does not assert that every reduced scheme is normal.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Normal.lean#L222-L223) (native source range).

<a id="api-358bd9c990fe67b0"></a>

### `AlgebraicGeometry.isDomain_stalk_of_specializes`

```lean
theorem AlgebraicGeometry.isDomain_stalk_of_specializes (X : Scheme) {x y : ↥X} (hxy : x ⤳ y) [IsDomain ↑(X.presheaf.stalk y)] : IsDomain ↑(X.presheaf.stalk x)
```

Being a domain is preserved from a scheme stalk to a generalization.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Normal.lean#L225-L252) (native source range).

<a id="api-dde205a6c1f6461e"></a>

### `AlgebraicGeometry.isIntegrallyClosed_stalk_of_specializes`

```lean
theorem AlgebraicGeometry.isIntegrallyClosed_stalk_of_specializes (X : Scheme) {x y : ↥X} (hxy : x ⤳ y) [IsDomain ↑(X.presheaf.stalk y)] [IsIntegrallyClosed ↑(X.presheaf.stalk y)] : IsIntegrallyClosed ↑(X.presheaf.stalk x)
```

Integral closedness is preserved from a scheme stalk to a
generalization.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Normal.lean#L254-L283) (native source range).


## SchemeProperties.NormalEtale

<a id="api-6b2d6b9c8097ca4a"></a>

### `IsLocallyNormalRing.pi`

```lean
theorem IsLocallyNormalRing.pi {I : Type u_1} (S : I → Type u_2) [(i : I) → CommRing (S i)] [Finite I] [∀ (i : I), IsLocallyNormalRing (S i)] : IsLocallyNormalRing ((i : I) → S i)
```

A finite product of locally normal rings is locally normal.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/NormalEtale.lean#L190-L214) (native source range).

<a id="api-0fc411e5ee034a33"></a>

### `IsLocallyNormalRing.of_finiteEtale_of_isDomain`

```lean
theorem IsLocallyNormalRing.of_finiteEtale_of_isDomain {R : Type u_1} {S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R] [IsIntegrallyClosed R] [Algebra.Etale R S] [Module.Finite R S] : IsLocallyNormalRing S
```

A finite etale algebra over an integrally closed domain is locally normal.
The algebra itself may be disconnected.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/NormalEtale.lean#L233-L273) (native source range).

<a id="api-4cd1c14aabd626d2"></a>

### `IsLocallyNormalRing.of_finiteEtale`

```lean
theorem IsLocallyNormalRing.of_finiteEtale {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [IsLocallyNormalRing R] [Algebra.Etale R S] [Module.Finite R S] : IsLocallyNormalRing S
```

A finite etale algebra over a locally normal ring is locally normal.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/NormalEtale.lean#L275-L330) (native source range).


## SchemeProperties.NormalLocalization

<a id="api-2cdc36d55ba5f199"></a>

### `IsLocallyNormalRing.of_isLocalization`

```lean
theorem IsLocallyNormalRing.of_isLocalization {R : Type u} [CommRing R] (M : Submonoid R) (S : Type v) [CommRing S] [Algebra R S] [IsLocalization M S] [IsLocallyNormalRing R] : IsLocallyNormalRing S
```

Any localization of a locally normal ring is locally normal.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/NormalLocalization.lean#L19-L45) (native source range).

<a id="api-74c0f5bc3fdb18a1"></a>

### `Localization.isLocallyNormalRing`

```lean
instance Localization.isLocallyNormalRing {R : Type u} [CommRing R] [IsLocallyNormalRing R] (M : Submonoid R) : IsLocallyNormalRing (Localization M)
```

The canonical localization at any submonoid of a locally normal ring is
locally normal.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/NormalLocalization.lean#L47-L52) (native source range).


## SchemeProperties.NormalPolynomial

<a id="api-a25c0e3063ac75c2"></a>

### `Polynomial.isLocallyNormalRing_of_isLocallyNormalRing`

```lean
instance Polynomial.isLocallyNormalRing_of_isLocallyNormalRing {R : Type u} [CommRing R] [IsLocallyNormalRing R] : IsLocallyNormalRing (Polynomial R)
```

A polynomial ring over a locally normal ring is locally normal.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/NormalPolynomial.lean#L24-L82) (native source range).

<a id="api-754713169858d4d8"></a>

### `MvPolynomial.isLocallyNormalRing_of_isLocallyNormalRing`

```lean
instance MvPolynomial.isLocallyNormalRing_of_isLocallyNormalRing {R : Type u} [CommRing R] [IsLocallyNormalRing R] {ι : Type u_1} [Finite ι] : IsLocallyNormalRing (MvPolynomial ι R)
```

A multivariate polynomial ring in finitely many variables over a locally
normal ring is locally normal.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/NormalPolynomial.lean#L84-L96) (native source range).


## SchemeProperties.NormalSeparable

<a id="api-ca0a151e6b2743a3"></a>

### `IsLocallyNormalRing.of_directed_iSup`

```lean
theorem IsLocallyNormalRing.of_directed_iSup {R : Type u_1} [CommRing R] {ι : Type u_2} [Nonempty ι] (S : ι → Subring R) (hS : Directed (fun (x1 x2 : Subring R) => x1 ≤ x2) S) (hTop : ⨆ (i : ι), S i = ⊤) (hflat : ∀ (i : ι), (S i).subtype.Flat) (hNormal : ∀ (i : ι), IsLocallyNormalRing ↥(S i)) : IsLocallyNormalRing R
```

A nonempty directed supremum of flat locally normal subrings is locally normal.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/NormalSeparable.lean#L246-L260) (native source range).

<a id="api-920bf7dcf6528bc2"></a>

### `IsLocallyNormalRing.tensorProduct_of_isSeparablyGenerated`

```lean
theorem IsLocallyNormalRing.tensorProduct_of_isSeparablyGenerated {k : Type u_1} {A : Type u_2} {L : Type u_3} [Field k] [CommRing A] [Field L] [Algebra k A] [Algebra k L] [IsLocallyNormalRing A] [Algebra.EssFiniteType k L] [Algebra.IsSeparablyGenerated k L] : IsLocallyNormalRing (TensorProduct k A L)
```

Tensoring a locally normal algebra with an essentially finite-type,
separably generated field extension preserves local normality.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/NormalSeparable.lean#L366-L460) (native source range).

<a id="api-8788fc42eb25e6b0"></a>

### `IsLocallyNormalRing.tensorProduct_of_isTranscendentalSeparable`

```lean
theorem IsLocallyNormalRing.tensorProduct_of_isTranscendentalSeparable {k : Type u_1} {A : Type u_2} {K : Type u_3} [Field k] [CommRing A] [Field K] [Algebra k A] [Algebra k K] [IsLocallyNormalRing A] [Algebra.IsTranscendentalSeparable k K] : IsLocallyNormalRing (TensorProduct k A K)
```

Tensoring a locally normal algebra with a transcendental-separable field
extension preserves local normality.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/NormalSeparable.lean#L462-L498) (native source range).


## SchemeProperties.NormalSeparableScheme

<a id="api-e4f80876ee1d7268"></a>

### `AlgebraicGeometry.IsNormal.pullback_specMap_of_isTranscendentalSeparable`

```lean
theorem AlgebraicGeometry.IsNormal.pullback_specMap_of_isTranscendentalSeparable {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.IsTranscendentalSeparable k K] {X : Scheme} [IsNormal X] (f : X ⟶ Spec ↧k) : IsNormal (CategoryTheory.Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
```

A normal scheme over a field remains normal after base change along a
transcendental-separable field extension.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/NormalSeparableScheme.lean#L52-L73) (native source range).


## SchemeProperties.PresheafModuleTensorStalk

<a id="api-f6c7327eefd0ebd6"></a>

### `PresheafOfModulesOfCommRing.stalkTensorEquiv`

```lean
noncomputable def PresheafOfModulesOfCommRing.stalkTensorEquiv {X : TopCat} (A : TopCat.Presheaf CommRingCat X) (P Q : PresheafOfModulesOfCommRing A) (x : ↑X) : ↑(TopCat.Presheaf.stalk (PresheafOfModules.presheaf (CategoryTheory.MonoidalCategoryStruct.tensorObj P Q)) x) ≃ₗ[↑(A.stalk x)] TensorProduct ↑(A.stalk x) ↑(TopCat.Presheaf.stalk (PresheafOfModules.presheaf P) x) ↑(TopCat.Presheaf.stalk (PresheafOfModules.presheaf Q) x)
```

Canonical tensor product comparison for stalks of modules over a commutative-ring
presheaf. No sheaf condition on the modules or assumption on the space is required.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/PresheafModuleTensorStalk.lean#L536-L548) (native source range).

<a id="api-86f26b1d430169b9"></a>

### `PresheafOfModulesOfCommRing.stalkTensorEquiv_germ_tmul`

```lean
theorem PresheafOfModulesOfCommRing.stalkTensorEquiv_germ_tmul {X : TopCat} (A : TopCat.Presheaf CommRingCat X) (P Q : PresheafOfModulesOfCommRing A) (x : ↑X) (V : TopologicalSpace.Opens ↑X) (hx : x ∈ V) (p : ↑(P.obj (Opposite.op V))) (q : ↑(Q.obj (Opposite.op V))) : (stalkTensorEquiv A P Q x) ((CategoryTheory.ConcreteCategory.hom (TopCat.Presheaf.germ (PresheafOfModules.presheaf (CategoryTheory.MonoidalCategoryStruct.tensorObj P Q)) V x hx)) (have this := p ⊗ₜ[↑(A.obj (Opposite.op V))] q; this)) = (CategoryTheory.ConcreteCategory.hom (TopCat.Presheaf.germ (PresheafOfModules.presheaf P) V x hx)) p ⊗ₜ[↑(A.stalk x)] (CategoryTheory.ConcreteCategory.hom (TopCat.Presheaf.germ (PresheafOfModules.presheaf Q) V x hx)) q
```

A pure tensor section at a common neighborhood maps to the tensor of germs.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/PresheafModuleTensorStalk.lean#L550-L564) (native source range).

<a id="api-5a7ca793b69cb634"></a>

### `PresheafOfModulesOfCommRing.stalkMapLinear`

```lean
noncomputable def PresheafOfModulesOfCommRing.stalkMapLinear {X : TopCat} (A : TopCat.Presheaf CommRingCat X) (P Q : PresheafOfModulesOfCommRing A) (x : ↑X) (f : P ⟶ Q) : ↑(TopCat.Presheaf.stalk (PresheafOfModules.presheaf P) x) →ₗ[↑(A.stalk x)] ↑(TopCat.Presheaf.stalk (PresheafOfModules.presheaf Q) x)
```

The map on native module stalks, linear over the unchanged ring stalk.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/PresheafModuleTensorStalk.lean#L584-L610) (native source range).

<a id="api-e4f74df5e3ae0fcc"></a>

### `PresheafOfModulesOfCommRing.stalkMapLinear_apply_stalkFunctor`

```lean
theorem PresheafOfModulesOfCommRing.stalkMapLinear_apply_stalkFunctor {X : TopCat} (A : TopCat.Presheaf CommRingCat X) (P Q : PresheafOfModulesOfCommRing A) (x : ↑X) (f : P ⟶ Q) (z : ↑(TopCat.Presheaf.stalk (PresheafOfModules.presheaf P) x)) : (stalkMapLinear A P Q x f) z = (AddCommGrpCat.Hom.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map ((PresheafOfModules.toPresheaf (CategoryTheory.Functor.comp A (CategoryTheory.forget₂ CommRingCat RingCat))).map f))) z
```

The underlying additive map of the linear stalk map.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/PresheafModuleTensorStalk.lean#L612-L618) (native source range).

<a id="api-e66c7e2624de525b"></a>

### `PresheafOfModulesOfCommRing.stalkMapLinear_germ`

```lean
theorem PresheafOfModulesOfCommRing.stalkMapLinear_germ {X : TopCat} (A : TopCat.Presheaf CommRingCat X) (P Q : PresheafOfModulesOfCommRing A) (x : ↑X) (f : P ⟶ Q) (U : TopologicalSpace.Opens ↑X) (hx : x ∈ U) (p : ↑(P.obj (Opposite.op U))) : (stalkMapLinear A P Q x f) ((CategoryTheory.ConcreteCategory.hom (TopCat.Presheaf.germ (PresheafOfModules.presheaf P) U x hx)) p) = (CategoryTheory.ConcreteCategory.hom (TopCat.Presheaf.germ (PresheafOfModules.presheaf Q) U x hx)) ((CategoryTheory.ConcreteCategory.hom (f.app (Opposite.op U))) p)
```

A stalk map acts on a germ by applying the presheaf morphism to its section.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/PresheafModuleTensorStalk.lean#L620-L625) (native source range).

<a id="api-287ccd2bcbb7cd61"></a>

### `PresheafOfModulesOfCommRing.stalkTensorEquiv_naturality`

```lean
theorem PresheafOfModulesOfCommRing.stalkTensorEquiv_naturality {X : TopCat} (A : TopCat.Presheaf CommRingCat X) (P Q : PresheafOfModulesOfCommRing A) (x : ↑X) {P' Q' : PresheafOfModulesOfCommRing A} (f : P ⟶ P') (g : Q ⟶ Q') (z : ↑(TopCat.Presheaf.stalk (PresheafOfModules.presheaf (CategoryTheory.MonoidalCategoryStruct.tensorObj P Q)) x)) : (stalkTensorEquiv A P' Q' x) ((stalkMapLinear A (CategoryTheory.MonoidalCategoryStruct.tensorObj P Q) (CategoryTheory.MonoidalCategoryStruct.tensorObj P' Q') x (CategoryTheory.MonoidalCategoryStruct.tensorHom f g)) z) = (TensorProduct.map (stalkMapLinear A P P' x f) (stalkMapLinear A Q Q' x g)) ((stalkTensorEquiv A P Q x) z)
```

The stalk tensor comparison is natural in both module arguments.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/PresheafModuleTensorStalk.lean#L632-L702) (native source range).


## SchemeProperties.QcqsModuleLocalization

<a id="api-32127dc5c06b5aa2"></a>

### `AlgebraicGeometry.Scheme.Modules.basicOpenRestriction`

```lean
noncomputable def AlgebraicGeometry.Scheme.Modules.basicOpenRestriction {X : Scheme} (M : X.Modules) {U : X.Opens} (f : ↑(X.presheaf.obj (Opposite.op U))) : ↑(M.presheaf.obj (Opposite.op U)) →ₗ[↑(X.presheaf.obj (Opposite.op U))] ↑(M.presheaf.obj (Opposite.op (X.basicOpen f)))
```

Restriction of module sections to a basic open, as a linear map over the
ring of sections on the ambient open.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/QcqsModuleLocalization.lean#L37-L49) (native source range).

<a id="api-e95d4f9015cd6488"></a>

### `AlgebraicGeometry.Scheme.Modules.affineOpenSectionsLinearEquiv`

```lean
noncomputable def AlgebraicGeometry.Scheme.Modules.affineOpenSectionsLinearEquiv {X : Scheme} (M : X.Modules) (U : X.Opens) (hU : IsAffineOpen U) : ↑(moduleSpecΓFunctor.obj ((M.restrict U.ι).restrict hU.isoSpec.inv)) ≃ₗ[↑(X.presheaf.obj (Opposite.op U))] ↑(M.presheaf.obj (Opposite.op U))
```

Sections of a module on an affine open agree with the global sections of its
double restriction to the corresponding spectrum.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/QcqsModuleLocalization.lean#L88-L96) (native source range).

<a id="api-67ad44c8cf9c1736"></a>

### `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpen_of_qcqs`

```lean
theorem AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpen_of_qcqs {X : Scheme} (M : X.Modules) [SheafOfModules.IsQuasicoherent M] {U : X.Opens} (hU : IsCompact U.carrier) (hU' : IsQuasiSeparated U.carrier) (f : ↑(X.presheaf.obj (Opposite.op U))) : IsLocalizedModule.Away f (M.basicOpenRestriction f)
```

Restriction of sections of a quasicoherent module to a basic open of a
compact quasiseparated open is localization away from the defining section.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/QcqsModuleLocalization.lean#L494-L523) (native source range).

<a id="api-e6690c9d82d297c2"></a>

### `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpen_of_qcqs_of_top`

```lean
theorem AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpen_of_qcqs_of_top {X : Scheme} (M : X.Modules) [SheafOfModules.IsQuasicoherent M] [CompactSpace ↥X] [QuasiSeparatedSpace ↥X] (f : ↑(X.presheaf.obj (Opposite.op ⊤))) : IsLocalizedModule.Away f (M.basicOpenRestriction f)
```

The global-sections specialization of
`isLocalizedModule_basicOpen_of_qcqs`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/QcqsModuleLocalization.lean#L525-L534) (native source range).


## SchemeProperties.Quasicoherent

<a id="api-dcc522ea649c5a1d"></a>

### `AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_restrict_affineOpen`

```lean
theorem AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_restrict_affineOpen (X : Scheme) (M : X.Modules) [SheafOfModules.IsQuasicoherent M] (U : X.Opens) (hU : IsAffineOpen U) : CategoryTheory.IsIso ((M.restrict U.ι).restrict hU.isoSpec.inv).fromTildeΓ
```

A quasicoherent module, restricted to an affine open and transported to
the literal spectrum of the ring of sections on that open, is recovered from
its global sections by the affine `fromTildeΓ` map.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Quasicoherent.lean#L27-L35) (native source range).

<a id="api-448264ed82baad24"></a>

### `AlgebraicGeometry.Scheme.Modules.presentationOfIsIsoFromTildeΓ`

```lean
noncomputable def AlgebraicGeometry.Scheme.Modules.presentationOfIsIsoFromTildeΓ {R : CommRingCat} (N : (Spec R).Modules) [hN : CategoryTheory.IsIso N.fromTildeΓ] : SheafOfModules.Presentation N
```

An affine module recovered from its global sections has a global
presentation.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Quasicoherent.lean#L37-L47) (native source range).

<a id="api-43ab40c4b3b412d1"></a>

### `AlgebraicGeometry.Scheme.Modules.presentationRestrictAffineOpenOfIsIsoFromTildeΓ`

```lean
noncomputable def AlgebraicGeometry.Scheme.Modules.presentationRestrictAffineOpenOfIsIsoFromTildeΓ (X : Scheme) (M : X.Modules) (U : X.Opens) (hU : IsAffineOpen U) [hFrom : CategoryTheory.IsIso ((M.restrict U.ι).restrict hU.isoSpec.inv).fromTildeΓ] : SheafOfModules.Presentation (M.restrict U.ι)
```

The affine `fromTildeΓ` condition gives a presentation of the original
restriction to the affine open, before transport to the over-site.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Quasicoherent.lean#L49-L66) (native source range).

<a id="api-362eacd937bf174d"></a>

### `AlgebraicGeometry.Scheme.Modules.presentationOverOfPresentationRestrict`

```lean
noncomputable def AlgebraicGeometry.Scheme.Modules.presentationOverOfPresentationRestrict (X : Scheme) (M : X.Modules) (U : X.Opens) (P : SheafOfModules.Presentation (M.restrict U.ι)) : (SheafOfModules.over M U).Presentation
```

A presentation of the scheme-theoretic restriction to an open gives a
presentation on the corresponding over-site.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Quasicoherent.lean#L68-L85) (native source range).

<a id="api-02362aea12bffd94"></a>

### `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isOpenCover_presentation`

```lean
theorem AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isOpenCover_presentation (X : Scheme) (M : X.Modules) {I : Type u} (U : I → X.Opens) (hU : TopologicalSpace.IsOpenCover U) (P : (i : I) → SheafOfModules.Presentation (M.restrict (U i).ι)) : SheafOfModules.IsQuasicoherent M
```

Quasicoherence glues from presentations on an open cover, expressed in
the scheme-facing restriction API.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Quasicoherent.lean#L87-L99) (native source range).

<a id="api-912555b5de2e4633"></a>

### `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_affineOpenCover_isIso_fromTildeΓ`

```lean
theorem AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_affineOpenCover_isIso_fromTildeΓ (X : Scheme) (M : X.Modules) {I : Type u} (U : I → X.Opens) (hU : TopologicalSpace.IsOpenCover U) (hUaff : ∀ (i : I), IsAffineOpen (U i)) [hFrom : ∀ (i : I), CategoryTheory.IsIso ((M.restrict (U i).ι).restrict ⋯.isoSpec.inv).fromTildeΓ] : SheafOfModules.IsQuasicoherent M
```

It suffices to verify the affine `fromTildeΓ` condition on one affine
open cover.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Quasicoherent.lean#L101-L113) (native source range).

<a id="api-150007e846c9795a"></a>

### `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_iff_affineOpenCover_isIso_fromTildeΓ`

```lean
theorem AlgebraicGeometry.Scheme.Modules.isQuasicoherent_iff_affineOpenCover_isIso_fromTildeΓ (X : Scheme) (M : X.Modules) {I : Type u} (U : I → X.Opens) (hU : TopologicalSpace.IsOpenCover U) (hUaff : ∀ (i : I), IsAffineOpen (U i)) : SheafOfModules.IsQuasicoherent M ↔ ∀ (i : I), CategoryTheory.IsIso ((M.restrict (U i).ι).restrict ⋯.isoSpec.inv).fromTildeΓ
```

On a fixed affine open cover, quasicoherence is equivalent to the affine
`fromTildeΓ` condition on every member of the cover.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Quasicoherent.lean#L115-L129) (native source range).


## SchemeProperties.QuasicoherentAbelian

<a id="api-76f3c6880b3d8d14"></a>

### `AlgebraicGeometry.tildeFunctor_preservesFiniteLimits`

```lean
instance AlgebraicGeometry.tildeFunctor_preservesFiniteLimits (R : CommRingCat) : CategoryTheory.Limits.PreservesFiniteLimits (tilde.functor R)
```

The affine tilde functor preserves finite limits.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/QuasicoherentAbelian.lean#L252-L258) (native source range).

<a id="api-4b23e55917f5790a"></a>

### `AlgebraicGeometry.Scheme.Modules.restrictFunctor_preservesFiniteLimits`

```lean
instance AlgebraicGeometry.Scheme.Modules.restrictFunctor_preservesFiniteLimits {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] : CategoryTheory.Limits.PreservesFiniteLimits (restrictFunctor f)
```

Restriction of modules along an open immersion preserves finite limits.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/QuasicoherentAbelian.lean#L263-L288) (native source range).

<a id="api-48e6c3b66cdb0468"></a>

### `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isLimit`

```lean
theorem AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isLimit (X : Scheme) {J : Type w} [CategoryTheory.SmallCategory J] [CategoryTheory.FinCategory J] {F : CategoryTheory.Functor J X.Modules} {c : CategoryTheory.Limits.Cone F} (hc : CategoryTheory.Limits.IsLimit c) (hF : ∀ (j : J), SheafOfModules.IsQuasicoherent (F.obj j)) : SheafOfModules.IsQuasicoherent c.pt
```

A finite limit of quasicoherent modules on an arbitrary scheme is
quasicoherent.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/QuasicoherentAbelian.lean#L292-L320) (native source range).

<a id="api-cbca89d76f1a2e12"></a>

### `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isColimit`

```lean
theorem AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isColimit (X : Scheme) {J : Type w} [CategoryTheory.SmallCategory J] [CategoryTheory.FinCategory J] {F : CategoryTheory.Functor J X.Modules} {c : CategoryTheory.Limits.Cocone F} (hc : CategoryTheory.Limits.IsColimit c) (hF : ∀ (j : J), SheafOfModules.IsQuasicoherent (F.obj j)) : SheafOfModules.IsQuasicoherent c.pt
```

A finite colimit of quasicoherent modules on an arbitrary scheme is
quasicoherent.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/QuasicoherentAbelian.lean#L324-L352) (native source range).

<a id="api-4501d794d36e9162"></a>

### `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_isClosedUnderFiniteLimits`

```lean
instance AlgebraicGeometry.Scheme.Modules.isQuasicoherent_isClosedUnderFiniteLimits (X : Scheme) : (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderFiniteLimits
```

Quasicoherent modules on an arbitrary scheme are closed under finite
limits.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/QuasicoherentAbelian.lean#L354-L361) (native source range).

<a id="api-ecb491a1394acac4"></a>

### `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_isClosedUnderFiniteColimits`

```lean
instance AlgebraicGeometry.Scheme.Modules.isQuasicoherent_isClosedUnderFiniteColimits (X : Scheme) : (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderFiniteColimits
```

Quasicoherent modules on an arbitrary scheme are closed under finite
colimits.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/QuasicoherentAbelian.lean#L363-L370) (native source range).

<a id="api-ef866e6bc2ce3d4c"></a>

### `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_containsZero`

```lean
instance AlgebraicGeometry.Scheme.Modules.isQuasicoherent_containsZero (X : Scheme) : (SheafOfModules.isQuasicoherent X.ringCatSheaf).ContainsZero
```

The quasicoherent-module property on an arbitrary scheme contains a zero
object.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/QuasicoherentAbelian.lean#L372-L379) (native source range).

<a id="api-2f6fd83aebac6ab9"></a>

### `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_isClosedUnderKernels`

```lean
instance AlgebraicGeometry.Scheme.Modules.isQuasicoherent_isClosedUnderKernels (X : Scheme) : (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderKernels
```

Quasicoherent modules on an arbitrary scheme are closed under kernels.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/QuasicoherentAbelian.lean#L381-L389) (native source range).

<a id="api-a04b7ddca616197f"></a>

### `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_isClosedUnderCokernels`

```lean
instance AlgebraicGeometry.Scheme.Modules.isQuasicoherent_isClosedUnderCokernels (X : Scheme) : (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderCokernels
```

Quasicoherent modules on an arbitrary scheme are closed under cokernels.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/QuasicoherentAbelian.lean#L391-L399) (native source range).


## SchemeProperties.Reduced

<a id="api-6a31683558121adb"></a>

### `IsLocalization.isReduced`

```lean
theorem IsLocalization.isReduced {R : Type u} [CommRing R] (M : Submonoid R) (S : Type v) [CommRing S] [Algebra R S] [IsLocalization M S] [IsReduced R] : IsReduced S
```

An arbitrary localization of a reduced commutative ring is reduced.

Unlike `isReduced_localizationPreserves`, this form permits the source and
target rings to live in independent universes.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Reduced.lean#L22-L45) (native source range).

<a id="api-d7a603e0698c364a"></a>

### `IsLocalization.AtPrime.isReduced_of_le`

```lean
theorem IsLocalization.AtPrime.isReduced_of_le {R : Type u} (S : Type v) (T : Type w) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] {p q : Ideal R} [p.IsPrime] [q.IsPrime] [IsLocalization.AtPrime S q] [IsLocalization.AtPrime T p] (hpq : p ≤ q) [IsReduced S] : IsReduced T
```

Let `S` and `T` be localizations of `R` at prime ideals `q` and `p`
respectively. If `p ≤ q` and `S` is reduced, then `T` is reduced.

Indeed, `q.primeCompl ≤ p.primeCompl`, so `T` is a further localization of
`S`.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Reduced.lean#L47-L71) (native source range).

<a id="api-699dfc50cdf2338a"></a>

### `AlgebraicGeometry.isReduced_stalk_of_specializes`

```lean
theorem AlgebraicGeometry.isReduced_stalk_of_specializes (X : Scheme) {x y : ↥X} (hxy : x ⤳ y) [_root_.IsReduced ↑(X.presheaf.stalk y)] : _root_.IsReduced ↑(X.presheaf.stalk x)
```

Reducedness of scheme stalks is preserved under generalization: if `x`
specializes to `y` and the stalk at `y` is reduced, then the stalk at `x` is
reduced.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Reduced.lean#L75-L106) (native source range).


## SchemeProperties.SheafFinitePresentation

<a id="api-fc4c32afc303812c"></a>

### `SheafOfModules.LocalGeneratorsData.isFinitePresentation_of_isLocallyFreeData`

```lean
theorem SheafOfModules.LocalGeneratorsData.isFinitePresentation_of_isLocallyFreeData {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} {R : CategoryTheory.Sheaf J RingCat} [∀ (X : C), CategoryTheory.HasSheafify (J.over X) AddCommGrpCat] [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat] {M : SheafOfModules R} (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] [q.IsFiniteType] : M.IsFinitePresentation
```

A local basis with finitely many generators on each chart gives local finite
presentation. The covering family need not be finite, and the numbers of generators
may vary between charts. Both hypotheses concern the same local generator datum.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/SheafFinitePresentation.lean#L40-L50) (native source range).


## SchemeProperties.StructureSheaf

<a id="api-67cad20ab9ada889"></a>

### `AlgebraicGeometry.Scheme.Modules.unit_isQuasicoherent`

```lean
theorem AlgebraicGeometry.Scheme.Modules.unit_isQuasicoherent (X : Scheme) : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent
```

The structure sheaf of any scheme is quasicoherent as a module over
itself.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/StructureSheaf.lean#L26-L45) (native source range).


## SchemeProperties.Torsion

<a id="api-88e42a1289c6b33f"></a>

### `Module.isTorsion_iff_subsingleton_tensorProduct`

```lean
theorem Module.isTorsion_iff_subsingleton_tensorProduct {R : Type u} {K : Type v} {M : Type w} [CommRing R] [CommRing K] [Algebra R K] [IsFractionRing R K] [AddCommGroup M] [Module R M] : IsTorsion R M ↔ Subsingleton (TensorProduct R K M)
```

A module over a commutative ring is torsion if and only if its base change
to any localization at the non-zero-divisors is zero.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Torsion.lean#L29-L46) (native source range).

<a id="api-0c5fae1fdfea2e83"></a>

### `Module.isTorsion_iff_subsingleton_fractionRing_tensorProduct`

```lean
theorem Module.isTorsion_iff_subsingleton_fractionRing_tensorProduct {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] : IsTorsion R M ↔ Subsingleton (TensorProduct R (FractionRing R) M)
```

A module over a commutative ring is torsion if and only if its base change
to the canonical localization at the non-zero-divisors is zero. For domains,
this is the usual fraction ring.

[Source](https://github.com/FormalFrontier/scheme-properties/blob/6b204a3e49f022e51d78a9f93e77513b99a87e00/SchemeProperties/Torsion.lean#L48-L55) (native source range).
