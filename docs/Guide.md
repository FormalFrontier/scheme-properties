# Scheme Properties: reader guide

This guide describes mathematical source assembled from accepted ordinary
development commit `04513a56ed7c339875f114b56fcc430e6b753fed`. It is a
navigation aid, **not** generated API documentation, a complete declaration
census, or an assertion of release readiness. The source files, rather than
this summary, determine the exact Lean statements.
For expression provenance and mathematical references, see [Credits](CREDITS.md).
The separate [generated API](API.md) supplies native signatures and source links
for its fixed historical 73-module snapshot, not the new finite-presentation,
rational-map-composition, dense-open-pullback, controlled-composition or
controlled over-base modules
or changed aggregate. Its
[generation contract](README.md) distinguishes display sites from proof bodies;
see the standalone [native finite-presentation guide](FinitePresentations.md)
and [relative-composition guide](RationalMapComposition.md),
[dense-open pullback guide](DenseOpenPullback.md) and
[controlled-composition guide](DenseOpenComposition.md), together with the
[controlled over-base guide](DenseOpenCompositionOver.md), for later APIs.

## Imports and conventions

The aggregate import is `import SchemeProperties` (the current
[root](../SchemeProperties.lean)); focused imports have the form
`import SchemeProperties.Reduced`, with the names below substituting for
`Reduced`; use `import SchemeProperties.RationalMapComposition` for the
[relative-composition lemmas](RationalMapComposition.md) and
`import SchemeProperties.DenseOpenPullback` for the
[all-dense-open predicate](DenseOpenPullback.md), or
`import SchemeProperties.DenseOpenComposition` for its
[conditional composition operations](DenseOpenComposition.md), or
`import SchemeProperties.DenseOpenCompositionOver` for the
[common-base preservation lemmas](DenseOpenCompositionOver.md). Some non-scheme
constructions, such as presheaf tensor stalks,
have their own focused import. The original 36 focused mathematical modules, including
[ComponentFibers](../SchemeProperties/ComponentFibers.lean) and
[FactorialNormal](../SchemeProperties/FactorialNormal.lean), now have native
`module` headers and public imports. The older
`ComponentFibers` consumer at `86f5ec67f52cc571cf1f2222fa8468363e8c7984`
does not establish compatibility with the current file:
`fbf96d925efa4eb54b27fa3e605cc6f33d9166d9` added a private
étale-section/open-immersion helper and the public theorem
`AlgebraicGeometry.geometricallyConnected_of_connectedSpace_of_section`.
`ComponentBaseChange` was identical in that *historical* comparison but changed
subsequently at `49a3c7e71850f5e7913c1423f33ccbcc7c89703e`: it now has a
native module/public-import header, a public section and `@[expose]` on
`toConnectedComponentsSpec`. The later native-documentation build of the exact
73-module source at `a05b182aa17ea7cd1a591ec7b60aa7d6f2b6704c` included every
shipped example and test module; the older historical client is not its evidence.

The [toolchain](../lean-toolchain), [Lake requirements](../lakefile.toml) and
[resolved manifest](../lake-manifest.json) record this assembly's Lean
v4.34.0-rc2, mathlib `83abb3e776bdefcbc447a1e44d0debe4010039e5`,
and official **private GitHub** `coherent-modules` and `finite-etale-algebras`
release inputs. Those URLs are not public-access promises; builds require
access. These exact URL/revision substitutions were used by that later
source/client build and native generation. This does not transfer an old
consumer's proof check or promise general source compatibility. The examples
below were compiled in that source build; their selected axiom printouts do not
constitute the separate complete release proof audit.

The APIs distinguish a ring from all of its local rings, a scheme from one
open or one stalk, and connectedness from geometric connectedness. `Scheme.{u}`
and `Over (Spec (.of K))` use the displayed universe of mathlib's scheme
interfaces; some ring/algebra results allow independent source/target universes.
Short names such as `Scheme.Modules.*` below assume
`open AlgebraicGeometry`; their fully qualified prefix is
`AlgebraicGeometry.Scheme.Modules`.
An empty scheme often satisfies stalkwise properties vacuously, whereas a
*nonempty* hypothesis in a topological theorem must not be silently removed.

## Local algebra and scheme properties

| Focused module | Entry points and precise scope |
| --- | --- |
| [Reduced](../SchemeProperties/Reduced.lean) | `IsLocalization.isReduced` works across independent ring universes; `IsLocalization.AtPrime.isReduced_of_le` assumes primes `p ≤ q` and reducedness at `q`, then proves it at `p`. `AlgebraicGeometry.isReduced_stalk_of_specializes` takes `x ⤳ y` and a reduced stalk at `y` to a reduced stalk at `x` (generalization), not the converse. |
| [Integral](../SchemeProperties/Integral.lean) | `AlgebraicGeometry.isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_stalk_isDomain` needs **connectedness**, local Noetherianity and a domain at **every stalk**; `isIntegral_of_isNoetherian_of_connectedSpace_of_stalk_isDomain` is its Noetherian variant. The intermediate irreducible-component lemmas are local, not a global integrality claim for disconnected schemes. |
| [Normal](../SchemeProperties/Normal.lean) | `IsLocallyNormalRing` means every prime localization is an integrally closed domain, allowing disconnected rings. `AlgebraicGeometry.IsNormal` imposes that property on scheme stalks. `isNormal_spec_iff_isLocallyNormalRing`, `IsNormal.iff_of_openCover`, open-immersion/iso and specialization lemmas provide affine and local interfaces; `isReduced_of_isNormal` gives the one-way normal ⇒ reduced implication. |
| [NormalLocalization](../SchemeProperties/NormalLocalization.lean), [NormalPolynomial](../SchemeProperties/NormalPolynomial.lean), [NormalEtale](../SchemeProperties/NormalEtale.lean) | `IsLocallyNormalRing.of_isLocalization` handles arbitrary localizations; the polynomial instances include finitely many indeterminates; `IsLocallyNormalRing.of_finiteEtale` permits disconnected base rings and independent base/target universes but assumes a **finite étale** algebra, not an arbitrary extension. |
| [NormalSeparable](../SchemeProperties/NormalSeparable.lean), [NormalSeparableScheme](../SchemeProperties/NormalSeparableScheme.lean) | `IsLocallyNormalRing.of_directed_iSup` requires a nonempty directed family, supremum top, flat inclusions and local normality of every member. `IsLocallyNormalRing.tensorProduct_of_isTranscendentalSeparable` and `AlgebraicGeometry.IsNormal.pullback_specMap_of_isTranscendentalSeparable` require transcendental-separability of the field extension; the latter is a same-universe scheme base-change statement, not preservation under *all* field extensions. |
| [Factorial](../SchemeProperties/Factorial.lean), [FactorialNormal](../SchemeProperties/FactorialNormal.lean) | `AlgebraicGeometry.IsFactorial` requires unique factorization in **each stalk**; `factorialSpec` assumes a UFD coordinate ring, while `factorialSpec_of_isDedekindDomain` obtains the stalkwise property without demanding global UFD. `AlgebraicGeometry.isNormal_of_isFactorial` is an instance of factorial ⇒ normal, not its converse. Empty schemes satisfy the stalkwise factorial predicate. |

## Partial and rational maps

| Focused module | Entry points and precise scope |
| --- | --- |
| [DenseOpenPullback](../SchemeProperties/DenseOpenPullback.lean) | `AlgebraicGeometry.Scheme.PartialMap.PullsDenseOpens` asks that the pullback of **every** dense target open be dense in **ambient `X`** for arbitrary same-universe schemes. Native equivalence, dense restriction and rational-map representatives preserve the condition. `pullsDenseOpens_of_isOpenMap` needs only `IsOpenMap f.hom`; the distinct dominant route requires `[PreirreducibleSpace X] [Nonempty Y] [IsDominant f.hom]`. This predicate module alone constructs no composite or concrete nondominant witness; see the [standalone guide](DenseOpenPullback.md). |
| [DenseOpenComposition](../SchemeProperties/DenseOpenComposition.lean) | `PartialMap.compOfPullsDenseOpens` and `RationalMap.compOfPullsDenseOpens` compose arbitrary partial and quotient rational maps given an explicit first-map `PullsDenseOpens` proof, with both representative-value bridges and compatibility with native `comp` and total-second `compHom` under the stated premises; no closure or category laws are proved. See the [focused guide](DenseOpenComposition.md). |
| [DenseOpenCompositionOver](../SchemeProperties/DenseOpenCompositionOver.lean) | `PartialMap.isOver_compOfPullsDenseOpens` and `RationalMap.isOver_compOfPullsDenseOpens` keep the controlled composite over `S` for arbitrary same-universe `X Y Z S` over `S`, explicit first-map `PullsDenseOpens` and `[f.IsOver S] [g.IsOver S]`. No second predicate, dominance, preirreducibility or nonemptiness is required; no arbitrary whole-domain rational representative is asserted over `S`. See [precise hypotheses and proof route](DenseOpenCompositionOver.md). |
| [RationalMapComposition](../SchemeProperties/RationalMapComposition.lean) | `PartialMap.isOver_comp_of_isDominant_first` and `RationalMap.isOver_comp_of_isDominant_first` preserve being over a common base under native composition, with a preirreducible source, nonempty intermediate scheme, dominant first map and over-base hypotheses; they do not use the new all-dense-open predicate. See [precise hypotheses](RationalMapComposition.md). |

## Components, coproducts and finite-type points

| Focused module | Entry points and precise scope |
| --- | --- |
| [ConnectedComponents](../SchemeProperties/ConnectedComponents.lean) | For a **locally connected** scheme, `Scheme.connectedComponentOpen` and `Scheme.connectedComponentSigmaIso` express it as the coproduct of its open connected-component subschemes; `Scheme.toConnectedComponentCoproduct` maps into a coproduct of copies of another scheme. Empty schemes and infinitely many components are allowed; finite decomposition is not assumed. |
| [NoetherianComponents](../SchemeProperties/NoetherianComponents.lean) | Noetherian schemes have open, finitely indexed connected components; `Scheme.connectedComponentOpenCover` and `IsNormal.iff_connectedComponentOpen` give the cover test, and `Scheme.connectedComponentOpen.isIntegral` needs both Noetherianity **and** normality. `isIrreducible_connectedComponent_of_closedPoints_homogeneous` additionally needs a Noetherian **Jacobson** space and transitive homeomorphisms on closed points. |
| [CoproductSections](../SchemeProperties/CoproductSections.lean) | `AlgebraicGeometry.Scheme.sigmaPresheafObjIso` identifies sections on **any open** of a same-universe scheme coproduct with the product of sections on summand preimages; `sigmaPresheafObjIso_hom_apply` and `sigmaPresheafObjIso_hom_res_apply` identify pullback and restriction. This is an arbitrary indexed coproduct, not only a finite or component-indexed one. |
| [CoproductTopology](../SchemeProperties/CoproductTopology.lean) | `AlgebraicGeometry.quasiSeparatedSpace_sigma` transports quasiseparatedness componentwise with no nonemptiness/compactness assumption. `AlgebraicGeometry.not_compactSpace_sigma` has the additional hypotheses **infinite index** and **every summand nonempty**; it is not a converse to quasiseparatedness. |
| [FiniteTypePoints](../SchemeProperties/FiniteTypePoints.lean) | For a field `K`, `AlgebraicGeometry.fgAlgCatOpEquivLftAffineOver` relates opposite finitely generated `K`-algebras to affine schemes locally of finite type over `K`; `finiteAlgSpecOver_isDense`, `lftPointsFullyFaithful`, and `lftPointsPreservesFiniteLimits` concern the restricted functor of points. `algebraicOver` adds a **quasicompact structure morphism** to locally finite type; this file stops before group-object refinements. |

## Geometric connectedness and component schemes

These constructions have different base-field assumptions. They do not turn
ordinary connectedness into geometric connectedness over an arbitrary field.

| Focused module | Entry points and precise scope |
| --- | --- |
| [GeometricConnectedness](../SchemeProperties/GeometricConnectedness.lean) | `PrimeSpectrum.connectedSpace_tensorProduct_fields` treats tensor products of extension fields over a **separably closed** field, including transcendental/imperfect situations. `AlgebraicGeometry.geometricallyConnected_of_isSepClosed` assumes a connected scheme over such a field; its scheme API follows mathlib's same-universe boundary and imposes no finite-type hypothesis. |
| [GlobalSectionsBaseChange](../SchemeProperties/GlobalSectionsBaseChange.lean) | `AlgebraicGeometry.Scheme.globalSectionsBaseChangeEquiv` identifies `K ⊗[k] Γ(X, ⊤)` with global sections after base change for a **compact and quasiseparated** `X` over `k`. `globalSectionsBaseChangeEquiv_identity` and `globalSectionsBaseChangeEquiv_tower` cover identity and successive extensions. The field/scheme constructions share a universe; no affineness, separatedness, finite field degree or nonemptiness is required. |
| [ComponentScheme](../SchemeProperties/ComponentScheme.lean) | `AlgebraicGeometry.componentSubalgebra` selects the greatest finite étale subalgebra of global sections; `componentScheme`, `toComponentScheme`, `flat_toComponentScheme` and `componentScheme_universal` package the canonical finite-étale target and universal factorization. They assume a scheme **locally of finite type and quasicompact over a field** (same-universe `Over`), not a connected or reduced source. |
| [ComponentBaseChange](../SchemeProperties/ComponentBaseChange.lean) | `AlgebraicGeometry.componentBaseChangeComparison`, `componentBaseChangeComparisonAlgEquiv`, and `componentBaseChangeIso` give the canonical comparison and isomorphism after an **arbitrary field extension**, within the same-universe/finite-type/quasicompact component-scheme setting. This is distinct from the separability condition for preserving normality. |
| [ComponentFibers](../SchemeProperties/ComponentFibers.lean) | `AlgebraicGeometry.range_fiberι_toComponentScheme_eq_connectedComponent` identifies the underlying residue-field fibre's range with the component of a **chosen source point mapping to the target point**; `geometricallyConnected_fiber_toComponentScheme` proves its **geometric** connectedness over the residue field. `geometricallyConnected_of_connectedSpace_of_section` additionally requires a **connected** source and a **section of its structure morphism**; it is not an unpointed connectedness theorem over arbitrary fields. The private helper for this last result is not a public import contract. |
| [ComponentProduct](../SchemeProperties/ComponentProduct.lean) | `AlgebraicGeometry.componentSchemeMapOfHom` is functorial on eligible over-field schemes; `componentProductComparison` and `componentProductIso` compare the component scheme of a **binary fibre product** with the product of component schemes. Both factors retain the locally-finite-type/quasicompact field hypotheses; the empty case is included. |

## Modules, quasicoherence and coherence

| Focused module | Entry points and precise scope |
| --- | --- |
| [Torsion](../SchemeProperties/Torsion.lean), [ModuleProperties](../SchemeProperties/ModuleProperties.lean) | `Module.isTorsion_iff_subsingleton_tensorProduct` uses **CommRing** `R` and a localization `K` at its non-zero-divisors; `Module.isTorsion_iff_subsingleton_fractionRing_tensorProduct` applies to the canonical total quotient ring for any **CommRing** `R`, including rings with zero-divisors. By contrast, `AlgebraicGeometry.Scheme.Modules.IsTorsionFree` and `VanishesAtGenericPoints` are stalkwise on arbitrary scheme modules (also empty/zero modules), while `tilde_vanishesAtGenericPoints_iff_isTorsion` and its fraction-ring variant require `tilde` on an **integral affine spectrum**; do not infer this last equivalence for every scheme module or general affine ring. |
| [Quasicoherent](../SchemeProperties/Quasicoherent.lean), [StructureSheaf](../SchemeProperties/StructureSheaf.lean) | `Scheme.Modules.isQuasicoherent_iff_affineOpenCover_isIso_fromTildeΓ` checks native quasicoherence using the transported `fromTildeΓ` on **any fixed affine open cover**; neither the cover nor the scheme must be finite or nonempty. `Scheme.Modules.unit_isQuasicoherent` covers the structure sheaf on every scheme. |
| [QcqsModuleLocalization](../SchemeProperties/QcqsModuleLocalization.lean) | `Scheme.Modules.isLocalizedModule_basicOpen_of_qcqs` requires a quasicoherent module and a **compact quasiseparated chosen open** `U`; it localizes its sections away from `f : Γ(X,U)`. `isLocalizedModule_basicOpen_of_qcqs_of_top` assumes compact/quasiseparated `X` for global sections. No affine or nonempty hypothesis is added. |
| [QuasicoherentAbelian](../SchemeProperties/QuasicoherentAbelian.lean) | `Scheme.Modules.isQuasicoherent_of_isLimit`/`isQuasicoherent_of_isColimit` and the finite-limit/colimit, zero, kernel and cokernel instances equip the **native full subcategory** of quasicoherent modules on **any** scheme with an abelian-category structure; this is not a claim that every ambient sheaf module is quasicoherent. |
| [CoherentQuasicoherent](../SchemeProperties/CoherentQuasicoherent.lean), [CoherentQuasicoherentLocality](../SchemeProperties/CoherentQuasicoherentLocality.lean) | `Scheme.Modules.isCoherent_basicOpen_of_qcqs` and `isCoherent_of_span_basicOpen_of_qcqs` work on compact quasiseparated opens; the converse uses a **set-indexed family** of principal opens whose sections span the unit ideal. `Scheme.Modules.isCoherentQuasicoherent` concerns objects of the native quasicoherent full subcategory; `isCoherentQuasicoherent_iff_affineOpenCover` checks that property on **any fixed affine open cover** without a globally finite cover or a qcqs scheme. |
| [IdealSheafModule](../SchemeProperties/IdealSheafModule.lean) | `Scheme.IdealSheafData.toModule` packages the kernel submodule of the structure sheaf's quotient by the supplied ideal data; `affineSectionsEquiv`, `toModule_isLocalizedModule_basicOpen`, `toModule_isQuasicoherent` and `Scheme.nilradicalModule` expose affine sections/localization, quasicoherence and nilradical clients. No reducedness or nonempty/finite hypothesis is needed. |
| [SheafFinitePresentation](../SchemeProperties/SheafFinitePresentation.lean) | `SheafOfModules.LocalGeneratorsData.isFinitePresentation_of_isLocallyFreeData` assumes **the same local-generator datum** has `IsLocallyFreeData` and `IsFiniteType`. Basis sizes can vary (including zero), and the cover can be infinite; two unrelated local covers are not identified by this theorem. This focused module depends on mathlib only. |
| [SheafFinitePresentationTransport](../SchemeProperties/SheafFinitePresentationTransport.lean), [ModuleFinitePresentation](../SchemeProperties/ModuleFinitePresentation.lean) | Five native finite-presentation APIs transport finite indices through a colimit-preserving functor, obtain local finite presentation from a supplied finite global presentation with site/over-site hypotheses, restrict along open immersions, prove finite presentation for `tilde` of finitely presented modules, and refine to an affine open cover with the same finite quasicoherent witness. These modules depend directly on mathlib, not on the earlier same-local-basis module; see [precise hypotheses and examples](FinitePresentations.md). |

## Tensor products and their comparison maps

These are sheafified ambient tensors, not an asserted monoidal-category
instance on all scheme modules. Distinguish tensoring sections over a **native
section ring** on a principal affine open from tensoring on an arbitrary open.

| Focused module | Entry points and precise scope |
| --- | --- |
| [PresheafModuleTensorStalk](../SchemeProperties/PresheafModuleTensorStalk.lean) | `PresheafOfModulesOfCommRing.stalkTensorEquiv`, `stalkTensorEquiv_germ_tmul` and `stalkTensorEquiv_naturality` identify stalks of pointwise tensor presheaves with tensors of stalks over the **ring stalk**. This is a presheaf/topological-space result: no scheme, sheaf or finiteness assumption. |
| [ModuleTensor](../SchemeProperties/ModuleTensor.lean) | `Scheme.Modules.tensorFunctor`, `tensor`, `tensorUnit`, `tmul`, `tensorHomEquiv`, and `tensorSymm` sheafify pointwise tensors of **arbitrary** scheme modules, with pure-section laws and an all-target sheafification Hom equivalence. No quasicoherence or global monoidal instance is supplied. |
| [ModuleTensorRestriction](../SchemeProperties/ModuleTensorRestriction.lean) | `Scheme.Modules.restrictTensorNatIso` and `restrictTensorNatIso_inv_app_tmul` compare the ambient tensor with restriction along a **same-universe open immersion**, naturally in both inputs and with the explicit pure-tensor formula; this is not a comparison along every scheme morphism. |
| [ModuleTensorAffine](../SchemeProperties/ModuleTensorAffine.lean) | `Scheme.Modules.affineTensorNatIso` identifies the tensor of associated modules on `Spec R` with `tilde (M ⊗[R] N)`, naturally in both modules; `affineTensorNatIso_inv_app_top_tmul` gives the top-open pure-tensor formula. Zero rings/modules are allowed and no finite-generation assumption appears. |
| [ModuleTensorLocalization](../SchemeProperties/ModuleTensorLocalization.lean) | `Scheme.Modules.basicTensorEquiv` compares **principal-open** sections, `locTensor` and `actual_restriction_square` relate localization to top-open restriction, and `awayTensorEquiv`/`awayLocTensor` use `Localization.Away f`; restrictions of principal opens are natural and semilinear. Includes `f = 0`, `f = 1`, zero rings and zero modules; **no** corresponding equivalence on arbitrary opens is claimed. |

## Inspectable clients and release boundary

- [Examples](../Examples/) contains direct, root-import and `AxiomAudit`
  clients for component schemes, component base change/products, coproduct
  sections/topology. For example, see the [component-scheme source client](../Examples/ComponentScheme.lean),
  [component-product root client](../Examples/ComponentProductRoot.lean) and
  [coproduct-sections client](../Examples/CoproductSections.lean).
- [Test](../Test/) holds direct/root clients and `Axioms` files for coherent
  quasicoherence, ideal/structure-sheaf modules, quasicoherent abelian categories
  and ambient/restricted tensors. Start with the [tensor client](../Test/ModuleTensorClient.lean),
  [restricted-tensor root client](../Test/ModuleTensorRestrictionRootClient.lean),
  and [coherence client](../Test/CoherentQuasicoherentClient.lean).
  The [dense-open pullback client](../Test/DenseOpenPullbackClient.lean) checks
  seven anonymous direct-import examples without defining public declarations.
  The [controlled-composition client](../Test/DenseOpenCompositionClient.lean)
  checks eleven further private direct-import examples, including both
  representative changes and native/total-second compatibility.
  The [controlled over-base client](../Test/DenseOpenCompositionOverClient.lean)
  checks five private generic uses, including the quotient, open-first and
  total-second routes; these are not public theorems or concrete examples.

These are persistent source files, not by themselves a complete release test
matrix. The initial static guide authoring stage ran no Lean commands. The later
native-documentation stage compiled the historical 73-module snapshot against
the exact official pins and generated the separate API reference. That snapshot
subsequently reached an independently accepted equal-tree official release;
the finite-presentation transfer also completed independent destination review,
integration and publication in
[release `193d4fe`](https://github.com/FormalFrontier/scheme-properties/commit/193d4fe284cf1de71b168c198ad7b24a6eb71d39).
The generated reference remains the explicitly historical 73-module snapshot;
the later additions are documented in [FinitePresentations.md](FinitePresentations.md),
[RationalMapComposition.md](RationalMapComposition.md) and
[DenseOpenPullback.md](DenseOpenPullback.md),
[DenseOpenComposition.md](DenseOpenComposition.md) and
[DenseOpenCompositionOver.md](DenseOpenCompositionOver.md).
Native display sites, compiled clients,
checked proof bodies and release acceptance are distinct. The additional
[finite-presentation client](../Test/FinitePresentationClient.lean) exercises
nine direct uses, including empty indices, zero module and zero ring.
