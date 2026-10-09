# Credits and expression provenance

**Authors: Formal Frontier Agents.** Original Formal Frontier contributions
are licensed [Apache-2.0](../LICENSE). This collective credit does not
identify a copyright owner or displace individual upstream notices. Formal
Frontier maintainers and contributors developed Lean proofs, examples and
documentation with AI assistance and mathematical review. AI assistance is
not a claim of independent human authorship or rights clearance.

## Original project and adapted expression

**Atlas** developed the initial reducedness, integrality, normality,
factoriality, connected-component and quasicoherence modules and coordinated
mathematical scope and later integration. **Anchor** contributed the
[tensor restriction comparison](../SchemeProperties/ModuleTensorRestriction.lean),
the native documentation adapter and later review/integration. **Prism**
developed the original generic finite-presentation transport, tilde
constructions and finite-witness refinement;
[SheafFinitePresentation](../SchemeProperties/SheafFinitePresentation.lean)
adapts Prism's original finite-local-basis argument. The
[native presentation module](../SchemeProperties/ModuleFinitePresentation.lean)
adapts that work and the mathlib affine-cover construction, retaining the
different original contributions and notices below.

[ConnectedComponents](../SchemeProperties/ConnectedComponents.lean) adapts
**Lattice**'s earlier original Formal Frontier module. The group-free
[FiniteTypePoints](../SchemeProperties/FiniteTypePoints.lean) adapts the
scheme-level part of Lattice's earlier algebraic-groups construction; it is
not a byte-identical copy and group-object refinements are outside this file.
Formal Frontier AI agents added the public `algebraicOverPoints_eq` equation
and its ordinary-import client as a separate API contribution, without changing
Lattice's original expression or the group-free extraction credit.
The [flat-image density](../SchemeProperties/FlatImageDensity.lean) proof uses
Mathlib's finite affine refinement of a quasi-compact cover and finite affine
coproduct to turn an open flat pullback over an affine test into a single
faithfully flat finitely presented algebra cover. Milne's Proposition 5.7 is
the finite-type antecedent; the locally finite-type field statement and the
field-free affine-lifting statement are generalizations, not translations of
his proof. Mathlib's restricted-points fullness supplies the finite-type test
comparison; no book prose or Mathlib proof expression is copied here.
[ModuleTensorLocalization](../SchemeProperties/ModuleTensorLocalization.lean)
develops Anchor's earlier basic-open/localization research into a distinct
reusable project proof. Original prototypes, later production proofs and
adaptations contribute different formal expression; none is silently treated
as independently written here.

Collective Formal Frontier contributions also include the
[native composition](RationalMapComposition.md),
[dense-open pullback](DenseOpenPullback.md),
[dominance companion](DenseOpenPullbackDominance.md),
[controlled composition](DenseOpenComposition.md),
[closure](DenseOpenCompositionClosure.md),
[associativity](DenseOpenCompositionAssociativity.md),
[units](DenseOpenCompositionUnits.md),
[relative controlled composition](DenseOpenCompositionOver.md),
[absolute](DenseOpenRationalCategory.md) and
[relative](DenseOpenRationalCategoryOver.md) rational-map categories,
[integral](IntegralDominantRationalCategory.md) and
[relative integral](IntegralDominantRationalCategoryOver.md) comparisons,
[function-field pullback](RationalFunctionFieldPullback.md),
[faithfulness](RationalFunctionFieldFaithfulness.md),
[reconstruction](RationalFunctionFieldReconstruction.md),
[given-arrow inverses](RationalFunctionFieldInverse.md),
[exact partial-isomorphism realization](RationalMapPartialIso.md),
[Jacobson obstruction](JacobsonBirationalObstruction.md) and
[generic-point maps](GenericPointFunctionField.md) and
[their chosen-base rational noninvertibility composition](GenericPointRationalNoninvertibility.md).
The same-project proof
expression reused in some of these modules is adapted rather than created
independently in this repository. The [reader guide](Guide.md) and module
headers explain their mathematical use.

[PullbackOpenImmersion](../SchemeProperties/PullbackOpenImmersion.lean) preserves
original Formal Frontier project proof expression, rather than independently
inventing it in Scheme Properties. Earlier Formal Frontier research proofs
supplied the generic kernel-product and common-kernel arguments; a subsequent
Formal Frontier contribution developed the localization, chart descent,
native open-immersion and exact-range proofs. The module preserves that
original expression, its statements and argument order, under the collective
project credit above. Module integration and the direct-import client are
separate adaptations, not claims of independent proof authorship. Imported
mathlib APIs are used, not copied, and no book prose is reproduced. The
[mathematical guide](PullbackOpenImmersion.md) explains the construction without
requiring access to the original research records.

## Mathematical sources and upstream notices

The polynomial-quotient scheme-point comparisons follow Vakil, *The Rising
Sea*, §3.6.9 and the discussion after Exercise 5.1.E, extended to possibly
nonreduced quotients. They use Mathlib's `Spec.map`, `Spec.homEquivAlgHom`,
`pointEquivClosedPoint` and generic finite-type affine-spectrum instance,
and the canonical quotient-evaluation and closed-point constructions from
Multivariate Polynomials. The scheme comparison requires a common universe;
the polynomial point-set correspondence itself does not.

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type over
a Field*, Definition 5.6 supplies the fat-subfunctor condition using one
faithfully flat algebra extension, generalized here to a category and morphism
property. His Lemma 5.9 and Proposition 5.10 directly inform the single-cover
extension statements and their Čech-gluing proof idea; the power-image
statement follows his example after Definition 5.6. Mathlib's fpqc singleton
descent supplies the proof for finite-type represented targets instead of
Milne's ring-level argument. The zero-additive nonfat boundary is derived
independently, not attributed to his example.

Milne's Corollary 5.11 supplies the finite-type antecedent for extending an
isomorphism of two dense subfunctors. The generic presheaf construction uses
the existing one-cover extension and its uniqueness to prove both inverse
laws. The scheme specialization follows from represented singleton descent
and Mathlib's fully faithful preimage of an isomorphism; it does not construct
transport to Milne's chosen small test category.

Milne's item 1.4 and Appendix A.33 supply finite-type **set-valued**
functor-of-points full faithfulness, without separatedness; the
[group-free implementation](../SchemeProperties/FiniteTypePoints.lean) also
covers locally-finite-type schemes and finite limits. Proposition 1.29
supplies the greatest finite-étale algebra, while the paragraph before 1.30
supplies its component spectrum and universal factorization. Proposition
1.30(a) informs comparison under **arbitrary field extensions** and its
canonical triangle; 1.30(b) concerns a **binary** fibre product over the base
field. Proposition 1.31 concerns component-scheme fibres over residue fields;
the Lean proof derives geometric connectedness before the fibre-algebra
identity, in the reverse order to Milne's argument. Corollary 1.32(a) supplies
the connected, pointed finite-type antecedent of the whole-scheme consequence.
Appendix A.14 informs the Noetherian finite/clopen-component argument, not
the separate integrality, normality or Jacobson component results. Arbitrary
indexed [locally connected scheme coproducts](../SchemeProperties/ConnectedComponents.lean)
are distinct from finite-étale component schemes.

Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*, Exercise
5.3.C supplies the Noetherian connected/domain-stalk integrality strategy;
the affine-neighborhood argument extends it to locally Noetherian schemes.
The aside to Exercise 5.4.M motivates local normality under
transcendental-separable field extension, not integrality of the tensor
product or connectedness of the base-changed scheme. Definition 6.1.1 and
Theorem 6.1.2 inform quasicoherence on **any fixed affine cover**; the
finite-kernel triangle of Exercise 6.1.A is not
asserted. The opening of §6.3 supplies the zero, finite-sum, kernel and
cokernel argument for the abelian quasicoherent-module category; Mathlib's
tilde construction and abelian full-subcategory API provide the formal route.

The [Stacks Project](https://stacks.math.columbia.edu/) tags 037U, 0386,
0385 and 0363 inform geometric connectedness for two extensions of a
separably closed field and the scheme-level connected-fiber/open-projection
passage. The Lean argument uses finite-type algebra intermediates but concludes
geometric connectedness for an **arbitrary connected scheme** over a
separably closed field, with no finite-type or rational-point assumption.
Mathlib's closed-point residue-field methods, purely inseparable
prime-spectrum homeomorphism and geometric-connectedness pullback supply
the formal steps from field extensions to schemes.

Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
Chapter I, §5, in the discussion before Lemma I.5.1.3 motivates
the module-to-sheaf preservation direction `isFinitePresentation_tilde` and
the affine-cover prerequisite with finite presentations on each chart in
[ModuleFinitePresentation](../SchemeProperties/ModuleFinitePresentation.lean).
The cover need not be finite. Neither result is presented as a reproduction
of a book proof or as the full affine comparison; the formal constructions
and finite-index witnesses have the distinct Mathlib and Prism provenance
identified below.

Mathlib's `Presheaf.restrictedULiftYoneda`, restricted-Yoneda density and
subcanonical/over-site results underlie
[finite-type points](../SchemeProperties/FiniteTypePoints.lean);
its flat qcqs section theorem
`isIso_pushoutSection_of_isQuasiSeparated_of_flat_right` supplies the field-extension
[global-sections comparison](../SchemeProperties/GlobalSectionsBaseChange.lean),
not a general Milne qcqs-sections theorem. Connected-component topology,
Noetherian irreducible components, Sigma coproducts and sheaf gluing support
the arbitrary-index component and coproduct results. These are followed
formalization methods, separate from the cited mathematical antecedents and
the original project expression credited above.

At the pinned Mathlib revision, [birational composition](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/AlgebraicGeometry/Birational/Composition.lean)
supplies Justus Springer's domain and morphism construction adapted in the
controlled-composition modules, its associativity proof pattern, and the
composition-domain expression adapted for exact partial isomorphisms. The
dense-open closure proof and the relative category constructions are separate
project arguments, not attributed wholesale to that source. Andrew Yang's
[native partial/rational-map interfaces](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/AlgebraicGeometry/Birational/RationalMap.lean)
are used, including the over-base API; use of these interfaces does not mean
their proof expression was copied. The two-sided exact realization uses
Mathlib's [partial-isomorphism interface](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/AlgebraicGeometry/Birational/Birational.lean).
Mathlib's [tilde affine-cover construction](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/AlgebraicGeometry/Modules/Tilde.lean#L591-L613)
is adapted in the native finite-presentation module with a separately credited
finite-index refinement.

For module tensors, Mathlib supplies pointwise presheaf tensor, sheafification,
stalk and tilde localization, and scalar/local-bijectivity APIs; the
[whole-tensor](../SchemeProperties/ModuleTensor.lean),
[stalk](../SchemeProperties/PresheafModuleTensorStalk.lean) and
[affine](../SchemeProperties/ModuleTensorAffine.lean) comparisons are project
constructions. The [restriction](../SchemeProperties/ModuleTensorRestriction.lean)
comparison follows Anchor's earlier method using genuine open-immersion
scalar maps; the [principal-open comparison](../SchemeProperties/ModuleTensorLocalization.lean)
follows Anchor's localization method, not an arbitrary-open sections formula.
Mathlib's **ring-valued** qcqs localization and compact-open induction feed
the project **module-valued** [extension](../SchemeProperties/QcqsModuleLocalization.lean).

The pinned `coherent-modules` formalization (`408a52bd54df17ccc928ce970942f1313ff10d5c`) supplies
`CoherentModules.Localization`'s coherence-under-localization and spanning
lemmas and `ModuleCat.isCoherent` from `CoherentModules/ModuleCat.lean`, used in
[CoherentQuasicoherent](../SchemeProperties/CoherentQuasicoherent.lean).
The pinned `finite-etale-algebras` formalization (`79575f65c9edec560f27756917761eed78331a2a`) supplies
`FiniteEtaleAlgebras.MaximalSubalgebra`'s greatest finite-etale subalgebra
lemma used in [ComponentScheme](../SchemeProperties/ComponentScheme.lean),
and `FiniteEtaleAlgebras.PurelyInseparableDescent` and
`FiniteEtaleAlgebras.SeparableClosureDescent` descent packages used in
[ComponentBaseChange](../SchemeProperties/ComponentBaseChange.lean).
Neither direct dependency supplies the scheme-level construction or the
arbitrary-extension comparison as a finished result.
The pinned `multivariate-polynomials` formalization (`45c90b8753e0470d40f6c050f9616f484afd0120`)
supplies the square-zero polynomial point quotient, its evaluation-module
presentation and the generator-prescribed algebra equivalence under pairwise
unit differences. Its quotient presentation uses only squares and
point-linear relations; the reduced-locus comparison is proved separately in
Scheme Properties using its square-zero criterion and Mathlib's localization
and spectrum equivalence APIs, rather than imported from that library.
Coherent Modules' coherence and localization criteria together with Mathlib's
affine communication lemma support the project
[any-affine-cover locality criterion](../SchemeProperties/CoherentQuasicoherentLocality.lean),
without a finite-cover or global qcqs assumption.

The function-field results use Mathlib's quotient rational maps,
generic-point maps and spreading out (Andrew Yang), stalk methods (Andrew
Yang and Fangming Li), dense-open composition (Justus Springer), locally
finite-type closed-point behavior (Christian Merten and Andrew Yang), and
Γ–Spec full faithfulness (Junyan Xu). In particular, the project
[pullback](RationalFunctionFieldPullback.md)
and [faithfulness](RationalFunctionFieldFaithfulness.md) do not require local
finite type; [reconstruction](RationalFunctionFieldReconstruction.md) needs
local finite type only on the target and an explicit chosen-base triangle.
[Inverse reflection](RationalFunctionFieldInverse.md) needs local finite type
of the original source, while the forward implication does not. This is an
isomorphism criterion for a given rational arrow, not a total-scheme
isomorphism. Earlier Formal Frontier proof expression for the chosen-base
inverse criterion is adapted rather than newly authored here.

The affine-cover argument in
[ModuleFinitePresentation](../SchemeProperties/ModuleFinitePresentation.lean)
adapts a mathlib construction and **retains Weihong Xu's 2024 copyright and
Apache-2.0 notice** and the original authors Kevin Buzzard, Johan Commelin,
Amelia Livingston, Sophie Morel, Jujian Zhang, Weihong Xu, Andrew Yang and
Brian Nugent. Prism's finite-witness refinement is credited separately.
Dense-open composition, closure, associativity, units and partial-isomorphism
adaptations retain **Justus Springer's** authentic 2026 copyright, license
and author notice in their respective Lean headers;
[DenseOpenCompositionOver](../SchemeProperties/DenseOpenCompositionOver.lean)
also retains **Andrew Yang's** 2024 copyright and author notice. Those
notices credit adapted upstream expression, not authorship of every new proof.

Other proofs import rather than copy mathlib's native rational-map, scheme,
birational, Jacobson and generic-stalk APIs, including work by **Andrew Yang**,
**Justus Springer**, **Fangming Li** and **Devon Tuma**. Authentic individual
notices remain in the upstream files, with their own applicable license terms;
this project does not replace them or relicense mathlib, `coherent-modules`,
`finite-etale-algebras` or `multivariate-polynomials`. No book prose or source PDF is shipped.
