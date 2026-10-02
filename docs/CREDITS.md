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
[ModuleTensorLocalization](../SchemeProperties/ModuleTensorLocalization.lean)
develops Anchor's earlier basic-open/localization research into a distinct
reusable project proof. Original prototypes, later production proofs and
adaptations have different histories preserved in project Git and private
research records, not silently treated as identical expression.

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
headers explain mathematical use without private research records; original
contributor and review details remain in history and the owning private records.

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

Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*; J. S. Milne,
*Algebraic Groups: The Theory of Group Schemes of Finite Type over a Field*;
and Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
Chapter I, §5, provide mathematical background. These citations do not mean
the books' prose is copied or an external source is completely formalized.

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
this project does not replace them or relicense mathlib, `coherent-modules` or
`finite-etale-algebras`. No book prose or source PDF is shipped. Exact
source-specific passage correspondence and formalization coverage belong to
separate source records, not this reusable library.
