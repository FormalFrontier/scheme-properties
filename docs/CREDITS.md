# Credits and expression provenance

**Authors: Formal Frontier Agents.** This collective project credit accompanies,
but does not erase, the distinguishable contributors below. It does not
identify a copyright owner. The original Formal Frontier contributions use
the project's standing Apache-2.0 authorization and the complete root
[LICENSE](../LICENSE). The earlier 73-module assembly reached an independently
accepted official release. The finite-presentation transfer also completed
independent destination review and integration and was published in
[release `193d4fe`](https://github.com/FormalFrontier/scheme-properties/commit/193d4fe284cf1de71b168c198ad7b24a6eb71d39).
See [Guide](Guide.md)
for mathematical API and readiness limits. The historical account below covers
the assembly based on ordinary accepted development commit
`04513a56ed7c339875f114b56fcc430e6b753fed`; historical predecessor
commits identify expression origin, not present-tense acceptance.

## Formal contributions

Git history attributes the initial [reducedness](../SchemeProperties/Reduced.lean),
[integrality](../SchemeProperties/Integral.lean),
[normality](../SchemeProperties/Normal.lean),
[factoriality](../SchemeProperties/Factorial.lean),
[connected-components](../SchemeProperties/ConnectedComponents.lean) and
[quasicoherence](../SchemeProperties/Quasicoherent.lean) modules, with subsequent
local-normality and Noetherian-component extensions, to **Atlas**. The initial
[component-scheme](../SchemeProperties/ComponentScheme.lean),
[component base-change](../SchemeProperties/ComponentBaseChange.lean),
[coproduct sections](../SchemeProperties/CoproductSections.lean),
[coproduct topology](../SchemeProperties/CoproductTopology.lean),
[qcqs module localization](../SchemeProperties/QcqsModuleLocalization.lean),
[global-sections base change](../SchemeProperties/GlobalSectionsBaseChange.lean),
[quasicoherent abelian](../SchemeProperties/QuasicoherentAbelian.lean),
[finite-presentation](../SchemeProperties/SheafFinitePresentation.lean),
[presheaf tensor stalks](../SchemeProperties/PresheafModuleTensorStalk.lean)
and [affine tensor comparison](../SchemeProperties/ModuleTensorAffine.lean)
contributions involve **Formalization Worker B** and, in some cases, further
review-driven edits by others. The initial
[geometric connectedness](../SchemeProperties/GeometricConnectedness.lean),
[torsion](../SchemeProperties/Torsion.lean),
[component fibres](../SchemeProperties/ComponentFibers.lean),
[component products](../SchemeProperties/ComponentProduct.lean),
[ideal sheaves](../SchemeProperties/IdealSheafModule.lean),
[ambient tensor](../SchemeProperties/ModuleTensor.lean) and
[basic-open tensor localization](../SchemeProperties/ModuleTensorLocalization.lean),
[coherent-section](../SchemeProperties/CoherentQuasicoherent.lean) and
[coherent-locality](../SchemeProperties/CoherentQuasicoherentLocality.lean)
contributions involve **Formalization Worker A**. **Anchor** supplied the
[tensor-restriction comparison](../SchemeProperties/ModuleTensorRestriction.lean)
and integrated/reviewed numerous later project contributions. These are
contributor credits, not claims of sole authorship of every current line or
legal ownership; exact file-level first introductions, later changes and
author/Task records are retained in Git history.

Several important *adapted project expressions* have earlier homes:

- [ConnectedComponents](../SchemeProperties/ConnectedComponents.lean) was
  byte-identical **at initial adoption** in Scheme commit
  `ea6716206eeee4398890c68ea2928f5b5b2231af` to
  `AlgebraicGroups/Scheme/ConnectedComponents.lean` at algebraic-groups
  development commit `36fd8edbbd2e17febff5ed3393f210b3de713b6f`.
  **Lattice** authored that earlier project module; **Atlas** transferred it.
  Scheme commit `49a3c7e71850f5e7913c1423f33ccbcc7c89703e` subsequently
  added three `@[expose]` attributes, so the accepted ordinary base
  `04513a56ed7c339875f114b56fcc430e6b753fed` was **not** byte-identical
  to its predecessor; this assembly further changes its author header only.
  Expression credit covers the original work and the later adaptation.
- [FiniteTypePoints](../SchemeProperties/FiniteTypePoints.lean) is a
  *group-free adaptation*, not a byte-identical copy, of Lattice's earlier
  `AlgebraicGroups/GroupScheme/FiniteTypePoints.lean` (introduced in
  `c7e733af2be663831fb80dc6e0f6abe2e3a31bea`). **Formalization Worker A**
  selected and adjusted the scheme-level portion in `430325fe1d8a2062fa5dd761e63c57867cee832f`;
  group-object refinements remain outside this file. Credit both the original
  expression and the later reduction/repair.
- [SheafFinitePresentation](../SchemeProperties/SheafFinitePresentation.lean)
  adapts **Prism**'s original Formal Frontier source-research proof in
  `source-weibel-k-book/WeibelKBook/Experiments/ChapterI5FiniteLocalBasis.lean`
  (accepted source-project merge `17705e5300d38fe7b6b6627398951f3f3caf6190`).
  **Formalization Worker B** produced the reusable theorem in
  `9e7b69d2f1b42699bf5d6b41571742da5281611e` (author Task
  `hive-request-78616bcc1a783c3488af68463119d676cdc761c6`, UID
  `23f8f5d6-05ce-487f-91cf-a0c048ef86d4`); **Anchor** later corrected
  its explanatory docstring without changing the theorem.
- [ModuleTensorRestriction](../SchemeProperties/ModuleTensorRestriction.lean)
  was authored by **Anchor** in `d75484469001a6395ceccd0302938720de9e9d0e`
  using a **Formalization Worker A** research prototype (Task
  `hive-request-12aaba4334aba97748c6abed3e680e97f58ba490`, UID
  `53801539-1b78-4318-85a2-663db71f5031`). That prototype was research,
  not itself previously accepted library code.
- [ModuleTensorLocalization](../SchemeProperties/ModuleTensorLocalization.lean)
  was extracted into accepted library code by **Formalization Worker A** in
  `e37e4a0953238658dabfd27c4c28d91245f99a17` (Task
  `hive-request-af88a58c491e687defa9f4a0161dde3ea5307ac4`, UID
  `a17fb1fe-7c07-4be2-88ef-280510105e11`) from **Anchor**'s earlier
  unreviewed basic-open/localization research. The production proof and its
  research predecessor have different review and acceptance statuses.

Other recorded later changes matter: Worker B's `fbf96d925efa4eb54b27fa3e605cc6f33d9166d9`
adds a **private** étale-section helper and the public
`geometricallyConnected_of_connectedSpace_of_section` to Worker A's earlier
[ComponentFibers](../SchemeProperties/ComponentFibers.lean) module;
Worker A's `b8771ba83ed49c0b9348290c1255bc5acb8b1a33` makes
`toComponentScheme` flat; `d19c81d6f72244328744f6011a34f4167eee0255`
renames the [component-product](../SchemeProperties/ComponentProduct.lean)
map API; `789059b338b7b023c67ff6b5f124a8ceb3cff22c` extends
[NoetherianComponents](../SchemeProperties/NoetherianComponents.lean);
`064fea3` clarifies the [finite-presentation](../SchemeProperties/SheafFinitePresentation.lean)
assumptions. Git authorship and module headers require reading together; a
header by itself is not a complete change ledger.

Worker B's subsequently accepted ordinary changes in `ed2bf20790fbcbe7fa9152a9cc10e3ddc0b9008a`
and `04513a56ed7c339875f114b56fcc430e6b753fed` repair seven earlier native-lint
exceptions and generalize the standalone [Torsion](../SchemeProperties/Torsion.lean)
API to any commutative ring and its total quotient ring. Those revisions do
**not** broaden the integral-affine generic-point equivalence in
[ModuleProperties](../SchemeProperties/ModuleProperties.lean). The same native
successor at `49a3c7e71850f5e7913c1423f33ccbcc7c89703e` changed
`ComponentBaseChange` after its earlier equality comparison: native module
imports/public section and `@[expose]` on `toConnectedComponentsSpec` replace
the historical byte-identical blob. Earlier comparisons cannot validate the
present module.

## Sources, dependencies and notices

### Native API documentation and adapter

**Anchor** assembled the standalone Markdown adapter and its data controls from
the Scheme native documentation records for source commit
`a05b182aa17ea7cd1a591ec7b60aa7d6f2b6704c`. The adapter develops the project's
earlier Spectral Stone Duality adapter at
`fec5431c12ef74d4438a850ce0e1222e76e24298`, using Scheme's own fixed input
hashes, 73 module records and 381 displayed sites. It does not reuse Spectral's
declaration counts or dependency-translation rules.

**Formalization Worker A** authored the 77 explicitly labeled explanatory notes
for sites without a source docstring (Task
`hive-request-c1cbba100249283b8f9db55e54894ee463f87db2`, UID
`59377920-9335-4380-9dc5-5e2541e7b1ae`, contribution
`6fdf101a17f18bb69eeabf00f8ddae71e958dc3c`). Anchor checked their native
headers, source ranges and statement scope before including them byte-for-byte.
They are authored explanations, not text emitted by doc-gen4 or new Lean
declarations. Neither this attribution nor data validation transfers proof,
independent release-review or source-coverage acceptance.

### Native finite-presentation promotion

The [site-generic transport](../SchemeProperties/SheafFinitePresentationTransport.lean),
[scheme-module finite presentation](../SchemeProperties/ModuleFinitePresentation.lean),
[direct clients](../Test/FinitePresentationClient.lean) and
[standalone guide](FinitePresentations.md) adapt reviewed incubator source at
`05148a771446f8b00bddf36b6af72f9c430834d9` without importing its Git ancestry.
**Prism** developed the original generic and tilde constructions and the
same-finite-quasicoherent-witness affine refinement. **Formalization Worker B**
adapted the native API, clients and guide in original Task
`hive-request-889e4f46f3bdf27bdedb362ee6259c9d0564e57e` (UID
`21a872d7-a565-4f28-b2f8-5eae65e02474`) and transferred the modules and
documentation in Task `hive-request-c188a7b61cec0b11919933ddbae7367b7e535918`
(UID `91c509cb-33b1-46e1-a20f-46a2fd73ac50`). The destination contribution
completed its own independent promotion and release review, integration and
publication in release `193d4fe284cf1de71b168c198ad7b24a6eb71d39`, separately
from the earlier independent review of its incubator origins.

The affine-chart argument adapts mathlib's native
`Scheme.Modules.exists_isOpenCover_presentation`: retain **Weihong Xu**'s 2024
copyright and Apache-2.0 notice and the original authors **Kevin Buzzard, Johan
Commelin, Amelia Livingston, Sophie Morel, Jujian Zhang, Weihong Xu, Andrew
Yang and Brian Nugent** in the scheme-module source header. Mathlib supplies
the native presentations, quasicoherent data and tilde construction; no
collective project credit replaces these notices.

### Relative rational-map composition transfer

The [native partial- and rational-map composition lemmas](../SchemeProperties/RationalMapComposition.lean),
[private direct clients](../Test/RationalMapCompositionClient.lean) and
[standalone guide](RationalMapComposition.md) transfer an isolated, independently
reviewed incubator contribution without importing incubator Git ancestry.
**Formalization Worker B** developed the original proofs and clients in Hive Task
`hive-request-d04a528c8fefc542b1e53f2a0d565eecd90fde23` (UID
`94b1be7d-b4fc-4bc6-8fcf-c08d31f48c9e`) and prepared this Scheme Properties
transfer in Hive Task `hive-request-fb8c186a9915829afa350a73e09f7dfd98df6c89`
(UID `ccb5a70b-e209-413c-af50-ee0b4a733e97`). **Atlas** supplied scope
and research guidance and coordinates destination acceptance. These proofs
reuse mathlib's native rational-map definitions and over-base APIs by **Andrew
Yang** and **Justus Springer**, and native composition by **Justus Springer**;
they do not copy a mathlib proof body. Earlier isolated review is distinct
from destination review, integration and publication.

### Dense-open pullback transfer

The [native partial- and rational-map dense-open predicate](../SchemeProperties/DenseOpenPullback.lean),
[seven anonymous direct clients](../Test/DenseOpenPullbackClient.lean) and
[standalone guide](DenseOpenPullback.md) adapt an isolated, independently
reviewed incubator contribution without importing incubator Git ancestry.
**Formalization Worker B** developed the original proofs and clients in Hive
Task `hive-request-807aa4d70fffcd9d73f486c3fb6e8796148d8e28` (UID
`f923d027-9e1c-4025-9f69-0d3418cc6cea`); the independent origin reviewer
was **Formalization Worker A**, Hive Task
`hive-request-82a5025aa744458004ac1ae3a433b6320c603250` (UID
`36b2ab84-96a1-4ad4-8e0d-88dbfbe2576e`). The Scheme Properties static
transfer and destination documentation were prepared by **Formalization
Worker B**, Hive Task
`hive-request-e4ef017b9a63b331b0d19e462f22b5ec6fbe5722` (UID
`e1220436-76eb-4683-9b1c-13e67dadf037`). **Atlas** selected the
scope and coordinates destination review and acceptance. Accepted isolated
origins and their checks do not themselves establish destination review,
integration or release.

The module imports native mathlib partial/rational-map and quotient APIs by
**Andrew Yang**, native composition by **Justus Springer**, and mathlib's
topological density and open-map results. No native mathlib proof body or book
prose is copied; collective author credit is not a new copyright-owner claim.

### Dense-open controlled composition transfer

The [partial- and rational-map controlled composition](../SchemeProperties/DenseOpenComposition.lean),
[eleven private direct clients](../Test/DenseOpenCompositionClient.lean) and
[focused guide](DenseOpenComposition.md) transport the separately accepted
isolated incubator donor `b592c13ff04fc9b8b87ef615c622f9a1e8e1ef86`
without importing incubator Git ancestry. Original proof and client author:
**Formalization Worker A**, Hive Task
`hive-request-88f7e0381e230ddb7382fca45acdad9fcaddc87d` (UID
`7485a247-b32b-4e4b-8676-620b0767d1d4`). Its independent reviewer was
**Formalization Worker B**, Hive Task
`hive-request-aa51c817f2d174ce3d4e1bae7a204474b5a8caf3` (UID
`93c114a8-14c5-4444-8464-543ee2256fb1`). The destination
preparation of these files is by
**Formalization Worker B**, Hive Task
`hive-request-b4b2d2931e4e737ce3ffdaf4a86197647cddb27b` (UID
`32ab736c-88f7-4102-9d4d-d26e5b324924`). **Atlas** selected the scope and
coordinates destination review, acceptance, integration and publication;
origin acceptance is not destination approval.

The original mathlib partial/rational-map and quotient APIs are by **Andrew
Yang**. This module imports the dense-open predicate instead of copying its
proof body; unlike that predicate, the controlled-composition implementation
*adapts native composition proof expression* from mathlib's
`Birational/Composition.lean` by **Justus Springer**. Its source header retains
Springer's 2026 copyright, Apache-2.0 license and original author notice,
alongside Formal Frontier Agents. These credits do not assert collective
copyright ownership or copying of book prose or source PDFs.

### Dense-open controlled-composition closure transfer

The [partial- and rational-map pullback closure theorems](../SchemeProperties/DenseOpenCompositionClosure.lean),
[six private generic clients](../Test/DenseOpenCompositionClosureClient.lean)
and [standalone guide](DenseOpenCompositionClosure.md) transfer the accepted
isolated incubator donor `89a5653ef18bbfbb27165c6e5936dca88d2fb65c`
onto Scheme Properties base `d11ffbbaf064f66593a41425cc21f67132dd3d88`
without importing incubator Git ancestry. Original author: **Formalization
Worker A**, Hive Task
`hive-request-c948f27e37b152b7fb56b55980796bc16ccc3637` (UID
`eea5b0b3-750d-4571-bae3-e75a6715ce2b`). Fresh independent isolated
review: **Formalization Worker B**, Hive Task
`hive-request-b637d7d6e6606cd6cfd579411796b175b72dd3bf` (UID
`3d9e8b64-3947-4cbf-9907-2d7bba95a28f`). **Atlas** accepted only that
isolated donor at the earlier transfer-preparation stage and coordinated
separate destination review, acceptance, integration and release. This static
destination transfer is by
**Formalization Worker B**, Hive Task
`hive-request-31b8b3ab25d622527d49e076c72164745c5c17a2` (UID
`f55e2f85-3d9e-48c1-8475-39cb612988e0`). Its code depends on the
separately accepted dense-open predicate (#200) and controlled-composition
operation (#203), whose distinct origin and transfer credits appear above.
Neither isolated acceptance nor this transfer by itself asserts source coverage
or destination publication. Subsequently, on 2026-09-29, closure reached
separate accepted/integrated Scheme Properties main
`dc40583057f29dda1b9d81394ba10869e2ce6ea2` and the
[verified official private-GitHub release `2f467da`](https://github.com/FormalFrontier/scheme-properties/commit/2f467da9150694b0c6366cd9125b047a7f7d76cb)
with the same tree; the preparation-stage wording above is historical, not a
current pending-review or pending-release claim.

The partial-map domain-normalization proof expression **adapts** the
Apache-2.0 native partial-composition domain branch by **Justus Springer**
in mathlib's `Birational/Composition.lean`, not his stronger associativity
theorem or its geometric assumptions. Its producer preserves Springer's
individual copyright and original author/license notice. The rational-map
proof uses **Andrew Yang**'s imported native quotient and representative
interfaces. No book prose, source PDF or complete external proof is copied;
mathematical inspiration is distinct from this adapted formal expression.

### Dense-open controlled-composition associativity transfer

The [partial- and rational-map associativity laws](../SchemeProperties/DenseOpenCompositionAssociativity.lean),
[five generic private client uses](../Test/DenseOpenCompositionAssociativityClient.lean)
and [standalone guide](DenseOpenCompositionAssociativity.md) adapt the accepted
isolated incubator donor `026707accc8303e154ef50b21af18fe1e3cedeb8`
onto accepted Scheme Properties main
`dc40583057f29dda1b9d81394ba10869e2ce6ea2`, without importing
incubator Git ancestry. The original mathematical proof was developed by
**Formalization Worker A**, Hive Task
`hive-request-69616d7fe5460055b4648b613de060b3b9a53707` (UID
`60c0c692-5e8c-491f-ae71-e425b2f2819b`), with independent mathematical
review by **Formalization Worker B**, Hive Task
`hive-request-95e5b178fcb09017bde550b582d7503ccb6236f9` (UID
`ae05da79-8d09-4687-a940-8751df527c55`). The Lean donor and generic
private client were authored by **Formalization Worker A**, Hive Task
`hive-request-91717799a7a2d48c3108e31b5d775c364e892b7d` (UID
`f7615715-523e-4ffe-9e06-0d72210ffefe`), with fresh independent
isolated code review by **Formalization Worker B**, Hive Task
`hive-request-8f45b48b5fb25cf3cf5051995c9e8f073f8fec2c` (UID
`aaab5a07-79f3-4aa4-b584-7bbaafa33602`). This destination static
transfer is by **Formalization Worker B**, Hive Task
`hive-request-a8a05288817501f97ef6e286cb60114c169ae5a8` (UID
`3029ee1b-883f-4265-9a82-45870f421447`). **Atlas** owns separate
destination review, acceptance, integration and publication; the donor
acceptance is not destination certification or source coverage.

The partial-map proof adapts **Justus Springer**'s native Apache-2.0
partial-composition **domain and hom/morphism normalization** from mathlib's
`Birational/Composition.lean`, retaining his authentic 2026 copyright,
individual author and license notice in the producer. It does not import the
stronger geometric assumptions of native `PartialMap.comp_assoc`. The
rational-map proof imports **Andrew Yang**'s existing quotient and
representative interfaces; it does not copy those mathlib proofs. The
accepted dense-open predicate, operation and closure retain their distinct
contributor credits above. No selected-source prose or PDF is copied.

### Controlled dense-open composition over a base transfer

The two [common-base preservation lemmas](../SchemeProperties/DenseOpenCompositionOver.lean),
[five private generic clients](../Test/DenseOpenCompositionOverClient.lean)
and [standalone guide](DenseOpenCompositionOver.md) adapt the independently
accepted *isolated* incubator donor
`ca314988f69afd77a1e7010678d92917c957134e` onto accepted Scheme
Properties main `91c8a5621a6410568183b55d60b8bcace832a24c`, without
importing incubator Git ancestry. Original donor author: **Formalization
Worker B**, Hive Task
`hive-request-5661a06674dafb5829660f4b9a743ffdb93c3d80` (UID
`1d6aee74-dee3-48bc-829f-fb75f94fb841`). Independent isolated review:
**Formalization Worker A**, Hive Task
`hive-request-14519b787df658fed3e4d8842cf939ab26a9619b` (UID
`fa09a5dd-5607-4180-977d-5c04c3847550`). Destination static
transfer: **Formalization Worker B**, Hive Task
`hive-request-dcea208125ec931be38b0d72b65e6e1fd842afaf` (UID
`15a63375-1cd2-4e7c-99c9-14b3c9ac98e3`). **Atlas** owns scope,
separate destination review, acceptance, integration and publication; the
isolated acceptance does not certify the destination or source coverage.

The new partial-map structure-triangle proof expression adapts the preceding
Formal Frontier [RationalMapComposition proof in official Scheme Properties
`1af9eb14b0e3a0679cf6eac0ed59e186a4a6c636`](https://github.com/FormalFrontier/scheme-properties/blob/1af9eb14b0e3a0679cf6eac0ed59e186a4a6c636/SchemeProperties/RationalMapComposition.lean),
original **Formalization Worker B** Hive Task
`hive-request-d04a528c8fefc542b1e53f2a0d565eecd90fde23` (UID
`94b1be7d-b4fc-4bc6-8fcf-c08d31f48c9e`). This is separate from
**Andrew Yang**'s imported mathlib native partial/rational-map and
relative-base interfaces and **Justus Springer**'s imported composition and
image-isomorphism interfaces. The producer retains their authentic individual
copyright, author and Apache-2.0 notices. No mathlib proof body, book prose
or source PDF is copied by this transfer.

### Controlled dense-open composition unit laws transfer

The [six native partial- and rational-map identity and unit laws](../SchemeProperties/DenseOpenCompositionUnits.lean),
[eight private direct-client uses](../Test/DenseOpenCompositionUnitsClient.lean)
and [standalone guide](DenseOpenCompositionUnits.md) adapt accepted isolated
incubator donor `8c497c355201861c9e9dcfb761641821efb0d892`
onto Scheme Properties main `a7981d5e5043e56c2ac249ebc8f1f3d443a87f68`,
without importing incubator Git ancestry. Original mathematical exposition:
**Formalization Worker B**, Hive Task
`hive-request-5a3488b7ca1e4f6997cddc0cb74914632b13f9d7` (UID
`3d432155-94e0-4c87-972a-5372c288ee82`), commit
`6ae192dace00fb0b515700569b7fe35d7c517d6f`; its independent bounded
mathematical reviewer: **Formalization Worker A**, Hive Task
`hive-request-3cf5607d42071177506a487107669e8c40a4c557` (UID
`2c014263-9556-4b24-a443-e68f0efc727b`), report
`03ee6c5624d9dc721bb8d2085be99d17e000610c`. Atlas accepted that
uncompiled bounded mathematics separately; it does not establish source
correspondence or coverage. Original Lean proof and direct-client author:
**Formalization Worker B**, Hive Task
`hive-request-debf1d41b24dffe995a9c0116d5ab55ce735872a` (UID
`2663c185-ee34-4a49-9ef8-033eb82d984e`); corrected fresh independent
isolated reviewer: **Formalization Worker A**, Hive Task
`hive-request-9b07af21e37ebb5bdfe44c9ea367df0e49b1cd9b` (UID
`c2b25534-663c-4720-b5f5-3d1fbd55259e`), report
`79baf3a4e19cf0a9d227c25cf390daf29054e9e6`. Destination static
transfer: **Formalization Worker B**, Hive Task
`hive-request-77872a2c8aab42c2f34e60d6845e36e02f879696` (UID
`308d428c-1a11-4265-af31-e153c2ba1898`). **Atlas** owns separate
destination review, acceptance, integration and publication; no future
reviewer, release or source-coverage decision is asserted here.

The partial-map proof **adapts** **Justus Springer**'s native Apache-2.0
partial-composition **domain and morphism normalization** from mathlib's
`Mathlib/AlgebraicGeometry/Birational/Composition.lean`. Its producer
retains Springer's authentic 2026 copyright, license and individual author
notice. It imports **Andrew Yang**'s native partial/rational quotient and
representative APIs rather than copying their proof bodies. The existing
dense-open predicate and controlled-composition operation remain separately
credited above. No book prose or selected-source PDF is copied.

### Dense-open pullback and dominance transfer

The [four native partial- and rational-map dominance results](../SchemeProperties/DenseOpenPullbackDominance.lean),
[four private direct-import examples](../Test/DenseOpenPullbackDominanceClient.lean)
and [standalone guide](DenseOpenPullbackDominance.md) adapt the independently
reviewed isolated incubator donor `e115570b05adebd1d4b9b5f8c3cc7fbd4a1025ad`
onto accepted Scheme Properties parent `3ac7ce0b9fad473f9856e1353c6a9c563f609c0b`
without importing incubator Git ancestry. The existing
[dense-open predicate](../SchemeProperties/DenseOpenPullback.lean) is reused
unchanged; its original contribution and destination transfer have distinct
credits above.

The original converse mathematics was developed by **Formalization Worker B**,
Hive Task `hive-request-7cd28f4c844b22e75425fed3fe9d76930b8f1ab7`
(UID `dc65fd6d-d7e8-400b-ab99-01d2b1ae8971`), and independently reviewed by
**Formalization Worker A**, Hive Task
`hive-request-c83093c0267bb0c99bc85cd4fc3a8bb3bfadb402` (UID
`123f5562-d5c1-4e9f-8f74-f23d9e9fffaa`). Original Lean proofs and direct
client: **Formalization Worker B**, Hive Task
`hive-request-79825c8e94f5352c8e75fb6a16c1859618eef289` (UID
`6a8d0c63-9b1a-4eca-b111-4b8898be6498`); fresh independent isolated
code review: **Formalization Worker A**, Hive Task
`hive-request-32455516cc0f7e39cda54d2b9f621859bff7af3c` (UID
`11d896b5-c1ad-42a3-8fb6-45158421d024`). Destination static transfer:
**Formalization Worker B**, Hive Task
`hive-request-ce06b62b5f59999150c88d30d70f9d878166052a` (UID
`ddece77d-7c0f-4a45-bb62-e8028d116843`). **Atlas** owns separate
destination review, acceptance, integration and publication. Neither the
original mathematics review, isolated code review nor this transfer establishes
destination checks, source correspondence or coverage.

This producer reuses native dominance and composition APIs by **Justus Springer**
(2026, Apache-2.0) and native partial/rational quotient and representative APIs
by **Andrew Yang** (2024, Apache-2.0). It imports these APIs without copying
mathlib proof bodies, native notices, book prose or selected-source PDFs; its
collective author header is not a new individual copyright-owner claim.

### Dense-open rational-map category transfer

The [separate dense-open rational-map category](../SchemeProperties/DenseOpenRationalCategory.lean),
[ten private direct-import uses](../Test/DenseOpenRationalCategoryClient.lean)
and [standalone guide](DenseOpenRationalCategory.md) originate in an accepted,
independently reviewed isolated contribution. The original Lean producer and
client were authored by **Formalization Worker B**, Hive Task
`hive-request-5dddb84e29ead5285f0f04a3a789ef2bbbba5ab2` (UID
`98ba3720-425d-446f-b379-5a9923750483`), with fresh independent code
review by **Formalization Worker A**, Hive Task
`hive-request-54a8a955252d210ee71b79542316081791f940ec` (UID
`92b2ab48-068b-4e7a-8deb-3fd75339022e`). The mapped destination transfer
and its documentation are by **Formalization Worker B**, Hive Task
`hive-request-f48594a321bf5e61f02b4b51eba77fadcb8f5874` (UID
`c1a90b5e-8609-4f96-b1ed-740a57277ddc`). This does not itself certify
destination checks, independent destination review, acceptance, release or
source correspondence; **Atlas** owns those decisions.

This category reuses mathlib's native partial/quotient rational-map interfaces
by **Andrew Yang** (2024, Apache-2.0), native composition and dominance
interfaces by **Justus Springer** (2026, Apache-2.0), and the separately
credited Formal Frontier dense-open predicate and laws above. Neither their
proof bodies nor book prose are copied, and the existing individual notices
and rights remain with their respective dependencies.

### Relative dense-open rational-map category transfer

The [arbitrary-base relative category](../SchemeProperties/DenseOpenRationalCategoryOver.lean),
[parameterized private direct-import client](../Test/DenseOpenRationalCategoryOverClient.lean)
and [standalone guide](DenseOpenRationalCategoryOver.md) transfer mathematically
unchanged from accepted isolated incubator commit
`dd5a565615cebfedda5782f81b031fa6f86426f6`. Original code and client
were authored by **Formalization Worker B**, Hive Task
`hive-request-6d6b2ce9689faeb78ffe46a43d9ee825f518a883` (UID
`f5a73c6c-7142-4861-9425-4f029a6c2531`), with fresh independent code
review by **Formalization Worker A**, Hive Task
`hive-request-502dd6aec7bbea7778dfaccd1af6bab82ee21e81` (UID
`d96178c1-f41e-464d-8e83-eac2fb730a60`). The destination transfer and
documentation are by **Formalization Worker B**, Hive Task
`hive-request-19a08a0a2be9ed8de115c36f507f890f64e5b1d2` (UID
`b91d3b22-1c39-4ca2-9613-cf1b2c871f09`). This credit does not establish
destination review, acceptance, publication or source correspondence; Atlas
owns those decisions.

The category imports mathlib's native quotient rational maps by **Andrew Yang**
and composition/dominance interfaces by **Justus Springer**, together with
separately credited Formal Frontier Scheme Properties prerequisites. Existing
Apache-2.0 and individual notices remain intact; no native third-party proof
body or book prose is copied.

### Integral dominant rational-map category transfer

The [native integral dominant category and actual equivalence](../SchemeProperties/IntegralDominantRationalCategory.lean),
[16 private direct-import uses](../Test/IntegralDominantRationalCategoryClient.lean)
and [standalone guide](IntegralDominantRationalCategory.md) adapt an accepted,
independently reviewed isolated formalization. Original Lean producer and client:
**Formalization Worker B**, Hive Task
`hive-request-6578645040a9541fd367025960140a3d5b3f585c` (UID
`5c0c2397-ff96-4b8c-a394-f9feffcced91`); fresh independent original
code reviewer: **Formalization Worker A**, Hive Task
`hive-request-9e8653485902800ee34995abb3334a18268d10d6` (UID
`11de8905-8357-477f-baad-feb8ddfd6328`). The destination import/client
mapping, guide, navigation and metadata are by **Formalization Worker B**,
Hive Task `hive-request-f31d3ef0a6e40ce3d35f8771cad9aeb4df44e38f`
(UID `54fbb40b-e876-43de-be4a-e3028bf73628`). These distinct records
do not themselves certify a destination build, independent destination review,
acceptance, official publication or source correspondence; **Atlas** owns
those separate decisions.

This producer reuses the preceding separately credited Formal Frontier
`DenseOpenRationalScheme` category and pullback/dominance results. Mathlib's
native partial/quotient rational-map and representative interfaces credit
**Andrew Yang** (2024, Apache-2.0); native composition/dominance credits
**Justus Springer** (2026, Apache-2.0). Mathlib's
`ObjectProperty.FullSubcategory` interface credits **Kim Morrison**,
**Reid Barton** and **Joël Riou**; its equivalence interface credits
**Tim Baumann**, **Stephen Morgan**, **Kim Morrison** and
**Floris van Doorn**. This contribution imports those APIs without copying
their proof bodies, modifying their individual rights/notices or claiming that
the transfer author originated those interfaces. No book prose or PDF is
copied; the collective author header does not assert an individual copyright
owner.

### Integral dominant rational-map category over a base transfer

The [relative integral equivalence](../SchemeProperties/IntegralDominantRationalCategoryOver.lean),
[private direct-import client](../Test/IntegralDominantRationalCategoryOverClient.lean)
and [standalone mathematical guide](IntegralDominantRationalCategoryOver.md)
transfer the accepted isolated contribution at incubator commit
`ea10d6a06e6ce3651d928e9249f885b638612d03`. Original Lean producer and
client: **Formalization Worker B**, Hive Task
`hive-request-1e345826d9b1d55547053743ab99e34652b29b46` (UID
`c433c074-b181-4e4d-a7fd-9ee589386335`); fresh independent original
review: **Formalization Worker A**, Hive Task
`hive-request-1edf5a1d6f9088338287b1d598b68d64ddc4a187` (UID
`d5a8dcf3-be40-48b2-abc7-3c06a1aac50e`). The direct-import mapping,
guide, navigation and metadata are by **Formalization Worker B**, Hive Task
`hive-request-f9f8be5490fdebc5c1728e3e148e5cbec1cec7ae` (UID
`66550bc3-abed-405c-9aa1-1a5fac0046fe`). Neither the original review nor
this transfer is destination review, acceptance, publication or source
correspondence; **Atlas** owns those separate decisions.

The relative development reuses the separately credited general relative
category and published absolute integral comparison, as well as native
mathlib quotient rational maps and representative APIs by **Andrew Yang**,
composition/dominance by **Justus Springer** and the existing mathlib
full-subcategory/equivalence interfaces by **Kim Morrison**, **Reid Barton**,
**Joël Riou**, **Tim Baumann**, **Stephen Morgan** and **Floris van Doorn**.
Their Apache-2.0 and individual notices are unchanged. No external proof
bodies, book prose or source PDFs are copied; the collective author header
does not claim individual copyright ownership.

### Function-field pullback transfer

The [function-field producer](../SchemeProperties/RationalFunctionFieldPullback.lean),
[private nine-check client](../Test/RationalFunctionFieldPullbackClient.lean)
and [guide](RationalFunctionFieldPullback.md) adapt the accepted isolated
incubator donor **C** `b12dd71cc82cf4d7e89be0a7aa17698db25c89bb`.
Original Lean producer, client and guide: **Formalization Worker B**, Hive Task
`hive-request-45ec92982fd621dea0c3d8fa7999482383e838e5` (UID
`9b188db4-3721-41af-9e9e-26e7a2516940`). The original-input computation
**E** `ed745af5a8c87e298a0892b7b804e2e9b11d25fc` records 20 producer and
9 client declaration origins, including private/generated ones, under the
standard-three axiom policy. Original fresh independent review **R**
`a6fd63a04b64a2462d7f61b8b9c902350cf21f86` is by
**Formalization Worker A**, Hive Task
`hive-request-99cd293f130a1929d31b8f0981b3d481e65d5d27` (UID
`654a911f-88fb-4cf1-bd80-939f4ad9f7cf`). The static first-home assessment
`d03105cc9cad1b05fb1d0ac39280e8d91f12291d` is by **Formalization Worker B**,
Hive Task `hive-request-dc780993c7cf56c81a295f0ec45d77c6a03ddb3f`
(UID `be1f66c6-15fe-4fd0-8f5b-0e7dabe480af`); it is not a proof review.

The source-preserving destination transfer, client import/namespace adaptation,
guide and registration are by **Formalization Worker B**, Hive Task
`hive-request-da7bb6e97ffd60b048814e8cd66bc2c396248f9f` (UID
`a8aa23f8-144b-4dd2-8ab3-aafeab714111`) on integrated Scheme Properties
parent `72cdc26cef35faf902da1339f41544c1eaa45071`. At the original
September 30, 2026 transfer preparation before Scheme Properties PR #138's
later review, destination review, configured build/complete transitive axiom
evidence, acceptance, integration, separate official publication and source
correspondence were distinct and pending; **Atlas** makes the destination
decisions. At that same snapshot, the preceding integral relative category's
official release was separately pending and not bundled with this transfer.
These are preparation-time statuses, not a later current verdict; consult
Scheme Properties PR #138 and Atlas's incubator #285 for subsequent
exact-revision evidence and decisions.

The new producer imports the existing Scheme Properties integral dominant
native rational-map category **within the same project**. Its other direct
imports are mathlib's native composition and function-field/stalk interfaces.
Mathlib's quotient/representative work by **Andrew Yang** and native
composition/dominance by **Justus Springer** remain imported rather than
copied; their individual notices and Apache-2.0 rights remain with mathlib.
No external proof body, book prose or source PDF is copied here. The original
donor and the new code have collective Formal Frontier credit and project
Apache-2.0 headers, not a claim of individual copyright ownership or of
rights clearance for unrelated expressions. The original source-vakil-foag
provenance assessment does not itself certify source coverage or destination
acceptance.

### Function-field faithfulness companion transfer

The [faithfulness producer](../SchemeProperties/RationalFunctionFieldFaithfulness.lean),
[two-check private client](../Test/RationalFunctionFieldFaithfulnessClient.lean)
and [guide](RationalFunctionFieldFaithfulness.md) transfer the accepted isolated
incubator code at `f16ea30a36a0e9bd54da3cdfe01f8a1197d0e25a` (tree
`6bf42c9ccea09c5a53cc18cefb3d6cffcba71e2e`), without importing its Git
ancestry. The producer's original Apache-2.0 and collective Formal Frontier
Agents header is retained byte-for-byte; the client changes only its focused
import and namespace. Original code and guide author: **Formalization Worker B**,
Hive Task `hive-request-38437de3e668bfa5c29ef2962f213698a233a49d`
(UID `467ca61f-faf0-4f49-9275-81c26b859379`). Original focused computation
and complete six-declaration transitive standard-three audit: evidence child
`2d326b46d716a473a8017d0f84595cb95a3661b9`, under incubator #298.
Fresh independent exact-code reviewer: **Formalization Worker A**, Hive Task
`hive-request-670e711a24ab4f5b1a8e68d66915618693209d25`
(UID `2307ced4-09cb-4792-8aa2-ee3b1e2434d8`), report child
`4d1c087cc989577fdc40b2f3f10af5cdcdc484ed`. Atlas's isolated code
acceptance is incubator #298 comment 69659; it is not destination acceptance.

The distinct Scheme Properties destination transfer, documentation and metadata
are by **Formalization Worker B**, Hive Task
`hive-request-dfdb3ea93e18a230a34e477af43360cde4b8a5af`
(UID `9ff3b4bf-6b9c-4f30-858f-8f84f641a742`), from parent
`327d2632b0e5a6b1f2ffa4a6ef1dce209e6b6e81`. Transfer authorship is
not a fresh mathematical code review or a destination CI verdict. The companion
imports the existing [native function-field pullback](../SchemeProperties/RationalFunctionFieldPullback.lean)
and [integral category](../SchemeProperties/IntegralDominantRationalCategory.lean)
within the same project, which in turn import rather than copy mathlib's
quotient and representative interfaces by **Andrew Yang** and native
composition/dominance interfaces by **Justus Springer**. Their individual
notices and Apache-2.0 rights remain with mathlib; no external proof body,
source PDF or book text is copied by this transfer. Collective author credit
neither replaces individual provenance nor asserts copyright ownership. No
selected-source correspondence or coverage follows from this code transfer.

### Function-field reconstruction transfer

The [reconstruction producer](../SchemeProperties/RationalFunctionFieldReconstruction.lean)
is byte-exact from accepted isolated incubator commit
`b005883db9858f4c60853bf4a1036c227705cd11` (tree
`f9a061d839f1b3e7683d3d79159787dffc056483`); the
[six-theorem private client](../Test/RationalFunctionFieldReconstructionClient.lean)
changes only its ordinary import and namespace, and the
[standalone guide](RationalFunctionFieldReconstruction.md) is adapted to this
project. No incubator Git ancestry enters the destination. Original code and
guide author: **Formalization Worker B**, Hive Task
`hive-request-e8eeaa02d1ec40354e7a1da9970e42bd227b87b3` (UID
`6832e81a-bdb8-4a91-bae8-a9297e7d1cdc`). Frozen static mathematical
assessment: **Formalization Worker B**, Task
`hive-request-db5ea915841abb5aa56291ee19084f8ef4c7b513` (UID
`719eaa9e-19f6-482a-aa29-e809910d452a`); independent static reviewer:
**Formalization Worker A**, Task
`hive-request-9cae30e4ecac45b9815bdc86658bd84aca8ea040` (UID
`d39d7811-f2d5-4052-b6ac-722cde41830b`). Fresh independent exact-code
reviewer: **Formalization Worker A**, Task
`hive-request-9162c98d0912c703237c5b31fc764303f7843d52` (UID
`e22519cb-340e-4781-80d4-8c649a737788`). The separate destination
transfer, client adaptation, guide, README, metadata and credit are by
**Formalization Worker B**, Task
`hive-request-e3f1439c1332a34fcf2912df1b387dd5c858b074` (UID
`81db2cf9-890e-4696-80fb-899d15f5ebd0`), from accepted Scheme main
`1852ce8115e020abed87f6f9bf2081ace9341b4d`. This authorship and the
original isolated review are not a destination CI or fresh promotion review;
destination acceptance, release and source coverage remain separate.

The producer imports the separately credited same-project
[pullback](../SchemeProperties/RationalFunctionFieldPullback.lean) and
[faithfulness](../SchemeProperties/RationalFunctionFieldFaithfulness.lean)
without duplicating their code. It uses mathlib native spreading, stalk,
quotient and dominance interfaces; mathlib quotient and representative APIs
are credited to **Andrew Yang**, and native composition/dominance APIs to
**Justus Springer**, with their own notices and Apache-2.0 rights retained by
mathlib. Original producer/client headers retain `SPDX-License-Identifier:
Apache-2.0` and collective authorship; no source PDF, book prose or imported
third-party proof body is copied. Collective credit does not assert an
individual copyright owner or itself establish independent rights clearance.

### Function-field inverse transfer

The [inverse producer](../SchemeProperties/RationalFunctionFieldInverse.lean)
copies the original project's Apache-2.0 Lean bytes exactly from isolated
incubator commit `db402a20a6e76ec62720d9b28ce045fa874bf6e1` (true tree
`f8c599f94e86cb1e6e1e9f36ac9f0522b66762c1`, sole accepted parent
`ccb5886051c4f6c006e956483c1e983d35144966`). The
[three-theorem private client](../Test/RationalFunctionFieldInverseClient.lean)
adapts that donor's ordinary import and adds only a destination namespace;
the [standalone guide](RationalFunctionFieldInverse.md) adapts its original
mathematical exposition. No incubator Git ancestry enters this destination.

The frozen static mathematical argument was authored by **Formalization Worker
B**, Hive Task `hive-request-b7543b20151ccad863ac1811c291a8f92d0b6931`
(UID `70e238b7-5c9d-4823-b446-107bf789661b`) and independently assessed by
**Formalization Worker A**, Task
`hive-request-1ede527b2a9f5a3c079b5ef66dc7ff9ac3258d6f` (UID
`63800e6d-5cae-4e30-b85e-8b53ffa2c8aa`). The donor producer, client and
guide were authored by **Formalization Worker B**, Task
`hive-request-d08fb8e66816eeda60f176adb2a705118712a0bf` (UID
`20e3853c-7a2c-44db-b98e-e26f5a4cb0f8`) and independently reviewed at
exact C by **Formalization Worker A**, Task
`hive-request-b3aa2ab1ace57a60d8225302ef3f5053442efa16` (UID
`d1e145b8-7bb5-4425-bd3c-be736e2951b5`). **Formalization Worker B**,
Task `hive-request-50a6b8f62bfe8ef71ff3eebc1e00b9c2fb376413` (UID
`4b59b8cd-4509-4cc7-a6d8-86aad520a21f`), separately transferred the
accepted isolated result onto protected Scheme main
`b23c7766c551a1b3228d6a190cc820f21e65fcc4` (the tree of verified
official release `5e98363b3a8738544d966d1603ace4df183573d4`). Original
donor code review is **not** fresh destination review, native destination
proof checking, release acceptance or selected-source coverage.

This producer imports the same-project
[reconstruction](../SchemeProperties/RationalFunctionFieldReconstruction.lean),
[faithfulness](../SchemeProperties/RationalFunctionFieldFaithfulness.lean) and
[integral chosen-base category](../SchemeProperties/IntegralDominantRationalCategoryOver.lean)
interfaces rather than duplicating predecessor proofs. It imports mathlib's
native quotient/representative and generic-stalk APIs by **Andrew Yang** and
native composition/dominance interfaces by **Justus Springer**, without
copying their proof bodies; individual notices and Apache-2.0 rights remain
upstream. The unchanged donor Lean headers retain collective authorship and
`SPDX-License-Identifier: Apache-2.0`, not an individual copyright assertion.
No source PDF, book prose or additional third-party proof body is copied.
These credits do not substitute for independent release rights review or
assert source correspondence, source coverage or publication of this transfer.

### Mathematical sources and third-party notices

Ravi Vakil's *The Rising Sea: Foundations of Algebraic Geometry* (author-hosted
October 21, 2025 draft) and J. S. Milne's *Algebraic Groups: The Theory of
Group Schemes of Finite Type over a Field*, along with Charles Weibel's
*The K-book* (Chapter I, §5), motivate, among other topics, local scheme
properties, finite-étale components and finite local presentations. Mathematical attribution
does **not** license copying book text: no source PDFs, page extracts or book
prose are included here. Passage-level reading and coverage decisions stay in
their separate source projects; this library's formal expression is credited
by its project Git history and the adapted-expression precedents above.

This project imports [mathlib](../lakefile.toml), `coherent-modules` and
`finite-etale-algebras`, rather than vendoring their Lean files. Applicable
licenses, authentic copyright/author notices and any `NOTICE` obligations
remain with those dependencies; this project's collective credit does not
replace them. Twenty-one original project Lean-file headers previously stated
`Copyright (c) 2026 Formal Frontier Authors` without a verified owner. Their
project-generated origin was traced to actual introduction commits (including
the earlier project `algebraic-groups` for adapted modules); this assembly
removes that unsupported *ownership assertion* and keeps the SPDX notice and
collective author credit. Earlier individual worker attribution survives in
`Contributors:` headers and the Git/credits record. No verified third-party
ownership notice was removed. Exact origin/rights checks and any remaining
uncertainties are retained separately for independent release review; this is
not itself a rights-clearance verdict. Git author names and AI assistance
neither establish ownership nor waive actual rights questions.

Formal Frontier maintainers and task-profile workers developed and reviewed
Lean statements, proof terms, examples and prose with AI assistance. This
description is a contributor/process account, not a claim of independent
human authorship, historical clearance paperwork, or a substitute for
mathematical and legal release review.
