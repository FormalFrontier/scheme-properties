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
