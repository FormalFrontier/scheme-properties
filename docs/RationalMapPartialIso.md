# Exact rational inverses and partial isomorphisms

Import `SchemeProperties.RationalMapPartialIso` directly. The public
results live in `AlgebraicGeometry.Scheme.RationalMap` and
`AlgebraicGeometry.Scheme.PartialIso`. They require only mathlib's native
`Birational` and `Composition` modules, not a project-specific rational-map
category. A direct-import client is
`Test.RationalMapPartialIsoClient`; its declarations are
private.

## API and conventions

For same-universe integral schemes `X` and `Y`, independently supplied dominant
native quotients `forward : X ⤏ Y` and `reverse : Y ⤏ X`, and **both** native
equations

```lean
forward.comp reverse = Scheme.RationalMap.id X
reverse.comp forward = Scheme.RationalMap.id Y
```

`RationalMap.exists_partialIso_of_inverse` gives `partialIso : X.PartialIso Y`
with `partialIso.toRationalMap = forward` **and**
`partialIso.symm.toRationalMap = reverse`. `comp` is source-first: the first
equation is `reverse ∘ forward = id_X`. The exact quotients matter; the
conclusion is stronger than the existence of some unrelated birational witness.

`RationalMap.exists_partialIso_of_inverse_over` additionally accepts any
scheme `S`, independently chosen total maps `sX : X ⟶ S` and `sY : Y ⟶ S`,
and only the **one** base equation

```lean
forward.compHom sY = sX.toRationalMap
```

It returns those same two exact readbacks together with the literal equation
`partialIso.IsOver sX sY`, namely
`partialIso.iso.hom ≫ partialIso.target.ι ≫ sY =
 partialIso.source.ι ≫ sX`. The inverse's quotient base equation follows from
the other inverse law and associativity; it is not an extra hypothesis. The
same-carrier case permits two independently chosen maps `X ⟶ S`, conditional
only on the displayed base equation. There is **no** assumption of local finite
type, separatedness, integrality of `S`, or dominance of either total map.

Conversely, every `partialIso : X.PartialIso Y` has a dominant exact forward
quotient by the instance `PartialIso.toRationalMap_isDominant`; applying it to
`partialIso.symm` supplies the reverse dominance. For integral `X` and `Y`,
`PartialIso.toRationalMap_comp_symm` and
`PartialIso.symm_toRationalMap_comp` prove the two native inverse identities.
Without extra integrality assumptions, literal `partialIso.IsOver sX sY`
implies the forward and reverse quotient base equations via
`PartialIso.toRationalMap_compHom_of_isOver` and
`PartialIso.symm_toRationalMap_compHom_of_isOver`.

## Proof method and limits

Native `RationalMap.IsOver` gives an *existential* over-base partial-map
representative; an arbitrary representative need not preserve the base map.
Choose appropriate forward and reverse representatives, transfer quotient
dominance, and turn both quotient inverse equations into actual scheme-morphism
equalities on dense opens `A` and `B`. Shrink by the correctly typed inverse
images on each representative's domain: intersect `A` with the source-domain
image of the forward inverse image of `B`, and dually intersect `B` with the
reverse inverse image of `A`. Dominant composition proves these opens dense.
The two morphism equations put each restricted map's range in the other new
open. `IsOpenImmersion.lift` factors genuine scheme morphisms, and cancellation
of the mono open inclusions proves the two inverse **morphism** laws. Native
restriction preserves each exact quotient, while the over-base representative's
literal equality restricts to the resulting partial isomorphism. The converse
uses the iso inverse laws on the actual composition domain, not pointwise
agreement alone. No maximal-domain gluing, function-field inverse criterion,
categorical equivalence, reducible extension, or total isomorphism is asserted.

## Reproduction and provenance

This Scheme Properties module transfers accepted isolated incubator producer
`465dac5aed5442050f68b5c37a19f80ea4eab3c1` (tree
`0238319c90f6598d1beabd1550316ba9c1613759`, sole predecessor
`d008961405585bc555e44b0d63263c3245446491`). The destination
was originally prepared on accepted Scheme Properties development main
`813359d1e044569284c60c704e31b8c6da3d3fe5` (tree
`2af72c73c1c7434f6ed429195d43f05f16be08b2`); this corrected-parent
reconciliation instead starts at accepted main
`9420b1e51ffd332036529f12a27a0e63a5c6275e` (tree
`1be256dde2ce13f69998a57c5cd5488198219914`). The original transfer
changes only the
producer's module/public-import/public-section/warning-fatal envelope and the
client's import, namespace and module envelope; mathematical statements and
proof bodies remain unchanged. The direct-import producer needs only mathlib's
native `Birational` and `Composition` modules, not the other Scheme Properties
modules. The project pins Lean `leanprover/lean4:v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, and its separately
published dependencies in [lakefile.toml](../lakefile.toml). These GitHub
dependencies require authorized access.

From this repository, fetch its matching mathlib cache before building:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake build SchemeProperties.RationalMapPartialIso
lake build Test.RationalMapPartialIsoClient
```

The isolated donor's original successful focused builds, warning-fatal checks
and complete actual-origin, private-inclusive standard-axiom audit, together
with its independent code review, apply **only** to the unchanged isolated
input. At the original September 30, 2026 transfer preparation, before Scheme
Properties PR #151's subsequent review and original native check, this adapted
destination still required applicable native build and transitive axiom
evidence for its actual declarations (including private and generated),
independent exact-transfer review, maintainer acceptance, integration and its
own reviewed official release/publication. This is preparation history, not a
later verdict; consult PR #151 and Atlas's incubator #343 for exact-revision
evidence and decisions. Neither this guide nor that original candidate
establishes acceptance of a corrected-parent successor or selected-source
correspondence.

The STATIC/uncompiled mathematical design was authored by worker-a Hive Task
`hive-request-2e1fd02a61b9d5c8531ab957f09d5a25291595e6` (UID
`4938ad42-dab9-45e3-8607-be1af22b4791`, commit `fb7e76d77a702dbd342cbb087ae8a80d12c0b5c4`)
and independently reviewed by worker-b Hive Task
`hive-request-9288fd4177302f9a0ff2c8976fbf76818bb8c8ed` (UID
`10b57a8f-ee28-45e3-b419-f101f5735772`, commit
`5ae3029dbedf3732d6a1f2f8b3f1fd91f30a4e59`). The isolated Lean
implementation was authored by worker-b Hive Task
`hive-request-1c06cb902ef44f69070e844697c5073c3ea5dcb3` (UID
`e9f585c0-fce1-462d-87ea-63c1f2e7f47c`) and reviewed independently by
worker-a Hive Task `hive-request-149bbf92e23f16582f1061cb19c05b9d67692881`
(UID `2436b3ac-e539-4648-9542-fbd815cc37ae`). Worker-b Hive Task
`hive-request-49bf186b9fd2ccf45f922c77cac0ccde35c4e7e5` (UID
`1a0882a3-0b82-44df-ab89-230dfb5a1403`) authored this separate
transfer. These records give credit without making users depend on research
files to use the API.

Mathlib's native quotient and representative contracts were developed by
Andrew Yang, and native composition and partial-isomorphism interfaces by
Justus Springer, with other mathlib contributors; their relevant modules
are licensed Apache-2.0 and retain their own notices upstream. This producer
also retains Springer's authentic individual notice for the adapted
composition-domain expression; it does not claim his authorship of the
independent geometric argument. This project uses those native contracts and
adapts their composition/restriction proof technique with attribution,
without copying source-book prose or claiming ownership of upstream expression.
