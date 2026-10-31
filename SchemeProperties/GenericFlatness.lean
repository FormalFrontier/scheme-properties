/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.GenericFlatness.BasicOpen
public import SchemeProperties.GenericFlatness.Uniform
public import SchemeProperties.GenericFlatness.Pointed
public import SchemeProperties.GenericFlatness.Reduced

/-!
# Generic flatness and affine flat source opens

For locally finite type morphisms to integral schemes, this module provides generic flatness
on affine principal opens, on the whole preimage of a nonempty dense target open when the
morphism is quasi-compact, and on affine neighborhoods of points above the generic point
without a quasi-compactness assumption.

A surjective locally finite type morphism to a nonempty reduced scheme with finitely many
irreducible components also has a nonempty affine open of its original source on which it
is flat, without a quasi-compactness assumption. The image of this source open need not be
dense in the whole target.
-/
