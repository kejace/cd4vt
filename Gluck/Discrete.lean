/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Gluck.Discrete.TabachnikovFourActive
public import Gluck.Discrete.LocalContinuity
public import Gluck.Discrete.TabachnikovConverse
public import Gluck.Discrete.TabachnikovCharacterization
public import Gluck.Discrete.SideTangentChordSeparation
public import Gluck.Discrete.SideTangentCircle
public import Gluck.Discrete.SideTangentContact
public import Gluck.Discrete.SideTangentConverse
public import Gluck.Discrete.SideTangentDFV
public import Gluck.Discrete.SideTangentFan
public import Gluck.Discrete.SideTangentField
public import Gluck.Discrete.SideTangentForward
public import Gluck.Discrete.SideTangentNecessityBalance
public import Gluck.Discrete.SideTangentPerturbation
public import Gluck.Discrete.SideTangentProjectiveFan
public import Gluck.Discrete.SideTangentReconstruction
public import Gluck.Discrete.SideTangentRegularFan
public import Gluck.Discrete.SideTangentScaledPolygon
public import Gluck.Discrete.SideTangentSignBlocks
public import Gluck.Discrete.SideTangentSquareFan
public import Gluck.Discrete.SideTangentSquareLabels
public import Gluck.Discrete.GlobalContinuity.LevelBands
public import Gluck.Discrete.GlobalContinuity.EnclosingCircleObstruction

/-!
# The discrete converse four-vertex theorem

Umbrella for Tabachnikov's Problem 2 (arXiv:0710.5902):
`Gluck.Discrete.tabachnikovProblem2_all` proves `TabachnikovProblem2 n` for
every `n ≥ 4`. That is, every positive cyclic curvature word of length `n`
which is constant or admits a strict four-vertex window at a positive level is
realized by a simple moderate-arc Euclidean `n`-gon with those curvatures.

At every nonconstant admissible profile the local-continuity companion selects
lengths and labelled vertices with C¹ dependence on the curvature vector.
-/
