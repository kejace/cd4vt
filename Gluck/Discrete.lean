/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Discrete.TabachnikovFourActive
import Gluck.Discrete.LocalContinuity
import Gluck.Discrete.TabachnikovConverse
import Gluck.Discrete.TabachnikovCharacterization
import Gluck.Discrete.SideTangentChordSeparation
import Gluck.Discrete.SideTangentCircle
import Gluck.Discrete.SideTangentContact
import Gluck.Discrete.SideTangentConverse
import Gluck.Discrete.SideTangentDFV
import Gluck.Discrete.SideTangentFan
import Gluck.Discrete.SideTangentField
import Gluck.Discrete.SideTangentForward
import Gluck.Discrete.SideTangentNecessityBalance
import Gluck.Discrete.SideTangentPerturbation
import Gluck.Discrete.SideTangentProjectiveFan
import Gluck.Discrete.SideTangentReconstruction
import Gluck.Discrete.SideTangentRegularFan
import Gluck.Discrete.SideTangentScaledPolygon
import Gluck.Discrete.SideTangentSignBlocks
import Gluck.Discrete.SideTangentSquareFan
import Gluck.Discrete.SideTangentSquareLabels
import Gluck.Discrete.GlobalContinuity.LevelBands
import Gluck.Discrete.GlobalContinuity.EnclosingCircleObstruction

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
