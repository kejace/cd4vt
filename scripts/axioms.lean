/-
Axiom check for the theorems displayed in the paper's Lean appendix.
Run after `lake build`:  lake env lean scripts/axioms.lean
Each should report exactly [propext, Classical.choice, Quot.sound].
-/
import Gluck

#print axioms Gluck.Discrete.tabachnikov_converse_geometric
#print axioms Gluck.Discrete.tabachnikov_radius_characterization
#print axioms Gluck.Discrete.SideTangent.sideTangentConverse
#print axioms Gluck.Discrete.SideTangent.realizesSideTangent_iff_admissible
#print axioms Gluck.Discrete.localContinuousRealization_of_dfv
#print axioms Gluck.Discrete.GlobalContinuity.no_continuous_regular_hexagon_path
#print axioms Gluck.Discrete.tabachnikovProblem2_all
