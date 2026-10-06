import JSP000404Research.ResidualWholeCubeProgressClassification
import JSP000404Research.ResidualWholeCubeUnifiedRank
import JSP000404Research.ResidualWholeCubeWellFounded
import JSP000404Research.ResidualTranslatedCubeRematchQuotient
import JSP000404Research.ResidualWholeCubePartnerSaturation
import JSP000404Research.ResidualThreeWholeCubeMinimalCoreCollapse
import JSP000404Research.ProjectionWholeCubeDiscoveryRankPositive

/-!
# Whole-cube finite-state recursion closure surface

This module is the compile/assembly surface for the current whole-cube hard
branch.

The assembled facts are:

* every second-coordinate continuation is either genuine progress or an exact
  rematching contraction;
* genuine progress is measured by one natural rank combining Boolean payload
  and discovery of the at-most-three active whole-cube coordinates;
* exact T/T full rematches are identified in a translated-cube quotient;
* after all three projected-loss whole-cube coordinates are populated, every
  further projected-loss rematch repeats an existing state;
* the saturated three-partner state is impossible in the genuine planar
  second layer;
* consequently every genuinely discovered coordinate registry has cardinality
  at most two, so the planar discovery rank is always positive.

This closes the finite-state whole-cube terminal itself.  It is still not the
final arbitrary-cardinality capacity theorem: the remaining task is to connect
this well-founded/quotiented recursion surface to the global Hall-capacity
assembly.
-/

namespace JSP000404Research

theorem wholeCube_finite_state_rank_base
    {n payload : ℕ}
    (coords : Finset (Fin n)) :
    OrderedEdgeColoring.wholeCubeProgressRank payload coords
      =
    4 * payload +
      OrderedEdgeColoring.wholeCubeDiscoveryRank coords := by
  rfl

#print axioms wholeCube_finite_state_rank_base

end JSP000404Research
