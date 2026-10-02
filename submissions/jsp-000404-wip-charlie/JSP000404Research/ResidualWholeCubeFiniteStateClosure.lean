import JSP000404Research.ResidualWholeCubeProgressClassification
import JSP000404Research.ResidualWholeCubeUnifiedRank
import JSP000404Research.ResidualWholeCubeWellFounded
import JSP000404Research.ResidualTranslatedCubeRematchQuotient
import JSP000404Research.ResidualWholeCubePartnerSaturation
import JSP000404Research.ResidualThreeWholeCubeMinimalCoreCollapse

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
* the saturated three-partner state is a 7-of-8 four-vertex deficient
  obstruction, and inside an inclusion-minimal deficient core it collapses the
  core exactly to those four vertices.

This is still a research terminal, not the final arbitrary-cardinality
capacity theorem: the exact four-vertex terminal must still be discharged or
absorbed by the global Hall argument.
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
