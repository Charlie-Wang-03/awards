import JSP000404Research.ResidualCompletionOverlapRewire
import JSP000404Research.PlanarCrossingHardOverlapRewire
import JSP000404Research.ResidualCompletionIntersectionMass
import JSP000404Research.ResidualSafeFlipDoubleMatching
import JSP000404Research.ResidualHardSoftOverlapPartition
import JSP000404Research.ResidualHardFaceGlobalTransport
import JSP000404Research.ResidualSaturatedHardRemainder
import JSP000404Research.PlanarLowerBranchSaturatedHardReduction
import JSP000404Research.ResidualRigidPaidDefectReduction
import JSP000404Research.PlanarLowerBranchPaidRigidReduction
import JSP000404Research.DirectionDataRigidHardTransportRefutation
import JSP000404Research.ResidualUnpaidRigidExactDebt
import JSP000404Research.ResidualUnpaidRigidPartialReservation
import JSP000404Research.ResidualUnpaidRigidNetPaymentReduction
import JSP000404Research.PlanarLowerBranchAscendingNetPaymentReduction
import JSP000404Research.ResidualUnpaidHardTerminalClassification
import JSP000404Research.ResidualDescendingRigidExactDebt
import JSP000404Research.ResidualBothMixedRigidSurplusPacking
import JSP000404Research.ResidualBothMixedRigidNetReduction
import JSP000404Research.ResidualTerminalDoubleSaturatedHard
import JSP000404Research.PlanarLowerBranchBothMixedNetPaymentReduction

/-!
# Verified local overlap-routing entrypoint for JSP-000404

Import this module to rebuild the actual kernel-checked local chain:
completion-cube accounting, exact global edge-owned Boolean-face overlap mass,
profile balance, safe-flip no-hole obstruction, triangular
exclusion, strict interior cube blocker, exact retained edge colour,
genuine planar AngleCap retained-separated residual rewire,\nand the globally injective hard-overlap WHOLE-FACE transport (conditional\non an available outward/inactive colour at every hard carrier).

The legacy all-modules entrypoint JSP000404Research.lean currently has
unrelated historical Lean failures and is not a proof certification target.
The admitted global-payment WIP theorem is deliberately NOT imported here.

The new full-face transport proves a global singleton+soft overlap mass bound,\nbut does NOT prove that the transport-colour hypothesis always holds.\nIts destinations are still covered words.\nThe main lower-branch global payment obligation remains OPEN.
-/

/-!
The new exact ascending-rigid net-payment chain is included in this
SORRY-FREE independent verification umbrella. The admitted WIP remains
excluded. Checked modules prove exact local debt, globally disjoint
partial reservations, genuine-Boolean-word net accounting, planar
conditional implication, and lower-saturated / transportable terminal
classification of the still-unpaid hard carriers. They do NOT
establish the final open planar inequality.
-/

/-!
# Additional proof frontier (2026-10-12)

This sorry-free umbrella now includes both directions of mixed-rigid
hard-carrier partial surplus reservations. The new simultaneous
matching theorem reserves old whole-face credits, lower surplus
on ascending rigid faces, and upper surplus on descending rigid
faces without reuse. The exact Boolean-word net-payment equivalence
reduces the remaining rigid hard carriers, under the usual one-layer
profile budget, to OUTGOING-TRANSPORTABLE or DOUBLY SATURATED.

The conditional planar bridge is included. The WIP entry with
one explicit sorry and sorryAx is deliberately NOT imported.
Passing this umbrella checks reductions, NOT the unsolved global
planar payment inequality or final JSP-000404 theorem.
-/
