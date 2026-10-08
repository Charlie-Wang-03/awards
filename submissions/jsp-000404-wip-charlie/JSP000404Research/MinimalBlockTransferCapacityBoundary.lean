import JSP000404Research.MinimalBlockSharedDeficit
import Mathlib.Tactic

/-!
# Hall transfer: a precise local-capacity and termination boundary

Deleting a vertex of a deficient Hall core while transferring its missing
private demand preserves the *global deficient inequality*, but need not
preserve local capacity.  Thus a recursive invocation of a theorem requiring
per-vertex capacity must separately discharge the transferred target's slack.

These theorems are unconditional finite-set facts, not a solution of the
all-N Sendov geometric minimax-angle problem.
-/

namespace JSP000404Research

/-- Local feasibility after transferring demand to `w` holds precisely when
the transferred amount fits the original unused local capacity at `w`. -/
theorem transfer_target_fits_local_capacity_iff
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    (demand : V → ℕ) (blocks : V → Finset W)
    (T : Finset V) (v w : V)
    (hlocal : demand w ≤ (blocks w).card) :
    addDemandAt demand w (deletedVertexTransfer demand blocks T v) w
        ≤ (blocks w).card ↔
      deletedVertexTransfer demand blocks T v
        ≤ (blocks w).card - demand w := by
  simp only [addDemandAt, ↓reduceIte]
  omega

/-- For an inclusion-minimal deficient core, the transfer is positive.
Consequently it violates the local bound at every saturated recipient,
even though the deletion-with-transfer remains globally deficient. -/
theorem minimal_deficient_transfer_deficient_but_saturated_target_invalid
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (demand : V → ℕ) (blocks : V → Finset W)
    {T : Finset V}
    (hdef : BlockDeficient demand blocks T)
    (hmin : ∀ U : Finset V, U ⊂ T → ¬ BlockDeficient demand blocks U)
    {v w : V}
    (hv : v ∈ T) (hw : w ∈ T.erase v)
    (hsaturated : demand w = (blocks w).card) :
    BlockDeficient
      (addDemandAt demand w (deletedVertexTransfer demand blocks T v))
      blocks (T.erase v)
    ∧
    (blocks w).card <
      addDemandAt demand w (deletedVertexTransfer demand blocks T v) w := by
  have hr : 0 < deletedVertexTransfer demand blocks T v :=
    minimal_deficient_deletedVertexTransfer_pos demand blocks hdef hmin hv
  constructor
  · exact minimal_deficient_delete_with_transfer_deficient
      demand blocks hdef hmin hv hw
  · simp only [addDemandAt, ↓reduceIte]
    omega

/-- Exact change of the total demand under a single vertex transfer.
The only possible decrease is the number of *private* words removed. -/
theorem transferred_total_demand_eq_original_sub_private
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (demand : V → ℕ) (blocks : V → Finset W)
    {T : Finset V} {v w : V}
    (hv : v ∈ T) (hw : w ∈ T.erase v)
    (hprivate :
      (privateBlockWords blocks T v).card ≤ demand v) :
    (∑ x ∈ T.erase v,
      addDemandAt demand w (deletedVertexTransfer demand blocks T v) x)
      =
    (∑ x ∈ T, demand x) -
      (privateBlockWords blocks T v).card := by
  have hsum :
      (∑ x ∈ T, demand x) =
        (∑ x ∈ T.erase v, demand x) + demand v := by
    rw [← Finset.sum_erase_add _ _ hv]
  rw [sum_addDemandAt demand (T.erase v) hw]
  unfold deletedVertexTransfer
  omega

/-- The total demand strictly drops on deletion exactly when some private
word is removed. This criterion is independent of the number of vertices. -/
theorem transferred_total_demand_strict_of_private_nonempty
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (demand : V → ℕ) (blocks : V → Finset W)
    {T : Finset V} {v w : V}
    (hv : v ∈ T) (hw : w ∈ T.erase v)
    (hprivate :
      (privateBlockWords blocks T v).card ≤ demand v)
    (hpos : 0 < (privateBlockWords blocks T v).card) :
    (∑ x ∈ T.erase v,
      addDemandAt demand w (deletedVertexTransfer demand blocks T v) x)
      <
    (∑ x ∈ T, demand x) := by
  rw [transferred_total_demand_eq_original_sub_private
    demand blocks hv hw hprivate]
  have hsum :
      (∑ x ∈ T, demand x) =
        (∑ x ∈ T.erase v, demand x) + demand v := by
    rw [← Finset.sum_erase_add _ _ hv]
  omega

/-- A zero-private-word transfer does not decrease the total demand.
This is a concrete boundary for any descent measure based only on demand. -/
theorem transferred_total_demand_stalls_of_no_private
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (demand : V → ℕ) (blocks : V → Finset W)
    {T : Finset V} {v w : V}
    (hv : v ∈ T) (hw : w ∈ T.erase v)
    (hzero : (privateBlockWords blocks T v).card = 0) :
    (∑ x ∈ T.erase v,
      addDemandAt demand w (deletedVertexTransfer demand blocks T v) x)
      =
    (∑ x ∈ T, demand x) := by
  have hprivate :
      (privateBlockWords blocks T v).card ≤ demand v := by
    omega
  rw [transferred_total_demand_eq_original_sub_private
    demand blocks hv hw hprivate, hzero]
  simp

#print axioms transfer_target_fits_local_capacity_iff
#print axioms minimal_deficient_transfer_deficient_but_saturated_target_invalid
#print axioms transferred_total_demand_eq_original_sub_private
#print axioms transferred_total_demand_strict_of_private_nonempty
#print axioms transferred_total_demand_stalls_of_no_private

end JSP000404Research
