
import JSP000404Research.ProjectionLocalDirectionValue
import JSP000404Research.AffineCyclicGapScaling
import JSP000404Research.ProjectiveGapCutRotation
import JSP000404Research.CentreStandardBandBudget
import Mathlib.Tactic

/-!
# Explicit local cycle obtained by cutting the canonical projective cycle

Fix the generic projection order and one canonical CentreProjectiveCycle.

Split its theta-sorted ray list at the global projective cut:

  low  = {theta < cut},
  high = {cut <= theta}.

Sortedness implies

  low ++ high = canonical rays.

The forward lifted branch is obtained by moving high to the front and
subtracting pi from its angles:

  (high-pi) ++ low.

ProjectionLocalDirectionValue identifies the corresponding DirectionData local
values with one uniform affine scaling of this unwrapped list.  Therefore the
ray order

  high ++ low

is a valid LocalDirectionCycle.

AffineCyclicGapScaling and ProjectiveGapCutRotation then show that its local
cyclic quotient exponent is exactly the genuine canonical centreExponent.

This closes the remaining representation bridge between the centre-gap and
standard residual/band formalisms.
-/

namespace JSP000404Research

/-- A sorted real-valued list splits exactly into the entries below a threshold
followed by those at or above it. -/
theorem filter_lt_append_filter_ge_eq_of_pairwise
    {α : Type*}
    (f : α → ℝ) (cut : ℝ)
    (xs : List α)
    (hsorted : xs.Pairwise (fun a b => f a ≤ f b)) :
    xs.filter (fun x => decide (f x < cut)) ++
      xs.filter (fun x => decide (cut ≤ f x))
      =
    xs := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hp := List.pairwise_cons.mp hsorted
      have ihTail := ih hp.2
      by_cases hx : f x < cut
      · have hnotge : ¬ cut ≤ f x := not_le_of_gt hx
        simp [hx, hnotge, ihTail]
      · have hge : cut ≤ f x := le_of_not_gt hx
        have hallGe :
            ∀ y ∈ xs, cut ≤ f y := by
          intro y hy
          exact hge.trans (hp.1 y hy)
        have hlowNil :
            xs.filter (fun y => decide (f y < cut)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro y hy
          simp only [decide_eq_true_eq]
          exact not_lt_of_ge (hallGe y hy)
        have hhighSelf :
            xs.filter (fun y => decide (cut ≤ f y)) = xs := by
          apply List.filter_eq_self.mpr
          intro y hy
          simp only [decide_eq_true_eq]
          exact hallGe y hy
        simp [hx, hge, hlowNil, hhighSelf]

namespace ProjectionOrdered

open Real

section

variable {V : Type*} [Fintype V]
variable {p : V → Plane}
variable (hp : Function.Injective p)

local instance projectionOrder :
    LinearOrder (ProjectionOrdered V) :=
  projectionLinearOrder hp

abbrev ReindexedPoint :=
  reindexedPoint p

abbrev ReindexedInjective :
    Function.Injective (ReindexedPoint (p := p)) :=
  reindexedPoint_injective hp

def projectionCutLowRays
    (i : ProjectionOrdered V)
    (C : CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    List (OtherVertex i) :=
  C.rays.filter fun j =>
    decide
      (rayThetaAt (reindexedPoint_injective hp) i j <
        projectionProjectiveCut p)

def projectionCutHighRays
    (i : ProjectionOrdered V)
    (C : CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    List (OtherVertex i) :=
  C.rays.filter fun j =>
    decide
      (projectionProjectiveCut p ≤
        rayThetaAt (reindexedPoint_injective hp) i j)

theorem projectionCut_low_append_high
    (i : ProjectionOrdered V)
    (C : CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    projectionCutLowRays hp i C ++
      projectionCutHighRays hp i C =
    C.rays := by
  exact filter_lt_append_filter_ge_eq_of_pairwise
    (fun j : OtherVertex i =>
      rayThetaAt (reindexedPoint_injective hp) i j)
    (projectionProjectiveCut p)
    C.rays C.theta_sorted

theorem mem_projectionCutLowRays_iff
    (i : ProjectionOrdered V)
    (C : CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (j : OtherVertex i) :
    j ∈ projectionCutLowRays hp i C ↔
      j ∈ C.rays ∧
      rayThetaAt (reindexedPoint_injective hp) i j <
        projectionProjectiveCut p := by
  simp [projectionCutLowRays]

theorem mem_projectionCutHighRays_iff
    (i : ProjectionOrdered V)
    (C : CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (j : OtherVertex i) :
    j ∈ projectionCutHighRays hp i C ↔
      j ∈ C.rays ∧
      projectionProjectiveCut p ≤
        rayThetaAt (reindexedPoint_injective hp) i j := by
  simp [projectionCutHighRays]

theorem projectionCutHigh_local_pairwise
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : ProjectionOrdered V)
    (C : CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    (projectionCutHighRays hp i C).Pairwise
      (fun a b =>
        (genericDirectionData_sendov hp hcap ht hlam).localDirectionValue i a ≤
        (genericDirectionData_sendov hp hcap ht hlam).localDirectionValue i b) := by
  have htheta :
      (projectionCutHighRays hp i C).Pairwise
        (fun a b =>
          rayThetaAt (reindexedPoint_injective hp) i a ≤
          rayThetaAt (reindexedPoint_injective hp) i b) := by
    unfold projectionCutHighRays
    exact C.theta_sorted.filter _
  apply List.Pairwise.imp_of_mem _ htheta
  intro a b ha hb hab
  have haCut :
      projectionProjectiveCut p ≤
        rayThetaAt (reindexedPoint_injective hp) i a :=
    ((mem_projectionCutHighRays_iff hp i C a).1 ha).2
  have hbCut :
      projectionProjectiveCut p ≤
        rayThetaAt (reindexedPoint_injective hp) i b :=
    ((mem_projectionCutHighRays_iff hp i C b).1 hb).2
  rw [genericLocalDirectionValue_eq_above_cut
        hp hcap ht hlam i a haCut,
      genericLocalDirectionValue_eq_above_cut
        hp hcap ht hlam i b hbCut]
  have hlamPos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos ht
  exact
    (div_le_div_iff_of_pos_right hlamPos).2
      (sub_le_sub_right hab (projectionProjectiveCut p))

theorem projectionCutLow_local_pairwise
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : ProjectionOrdered V)
    (C : CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    (projectionCutLowRays hp i C).Pairwise
      (fun a b =>
        (genericDirectionData_sendov hp hcap ht hlam).localDirectionValue i a ≤
        (genericDirectionData_sendov hp hcap ht hlam).localDirectionValue i b) := by
  have htheta :
      (projectionCutLowRays hp i C).Pairwise
        (fun a b =>
          rayThetaAt (reindexedPoint_injective hp) i a ≤
          rayThetaAt (reindexedPoint_injective hp) i b) := by
    unfold projectionCutLowRays
    exact C.theta_sorted.filter _
  apply List.Pairwise.imp_of_mem _ htheta
  intro a b ha hb hab
  have haCut :
      rayThetaAt (reindexedPoint_injective hp) i a <
        projectionProjectiveCut p :=
    ((mem_projectionCutLowRays_iff hp i C a).1 ha).2
  have hbCut :
      rayThetaAt (reindexedPoint_injective hp) i b <
        projectionProjectiveCut p :=
    ((mem_projectionCutLowRays_iff hp i C b).1 hb).2
  rw [genericLocalDirectionValue_eq_below_cut
        hp hcap ht hlam i a haCut,
      genericLocalDirectionValue_eq_below_cut
        hp hcap ht hlam i b hbCut]
  have hlamPos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos ht
  exact
    (div_le_div_iff_of_pos_right hlamPos).2
      (by linarith)

theorem projectionCut_cross_local_le
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : ProjectionOrdered V)
    (C : CentreProjectiveCycle (reindexedPoint_injective hp) i)
    {a b : OtherVertex i}
    (ha : a ∈ projectionCutHighRays hp i C)
    (hb : b ∈ projectionCutLowRays hp i C) :
    (genericDirectionData_sendov hp hcap ht hlam).localDirectionValue i a ≤
      (genericDirectionData_sendov hp hcap ht hlam).localDirectionValue i b := by
  have haCut :
      projectionProjectiveCut p ≤
        rayThetaAt (reindexedPoint_injective hp) i a :=
    ((mem_projectionCutHighRays_iff hp i C a).1 ha).2
  have hbCut :
      rayThetaAt (reindexedPoint_injective hp) i b <
        projectionProjectiveCut p :=
    ((mem_projectionCutLowRays_iff hp i C b).1 hb).2
  rw [genericLocalDirectionValue_eq_above_cut
        hp hcap ht hlam i a haCut,
      genericLocalDirectionValue_eq_below_cut
        hp hcap ht hlam i b hbCut]
  have hlamPos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos ht
  apply (div_le_div_iff_of_pos_right hlamPos).2
  have haPi :
      rayThetaAt (reindexedPoint_injective hp) i a < Real.pi :=
    rayThetaAt_lt_pi (reindexedPoint_injective hp) i a
  have hb0 :
      0 ≤ rayThetaAt (reindexedPoint_injective hp) i b :=
    rayThetaAt_nonneg (reindexedPoint_injective hp) i b
  linarith

theorem projectionCut_rotated_local_pairwise
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : ProjectionOrdered V)
    (C : CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    (projectionCutHighRays hp i C ++
      projectionCutLowRays hp i C).Pairwise
      (fun a b =>
        (genericDirectionData_sendov hp hcap ht hlam).localDirectionValue i a ≤
        (genericDirectionData_sendov hp hcap ht hlam).localDirectionValue i b) := by
  rw [List.pairwise_append]
  refine ⟨
    projectionCutHigh_local_pairwise hp hcap ht hlam i C,
    projectionCutLow_local_pairwise hp hcap ht hlam i C,
    ?_⟩
  intro a ha b hb
  exact projectionCut_cross_local_le
    hp hcap ht hlam i C ha hb

/-- Explicit local-direction cycle obtained from the canonical cycle by moving
the high projective block to the front. -/
noncomputable def projectionCutLocalCycle
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : ProjectionOrdered V)
    (C : CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    LocalDirectionCycle
      (genericDirectionData_sendov hp hcap ht hlam) i := by
  let low := projectionCutLowRays hp i C
  let high := projectionCutHighRays hp i C
  have hcanon : low ++ high = C.rays := by
    exact projectionCut_low_append_high hp i C
  have hrot : (low ++ high) ~r (high ++ low) :=
    List.isRotated_append
  refine
    { rays := high ++ low
      complete := ?_
      nodup := ?_
      nonempty := ?_
      value_sorted :=
        projectionCut_rotated_local_pairwise
          hp hcap ht hlam i C }
  · rw [← C.complete]
    apply Finset.ext
    intro j
    simp only [List.mem_toFinset]
    rw [← hcanon]
    exact hrot.mem_iff.symm
  · have hleft : (low ++ high).Nodup := by
      rw [hcanon]
      exact C.nodup
    exact hrot.nodup_iff.mp hleft
  · intro hnil
    have hrightLen : (high ++ low).length = 0 := by
      rw [hnil]
      rfl
    have hleftLen :
        (low ++ high).length = 0 := by
      have hpLen := hrot.perm.length_eq
      omega
    have hleftNil :
        low ++ high = [] :=
      List.length_eq_zero_iff.mp hleftLen
    rw [hcanon] at hleftNil
    exact C.nonempty hleftNil

def projectionCutLowAngles
    (i : ProjectionOrdered V)
    (C : CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    List ℝ :=
  (projectionCutLowRays hp i C).map
    (rayThetaAt (reindexedPoint_injective hp) i)

def projectionCutHighAngles
    (i : ProjectionOrdered V)
    (C : CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    List ℝ :=
  (projectionCutHighRays hp i C).map
    (rayThetaAt (reindexedPoint_injective hp) i)

theorem centreAngles_eq_cutLow_append_cutHigh
    (i : ProjectionOrdered V)
    (C : CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    C.angles =
      projectionCutLowAngles hp i C ++
        projectionCutHighAngles hp i C := by
  unfold CentreProjectiveCycle.angles
  rw [← projectionCut_low_append_high hp i C]
  simp [projectionCutLowAngles, projectionCutHighAngles]

theorem projectionCutLocalCycle_values_eq_affine_unwrapped
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : ProjectionOrdered V)
    (C : CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    (projectionCutLocalCycle hp hcap ht hlam i C).values
      =
    ((projectionCutHighAngles hp i C).map
        (fun theta => theta - Real.pi) ++
      projectionCutLowAngles hp i C).map
        (affineAngleValue
          (projectionAngleBase (genericProjectionSlope p))
          lam) := by
  unfold LocalDirectionCycle.values projectionCutLocalCycle
  simp only [List.map_append, List.map_map]
  apply congrArg₂ (· ++ ·)
  · apply List.map_congr_left
    intro j hj
    have hjHigh :
        j ∈ projectionCutHighRays hp i C := by
      simpa using hj
    have hjCut :
        projectionProjectiveCut p ≤
          rayThetaAt (reindexedPoint_injective hp) i j :=
      ((mem_projectionCutHighRays_iff hp i C j).1 hjHigh).2
    rw [genericLocalDirectionValue_eq_above_cut
          hp hcap ht hlam i j hjCut]
    unfold affineAngleValue projectionProjectiveCut
    ring
  · apply List.map_congr_left
    intro j hj
    have hjLow :
        j ∈ projectionCutLowRays hp i C := by
      simpa using hj
    have hjCut :
        rayThetaAt (reindexedPoint_injective hp) i j <
          projectionProjectiveCut p :=
      ((mem_projectionCutLowRays_iff hp i C j).1 hjLow).2
    rw [genericLocalDirectionValue_eq_below_cut
          hp hcap ht hlam i j hjCut]
    unfold affineAngleValue projectionProjectiveCut
    ring

/-- Main representation theorem: the explicitly cut local cycle has exactly
the genuine Sendov centre exponent. -/
theorem projectionCutLocalCycle_exponent_eq_centreExponent
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : ProjectionOrdered V)
    (C : CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    (projectionCutLocalCycle hp hcap ht hlam i C).exponent =
      centreExponent C t := by
  let low := projectionCutLowAngles hp i C
  let high := projectionCutHighAngles hp i C
  let unwrapped :=
    high.map (fun theta => theta - Real.pi) ++ low
  have hangles : C.angles = low ++ high := by
    exact centreAngles_eq_cutLow_append_cutHigh hp i C
  have hne : low ++ high ≠ [] := by
    intro h
    apply C.angles_nonempty
    rw [hangles]
    exact h
  have hvalues :
      (projectionCutLocalCycle hp hcap ht hlam i C).values =
        unwrapped.map
          (affineAngleValue
            (projectionAngleBase (genericProjectionSlope p))
            lam) := by
    simpa [low, high, unwrapped] using
      projectionCutLocalCycle_values_eq_affine_unwrapped
        hp hcap ht hlam i C
  unfold LocalDirectionCycle.exponent
  rw [hvalues]
  rw [linearExponent_affine_eq_projectiveExponent
      (projectionAngleBase (genericProjectionSlope p))
      lam t ht hlam unwrapped]
  have hcut :=
    listExponent_cut_rotate t low high hne
  change
    listExponent
      (quotientList t
        (normalizedProjectiveGaps unwrapped))
      =
    centreExponent C t
  rw [show unwrapped =
      high.map (fun x => x - Real.pi) ++ low by
        rfl]
  rw [hcut]
  rw [← hangles]
  exact
    listExponent_quotientList_eq_centreExponent'
      C t

#print axioms filter_lt_append_filter_ge_eq_of_pairwise
#print axioms projectionCut_low_append_high
#print axioms projectionCut_rotated_local_pairwise
#print axioms projectionCutLocalCycle
#print axioms projectionCutLocalCycle_values_eq_affine_unwrapped
#print axioms projectionCutLocalCycle_exponent_eq_centreExponent

end

end ProjectionOrdered
end JSP000404Research
