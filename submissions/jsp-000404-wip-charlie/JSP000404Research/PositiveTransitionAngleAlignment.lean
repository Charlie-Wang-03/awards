import JSP000404Research.TransitionQuotientLargeAngle
import JSP000404Research.TransitionPositiveExactAlignment
import JSP000404Research.CyclicActualAngles
import JSP000404Research.ListPositiveMemberBound
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Rotate
import Mathlib.Tactic

/-!
# Positive transition quotients carry large actual angles

In an exact support-three / three-transition centre, the positive quotient
positions and the sign-transition positions coincide.  If the total quotient
mass is n, every positive quotient is at most n-2.  Each such transition
therefore carries a genuine Euclidean angle strictly larger than

  (1+delta) * lambda.

This file packages that statement positionwise and proves that the package is
invariant under simultaneous cyclic rotation of the quotient and actual-angle
lists.  It is designed to be consumed by the pinned middle-hidden six-point
terminal.
-/

namespace JSP000404Research

open Real

def PositiveQuotientAngleGt
    (threshold : ℝ) (qs : List ℕ) (As : List ℝ) : Prop :=
  List.Forall₂ (fun q A => q ≠ 0 → threshold < A) qs As

theorem positiveQuotientAngleGt_rotate
    {threshold : ℝ} {qs : List ℕ} {As : List ℝ}
    (h : PositiveQuotientAngleGt threshold qs As)
    (k : ℕ) :
    PositiveQuotientAngleGt threshold
      (qs.rotate k) (As.rotate k) := by
  unfold PositiveQuotientAngleGt at h ⊢
  have hlen : qs.length = As.length :=
    List.Forall₂.length_eq h
  rw [List.rotate_eq_drop_append_take_mod,
      List.rotate_eq_drop_append_take_mod]
  rw [← hlen]
  exact List.rel_append
    (List.forall₂_drop (k % qs.length) h)
    (List.forall₂_take (k % qs.length) h)

theorem positiveOnlyOnTransition_append_singleton_prefix
    (a b : Bool)
    (signs : List Bool) (qs : List ℕ) (q : ℕ)
    (hlen : signs.length = qs.length)
    (h :
      PositiveOnlyOnTransition
        a (signs ++ [b]) (qs ++ [q])) :
    PositiveOnlyOnTransition a signs qs := by
  induction signs generalizing a qs with
  | nil =>
      cases qs with
      | nil =>
          trivial
      | cons q0 qs =>
          simp at hlen
  | cons x xs ih =>
      cases qs with
      | nil =>
          simp at hlen
      | cons q0 qs =>
          simp at hlen
          simp only [List.cons_append,
            PositiveOnlyOnTransition] at h
          exact ⟨h.1, ih x qs hlen h.2⟩

theorem positiveOnlyOnTransition_appended_singleton_step
    (a b : Bool)
    (signs : List Bool) (qs : List ℕ) (q : ℕ)
    (hlen : signs.length = qs.length)
    (h :
      PositiveOnlyOnTransition
        a (signs ++ [b]) (qs ++ [q])) :
    q ≠ 0 → boolLastFrom a signs ≠ b := by
  induction signs generalizing a qs with
  | nil =>
      cases qs with
      | nil =>
          simpa [PositiveOnlyOnTransition, boolLastFrom] using h.1
      | cons q0 qs =>
          simp at hlen
  | cons x xs ih =>
      cases qs with
      | nil =>
          simp at hlen
      | cons q0 qs =>
          simp at hlen
          simp only [List.cons_append,
            PositiveOnlyOnTransition] at h
          have hlast :=
            ih x qs hlen h.2
          simpa [boolLastFrom] using hlast

theorem consecutiveRayQuotients_length
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) (t : ℝ)
    (prev : OtherVertex i)
    (rs : List (OtherVertex i)) :
    (consecutiveRayQuotients hp i t prev rs).length =
      rs.length := by
  induction rs generalizing prev with
  | nil =>
      rfl
  | cons r rs ih =>
      simp [consecutiveRayQuotients, ih]

theorem consecutive_positive_transition_angles_large
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {n : ℕ} {delta t lam : ℝ}
    (hn2 : 2 ≤ n)
    (htpos : 0 < t)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (i : V)
    (prev : OtherVertex i)
    (rs : List (OtherVertex i))
    (hnodup : (prev :: rs).Nodup)
    (hsorted :
      (prev :: rs).Pairwise
        (fun a b =>
          rayThetaAt hp i a ≤ rayThetaAt hp i b))
    (hpositive :
      PositiveOnlyOnTransition
        (raySignAt hp i prev)
        (rs.map (raySignAt hp i))
        (consecutiveRayQuotients hp i t prev rs))
    (hbound :
      ∀ q ∈ consecutiveRayQuotients hp i t prev rs,
        q ≠ 0 → q ≤ n - 2) :
    PositiveQuotientAngleGt
      ((1 + delta) * lam)
      (consecutiveRayQuotients hp i t prev rs)
      (consecutiveRayAngles (p := p) i prev rs) := by
  induction rs generalizing prev with
  | nil =>
      exact List.Forall₂.nil
  | cons r rs ih =>
      have hnod := List.nodup_cons.mp hnodup
      have hpair := List.pairwise_cons.mp hsorted
      have horder :
          rayThetaAt hp i prev ≤ rayThetaAt hp i r :=
        hpair.1 r (by simp)
      rcases hpositive with ⟨hhead, hrest⟩
      unfold PositiveQuotientAngleGt
      apply List.Forall₂.cons
      · intro hq0
        have hsign :
            raySignAt hp i prev ≠ raySignAt hp i r :=
          hhead hq0
        have hqle :
            Nat.floor
                (t * ((rayThetaAt hp i r -
                  rayThetaAt hp i prev) / Real.pi))
              ≤ n - 2 := by
          apply hbound
          · simp [consecutiveRayQuotients]
          · exact hq0
        exact
          actual_angle_gt_one_add_delta_mul_lam_of_transition_quotient_le
            hp hn2 htpos ht hlam i horder hsign hqle
      · apply ih r hnod.2 hpair.2 hrest
        intro q hqmem hq0
        apply hbound q
        · simp [consecutiveRayQuotients, hqmem]
        · exact hq0

/-- Full cyclic centre statement.  The nonempty tail condition only excludes
the one-ray degenerate cycle; every support-three application satisfies it
automatically. -/
theorem centre_three_transition_positive_angles_large
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {n : ℕ} {delta t lam : ℝ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hn2 : 2 ≤ n)
    (htpos : 0 < t)
    (htone : 1 ≤ t)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (i : V)
    (C : CentreProjectiveCycle hp i)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (hrays : C.rays = first :: rest)
    (hrest : rest ≠ [])
    (htrans :
      boolTransitionCountFrom
        (raySignAt hp i first)
        (liftedCentreSignPath hp i first rest) = 3)
    (hsupport :
      listPositiveCount (quotientList t C.gaps) = 3)
    (hqsum :
      (quotientList t C.gaps).sum = n) :
    PositiveQuotientAngleGt
      ((1 + delta) * lam)
      (quotientList t C.gaps)
      (cyclicRayAngles (p := p) i first rest) := by
  let ordQs :=
    consecutiveRayQuotients hp i t first rest
  let wrapQ :=
    wrapRayQuotient hp i t first (rest.getLastD first)
  let signsOrd := rest.map (raySignAt hp i)

  have hchanges :=
    centre_changesOnlyOnPositive
      hp hcap htpos htone hlam i C first rest hrays
  have hpositive0 :=
    support_three_three_transitions_all_positive_are_transitions
      (raySignAt hp i first)
      (liftedCentreSignPath hp i first rest)
      (quotientList t C.gaps)
      hchanges htrans hsupport

  have hqdecomp :
      quotientList t C.gaps = ordQs ++ [wrapQ] := by
    dsimp [ordQs, wrapQ]
    exact centreQuotientList_decompose
      C t first rest hrays

  have hpositive :
      PositiveOnlyOnTransition
        (raySignAt hp i first)
        (signsOrd ++ [!raySignAt hp i first])
        (ordQs ++ [wrapQ]) := by
    rw [← hqdecomp]
    simpa [signsOrd, liftedCentreSignPath] using hpositive0

  have hlenOrd : signsOrd.length = ordQs.length := by
    dsimp [signsOrd, ordQs]
    rw [List.length_map,
        consecutiveRayQuotients_length]

  have hpositiveOrd :
      PositiveOnlyOnTransition
        (raySignAt hp i first)
        signsOrd ordQs :=
    positiveOnlyOnTransition_append_singleton_prefix
      (raySignAt hp i first)
      (!raySignAt hp i first)
      signsOrd ordQs wrapQ hlenOrd hpositive

  have hpositiveWrap :
      wrapQ ≠ 0 →
        boolLastFrom (raySignAt hp i first) signsOrd ≠
          !raySignAt hp i first :=
    positiveOnlyOnTransition_appended_singleton_step
      (raySignAt hp i first)
      (!raySignAt hp i first)
      signsOrd ordQs wrapQ hlenOrd hpositive

  have hboundAll :
      ∀ q ∈ quotientList t C.gaps,
        q ≠ 0 → q ≤ n - 2 := by
    intro q hqmem hq0
    exact
      positive_member_le_n_sub_two_of_support_three_sum
        (quotientList t C.gaps)
        hsupport hqsum hqmem hq0

  have hboundOrd :
      ∀ q ∈ ordQs, q ≠ 0 → q ≤ n - 2 := by
    intro q hqmem hq0
    apply hboundAll q
    · rw [hqdecomp]
      exact List.mem_append_left _ hqmem
    · exact hq0

  have hnodup :
      (first :: rest).Nodup := by
    simpa [hrays] using C.nodup
  have hsorted :
      (first :: rest).Pairwise
        (fun a b =>
          rayThetaAt hp i a ≤ rayThetaAt hp i b) := by
    simpa [hrays] using C.theta_sorted

  have hord :
      PositiveQuotientAngleGt
        ((1 + delta) * lam)
        ordQs
        (consecutiveRayAngles (p := p) i first rest) := by
    dsimp [ordQs, signsOrd] at hpositiveOrd hboundOrd ⊢
    exact consecutive_positive_transition_angles_large
      hp hn2 htpos ht hlam i first rest
      hnodup hsorted hpositiveOrd hboundOrd

  let last := rest.getLastD first
  have hlastMem : last ∈ rest := by
    dsimp [last]
    exact List.getLastD_mem hrest
  have hfirstLast : first ≠ last := by
    intro hEq
    subst last
    exact (List.nodup_cons.mp hnodup).1 hlastMem
  have horder :
      rayThetaAt hp i first ≤ rayThetaAt hp i last :=
    (List.pairwise_cons.mp hsorted).1 last hlastMem

  have hlastSign :
      boolLastFrom
          (raySignAt hp i first) signsOrd =
        raySignAt hp i last := by
    dsimp [signsOrd, last]
    rw [boolLastFrom_eq_getLastD, map_getLastD]

  have hwrapRel :
      wrapQ ≠ 0 →
        (1 + delta) * lam <
          EuclideanGeometry.angle
            (p last.1) (p i) (p first.1) := by
    intro hq0
    have htransition := hpositiveWrap hq0
    rw [hlastSign] at htransition
    have hqle : wrapQ ≤ n - 2 := by
      apply hboundAll wrapQ
      · rw [hqdecomp]
        simp
      · exact hq0
    dsimp [wrapQ] at hqle
    exact
      actual_angle_gt_one_add_delta_mul_lam_of_wrap_transition_quotient_le
        hp hn2 htpos ht hlam i horder htransition hqle

  unfold PositiveQuotientAngleGt at hord ⊢
  rw [hqdecomp]
  unfold cyclicRayAngles
  exact List.rel_append
    hord
    (List.Forall₂.cons hwrapRel List.Forall₂.nil)

#print axioms positiveQuotientAngleGt_rotate
#print axioms consecutive_positive_transition_angles_large
#print axioms centre_three_transition_positive_angles_large

end JSP000404Research
