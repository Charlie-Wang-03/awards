import JSP000404Research.LargeTransitionAngleQuotientBound
import JSP000404Research.PositiveTransitionAngleAlignment
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Rotate
import Mathlib.Tactic

/-!
# Positionwise upper bounds from large positive-transition angles

This is the converse quantitative package to
`PositiveTransitionAngleAlignment`.

At a support-three centre with exactly three sign transitions, every positive
quotient is a transition.  In the lower Sendov branch, if the actual angle at
such a slot is at least

  ((n-2)-2*delta)*lambda,

then the corresponding quotient is at most three.

The statement is packaged as a `List.Forall₂` relation and is invariant under
simultaneous cyclic rotation, so it can be applied after pinning the ray to the
top centre.
-/

namespace JSP000404Research

open Real

def LargePositiveTransitionQuotientLeThree
    (threshold : ℝ) (qs : List ℕ) (As : List ℝ) : Prop :=
  List.Forall₂
    (fun q A => q ≠ 0 → threshold ≤ A → q ≤ 3)
    qs As

theorem largePositiveTransitionQuotientLeThree_rotate
    {threshold : ℝ} {qs : List ℕ} {As : List ℝ}
    (h : LargePositiveTransitionQuotientLeThree threshold qs As)
    (k : ℕ) :
    LargePositiveTransitionQuotientLeThree threshold
      (qs.rotate k) (As.rotate k) := by
  unfold LargePositiveTransitionQuotientLeThree at h ⊢
  have hlen : qs.length = As.length :=
    List.Forall₂.length_eq h
  rw [List.rotate_eq_drop_append_take_mod,
      List.rotate_eq_drop_append_take_mod]
  rw [← hlen]
  exact List.rel_append
    (List.forall₂_drop (k % qs.length) h)
    (List.forall₂_take (k % qs.length) h)

theorem consecutive_large_positive_transition_quotients_le_three
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {n : ℕ} {delta t lam : ℝ}
    (hn2 : 2 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
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
        (consecutiveRayQuotients hp i t prev rs)) :
    LargePositiveTransitionQuotientLeThree
      ((((n - 2 : ℕ) : ℝ) - 2 * delta) * lam)
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
      unfold LargePositiveTransitionQuotientLeThree
      apply List.Forall₂.cons
      · intro hq0 hlarge
        exact ordinary_transition_quotient_le_three_of_large_angle
          hp hn2 hdelta0 hdeltaHalf ht hlam
          i horder (hhead hq0) hlarge
      · exact ih r hnod.2 hpair.2 hrest

theorem centre_three_transition_large_positive_quotients_le_three
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {n : ℕ} {delta t lam : ℝ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hn2 : 2 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
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
      listPositiveCount (quotientList t C.gaps) = 3) :
    LargePositiveTransitionQuotientLeThree
      ((((n - 2 : ℕ) : ℝ) - 2 * delta) * lam)
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

  have hnodup :
      (first :: rest).Nodup := by
    simpa [hrays] using C.nodup
  have hsorted :
      (first :: rest).Pairwise
        (fun a b =>
          rayThetaAt hp i a ≤ rayThetaAt hp i b) := by
    simpa [hrays] using C.theta_sorted

  have hord :
      LargePositiveTransitionQuotientLeThree
        ((((n - 2 : ℕ) : ℝ) - 2 * delta) * lam)
        ordQs
        (consecutiveRayAngles (p := p) i first rest) := by
    dsimp [ordQs, signsOrd] at hpositiveOrd ⊢
    exact consecutive_large_positive_transition_quotients_le_three
      hp hn2 hdelta0 hdeltaHalf ht hlam
      i first rest hnodup hsorted hpositiveOrd

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
      ((((n - 2 : ℕ) : ℝ) - 2 * delta) * lam) ≤
          EuclideanGeometry.angle
            (p last.1) (p i) (p first.1) →
      wrapQ ≤ 3 := by
    intro hq0 hlarge
    have htransition := hpositiveWrap hq0
    rw [hlastSign] at htransition
    dsimp [wrapQ]
    exact wrap_transition_quotient_le_three_of_large_angle
      hp hn2 hdelta0 hdeltaHalf ht hlam
      i horder htransition hlarge

  unfold LargePositiveTransitionQuotientLeThree at hord ⊢
  rw [hqdecomp]
  unfold cyclicRayAngles
  exact List.rel_append
    hord
    (List.Forall₂.cons hwrapRel List.Forall₂.nil)

#print axioms largePositiveTransitionQuotientLeThree_rotate
#print axioms consecutive_large_positive_transition_quotients_le_three
#print axioms centre_three_transition_large_positive_quotients_le_three

end JSP000404Research
