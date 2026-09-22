import JSP000404Research.CentreSignPath
import JSP000404Research.SmallSameSignGapAngle
import JSP000404Research.CanonicalSignGap
import Mathlib.Tactic

/-!
# Actual Euclidean angles aligned with one centre's cyclic projective gaps

For a sorted concrete centre cycle

  r0, r1, ..., r_{m-1},

define the cyclic actual-angle list by the ordinary consecutive angles at the
centre followed by the wrap angle from r_{m-1} back to r0.

It has exactly the same positions as

  C.gaps
  quotientList t C.gaps.

At any position whose Sendov quotient is zero, the canonical sign cannot
change.  Hence the actual Euclidean angle at that position is exactly the
physical projective gap pi*g.

This provides a positionwise bridge from zero-gap remainder mass to actual
angular path length without constructing a common signed interval.
-/

namespace JSP000404Research

open Real

def consecutiveRayAngles
    {V : Type*} {p : V → Plane}
    (i : V) :
    OtherVertex i → List (OtherVertex i) → List ℝ
  | _, [] => []
  | prev, r :: rs =>
      EuclideanGeometry.angle (p prev.1) (p i) (p r.1) ::
        consecutiveRayAngles i r rs

def cyclicRayAngles
    {V : Type*} {p : V → Plane}
    (i : V)
    (first : OtherVertex i)
    (rest : List (OtherVertex i)) : List ℝ :=
  consecutiveRayAngles i first rest ++
    [EuclideanGeometry.angle
      (p (rest.getLastD first).1) (p i) (p first.1)]

theorem consecutiveRayAngles_length
    {V : Type*} {p : V → Plane}
    (i : V) (prev : OtherVertex i)
    (rs : List (OtherVertex i)) :
    (consecutiveRayAngles (p := p) i prev rs).length = rs.length := by
  induction rs generalizing prev with
  | nil => rfl
  | cons r rs ih =>
      simp [consecutiveRayAngles, ih]

theorem cyclicRayAngles_length
    {V : Type*} {p : V → Plane}
    (i : V) (first : OtherVertex i)
    (rest : List (OtherVertex i)) :
    (cyclicRayAngles (p := p) i first rest).length =
      (first :: rest).length := by
  simp [cyclicRayAngles, consecutiveRayAngles_length]

/-- Recursive alignment saying that every zero quotient position has actual
angle exactly pi times its normalized projective gap. -/
def ZeroQuotientAngleAligned :
    List ℕ → List ℝ → List ℝ → Prop
  | [], [], [] => True
  | q :: qs, g :: gs, A :: As =>
      (q = 0 → A = Real.pi * g) ∧
        ZeroQuotientAngleAligned qs gs As
  | _, _, _ => False

theorem zeroQuotientAngleAligned_length_q_gap
    {qs : List ℕ} {gs As : List ℝ}
    (h : ZeroQuotientAngleAligned qs gs As) :
    qs.length = gs.length := by
  induction qs generalizing gs As with
  | nil =>
      cases gs <;> cases As <;>
        simp [ZeroQuotientAngleAligned] at h ⊢
  | cons q qs ih =>
      cases gs <;> cases As <;>
        simp [ZeroQuotientAngleAligned] at h ⊢
      exact congrArg Nat.succ (ih h.2)

theorem zeroQuotientAngleAligned_length_q_angle
    {qs : List ℕ} {gs As : List ℝ}
    (h : ZeroQuotientAngleAligned qs gs As) :
    qs.length = As.length := by
  induction qs generalizing gs As with
  | nil =>
      cases gs <;> cases As <;>
        simp [ZeroQuotientAngleAligned] at h ⊢
  | cons q qs ih =>
      cases gs <;> cases As <;>
        simp [ZeroQuotientAngleAligned] at h ⊢
      exact congrArg Nat.succ (ih h.2)

/-- On an ordinary sorted ray chain, zero quotients have exact actual-angle
cost pi*g. -/
theorem consecutive_zeroQuotientAngleAligned
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : V)
    (prev : OtherVertex i)
    (rs : List (OtherVertex i))
    (hnodup : (prev :: rs).Nodup)
    (hsorted :
      (prev :: rs).Pairwise
        (fun a b =>
          rayThetaAt hp i a ≤ rayThetaAt hp i b)) :
    ZeroQuotientAngleAligned
      (consecutiveRayQuotients hp i t prev rs)
      ((successiveDiffsFrom
          (rayThetaAt hp i prev)
          (rs.map (rayThetaAt hp i))).map
        (fun d => d / Real.pi))
      (consecutiveRayAngles (p := p) i prev rs) := by
  induction rs generalizing prev with
  | nil =>
      simp [consecutiveRayQuotients,
        consecutiveRayAngles, successiveDiffsFrom,
        ZeroQuotientAngleAligned]
  | cons r rs ih =>
      have hnod := List.nodup_cons.mp hnodup
      have hpair := List.pairwise_cons.mp hsorted
      have hpr : prev ≠ r := by
        intro h
        subst r
        exact hnod.1 (by simp)
      have horder :
          rayThetaAt hp i prev ≤ rayThetaAt hp i r :=
        hpair.1 r (by simp)
      have hhead :
          Nat.floor
              (t * ((rayThetaAt hp i r -
                rayThetaAt hp i prev) / Real.pi)) = 0 →
          EuclideanGeometry.angle
              (p prev.1) (p i) (p r.1) =
            Real.pi *
              ((rayThetaAt hp i r -
                rayThetaAt hp i prev) / Real.pi) := by
        intro hq0
        have hsign :
            raySignAt hp i prev = raySignAt hp i r := by
          by_contra hne
          have hnonzero :=
            floor_t_mul_gap_ne_zero_of_canonical_sign_ne
              hp hcap ht hlam i hpr horder hne
          exact hnonzero hq0
        have hang :=
          actual_angle_eq_ordinary_projective_gap_of_sign_eq
            hp i horder hsign
        rw [hang]
        field_simp [Real.pi_ne_zero]
      have htail :=
        ih r hnod.2 hpair.2
      simpa [consecutiveRayQuotients,
        consecutiveRayAngles, successiveDiffsFrom,
        ZeroQuotientAngleAligned] using
        And.intro hhead htail

/-- Wrap zero quotient has the same exact actual-angle cost. -/
theorem wrap_zero_actual_angle_eq_pi_mul_gap
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : V)
    (first last : OtherVertex i)
    (hfl : first ≠ last)
    (horder :
      rayThetaAt hp i first ≤ rayThetaAt hp i last)
    (hq0 :
      wrapRayQuotient hp i t first last = 0) :
    EuclideanGeometry.angle (p last.1) (p i) (p first.1) =
      Real.pi *
        ((rayThetaAt hp i first + Real.pi -
          rayThetaAt hp i last) / Real.pi) := by
  have hsign :
      raySignAt hp i last = !raySignAt hp i first := by
    by_contra hne
    have hnonzero :=
      floor_t_mul_wrap_gap_ne_zero_of_canonical_sign_ne
        hp hcap ht hlam i hfl horder hne
    exact hnonzero (by simpa [wrapRayQuotient] using hq0)
  have hang :=
    actual_angle_eq_wrap_projective_gap_of_lifted_sign_eq
      hp i horder hsign
  rw [hang]
  field_simp [Real.pi_ne_zero]

/-- Append one aligned position to a zero-angle alignment. -/
theorem zeroQuotientAngleAligned_append_singleton
    {qs : List ℕ} {gs As : List ℝ}
    {q : ℕ} {g A : ℝ}
    (h : ZeroQuotientAngleAligned qs gs As)
    (hlast : q = 0 → A = Real.pi * g) :
    ZeroQuotientAngleAligned
      (qs ++ [q]) (gs ++ [g]) (As ++ [A]) := by
  induction qs generalizing gs As with
  | nil =>
      cases gs <;> cases As <;>
        simp [ZeroQuotientAngleAligned] at h ⊢
      simpa [ZeroQuotientAngleAligned] using hlast
  | cons q0 qs ih =>
      cases gs <;> cases As <;>
        simp [ZeroQuotientAngleAligned] at h ⊢
      exact ⟨h.1, ih h.2⟩


/-- Full concrete centre-cycle alignment.  The singleton-centre-ray degenerate
case is included: its wrap quotient is positive when t>=1, so the zero
implication is vacuous. -/
theorem centre_zeroQuotientAngleAligned
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t : ℝ}
    (ht : 0 < t)
    (htone : 1 ≤ t)
    (hlam : lam = Real.pi / t)
    (i : V)
    (C : CentreProjectiveCycle hp i)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (hrays : C.rays = first :: rest) :
    ZeroQuotientAngleAligned
      (quotientList t C.gaps)
      C.gaps
      (cyclicRayAngles (p := p) i first rest) := by
  have hnodup :
      (first :: rest).Nodup := by
    simpa [hrays] using C.nodup
  have hsorted :
      (first :: rest).Pairwise
        (fun a b =>
          rayThetaAt hp i a ≤ rayThetaAt hp i b) := by
    simpa [hrays] using C.theta_sorted
  have hord :=
    consecutive_zeroQuotientAngleAligned
      hp hcap ht hlam i first rest hnodup hsorted
  rw [centreQuotientList_decompose C t first rest hrays]
  rw [CentreProjectiveCycle.gaps,
      CentreProjectiveCycle.angles, hrays]
  simp only [List.map_cons, normalizedProjectiveGaps,
    projectiveGaps, List.map_append, List.map_singleton]
  unfold cyclicRayAngles
  have hgapOrd :
      ((successiveDiffsFrom
          (rayThetaAt hp i first)
          (rest.map (rayThetaAt hp i))).map
        (fun d => d / Real.pi)) =
      ((successiveDiffsFrom
          (rayThetaAt hp i first)
          (rest.map (rayThetaAt hp i))).map
        (fun d => d / Real.pi)) := rfl
  cases hrest : rest with
  | nil =>
      subst rest
      simp only [consecutiveRayQuotients,
        consecutiveRayAngles, List.map_nil,
        successiveDiffsFrom, List.append_nil,
        List.getLastD_nil]
      have hwrapNonzero :
          wrapRayQuotient hp i t first first ≠ 0 := by
        unfold wrapRayQuotient
        have harg :
            t * ((rayThetaAt hp i first + Real.pi -
              rayThetaAt hp i first) / Real.pi) = t := by
          field_simp [Real.pi_ne_zero]
        rw [harg]
        have hfloor : 1 ≤ Nat.floor t := by
          apply Nat.le_floor ht.le
          exact_mod_cast htone
        omega
      simp [ZeroQuotientAngleAligned, hwrapNonzero,
        wrapRayQuotient]
  | cons r rs =>
      have hlastMem :
          (r :: rs).getLastD first ∈ r :: rs :=
        List.getLastD_mem (by simp)
      have hfl :
          first ≠ (r :: rs).getLastD first := by
        intro h
        have htailNo := (List.nodup_cons.mp hnodup).1
        apply htailNo
        simpa [h] using hlastMem
      have horder :
          rayThetaAt hp i first ≤
            rayThetaAt hp i ((r :: rs).getLastD first) := by
        exact (List.pairwise_cons.mp hsorted).1 _
          hlastMem
      have hwrap :
          wrapRayQuotient hp i t first
              ((r :: rs).getLastD first) = 0 →
            EuclideanGeometry.angle
                (p ((r :: rs).getLastD first).1)
                (p i) (p first.1)
              =
            Real.pi *
              ((rayThetaAt hp i first + Real.pi -
                rayThetaAt hp i ((r :: rs).getLastD first)) /
                Real.pi) :=
        wrap_zero_actual_angle_eq_pi_mul_gap
          hp hcap ht hlam i first
          ((r :: rs).getLastD first)
          hfl horder
      simpa [ZeroQuotientAngleAligned,
        wrapRayQuotient, List.getLastD_cons] using
        zeroQuotientAngleAligned_append_singleton
          hord hwrap


def listZeroAngleMass : List ℕ → List ℝ → ℝ
  | [], [] => 0
  | q :: qs, A :: As =>
      (if q = 0 then A else 0) + listZeroAngleMass qs As
  | _, _ => 0

/-- Positionwise exactness sums to an exact equality between zero-angle mass
and pi times zero-gap mass. -/
theorem listZeroAngleMass_eq_pi_mul_listZeroGapMass
    {qs : List ℕ} {gs As : List ℝ}
    (h : ZeroQuotientAngleAligned qs gs As) :
    listZeroAngleMass qs As =
      Real.pi * listZeroGapMass qs gs := by
  induction qs generalizing gs As with
  | nil =>
      cases gs <;> cases As <;>
        simp [ZeroQuotientAngleAligned,
          listZeroAngleMass, listZeroGapMass] at h ⊢
  | cons q qs ih =>
      cases gs <;> cases As <;>
        simp [ZeroQuotientAngleAligned] at h
      rename_i g gs A As
      rcases h with ⟨hhead, htail⟩
      have ihtail := ih htail
      by_cases hq : q = 0
      · subst q
        have hA := hhead rfl
        simp [listZeroAngleMass, listZeroGapMass,
          hA, ihtail]
        ring
      · simp [listZeroAngleMass, listZeroGapMass,
          hq, ihtail]

theorem listZeroAngleMass_nonneg
    (qs : List ℕ) (As : List ℝ)
    (hA0 : ∀ A ∈ As, 0 ≤ A) :
    0 ≤ listZeroAngleMass qs As := by
  induction qs generalizing As with
  | nil =>
      cases As <;> simp [listZeroAngleMass]
  | cons q qs ih =>
      cases As with
      | nil =>
          simp [listZeroAngleMass]
      | cons A As =>
          have h0 : 0 ≤ A := hA0 A (by simp)
          have htail0 : ∀ x ∈ As, 0 ≤ x := by
            intro x hx
            exact hA0 x (by simp [hx])
          have ht := ih As htail0
          by_cases hq : q = 0 <;>
            simp [listZeroAngleMass, hq, h0, ht]

/-- Concrete deficit-two/support-two centre: the total actual angle mass over
all zero quotient positions is at most delta*lambda. -/
theorem centre_zeroAngleMass_le_delta_lam
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (i : V)
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (hrays : C.rays = first :: rest) :
    listZeroAngleMass
        (quotientList t C.gaps)
        (cyclicRayAngles (p := p) i first rest)
      ≤ delta * lam := by
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have htone : 1 ≤ t := by
    rw [ht]
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have halignA :=
    centre_zeroQuotientAngleAligned
      hp hcap htpos htone hlam i C first rest hrays
  have hzeroEq :=
    listZeroAngleMass_eq_pi_mul_listZeroGapMass
      halignA
  have hqsum :=
    centre_quotientList_sum_eq_n_of_deficit_two_support_two
      C hn hdelta0 hdelta1 ht hexp hsupport
  have halignQ :=
    centreQuotient_aligned C htpos.le
  have hmass :
      t * listZeroGapMass
          (quotientList t C.gaps) C.gaps ≤ delta :=
    listZeroGapMass_scaled_le_delta
      (quotientList t C.gaps) C.gaps
      ht C.gaps_sum hqsum halignQ
  have hpiMass :
      Real.pi * listZeroGapMass
          (quotientList t C.gaps) C.gaps
        ≤ delta * lam :=
    pi_mul_width_le_delta_lam_of_scaled_width
      htpos hlam hmass
  rw [hzeroEq]
  exact hpiMass

#print axioms consecutive_zeroQuotientAngleAligned
#print axioms listZeroAngleMass_eq_pi_mul_listZeroGapMass
#print axioms centre_zeroAngleMass_le_delta_lam
#print axioms wrap_zero_actual_angle_eq_pi_mul_gap
#print axioms zeroQuotientAngleAligned_append_singleton

end JSP000404Research
