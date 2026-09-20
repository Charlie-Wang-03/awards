import JSP000404Research.OneSupportTransitionCost
import JSP000404Research.TransitionRaySplit
import JSP000404Research.TransitionGapRayAlignment
import JSP000404Research.TransitionSplitInterval
import JSP000404Research.ConcreteHighExponentExposure
import Mathlib.Tactic

/-!
# Concrete interval certificate for a one-support centre

For an actual centre whose quotient support is exactly one, this file packages
all data needed by global support-arc packing.

There is one distinguished transition quotient qe and normalized projective
gap ge such that

  qe = centreExponent + 1,
  qe <= t * ge,
  ge > 0.

Cutting the actual ray cycle at that transition yields one common-signed real
parameter interval of exact width

  pi * (1 - ge) < pi.

This statement handles both an ordinary transition and the projective wrap
transition.
-/

namespace JSP000404Research

open Real
open scoped BigOperators

/-- Full geometric/arithmetic certificate attached to one support-one centre. -/
theorem concrete_one_support_interval_certificate
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (i : V)
    (C : CentreProjectiveCycle hp i)
    (hsupport :
      positiveSupport (centreQuotient C t) = 1) :
    ∃ qe : ℕ, ∃ ge a width : ℝ, ∃ sigma : Bool,
      qe ≠ 0 ∧
      qe = centreExponent C t + 1 ∧
      (qe : ℝ) ≤ t * ge ∧
      0 < ge ∧
      width = Real.pi * (1 - ge) ∧
      0 ≤ width ∧
      width < Real.pi ∧
      (∀ j, j ≠ i →
        ∃ rho : ℝ, ∃ theta : ℝ,
          0 < rho ∧
          a ≤ theta ∧ theta ≤ a + width ∧
          p j - p i =
            rho • signedRayDirection sigma theta) := by
  obtain ⟨first, rest, hrays⟩ :
      ∃ first rest, C.rays = first :: rest := by
    cases h : C.rays with
    | nil => exact False.elim (C.nonempty h)
    | cons first rest => exact ⟨first, rest, h⟩
  let sigma0 : Bool := raySignAt hp i first
  have ht1 : 1 ≤ t :=
    sendov_scale_one_le hn hdelta0 ht
  have htpos : 0 < t :=
    lt_of_lt_of_le zero_lt_one ht1
  have hchanges :
      ChangesOnlyOnPositive
        sigma0
        (liftedCentreSignPath hp i first rest)
        (quotientList t C.gaps) := by
    dsimp [sigma0]
    exact centre_changesOnlyOnPositive
      hp hcap htpos ht1 hlam i C first rest hrays
  have hlast :
      boolLastFrom sigma0
          (liftedCentreSignPath hp i first rest)
        = !sigma0 := by
    dsimp [sigma0]
    exact liftedCentreSignPath_last_not hp i first rest
  have hsupportList :
      listPositiveCount (quotientList t C.gaps) = 1 := by
    rw [← centreQuotient_ofFn]
    rw [listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupport
  obtain ⟨pre, post, qe, hqe, hq, hsignLift⟩ :=
    antiperiodic_positive_transition_gap_of_support_le_two
      sigma0
      (liftedCentreSignPath hp i first rest)
      (quotientList t C.gaps)
      hchanges hlast
      (by omega : listPositiveCount (quotientList t C.gaps) ≤ 2)
  have hsupportDecomp :
      listPositiveCount (pre ++ qe :: post) = 1 := by
    rw [← hq]
    exact hsupportList
  have hlistSum :
      (quotientList t C.gaps).sum = qe := by
    rw [hq]
    exact distinguished_positive_eq_list_sum_of_support_one
      pre post qe hqe hsupportDecomp
  have hqeExp :
      qe = centreExponent C t + 1 := by
    have hid :=
      floorExcess_add_positiveSupport (centreQuotient C t)
    have hid' :
        centreExponent C t + 1 =
          ∑ r, centreQuotient C t r := by
      simpa [centreExponent, hsupport] using hid
    rw [centreQuotient_sum_eq_list_sum C t, hlistSum] at hid'
    omega
  have halign :
      QuotientGapAligned t (pre ++ qe :: post) C.gaps := by
    have h0 :=
      centreQuotient_aligned C htpos.le
    rwa [← hq]
  obtain ⟨gpre, gpost, ge, hgaps, hpreGapLen,
      hpostGapLen, hqeGap, _, _⟩ :=
    aligned_gap_decomposition halign
  have hgePos :
      0 < ge :=
    aligned_transition_gap_pos htpos hqe hqeGap
  have hsplitLift :
      rest.map (raySignAt hp i) ++ [!sigma0] =
        List.replicate pre.length sigma0 ++
          List.replicate (post.length + 1) (!sigma0) := by
    simpa [liftedCentreSignPath, sigma0] using hsignLift
  obtain ⟨before, after, hrest, hbeforeLen, hafterLen,
      hbeforeMap, hafterMap⟩ :=
    exists_ray_split_of_lifted_sign_blocks
      (raySignAt hp i) sigma0 rest
      pre.length post.length hsplitLift
  have hbeforeMapLen :
      before.map (raySignAt hp i) =
        List.replicate before.length sigma0 := by
    rw [hbeforeLen]
    exact hbeforeMap
  have hafterMapLen :
      after.map (raySignAt hp i) =
        List.replicate after.length (!sigma0) := by
    rw [hafterLen]
    exact hafterMap
  cases hafter : after with
  | nil =>
      have hpostLen0 : post.length = 0 := by
        rw [← hafterLen, hafter]
        rfl
      have hpostNil : post = [] := List.length_eq_zero.mp hpostLen0
      have hgpostNil : gpost = [] := by
        apply List.length_eq_zero.mp
        rw [hpostGapLen, hpostLen0]
      have hrestEq : rest = before := by
        rw [hafter] at hrest
        simpa using hrest
      have hrays' : C.rays = first :: before := by
        rw [hrays, hrestEq]
      let last : OtherVertex i :=
        (first :: before).getLast (by simp)
      have hgeEq :
          ge =
            (rayThetaAt hp i first + Real.pi -
              rayThetaAt hp i last) / Real.pi := by
        dsimp [last]
        exact centre_gap_eq_wrap_cut
          C first before hrays'
          hgaps
          (by simpa [hbeforeLen] using hpreGapLen)
          hgpostNil
      let width : ℝ :=
        rayThetaAt hp i last - rayThetaAt hp i first
      have hwidthEq :
          width = Real.pi * (1 - ge) := by
        dsimp [width]
        have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
        rw [hgeEq]
        field_simp [hpi]
        ring
      have hpair :
          (first :: before).Pairwise
            (fun a b =>
              rayThetaAt hp i a ≤ rayThetaAt hp i b) := by
        rw [← hrays']
        exact C.theta_sorted
      have hcover :
          ∀ j : OtherVertex i, j ∈ first :: before := by
        intro j
        rw [← hrays']
        exact C.mem_rays_iff j
      have hsign :
          ∀ j ∈ first :: before,
            raySignAt hp i j = sigma0 := by
        intro j hj
        rcases List.mem_cons.mp hj with hj | hj
        · subst j
          rfl
        · exact sign_eq_of_mem_map_replicate
            (raySignAt hp i) sigma0 before
            hbeforeMapLen hj
      have hrepr0 :=
        commonSignedIntervalRepr_of_common_sign_cons
          hp sigma0 first before hcover hsign hpair
      have hfirstLast :
          rayThetaAt hp i first ≤ rayThetaAt hp i last := by
        dsimp [last]
        exact hpair.rel_getLast (by simp)
      have hwidth0 : 0 ≤ width := by
        dsimp [width]
        linarith
      have hwidthPi : width < Real.pi := by
        have hlastPi := rayThetaAt_lt_pi hp i last
        have hfirst0 := rayThetaAt_nonneg hp i first
        dsimp [width]
        linarith
      refine ⟨qe, ge, rayThetaAt hp i first,
        width, sigma0, hqe, hqeExp, hqeGap,
        hgePos, hwidthEq, hwidth0, hwidthPi, ?_⟩
      intro j hji
      simpa [width, last] using hrepr0 j hji
  | cons right tail =>
      have hrestEq :
          rest = before ++ right :: tail := by
        simpa [hafter] using hrest
      have hrays' :
          C.rays =
            first :: (before ++ right :: tail) := by
        rw [hrays, hrestEq]
      let left : OtherVertex i :=
        (first :: before).getLast (by simp)
      have hgeEq :
          ge =
            (rayThetaAt hp i right -
              rayThetaAt hp i left) / Real.pi := by
        dsimp [left]
        exact centre_gap_eq_ordinary_cut
          C first right before tail hrays'
          hgaps
          (by simpa [hbeforeLen] using hpreGapLen)
      have hpair :
          ((first :: before) ++ (right :: tail)).Pairwise
            (fun a b =>
              rayThetaAt hp i a ≤ rayThetaAt hp i b) := by
        rw [← hrays']
        exact C.theta_sorted
      have hpairs :
          (first :: before).Pairwise
              (fun a b =>
                rayThetaAt hp i a ≤ rayThetaAt hp i b) ∧
            (right :: tail).Pairwise
              (fun a b =>
                rayThetaAt hp i a ≤ rayThetaAt hp i b) ∧
            (∀ a ∈ first :: before, ∀ b ∈ right :: tail,
              rayThetaAt hp i a ≤ rayThetaAt hp i b) := by
        simpa only [List.pairwise_append] using hpair
      have hleftMem : left ∈ first :: before := by
        dsimp [left]
        exact List.getLast_mem _
      have hbeforeSign :
          ∀ j ∈ first :: before,
            raySignAt hp i j = sigma0 := by
        intro j hj
        rcases List.mem_cons.mp hj with hj | hj
        · subst j
          rfl
        · exact sign_eq_of_mem_map_replicate
            (raySignAt hp i) sigma0 before
            hbeforeMapLen hj
      have hafterSign :
          ∀ j ∈ right :: tail,
            raySignAt hp i j = !sigma0 := by
        intro j hj
        have hjAfter : j ∈ after := by
          rw [hafter]
          exact hj
        exact sign_eq_of_mem_map_replicate
          (raySignAt hp i) (!sigma0) after
          hafterMapLen hjAfter
      have hbeforeTheta :
          ∀ j ∈ first :: before,
            rayThetaAt hp i j ≤ rayThetaAt hp i left := by
        intro j hj
        dsimp [left]
        exact hpairs.1.rel_getLast hj
      have hafterTheta :
          ∀ j ∈ right :: tail,
            rayThetaAt hp i right ≤ rayThetaAt hp i j := by
        intro j hj
        rcases List.mem_cons.mp hj with hj | hj
        · subst j
          rfl
        · exact (List.pairwise_cons.mp hpairs.2.1).1 j hj
      have hcover :
          ∀ j : OtherVertex i,
            j ∈ first :: before ∨ j ∈ right :: tail := by
        intro j
        have hj := C.mem_rays_iff j
        rw [hrays', List.mem_append] at hj
        exact hj
      let width : ℝ :=
        rayThetaAt hp i left + Real.pi -
          rayThetaAt hp i right
      have hwidthEq :
          width = Real.pi * (1 - ge) := by
        dsimp [width]
        have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
        rw [hgeEq]
        field_simp [hpi]
        ring
      have hleftRight :
          rayThetaAt hp i left ≤
            rayThetaAt hp i right :=
        hpairs.2.2 left hleftMem right (by simp)
      have hwidth0 : 0 ≤ width := by
        have hleft0 := rayThetaAt_nonneg hp i left
        have hrightPi := rayThetaAt_lt_pi hp i right
        dsimp [width]
        linarith
      have hwidthPi : width < Real.pi := by
        have hphys :
            0 <
              rayThetaAt hp i right -
                rayThetaAt hp i left := by
          have hpi : 0 < Real.pi := Real.pi_pos
          rw [hgeEq] at hgePos
          have :
              0 <
                (rayThetaAt hp i right -
                  rayThetaAt hp i left) / Real.pi :=
            hgePos
          exact (div_pos_iff.mp this).resolve_right
            (by linarith : ¬ Real.pi < 0) |>.1
        dsimp [width]
        linarith
      have hrepr0 :=
        commonSignedIntervalRepr_of_two_sign_blocks
          hp sigma0
          (first :: before) (right :: tail)
          hcover hbeforeSign hafterSign
          hbeforeTheta hafterTheta
          (rayThetaAt_nonneg hp i left)
          (rayThetaAt_lt_pi hp i right)
      refine ⟨qe, ge, rayThetaAt hp i right,
        width, !sigma0, hqe, hqeExp, hqeGap,
        hgePos, hwidthEq, hwidth0, hwidthPi, ?_⟩
      intro j hji
      simpa [width] using hrepr0 j hji

#print axioms concrete_one_support_interval_certificate

end JSP000404Research
