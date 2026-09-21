import JSP000404Research.SupportIntervalCertificate
import JSP000404Research.CentreSignPath
import JSP000404Research.UniqueTransitionGap
import JSP000404Research.TransitionRaySplit
import JSP000404Research.TransitionGapAlignment
import JSP000404Research.TransitionSplitInterval
import Mathlib.Tactic

/-!
# Quantitative support interval from one actual sign transition

For a concrete centre cycle, suppose the lifted canonical sign path changes
exactly once.  The global angle cap implies that this transition is carried by
a positive Sendov quotient.  Aligning the quotient list with the actual
projective gaps therefore produces a geometric cut gap ge with

  1/t <= ge.

Cutting the ray cycle at that gap makes every actual displacement ray have one
common sign on an interval of width

  pi * (1 - ge).

Hence the dual strict-support interval has turn length pi*ge, which is at least
lambda = pi/t.

This theorem is deliberately independent of any exponent or deficit
hypothesis.  In the four-centre mixed branch it reduces the remaining exterior
geometry to the single statement that a strictly exposed fourth point cannot
have three alternating canonical sign transitions.
-/

namespace JSP000404Research

open Real

theorem lam_le_turnLength_of_complement_gap
    {V : Type*} {p : V → Plane} {i : V}
    (S : SupportIntervalCertificate (p := p) i)
    {lam ge : ℝ}
    (hwidth : S.width = Real.pi * (1 - ge))
    (hgap : lam ≤ Real.pi * ge) :
    lam ≤ S.turnLength := by
  unfold SupportIntervalCertificate.turnLength
  rw [hwidth]
  linarith

/-- One genuine transition in the concrete lifted sign path gives a support
interval whose dual turn length is at least one full cap unit. -/
theorem exists_supportIntervalCertificate_of_one_sign_transition
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
    (hrays : C.rays = first :: rest)
    (htrans :
      boolTransitionCountFrom
          (raySignAt hp i first)
          (liftedCentreSignPath hp i first rest) = 1) :
    ∃ S : SupportIntervalCertificate (p := p) i,
      lam ≤ S.turnLength := by
  let sigma0 : Bool := raySignAt hp i first
  have hchanges :
      ChangesOnlyOnPositive
        sigma0
        (liftedCentreSignPath hp i first rest)
        (quotientList t C.gaps) := by
    simpa [sigma0] using
      centre_changesOnlyOnPositive
        hp hcap ht htone hlam i C first rest hrays
  obtain ⟨pre, post, qe, hqe, hq, hsignLift⟩ :=
    one_transition_positive_gap_decomposition
      sigma0
      (liftedCentreSignPath hp i first rest)
      (quotientList t C.gaps)
      hchanges
      (by simpa [sigma0] using htrans)
  have hsplitLift :
      rest.map (raySignAt hp i) ++ [!sigma0] =
        List.replicate pre.length sigma0 ++
          List.replicate (post.length + 1) (!sigma0) := by
    simpa [liftedCentreSignPath, sigma0] using hsignLift
  have halign :
      QuotientGapAligned t (pre ++ qe :: post) C.gaps := by
    have h0 := centreQuotient_aligned C ht.le
    rwa [← hq]
  obtain ⟨gpre, gpost, ge, hgaps, hpreGapLen,
      hpostGapLen, hqeGap, _, _⟩ :=
    aligned_gap_decomposition halign
  have hgePos :
      0 < ge :=
    aligned_transition_gap_pos ht hqe hqeGap
  have hlamGap :
      lam ≤ Real.pi * ge :=
    lam_le_pi_mul_gap_of_positive_quotient
      ht hqe hqeGap hlam
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
      have hwidth0 : 0 ≤ width := by
        dsimp [width]
        have hfirstLast :
            rayThetaAt hp i first ≤ rayThetaAt hp i last := by
          dsimp [last]
          exact hpair.rel_getLast (by simp)
        linarith
      have hwidthPi : width < Real.pi := by
        have hlastPi := rayThetaAt_lt_pi hp i last
        have hfirst0 := rayThetaAt_nonneg hp i first
        dsimp [width]
        linarith
      let S : SupportIntervalCertificate (p := p) i :=
        { a := rayThetaAt hp i first
          width := width
          sigma := sigma0
          width_nonneg := hwidth0
          width_lt_pi := hwidthPi
          repr := by
            intro j hji
            simpa [width, last] using hrepr0 j hji }
      refine ⟨S, ?_⟩
      apply lam_le_turnLength_of_complement_gap S hwidthEq
      exact hlamGap
  | cons right tail =>
      have hrestEq :
          rest = before ++ right :: tail := by
        simpa [hafter] using hrest
      have hrays' :
          C.rays = first :: (before ++ right :: tail) := by
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
            (raySignAt hp i) sigma0 before hbeforeMapLen hj
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
      have hwidth0 : 0 ≤ width := by
        have hleftRight :
            rayThetaAt hp i left ≤ rayThetaAt hp i right :=
          hpairs.2.2 left hleftMem right (by simp)
        have hleft0 := rayThetaAt_nonneg hp i left
        have hrightPi := rayThetaAt_lt_pi hp i right
        dsimp [width]
        linarith
      have hwidthPi : width < Real.pi := by
        have hphys :
            0 <
              rayThetaAt hp i right -
                rayThetaAt hp i left := by
          rw [hgeEq] at hgePos
          have hpi : 0 < Real.pi := Real.pi_pos
          exact (div_pos_iff.mp hgePos).resolve_right
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
      let S : SupportIntervalCertificate (p := p) i :=
        { a := rayThetaAt hp i right
          width := width
          sigma := !sigma0
          width_nonneg := hwidth0
          width_lt_pi := hwidthPi
          repr := by
            intro j hji
            simpa [width] using hrepr0 j hji }
      refine ⟨S, ?_⟩
      apply lam_le_turnLength_of_complement_gap S hwidthEq
      exact hlamGap

#print axioms lam_le_turnLength_of_complement_gap
#print axioms exists_supportIntervalCertificate_of_one_sign_transition

end JSP000404Research
