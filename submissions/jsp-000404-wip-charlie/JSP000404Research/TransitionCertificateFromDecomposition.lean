import JSP000404Research.ConcreteTransitionInterval
import Mathlib.Tactic

/-!
# Reconstructing a transition interval without forgetting the transition cut

HighExponentTransitionIntervalCertificate is intentionally compact, but the
construction of such a certificate starts from a much richer witness:

* a concrete ray list first :: rest;
* a quotient decomposition pre ++ qe :: post;
* the exact two-block lifted sign shape across that distinguished quotient.

Later mixed four-centre arguments need to remember that the qe packed
globally is exactly this unique sign-transition quotient.  This file exposes
the constructor from the rich decomposition to the compact interval
certificate, preserving H.qe = qe.

No new geometry is introduced here; this is the proof from
exists_highExponentTransitionIntervalCertificate factored at the point where
the transition decomposition has already been obtained.
-/

namespace JSP000404Research

open Real

theorem exists_highExponentTransitionIntervalCertificate_of_decomposition
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {t : ℝ}
    (htpos : 0 < t)
    (i : V)
    (C : CentreProjectiveCycle hp i)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (pre post : List ℕ)
    (qe : ℕ)
    (hrays : C.rays = first :: rest)
    (hqe : qe ≠ 0)
    (hq :
      quotientList t C.gaps =
        pre ++ qe :: post)
    (hsignLift :
      liftedCentreSignPath hp i first rest =
        List.replicate pre.length (raySignAt hp i first) ++
          List.replicate (post.length + 1)
            (!raySignAt hp i first)) :
    ∃ H : HighExponentTransitionIntervalCertificate hp t i C,
      H.qe = qe := by
  let sigma0 : Bool := raySignAt hp i first
  have hsplitLift :
      rest.map (raySignAt hp i) ++ [!sigma0] =
        List.replicate pre.length sigma0 ++
          List.replicate (post.length + 1) (!sigma0) := by
    simpa [liftedCentreSignPath, sigma0] using hsignLift
  have halign :
      QuotientGapAligned t (pre ++ qe :: post) C.gaps := by
    have h0 := centreQuotient_aligned C htpos.le
    rwa [← hq]
  obtain ⟨gpre, gpost, ge, hgaps, hpreGapLen,
      hpostGapLen, hqeGap, _, _⟩ :=
    aligned_gap_decomposition halign
  have hgePos :
      0 < ge :=
    aligned_transition_gap_pos htpos hqe hqeGap
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
      let H : HighExponentTransitionIntervalCertificate hp t i C :=
        {
          qe := qe
          ge := ge
          a := rayThetaAt hp i first
          width := width
          sigma := sigma0
          qe_ne := hqe
          qe_mem := by
            rw [hq]
            simp [hqe]
          qe_le := hqeGap
          ge_pos := hgePos
          width_eq := hwidthEq
          width_nonneg := hwidth0
          width_lt_pi := hwidthPi
          repr := by
            intro j hji
            simpa [width, last] using hrepr0 j hji
        }
      exact ⟨H, rfl⟩
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
      let H : HighExponentTransitionIntervalCertificate hp t i C :=
        {
          qe := qe
          ge := ge
          a := rayThetaAt hp i right
          width := width
          sigma := !sigma0
          qe_ne := hqe
          qe_mem := by
            rw [hq]
            simp [hqe]
          qe_le := hqeGap
          ge_pos := hgePos
          width_eq := hwidthEq
          width_nonneg := hwidth0
          width_lt_pi := hwidthPi
          repr := by
            intro j hji
            simpa [width] using hrepr0 j hji
        }
      exact ⟨H, rfl⟩

#print axioms exists_highExponentTransitionIntervalCertificate_of_decomposition

end JSP000404Research
