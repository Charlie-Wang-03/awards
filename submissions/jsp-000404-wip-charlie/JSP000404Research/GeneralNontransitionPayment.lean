import JSP000404Research.HiddenSameSignQuotient
import JSP000404Research.SmallSameSignGapAngle
import JSP000404Research.LinearizedTransitionExposure
import Mathlib.Tactic

/-!
# Arbitrary-cardinality non-transition quotient payment

The four-centre development proved that a quotient value carried by a
non-transition gap pays a genuine Euclidean angle.  This file removes the
three-ray restriction.

For the ordinary sorted ray path, an aligned quotient occurrence whose endpoint
signs agree gives

  q * lambda <= actual angle.

For the final cyclic wrap step, lifted sign agreement means

  sign(last) = !sign(first),

and the same payment holds using the wrap projective-gap formula.

Therefore any SameSignQuotientOccurs witness in an arbitrary centre cycle
produces two actual non-centre vertices whose angle at the centre is at least
q*lambda.
-/

namespace JSP000404Research

open Real

theorem consecutiveRayQuotients_length
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) (t : ℝ)
    (prev : OtherVertex i) (rs : List (OtherVertex i)) :
    (consecutiveRayQuotients hp i t prev rs).length = rs.length := by
  induction rs generalizing prev with
  | nil =>
      rfl
  | cons r rs ih =>
      simp [consecutiveRayQuotients, ih]

theorem sameSignQuotientOccurs_append_singleton_iff
    (q qlast : ℕ)
    (a b : Bool)
    (signs : List Bool) (qs : List ℕ)
    (hlen : signs.length = qs.length) :
    SameSignQuotientOccurs q a
        (signs ++ [b]) (qs ++ [qlast]) ↔
      SameSignQuotientOccurs q a signs qs ∨
        (qlast = q ∧ boolLastFrom a signs = b) := by
  induction signs generalizing a qs with
  | nil =>
      cases qs with
      | nil =>
          simp [SameSignQuotientOccurs, boolLastFrom]
      | cons r rs =>
          simp at hlen
  | cons x xs ih =>
      cases qs with
      | nil =>
          simp at hlen
      | cons r rs =>
          simp at hlen
          simp only [List.cons_append, SameSignQuotientOccurs,
            boolLastFrom]
          rw [ih x rs hlen]
          tauto

theorem ordinary_sameSignQuotient_pays_angle
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t lam : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : V)
    (prev : OtherVertex i)
    (rs : List (OtherVertex i))
    (hnodup : (prev :: rs).Nodup)
    (hsorted :
      (prev :: rs).Pairwise
        (fun a b =>
          rayThetaAt hp i a ≤ rayThetaAt hp i b))
    (q : ℕ)
    (hocc :
      SameSignQuotientOccurs q
        (raySignAt hp i prev)
        (rs.map (raySignAt hp i))
        (consecutiveRayQuotients hp i t prev rs)) :
    ∃ x y : OtherVertex i,
      x ≠ y ∧
      (q : ℝ) * lam ≤
        EuclideanGeometry.angle (p x.1) (p i) (p y.1) := by
  induction rs generalizing prev with
  | nil =>
      simp [SameSignQuotientOccurs,
        consecutiveRayQuotients] at hocc
  | cons r rs ih =>
      have hnod := List.nodup_cons.mp hnodup
      have hpair := List.pairwise_cons.mp hsorted
      have hprevR : prev ≠ r := by
        intro h
        subst r
        exact hnod.1 (by simp)
      have horder :
          rayThetaAt hp i prev ≤ rayThetaAt hp i r :=
        hpair.1 r (by simp)
      simp only [List.map_cons, consecutiveRayQuotients,
        SameSignQuotientOccurs] at hocc
      rcases hocc with hhead | htail
      · rcases hhead with ⟨hqeq, hsign⟩
        let g : ℝ :=
          (rayThetaAt hp i r -
            rayThetaAt hp i prev) / Real.pi
        have hg0 : 0 ≤ g := by
          dsimp [g]
          exact div_nonneg (sub_nonneg.mpr horder) Real.pi_pos.le
        have hfloor :
            (q : ℝ) ≤ t * g := by
          have hf :
              ((Nat.floor (t * g) : ℕ) : ℝ) ≤ t * g :=
            Nat.floor_le (mul_nonneg ht.le hg0)
          have hnat :
              Nat.floor (t * g) = q := by
            simpa [g] using hqeq
          rw [hnat] at hf
          exact hf
        have hpay :=
          quotient_mul_lam_le_pi_mul_gap
            ht hfloor hlam
        have hang :=
          actual_angle_eq_ordinary_projective_gap_of_sign_eq
            hp i horder hsign
        refine ⟨prev, r, hprevR, ?_⟩
        calc
          (q : ℝ) * lam ≤ Real.pi * g := hpay
          _ = rayThetaAt hp i r -
                rayThetaAt hp i prev := by
              dsimp [g]
              field_simp [Real.pi_ne_zero]
          _ =
              EuclideanGeometry.angle
                (p prev.1) (p i) (p r.1) := hang.symm
      · exact ih r hnod.2 hpair.2 htail

theorem sameSignQuotient_pays_angle
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {t lam : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : V)
    (C : CentreProjectiveCycle hp i)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (hrays : C.rays = first :: rest)
    (q : ℕ)
    (hocc :
      SameSignQuotientOccurs q
        (raySignAt hp i first)
        (liftedCentreSignPath hp i first rest)
        (quotientList t C.gaps)) :
    ∃ x y : OtherVertex i,
      x ≠ y ∧
      (q : ℝ) * lam ≤
        EuclideanGeometry.angle (p x.1) (p i) (p y.1) := by
  have hqdec :=
    centreQuotientList_decompose
      C t first rest hrays
  rw [hqdec] at hocc
  unfold liftedCentreSignPath at hocc
  have hlen :
      (rest.map (raySignAt hp i)).length =
        (consecutiveRayQuotients hp i t first rest).length := by
    simp [consecutiveRayQuotients_length]
  rw [sameSignQuotientOccurs_append_singleton_iff
      q
      (wrapRayQuotient hp i t first (rest.getLastD first))
      (raySignAt hp i first)
      (!raySignAt hp i first)
      (rest.map (raySignAt hp i))
      (consecutiveRayQuotients hp i t first rest)
      hlen] at hocc
  rcases hocc with hord | hwrap
  · have hnodup :
        (first :: rest).Nodup := by
      simpa [hrays] using C.nodup
    have hsorted :
        (first :: rest).Pairwise
          (fun a b =>
            rayThetaAt hp i a ≤ rayThetaAt hp i b) := by
      simpa [hrays] using C.theta_sorted
    exact ordinary_sameSignQuotient_pays_angle
      hp ht hlam i first rest
      hnodup hsorted q hord
  · rcases hwrap with ⟨hqwrap, hlastLift⟩
    by_cases hrest : rest = []
    · subst rest
      simp [boolLastFrom] at hlastLift
    · let last : OtherVertex i := rest.getLastD first
      have hlastMem : last ∈ rest := by
        dsimp [last]
        exact List.getLastD_mem hrest
      have hnodup :
          (first :: rest).Nodup := by
        simpa [hrays] using C.nodup
      have hfirstLast : first ≠ last := by
        intro h
        subst last
        exact (List.nodup_cons.mp hnodup).1 hlastMem
      have hsorted :
          (first :: rest).Pairwise
            (fun a b =>
              rayThetaAt hp i a ≤ rayThetaAt hp i b) := by
        simpa [hrays] using C.theta_sorted
      have horder :
          rayThetaAt hp i first ≤ rayThetaAt hp i last :=
        (List.pairwise_cons.mp hsorted).1 last hlastMem
      have hlastSign :
          boolLastFrom
              (raySignAt hp i first)
              (rest.map (raySignAt hp i))
            =
          raySignAt hp i last := by
        rw [boolLastFrom_eq_getLastD, map_getLastD]
        rfl
      have hsign :
          raySignAt hp i last =
            !raySignAt hp i first := by
        rw [← hlastSign]
        exact hlastLift
      let g : ℝ :=
        (rayThetaAt hp i first + Real.pi -
          rayThetaAt hp i last) / Real.pi
      have hg0 : 0 ≤ g := by
        have hlastPi := rayThetaAt_lt_pi hp i last
        have hfirst0 := rayThetaAt_nonneg hp i first
        dsimp [g]
        exact div_nonneg (by linarith) Real.pi_pos.le
      have hwrapDef :
          wrapRayQuotient hp i t first last =
            Nat.floor (t * g) := by
        rfl
      have hfloor :
          (q : ℝ) ≤ t * g := by
        have hf :
            ((Nat.floor (t * g) : ℕ) : ℝ) ≤ t * g :=
          Nat.floor_le (mul_nonneg ht.le hg0)
        have hnat :
            Nat.floor (t * g) = q := by
          have hqwrap' :
              wrapRayQuotient hp i t first last = q := by
            simpa [last] using hqwrap
          simpa [hwrapDef] using hqwrap'
        rw [hnat] at hf
        exact hf
      have hpay :=
        quotient_mul_lam_le_pi_mul_gap
          ht hfloor hlam
      have hang :=
        actual_angle_eq_wrap_projective_gap_of_lifted_sign_eq
          hp i horder hsign
      refine ⟨last, first, hfirstLast.symm, ?_⟩
      calc
        (q : ℝ) * lam ≤ Real.pi * g := hpay
        _ =
            rayThetaAt hp i first + Real.pi -
              rayThetaAt hp i last := by
              dsimp [g]
              field_simp [Real.pi_ne_zero]
        _ =
            EuclideanGeometry.angle
              (p last.1) (p i) (p first.1) := hang.symm

/-- The hardest support-two case now produces a genuine large-angle witness
without any cardinality restriction. -/
theorem support_two_unit_transition_hidden_angle
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (i : V)
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (pre post : List ℕ)
    (qe : ℕ)
    (hrays : C.rays = first :: rest)
    (hqe0 : qe ≠ 0)
    (hq :
      quotientList t C.gaps =
        pre ++ qe :: post)
    (hsignLift :
      liftedCentreSignPath hp i first rest =
        List.replicate pre.length (raySignAt hp i first) ++
          List.replicate (post.length + 1)
            (!raySignAt hp i first))
    (hqeOne : qe = 1) :
    ∃ x y : OtherVertex i,
      x ≠ y ∧
      (((n - 1 : ℕ) : ℝ) * lam) ≤
        EuclideanGeometry.angle (p x.1) (p i) (p y.1) := by
  have hocc :=
    support_two_unit_transition_hidden_sameSign
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      i C hexp hsupport
      first rest pre post qe
      hrays hqe0 hq hsignLift hqeOne
  have htpos :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  exact sameSignQuotient_pays_angle
    hp htpos hlam i C first rest hrays
    (n - 1) hocc

#print axioms sameSignQuotientOccurs_append_singleton_iff
#print axioms ordinary_sameSignQuotient_pays_angle
#print axioms sameSignQuotient_pays_angle
#print axioms support_two_unit_transition_hidden_angle

end JSP000404Research
