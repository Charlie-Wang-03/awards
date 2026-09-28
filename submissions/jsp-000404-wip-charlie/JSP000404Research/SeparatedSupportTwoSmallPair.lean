import JSP000404Research.SeparatedSupportTwoResidualBudget
import Mathlib.Tactic

/-!
# A delta-small non-top pair at every separated support-two minimum

The separated support-two residual budget leaves at most 2*delta*lambda after
one top-adjacent zero quotient has already consumed at least
(1-delta)*lambda.

Because a six-point centre has exactly five cyclic gaps, the internal block
between the four non-top rays has exactly three gaps.

* If exactly one top-adjacent end quotient is zero, the internal block has at
  most one positive quotient, hence at least two zero quotients.  Their total
  actual-angle mass is at most 2*delta*lambda, so one has angle at most
  delta*lambda.

* If both top-adjacent end quotients are zero, the internal block has exactly
  two positive quotients and one zero quotient.  The second sharp outer angle
  also costs at least (1-delta)*lambda, leaving the unique internal zero angle
  at most (3*delta-1)*lambda < delta*lambda.

Thus every separated support-two minimum owns a genuine delta-small angular
pair among the four rays avoiding the sharp top.
-/

namespace JSP000404Research

open Real

theorem exists_small_zero_of_three_support_le_one
    (q₁ q₂ q₃ : ℕ)
    (A₁ A₂ A₃ D : ℝ)
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hA₃ : 0 ≤ A₃)
    (hD : 0 ≤ D)
    (hcount :
      listPositiveCount [q₁,q₂,q₃] ≤ 1)
    (hmass :
      listZeroAngleMass [q₁,q₂,q₃] [A₁,A₂,A₃] ≤ 2 * D) :
    (q₁ = 0 ∧ A₁ ≤ D) ∨
      (q₂ = 0 ∧ A₂ ≤ D) ∨
      (q₃ = 0 ∧ A₃ ≤ D) := by
  have hz :
      (q₁ = 0 ∧ q₂ = 0) ∨
      (q₁ = 0 ∧ q₃ = 0) ∨
      (q₂ = 0 ∧ q₃ = 0) := by
    by_cases h1 : q₁ = 0 <;>
      by_cases h2 : q₂ = 0 <;>
      by_cases h3 : q₃ = 0 <;>
      simp [listPositiveCount, h1, h2, h3] at hcount ⊢
  rcases hz with h12 | h13 | h23
  · by_cases h1D : A₁ ≤ D
    · exact Or.inl ⟨h12.1, h1D⟩
    · by_cases h2D : A₂ ≤ D
      · exact Or.inr (Or.inl ⟨h12.2, h2D⟩)
      · exfalso
        by_cases h3 : q₃ = 0
        · simp [listZeroAngleMass, h12.1, h12.2, h3] at hmass
          nlinarith
        · simp [listZeroAngleMass, h12.1, h12.2, h3] at hmass
          nlinarith
  · by_cases h1D : A₁ ≤ D
    · exact Or.inl ⟨h13.1, h1D⟩
    · by_cases h3D : A₃ ≤ D
      · exact Or.inr (Or.inr ⟨h13.2, h3D⟩)
      · exfalso
        by_cases h2 : q₂ = 0
        · simp [listZeroAngleMass, h13.1, h13.2, h2] at hmass
          nlinarith
        · simp [listZeroAngleMass, h13.1, h13.2, h2] at hmass
          nlinarith
  · by_cases h2D : A₂ ≤ D
    · exact Or.inr (Or.inl ⟨h23.1, h2D⟩)
    · by_cases h3D : A₃ ≤ D
      · exact Or.inr (Or.inr ⟨h23.2, h3D⟩)
      · exfalso
        by_cases h1 : q₁ = 0
        · simp [listZeroAngleMass, h23.1, h23.2, h1] at hmass
          nlinarith
        · simp [listZeroAngleMass, h23.1, h23.2, h1] at hmass
          nlinarith

theorem exists_small_zero_of_three_support_eq_two_after_outer
    (q₁ q₂ q₃ : ℕ)
    (A₁ A₂ A₃ AOuter delta lam : ℝ)
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hA₃ : 0 ≤ A₃)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlam : 0 < lam)
    (hcount :
      listPositiveCount [q₁,q₂,q₃] = 2)
    (houter :
      (1 - delta) * lam ≤ AOuter)
    (hmass :
      listZeroAngleMass [q₁,q₂,q₃] [A₁,A₂,A₃] +
        AOuter ≤ 2 * delta * lam) :
    (q₁ = 0 ∧ A₁ ≤ delta * lam) ∨
      (q₂ = 0 ∧ A₂ ≤ delta * lam) ∨
      (q₃ = 0 ∧ A₃ ≤ delta * lam) := by
  have hz :
      (q₁ = 0 ∧ q₂ ≠ 0 ∧ q₃ ≠ 0) ∨
      (q₁ ≠ 0 ∧ q₂ = 0 ∧ q₃ ≠ 0) ∨
      (q₁ ≠ 0 ∧ q₂ ≠ 0 ∧ q₃ = 0) := by
    by_cases h1 : q₁ = 0 <;>
      by_cases h2 : q₂ = 0 <;>
      by_cases h3 : q₃ = 0 <;>
      simp [listPositiveCount, h1, h2, h3] at hcount ⊢
  rcases hz with h1 | h2 | h3
  · left
    refine ⟨h1.1, ?_⟩
    simp [listZeroAngleMass, h1.1, h1.2.1, h1.2.2] at hmass
    nlinarith
  · right; left
    refine ⟨h2.2.1, ?_⟩
    simp [listZeroAngleMass, h2.1, h2.2.1, h2.2.2] at hmass
    nlinarith
  · right; right
    refine ⟨h3.2.2, ?_⟩
    simp [listZeroAngleMass, h3.1, h3.2.1, h3.2.2] at hmass
    nlinarith

theorem separated_support_two_has_small_pair_away_from_top
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (Cfam : ∀ v : V, CentreProjectiveCycle hp v)
    {lam t delta : ℝ} {n : ℕ}
    (hcard : Fintype.card V = 6)
    (hn : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (top : V)
    (hTop : centreExponent (Cfam top) t = n - 1)
    {i : V}
    (hit : i ≠ top)
    (hI : centreExponent (Cfam i) t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient (Cfam i) t) = 2)
    (hsep :
      ¬ TopPinnedPositivePair Cfam top i hit t) :
    ∃ x y : OtherVertex i,
      x ≠ y ∧
      x.1 ≠ top ∧ y.1 ≠ top ∧
      EuclideanGeometry.angle (p x.1) (p i) (p y.1)
        ≤ delta * lam := by
  have htpos :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos

  obtain ⟨first0, rest0, k, pre, post, r, rest,
      qFirst, qLast, qmid,
      _hrays0, _hsplit, _hk, hrotRays, hqrot,
      hsupportRot, hend, htailBudget, hheadBudget⟩ :=
    separated_support_two_residual_zero_budget
      hp hcap Cfam hcard hn hdelta0 hdeltaHalf
      ht hlam top hTop hit hI hsupport hsep

  have hRayLen : (Cfam i).rays.length = 5 := by
    rw [centreRayList_length_eq_card_sub_one (Cfam i), hcard]
    norm_num
  have hrestLen : rest.length = 3 := by
    have h := congrArg List.length hrotRays
    rw [List.length_rotate, hRayLen] at h
    simp at h
    omega
  obtain ⟨b,c,d,hrest⟩ :
      ∃ b c d : OtherVertex i, rest = [b,c,d] := by
    cases rest with
    | nil => simp at hrestLen
    | cons b rest1 =>
      cases rest1 with
      | nil => simp at hrestLen
      | cons c rest2 =>
        cases rest2 with
        | nil => simp at hrestLen
        | cons d rest3 =>
          have hnil : rest3 = [] := by
            simpa using hrestLen
          subst rest3
          exact ⟨b,c,d,rfl⟩

  have hQLen :
      (quotientList t (Cfam i).gaps).length = 5 := by
    rw [quotientList_length, (Cfam i).gaps_length, hRayLen]
  have hqmidLen : qmid.length = 3 := by
    have h := congrArg List.length hqrot
    rw [List.length_rotate, hQLen] at h
    simp at h
    omega
  obtain ⟨q₁,q₂,q₃,hqmid⟩ :
      ∃ q₁ q₂ q₃ : ℕ, qmid = [q₁,q₂,q₃] := by
    cases qmid with
    | nil => simp at hqmidLen
    | cons q₁ qs1 =>
      cases qs1 with
      | nil => simp at hqmidLen
      | cons q₂ qs2 =>
        cases qs2 with
        | nil => simp at hqmidLen
        | cons q₃ qs3 =>
          have hnil : qs3 = [] := by
            simpa using hqmidLen
          subst qs3
          exact ⟨q₁,q₂,q₃,rfl⟩

  let A₁ := EuclideanGeometry.angle (p r.1) (p i) (p b.1)
  let A₂ := EuclideanGeometry.angle (p b.1) (p i) (p c.1)
  let A₃ := EuclideanGeometry.angle (p c.1) (p i) (p d.1)
  have hA₁ : 0 ≤ A₁ := by positivity
  have hA₂ : 0 ≤ A₂ := by positivity
  have hA₃ : 0 ≤ A₃ := by positivity

  have hrotNodup :
      ((⟨top, hit⟩ : OtherVertex i) :: r :: b :: c :: d :: []).Nodup := by
    rw [← hrest] at hrotRays
    rw [← hrotRays]
    simpa using (Cfam i).nodup

  have htailNodup :
      (r :: b :: c :: d :: []).Nodup :=
    (List.nodup_cons.mp hrotNodup).2
  have htopNotTail :
      (⟨top, hit⟩ : OtherVertex i) ∉
        (r :: b :: c :: d :: []) :=
    (List.nodup_cons.mp hrotNodup).1

  have hrTop : r.1 ≠ top := by
    intro h
    apply htopNotTail
    simp only [List.mem_cons, List.mem_singleton]
    left
    apply Subtype.ext
    exact h
  have hbTop : b.1 ≠ top := by
    intro h
    apply htopNotTail
    simp only [List.mem_cons, List.mem_singleton]
    right; left
    apply Subtype.ext
    exact h
  have hcTop : c.1 ≠ top := by
    intro h
    apply htopNotTail
    simp only [List.mem_cons, List.mem_singleton]
    right; right; left
    apply Subtype.ext
    exact h
  have hdTop : d.1 ≠ top := by
    intro h
    apply htopNotTail
    simp only [List.mem_cons, List.mem_singleton]
    right; right; right
    apply Subtype.ext
    exact h

  have hrb : r ≠ b :=
    (List.nodup_cons.mp htailNodup).1 (by simp)
  have hbc : b ≠ c := by
    have hbcN := (List.nodup_cons.mp htailNodup).2
    exact (List.nodup_cons.mp hbcN).1 (by simp)
  have hcd : c ≠ d := by
    have hbcN := (List.nodup_cons.mp htailNodup).2
    have hcdN := (List.nodup_cons.mp hbcN).2
    exact (List.nodup_cons.mp hcdN).1 (by simp)

  have hsupport3 :
      listPositiveCount (qFirst :: [q₁,q₂,q₃] ++ [qLast]) = 2 := by
    simpa [hqmid] using hsupportRot

  by_cases hF : qFirst = 0
  · by_cases hL : qLast = 0
    · have hmidCount :
          listPositiveCount [q₁,q₂,q₃] = 2 := by
        simp [listPositiveCount, hF, hL] at hsupport3 ⊢
        exact hsupport3
      have htail := htailBudget hF
      rw [hrest, hqmid] at htail
      simp [consecutiveRayAngles, A₁, A₂, A₃, hL] at htail
      have hLastLower :
          (1 - delta) * lam ≤
            EuclideanGeometry.angle (p d.1) (p i) (p top) := by
        rcases hend with hFirst | hLast
        · have hsharp :
              SharpAt p delta lam top :=
            concrete_unit_deficit_is_sharp
              hp hcap (by omega : 2 ≤ n)
              hdelta0 (by linarith : delta < 1)
              ht hlam top (Cfam top) hTop
          have h :=
            outer_angle_ge_one_sub_delta_mul_lam_of_sharp
              hp hcap hit.symm hdTop
              (by intro h; exact d.2 h.symm) hsharp
          simpa [EuclideanGeometry.angle_comm] using h
        · rw [hrest] at hLast
          simpa using hLast.2
      obtain hsmall :=
        exists_small_zero_of_three_support_eq_two_after_outer
          q₁ q₂ q₃ A₁ A₂ A₃
          (EuclideanGeometry.angle (p d.1) (p i) (p top))
          delta lam hA₁ hA₂ hA₃ hdelta0 hdeltaHalf hlampos
          hmidCount hLastLower
          (by simpa [listZeroAngleMass] using htail)
      rcases hsmall with h1 | h2 | h3
      · exact ⟨r,b,hrb,hrTop,hbTop,by simpa [A₁] using h1.2⟩
      · exact ⟨b,c,hbc,hbTop,hcTop,by simpa [A₂] using h2.2⟩
      · exact ⟨c,d,hcd,hcTop,hdTop,by simpa [A₃] using h3.2⟩
    · have hmidCount :
          listPositiveCount [q₁,q₂,q₃] ≤ 1 := by
        simp [listPositiveCount, hF, hL] at hsupport3
        omega
      have htail := htailBudget hF
      rw [hrest, hqmid] at htail
      simp [consecutiveRayAngles, A₁, A₂, A₃, hL] at htail
      obtain hsmall :=
        exists_small_zero_of_three_support_le_one
          q₁ q₂ q₃ A₁ A₂ A₃
          (delta * lam)
          hA₁ hA₂ hA₃
          (mul_nonneg hdelta0 hlampos.le)
          hmidCount
          (by simpa [listZeroAngleMass] using htail)
      rcases hsmall with h1 | h2 | h3
      · exact ⟨r,b,hrb,hrTop,hbTop,h1.2⟩
      · exact ⟨b,c,hbc,hbTop,hcTop,h2.2⟩
      · exact ⟨c,d,hcd,hcTop,hdTop,h3.2⟩
  · have hL : qLast = 0 := by
      rcases hend with hFirst | hLast
      · exact False.elim (hF hFirst.1)
      · exact hLast.1
    have hmidCount :
        listPositiveCount [q₁,q₂,q₃] ≤ 1 := by
      simp [listPositiveCount, hF, hL] at hsupport3
      omega
    have hhead := hheadBudget hL
    rw [hrest, hqmid] at hhead
    simp [consecutiveRayAngles, A₁, A₂, A₃, hF] at hhead
    obtain hsmall :=
      exists_small_zero_of_three_support_le_one
        q₁ q₂ q₃ A₁ A₂ A₃
        (delta * lam)
        hA₁ hA₂ hA₃
        (mul_nonneg hdelta0 hlampos.le)
        hmidCount
        (by simpa [listZeroAngleMass] using hhead)
    rcases hsmall with h1 | h2 | h3
    · exact ⟨r,b,hrb,hrTop,hbTop,h1.2⟩
    · exact ⟨b,c,hbc,hbTop,hcTop,h2.2⟩
    · exact ⟨c,d,hcd,hcTop,hdTop,h3.2⟩

#print axioms exists_small_zero_of_three_support_le_one
#print axioms exists_small_zero_of_three_support_eq_two_after_outer
#print axioms separated_support_two_has_small_pair_away_from_top

end JSP000404Research
