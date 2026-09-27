import JSP000404Research.SupportTwoZeroAngleAverage
import JSP000404Research.SixPointSupportThreeShape
import JSP000404Research.SharpOuterAngles
import Mathlib.Tactic

/-!
# A uniformly small non-sharp pair at a six-point support-two minimum

At an exact n-3/support-two centre the five cyclic quotient positions contain
exactly three zeros.  Their total genuine angle mass is at most

  (1+delta) * lambda.

Hence one zero position has actual angle at most

  ((1+delta)/3) * lambda.

In the lower branch delta<1/2 this is strictly smaller than
(1-delta)*lambda.  SharpOuterAngles therefore shows that neither endpoint of
this small pair can be the sharp top centre.
-/

namespace JSP000404Research

open Real

theorem mem_zeroAngleEntries_angle
    {qs : List ℕ} {As : List ℝ} {A : ℝ}
    (h : A ∈ zeroAngleEntries qs As) :
    A ∈ As := by
  induction qs generalizing As with
  | nil =>
      cases As <;> simp [zeroAngleEntries] at h
  | cons q qs ih =>
      cases As with
      | nil =>
          simp [zeroAngleEntries] at h
      | cons B Bs =>
          by_cases hq : q = 0
          · subst q
            simp only [zeroAngleEntries, if_pos, List.singleton_append,
              List.mem_cons] at h
            rcases h with rfl | htail
            · simp
            · exact List.mem_cons_of_mem B (ih htail)
          · simp only [zeroAngleEntries, if_neg hq,
              List.nil_append] at h
            exact List.mem_cons_of_mem B (ih h)

theorem mem_consecutiveRayAngles_exists_pair
    {V : Type*} {p : V → Plane}
    (i : V)
    (prev : OtherVertex i)
    (rs : List (OtherVertex i))
    {A : ℝ}
    (hA : A ∈ consecutiveRayAngles (p := p) i prev rs) :
    ∃ x y : OtherVertex i,
      x ∈ prev :: rs ∧
      y ∈ prev :: rs ∧
      A = EuclideanGeometry.angle (p x.1) (p i) (p y.1) := by
  induction rs generalizing prev with
  | nil =>
      simp [consecutiveRayAngles] at hA
  | cons r rs ih =>
      simp only [consecutiveRayAngles, List.mem_cons] at hA
      rcases hA with hhead | htail
      · exact ⟨prev, r, by simp, by simp, hhead⟩
      · obtain ⟨x,y,hx,hy,hxy⟩ := ih r htail
        exact ⟨x,y,by simp at hx ⊢; exact hx,
          by simp at hy ⊢; exact hy,hxy⟩

/-- Every member of the cyclic actual-angle list comes from a pair of rays in
the displayed cycle.  Under nodup and at least two rays the endpoints are
distinct. -/
theorem mem_cyclicRayAngles_exists_distinct_pair
    {V : Type*} {p : V → Plane}
    (i : V)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (hnodup : (first :: rest).Nodup)
    (hrest : rest ≠ [])
    {A : ℝ}
    (hA : A ∈ cyclicRayAngles (p := p) i first rest) :
    ∃ x y : OtherVertex i,
      x ≠ y ∧
      A = EuclideanGeometry.angle (p x.1) (p i) (p y.1) := by
  unfold cyclicRayAngles at hA
  simp only [List.mem_append, List.mem_singleton] at hA
  rcases hA with hord | hwrap
  · obtain ⟨x,y,hx,hy,hxy⟩ :=
      mem_consecutiveRayAngles_exists_pair
        (p := p) i first rest hord
    have hxyNe : x ≠ y := by
      -- Consecutive entries in a nodup ray list are distinct.  It is enough
      -- here to rule out equality using positivity of the displayed angle:
      -- instead use membership plus nodup after recovering the recursive
      -- adjacent pair through a second induction.
      induction rest generalizing first with
      | nil =>
          simp [consecutiveRayAngles] at hord
      | cons r rs ih =>
          have hnd := List.nodup_cons.mp hnodup
          simp only [consecutiveRayAngles, List.mem_cons] at hord
          rcases hord with hhead | htail
          · have hfr : first ≠ r := by
              intro h
              subst r
              exact hnd.1 (by simp)
            -- hxy identifies the same head angle; choose the actual head pair.
            exact hfr
          · have htailNodup : (r :: rs).Nodup := hnd.2
            exact ih r htailNodup htail
    exact ⟨x,y,hxyNe,hxy⟩
  · let last := rest.getLastD first
    have hlastMem : last ∈ rest := by
      dsimp [last]
      exact List.getLastD_mem hrest
    have hfl : last ≠ first := by
      intro h
      subst last
      exact (List.nodup_cons.mp hnodup).1 hlastMem
    exact ⟨last, first, hfl, hwrap⟩

/-- Six-point support-two centres contain a genuinely small pair. -/
theorem six_point_support_two_has_one_third_small_angle
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hcardV : Fintype.card V = 6)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (i : V)
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2) :
    ∃ x y : OtherVertex i,
      x ≠ y ∧
      EuclideanGeometry.angle (p x.1) (p i) (p y.1)
        ≤ ((1 + delta) * lam) / 3 := by
  obtain ⟨first,rest,hrays⟩ :
      ∃ first rest, C.rays = first :: rest := by
    cases hR : C.rays with
    | nil => exact False.elim (C.nonempty hR)
    | cons first rest => exact ⟨first,rest,hR⟩
  let qs := quotientList t C.gaps
  let As := cyclicRayAngles (p := p) i first rest

  have hqLen : qs.length = 5 := by
    dsimp [qs]
    rw [quotientList_length, C.gaps_length,
      centreRayList_length_eq_five_of_card_six C hcardV]
  have hlen : qs.length = As.length := by
    dsimp [qs,As]
    rw [quotientList_length, C.gaps_length,
      cyclicRayAngles_length]
    simpa [hrays]
  have hsupportList : listPositiveCount qs = 2 := by
    dsimp [qs]
    rw [← centreQuotient_ofFn C t,
      listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupport
  have hA0 : ∀ A ∈ As, 0 ≤ A := by
    dsimp [As]
    exact all_cyclicRayAngles_nonneg (p := p) i first rest
  have hmass :
      listZeroAngleMass qs As ≤ (1 + delta) * lam := by
    dsimp [qs,As]
    exact centre_zeroAngleMass_le_one_add_delta_lam_of_deficit_three_support_two
      hp hcap (by omega : 4 ≤ n) hdelta0 hdeltaHalf
      ht hlam i C hexp hsupport first rest hrays

  obtain ⟨A,hAz,hAsmall⟩ :=
    exists_small_zeroAngleEntry_of_five_support_two
      qs As hqLen hlen hsupportList hA0 hmass
  have hAin : A ∈ As := mem_zeroAngleEntries_angle hAz

  have hrestLen : rest.length = 4 := by
    have hlen5 :=
      centreRayList_length_eq_five_of_card_six C hcardV
    rw [hrays] at hlen5
    simp at hlen5
    omega
  have hrest : rest ≠ [] := by
    intro h
    rw [h] at hrestLen
    simp at hrestLen
  have hnodup : (first :: rest).Nodup := by
    simpa [hrays] using C.nodup

  obtain ⟨x,y,hxy,hAeq⟩ :=
    mem_cyclicRayAngles_exists_distinct_pair
      (p := p) i first rest hnodup hrest hAin
  exact ⟨x,y,hxy,by simpa [hAeq] using hAsmall⟩

/-- With a sharp top present, the averaged support-two small pair avoids the
top ray at both endpoints. -/
theorem six_point_support_two_small_pair_avoids_sharp
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hcardV : Fintype.card V = 6)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {top i : V}
    (hti : top ≠ i)
    (hSharp : SharpAt p delta lam top)
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2) :
    ∃ x y : OtherVertex i,
      x ≠ y ∧
      x.1 ≠ top ∧
      y.1 ≠ top ∧
      EuclideanGeometry.angle (p x.1) (p i) (p y.1)
        ≤ ((1 + delta) * lam) / 3 := by
  obtain ⟨x,y,hxy,hsmall⟩ :=
    six_point_support_two_has_one_third_small_angle
      hp hcap hcardV hn5 hdelta0 hdeltaHalf
      ht hlam i C hexp hsupport
  have htpos :
      0 < t := sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hcoef :
      ((1 + delta) * lam) / 3 <
        (1 - delta) * lam := by
    nlinarith
  have hxTop : x.1 ≠ top := by
    intro hx
    have hyTop : y.1 ≠ top := by
      intro hy
      apply hxy
      apply Subtype.ext
      exact hx.trans hy.symm
    have houter :=
      outer_angle_ge_one_sub_delta_mul_lam_of_sharp
        hp hcap hti hyTop y.2.symm hSharp
    have hs :
        EuclideanGeometry.angle (p top) (p i) (p y.1)
          ≤ ((1 + delta) * lam) / 3 := by
      simpa [hx] using hsmall
    linarith
  have hyTop : y.1 ≠ top := by
    intro hy
    have hxTop' : x.1 ≠ top := hxTop
    have houter :=
      outer_angle_ge_one_sub_delta_mul_lam_of_sharp
        hp hcap hti hxTop' x.2.symm hSharp
    have hcomm :
        EuclideanGeometry.angle (p x.1) (p i) (p top) =
          EuclideanGeometry.angle (p top) (p i) (p x.1) :=
      EuclideanGeometry.angle_comm _ _ _
    have hs :
        EuclideanGeometry.angle (p top) (p i) (p x.1)
          ≤ ((1 + delta) * lam) / 3 := by
      rw [← hcomm]
      simpa [hy] using hsmall
    linarith
  exact ⟨x,y,hxy,hxTop,hyTop,hsmall⟩

#print axioms six_point_support_two_has_one_third_small_angle
#print axioms six_point_support_two_small_pair_avoids_sharp

end JSP000404Research
