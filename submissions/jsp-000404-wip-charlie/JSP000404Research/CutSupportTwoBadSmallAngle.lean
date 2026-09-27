import JSP000404Research.CutSupportThreeBadSmallAngle
import JSP000404Research.CutSaturatedSupportMismatch
import JSP000404Research.SharpOuterAngles
import Mathlib.Tactic

/-!
# A sub-half-angle pair at a support-two saturation-bad six-point minimum

For an exact n-3 minimum with quotient support two, the five cyclic cut gaps
contain exactly three quotient-zero gaps. Their total normalized mass is at
most

  (n + delta) - (n - 1) = 1 + delta.

Hence one zero gap has normalized width at most (1+delta)/3.  At a
saturation-bad cut the wrap quotient is at least two, so this selected
quotient-zero gap is an ordinary successive gap between two adjacent cut rays.

A quotient-zero gap cannot change the adjusted sign, so the genuine Euclidean
angle equals the projective gap and is at most

  ((1+delta)/3) * lambda.

Since delta<1/2, this coefficient is strictly below both 1/2 and 1-delta.
Thus in the presence of the sharp top, neither endpoint can be the top ray.
-/

namespace JSP000404Research

open Real
open BinaryEdgePartition

def zeroGapValues : List ℕ → List ℝ → List ℝ
  | [], [] => []
  | q :: qs, g :: gs =>
      if q = 0 then g :: zeroGapValues qs gs
      else zeroGapValues qs gs
  | _, _ => []

theorem zeroGapValues_sum
    (qs : List ℕ) (gs : List ℝ)
    (hlen : qs.length = gs.length) :
    (zeroGapValues qs gs).sum = listZeroGapMass qs gs := by
  induction qs generalizing gs with
  | nil =>
      cases gs <;> simp [zeroGapValues, listZeroGapMass]
  | cons q qs ih =>
      cases gs with
      | nil => simp at hlen
      | cons g gs =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          by_cases hq : q = 0 <;>
            simp [zeroGapValues, listZeroGapMass, hq, ih gs hlen]

theorem zeroGapValues_length
    (qs : List ℕ) (gs : List ℝ)
    (hlen : qs.length = gs.length) :
    (zeroGapValues qs gs).length =
      qs.length - listPositiveCount qs := by
  induction qs generalizing gs with
  | nil =>
      cases gs <;> simp [zeroGapValues, listPositiveCount]
  | cons q qs ih =>
      cases gs with
      | nil => simp at hlen
      | cons g gs =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          by_cases hq : q = 0
          · subst q
            simp [zeroGapValues, listPositiveCount, ih gs hlen]
          · simp [zeroGapValues, listPositiveCount, hq, ih gs hlen]
            omega

theorem mem_zeroGapValues_of_map_floor
    {gs : List ℝ} {g : ℝ}
    (hg : g ∈ zeroGapValues (gs.map Nat.floor) gs) :
    g ∈ gs ∧ Nat.floor g = 0 := by
  induction gs with
  | nil => simp [zeroGapValues] at hg
  | cons x xs ih =>
      by_cases hx : Nat.floor x = 0
      · simp [zeroGapValues, hx] at hg
        rcases hg with rfl | hg
        · exact ⟨by simp, hx⟩
        · obtain ⟨hmem, hzero⟩ := ih hg
          exact ⟨by simp [hmem], hzero⟩
      · simp [zeroGapValues, hx] at hg
        obtain ⟨hmem, hzero⟩ := ih hg
        exact ⟨by simp [hmem], hzero⟩

theorem exists_le_third_of_nonneg_length_three
    {xs : List ℝ} {B : ℝ}
    (hlen : xs.length = 3)
    (h0 : ∀ x ∈ xs, 0 ≤ x)
    (hsum : xs.sum ≤ B) :
    ∃ x ∈ xs, x ≤ B / 3 := by
  obtain ⟨x,y,z,rfl⟩ := List.length_eq_three.mp hlen
  simp only [List.sum_cons, List.sum_nil, add_zero] at hsum
  have hx0 := h0 x (by simp)
  have hy0 := h0 y (by simp)
  have hz0 := h0 z (by simp)
  by_cases hx : x ≤ B / 3
  · exact ⟨x, by simp, hx⟩
  by_cases hy : y ≤ B / 3
  · exact ⟨y, by simp, hy⟩
  have hz : z ≤ B / 3 := by
    by_contra hnot
    have hx' : B / 3 < x := lt_of_not_ge hx
    have hy' : B / 3 < y := lt_of_not_ge hy
    have hz' : B / 3 < z := lt_of_not_ge hnot
    linarith
  exact ⟨z, by simp, hz⟩

theorem exists_adjacent_source_pair_of_diff_mem_successiveDiffsFrom
    {α : Type*}
    (f : α → ℝ)
    (first : α)
    (rest : List α)
    (hnodup : (first :: rest).Nodup)
    {g : ℝ}
    (hg : g ∈ successiveDiffsFrom (f first) (rest.map f)) :
    ∃ u v : α,
      u ≠ v ∧
      u ∈ first :: rest ∧
      v ∈ first :: rest ∧
      g = f v - f u := by
  induction rest generalizing first with
  | nil =>
      simp [successiveDiffsFrom] at hg
  | cons r rs ih =>
      have hnd := List.nodup_cons.mp hnodup
      have htail := List.nodup_cons.mp hnd.2
      simp only [List.map_cons, successiveDiffsFrom,
        List.mem_cons] at hg
      rcases hg with rfl | hg
      · have hfr : first ≠ r := by
          intro h
          apply hnd.1
          simp [h]
        exact ⟨first, r, hfr, by simp, by simp, rfl⟩
      · obtain ⟨u,v,huv,hu,hv,hgEq⟩ := ih r hnd.2 hg
        exact ⟨u,v,huv, by simp [hu], by simp [hv], hgEq⟩

theorem support_two_zero_gap_mass_le_one_add_delta
    {gs : List ℝ} {n : ℕ} {delta : ℝ}
    (hg0 : ∀ g ∈ gs, 0 ≤ g)
    (hgsum : gs.sum = (n : ℝ) + delta)
    (hqsum : (gs.map Nat.floor).sum = n - 1) :
    listZeroGapMass (gs.map Nat.floor) gs ≤ 1 + delta := by
  have halign :
      QuotientGapAligned 1 (gs.map Nat.floor) gs :=
    floor_gaps_aligned_at_one gs hg0
  have hmass :=
    listZeroGapMass_scaled_le_remainder halign
  have hlen :
      (gs.map Nat.floor).length = gs.length := by simp
  rw [listRemainderMass_eq 1 (gs.map Nat.floor) gs hlen,
      hgsum, hqsum] at hmass
  norm_num at hmass
  have hncast :
      (((n - 1 : ℕ) : ℝ)) ≥ (n : ℝ) - 1 := by
    by_cases hn0 : n = 0
    · subst n
      norm_num
    · have hn1 : 1 ≤ n := by omega
      rw [Nat.cast_sub hn1]
      norm_num
  linarith

/-- Main support-two bad-centre small-pair theorem. -/
theorem cutSaturationBadAt_support_two_has_subhalf_angle
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta c : ℝ} {n : ℕ}
    (hcardV : Fintype.card V = 6)
    (hn5 : 5 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c)
    (hcpi : c < Real.pi)
    (i : V)
    (hexp :
      centreExponent (C i) t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient (C i) t) = 2)
    (hbad :
      CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi i) :
    ∃ u v : OtherVertex i,
      u ≠ v ∧
      EuclideanGeometry.angle (p u.1) (p i) (p v.1)
        ≤ ((1 + delta) / 3) * lam := by
  let R : CentreCutRayCycle hp (C i) c :=
    Classical.choice (exists_centreCutRayCycle hp (C i) c)
  obtain ⟨a,xs,hvalues,hseam⟩ :=
    R.saturated_failure_has_wrap_unit_subslot_data
      hp hcap (by omega : 1 ≤ n)
      htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi (C i) R
      (by
        let htop : t < (n + 1 : ℕ) := by
          rw [ht]; push_cast; linarith
        let P :=
          cutProjectiveBandPartition
            hp hcap htpos hlam hc0 hcpi n htop
        let exponent : V → ℕ := fun v => centreExponent (C v) t
        have hb :
            SaturationCollisionFailure P exponent i := by
          simpa [CutSaturationBadAt, P, exponent, htop] using hbad
        simpa [P, exponent, htop] using hb.1)
      (by
        let htop : t < (n + 1 : ℕ) := by
          rw [ht]; push_cast; linarith
        let P :=
          cutProjectiveBandPartition
            hp hcap htpos hlam hc0 hcpi n htop
        let exponent : V → ℕ := fun v => centreExponent (C v) t
        have hb :
            SaturationCollisionFailure P exponent i := by
          simpa [CutSaturationBadAt, P, exponent, htop] using hbad
        simpa [P, htop] using hb.2)

  let gs := cyclicRealGapsAt t (a :: xs)
  have haMem : a ∈ R.normalizedValues t := by
    rw [hvalues]; simp
  have ha0 :
      0 ≤ a :=
    (R.normalizedValues_mem_bounds htpos hc0 hcpi haMem).1
  have hsorted :
      (a :: xs).Pairwise (· ≤ ·) := by
    simpa [hvalues] using R.normalizedValues_pairwise htpos.le
  have hall :
      ∀ x ∈ a :: xs, x < t := by
    intro x hx
    exact
      (R.normalizedValues_mem_bounds htpos hc0 hcpi
        (by simpa [hvalues] using hx)).2
  have hgs0 :
      ∀ g ∈ gs, 0 ≤ g := by
    dsimp [gs]
    exact cyclicRealGapsAt_nonneg_of_sorted ha0 hsorted hall
  have hgsum :
      gs.sum = (n : ℝ) + delta := by
    dsimp [gs]
    rw [cyclicRealGapsAt_sum_eq_width t a xs, ht]

  have hqPos :
      listPositiveCount (gs.map Nat.floor) = 2 := by
    have h :=
      R.gapQuotients_positiveCount_eq_canonical hp htpos
    rw [hsupport] at h
    have hmap :
        gs.map Nat.floor =
          linearCyclicGapQuotients t (a :: xs) := by
      dsimp [gs]
      simpa [cyclicRealGapsAt, cyclicGapsAt] using
        (linearCyclicGapQuotients_eq_floor_cyclicGapsAt
          t (a :: xs)).symm
    rw [hmap]
    simpa [CentreCutRayCycle.gapQuotients, hvalues] using h

  have hqExp :
      listExponent (gs.map Nat.floor) = n - 3 := by
    have h :=
      R.exponent_eq_centreExponent hp htpos
    rw [hexp] at h
    have hmap :
        gs.map Nat.floor =
          linearCyclicGapQuotients t (a :: xs) := by
      dsimp [gs]
      simpa [cyclicRealGapsAt, cyclicGapsAt] using
        (linearCyclicGapQuotients_eq_floor_cyclicGapsAt
          t (a :: xs)).symm
    rw [hmap]
    simpa [CentreCutRayCycle.exponent,
      CentreCutRayCycle.gapQuotients, hvalues] using h

  have hqsum :
      (gs.map Nat.floor).sum = n - 1 := by
    have hid :=
      listExponent_add_listPositiveCount (gs.map Nat.floor)
    rw [hqExp, hqPos] at hid
    omega

  have hgsLen : gs.length = 5 := by
    dsimp [gs]
    have hvalsLen :
        (a :: xs).length = 5 := by
      rw [← hvalues]
      simp [CentreCutRayCycle.normalizedValues,
        centreRayList_length_eq_five_of_card_six
          (C i) hcardV]
    simp [cyclicRealGapsAt, hvalsLen]
  have hzeroLen :
      (zeroGapValues (gs.map Nat.floor) gs).length = 3 := by
    rw [zeroGapValues_length _ _ (by simp)]
    simp [hgsLen, hqPos]

  have hzero0 :
      ∀ g ∈ zeroGapValues (gs.map Nat.floor) gs, 0 ≤ g := by
    intro g hg
    exact hgs0 g (mem_zeroGapValues_of_map_floor hg).1
  have hzeroSum :
      (zeroGapValues (gs.map Nat.floor) gs).sum ≤ 1 + delta := by
    rw [zeroGapValues_sum _ _ (by simp)]
    exact support_two_zero_gap_mass_le_one_add_delta
      hgs0 hgsum hqsum

  obtain ⟨g,hgZero,hgSmall⟩ :=
    exists_le_third_of_nonneg_length_three
      hzeroLen hzero0 hzeroSum
  obtain ⟨hgMem,hgFloor⟩ :=
    mem_zeroGapValues_of_map_floor hgZero

  have hwrapPos :
      2 ≤ Nat.floor (a + t - xs.getLastD a) :=
    hseam.1
  have hgSucc :
      g ∈ successiveDiffsFrom a xs := by
    dsimp [gs] at hgMem
    simp only [cyclicRealGapsAt, List.mem_append,
      List.mem_singleton] at hgMem
    rcases hgMem with h | h
    · exact h
    · subst g
      omega

  cases hrays : R.rays with
  | nil =>
      exact False.elim (R.nonempty hrays)
  | cons first rest =>
      have hvalues' :
          a :: xs =
            cutNormalizedRayTheta hp t c i first ::
              rest.map (cutNormalizedRayTheta hp t c i) := by
        rw [← hvalues]
        simp [CentreCutRayCycle.normalizedValues, hrays]
      have ha :
          a = cutNormalizedRayTheta hp t c i first :=
        (List.cons.inj hvalues').1
      have hxs :
          xs =
            rest.map (cutNormalizedRayTheta hp t c i) :=
        (List.cons.inj hvalues').2
      have hnod :
          (first :: rest).Nodup := by
        simpa [hrays] using R.nodup
      obtain ⟨u,v,huv,huMem,hvMem,hgEq⟩ :=
        exists_adjacent_source_pair_of_diff_mem_successiveDiffsFrom
          (cutNormalizedRayTheta hp t c i)
          first rest hnod
          (by simpa [ha,hxs] using hgSucc)
      have hcoordOrder :
          cutNormalizedRayTheta hp t c i u ≤
            cutNormalizedRayTheta hp t c i v := by
        have hs :
            (R.rays.map
              (cutNormalizedRayTheta hp t c i)).Pairwise (· ≤ ·) :=
          R.normalizedValues_pairwise htpos.le
        rw [hrays] at hs
        -- Membership comes from an adjacent successive difference; the
        -- equality hgEq and nonnegative g already give the needed order.
        have hg0 : 0 ≤ g := hgs0 g hgMem
        rw [hgEq] at hg0
        linarith
      have htheta :
          cutRayTheta hp c i u ≤ cutRayTheta hp c i v :=
        cutRayTheta_le_of_cutNormalized_le hp htpos i hcoordOrder
      have hsign :
          cutRaySign hp c i u = cutRaySign hp c i v := by
        by_contra hne
        have hcost :=
          one_le_t_mul_cutRay_gap_of_sign_ne
            hp hcap htpos hlam hc0 hcpi i
            huv htheta hne
        have hgapEq :
            t * ((cutRayTheta hp c i v -
              cutRayTheta hp c i u) / Real.pi) = g := by
          rw [hgEq]
          unfold cutNormalizedRayTheta
          ring
        rw [hgapEq] at hcost
        have hgLt : g < 1 := Nat.floor_eq_zero.mp hgFloor
        linarith
      have hscaled :
          t * ((cutRayTheta hp c i v -
            cutRayTheta hp c i u) / Real.pi)
            ≤ (1 + delta) / 3 := by
        have hgapEq :
            t * ((cutRayTheta hp c i v -
              cutRayTheta hp c i u) / Real.pi) = g := by
          rw [hgEq]
          unfold cutNormalizedRayTheta
          ring
        rw [hgapEq]
        exact hgSmall
      exact ⟨u,v,huv,
        actual_angle_le_delta_lam_of_cut_same_sign_gap
          hp htpos hlam hc0 hcpi i htheta hsign
          (by
            -- Reuse the angle lemma with the coefficient
            -- ((1+delta)/3) as its abstract "delta".
            exact hscaled)⟩

/-- The support-two sub-half pair avoids the sharp top. -/
theorem cutSaturationBadAt_support_two_subhalf_pair_avoids_sharp
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta c : ℝ} {n : ℕ}
    (hcardV : Fintype.card V = 6)
    (hn5 : 5 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c)
    (hcpi : c < Real.pi)
    {top i : V}
    (hti : top ≠ i)
    (hSharp : SharpAt p delta lam top)
    (hexp : centreExponent (C i) t = n - 3)
    (hsupport : positiveSupport (centreQuotient (C i) t) = 2)
    (hbad :
      CutSaturationBadAt hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1) hc0 hcpi i) :
    ∃ u v : OtherVertex i,
      u ≠ v ∧ u.1 ≠ top ∧ v.1 ≠ top ∧
      EuclideanGeometry.angle (p u.1) (p i) (p v.1)
        ≤ ((1 + delta) / 3) * lam := by
  obtain ⟨u,v,huv,hsmall⟩ :=
    cutSaturationBadAt_support_two_has_subhalf_angle
      hp hcap C hcardV hn5 htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi i hexp hsupport hbad
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hepsOuter :
      ((1 + delta) / 3) * lam < (1 - delta) * lam := by
    have hcoef : (1 + delta) / 3 < 1 - delta := by
      linarith
    nlinarith
  have huTop : u.1 ≠ top := by
    intro hu
    have htv : top ≠ v.1 := by
      intro hv
      apply huv
      apply Subtype.ext
      exact hu.trans hv.symm
    have houter :=
      outer_angle_ge_one_sub_delta_mul_lam_of_sharp
        hp hcap hti htv v.2.symm hSharp
    have hsmall' :
        EuclideanGeometry.angle (p top) (p i) (p v.1)
          ≤ ((1 + delta) / 3) * lam := by
      simpa [hu] using hsmall
    linarith
  have hvTop : v.1 ≠ top := by
    intro hv
    have htu : top ≠ u.1 := by
      intro hu
      apply huv
      apply Subtype.ext
      exact hu.symm.trans hv
    have houter :=
      outer_angle_ge_one_sub_delta_mul_lam_of_sharp
        hp hcap hti htu u.2.symm hSharp
    have hcomm :
        EuclideanGeometry.angle (p u.1) (p i) (p top) =
          EuclideanGeometry.angle (p top) (p i) (p u.1) :=
      EuclideanGeometry.angle_comm _ _ _
    have hsmall' :
        EuclideanGeometry.angle (p top) (p i) (p u.1)
          ≤ ((1 + delta) / 3) * lam := by
      rw [← hcomm]
      simpa [hv] using hsmall
    linarith
  exact ⟨u,v,huv,huTop,hvTop,hsmall⟩

#print axioms zeroGapValues_length
#print axioms mem_zeroGapValues_of_map_floor
#print axioms exists_le_third_of_nonneg_length_three
#print axioms cutSaturationBadAt_support_two_has_subhalf_angle
#print axioms cutSaturationBadAt_support_two_subhalf_pair_avoids_sharp

end JSP000404Research
