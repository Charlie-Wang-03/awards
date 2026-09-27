import JSP000404Research.CutSupportThreeBadSmallAngle
import JSP000404Research.SixPointSupportThreeShape
import Mathlib.Tactic

/-!
# Same-band delta-small pair at a support-three saturation-bad minimum

At a six-point centre there are exactly five cut-sorted rays.  If an exact
n-3 minimum is saturation-bad, its old cut palette has exactly four occupied
bands.  Hence the five sorted band labels are not nodup.  Because they are
nondecreasing, some two consecutive cut rays lie in the same old unit band.

For support three the cut quotient support is exactly three, so the five
cyclic gaps contain exactly two quotient-zero positions.  Their total scaled
gap mass is at most delta.  In particular the same-band consecutive pair has
scaled gap at most delta.  A quotient-zero gap cannot change the adjusted
cut sign, hence its genuine Euclidean angle is at most delta*lambda.

Together with CutSupportThreeBadSmallAngle, a support-three bad minimum thus
carries both:
* one adjacent-band delta-small pair (the unique q=0,b=1 mismatch), and
* one same-band delta-small pair (a q=0,b=0 position).
-/

namespace JSP000404Research

open BinaryEdgePartition
open Real

/-- In a nondecreasing mapped list, any repetition occurs already at two
consecutive source entries. -/
theorem exists_adjacent_map_eq_of_pairwise_of_not_nodup
    {α β : Type*} [LinearOrder β]
    (f : α → β)
    (xs : List α)
    (hsorted : (xs.map f).Pairwise (· ≤ ·))
    (hnot : ¬ (xs.map f).Nodup) :
    ∃ pre : List α, ∃ u v : α, ∃ post : List α,
      xs = pre ++ u :: v :: post ∧
      f u = f v := by
  induction xs with
  | nil =>
      exact False.elim (hnot (by simp))
  | cons a tail ih =>
      cases tail with
      | nil =>
          exact False.elim (hnot (by simp))
      | cons b bs =>
          have hp :=
            List.pairwise_cons.mp hsorted
          by_cases hab : f a = f b
          · exact ⟨[], a, b, bs, by simp, hab⟩
          · have htailNot :
                ¬ ((b :: bs).map f).Nodup := by
              intro htailNodup
              apply hnot
              apply List.nodup_cons.mpr
              constructor
              · intro hmem
                rw [List.mem_map] at hmem
                obtain ⟨z, hz, hza⟩ := hmem
                simp only [List.mem_cons] at hz
                rcases hz with hzb | hzbs
                · subst z
                  exact hab hza
                · have habLe :
                      f a ≤ f b :=
                    hp.1 (f b) (by simp)
                  have htailPair :=
                    List.pairwise_cons.mp hp.2
                  have hbz :
                      f b ≤ f z :=
                    htailPair.1 (f z) (by
                      rw [List.mem_map]
                      exact ⟨z, hzbs, rfl⟩)
                  have hba :
                      f b ≤ f a := by
                    rw [← hza] at hbz
                    exact hbz
                  exact hab (le_antisymm habLe hba)
              · exact htailNodup
            have htailSorted : ((b :: bs).map f).Pairwise (· ≤ ·) :=
              hp.2
            obtain ⟨pre, u, v, post, hdec, huv⟩ :=
              ih htailSorted htailNot
            exact ⟨a :: pre, u, v, post,
              by simp [hdec], huv⟩

/-- The difference across a displayed adjacent source pair occurs among the
ordinary successive differences of the mapped list. -/
theorem adjacent_sub_mem_successiveDiffsFrom
    {α : Type*}
    (f : α → ℝ)
    (first : α) (rest : List α)
    (pre post : List α)
    (u v : α)
    (hdec :
      first :: rest = pre ++ u :: v :: post) :
    f v - f u ∈
      successiveDiffsFrom (f first) (rest.map f) := by
  induction pre generalizing first rest with
  | nil =>
      simp only [List.nil_append] at hdec
      injection hdec with hfirst hrest
      subst first
      subst rest
      simp [successiveDiffsFrom]
  | cons w ws ih =>
      simp only [List.cons_append] at hdec
      injection hdec with hfirst hrest
      subst first
      subst rest
      cases ws with
      | nil =>
          simp [successiveDiffsFrom]
      | cons z zs =>
          simp only [List.cons_append, List.map_cons,
            successiveDiffsFrom, List.mem_cons]
          right
          exact ih z
            (zs ++ u :: v :: post)
            rfl

/-- The same adjacent difference is a member of the full cyclic real-gap
list. -/
theorem adjacent_sub_mem_cyclicRealGapsAt
    {α : Type*}
    (width : ℝ)
    (f : α → ℝ)
    (xs pre post : List α)
    (u v : α)
    (hdec : xs = pre ++ u :: v :: post) :
    f v - f u ∈
      cyclicRealGapsAt width (xs.map f) := by
  subst xs
  cases pre with
  | nil =>
      simp [cyclicRealGapsAt, successiveDiffsFrom]
  | cons first rest =>
      simp only [List.cons_append, List.map_append,
        List.map_cons, cyclicRealGapsAt, List.mem_append]
      left
      exact adjacent_sub_mem_successiveDiffsFrom
        f first (rest ++ u :: v :: post)
        (first :: rest) post u v rfl

/-- Cyclic real gaps of a sorted list in [0,width) are nonnegative. -/
theorem cyclicRealGapsAt_nonneg_of_sorted
    {width a : ℝ} {xs : List ℝ}
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall : ∀ x ∈ a :: xs, x < width) :
    ∀ g ∈ cyclicRealGapsAt width (a :: xs), 0 ≤ g := by
  intro g hg
  simp only [cyclicRealGapsAt, List.mem_append,
    List.mem_singleton] at hg
  rcases hg with hg | rfl
  · induction xs generalizing a with
    | nil =>
        simp [successiveDiffsFrom] at hg
    | cons b bs ih =>
        have hp := List.pairwise_cons.mp hsorted
        simp only [successiveDiffsFrom, List.mem_cons] at hg
        rcases hg with rfl | hg
        · exact sub_nonneg.mpr (hp.1 b (by simp))
        · have hb0 : 0 ≤ b :=
            ha0.trans (hp.1 b (by simp))
          exact ih b hb0 hp.2
            (fun x hx => hall x (by simp [hx])) hg
  · have hlast :
        xs.getLastD a < width :=
      hall _ (List.getLastD_mem_cons a xs)
    have hafirst :
        a ≤ xs.getLastD a :=
      head_le_getLastD_of_pairwise a xs hsorted
    linarith

/-- A support-three saturation-bad six-point minimum contains two consecutive
cut rays in the same old band whose genuine angle is at most delta*lambda. -/
theorem cutSaturationBadAt_support_three_has_delta_small_same_band_angle
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
      positiveSupport (centreQuotient (C i) t) = 3)
    (hbad :
      CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi i) :
    ∃ u v : OtherVertex i,
      u ≠ v ∧
      Nat.floor (cutNormalizedRayTheta hp t c i u) =
        Nat.floor (cutNormalizedRayTheta hp t c i v) ∧
      EuclideanGeometry.angle (p u.1) (p i) (p v.1)
        ≤ delta * lam := by
  let htop : t < (n + 1 : ℕ) := by
    rw [ht]
    push_cast
    linarith
  let P :=
    cutProjectiveBandPartition
      hp hcap htpos hlam hc0 hcpi n htop
  let exponent : V → ℕ :=
    fun v => centreExponent (C v) t

  have hbad' :
      SaturationCollisionFailure P exponent i := by
    simpa [CutSaturationBadAt, P, exponent, htop] using hbad
  have hactive4 :
      (active P i).card = 4 := by
    rw [hbad'.1]
    dsimp [exponent]
    rw [hexp]
    omega

  let R : CentreCutRayCycle hp (C i) c :=
    Classical.choice (exists_centreCutRayCycle hp (C i) c)
  let coord : OtherVertex i → ℝ :=
    cutNormalizedRayTheta hp t c i
  let band : OtherVertex i → ℕ :=
    fun r => Nat.floor (coord r)

  have hoccR :
      (occupiedNatBands (R.normalizedValues t)).card =
        (occupiedCutProjectiveBands hp t c n i).card :=
    R.occupiedNatBands_normalizedValues_card_eq_occupiedCut
      hp htpos hc0 hcpi n htop
  have hactiveOcc :
      (active P i).card =
        (occupiedCutProjectiveBands hp t c n i).card := by
    dsimp [P]
    rw [cutProjectiveBandPartition_active_eq_occupied
      hp hcap htpos hlam hc0 hcpi n htop i]
  have hocc4 :
      (occupiedNatBands (R.normalizedValues t)).card = 4 := by
    omega

  have hlenR : R.rays.length = 5 := by
    obtain ⟨k, hk⟩ := R.rotation
    rw [hk, List.length_rotate,
      centreRayList_length_eq_five_of_card_six (C i) hcardV]

  have hlabelCard :
      (R.rays.map band).toFinset.card = 4 := by
    have h :
        (R.rays.map band).toFinset =
          occupiedNatBands (R.normalizedValues t) := by
      unfold band coord occupiedNatBands
      simp [CentreCutRayCycle.normalizedValues,
        List.map_map, Function.comp_def]
    rw [h, hocc4]

  have hlabelLen :
      (R.rays.map band).length = 5 := by
    simp [hlenR]

  have hlabelNotNodup :
      ¬ (R.rays.map band).Nodup := by
    intro hnd
    have hc :=
      List.toFinset_card_of_nodup hnd
    rw [hlabelCard, hlabelLen] at hc
    omega

  have hvalueSorted :
      (R.rays.map coord).Pairwise (· ≤ ·) := by
    simpa [coord, CentreCutRayCycle.normalizedValues] using
      R.normalizedValues_pairwise htpos.le

  have hfloorValueSorted :
      ((R.normalizedValues t).map Nat.floor).Pairwise (· ≤ ·) := by
    rw [List.pairwise_map]
    exact
      (R.normalizedValues_pairwise htpos.le).imp
        (fun _ _ hxy => Nat.floor_mono hxy)

  have hlabelSorted :
      (R.rays.map band).Pairwise (· ≤ ·) := by
    simpa [band, coord,
      CentreCutRayCycle.normalizedValues,
      List.map_map, Function.comp_def] using hfloorValueSorted

  obtain ⟨pre, u, v, post, hdec, hbandEq⟩ :=
    exists_adjacent_map_eq_of_pairwise_of_not_nodup
      band R.rays hlabelSorted hlabelNotNodup

  have huv : u ≠ v := by
    intro huv
    subst v
    have hnd := R.nodup
    rw [hdec] at hnd
    simp at hnd

  have hcoordLe :
      coord u ≤ coord v := by
    have hs := hvalueSorted
    rw [hdec] at hs
    simp only [List.map_append, List.map_cons] at hs
    have hsuf :=
      (List.pairwise_append.mp hs).2.1
    exact (List.pairwise_cons.mp hsuf).1
      (coord v) (by simp)

  have hcoordU0 : 0 ≤ coord u :=
    cutNormalizedRayTheta_nonneg
      hp htpos.le hc0 hcpi i u
  have hgapFloor :
      Nat.floor (coord v - coord u) = 0 :=
    natFloor_sub_eq_zero_of_floor_eq
      hcoordU0 hcoordLe hbandEq.symm

  have hgapMem :
      coord v - coord u ∈
        cyclicRealGapsAt t (R.normalizedValues t) := by
    have h :=
      adjacent_sub_mem_cyclicRealGapsAt
        t coord R.rays pre post u v hdec
    simpa [coord, CentreCutRayCycle.normalizedValues] using h

  obtain ⟨a, xs, hvalues⟩ :
      ∃ a xs, R.normalizedValues t = a :: xs := by
    cases hv : R.normalizedValues t with
    | nil =>
        exact False.elim (R.normalizedValues_nonempty t hv)
    | cons a xs =>
        exact ⟨a, xs, hv⟩

  have haMem : a ∈ R.normalizedValues t := by
    rw [hvalues]
    simp
  have ha0 :
      0 ≤ a :=
    (R.normalizedValues_mem_bounds
      htpos hc0 hcpi haMem).1
  have hsorted :
      (a :: xs).Pairwise (· ≤ ·) := by
    simpa [hvalues] using R.normalizedValues_pairwise htpos.le
  have hallT :
      ∀ x ∈ a :: xs, x < t := by
    intro x hx
    exact
      (R.normalizedValues_mem_bounds
        htpos hc0 hcpi
        (by simpa [hvalues] using hx)).2

  let qs := linearCyclicGapQuotients t (a :: xs)
  have hqPos :
      listPositiveCount qs = 3 := by
    have h :=
      R.gapQuotients_positiveCount_eq_canonical hp htpos
    rw [hsupport] at h
    simpa [qs, CentreCutRayCycle.gapQuotients,
      hvalues] using h
  have hqExp :
      listExponent qs = n - 3 := by
    have h :=
      R.exponent_eq_centreExponent hp htpos
    rw [hexp] at h
    simpa [qs, CentreCutRayCycle.exponent,
      CentreCutRayCycle.gapQuotients, hvalues] using h
  have hqSum : qs.sum = n := by
    have hid := listExponent_add_listPositiveCount qs
    rw [hqExp, hqPos] at hid
    omega

  let gs := cyclicRealGapsAt t (a :: xs)
  have hgsum :
      gs.sum = (n : ℝ) + delta := by
    rw [cyclicRealGapsAt_sum_eq_width t a xs, ht]
  have hgs0 :
      ∀ g ∈ gs, 0 ≤ g :=
    cyclicRealGapsAt_nonneg_of_sorted
      ha0 hsorted hallT
  have hqMap :
      gs.map Nat.floor = qs := by
    dsimp [gs, qs]
    simpa [cyclicRealGapsAt, cyclicGapsAt] using
      (linearCyclicGapQuotients_eq_floor_cyclicGapsAt
        t (a :: xs)).symm
  have hgapMem' :
      coord v - coord u ∈ gs := by
    simpa [gs, hvalues] using hgapMem

  have hgapLe :
      coord v - coord u ≤ delta := by
    apply floor_zero_member_le_delta_of_sum
      hgs0 hgsum
    · simpa [hqMap] using hqSum
    · exact hgapMem'
    · exact hgapFloor

  have hthetaLe :
      cutRayTheta hp c i u ≤
        cutRayTheta hp c i v :=
    cutRayTheta_le_of_cutNormalized_le
      hp htpos i hcoordLe

  have hsign :
      cutRaySign hp c i u =
        cutRaySign hp c i v := by
    by_contra hne
    have hcost :=
      one_le_t_mul_cutRay_gap_of_sign_ne
        hp hcap htpos hlam hc0 hcpi i
        huv hthetaLe hne
    have hgapEq :
        t * ((cutRayTheta hp c i v -
          cutRayTheta hp c i u) / Real.pi)
          =
        coord v - coord u := by
      dsimp [coord]
      unfold cutNormalizedRayTheta
      ring
    rw [hgapEq] at hcost
    have hgapLt :
        coord v - coord u < 1 :=
      Nat.floor_eq_zero.mp hgapFloor
    linarith

  have hscaled :
      t * ((cutRayTheta hp c i v -
        cutRayTheta hp c i u) / Real.pi) ≤ delta := by
    have hgapEq :
        t * ((cutRayTheta hp c i v -
          cutRayTheta hp c i u) / Real.pi)
          =
        coord v - coord u := by
      dsimp [coord]
      unfold cutNormalizedRayTheta
      ring
    rw [hgapEq]
    exact hgapLe

  exact ⟨u, v, huv, hbandEq,
    actual_angle_le_delta_lam_of_cut_same_sign_gap
      hp htpos hlam hc0 hcpi i
      hthetaLe hsign hscaled⟩

/-- With a sharp top present, neither endpoint of the same-band delta-small
pair can be the top ray. -/
theorem cutSaturationBadAt_support_three_same_band_pair_avoids_sharp
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
    (hexp :
      centreExponent (C i) t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient (C i) t) = 3)
    (hbad :
      CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi i) :
    ∃ u v : OtherVertex i,
      u ≠ v ∧
      u.1 ≠ top ∧
      v.1 ≠ top ∧
      Nat.floor (cutNormalizedRayTheta hp t c i u) =
        Nat.floor (cutNormalizedRayTheta hp t c i v) ∧
      EuclideanGeometry.angle (p u.1) (p i) (p v.1)
        ≤ delta * lam := by
  obtain ⟨u, v, huv, hband, hsmall⟩ :=
    cutSaturationBadAt_support_three_has_delta_small_same_band_angle
      hp hcap C hcardV hn5 htpos hlam ht
      hdelta0 hdeltaHalf hc0 hcpi
      i hexp hsupport hbad
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have huTop : u.1 ≠ top := by
    intro hu
    have htv : top ≠ v.1 := by
      intro hv
      apply huv
      apply Subtype.ext
      exact hu.trans hv.symm
    have hlow :=
      delta_mul_lam_lt_outer_angle_of_sharp
        hp hcap hdeltaHalf hlampos
        hti htv v.2.symm hSharp
    have hsmall' :
        EuclideanGeometry.angle (p top) (p i) (p v.1)
          ≤ delta * lam := by
      simpa [hu] using hsmall
    linarith
  have hvTop : v.1 ≠ top := by
    intro hv
    have htu : top ≠ u.1 := by
      intro hu
      apply huv
      apply Subtype.ext
      exact hu.symm.trans hv
    have hlow :=
      delta_mul_lam_lt_outer_angle_of_sharp
        hp hcap hdeltaHalf hlampos
        hti htu u.2.symm hSharp
    have hcomm :
        EuclideanGeometry.angle (p u.1) (p i) (p top) =
          EuclideanGeometry.angle (p top) (p i) (p u.1) :=
      EuclideanGeometry.angle_comm _ _ _
    have hsmall' :
        EuclideanGeometry.angle (p top) (p i) (p u.1)
          ≤ delta * lam := by
      rw [← hcomm]
      simpa [hv] using hsmall
    linarith
  exact ⟨u, v, huv, huTop, hvTop, hband, hsmall⟩

#print axioms exists_adjacent_map_eq_of_pairwise_of_not_nodup
#print axioms adjacent_sub_mem_cyclicRealGapsAt
#print axioms cyclicRealGapsAt_nonneg_of_sorted
#print axioms cutSaturationBadAt_support_three_has_delta_small_same_band_angle
#print axioms cutSaturationBadAt_support_three_same_band_pair_avoids_sharp

end JSP000404Research
