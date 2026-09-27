import JSP000404Research.CutSaturatedSupportMismatch
import JSP000404Research.CutZeroUnitStep
import JSP000404Research.ListZeroGapMass
import JSP000404Research.CutCentreTransitionPath
import JSP000404Research.SignedRayAngle
import Mathlib.Tactic

/-!
# Delta-small angle forced by a support-three bad cut centre

For a deficit-three/support-three centre,

  exponent = n-3,   positive support = 3,

so the cut quotient sum is exactly n.  The cut-sorted cyclic real gaps have
total width t=n+delta.  Hence the total mass of all quotient-zero cut gaps is
at most delta.

A saturation collision failure supplies a quotient-zero unit-band crossing.
We retain that exact recursive witness, so the same concrete adjacent ray pair
is known to occur in the cut successive-gap list.  Its scaled gap is therefore
at most delta.  A quotient-zero gap cannot change the adjusted cut sign, and
the genuine Euclidean angle is at most delta*lambda.
-/

namespace JSP000404Research

open Real

theorem successiveDiffsFrom_sum_telescoping_real
    (a : ℝ) (xs : List ℝ) :
    (successiveDiffsFrom a xs).sum =
      xs.getLastD a - a := by
  induction xs generalizing a with
  | nil =>
      simp [successiveDiffsFrom]
  | cons b bs ih =>
      simp only [successiveDiffsFrom, List.sum_cons]
      rw [ih b]
      cases bs with
      | nil =>
          simp
      | cons d ds =>
          simp [List.getLastD_cons]
          ring

theorem cyclicRealGapsAt_sum_eq_width
    (width a : ℝ) (xs : List ℝ) :
    (cyclicRealGapsAt width (a :: xs)).sum = width := by
  simp only [cyclicRealGapsAt, List.sum_append,
    List.sum_singleton]
  rw [successiveDiffsFrom_sum_telescoping_real]
  ring

theorem floor_gaps_aligned_at_one
    (gs : List ℝ)
    (hg0 : ∀ g ∈ gs, 0 ≤ g) :
    QuotientGapAligned 1 (gs.map Nat.floor) gs := by
  induction gs with
  | nil =>
      exact List.Forall₂.nil
  | cons g gs ih =>
      apply List.Forall₂.cons
      · simpa using Nat.floor_le (hg0 g (by simp))
      · apply ih
        intro x hx
        exact hg0 x (by simp [hx])

theorem listZeroGapMass_ge_member_of_floor_zero
    {gs : List ℝ} {g : ℝ}
    (hg0 : ∀ x ∈ gs, 0 ≤ x)
    (hgmem : g ∈ gs)
    (hfloor : Nat.floor g = 0) :
    g ≤ listZeroGapMass (gs.map Nat.floor) gs := by
  induction gs with
  | nil =>
      simp at hgmem
  | cons x xs ih =>
      simp only [List.mem_cons] at hgmem
      rcases hgmem with rfl | hgmem
      · have htail0 :
            0 ≤ listZeroGapMass (xs.map Nat.floor) xs := by
          apply listZeroGapMass_nonneg
          · simp
          · intro y hy
            exact hg0 y (by simp [hy])
        simp [listZeroGapMass, hfloor]
        exact htail0
      · have htail :=
          ih
            (fun y hy => hg0 y (by simp [hy]))
            hgmem hfloor
        by_cases hx : Nat.floor x = 0
        · have hx0 := hg0 x (by simp)
          simp [listZeroGapMass, hx]
          linarith
        · simpa [listZeroGapMass, hx] using htail

theorem floor_zero_member_le_delta_of_sum
    {gs : List ℝ} {g delta : ℝ} {n : ℕ}
    (hg0 : ∀ x ∈ gs, 0 ≤ x)
    (hgsum : gs.sum = (n : ℝ) + delta)
    (hqsum : (gs.map Nat.floor).sum = n)
    (hgmem : g ∈ gs)
    (hfloor : Nat.floor g = 0) :
    g ≤ delta := by
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
  have hgLe :=
    listZeroGapMass_ge_member_of_floor_zero
      hg0 hgmem hfloor
  linarith

theorem exists_cutRay_pair_mem_successive_of_rayStep
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (t c : ℝ) (i : V)
    (prev : OtherVertex i)
    (rs : List (OtherVertex i))
    (hstep :
      HasZeroQuotientUnitCutRayStepFrom
        hp t c i prev rs) :
    ∃ u v : OtherVertex i,
      Nat.floor (cutNormalizedRayTheta hp t c i v) =
          Nat.floor (cutNormalizedRayTheta hp t c i u) + 1 ∧
      Nat.floor
        (cutNormalizedRayTheta hp t c i v -
          cutNormalizedRayTheta hp t c i u) = 0 ∧
      (cutNormalizedRayTheta hp t c i v -
          cutNormalizedRayTheta hp t c i u)
        ∈
      successiveDiffsFrom
        (cutNormalizedRayTheta hp t c i prev)
        (rs.map (cutNormalizedRayTheta hp t c i)) := by
  induction rs generalizing prev with
  | nil =>
      simp [HasZeroQuotientUnitCutRayStepFrom] at hstep
  | cons r rs ih =>
      rw [hasZeroQuotientUnitCutRayStepFrom_cons] at hstep
      rcases hstep with hhead | htail
      · exact ⟨prev, r, hhead.1, hhead.2,
          by simp [successiveDiffsFrom]⟩
      · obtain ⟨u, v, hband, hzero, hmem⟩ :=
          ih r htail
        exact ⟨u, v, hband, hzero,
          by simp [successiveDiffsFrom, hmem]⟩

theorem CentreCutRayCycle.exists_cutRay_pair_mem_successive_of_zeroUnitStep
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} {c t : ℝ}
    {C : CentreProjectiveCycle hp i}
    (R : CentreCutRayCycle hp C c)
    {a : ℝ} {xs : List ℝ}
    (hvalues : R.normalizedValues t = a :: xs)
    (hstep : HasZeroQuotientUnitStep a xs) :
    ∃ u v : OtherVertex i,
      u ≠ v ∧
      Nat.floor (cutNormalizedRayTheta hp t c i v) =
          Nat.floor (cutNormalizedRayTheta hp t c i u) + 1 ∧
      Nat.floor
        (cutNormalizedRayTheta hp t c i v -
          cutNormalizedRayTheta hp t c i u) = 0 ∧
      (cutNormalizedRayTheta hp t c i v -
          cutNormalizedRayTheta hp t c i u)
        ∈ successiveDiffsFrom a xs := by
  cases hrays : R.rays with
  | nil =>
      exact False.elim (R.nonempty hrays)
  | cons first rest =>
      have hvalues' :
          R.normalizedValues t =
            cutNormalizedRayTheta hp t c i first ::
              rest.map (cutNormalizedRayTheta hp t c i) := by
        simp [CentreCutRayCycle.normalizedValues, hrays]
      have hcons :
          a :: xs =
            cutNormalizedRayTheta hp t c i first ::
              rest.map (cutNormalizedRayTheta hp t c i) := by
        rw [← hvalues, hvalues']
      have ha :
          a = cutNormalizedRayTheta hp t c i first :=
        (List.cons.inj hcons).1
      have hxs :
          xs =
            rest.map (cutNormalizedRayTheta hp t c i) :=
        (List.cons.inj hcons).2
      have hstep' :
          HasZeroQuotientUnitCutRayStepFrom
            hp t c i first rest := by
        apply
          (hasZeroQuotientUnitStep_map_cut_iff_rayStep
            hp t c i first rest).1
        simpa [ha, hxs] using hstep
      obtain ⟨u, v, hband, hzero, hmem⟩ :=
        exists_cutRay_pair_mem_successive_of_rayStep
          hp t c i first rest hstep'
      have huv : u ≠ v := by
        intro huv
        subst v
        omega
      refine ⟨u, v, huv, hband, hzero, ?_⟩
      simpa [ha, hxs] using hmem

theorem cutNormalized_lt_of_floor_succ
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t c : ℝ}
    (ht : 0 < t)
    (hc0 : 0 ≤ c)
    (hcpi : c < Real.pi)
    (i : V)
    {u v : OtherVertex i}
    (hband :
      Nat.floor (cutNormalizedRayTheta hp t c i v) =
        Nat.floor (cutNormalizedRayTheta hp t c i u) + 1) :
    cutNormalizedRayTheta hp t c i u <
      cutNormalizedRayTheta hp t c i v := by
  have hu0 :
      0 ≤ cutNormalizedRayTheta hp t c i u :=
    cutNormalizedRayTheta_nonneg hp ht.le hc0 hcpi i u
  have hv0 :
      0 ≤ cutNormalizedRayTheta hp t c i v :=
    cutNormalizedRayTheta_nonneg hp ht.le hc0 hcpi i v
  have huHi :
      cutNormalizedRayTheta hp t c i u <
        (Nat.floor
          (cutNormalizedRayTheta hp t c i u) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hvLo :
      (Nat.floor
        (cutNormalizedRayTheta hp t c i v) : ℝ)
        ≤ cutNormalizedRayTheta hp t c i v :=
    Nat.floor_le hv0
  rw [hband] at hvLo
  push_cast at hvLo
  linarith

theorem cutRayTheta_le_of_cutNormalized_le
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t c : ℝ}
    (ht : 0 < t)
    (i : V)
    {u v : OtherVertex i}
    (h :
      cutNormalizedRayTheta hp t c i u ≤
        cutNormalizedRayTheta hp t c i v) :
    cutRayTheta hp c i u ≤ cutRayTheta hp c i v := by
  unfold cutNormalizedRayTheta at h
  have hcoef : 0 < t / Real.pi :=
    div_pos ht Real.pi_pos
  have h' :
      (t / Real.pi) * cutRayTheta hp c i u ≤
        (t / Real.pi) * cutRayTheta hp c i i v := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm,
      mul_comm] using h
  exact (mul_le_mul_left hcoef).mp h'

theorem actual_angle_eq_cut_gap_of_sign_eq
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {c : ℝ}
    (hc0 : 0 ≤ c)
    (hcpi : c < Real.pi)
    (i : V)
    {u v : OtherVertex i}
    (horder :
      cutRayTheta hp c i u ≤
        cutRayTheta hp c i v)
    (hsign :
      cutRaySign hp c i u =
        cutRaySign hp c i v) :
    EuclideanGeometry.angle (p u.1) (p i) (p v.1) =
      cutRayTheta hp c i v - cutRayTheta hp c i u := by
  have hu0 := cutRayTheta_nonneg hp hc0 hcpi i u
  have hvpi := cutRayTheta_lt_pi hp hc0 hcpi i v
  have hspan :
      cutRayTheta hp c i v - cutRayTheta hp c i u ≤ Real.pi := by
    linarith
  have habs :
      |(c + cutRayTheta hp c i u) -
        (c + cutRayTheta hp c i v)|
        =
      cutRayTheta hp c i v - cutRayTheta hp c i u := by
    rw [abs_of_nonpos]
    · ring
    · linarith
  change
    InnerProductGeometry.angle
        (p u.1 - p i) (p v.1 - p i) =
      cutRayTheta hp c i v - cutRayTheta hp c i u
  rw [cutRayRepAt_eq hp c i u,
      cutRayRepAt_eq hp c i v,
      angle_positive_smul_signedRay
        (rayRhoAt_pos hp i u) (rayRhoAt_pos hp i v)]
  rw [angle_signedRayDirection_eq_of_sign_eq hsign]
  · exact habs
  · rw [habs]
    exact hspan

theorem actual_angle_le_delta_lam_of_cut_same_sign_gap
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t lam delta c : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c)
    (hcpi : c < Real.pi)
    (i : V)
    {u v : OtherVertex i}
    (horder :
      cutRayTheta hp c i u ≤
        cutRayTheta hp c i v)
    (hsign :
      cutRaySign hp c i u =
        cutRaySign hp c i v)
    (hsmall :
      t * ((cutRayTheta hp c i v -
        cutRayTheta hp c i u) / Real.pi) ≤ delta) :
    EuclideanGeometry.angle (p u.1) (p i) (p v.1)
      ≤ delta * lam := by
  rw [actual_angle_eq_cut_gap_of_sign_eq
      hp hc0 hcpi i horder hsign, hlam]
  have hcoef : 0 < t / Real.pi :=
    div_pos ht Real.pi_pos
  have hsmall' :
      (t / Real.pi) *
          (cutRayTheta hp c i v -
            cutRayTheta hp c i u)
        ≤ delta := by
    convert hsmall using 1 <;> ring
  have hdiv :=
    (le_div_iff₀ hcoef).mpr hsmall'
  field_simp [ne_of_gt ht, Real.pi_ne_zero] at hdiv ⊢
  nlinarith

theorem cutSaturationBadAt_support_three_has_delta_small_angle
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta c : ℝ} {n : ℕ}
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
      EuclideanGeometry.angle (p u.1) (p i) (p v.1)
        ≤ delta * lam := by
  let R : CentreCutRayCycle hp (C i) c :=
    Classical.choice (exists_centreCutRayCycle hp (C i) c)
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
  have hsat :
      centreExponent (C i) t +
        (BinaryEdgePartition.active P i).card = n + 1 := by
    simpa [exponent] using hbad'.1
  have hfail :
      ¬ (
        (0 : Fin (n + 1)) ∈ BinaryEdgePartition.active P i ∧
        Fin.last n ∈ BinaryEdgePartition.active P i) :=
    hbad'.2

  obtain ⟨a, xs, hvalues, hstep⟩ :=
    R.zeroUnitStep_of_saturated_boundary_collision_failure
      hp hcap (by omega : 1 ≤ n)
      htpos hlam ht hdeltaHalf
      hc0 hcpi hsat
      (by simpa [P, htop] using hfail)

  obtain ⟨u, v, huv, hband, hfloor0, hgapMem⟩ :=
    R.exists_cutRay_pair_mem_successive_of_zeroUnitStep
      hvalues hstep

  let qs := linearCyclicGapQuotients t (a :: xs)
  have hqPos :
      listPositiveCount qs = 3 := by
    have h :=
      R.gapQuotients_positiveCount_eq_canonical hp htpos
    rw [hsupport] at h
    simpa [qs, CentreCutRayCycle.gapQuotients, hvalues] using h
  have hqExp :
      listExponent qs = n - 3 := by
    have h := R.exponent_eq_centreExponent hp htpos
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
  have hgs0 :
      ∀ g ∈ gs, 0 ≤ g := by
    intro g hg
    dsimp [gs] at hg
    simp only [cyclicRealGapsAt, List.mem_append,
      List.mem_singleton] at hg
    rcases hg with hg | rfl
    · induction xs generalizing a with
      | nil =>
          simp [successiveDiffsFrom] at hg
      | cons b bs ih =>
          have hpw := List.pairwise_cons.mp hsorted
          simp only [successiveDiffsFrom, List.mem_cons] at hg
          rcases hg with rfl | hg
          · exact sub_nonneg.mpr (hpw.1 b (by simp))
          · exact ih b hpw.2
              (fun x hx => hallT x (by simp [hx])) hg
    · have hz :
          xs.getLastD a < t :=
        hallT _ (List.getLastD_mem_cons a xs)
      have haz :
          a ≤ xs.getLastD a := by
        cases xs with
        | nil => simp
        | cons b bs =>
            exact
              (List.pairwise_cons.mp hsorted).1
                ((b :: bs).getLastD a)
                (by simpa using
                  (List.getLastD_mem_cons a (b :: bs)))
      linarith

  have hqMap :
      gs.map Nat.floor = qs := by
    dsimp [gs, qs]
    simpa [cyclicRealGapsAt, cyclicGapsAt] using
      (linearCyclicGapQuotients_eq_floor_cyclicGapsAt
        t (a :: xs)).symm

  let g :=
    cutNormalizedRayTheta hp t c i v -
      cutNormalizedRayTheta hp t c i u
  have hgMem : g ∈ gs := by
    dsimp [g, gs]
    simp [cyclicRealGapsAt, hgapMem]
  have hgFloor : Nat.floor g = 0 := hfloor0
  have hgLe : g ≤ delta := by
    apply floor_zero_member_le_delta_of_sum
      hgs0 hgsum
    · simpa [hqMap] using hqSum
    · exact hgMem
    · exact hgFloor

  have hcoordLt :
      cutNormalizedRayTheta hp t c i u <
        cutNormalizedRayTheta hp t c i v :=
    cutNormalized_lt_of_floor_succ
      hp htpos hc0 hcpi i hband
  have htheta :
      cutRayTheta hp c i u ≤
        cutRayTheta hp c i v :=
    cutRayTheta_le_of_cutNormalized_le
      hp htpos i hcoordLt.le

  have hsign :
      cutRaySign hp c i u =
        cutRaySign hp c i v := by
    by_contra hne
    have hcost :=
      one_le_t_mul_cutRay_gap_of_sign_ne
        hp hcap htpos hlam hc0 hcpi i
        huv htheta hne
    have hgapEq :
        t * ((cutRayTheta hp c i v -
          cutRayTheta hp c i u) / Real.pi)
          =
        g := by
      dsimp [g]
      unfold cutNormalizedRayTheta
      ring
    rw [hgapEq] at hcost
    have hgLt : g < 1 :=
      Nat.floor_eq_zero.mp hgFloor
    linarith

  have hsmallScaled :
      t * ((cutRayTheta hp c i v -
        cutRayTheta hp c i u) / Real.pi) ≤ delta := by
    have hgapEq :
        t * ((cutRayTheta hp c i v -
          cutRayTheta hp c i u) / Real.pi)
          =
        g := by
      dsimp [g]
      unfold cutNormalizedRayTheta
      ring
    rw [hgapEq]
    exact hgLe

  exact ⟨u, v, huv,
    actual_angle_le_delta_lam_of_cut_same_sign_gap
      hp htpos hlam hc0 hcpi i htheta hsign hsmallScaled⟩

#print axioms cyclicRealGapsAt_sum_eq_width
#print axioms floor_zero_member_le_delta_of_sum
#print axioms CentreCutRayCycle.exists_cutRay_pair_mem_successive_of_zeroUnitStep
#print axioms actual_angle_le_delta_lam_of_cut_same_sign_gap
#print axioms cutSaturationBadAt_support_three_has_delta_small_angle

end JSP000404Research
