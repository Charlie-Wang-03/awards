import JSP000404Research.ListZeroGapMass
import JSP000404Research.SmallSameSignGapAngle
import JSP000404Research.CanonicalSignGap
import JSP000404Research.DeficitTwo
import Mathlib.Tactic

/-!
# Arbitrary-cardinality zero quotient gaps are genuinely delta-small

This file removes the Fin 4 restriction from ZeroGapActualAngle.

At a concrete centre with

  exponent = n-2,
  positive quotient support = 2,

the quotient sum is exactly n.  Therefore the aligned list zero-gap remainder
budget applies to every displayed quotient-zero gap.

For an ordinary adjacent ray cut, quotient zero also forbids a canonical sign
change, so the true angle across the cut equals the projective gap.  The same
holds for the final wrap gap after the usual lifted-sign comparison.

Hence every displayed zero quotient gap in an arbitrary finite centre cycle
has genuine Euclidean angle at most delta*lambda.
-/

namespace JSP000404Research

open Real

theorem centre_quotientList_sum_eq_n_of_deficit_two_support_two
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2) :
    (quotientList t C.gaps).sum = n := by
  have hQ :
      (∑ r, centreQuotient C t r) ≤ n :=
    centreQuotient_function_sum_le_n
      C n delta t (by omega : 1 ≤ n)
      hdelta0 hdelta1 ht
  have hell :
      n - floorExcess (centreQuotient C t) = 2 := by
    change n - centreExponent C t = 2
    rw [hexp]
    omega
  have hstruct :=
    deficit_two_structure
      (centreQuotient C t) n hn hQ hell
  rcases hstruct with h1 | h2
  · omega
  · have hsumFn := h2.2
    rw [centreQuotient_sum_eq_list_sum C t] at hsumFn
    exact hsumFn

/-- Ordinary displayed zero gap in an arbitrary centre cycle. -/
theorem displayed_ordinary_zero_gap_actual_angle_le_delta_lam
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
    (first right : OtherVertex i)
    (before tail : List (OtherVertex i))
    (hrays :
      C.rays = first :: (before ++ right :: tail))
    (qpre qpost : List ℕ)
    (hq :
      quotientList t C.gaps = qpre ++ 0 :: qpost)
    (hlen : qpre.length = before.length)
    (hneq :
      (first :: before).getLast (by simp) ≠ right) :
    EuclideanGeometry.angle
        (p ((first :: before).getLast (by simp)).1)
        (p i) (p right.1)
      ≤ delta * lam := by
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have halign0 :=
    centreQuotient_aligned C htpos.le
  have halign :
      QuotientGapAligned t (qpre ++ 0 :: qpost) C.gaps := by
    rwa [← hq]
  obtain ⟨gpre, gpost, ge, hgaps, hpreLen, hpostLen,
      _hzeroAlign, _hpreAlign, _hpostAlign⟩ :=
    aligned_gap_decomposition halign
  have hgeomPre :
      gpre.length = before.length := by
    rw [hpreLen, hlen]
  have hgeEq :=
    centre_gap_eq_ordinary_cut
      C first right before tail hrays
      hgaps hgeomPre
  have hqsum :
      (qpre ++ 0 :: qpost).sum = n := by
    rw [← hq]
    exact centre_quotientList_sum_eq_n_of_deficit_two_support_two
      C hn hdelta0 hdelta1 ht hexp hsupport
  have hgap0 :
      ∀ g ∈ gpre ++ ge :: gpost, 0 ≤ g := by
    intro g hg
    apply C.gaps_nonneg g
    rw [hgaps]
    exact hg
  have hgapsum :
      (gpre ++ ge :: gpost).sum = 1 := by
    rw [← hgaps]
    exact C.gaps_sum
  have hsmallGe :
      t * ge ≤ delta :=
    displayed_zero_gap_scaled_le_delta
      qpre qpost gpre gpost ge
      ht hpreLen hpostLen hgap0 hgapsum hqsum
      (by rwa [hgaps] at halign)
      htpos.le
  let left : OtherVertex i :=
    (first :: before).getLast (by simp)
  have hpair :
      ((first :: before) ++ (right :: tail)).Pairwise
        (fun a b =>
          rayThetaAt hp i a ≤ rayThetaAt hp i b) := by
    have h := C.theta_sorted
    rw [hrays] at h
    simpa [List.cons_append, List.append_assoc] using h
  have hparts :
      (first :: before).Pairwise
          (fun a b =>
            rayThetaAt hp i a ≤ rayThetaAt hp i b) ∧
      (right :: tail).Pairwise
          (fun a b =>
            rayThetaAt hp i a ≤ rayThetaAt hp i b) ∧
      (∀ a ∈ first :: before, ∀ b ∈ right :: tail,
        rayThetaAt hp i a ≤ rayThetaAt hp i b) := by
    simpa only [List.pairwise_append] using hpair
  have horder :
      rayThetaAt hp i left ≤ rayThetaAt hp i right := by
    exact hparts.2.2 left
      (by
        dsimp [left]
        exact List.getLast_mem _)
      right (by simp)
  have hfloor0 :
      Nat.floor
        (t * ((rayThetaAt hp i right -
          rayThetaAt hp i left) / Real.pi)) = 0 := by
    have hstd :
        quotientList t C.gaps =
          (gpre.map (fun g => Nat.floor (t * g))) ++
            Nat.floor (t * ge) ::
              (gpost.map (fun g => Nat.floor (t * g))) := by
      rw [hgaps]
      simp [quotientList, List.map_append]
    have heq :=
      distinguished_entry_eq_of_decompositions
        hq hstd (by simp [hpreLen])
    have hgeFloor : Nat.floor (t * ge) = 0 := heq.symm
    rw [hgeEq] at hgeFloor
    simpa [left] using hgeFloor
  have hsign :
      raySignAt hp i left = raySignAt hp i right := by
    by_contra hne
    have hnonzero :=
      floor_t_mul_gap_ne_zero_of_canonical_sign_ne
        hp hcap htpos hlam i hneq horder hne
    exact hnonzero hfloor0
  have hsmall :
      t * ((rayThetaAt hp i right -
        rayThetaAt hp i left) / Real.pi) ≤ delta := by
    rw [hgeEq] at hsmallGe
    simpa [left] using hsmallGe
  exact actual_angle_le_delta_lam_of_ordinary_same_sign_gap
    hp htpos hlam i horder hsign hsmall

/-- Final wrap zero gap in an arbitrary centre cycle. -/
theorem displayed_wrap_zero_gap_actual_angle_le_delta_lam
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
    (hrays : C.rays = first :: rest)
    (qpre : List ℕ)
    (hq :
      quotientList t C.gaps = qpre ++ [0])
    (hlen : qpre.length = rest.length)
    (hrest : rest ≠ [])
    (hneq :
      first ≠ (first :: rest).getLast (by simp)) :
    EuclideanGeometry.angle
        (p ((first :: rest).getLast (by simp)).1)
        (p i) (p first.1)
      ≤ delta * lam := by
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have halign :
      QuotientGapAligned t (qpre ++ 0 :: []) C.gaps := by
    have h0 := centreQuotient_aligned C htpos.le
    simpa using (show
      QuotientGapAligned t (qpre ++ [0]) C.gaps by
        rwa [← hq])
  obtain ⟨gpre, gpost, ge, hgaps, hpreLen, hpostLen,
      _hzeroAlign, _hpreAlign, _hpostAlign⟩ :=
    aligned_gap_decomposition halign
  have hgpost : gpost = [] :=
    List.length_eq_zero.mp (by simpa using hpostLen)
  subst gpost
  have hgeEq :=
    centre_gap_eq_wrap_cut
      C first rest hrays
      hgaps
      (by rw [hpreLen, hlen])
      rfl
  have hqsum :
      (qpre ++ [0]).sum = n := by
    rw [← hq]
    exact centre_quotientList_sum_eq_n_of_deficit_two_support_two
      C hn hdelta0 hdelta1 ht hexp hsupport
  have hgap0 :
      ∀ g ∈ gpre ++ ge :: ([] : List ℝ), 0 ≤ g := by
    intro g hg
    apply C.gaps_nonneg g
    rw [hgaps]
    simpa using hg
  have hgapsum :
      (gpre ++ ge :: ([] : List ℝ)).sum = 1 := by
    rw [← hgaps]
    exact C.gaps_sum
  have hsmallGe :
      t * ge ≤ delta :=
    displayed_zero_gap_scaled_le_delta
      qpre [] gpre [] ge
      ht hpreLen rfl hgap0 hgapsum
      (by simpa using hqsum)
      (by simpa using halign)
      htpos.le
  let last : OtherVertex i :=
    (first :: rest).getLast (by simp)
  have horder :
      rayThetaAt hp i first ≤ rayThetaAt hp i last := by
    dsimp [last]
    exact C.theta_sorted.rel_getLast
      (by rw [hrays]; simp)
  have hfloor0 :
      Nat.floor
        (t * ((rayThetaAt hp i first + Real.pi -
          rayThetaAt hp i last) / Real.pi)) = 0 := by
    have hstd :
        quotientList t C.gaps =
          (gpre.map (fun g => Nat.floor (t * g))) ++
            [Nat.floor (t * ge)] := by
      rw [hgaps]
      simp [quotientList, List.map_append]
    have heq :=
      distinguished_entry_eq_of_decompositions
        hq hstd (by simp [hpreLen])
    have hgeFloor : Nat.floor (t * ge) = 0 := heq.symm
    rw [hgeEq] at hgeFloor
    simpa [last] using hgeFloor
  have hsign :
      raySignAt hp i last = !raySignAt hp i first := by
    by_contra hne
    have hnonzero :=
      floor_t_mul_wrap_gap_ne_zero_of_canonical_sign_ne
        hp hcap htpos hlam i hneq horder hne
    exact hnonzero hfloor0
  have hsmall :
      t * ((rayThetaAt hp i first + Real.pi -
        rayThetaAt hp i last) / Real.pi) ≤ delta := by
    rw [hgeEq] at hsmallGe
    simpa [last] using hsmallGe
  exact actual_angle_le_delta_lam_of_wrap_same_sign_gap
    hp htpos hlam i horder hsign hsmall

#print axioms centre_quotientList_sum_eq_n_of_deficit_two_support_two
#print axioms displayed_ordinary_zero_gap_actual_angle_le_delta_lam
#print axioms displayed_wrap_zero_gap_actual_angle_le_delta_lam

end JSP000404Research
