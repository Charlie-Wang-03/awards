import JSP000404Research.CyclicActualAngles
import JSP000404Research.DeficitThree
import Mathlib.Tactic

/-!
# Full quotient mass gives a delta-small zero-angle budget

The support-two / deficit-two theorem centre_zeroAngleMass_le_delta_lam used
only one arithmetic fact from that regime: the total quotient sum equals n.

This file isolates that fact as the real hypothesis.  Whenever

  quotientList.sum = n,
  gaps.sum = 1,
  t = n + delta,

all zero-quotient actual angles in the concrete centre cycle have total mass
at most delta*lambda.

This immediately applies to the support-three / deficit-three branch, because
the exact zero-carry identity forces quotient sum n there as well.
-/

namespace JSP000404Research

open Real

theorem centre_zeroAngleMass_le_delta_lam_of_quotient_sum
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (ht : t = (n : ℝ) + delta)
    (htpos : 0 < t)
    (htone : 1 ≤ t)
    (hlam : lam = Real.pi / t)
    (i : V)
    (C : CentreProjectiveCycle hp i)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (hrays : C.rays = first :: rest)
    (hqsum : (quotientList t C.gaps).sum = n) :
    listZeroAngleMass
        (quotientList t C.gaps)
        (cyclicRayAngles (p := p) i first rest)
      ≤ delta * lam := by
  have halignA :=
    centre_zeroQuotientAngleAligned
      hp hcap htpos htone hlam i C first rest hrays
  have hzeroEq :=
    listZeroAngleMass_eq_pi_mul_listZeroGapMass
      halignA
  have halignQ :=
    centreQuotient_aligned C htpos.le
  have hmass :
      t * listZeroGapMass
          (quotientList t C.gaps) C.gaps ≤ delta :=
    listZeroGapMass_scaled_le_delta
      (quotientList t C.gaps) C.gaps
      ht C.gaps_sum hqsum halignQ
  have hpiMass :
      Real.pi * listZeroGapMass
          (quotientList t C.gaps) C.gaps
        ≤ delta * lam :=
    pi_mul_width_le_delta_lam_of_scaled_width
      htpos hlam hmass
  rw [hzeroEq]
  exact hpiMass

/-- Concrete deficit-three/support-three specialization. -/
theorem centre_zeroAngleMass_le_delta_lam_of_deficit_three_support_three
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (i : V)
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient C t) = 3)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (hrays : C.rays = first :: rest) :
    listZeroAngleMass
        (quotientList t C.gaps)
        (cyclicRayAngles (p := p) i first rest)
      ≤ delta * lam := by
  have hdelta1 : delta < 1 := by linarith
  have hQ :=
    centreQuotient_function_sum_le_n
      C n delta t (by omega : 1 ≤ n)
      hdelta0 hdelta1 ht
  have hell :
      n - floorExcess (centreQuotient C t) = 3 := by
    change n - centreExponent C t = 3
    rw [hexp]
    omega
  have hstruct :=
    deficit_three_structure
      (centreQuotient C t) n hn hQ hell
  have hsumFn :
      (∑ r, centreQuotient C t r) = n := by
    rcases hstruct with h1 | h2 | h3
    · rw [hsupport] at h1
      omega
    · rw [hsupport] at h2
      omega
    · exact h3.2
  have hsumList :
      (quotientList t C.gaps).sum = n := by
    rw [← centreQuotient_sum_eq_list_sum C t]
    exact hsumFn
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have htone : 1 ≤ t := by
    rw [ht]
    have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  exact centre_zeroAngleMass_le_delta_lam_of_quotient_sum
    hp hcap ht htpos htone hlam
    i C first rest hrays hsumList


/-- If the total quotient mass is n-1, zero quotient positions carry at most
(1+delta)*lambda of genuine actual angle. -/
theorem centre_zeroAngleMass_le_one_add_delta_lam_of_quotient_sum_n_sub_one
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (ht : t = (n : ℝ) + delta)
    (htpos : 0 < t)
    (htone : 1 ≤ t)
    (hlam : lam = Real.pi / t)
    (i : V)
    (C : CentreProjectiveCycle hp i)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (hrays : C.rays = first :: rest)
    (hqsum : (quotientList t C.gaps).sum = n - 1) :
    listZeroAngleMass
        (quotientList t C.gaps)
        (cyclicRayAngles (p := p) i first rest)
      ≤ (1 + delta) * lam := by
  have halignA :=
    centre_zeroQuotientAngleAligned
      hp hcap htpos htone hlam i C first rest hrays
  have hzeroEq :=
    listZeroAngleMass_eq_pi_mul_listZeroGapMass halignA
  have halignQ :=
    centreQuotient_aligned C htpos.le
  have hlen : (quotientList t C.gaps).length = C.gaps.length :=
    List.Forall₂.length_eq halignQ
  have hmass0 :=
    listZeroGapMass_scaled_le_remainder halignQ
  rw [listRemainderMass_eq t
        (quotientList t C.gaps) C.gaps hlen,
      C.gaps_sum, hqsum, ht] at hmass0
  have hncast :
      (((n - 1 : ℕ) : ℝ)) = (n : ℝ) - 1 := by
    exact_mod_cast (Nat.sub_add_cancel hn)
  rw [hncast] at hmass0
  norm_num at hmass0
  have hpiMass :
      Real.pi * listZeroGapMass
          (quotientList t C.gaps) C.gaps
        ≤ (1 + delta) * lam :=
    pi_mul_width_le_delta_lam_of_scaled_width
      htpos hlam (by
        simpa [add_comm, add_left_comm, add_assoc] using hmass0)
  rw [hzeroEq]
  exact hpiMass

/-- Exact deficit-three/support-two specialization. -/
theorem centre_zeroAngleMass_le_one_add_delta_lam_of_deficit_three_support_two
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (i : V)
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (hrays : C.rays = first :: rest) :
    listZeroAngleMass
        (quotientList t C.gaps)
        (cyclicRayAngles (p := p) i first rest)
      ≤ (1 + delta) * lam := by
  have hdelta1 : delta < 1 := by linarith
  have hsumFn :=
    deficit_three_support_two_sum
      C hn hdelta0 hdelta1 ht hexp hsupport
  have hsumList :
      (quotientList t C.gaps).sum = n - 1 := by
    rw [← centreQuotient_sum_eq_list_sum C t]
    exact hsumFn
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have htone : 1 ≤ t :=
    sendov_scale_one_le (by omega : 1 ≤ n) hdelta0 ht
  exact
    centre_zeroAngleMass_le_one_add_delta_lam_of_quotient_sum_n_sub_one
      hp hcap (by omega : 1 ≤ n) ht htpos htone hlam
      i C first rest hrays hsumList

#print axioms centre_zeroAngleMass_le_delta_lam_of_quotient_sum
#print axioms centre_zeroAngleMass_le_delta_lam_of_deficit_three_support_three

end JSP000404Research
