import JSP000404Research.NarrowObserverDirections
import JSP000404Research.UpperHalfPlaneDirections

/-!
# A geometric cardinality bound between two narrow observers

For two points on a horizontal base, consider points strictly above that base
whose two base angles are smaller than lambda. Under the genuine planar cap
pi-lambda, the selected points have cardinality at most `2^k` whenever
pi/lambda-3<k. All geometric and observer assumptions appear in the statement.
-/

namespace JSP000404Research

/-- Two narrow viewpoints on one side of a horizontal base leave at most
`2^k` actual points when the normalized width is less than `k+3`. -/
theorem two_narrow_observer_card_bound
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p) {lam t : ℝ}
    (hcap : AngleCap p lam) (hlam : 0 < lam) (ht : 0 < t)
    (hscale : Real.pi = t * lam)
    (S : Finset V) {a b : V}
    (hlevel : p a 1 = p b 1) (hleft : p a 0 < p b 0)
    (habove : ∀ i ∈ S, p a 1 < p i 1)
    (hview : ∀ i ∈ S,
      EuclideanGeometry.angle (p b) (p a) (p i) < lam ∧
      EuclideanGeometry.angle (p a) (p b) (p i) < lam)
    (k : ℕ) (hwidth : t - 3 < k) : S.card ≤ 2 ^ k := by
  classical
  let := heightLinearOrder hp
  let F := upperHalfPlaneForwardLift hp (heightLinearOrder_forward hp)
  let D := F.toDirectionData hcap hlam ht hscale
  have hab : a < b := by
    change toLex (p a 1, p a 0) < toLex (p b 1, p b 0)
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hlevel, hleft⟩)
  have hbefore (i : V) (hi : i ∈ S) : b < i := by
    change toLex (p b 1, p b 0) < toLex (p i 1, p i 0)
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (by simpa [← hlevel] using habove i hi))
  have hzero : F.theta a b = 0 := by
    change (planeToComplex (p b - p a)).arg = 0
    have hz : planeToComplex (p b - p a) = ((p b 0 - p a 0 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [planeToComplex_apply, hlevel]
    rw [hz]
    exact Complex.arg_ofReal_of_nonneg (sub_pos.mpr hleft).le
  apply D.two_observer_card_le S hab hbefore
  · intro i hi
    have hangle := F.angle_first_eq_abs hab (hbefore i hi)
    have htheta := F.theta_lower (hab.trans (hbefore i hi))
    rw [hzero, zero_sub, abs_neg, abs_of_nonneg htheta] at hangle
    change (F.theta a i - 0) / lam < 1
    rw [sub_zero, div_lt_iff₀ hlam, one_mul]
    simpa [hangle] using (hview i hi).1
  · intro i hi
    have hangle := F.angle_middle_eq_pi_sub_abs hab (hbefore i hi)
    have htheta := F.theta_lower (hbefore i hi)
    rw [hzero, zero_sub, abs_neg, abs_of_nonneg htheta] at hangle
    have hsmall := (hview i hi).2
    change t - 1 < (F.theta b i - 0) / lam
    rw [sub_zero, lt_div_iff₀ hlam]
    rw [hangle] at hsmall
    nlinarith
  · exact hwidth

#print axioms two_narrow_observer_card_bound

end JSP000404Research
