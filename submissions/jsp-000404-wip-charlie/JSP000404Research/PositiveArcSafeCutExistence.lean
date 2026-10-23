import JSP000404Research.PositiveArcBoundaryCutBridge
import Mathlib.Tactic

/-! From one globally full-arc-safe physical phase x in [0,t), construct
its genuine projective cut c=pi*x/t. The merged boundary edge graph admits
the explicit cutBoundaryWrapBit proper two-colouring. The statement does not
assert dyadic-capacity/global Boolean-hole payment. -/
namespace JSP000404Research

theorem exists_boundary_cut_coloring_of_full_positive_deltaArc_safe
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {lam t delta x : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hn : 1 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hx0 : 0 ≤ x) (hxt : x < t)
    (hsafe : ∀ v : GlobalPositiveGapSlot C t,
      ¬ CyclicDeltaArcAtAnyBase t delta
        (globalPositiveGapStart C t v) x) :
    ∃ c : ℝ, ∃ hc0 : 0 ≤ c, ∃ hcpi : c < Real.pi,
      let htop : t < (n + 1 : ℕ) := by rw [ht]; push_cast; linarith
      let P := cutProjectiveBandPartition hp hcap htpos hlam hc0 hcpi n htop
      let bit := cutBoundaryWrapBit (delta := delta) hp n htpos htop hc0 hcpi
      ∀ {u v : V}, u < v →
        ((P.edgeColor u v).val = 0 ∨ (P.edgeColor u v).val = n) →
        bit u ≠ bit v := by
  let c : ℝ := x * Real.pi / t
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg (mul_nonneg hx0 Real.pi_pos.le) htpos.le
  have hcpi : c < Real.pi := by
    dsimp [c]
    apply (div_lt_iff₀ htpos).2
    simpa only [mul_comm] using mul_lt_mul_of_pos_right hxt Real.pi_pos
  have hphase : t * c / Real.pi = x := by
    dsimp [c]
    have htne : t ≠ 0 := ne_of_gt htpos
    have hpine : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    field_simp
  exact ⟨c, hc0, hcpi,
    positive_deltaArc_safe_implies_boundary_cut_separation
      hp hcap C hn htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi hphase hsafe⟩

#print axioms exists_boundary_cut_coloring_of_full_positive_deltaArc_safe

end JSP000404Research
