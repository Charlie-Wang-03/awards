import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic

/-!
Closed sharp-centre consequences used in the JSP-000404 research proof.

This file deliberately isolates proved consequences from the still-open bridge
from Sendov's local gap data to `SharpAt`, and from local data to the global
weighted Kraft / zero-carry bound.
-/

namespace JSP000404Research

open Real

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A uniform angle cap at scale `lam`. -/
def AngleCap {V : Type*} (p : V → Plane) (lam : ℝ) : Prop :=
  ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
    EuclideanGeometry.angle (p a) (p b) (p c) ≤ Real.pi - lam

/-- The geometric consequence of a Sendov sharp centre:
all angles at the centre are at most `delta * lam`. -/
def SharpAt {V : Type*} (p : V → Plane) (delta lam : ℝ) (i : V) : Prop :=
  ∀ j k, j ≠ i → k ≠ i → j ≠ k →
    EuclideanGeometry.angle (p j) (p i) (p k) ≤ delta * lam

/-- In the small-delta branch, twice the sharp-centre angular width is
strictly smaller than one cap unit. -/
theorem two_delta_lam_lt_lam {delta lam : ℝ}
    (hdelta : delta < 1 / 2) (hlam : 0 < lam) :
    2 * delta * lam < lam := by
  nlinarith

/-- For Sendov's normalization `lam = pi / (n + delta)`, three sharp
angular widths are strictly smaller than a full angle whenever `n ≥ 2`
and `delta < 1`. -/
theorem three_delta_lam_lt_pi {n : ℕ} {delta lam : ℝ}
    (hn : 2 ≤ n) (hdelta0 : 0 ≤ delta) (hdelta1 : delta < 1)
    (hlam : lam = Real.pi / ((n : ℝ) + delta)) :
    3 * delta * lam < Real.pi := by
  have hnR : (2 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hq : 0 < (n : ℝ) + delta := by
    linarith
  have hbase : 3 * delta < (n : ℝ) + delta := by
    nlinarith
  rw [hlam]
  rw [show 3 * delta * (Real.pi / ((n : ℝ) + delta)) =
      (3 * delta * Real.pi) / ((n : ℝ) + delta) by ring]
  rw [div_lt_iff₀ hq]
  have hmul := mul_lt_mul_of_pos_right hbase Real.pi_pos
  simpa [mul_assoc, mul_comm, mul_left_comm] using hmul

/-- Three pairwise-distinct sharp centres are impossible as soon as
`3 * delta * lam < pi`. -/
theorem no_three_sharp {V : Type*} {p : V → Plane} {delta lam : ℝ}
    (hp : Function.Injective p)
    {i j k : V} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : SharpAt p delta lam i)
    (hj : SharpAt p delta lam j)
    (hk : SharpAt p delta lam k)
    (hwidth : 3 * delta * lam < Real.pi) : False := by
  have hai :
      EuclideanGeometry.angle (p j) (p i) (p k) ≤ delta * lam :=
    hi j k (Ne.symm hij) (Ne.symm hik) hjk
  have haj :
      EuclideanGeometry.angle (p k) (p j) (p i) ≤ delta * lam :=
    hj k i (Ne.symm hjk) hij (Ne.symm hik)
  have hak :
      EuclideanGeometry.angle (p i) (p k) (p j) ≤ delta * lam :=
    hk i j hik hjk hij
  have hsum :
      EuclideanGeometry.angle (p j) (p i) (p k) +
        EuclideanGeometry.angle (p i) (p k) (p j) +
        EuclideanGeometry.angle (p k) (p j) (p i) = Real.pi := by
    simpa [add_assoc, add_left_comm, add_comm] using
      (EuclideanGeometry.angle_add_angle_add_angle_eq_pi
        (p₁ := p j) (p₂ := p i) (p k) (hp.ne hij))
  nlinarith

/-- Sendov-normalized corollary: under `n ≥ 2`, `0 ≤ delta < 1`,
there cannot be three sharp centres. -/
theorem no_three_sharp_sendov {V : Type*} {p : V → Plane}
    {n : ℕ} {delta lam : ℝ}
    (hp : Function.Injective p)
    (hn : 2 ≤ n) (hdelta0 : 0 ≤ delta) (hdelta1 : delta < 1)
    (hlam : lam = Real.pi / ((n : ℝ) + delta))
    {i j k : V} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : SharpAt p delta lam i)
    (hj : SharpAt p delta lam j)
    (hk : SharpAt p delta lam k) : False := by
  exact no_three_sharp hp hij hik hjk hi hj hk
    (three_delta_lam_lt_pi hn hdelta0 hdelta1 hlam)

/-- In the first Sendov branch, two sharp centres and a third distinct
centre violate the global angle cap. -/
theorem two_sharp_no_third_small_delta
    {V : Type*} {p : V → Plane} {delta lam : ℝ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hdelta : delta < 1 / 2) (hlam : 0 < lam)
    {i j k : V} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : SharpAt p delta lam i)
    (hj : SharpAt p delta lam j) : False := by
  have hai :
      EuclideanGeometry.angle (p j) (p i) (p k) ≤ delta * lam :=
    hi j k (Ne.symm hij) (Ne.symm hik) hjk
  have haj :
      EuclideanGeometry.angle (p k) (p j) (p i) ≤ delta * lam :=
    hj k i (Ne.symm hjk) hij (Ne.symm hik)
  have hak :
      EuclideanGeometry.angle (p i) (p k) (p j) ≤ Real.pi - lam :=
    hcap i k j hik hij (Ne.symm hjk)
  have hsum :
      EuclideanGeometry.angle (p j) (p i) (p k) +
        EuclideanGeometry.angle (p i) (p k) (p j) +
        EuclideanGeometry.angle (p k) (p j) (p i) = Real.pi := by
    simpa [add_assoc, add_left_comm, add_comm] using
      (EuclideanGeometry.angle_add_angle_add_angle_eq_pi
        (p₁ := p j) (p₂ := p i) (p k) (hp.ne hij))
  have htwo : 2 * delta * lam < lam :=
    two_delta_lam_lt_lam hdelta hlam
  nlinarith

#print axioms two_delta_lam_lt_lam
#print axioms three_delta_lam_lt_pi
#print axioms no_three_sharp
#print axioms no_three_sharp_sendov
#print axioms two_sharp_no_third_small_delta

end JSP000404Research
