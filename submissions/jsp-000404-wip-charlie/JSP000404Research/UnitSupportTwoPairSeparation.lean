import JSP000404Research.FinFourUnitSupportTwoExactSpectrum
import JSP000404Research.HiddenLargeAngleTriangle
import Mathlib.Tactic

/-!
# Small and hidden-large pairs are distinct at a unit-transition support-two centre

In the lower branch a delta*lambda-small pair cannot simultaneously be the
hidden (n-1)*lambda pair.  Numerically n-1 > delta for n>=3 and delta<1/2.

This elementary separation lets later Fin-4 case analysis distinguish the
unique zero-gap pair from the hidden n-1 pair.
-/

namespace JSP000404Research

theorem delta_lt_n_sub_one
    {n : ℕ} {delta : ℝ}
    (hn3 : 3 ≤ n)
    (hdeltaHalf : delta < (1 : ℝ) / 2) :
    delta < (n - 1 : ℕ) := by
  have hn : (2 : ℝ) ≤ (n - 1 : ℕ) := by
    exact_mod_cast (show 2 ≤ n - 1 by omega)
  linarith

theorem small_angle_ne_hidden_large_angle
    {V : Type*} {p : V → Plane}
    {lam delta : ℝ} {n : ℕ}
    (hn3 : 3 ≤ n)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    {i x y : V}
    (hsmall :
      EuclideanGeometry.angle (p x) (p i) (p y)
        ≤ delta * lam)
    (hlarge :
      ((n - 1 : ℕ) : ℝ) * lam
        ≤ EuclideanGeometry.angle (p x) (p i) (p y)) :
    False := by
  have hcoeff := delta_lt_n_sub_one hn3 hdeltaHalf
  have hmul :
      delta * lam < ((n - 1 : ℕ) : ℝ) * lam :=
    (mul_lt_mul_right hlampos).2 (by
      exact_mod_cast hcoeff)
  linarith

/-- If one unordered pair among three neighbours is small and a second one is
hidden-large, the two pairs cannot be the same unordered pair. -/
theorem small_pair_unordered_ne_hidden_pair
    {V : Type*} {p : V → Plane}
    {lam delta : ℝ} {n : ℕ}
    (hn3 : 3 ≤ n)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    {i a b x y : V}
    (hsmall :
      EuclideanGeometry.angle (p a) (p i) (p b)
        ≤ delta * lam)
    (hlarge :
      ((n - 1 : ℕ) : ℝ) * lam
        ≤ EuclideanGeometry.angle (p x) (p i) (p y))
    (heq :
      (x = a ∧ y = b) ∨ (x = b ∧ y = a)) :
    False := by
  rcases heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact small_angle_ne_hidden_large_angle
      hn3 hdeltaHalf hlampos hsmall hlarge
  · have hlarge' :
        ((n - 1 : ℕ) : ℝ) * lam
          ≤ EuclideanGeometry.angle (p a) (p i) (p b) := by
      simpa [EuclideanGeometry.angle_comm] using hlarge
    exact small_angle_ne_hidden_large_angle
      hn3 hdeltaHalf hlampos hsmall hlarge'

#print axioms small_angle_ne_hidden_large_angle
#print axioms small_pair_unordered_ne_hidden_pair

end JSP000404Research
