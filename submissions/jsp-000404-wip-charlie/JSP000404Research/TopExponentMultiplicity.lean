import JSP000404Research.ConcreteSharpCentre
import JSP000404Research.CentreExponentBounds
import Mathlib.Tactic

/-!
# Multiplicity of the top Sendov exponent in the lower branch

In the lower branch delta<1/2, a centre with exponent n-1 is a concrete
unit-deficit sharp centre.  Two such sharp centres are incompatible with any
third distinct centre under the global angle cap.

Hence for a configuration indexed by Fin m with m>=3, the top exponent n-1
occurs at most once.

This is exactly the top tail-count bound

  #{v | n-2 < k(v)} <= 1

for the exponent profile.
-/

namespace JSP000404Research

theorem topExponent_filter_card_le_one
    {m : ℕ}
    {p : Fin m → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hm : 3 ≤ m)
    (hn : 2 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : Fin m, CentreProjectiveCycle hp i) :
    ((Finset.univ : Finset (Fin m)).filter
      (fun i => centreExponent (C i) t = n - 1)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  by_contra hab
  obtain ⟨c, hca, hcb⟩ :=
    Fin.exists_ne_and_ne_of_two_lt a b (by omega)
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hdelta1 : delta < 1 := by linarith
  have hsharpA :=
    concrete_unit_deficit_is_sharp
      hp hcap hn hdelta0 hdelta1 ht hlam
      a (C a) ha
  have hsharpB :=
    concrete_unit_deficit_is_sharp
      hp hcap hn hdelta0 hdelta1 ht hlam
      b (C b) hb
  exact two_sharp_no_third_small_delta
    hp hcap hdeltaHalf hlampos
    hab hca.symm hcb.symm
    hsharpA hsharpB

/-- Tail form: because every centre exponent is below n in the normalized
lower branch, the threshold n-2 tail consists exactly of exponent n-1
centres. -/
theorem topExponent_tailCount_le_one
    {m : ℕ}
    {p : Fin m → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hm : 3 ≤ m)
    (hn : 2 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : Fin m, CentreProjectiveCycle hp i) :
    tailCount (fun i => centreExponent (C i) t) (n - 2) ≤ 1 := by
  classical
  have hdelta1 : delta < 1 := by linarith
  have hlt :
      ∀ i : Fin m, centreExponent (C i) t < n := by
    intro i
    exact centreExponent_lt_n
      (C i) n delta t (by omega) hdelta0 hdelta1 ht
  have hset :
      ((Finset.univ : Finset (Fin m)).filter
        (fun i => n - 2 < centreExponent (C i) t))
      =
      ((Finset.univ : Finset (Fin m)).filter
        (fun i => centreExponent (C i) t = n - 1)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hi := hlt i
    omega
  unfold tailCount
  rw [hset]
  exact topExponent_filter_card_le_one
    hp hcap hm hn hdelta0 hdeltaHalf ht hlam C

#print axioms topExponent_filter_card_le_one
#print axioms topExponent_tailCount_le_one

end JSP000404Research
