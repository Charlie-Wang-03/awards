import JSP000404Research.PlanarLowerTwoFourActualQuartet
import JSP000404Research.CentreExponentBounds
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-!
# n=2 original four-centre global dyadic capacity, without extra hypotheses

The arbitrary-vertex-type quartet sharp-exclusion theorem is applied using a
Fin4 equivalence ONLY to choose the four distinct labels. All centre cycles
remain the ACTUAL original `CentreProjectiveCycle hp i` values, not
reconstructed via a relabelled configuration.

No top-exponent hypothesis is required; it follows from actual AngleCap.
-/

namespace JSP000404Research

theorem lower_two_four_original_centre_dyadic_capacity
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hcard : Fintype.card V = 4)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (2 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    (∑ i : V, (2 : ℕ) ^ centreExponent (C i) t) ≤ 2 ^ 2 := by
  classical
  let e : Fin 4 ≃ V :=
    Fintype.equivOfCardEq (by simpa using hcard.symm)
  have hDiff {a b : Fin 4} (hab : a ≠ b) : e a ≠ e b :=
    fun h => hab (e.injective h)
  have hquartet
      (a b c d : Fin 4)
      (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
      (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
      centreExponent (C (e a)) t ≠ 1 := by
    intro hexp
    exact lower_two_no_sharp_with_three_other_centres
      (s := e a) (u := e b) (v := e c) (w := e d)
      hp hcap hdelta0 hdeltaHalf ht hlam C
      (hDiff hab) (hDiff hac) (hDiff had)
      (hDiff hbc) (hDiff hbd) (hDiff hcd)
      hexp
  have hno : ∀ i : V, centreExponent (C i) t ≠ 1 := by
    intro i
    obtain ⟨j, rfl⟩ := e.surjective i
    fin_cases j
    · exact hquartet 0 1 2 3 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact hquartet 1 0 2 3 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact hquartet 2 0 1 3 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact hquartet 3 0 1 2 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
  have hdelta1 : delta < 1 := by linarith
  have hzero : ∀ i : V, centreExponent (C i) t = 0 := by
    intro i
    have hlt : centreExponent (C i) t < 2 :=
      centreExponent_lt_n (C i) 2 delta t
        (by omega) hdelta0 hdelta1
        (by simpa only [Nat.cast_ofNat] using ht)
    have hnon := hno i
    omega
  calc
    (∑ i : V, (2 : ℕ) ^ centreExponent (C i) t)
        = ∑ _ : V, (1 : ℕ) := by
          apply Finset.sum_congr rfl
          intro i _
          simp [hzero i]
    _ = Fintype.card V := by simp
    _ = 4 := hcard
    _ ≤ (2 : ℕ) ^ 2 := by norm_num

#print axioms lower_two_four_original_centre_dyadic_capacity

end JSP000404Research
