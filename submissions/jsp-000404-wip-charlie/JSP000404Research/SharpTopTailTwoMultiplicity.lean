import JSP000404Research.TopTwoTailMultiplicity
import JSP000404Research.TopForcesNextMultiplicity
import Mathlib.Tactic

/-!
# Sharpen the full top-two dyadic tail from three to two

The old TopTwoTailMultiplicity theorem allowed three centres in the
tail strictly above n-3 when a top exponent n-1 is present.
The unconditional planar top+two-next exclusion reduces this to two
in configurations with at least four actual centres.
No new global payment credits are claimed.
-/

namespace JSP000404Research

theorem topTwo_tailCount_le_two_of_card_ge_four
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hcard : 4 ≤ Fintype.card V)
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (s : V)
    (hS : centreExponent (C s) t = n - 1) :
    tailCount (fun i => centreExponent (C i) t) (n - 3) ≤ 2 := by
  classical
  let T : Finset V :=
    (Finset.univ : Finset V).filter
      (fun i => n - 3 < centreExponent (C i) t)
  let S2 : Finset V :=
    (Finset.univ : Finset V).filter
      (fun i => centreExponent (C i) t = n - 2)
  have hdelta1 : delta < 1 := by linarith
  have hexpLt :
      ∀ i : V, centreExponent (C i) t < n := by
    intro i
    exact centreExponent_lt_n
      (C i) n delta t (by omega : 1 ≤ n)
      hdelta0 hdelta1 ht
  have hsub : T ⊆ insert s S2 := by
    intro i hi
    have hiTail : n - 3 < centreExponent (C i) t := by
      simpa [T] using hi
    have hiLt := hexpLt i
    have hcases :
        centreExponent (C i) t = n - 1 ∨
          centreExponent (C i) t = n - 2 := by omega
    rcases hcases with htop | hsecond
    · have his : i = s :=
        topExponent_eq_fixed_top
          hp hcap (by omega : 3 ≤ Fintype.card V)
          hn hdelta0 hdeltaHalf ht hlam C s i hS htop
      simp [his]
    · simp [S2, hsecond]
  have hS2 : S2.card ≤ 1 := by
    exact actual_next_exponent_card_le_one_of_top
      hp hcap hcard hn hdelta0 hdeltaHalf ht hlam C s hS
  have hupper : T.card ≤ 2 := by
    have hm := Finset.card_le_card hsub
    have hi : (insert s S2).card ≤ S2.card + 1 :=
      Finset.card_insert_le s S2
    omega
  unfold tailCount
  simpa [T] using hupper

#print axioms topTwo_tailCount_le_two_of_card_ge_four

end JSP000404Research
