import JSP000404Research.TopNextSupportOneFourCentrePacking
import Mathlib.Tactic

/-!
# Seven-centre top+next support-one case: exactly one other low-support slot

The EXISTING kernel-checked original-plane theorem
top_next_support_one_low_support_card_le_one already says that
there can be AT MOST ONE other low-support original vertex besides
a top and a support-one next exponent centre.

This file lifts that source theorem directly to an all-cardinality
high-support lower bound, avoiding a redundant global packing proof.
It is a necessary AngleCap consequence, not an exterior Boolean-hole
payment or an elimination of the n=3 overweight motif.
-/

namespace JSP000404Research

/-- In original n=3 AngleCap, if a top exponent-two centre coexists
with a distinct exponent-one support-one centre, at most three
ORIGINAL centres have quotient support <=2. -/
theorem planar_three_top_next_support_one_forces_high_support_plus_three
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (s a : V)
    (hs : centreExponent (C s) t = 2)
    (ha : centreExponent (C a) t = 1)
    (haSupport : positiveSupport (centreQuotient (C a) t) = 1) :
    Fintype.card V ≤
      ((Finset.univ : Finset V).filter
        (fun i => 3 ≤ positiveSupport (centreQuotient (C i) t))).card + 3 := by
  classical
  have hsa : s ≠ a := by
    intro h
    rw [h] at hs
    omega
  let L : Finset V :=
    Finset.univ.filter (fun i =>
      positiveSupport (centreQuotient (C i) t) ≤ 2)
  let H : Finset V :=
    Finset.univ.filter (fun i =>
      3 ≤ positiveSupport (centreQuotient (C i) t))
  let E : Finset V :=
    Finset.univ.filter (fun i =>
      i ≠ s ∧ i ≠ a ∧
      positiveSupport (centreQuotient (C i) t) ≤ 2)
  have hE : E.card ≤ 1 := by
    simpa only [E] using
      (top_next_support_one_low_support_card_le_one
        hp hcap (by decide : 3 ≤ (3 : ℕ))
        hdelta0 hdeltaHalf ht hlam C hsa hs ha haSupport)
  have hsubset : L ⊆ insert s (insert a E) := by
    intro i hi
    have hilow :
        positiveSupport (centreQuotient (C i) t) ≤ 2 :=
      (Finset.mem_filter.mp hi).2
    by_cases his : i = s
    · simp [his]
    by_cases hia : i = a
    · simp [hia]
    have hiE : i ∈ E :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ⟨his, hia, hilow⟩⟩
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hiE)
  have hcardBound :
      (insert s (insert a E)).card ≤ E.card + 2 := by
    have h1 := Finset.card_insert_le a E
    have h2 := Finset.card_insert_le s (insert a E)
    omega
  have hlow : L.card ≤ 3 :=
    (Finset.card_le_card hsubset).trans (by omega)
  have hcomp : H = (Finset.univ : Finset V) \ L := by
    ext i
    simp only [H, L, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_sdiff]
    omega
  have hpart : H.card + L.card = Fintype.card V := by
    have hc := Finset.card_sdiff_add_card_inter
      (Finset.univ : Finset V) L
    rw [← hcomp] at hc
    simpa using hc
  change Fintype.card V ≤ H.card + 3
  omega

/-- In any such genuine configuration with seven or more ORIGINAL
vertices, at least FOUR are support-three saturated centres.
Their geometric gaps are not globally disjoint Boolean-hole credits. -/
theorem planar_three_seven_top_next_support_one_forces_four_high
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hseven : 7 ≤ Fintype.card V)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (s a : V)
    (hs : centreExponent (C s) t = 2)
    (ha : centreExponent (C a) t = 1)
    (haSupport : positiveSupport (centreQuotient (C a) t) = 1) :
    4 ≤ ((Finset.univ : Finset V).filter
      (fun i => 3 ≤ positiveSupport (centreQuotient (C i) t))).card := by
  have h := planar_three_top_next_support_one_forces_high_support_plus_three
    hp hcap hdelta0 hdeltaHalf ht hlam C s a hs ha haSupport
  omega

#print axioms planar_three_top_next_support_one_forces_high_support_plus_three
#print axioms planar_three_seven_top_next_support_one_forces_four_high

end JSP000404Research
