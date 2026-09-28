import Mathlib.Tactic

/-!
# Source-assembly repairs for JSP-000404

This module formalizes two source-level logical bridges isolated by the
Acta 1995 proof-dependency audit.

1. Exact-cardinality perfectization is not needed for a capacity transfer:
   a reduction which preserves the angle property and does not decrease
   cardinality is enough.

2. The final passage from the threshold function N(a) to the minimax value
   alpha(N) should use a generalized-inverse characterization
      N <= Ncap(a) <-> alpha(N) <= a,
   rather than the blanket identity alpha(Ncap(a)) = a.

These are abstract order/logic lemmas.  They do not claim the still-open
general-s geometric capacity theorem.
-/

namespace JSP000404Research

/-- A nonshrinking reduction transfers any cardinality capacity bound. -/
theorem capacity_transfer_of_nonshrinking_reduction
    {Config Reduced : Type*}
    (size : Config → ℕ)
    (reducedSize : Reduced → ℕ)
    (admissible : Config → Prop)
    (reducedAdmissible : Reduced → Prop)
    (reduce : Config → Reduced)
    (bound : ℕ)
    (hsize : ∀ X, size X ≤ reducedSize (reduce X))
    (hadmissible :
      ∀ X, admissible X → reducedAdmissible (reduce X))
    (hcapacity :
      ∀ Y, reducedAdmissible Y → reducedSize Y ≤ bound) :
    ∀ X, admissible X → size X ≤ bound := by
  intro X hX
  exact (hsize X).trans
    (hcapacity (reduce X) (hadmissible X hX))

/-- Sendov-style specialization: if perfectization preserves the relevant
angle value and never decreases cardinality, a capacity theorem for perfect
objects already bounds arbitrary objects.  No exact-cardinality
perfectization statement is required. -/
theorem capacity_transfer_of_nonshrinking_same_value
    {Config : Type*}
    (size : Config → ℕ)
    (value : Config → ℝ)
    (perfect : Config → Prop)
    (perfectize : Config → Config)
    (a : ℝ)
    (bound : ℕ)
    (hsize : ∀ X, size X ≤ size (perfectize X))
    (hvalue : ∀ X, value (perfectize X) = value X)
    (hperfect : ∀ X, perfect (perfectize X))
    (hcapacity :
      ∀ Y, perfect Y → value Y ≤ a → size Y ≤ bound) :
    ∀ X, value X ≤ a → size X ≤ bound := by
  intro X hX
  have hred :
      size (perfectize X) ≤ bound := by
    apply hcapacity (perfectize X) (hperfect X)
    rw [hvalue X]
    exact hX
  exact (hsize X).trans hred

/-- Correct generalized-inverse interface between a minimax value alpha(N)
and a threshold-cardinality function Ncap(a). -/
def ThresholdCharacterization
    (alpha : ℕ → ℝ) (Ncap : ℝ → ℕ) : Prop :=
  ∀ N a, N ≤ Ncap a ↔ alpha N ≤ a

theorem alpha_monotone_of_thresholdCharacterization
    {alpha : ℕ → ℝ} {Ncap : ℝ → ℕ}
    (h : ThresholdCharacterization alpha Ncap) :
    Monotone alpha := by
  intro m n hmn
  have hn : n ≤ Ncap (alpha n) :=
    (h n (alpha n)).2 le_rfl
  have hm : m ≤ Ncap (alpha n) :=
    hmn.trans hn
  exact (h m (alpha n)).1 hm

theorem Ncap_monotone_of_thresholdCharacterization
    {alpha : ℕ → ℝ} {Ncap : ℝ → ℕ}
    (h : ThresholdCharacterization alpha Ncap) :
    Monotone Ncap := by
  intro a b hab
  have ha : alpha (Ncap a) ≤ a :=
    (h (Ncap a) a).1 le_rfl
  exact (h (Ncap a) b).2 (ha.trans hab)

theorem alpha_at_capacity_le
    {alpha : ℕ → ℝ} {Ncap : ℝ → ℕ}
    (h : ThresholdCharacterization alpha Ncap)
    (a : ℝ) :
    alpha (Ncap a) ≤ a :=
  (h (Ncap a) a).1 le_rfl

/-- If N lies strictly above the threshold cardinality at a, then its minimax
value is strictly above a. -/
theorem alpha_gt_of_capacity_lt
    {alpha : ℕ → ℝ} {Ncap : ℝ → ℕ}
    (h : ThresholdCharacterization alpha Ncap)
    {N : ℕ} {a : ℝ}
    (hN : Ncap a < N) :
    a < alpha N := by
  have hnot : ¬ alpha N ≤ a := by
    intro hle
    have hleN : N ≤ Ncap a :=
      (h N a).2 hle
    exact (not_le_of_gt hN) hleN
  exact lt_of_not_ge hnot

/-- Conversely, alpha(N) > a forces N to lie strictly above Ncap(a). -/
theorem capacity_lt_of_alpha_gt
    {alpha : ℕ → ℝ} {Ncap : ℝ → ℕ}
    (h : ThresholdCharacterization alpha Ncap)
    {N : ℕ} {a : ℝ}
    (ha : a < alpha N) :
    Ncap a < N := by
  by_contra hnot
  have hleN : N ≤ Ncap a := by omega
  have hleAlpha : alpha N ≤ a :=
    (h N a).1 hleN
  linarith

#print axioms capacity_transfer_of_nonshrinking_reduction
#print axioms capacity_transfer_of_nonshrinking_same_value
#print axioms alpha_monotone_of_thresholdCharacterization
#print axioms Ncap_monotone_of_thresholdCharacterization
#print axioms alpha_at_capacity_le
#print axioms alpha_gt_of_capacity_lt
#print axioms capacity_lt_of_alpha_gt

end JSP000404Research
