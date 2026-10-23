import JSP000404Research.SixPointTwoNonGainers
import JSP000404Research.PositiveGapSlots
import Mathlib.Tactic

/-!
# A sharper positive-gap budget in the support-one hard branch

In the uncompensated six-centre top profile two distinct non-gaining minima
exist. If these have types (1,2), the positive quotient-gap support across
all six original centres is at most 13, not the previous uniform bound 14.
If there is no such pair the existing witness theorem supplies two separate
non-gaining support-two minima.

This is a structural improvement only. It does NOT allocate Boolean holes,
dyadic surplus, or close the planar global lower-branch payment inequality.
-/

namespace JSP000404Research

open scoped BigOperators

private theorem six_centre_sum_le_thirteen_of_three_distinguished
    {V : Type*} [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = 6)
    (f : V → ℕ)
    (top a b : V)
    (hat : a ≠ top) (hbt : b ≠ top) (hab : a ≠ b)
    (hall : ∀ i, f i ≤ 3)
    (htop : f top ≤ 1)
    (ha : f a = 1)
    (hb : f b = 2) :
    (∑ i : V, f i) ≤ 13 := by
  let S : Finset V := Finset.univ.erase top
  let R : Finset V := S.erase a
  let T : Finset V := R.erase b
  have hScard : S.card = 5 := by
    dsimp [S]
    rw [Finset.card_erase_of_mem (Finset.mem_univ top),
        Finset.card_univ, hcard]
  have haS : a ∈ S :=
    Finset.mem_erase.mpr ⟨hat, Finset.mem_univ a⟩
  have hbS : b ∈ S :=
    Finset.mem_erase.mpr ⟨hbt, Finset.mem_univ b⟩
  have hbR : b ∈ R :=
    Finset.mem_erase.mpr ⟨hab.symm, hbS⟩
  have hRcard : R.card = 4 := by
    dsimp [R]
    rw [Finset.card_erase_of_mem haS]
    omega
  have hTcard : T.card = 3 := by
    dsimp [T]
    rw [Finset.card_erase_of_mem hbR]
    omega
  have htail : (∑ i ∈ T, f i) ≤ 9 := by
    calc
      (∑ i ∈ T, f i) ≤ ∑ _i ∈ T, (3 : ℕ) := by
        apply Finset.sum_le_sum
        intro i _hi
        exact hall i
      _ = T.card * 3 := by simp
      _ = 9 := by rw [hTcard]
  have htopSplit :
      (∑ i : V, f i) = f top + ∑ i ∈ S, f i := by
    have h := Finset.sum_erase_add
      (Finset.univ : Finset V) f (Finset.mem_univ top)
    simpa [S, add_comm] using h.symm
  have haSplit :
      (∑ i ∈ S, f i) = f a + ∑ i ∈ R, f i := by
    have h := Finset.sum_erase_add S f haS
    simpa [R, add_comm] using h.symm
  have hbSplit :
      (∑ i ∈ R, f i) = f b + ∑ i ∈ T, f i := by
    have h := Finset.sum_erase_add R f hbR
    simpa [T, add_comm] using h.symm
  rw [htopSplit, haSplit, hbSplit]
  omega

/-- The 1+1+2+3+3+3 original-centre support budget is 13. -/
theorem six_point_positive_gap_card_le_thirteen_of_support_one_two
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    {t delta : ℝ} {n : ℕ}
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (top a b : V)
    (hat : a ≠ top) (hbt : b ≠ top) (hab : a ≠ b)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin : ∀ i : V, i ≠ top →
      centreExponent (C i) t = n - 3)
    (ha : positiveSupport (centreQuotient (C a) t) = 1)
    (hb : positiveSupport (centreQuotient (C b) t) = 2) :
    Fintype.card (GlobalPositiveGapSlot C t) ≤ 13 := by
  classical
  let f : V → ℕ := fun i => positiveSupport (centreQuotient (C i) t)
  have htop : f top ≤ 1 :=
    centre_positiveSupport_le_one_of_exponent_n_sub_one
      (C top) (by omega : 4 ≤ n) hdelta0
      (by linarith : delta < 1) ht hTop
  have hother : ∀ i, i ≠ top → f i ≤ 3 := by
    intro i hi
    exact centre_positiveSupport_le_three_of_exponent_n_sub_three
      (C i) (by omega : 4 ≤ n) hdelta0
      (by linarith : delta < 1) ht (hMin i hi)
  have hall : ∀ i, f i ≤ 3 := by
    intro i
    by_cases hi : i = top
    · subst i
      omega
    · exact hother i hi
  rw [globalPositiveGapSlot_card_eq_sum_positiveSupport C t]
  exact six_centre_sum_le_thirteen_of_three_distinguished
    hcard f top a b hat hbt hab hall htop ha hb

/-- The genuinely uncompensated six-centre geometry has a strict alternative:
either its full positive quotient-gap universe has cardinal at most 13,
or two distinct non-gaining support-two minima survive. -/
theorem six_point_hard_top_thirteen_slots_or_two_support_two
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin : ∀ i : V, i ≠ top →
      centreExponent (C i) t = n - 3)
    (hNoTop :
      SixPointNoCompensatedTopDeletion
        C (by rw [hcard]; omega) top t n) :
    Fintype.card (GlobalPositiveGapSlot C t) ≤ 13 ∨
    ∃ a b : V,
      a ≠ top ∧ b ≠ top ∧ a ≠ b ∧
      a ∉ topDeletionGainMinima C
        (by rw [hcard]; omega) top t ∧
      b ∉ topDeletionGainMinima C
        (by rw [hcard]; omega) top t ∧
      positiveSupport (centreQuotient (C a) t) = 2 ∧
      positiveSupport (centreQuotient (C b) t) = 2 := by
  classical
  rcases two_nonGaining_lowSupport_witnesses
      hp hcap C hcard hn5 hdelta0 hdeltaHalf ht hlam
      top hTop hMin hNoTop with htwo | hone
  · right
    obtain ⟨a, b, hat, hbt, hab, haNot, hbNot,
      haTwo, hbTwo, _hpinA, _hpinB⟩ := htwo
    exact ⟨a, b, hat, hbt, hab, haNot, hbNot, haTwo, hbTwo⟩
  · left
    obtain ⟨a, b, hat, hbt, hab, _haNot, _hbNot,
      haOne, hbTwo, _hpinB⟩ := hone
    exact six_point_positive_gap_card_le_thirteen_of_support_one_two
      C hcard hn5 hdelta0 hdeltaHalf ht top a b
      hat hbt hab hTop hMin haOne hbTwo

#print axioms six_point_positive_gap_card_le_thirteen_of_support_one_two
#print axioms six_point_hard_top_thirteen_slots_or_two_support_two

end JSP000404Research
