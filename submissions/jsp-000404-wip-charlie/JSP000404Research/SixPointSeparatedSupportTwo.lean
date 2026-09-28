import JSP000404Research.SixPointMixedTopDeletion
import JSP000404Research.ConcreteDeficitThree
import JSP000404Research.ThirdLayerSupportOneMultiplicity
import Mathlib.Tactic

/-!
# A separated support-two minimum in every hard top-deletion branch

Let G be the set of non-top minima whose exponent rises by at least one after
deleting the sharp top.

The top-deletion weight ledger needs only |G| >= 4, not exactly four.  Since
there are five minima, four gains already replace the lost top mass.

Therefore in a branch with no compensated top deletion, |G| <= 3 and at least
two minima are non-gaining.

Every support-three minimum belongs to G by SharpSupportThreeDeletionGain.
Thus every non-gaining minimum has support one or two.  There can be at most
one support-one minimum, so among two distinct non-gaining minima at least one
has support two.

Finally, if the ray from such a support-two centre to top were flanked by two
positive cyclic quotients, CyclicPositiveRayDeletionGain would put that centre
back in G.  Hence the support-two witness is genuinely separated at the top
ray.

This removes the previous mixed/pure support-profile case split from the hard
branch: every uncompensated six-point profile contains one concrete separated
support-two minimum.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Non-top minima that gain one exponent unit when the top is deleted. -/
noncomputable def topDeletionGainMinima
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard3 : 3 ≤ Fintype.card V)
    (top : V) (t : ℝ) : Finset V := by
  classical
  exact (Finset.univ.erase top).filter fun v =>
    centreExponent (C v) t + 1 ≤
      exponentAfterDeleteTopAt C hcard3 top t v

theorem mem_topDeletionGainMinima_iff
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard3 : 3 ≤ Fintype.card V)
    (top : V) (t : ℝ) (v : V) :
    v ∈ topDeletionGainMinima C hcard3 top t ↔
      v ≠ top ∧
      centreExponent (C v) t + 1 ≤
        exponentAfterDeleteTopAt C hcard3 top t v := by
  classical
  simp [topDeletionGainMinima]

/-- The pure ledger works with any gain set of cardinality at least four. -/
theorem five_survivor_weight_ge_six_point_profile_of_at_least_four_gains
    {V : Type*} [Fintype V] [DecidableEq V]
    {n : ℕ}
    (hn : 3 ≤ n)
    (top : V)
    (hcard : Fintype.card V = 6)
    (childExponent : V → ℕ)
    (good : Finset V)
    (hgoodSub :
      good ⊆ (Finset.univ.erase top : Finset V))
    (hgoodCard : 4 ≤ good.card)
    (hbase :
      ∀ v : V, v ≠ top →
        n - 3 ≤ childExponent v)
    (hgain :
      ∀ v ∈ good,
        n - 2 ≤ childExponent v) :
    2 ^ (n - 1) + 5 * 2 ^ (n - 3)
      ≤
    ∑ v ∈ (Finset.univ.erase top : Finset V),
      2 ^ childExponent v := by
  classical
  let S : Finset V := Finset.univ.erase top
  let R : Finset V := S \ good
  have hScard : S.card = 5 := by
    dsimp [S]
    rw [Finset.card_erase_of_mem (Finset.mem_univ top),
        Finset.card_univ, hcard]
  have hgoodLe : good.card ≤ 5 := by
    exact (Finset.card_le_card hgoodSub).trans_eq hScard
  have hRcard : R.card = 5 - good.card := by
    dsimp [R]
    rw [Finset.card_sdiff hgoodSub, hScard]

  have hgoodLower :
      good.card * 2 ^ (n - 2)
        ≤
      ∑ v ∈ good, 2 ^ childExponent v := by
    calc
      good.card * 2 ^ (n - 2)
          = ∑ _v ∈ good, 2 ^ (n - 2) := by
              simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ good, 2 ^ childExponent v := by
            exact Finset.sum_le_sum
              (fun v hv =>
                Nat.pow_le_pow_right
                  (by norm_num : 0 < 2)
                  (hgain v hv))

  have hrestLower :
      R.card * 2 ^ (n - 3)
        ≤
      ∑ v ∈ R, 2 ^ childExponent v := by
    calc
      R.card * 2 ^ (n - 3)
          = ∑ _v ∈ R, 2 ^ (n - 3) := by
              simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ R, 2 ^ childExponent v := by
            exact Finset.sum_le_sum
              (fun v hv => by
                apply Nat.pow_le_pow_right
                  (by norm_num : 0 < 2)
                apply hbase v
                have hvS : v ∈ S :=
                  (Finset.mem_sdiff.mp hv).1
                simpa [S] using (Finset.mem_erase.mp hvS).1)

  have hsplit :
      (∑ v ∈ S, 2 ^ childExponent v)
        =
      (∑ v ∈ good, 2 ^ childExponent v) +
      (∑ v ∈ R, 2 ^ childExponent v) := by
    have hsd :=
      Finset.sum_sdiff hgoodSub
        (fun v => 2 ^ childExponent v)
    dsimp [R]
    omega

  have hchild :
      good.card * 2 ^ (n - 2) +
          R.card * 2 ^ (n - 3)
        ≤
      ∑ v ∈ S, 2 ^ childExponent v := by
    rw [hsplit]
    omega

  have hn2 : n - 2 = (n - 3) + 1 := by omega
  have hn1 : n - 1 = (n - 3) + 2 := by omega
  rw [hn2, hn1, pow_add, pow_add] at hchild ⊢
  norm_num at hchild ⊢
  rw [hRcard] at hchild
  have hcoef : 9 ≤ 2 * good.card + (5 - good.card) := by
    omega
  have hpowPos : 0 < 2 ^ (n - 3) := by positivity
  dsimp [S]
  nlinarith

/-- Four or more actual top-deletion gain minima already compensate the top. -/
theorem six_point_top_deletion_compensated_of_gain_set_card_ge_four
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t : ℝ} {n : ℕ}
    (hcard : Fintype.card V = 6)
    (hn : 3 ≤ n)
    (ht0 : 0 ≤ t)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin :
      ∀ v : V, v ≠ top →
        centreExponent (C v) t = n - 3)
    (hgainCard :
      4 ≤
        (topDeletionGainMinima C
          (by rw [hcard]; omega) top t).card) :
    2 ^ (n - 1) + 5 * 2 ^ (n - 3)
      ≤
    ∑ v ∈ (Finset.univ.erase top : Finset V),
      2 ^ exponentAfterDeleteTopAt C
        (by rw [hcard]; omega) top t v := by
  let hcard3 : 3 ≤ Fintype.card V := by
    rw [hcard]
    omega
  let G := topDeletionGainMinima C hcard3 top t
  apply five_survivor_weight_ge_six_point_profile_of_at_least_four_gains
      hn top hcard
      (exponentAfterDeleteTopAt C hcard3 top t)
      G
  · intro v hv
    have h := (mem_topDeletionGainMinima_iff
      C hcard3 top t v).1 hv
    simp [G]
    exact Finset.mem_erase.mpr ⟨h.1, Finset.mem_univ v⟩
  · simpa [G] using hgainCard
  · intro v hvt
    rw [← hMin v hvt]
    exact exponent_le_after_delete_top C top ht0 hcard3 hvt
  · intro v hv
    have hg := (mem_topDeletionGainMinima_iff
      C hcard3 top t v).1 hv
    rw [hMin v hg.1] at hg
    omega

theorem topDeletionGainMinima_card_le_three_of_no_compensated_top
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t : ℝ} {n : ℕ}
    (hcard : Fintype.card V = 6)
    (hn : 3 ≤ n)
    (ht0 : 0 ≤ t)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin :
      ∀ v : V, v ≠ top →
        centreExponent (C v) t = n - 3)
    (hNoTop :
      SixPointNoCompensatedTopDeletion
        C (by rw [hcard]; omega) top t n) :
    (topDeletionGainMinima C
      (by rw [hcard]; omega) top t).card ≤ 3 := by
  by_contra hnot
  have hfour :
      4 ≤
        (topDeletionGainMinima C
          (by rw [hcard]; omega) top t).card := by
    omega
  exact hNoTop
    (six_point_top_deletion_compensated_of_gain_set_card_ge_four
      C hcard hn ht0 top hTop hMin hfour)

/-- A support-three minimum is always in the top-deletion gain set. -/
theorem support_three_mem_topDeletionGainMinima
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta : ℝ} {n : ℕ}
    (hcard : Fintype.card V = 6)
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    {v : V}
    (hvt : v ≠ top)
    (hV : centreExponent (C v) t = n - 3)
    (hsup :
      positiveSupport (centreQuotient (C v) t) = 3) :
    v ∈ topDeletionGainMinima C
      (by rw [hcard]; omega) top t := by
  rw [mem_topDeletionGainMinima_iff]
  refine ⟨hvt, ?_⟩
  exact exponent_add_one_le_after_delete_top_of_support_three
    hp hcap C (by rw [hcard]; omega)
    hn hdelta0 hdeltaHalf ht hlam
    top hTop hvt hV hsup

/-- Top-pinned positive-positive quotient support is also a gain-set witness. -/
def TopPinnedPositivePair
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (top i : V) (hit : i ≠ top) (t : ℝ) : Prop :=
  ∃ pre post : List (OtherVertex i),
    ∃ qOut qIn : ℕ, ∃ qmid : List ℕ,
      (C i).rays =
        pre ++ deletedParentRay top i hit :: post ∧
      (quotientList t (C i).gaps).rotate pre.length =
        qOut :: qmid ++ [qIn] ∧
      1 ≤ qOut ∧ 1 ≤ qIn

theorem topPinnedPositivePair_mem_topDeletionGainMinima
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t : ℝ}
    (hcard3 : 3 ≤ Fintype.card V)
    (ht0 : 0 ≤ t)
    (top i : V)
    (hit : i ≠ top)
    (hpin : TopPinnedPositivePair C top i hit t) :
    i ∈ topDeletionGainMinima C hcard3 top t := by
  obtain ⟨pre, post, qOut, qIn, qmid,
      hsplit, hqrot, hOut, hIn⟩ := hpin
  rw [mem_topDeletionGainMinima_iff]
  refine ⟨hit, ?_⟩
  exact exponent_add_one_le_after_delete_top_of_positive_positive_pin
    C hcard3 ht0 hit pre post hsplit
    qOut qIn qmid hqrot hOut hIn

/-- Main hard-branch reduction: some minimum has support two, does not gain
when top is deleted, and therefore cannot be positive-positive pinned at the
top ray. -/
theorem exists_separated_support_two_minimum_of_no_compensated_top
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta : ℝ} {n : ℕ}
    (hcard : Fintype.card V = 6)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin :
      ∀ v : V, v ≠ top →
        centreExponent (C v) t = n - 3)
    (hNoTop :
      SixPointNoCompensatedTopDeletion
        C (by rw [hcard]; omega) top t n) :
    ∃ v : V,
      v ≠ top ∧
      positiveSupport (centreQuotient (C v) t) = 2 ∧
      v ∉ topDeletionGainMinima C
        (by rw [hcard]; omega) top t ∧
      ¬ TopPinnedPositivePair C top v
          (by assumption) t := by
  classical
  let hcard3 : 3 ≤ Fintype.card V := by
    rw [hcard]
    omega
  let minima : Finset V := Finset.univ.erase top
  let G : Finset V :=
    topDeletionGainMinima C hcard3 top t
  let N : Finset V := minima \ G

  have hminCard : minima.card = 5 := by
    dsimp [minima]
    rw [Finset.card_erase_of_mem (Finset.mem_univ top),
        Finset.card_univ, hcard]

  have hGsub : G ⊆ minima := by
    intro v hv
    have hg :=
      (mem_topDeletionGainMinima_iff
        C hcard3 top t v).1 hv
    exact Finset.mem_erase.mpr ⟨hg.1, Finset.mem_univ v⟩

  have hGcard : G.card ≤ 3 := by
    dsimp [G, hcard3]
    exact topDeletionGainMinima_card_le_three_of_no_compensated_top
      C hcard (by omega : 3 ≤ n)
      (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht).le
      top hTop hMin hNoTop

  have hNcard : 2 ≤ N.card := by
    dsimp [N]
    rw [Finset.card_sdiff hGsub, hminCard]
    omega

  obtain ⟨a, haN, b, hbN, hab⟩ :=
    Finset.two_le_card.mp hNcard

  have haMin : a ∈ minima := (Finset.mem_sdiff.mp haN).1
  have hbMin : b ∈ minima := (Finset.mem_sdiff.mp hbN).1
  have haNotG : a ∉ G := (Finset.mem_sdiff.mp haN).2
  have hbNotG : b ∉ G := (Finset.mem_sdiff.mp hbN).2
  have hat : a ≠ top := (Finset.mem_erase.mp haMin).1
  have hbt : b ≠ top := (Finset.mem_erase.mp hbMin).1

  have support12 :
      ∀ v : V, v ≠ top →
        v ∉ G →
        positiveSupport (centreQuotient (C v) t) = 1 ∨
          positiveSupport (centreQuotient (C v) t) = 2 := by
    intro v hvt hvNotG
    rcases concrete_deficit_three_structure
        (C v) (by omega : 4 ≤ n)
        hdelta0 (by linarith : delta < 1)
        ht (hMin v hvt)
      with h1 | h2 | h3
    · exact Or.inl h1.1
    · exact Or.inr h2.1
    · exfalso
      apply hvNotG
      dsimp [G, hcard3]
      exact support_three_mem_topDeletionGainMinima
        hp hcap C hcard (by omega : 4 ≤ n)
        hdelta0 hdeltaHalf ht hlam
        top hTop hvt (hMin v hvt) h3.1

  have ha12 := support12 a hat haNotG
  have hb12 := support12 b hbt hbNotG

  have chooseSupportTwo :
      ∃ v : V,
        v ≠ top ∧ v ∉ G ∧
        positiveSupport (centreQuotient (C v) t) = 2 := by
    rcases ha12 with ha1 | ha2
    · rcases hb12 with hb1 | hb2
      · exfalso
        exact no_top_with_two_support_one_deficit_three
          hp hcap C hn5 hdelta0 hdeltaHalf ht hlam
          hat.symm hbt.symm hab
          hTop (hMin a hat) (hMin b hbt)
          ha1 hb1
      · exact ⟨b, hbt, hbNotG, hb2⟩
    · exact ⟨a, hat, haNotG, ha2⟩

  obtain ⟨v, hvt, hvNotG, hsup2⟩ := chooseSupportTwo
  have hnotPinned :
      ¬ TopPinnedPositivePair C top v hvt t := by
    intro hpin
    apply hvNotG
    dsimp [G, hcard3]
    exact topPinnedPositivePair_mem_topDeletionGainMinima
      C (by rw [hcard]; omega)
      (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht).le
      top v hvt hpin

  refine ⟨v, hvt, hsup2, ?_, hnotPinned⟩
  simpa [G, hcard3] using hvNotG

#print axioms topDeletionGainMinima
#print axioms five_survivor_weight_ge_six_point_profile_of_at_least_four_gains
#print axioms topDeletionGainMinima_card_le_three_of_no_compensated_top
#print axioms exists_separated_support_two_minimum_of_no_compensated_top

end JSP000404Research
