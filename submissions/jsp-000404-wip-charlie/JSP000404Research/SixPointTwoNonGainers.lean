import JSP000404Research.SixPointSeparatedSupportTwo
import JSP000404Research.ThirdLayerSupportOneMultiplicity
import Mathlib.Tactic

/-!
# Two non-gainers in the uncompensated top-deletion branch

In the six-point profile, failure of compensated top deletion implies that
the top-deletion gain set has cardinality at most three.  Hence among the five
minima there are at least two distinct non-gainers.

Every non-gainer has support one or two; support three would itself be a
top-deletion gain.  Moreover there is at most one support-one minimum.

Therefore the hard branch has a sharper low-support dichotomy:

* either two distinct non-gaining minima both have support two;
* or one non-gaining minimum has support one and a second one has support two.

Every non-gaining support-two minimum is automatically separated at the top
ray, because a positive-positive top pin would itself create a top-deletion
gain.

This retains both low-support witnesses instead of discarding one of them.
-/

namespace JSP000404Research

theorem nonGaining_support_one_or_two
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
    {v : V}
    (hvt : v ≠ top)
    (hMin : centreExponent (C v) t = n - 3)
    (hNotGain :
      v ∉ topDeletionGainMinima C
        (by rw [hcard]; omega) top t) :
    positiveSupport (centreQuotient (C v) t) = 1 ∨
      positiveSupport (centreQuotient (C v) t) = 2 := by
  rcases concrete_deficit_three_structure
      (C v) (by omega : 4 ≤ n)
      hdelta0 (by linarith : delta < 1)
      ht hMin
    with h1 | h2 | h3
  · exact Or.inl h1.1
  · exact Or.inr h2.1
  · exfalso
    exact hNotGain
      (support_three_mem_topDeletionGainMinima
        hp hcap C hcard (by omega : 4 ≤ n)
        hdelta0 hdeltaHalf ht hlam
        top hTop hvt hMin h3.1)

theorem nonGaining_support_two_is_separated
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t : ℝ}
    (hcard : Fintype.card V = 6)
    (ht0 : 0 ≤ t)
    (top v : V)
    (hvt : v ≠ top)
    (hNotGain :
      v ∉ topDeletionGainMinima C
        (by rw [hcard]; omega) top t) :
    ¬ TopPinnedPositivePair C top v hvt t := by
  intro hpin
  exact hNotGain
    (topPinnedPositivePair_mem_topDeletionGainMinima
      C (by rw [hcard]; omega) ht0
      top v hvt hpin)

/-- Main two-witness hard-top dichotomy. -/
theorem two_nonGaining_lowSupport_witnesses
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
    (
      ∃ a b : V,
        a ≠ top ∧ b ≠ top ∧ a ≠ b ∧
        a ∉ topDeletionGainMinima C
          (by rw [hcard]; omega) top t ∧
        b ∉ topDeletionGainMinima C
          (by rw [hcard]; omega) top t ∧
        positiveSupport (centreQuotient (C a) t) = 2 ∧
        positiveSupport (centreQuotient (C b) t) = 2 ∧
        ¬ TopPinnedPositivePair C top a (by assumption) t ∧
        ¬ TopPinnedPositivePair C top b (by assumption) t
    )
    ∨
    (
      ∃ a b : V,
        a ≠ top ∧ b ≠ top ∧ a ≠ b ∧
        a ∉ topDeletionGainMinima C
          (by rw [hcard]; omega) top t ∧
        b ∉ topDeletionGainMinima C
          (by rw [hcard]; omega) top t ∧
        positiveSupport (centreQuotient (C a) t) = 1 ∧
        positiveSupport (centreQuotient (C b) t) = 2 ∧
        ¬ TopPinnedPositivePair C top b (by assumption) t
    ) := by
  classical
  let hcard3 : 3 ≤ Fintype.card V := by
    rw [hcard]
    omega
  let minima : Finset V := Finset.univ.erase top
  let G : Finset V := topDeletionGainMinima C hcard3 top t
  let N : Finset V := minima \ G

  have hminCard : minima.card = 5 := by
    dsimp [minima]
    rw [Finset.card_erase_of_mem (Finset.mem_univ top),
        Finset.card_univ, hcard]

  have hGsub : G ⊆ minima := by
    intro v hv
    have hg :=
      (mem_topDeletionGainMinima_iff C hcard3 top t v).1 hv
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

  obtain ⟨a, haN, b, hbN, hab⟩ := Finset.two_le_card.mp hNcard
  have haMin := (Finset.mem_sdiff.mp haN).1
  have hbMin := (Finset.mem_sdiff.mp hbN).1
  have haNotG : a ∉ G := (Finset.mem_sdiff.mp haN).2
  have hbNotG : b ∉ G := (Finset.mem_sdiff.mp hbN).2
  have hat : a ≠ top := (Finset.mem_erase.mp haMin).1
  have hbt : b ≠ top := (Finset.mem_erase.mp hbMin).1

  have ha12 :=
    nonGaining_support_one_or_two
      hp hcap C hcard hn5 hdelta0 hdeltaHalf ht hlam
      top hTop hat (hMin a hat)
      (by simpa [G, hcard3] using haNotG)
  have hb12 :=
    nonGaining_support_one_or_two
      hp hcap C hcard hn5 hdelta0 hdeltaHalf ht hlam
      top hTop hbt (hMin b hbt)
      (by simpa [G, hcard3] using hbNotG)

  have hsepA :
      ¬ TopPinnedPositivePair C top a hat t :=
    nonGaining_support_two_is_separated
      C hcard
      (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht).le
      top a hat
      (by simpa [G, hcard3] using haNotG)
  have hsepB :
      ¬ TopPinnedPositivePair C top b hbt t :=
    nonGaining_support_two_is_separated
      C hcard
      (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht).le
      top b hbt
      (by simpa [G, hcard3] using hbNotG)

  rcases ha12 with ha1 | ha2
  · rcases hb12 with hb1 | hb2
    · exact False.elim
        (no_top_with_two_support_one_deficit_three
          hp hcap C hn5 hdelta0 hdeltaHalf ht hlam
          hat.symm hbt.symm hab
          hTop (hMin a hat) (hMin b hbt)
          ha1 hb1)
    · exact Or.inr
        ⟨a,b,hat,hbt,hab,
          by simpa [G,hcard3] using haNotG,
          by simpa [G,hcard3] using hbNotG,
          ha1,hb2,hsepB⟩
  · rcases hb12 with hb1 | hb2
    · exact Or.inr
        ⟨b,a,hbt,hat,hab.symm,
          by simpa [G,hcard3] using hbNotG,
          by simpa [G,hcard3] using haNotG,
          hb1,ha2,hsepA⟩
    · exact Or.inl
        ⟨a,b,hat,hbt,hab,
          by simpa [G,hcard3] using haNotG,
          by simpa [G,hcard3] using hbNotG,
          ha2,hb2,hsepA,hsepB⟩

#print axioms nonGaining_support_one_or_two
#print axioms nonGaining_support_two_is_separated
#print axioms two_nonGaining_lowSupport_witnesses

end JSP000404Research
