import JSP000404Research.SixPointNFourUnconditionalSameSignSlot
import JSP000404Research.TransitionSameSignDisjoint
import JSP000404Research.SixPointUnitGapSlots
import JSP000404Research.MinimalPhaseCover
import Mathlib.Tactic

/-!
# Finite-period phase covers instead of an entire-real-line cover

A normalized angular cut phase is periodic with period t = n + delta.
Covering EVERY real number by finitely many bounded bad-phase intervals
would be formally impossible for the wrong reason. The physically relevant
predicate quantifies x over [0,t), retaining any truly periodic translation
inside the phase-obstruction predicate A.

Here the lower bound t <= |T|*delta remains an EXPLICIT hypothesis.
We discharge the additional six-centre n=4 same-sign-unusable hypothesis
when A is supported on concrete ordinary transition unit slots.

No global six-source Boolean-hole theorem follows from this reduction.
-/

namespace JSP000404Research

/-- A finite family covers one half-open normalized projective period. -/
def FinitePeriodCovers
    {I : Type*} (t : ℝ) (A : I → ℝ → Prop) (S : Finset I) : Prop :=
  ∀ x : ℝ, 0 ≤ x → x < t → ∃ i : I, i ∈ S ∧ A i x

theorem no_six_point_finite_period_transition_slot_cover
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin :
      ∀ i : V, i ≠ top →
        centreExponent (C i) t = n - 3)
    (A : GlobalUnitGapSlot C t → ℝ → Prop)
    (S : Finset (GlobalUnitGapSlot C t))
    (hTransition :
      ∀ u : GlobalUnitGapSlot C t, ∀ x : ℝ,
        A u x → GlobalUnitGapOrdinaryTransition C t u)
    (hcoverLower :
      ∀ T : Finset (GlobalUnitGapSlot C t), T ⊆ S →
        FinitePeriodCovers t A T →
        t ≤ (T.card : ℝ) * delta) :
    ¬ FinitePeriodCovers t A S := by
  classical
  have hten :
      Fintype.card (GlobalUnitGapSlot C t) ≤ 10 :=
    six_point_globalUnitGapSlot_card_le_ten C hn
      hdelta0 (by linarith : delta < 1)
      ht hcard top hTop hMin
  have hSbound :
      S.card ≤ 10 :=
    (Finset.card_le_univ S).trans hten
  intro hcover
  have hcredit : t ≤ (S.card : ℝ) * delta :=
    hcoverLower S (Finset.Subset.rfl) hcover
  by_cases hn5 : 5 ≤ n
  · have hnReal : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn5
    have hcardReal : (S.card : ℝ) ≤ 10 := by
      exact_mod_cast hSbound
    have hmul : (S.card : ℝ) * delta ≤ 10 * delta :=
      mul_le_mul_of_nonneg_right hcardReal hdelta0
    have hcredit' :
        (n : ℝ) + delta ≤ (S.card : ℝ) * delta := by
      calc
        (n : ℝ) + delta = t := ht.symm
        _ ≤ (S.card : ℝ) * delta := hcredit
    linarith
  · have hn4 : n = 4 := by omega
    by_cases hsmall : Fintype.card (GlobalUnitGapSlot C t) ≤ 9
    · have hcardS : S.card ≤ 9 :=
        (Finset.card_le_univ S).trans hsmall
      have hcardReal : (S.card : ℝ) ≤ 9 := by
        exact_mod_cast hcardS
      have hmul : (S.card : ℝ) * delta ≤ 9 * delta :=
        mul_le_mul_of_nonneg_right hcardReal hdelta0
      have hcredit4 :
          (4 : ℝ) + delta ≤ (S.card : ℝ) * delta := by
        calc
          (4 : ℝ) + delta = t := by simpa [hn4] using ht.symm
          _ ≤ (S.card : ℝ) * delta := hcredit
      linarith
    · have htenEq : Fintype.card (GlobalUnitGapSlot C t) = 10 := by
        omega
      have htotal :
          (∑ i : V, unitSupport (centreQuotient (C i) t)) = 10 :=
        (globalUnitGapSlot_card_eq_sum_unitSupport C t).symm.trans htenEq
      have ht4 : t = (4 : ℝ) + delta := by
        simpa [hn4] using ht
      have hTop4 : centreExponent (C top) t = 3 := by
        simpa [hn4] using hTop
      have hMin4 :
          ∀ i : V, i ≠ top →
            centreExponent (C i) t = 1 := by
        intro i hi
        simpa [hn4] using hMin i hi
      obtain ⟨u, hsame⟩ :=
        six_point_n_four_equality_exists_global_sameSign_unit_slot
          hp hcap hdelta0 hdeltaHalf ht4 hlam
          C hcard top hTop4 hMin4 htotal
      have hremove :
          FinitePeriodCovers t A (S.erase u) := by
        intro x hx0 hxt
        obtain ⟨v, hvS, hvA⟩ := hcover x hx0 hxt
        have hvne : v ≠ u := by
          intro hvu
          subst v
          exact (globalUnitGapSameSign_not_ordinaryTransition
            C t u hsame) (hTransition u x hvA)
        exact ⟨v, Finset.mem_erase.mpr ⟨hvne, hvS⟩, hvA⟩
      have hsub : S.erase u ⊆ S := Finset.erase_subset u S
      have hlower : t ≤ ((S.erase u).card : ℝ) * delta :=
        hcoverLower (S.erase u) hsub hremove
      have heraseSub :
          S.erase u ⊆ (Finset.univ.erase u) := by
        intro v hv
        exact Finset.mem_erase.mpr
          ⟨(Finset.mem_erase.mp hv).1, Finset.mem_univ v⟩
      have heraseCard : (Finset.univ.erase u).card = 9 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ u),
          Finset.card_univ, htenEq]
      have hcard9 : (S.erase u).card ≤ 9 :=
        (Finset.card_le_card heraseSub).trans_eq heraseCard
      have hcardReal : ((S.erase u).card : ℝ) ≤ 9 := by
        exact_mod_cast hcard9
      have hmul :
          ((S.erase u).card : ℝ) * delta ≤ 9 * delta :=
        mul_le_mul_of_nonneg_right hcardReal hdelta0
      have hlower4 :
          (4 : ℝ) + delta ≤ ((S.erase u).card : ℝ) * delta := by
        calc
          (4 : ℝ) + delta = t := ht4.symm
          _ ≤ ((S.erase u).card : ℝ) * delta := hlower
      linarith

#print axioms no_six_point_finite_period_transition_slot_cover

end JSP000404Research
