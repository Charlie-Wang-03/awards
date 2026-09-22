import JSP000404Research.TransitionGapAlignment
import Mathlib.Tactic

/-!
# Zero-gap mass for aligned quotient/gap lists

This is the list-valued counterpart of GapRemainder.zeroGapMass.

For aligned quotient/gap lists, every quotient-zero position contributes its
whole geometric gap to the fractional remainder budget.  If

  gaps.sum = 1,
  quotients.sum = n,
  t = n + delta,

then all zero-quotient gaps together have scaled width at most delta.

The localized displayed-entry theorem is the form needed by arbitrary-cardinality
ordinary/wrap zero-gap geometry.
-/

namespace JSP000404Research

def listZeroGapMass : List ℕ → List ℝ → ℝ
  | [], [] => 0
  | q :: qs, g :: gs =>
      (if q = 0 then g else 0) + listZeroGapMass qs gs
  | _, _ => 0

def listRemainderMass (t : ℝ) : List ℕ → List ℝ → ℝ
  | [], [] => 0
  | q :: qs, g :: gs =>
      (t * g - (q : ℝ)) + listRemainderMass t qs gs
  | _, _ => 0

theorem listRemainderMass_eq
    (t : ℝ) (qs : List ℕ) (gs : List ℝ)
    (hlen : qs.length = gs.length) :
    listRemainderMass t qs gs =
      t * gs.sum - (qs.sum : ℝ) := by
  induction qs generalizing gs with
  | nil =>
      cases gs <;> simp [listRemainderMass]
  | cons q qs ih =>
      cases gs with
      | nil =>
          simp at hlen
      | cons g gs =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          simp [listRemainderMass, ih gs hlen]
          ring

theorem listZeroGapMass_scaled_le_remainder
    {t : ℝ} {qs : List ℕ} {gs : List ℝ}
    (halign : QuotientGapAligned t qs gs) :
    t * listZeroGapMass qs gs ≤
      listRemainderMass t qs gs := by
  induction halign with
  | nil =>
      simp [listZeroGapMass, listRemainderMass]
  | @cons q g qs gs hqg htail ih =>
      have hrem : 0 ≤ t * g - (q : ℝ) := by
        linarith
      by_cases hq0 : q = 0
      · subst q
        simp [listZeroGapMass, listRemainderMass] at ih ⊢
        linarith
      · simp [listZeroGapMass, listRemainderMass, hq0] at ih ⊢
        linarith

theorem listZeroGapMass_scaled_le_delta
    (qs : List ℕ) (gs : List ℝ)
    {n : ℕ} {delta t : ℝ}
    (ht : t = (n : ℝ) + delta)
    (hgapsum : gs.sum = 1)
    (hqsum : qs.sum = n)
    (halign : QuotientGapAligned t qs gs) :
    t * listZeroGapMass qs gs ≤ delta := by
  have hlen : qs.length = gs.length :=
    List.Forall₂.length_eq halign
  have hmass :=
    listZeroGapMass_scaled_le_remainder halign
  rw [listRemainderMass_eq t qs gs hlen,
      hgapsum, hqsum, ht] at hmass
  norm_num at hmass
  exact hmass

theorem listZeroGapMass_nonneg
    (qs : List ℕ) (gs : List ℝ)
    (hlen : qs.length = gs.length)
    (hg0 : ∀ g ∈ gs, 0 ≤ g) :
    0 ≤ listZeroGapMass qs gs := by
  induction qs generalizing gs with
  | nil =>
      cases gs <;> simp [listZeroGapMass] at hlen ⊢
  | cons q qs ih =>
      cases gs with
      | nil =>
          simp at hlen
      | cons g gs =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          have hg : 0 ≤ g := hg0 g (by simp)
          have htail : ∀ x ∈ gs, 0 ≤ x := by
            intro x hx
            exact hg0 x (by simp [hx])
          have hi := ih gs hlen htail
          by_cases hq : q = 0 <;>
            simp [listZeroGapMass, hq, hg, hi]

theorem listZeroGapMass_append
    (qs₁ qs₂ : List ℕ) (gs₁ gs₂ : List ℝ)
    (hlen : qs₁.length = gs₁.length) :
    listZeroGapMass (qs₁ ++ qs₂) (gs₁ ++ gs₂) =
      listZeroGapMass qs₁ gs₁ +
        listZeroGapMass qs₂ gs₂ := by
  induction qs₁ generalizing gs₁ with
  | nil =>
      have hnil : gs₁ = [] := List.length_eq_zero.mp (by simpa using hlen.symm)
      subst gs₁
      simp [listZeroGapMass]
  | cons q qs ih =>
      cases gs₁ with
      | nil =>
          simp at hlen
      | cons g gs =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          simp [listZeroGapMass, ih gs hlen, add_assoc]

theorem displayed_zero_gap_mass_eq
    (qpre qpost : List ℕ)
    (gpre gpost : List ℝ)
    (ge : ℝ)
    (hpreLen : qpre.length = gpre.length) :
    listZeroGapMass
        (qpre ++ 0 :: qpost)
        (gpre ++ ge :: gpost)
      =
    listZeroGapMass qpre gpre +
      ge + listZeroGapMass qpost gpost := by
  rw [listZeroGapMass_append qpre (0 :: qpost)
      gpre (ge :: gpost) hpreLen]
  simp [listZeroGapMass, add_assoc]

/-- A displayed quotient-zero entry is bounded by the global fractional
remainder budget. -/
theorem displayed_zero_gap_scaled_le_delta
    (qpre qpost : List ℕ)
    (gpre gpost : List ℝ)
    (ge : ℝ)
    {n : ℕ} {delta t : ℝ}
    (ht : t = (n : ℝ) + delta)
    (hpreLen : gpre.length = qpre.length)
    (hpostLen : gpost.length = qpost.length)
    (hgap0 : ∀ g ∈ gpre ++ ge :: gpost, 0 ≤ g)
    (hgapsum : (gpre ++ ge :: gpost).sum = 1)
    (hqsum : (qpre ++ 0 :: qpost).sum = n)
    (halign :
      QuotientGapAligned t
        (qpre ++ 0 :: qpost)
        (gpre ++ ge :: gpost))
    (ht0 : 0 ≤ t) :
    t * ge ≤ delta := by
  have hpre0 :
      ∀ g ∈ gpre, 0 ≤ g := by
    intro g hg
    exact hgap0 g (by simp [hg])
  have hpost0 :
      ∀ g ∈ gpost, 0 ≤ g := by
    intro g hg
    exact hgap0 g (by simp [hg])
  have hpreMass0 :
      0 ≤ listZeroGapMass qpre gpre :=
    listZeroGapMass_nonneg qpre gpre hpreLen.symm hpre0
  have hpostMass0 :
      0 ≤ listZeroGapMass qpost gpost :=
    listZeroGapMass_nonneg qpost gpost hpostLen.symm hpost0
  have hge0 : 0 ≤ ge :=
    hgap0 ge (by simp)
  have hgeLe :
      ge ≤
        listZeroGapMass
          (qpre ++ 0 :: qpost)
          (gpre ++ ge :: gpost) := by
    rw [displayed_zero_gap_mass_eq
      qpre qpost gpre gpost ge hpreLen.symm]
    linarith
  have hscaled :=
    mul_le_mul_of_nonneg_left hgeLe ht0
  have hmass :=
    listZeroGapMass_scaled_le_delta
      (qpre ++ 0 :: qpost)
      (gpre ++ ge :: gpost)
      ht hgapsum hqsum halign
  exact hscaled.trans hmass

#print axioms listRemainderMass_eq
#print axioms listZeroGapMass_scaled_le_remainder
#print axioms listZeroGapMass_scaled_le_delta
#print axioms listZeroGapMass_append
#print axioms displayed_zero_gap_scaled_le_delta

end JSP000404Research
