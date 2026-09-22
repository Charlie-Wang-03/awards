import JSP000404Research.ListZeroGapMass
import JSP000404Research.FourCentreTransitionCases
import JSP000404Research.TransitionGapAlignment
import Mathlib.Tactic

/-!
# Two narrow clusters after the extremal support-two transition cut

Consider an aligned quotient/gap cycle with exactly two positive quotients,
total quotient mass n, and a distinguished transition quotient equal to one:

  qs = pre ++ 1 :: post.

After cutting at the transition, the interior cyclic order is

  post ++ pre.

Its positive support is exactly one and its sum is n-1.  Hence its unique
positive quotient is n-1.  Splitting there leaves two quotient blocks which
are identically zero.

The aligned geometric gap list splits at the same two cuts.  Since the full
zero-quotient gap mass is at most delta/t, the sum of the geometric widths of
the two zero blocks is at most delta/t.

This is the list-level "two narrow clusters" certificate for the hardest
support-two deficit-two regime.  No cardinality assumption is used.
-/

namespace JSP000404Research

theorem quotientGapAligned_append
    {t : ℝ}
    {q₁ q₂ : List ℕ} {g₁ g₂ : List ℝ}
    (h₁ : QuotientGapAligned t q₁ g₁)
    (h₂ : QuotientGapAligned t q₂ g₂) :
    QuotientGapAligned t (q₁ ++ q₂) (g₁ ++ g₂) := by
  induction h₁ with
  | nil =>
      simpa using h₂
  | cons hqg hrest ih =>
      exact List.Forall₂.cons hqg (ih h₂)

theorem listPositiveCount_eq_zero_forall
    (qs : List ℕ)
    (hzero : listPositiveCount qs = 0) :
    ∀ q ∈ qs, q = 0 := by
  intro q hq
  have hsum :=
    list_sum_eq_zero_of_positiveCount_eq_zero qs hzero
  have hle : q ≤ qs.sum :=
    List.le_sum_of_mem hq
  rw [hsum] at hle
  omega

theorem split_unique_positive_of_count_one
    (qs : List ℕ) (q : ℕ)
    (hq0 : q ≠ 0)
    (hsupport : listPositiveCount qs = 1)
    (hqmem : q ∈ qs) :
    ∃ left right : List ℕ,
      qs = left ++ q :: right ∧
      (∀ x ∈ left, x = 0) ∧
      (∀ x ∈ right, x = 0) := by
  induction qs with
  | nil =>
      simp at hqmem
  | cons a as ih =>
      rw [List.mem_cons] at hqmem
      by_cases ha0 : a = 0
      · subst a
        simp only [listPositiveCount, if_pos rfl, zero_add] at hsupport
        rcases hqmem with hbad | htail
        · exact False.elim (hq0 hbad.symm)
        · obtain ⟨left, right, hsplit, hleft, hright⟩ :=
            ih hsupport htail
          refine ⟨0 :: left, right, ?_, ?_, hright⟩
          · simp [hsplit]
          · intro x hx
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · rfl
            · exact hleft x hx
      · have haPos : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
        simp only [listPositiveCount, if_neg ha0] at hsupport
        have htailCount : listPositiveCount as = 0 := by omega
        rcases hqmem with hqa | htail
        · have haq : a = q := hqa.symm
          subst a
          refine ⟨[], as, by simp, ?_, ?_⟩
          · simp
          · exact listPositiveCount_eq_zero_forall as htailCount
        · have hqTailZero :=
            listPositiveCount_eq_zero_forall as htailCount q htail
          exact False.elim (hq0 hqTailZero)

theorem listZeroGapMass_append
    (q₁ q₂ : List ℕ) (g₁ g₂ : List ℝ)
    (hlen : q₁.length = g₁.length) :
    listZeroGapMass (q₁ ++ q₂) (g₁ ++ g₂) =
      listZeroGapMass q₁ g₁ + listZeroGapMass q₂ g₂ := by
  induction q₁ generalizing g₁ with
  | nil =>
      have hg : g₁ = [] := List.length_eq_zero.mp (by simpa using hlen.symm)
      subst g₁
      simp [listZeroGapMass]
  | cons q qs ih =>
      cases g₁ with
      | nil =>
          simp at hlen
      | cons g gs =>
          simp at hlen
          simp [listZeroGapMass, ih gs hlen, add_assoc]

theorem listZeroGapMass_two_zero_blocks
    (left right : List ℕ)
    (leftG rightG : List ℝ)
    (q : ℕ) (g : ℝ)
    (hq0 : q ≠ 0)
    (hlenL : left.length = leftG.length)
    (hlenR : right.length = rightG.length)
    (hleft : ∀ x ∈ left, x = 0)
    (hright : ∀ x ∈ right, x = 0) :
    listZeroGapMass
        (left ++ q :: right)
        (leftG ++ g :: rightG)
      =
    leftG.sum + rightG.sum := by
  rw [listZeroGapMass_append left (q :: right)
        leftG (g :: rightG) hlenL]
  have hleftMass :=
    listZeroGapMass_eq_gap_sum_of_all_zero
      left leftG hlenL hleft
  rw [hleftMass]
  simp only [listZeroGapMass, if_neg hq0]
  have hrightMass :=
    listZeroGapMass_eq_gap_sum_of_all_zero
      right rightG hlenR hright
  rw [hrightMass]
  ring

/-- Main pure list theorem: after cutting the transition quotient 1 and then
the hidden quotient n-1, the two remaining aligned gap blocks have total
scaled width at most delta. -/
theorem exists_two_narrow_zero_blocks
    (qs : List ℕ) (gaps : List ℝ)
    (pre post : List ℕ)
    {n : ℕ} {delta t : ℝ}
    (hn : 3 ≤ n)
    (ht : t = (n : ℝ) + delta)
    (htpos : 0 < t)
    (hq :
      qs = pre ++ 1 :: post)
    (hsupport :
      listPositiveCount qs = 2)
    (hqsum : qs.sum = n)
    (hgapsum : gaps.sum = 1)
    (halign : QuotientGapAligned t qs gaps)
    (hhidden : n - 1 ∈ qs) :
    ∃ gpre gpost : List ℝ, ∃ ge : ℝ,
      ∃ leftQ rightQ : List ℕ,
      ∃ leftG rightG : List ℝ, ∃ gh : ℝ,
        gaps = gpre ++ ge :: gpost ∧
        pre.length = gpre.length ∧
        post.length = gpost.length ∧
        post ++ pre = leftQ ++ (n - 1) :: rightQ ∧
        gpost ++ gpre = leftG ++ gh :: rightG ∧
        leftQ.length = leftG.length ∧
        rightQ.length = rightG.length ∧
        (∀ x ∈ leftQ, x = 0) ∧
        (∀ x ∈ rightQ, x = 0) ∧
        (((n - 1 : ℕ) : ℝ) ≤ t * gh) ∧
        t * (leftG.sum + rightG.sum) ≤ delta := by
  have halign' :
      QuotientGapAligned t (pre ++ 1 :: post) gaps := by
    rw [← hq]
    exact halign
  obtain ⟨gpre, gpost, ge, hgaps, hpreLen, hpostLen,
      htransAlign, hpreAlign, hpostAlign⟩ :=
    aligned_gap_decomposition halign'

  have hsFull :
      listPositiveCount (pre ++ 1 :: post) = 2 := by
    rw [← hq]
    exact hsupport
  have hInternalSupport :
      listPositiveCount (post ++ pre) = 1 := by
    rw [listPositiveCount_append] at hsFull ⊢
    simp [listPositiveCount] at hsFull
    omega

  have hInternalSum :
      (post ++ pre).sum = n - 1 := by
    have hsumFull :
        (pre ++ 1 :: post).sum = n := by
      rw [← hq]
      exact hqsum
    simp only [List.sum_append, List.sum_cons, List.sum_nil,
      add_zero] at hsumFull ⊢
    omega

  have hne : n - 1 ≠ 1 := by omega
  have hhiddenInternal : n - 1 ∈ post ++ pre := by
    rw [hq] at hhidden
    simp only [List.mem_append, List.mem_cons] at hhidden ⊢
    rcases hhidden with hpre | hmid
    · exact Or.inr hpre
    · rcases hmid with hmid | hpost
      · exact False.elim (hne hmid.symm)
      · exact Or.inl hpost

  obtain ⟨leftQ, rightQ, hsplitQ, hleftZero, hrightZero⟩ :=
    split_unique_positive_of_count_one
      (post ++ pre) (n - 1)
      (by omega) hInternalSupport hhiddenInternal

  have hInternalAlign :
      QuotientGapAligned t (post ++ pre) (gpost ++ gpre) :=
    quotientGapAligned_append hpostAlign hpreAlign
  have hInternalAlign' :
      QuotientGapAligned t
        (leftQ ++ (n - 1) :: rightQ)
        (gpost ++ gpre) := by
    rw [← hsplitQ]
    exact hInternalAlign
  obtain ⟨leftG, rightG, gh, hsplitG,
      hleftLen, hrightLen, hhiddenAlign, _, _⟩ :=
    aligned_gap_decomposition hInternalAlign'

  have hzeroFull :
      t * listZeroGapMass qs gaps ≤ delta :=
    listZeroGapMass_scaled_le_delta
      qs gaps ht hgapsum hqsum halign

  have hfullMass :
      listZeroGapMass qs gaps =
        listZeroGapMass (post ++ pre) (gpost ++ gpre) := by
    rw [hq, hgaps]
    have hpreLen' : pre.length = gpre.length := hpreLen.symm
    rw [listZeroGapMass_append pre (1 :: post)
          gpre (ge :: gpost) hpreLen']
    simp only [listZeroGapMass, if_neg (by decide : (1 : ℕ) ≠ 0)]
    have hpostLen' : post.length = gpost.length := hpostLen.symm
    rw [listZeroGapMass_append post pre gpost gpre hpostLen']
    ring

  have hInternalMass :
      listZeroGapMass (post ++ pre) (gpost ++ gpre) =
        leftG.sum + rightG.sum := by
    rw [hsplitQ, hsplitG]
    exact listZeroGapMass_two_zero_blocks
      leftQ rightQ leftG rightG (n - 1) gh
      (by omega) hleftLen.symm hrightLen.symm
      hleftZero hrightZero

  refine ⟨gpre, gpost, ge,
    leftQ, rightQ, leftG, rightG, gh,
    hgaps, ?_, ?_, hsplitQ, hsplitG,
    ?_, ?_, hleftZero, hrightZero,
    hhiddenAlign, ?_⟩
  · exact hpreLen.symm
  · exact hpostLen.symm
  · exact hleftLen.symm
  · exact hrightLen.symm
  · rw [hfullMass, hInternalMass] at hzeroFull
    exact hzeroFull


theorem list_sum_pos_of_positiveCount_pos
    (qs : List ℕ)
    (hpos : 0 < listPositiveCount qs) :
    0 < qs.sum := by
  induction qs with
  | nil =>
      simp [listPositiveCount] at hpos
  | cons q qs ih =>
      by_cases hq0 : q = 0
      · subst q
        simp only [listPositiveCount, if_pos rfl, zero_add] at hpos
        simp only [List.sum_cons, zero_add]
        exact ih hpos
      · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
        simp only [List.sum_cons]
        omega

/-- General support-two form.  The distinguished transition quotient may be
any positive qe.  The unique other positive quotient is n-qe, and all
remaining gaps form two zero blocks of total scaled width at most delta. -/
theorem exists_two_narrow_zero_blocks_of_support_two
    (qs : List ℕ) (gaps : List ℝ)
    (pre post : List ℕ) (qe : ℕ)
    {n : ℕ} {delta t : ℝ}
    (ht : t = (n : ℝ) + delta)
    (htpos : 0 < t)
    (hqe0 : qe ≠ 0)
    (hq :
      qs = pre ++ qe :: post)
    (hsupport :
      listPositiveCount qs = 2)
    (hqsum : qs.sum = n)
    (hgapsum : gaps.sum = 1)
    (halign : QuotientGapAligned t qs gaps) :
    ∃ gpre gpost : List ℝ, ∃ ge : ℝ,
      ∃ leftQ rightQ : List ℕ,
      ∃ leftG rightG : List ℝ, ∃ gh : ℝ,
        gaps = gpre ++ ge :: gpost ∧
        pre.length = gpre.length ∧
        post.length = gpost.length ∧
        0 < n - qe ∧
        post ++ pre = leftQ ++ (n - qe) :: rightQ ∧
        gpost ++ gpre = leftG ++ gh :: rightG ∧
        leftQ.length = leftG.length ∧
        rightQ.length = rightG.length ∧
        (∀ x ∈ leftQ, x = 0) ∧
        (∀ x ∈ rightQ, x = 0) ∧
        (((n - qe : ℕ) : ℝ) ≤ t * gh) ∧
        t * (leftG.sum + rightG.sum) ≤ delta := by
  have halign' :
      QuotientGapAligned t (pre ++ qe :: post) gaps := by
    rw [← hq]
    exact halign
  obtain ⟨gpre, gpost, ge, hgaps, hpreLen, hpostLen,
      htransAlign, hpreAlign, hpostAlign⟩ :=
    aligned_gap_decomposition halign'

  have hsFull :
      listPositiveCount (pre ++ qe :: post) = 2 := by
    rw [← hq]
    exact hsupport
  have hInternalSupport :
      listPositiveCount (post ++ pre) = 1 := by
    rw [listPositiveCount_append] at hsFull ⊢
    simp [listPositiveCount, hqe0] at hsFull
    omega
  have hInternalSum :
      (post ++ pre).sum = n - qe := by
    have hsumFull :
        (pre ++ qe :: post).sum = n := by
      rw [← hq]
      exact hqsum
    simp only [List.sum_append, List.sum_cons, List.sum_nil,
      add_zero] at hsumFull ⊢
    omega
  have hhiddenPos :
      0 < n - qe := by
    have hpos :=
      list_sum_pos_of_positiveCount_pos
        (post ++ pre) (by omega)
    rw [hInternalSum] at hpos
    exact hpos
  have hhiddenInternal :
      n - qe ∈ post ++ pre := by
    have hmem :=
      list_sum_mem_of_positiveCount_one
        (post ++ pre) hInternalSupport
        (by rw [hInternalSum]; exact hhiddenPos)
    rw [hInternalSum] at hmem
    exact hmem

  obtain ⟨leftQ, rightQ, hsplitQ, hleftZero, hrightZero⟩ :=
    split_unique_positive_of_count_one
      (post ++ pre) (n - qe)
      (by omega) hInternalSupport hhiddenInternal

  have hInternalAlign :
      QuotientGapAligned t (post ++ pre) (gpost ++ gpre) :=
    quotientGapAligned_append hpostAlign hpreAlign
  have hInternalAlign' :
      QuotientGapAligned t
        (leftQ ++ (n - qe) :: rightQ)
        (gpost ++ gpre) := by
    rw [← hsplitQ]
    exact hInternalAlign
  obtain ⟨leftG, rightG, gh, hsplitG,
      hleftLen, hrightLen, hhiddenAlign, _, _⟩ :=
    aligned_gap_decomposition hInternalAlign'

  have hzeroFull :
      t * listZeroGapMass qs gaps ≤ delta :=
    listZeroGapMass_scaled_le_delta
      qs gaps ht hgapsum hqsum halign

  have hfullMass :
      listZeroGapMass qs gaps =
        listZeroGapMass (post ++ pre) (gpost ++ gpre) := by
    rw [hq, hgaps]
    have hpreLen' : pre.length = gpre.length := hpreLen.symm
    rw [listZeroGapMass_append pre (qe :: post)
          gpre (ge :: gpost) hpreLen']
    simp only [listZeroGapMass, if_neg hqe0]
    have hpostLen' : post.length = gpost.length := hpostLen.symm
    rw [listZeroGapMass_append post pre gpost gpre hpostLen']
    ring

  have hInternalMass :
      listZeroGapMass (post ++ pre) (gpost ++ gpre) =
        leftG.sum + rightG.sum := by
    rw [hsplitQ, hsplitG]
    exact listZeroGapMass_two_zero_blocks
      leftQ rightQ leftG rightG (n - qe) gh
      (by omega) hleftLen.symm hrightLen.symm
      hleftZero hrightZero

  refine ⟨gpre, gpost, ge,
    leftQ, rightQ, leftG, rightG, gh,
    hgaps, hpreLen.symm, hpostLen.symm,
    hhiddenPos, hsplitQ, hsplitG,
    hleftLen.symm, hrightLen.symm,
    hleftZero, hrightZero,
    hhiddenAlign, ?_⟩
  rw [hfullMass, hInternalMass] at hzeroFull
  exact hzeroFull

#print axioms split_unique_positive_of_count_one
#print axioms listZeroGapMass_two_zero_blocks
#print axioms exists_two_narrow_zero_blocks

end JSP000404Research
