import JSP000404Research.TransitionRotation
import JSP000404Research.LinearizedTransitionExposure
import Mathlib.Data.List.Rotate
import Mathlib.Tactic

/-!
# Aligning the unique transition quotient with its geometric gap

The quotient list and the normalized angular-gap list have the same cyclic
order and satisfy pointwise

  q_j <= t * gap_j.

Once the unique transition decomposition gives

  qs = pre ++ qe :: post,   qe != 0,

List.Forall₂ lets us split the gap list at the identical position:

  gaps = gpre ++ ge :: gpost

with qe <= t*ge.  Hence ge>0.

Rotating both lists by |pre|+1 moves the transition quotient and its geometric
gap to the final position:

  post ++ pre ++ [qe],
  gpost ++ gpre ++ [ge].

This is the representation bridge needed before applying the linearized
transition-exposure theorem.
-/

namespace JSP000404Research

/-- Quotients are aligned with normalized gaps through the usual floor lower
bound. -/
def QuotientGapAligned (t : ℝ) (qs : List ℕ) (gaps : List ℝ) : Prop :=
  List.Forall₂ (fun q g => (q : ℝ) ≤ t * g) qs gaps

theorem quotientGapAligned_length
    {t : ℝ} {qs : List ℕ} {gaps : List ℝ}
    (h : QuotientGapAligned t qs gaps) :
    qs.length = gaps.length := by
  exact List.Forall₂.length_eq h

/-- Split aligned quotient/gap lists at a distinguished quotient entry. -/
theorem aligned_gap_decomposition
    {t : ℝ}
    {pre post : List ℕ} {qe : ℕ}
    {gaps : List ℝ}
    (halign :
      QuotientGapAligned t (pre ++ qe :: post) gaps) :
    ∃ gpre gpost : List ℝ, ∃ ge : ℝ,
      gaps = gpre ++ ge :: gpost ∧
      gpre.length = pre.length ∧
      gpost.length = post.length ∧
      (qe : ℝ) ≤ t * ge ∧
      QuotientGapAligned t pre gpre ∧
      QuotientGapAligned t post gpost := by
  induction pre generalizing gaps with
  | nil =>
      simp only [List.nil_append] at halign
      cases gaps with
      | nil =>
          cases halign
      | cons ge gpost =>
          cases halign with
          | cons hqe hpost =>
              refine ⟨[], gpost, ge, ?_, rfl, ?_, hqe, ?_, hpost⟩
              · rfl
              · exact quotientGapAligned_length hpost
              · exact List.Forall₂.nil
  | cons q pre ih =>
      simp only [List.cons_append] at halign
      cases gaps with
      | nil =>
          cases halign
      | cons g gaps =>
          cases halign with
          | cons hqg htail =>
              obtain ⟨gpre, gpost, ge, hgaps, hlenPre,
                  hlenPost, hqe, hpreAlign, hpostAlign⟩ :=
                ih htail
              refine ⟨g :: gpre, gpost, ge, ?_, ?_, hlenPost,
                hqe, ?_, hpostAlign⟩
              · simp [hgaps]
              · simp [hlenPre]
              · exact List.Forall₂.cons hqg hpreAlign

/-- A positive distinguished quotient gives a positive aligned geometric gap. -/
theorem aligned_transition_gap_pos
    {t ge : ℝ} {qe : ℕ}
    (ht : 0 < t)
    (hqe : qe ≠ 0)
    (halign : (qe : ℝ) ≤ t * ge) :
    0 < ge :=
  gap_pos_of_positive_quotient ht hqe halign

/-- Rotating a list at the distinguished decomposition moves that entry to the
last position. -/
theorem rotate_decomposition_to_last
    {α : Type*}
    (pre post : List α) (x : α) :
    (pre ++ x :: post).rotate (pre.length + 1) =
      post ++ pre ++ [x] := by
  have hrewrite :
      pre ++ x :: post = (pre ++ [x]) ++ post := by
    simp [List.append_assoc]
  rw [hrewrite]
  have hlen : (pre ++ [x]).length = pre.length + 1 := by simp
  rw [← hlen, List.rotate_append_length_eq]
  simp [List.append_assoc]

/-- Simultaneous transition rotation of aligned quotient and geometric gap
lists. -/
theorem rotate_aligned_transition_to_last
    {t : ℝ}
    {pre post : List ℕ} {qe : ℕ}
    {gaps : List ℝ}
    (halign :
      QuotientGapAligned t (pre ++ qe :: post) gaps) :
    ∃ gpre gpost : List ℝ, ∃ ge : ℝ,
      gaps = gpre ++ ge :: gpost ∧
      (pre ++ qe :: post).rotate (pre.length + 1) =
        post ++ pre ++ [qe] ∧
      gaps.rotate (pre.length + 1) =
        gpost ++ gpre ++ [ge] ∧
      (qe : ℝ) ≤ t * ge ∧
      gpre.length = pre.length ∧
      gpost.length = post.length := by
  obtain ⟨gpre, gpost, ge, hgaps, hpre, hpost, hqe, _, _⟩ :=
    aligned_gap_decomposition halign
  refine ⟨gpre, gpost, ge, hgaps, ?_, ?_, hqe, hpre, hpost⟩
  · exact rotate_decomposition_to_last pre post qe
  · rw [hgaps, hpre]
    exact rotate_decomposition_to_last gpre gpost ge

#print axioms quotientGapAligned_length
#print axioms aligned_gap_decomposition
#print axioms aligned_transition_gap_pos
#print axioms rotate_decomposition_to_last
#print axioms rotate_aligned_transition_to_last

end JSP000404Research
