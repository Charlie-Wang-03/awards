import JSP000404Research.ResidualNetCollisionCertifiedDuplicateWitness
import Mathlib.Tactic

/-!
# Exact support identity for two distinct coordinate flips

Earlier double-flip rigidity showed that equal diagonal targets force
two source words to agree OUTSIDE four chosen flip coordinates. The
following sharpens containment to EXACTLY the symmetric difference of
two unordered 2-element coordinate sets, as long as each selected
forward/reverse pair has distinct coordinates (already proved for
actual NET cross-transport collisions).

This is a Boolean identity, not a new AngleCap hypothesis. It
reduces possible target collisions to the two/four bit Hamming cases;
the duplicate debt is not yet shown to vanish.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- At a fixed coordinate a genuine double flip toggles that bit
exactly when the coordinate belongs to its two-element flip support. -/
theorem distinct_two_flip_coordinate_eval
    {n : ℕ} (w : Fin n → Bool)
    (a b e : Fin n) (hab : a ≠ b) :
    flipCompletionWord a (flipCompletionWord b w) e =
      if e = a ∨ e = b then !(w e) else w e := by
  by_cases hea : e = a
  · subst e
    have hba : b ≠ a := hab.symm
    simp [flipCompletionWord, hab, hba]
  · by_cases heb : e = b
    · subst e
      have hba : b ≠ a := hab.symm
      simp [flipCompletionWord, hea, hab, hba]
    · simp [flipCompletionWord, hea, heb]

/-- At EVERY coordinate, equal double-flip targets make the two
source words disagree iff EXACTLY ONE of the two flip-pair supports
contains that coordinate. This is stronger than the previous
outside-four agreement criterion. -/
theorem two_flip_target_eq_source_diff_iff_pair_exclusive
    {n : ℕ} (w z : Fin n → Bool)
    (a b c d : Fin n)
    (hab : a ≠ b) (hcd : c ≠ d)
    (heq :
      flipCompletionWord a (flipCompletionWord b w) =
      flipCompletionWord c (flipCompletionWord d z))
    (e : Fin n) :
    (w e ≠ z e) ↔
      ((e = a ∨ e = b) ∧ ¬(e = c ∨ e = d)) ∨
      (¬(e = a ∨ e = b) ∧ (e = c ∨ e = d)) := by
  have h := congrArg (fun u : Fin n → Bool => u e) heq
  rw [distinct_two_flip_coordinate_eval w a b e hab,
      distinct_two_flip_coordinate_eval z c d e hcd] at h
  by_cases h1 : e = a ∨ e = b
  · by_cases h2 : e = c ∨ e = d
    · simp only [if_pos h1, if_pos h2] at h
      have hval : w e = z e := by
        cases hw : w e <;> cases hz : z e <;> simp_all
      simp [h1, h2, hval]
    · simp only [if_pos h1, if_neg h2] at h
      have hval : w e ≠ z e := by
        intro hsame
        rw [hsame] at h
        cases hz : z e <;> simp [hz] at h
      simp [h1, h2, hval]
  · by_cases h2 : e = c ∨ e = d
    · simp only [if_neg h1, if_pos h2] at h
      have hval : w e ≠ z e := by
        intro hsame
        rw [hsame] at h
        cases hz : z e <;> simp [hz] at h
      simp [h1, h2, hval]
    · simp only [if_neg h1, if_neg h2] at h
      simp [h1, h2, h]

/-- The set of all DIFFERING source coordinates is EXACTLY the
symmetric difference of the two unordered two-colour supports. -/
theorem two_flip_equal_target_exact_difference_set
    {n : ℕ} (w z : Fin n → Bool)
    (a b c d : Fin n)
    (hab : a ≠ b) (hcd : c ≠ d)
    (heq :
      flipCompletionWord a (flipCompletionWord b w) =
      flipCompletionWord c (flipCompletionWord d z)) :
    (Finset.univ.filter (fun e : Fin n => w e ≠ z e)) =
      (({a, b} : Finset (Fin n)) \ ({c, d} : Finset (Fin n))) ∪
      (({c, d} : Finset (Fin n)) \ ({a, b} : Finset (Fin n))) := by
  classical
  ext e
  rw [Finset.mem_filter, Finset.mem_union,
    Finset.mem_sdiff, Finset.mem_sdiff]
  simp only [Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  have hiff := two_flip_target_eq_source_diff_iff_pair_exclusive
    w z a b c d hab hcd heq e
  constructor
  · intro hw
    rcases hiff.mp hw with hleft | hright
    · exact Or.inl hleft
    · exact Or.inr ⟨hright.2, hright.1⟩
  · intro hw
    apply hiff.mpr
    rcases hw with hleft | hright
    · exact Or.inl hleft
    · exact Or.inr ⟨hright.2, hright.1⟩

/-- In particular, EQUAL diagonal targets from the SAME UNORDERED
flip support have EQUAL original source words, hence cannot
contribute positive multiplicity in the canonical diagonal image. -/
theorem two_flip_equal_target_same_support_source_eq
    {n : ℕ} (w z : Fin n → Bool)
    (a b c d : Fin n)
    (hab : a ≠ b) (hcd : c ≠ d)
    (heq :
      flipCompletionWord a (flipCompletionWord b w) =
      flipCompletionWord c (flipCompletionWord d z))
    (hsame : ({a, b} : Finset (Fin n)) = {c, d}) :
    w = z := by
  funext e
  by_contra hne
  have hiff :=
    two_flip_target_eq_source_diff_iff_pair_exclusive
      w z a b c d hab hcd heq e
  have hmem :
      (e = a ∨ e = b) ↔ (e = c ∨ e = d) := by
    have hh := congrArg (fun s : Finset (Fin n) => e ∈ s) hsame
    simpa [Finset.mem_insert, Finset.mem_singleton] using hh
  rcases hiff.mp hne with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h2 (hmem.mp h1)
  · exact h1 (hmem.mpr h2)

#print axioms distinct_two_flip_coordinate_eval
#print axioms two_flip_target_eq_source_diff_iff_pair_exclusive
#print axioms two_flip_equal_target_exact_difference_set
#print axioms two_flip_equal_target_same_support_source_eq

end OrderedEdgeColoring
end JSP000404Research
