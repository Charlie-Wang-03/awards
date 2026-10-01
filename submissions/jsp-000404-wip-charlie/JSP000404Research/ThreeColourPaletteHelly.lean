import Mathlib.Tactic

/-!
# Helly lemma for three-consecutive-integer palettes

Four palettes of the form {m,m+1,m+2} that pairwise intersect have a common
integer.  This is the discrete interval fact needed by the exact-two Q/T/T/T
palette terminal.
-/

namespace JSP000404Research

def threeNatInterval (m : ℕ) : Finset ℕ :=
  {m,m+1,m+2}

theorem mem_threeNatInterval_iff_bounds
    {m k : ℕ} :
    k ∈ threeNatInterval m ↔
      m ≤ k ∧ k ≤ m + 2 := by
  unfold threeNatInterval
  constructor
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl <;> omega
  · rintro ⟨hlo,hhi⟩
    have hk : k = m ∨ k = m + 1 ∨ k = m + 2 := by
      omega
    simp [threeNatInterval,hk]

theorem pair_intersection_bounds_starts
    {m n : ℕ}
    (h :
      (threeNatInterval m ∩ threeNatInterval n).Nonempty) :
    m ≤ n + 2 ∧ n ≤ m + 2 := by
  obtain ⟨k,hkm,hkn⟩ := h
  have hm := (mem_threeNatInterval_iff_bounds.mp hkm)
  have hn := (mem_threeNatInterval_iff_bounds.mp hkn)
  omega

theorem four_threeNatIntervals_pairwise_intersect_common
    {a b c d : ℕ}
    (hab :
      (threeNatInterval a ∩ threeNatInterval b).Nonempty)
    (hac :
      (threeNatInterval a ∩ threeNatInterval c).Nonempty)
    (had :
      (threeNatInterval a ∩ threeNatInterval d).Nonempty)
    (hbc :
      (threeNatInterval b ∩ threeNatInterval c).Nonempty)
    (hbd :
      (threeNatInterval b ∩ threeNatInterval d).Nonempty)
    (hcd :
      (threeNatInterval c ∩ threeNatInterval d).Nonempty) :
    ∃ k : ℕ,
      k ∈ threeNatInterval a ∧
      k ∈ threeNatInterval b ∧
      k ∈ threeNatInterval c ∧
      k ∈ threeNatInterval d := by
  let M := max (max a b) (max c d)
  have haM : a ≤ M := by
    dsimp [M]
    omega
  have hbM : b ≤ M := by
    dsimp [M]
    omega
  have hcM : c ≤ M := by
    dsimp [M]
    omega
  have hdM : d ≤ M := by
    dsimp [M]
    omega

  have habB := pair_intersection_bounds_starts hab
  have hacB := pair_intersection_bounds_starts hac
  have hadB := pair_intersection_bounds_starts had
  have hbcB := pair_intersection_bounds_starts hbc
  have hbdB := pair_intersection_bounds_starts hbd
  have hcdB := pair_intersection_bounds_starts hcd

  have haHi : M ≤ a + 2 := by
    dsimp [M]
    omega
  have hbHi : M ≤ b + 2 := by
    dsimp [M]
    omega
  have hcHi : M ≤ c + 2 := by
    dsimp [M]
    omega
  have hdHi : M ≤ d + 2 := by
    dsimp [M]
    omega

  refine ⟨M,?_,?_,?_,?_⟩
  · exact mem_threeNatInterval_iff_bounds.mpr ⟨haM,haHi⟩
  · exact mem_threeNatInterval_iff_bounds.mpr ⟨hbM,hbHi⟩
  · exact mem_threeNatInterval_iff_bounds.mpr ⟨hcM,hcHi⟩
  · exact mem_threeNatInterval_iff_bounds.mpr ⟨hdM,hdHi⟩

#print axioms four_threeNatIntervals_pairwise_intersect_common

end JSP000404Research
