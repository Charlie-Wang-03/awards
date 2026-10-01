import JSP000404Research.ThreeColourPaletteHelly
import Mathlib.Tactic

/-!
# Five-band envelope for pairwise-intersecting three-colour palettes

If four length-three integer intervals pairwise intersect, their starting
indices differ by at most two.  Hence the union of all four palettes is
contained in one block of five consecutive integer labels.
-/

namespace JSP000404Research

def fiveNatInterval (m : ℕ) : Finset ℕ :=
  {m,m+1,m+2,m+3,m+4}

theorem mem_fiveNatInterval_iff_bounds
    {m k : ℕ} :
    k ∈ fiveNatInterval m ↔
      m ≤ k ∧ k ≤ m + 4 := by
  unfold fiveNatInterval
  constructor
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> omega
  · rintro ⟨hlo,hhi⟩
    have hk :
        k = m ∨ k = m+1 ∨ k = m+2 ∨ k = m+3 ∨ k = m+4 := by
      omega
    simp [fiveNatInterval,hk]

theorem four_threeNatIntervals_pairwise_intersect_five_envelope
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
    ∃ m : ℕ,
      threeNatInterval a ⊆ fiveNatInterval m ∧
      threeNatInterval b ⊆ fiveNatInterval m ∧
      threeNatInterval c ⊆ fiveNatInterval m ∧
      threeNatInterval d ⊆ fiveNatInterval m := by
  let m := min (min a b) (min c d)
  have hmA : m ≤ a := by dsimp [m]; omega
  have hmB : m ≤ b := by dsimp [m]; omega
  have hmC : m ≤ c := by dsimp [m]; omega
  have hmD : m ≤ d := by dsimp [m]; omega

  have habB := pair_intersection_bounds_starts hab
  have hacB := pair_intersection_bounds_starts hac
  have hadB := pair_intersection_bounds_starts had
  have hbcB := pair_intersection_bounds_starts hbc
  have hbdB := pair_intersection_bounds_starts hbd
  have hcdB := pair_intersection_bounds_starts hcd

  have haHi : a ≤ m + 2 := by
    dsimp [m]
    omega
  have hbHi : b ≤ m + 2 := by
    dsimp [m]
    omega
  have hcHi : c ≤ m + 2 := by
    dsimp [m]
    omega
  have hdHi : d ≤ m + 2 := by
    dsimp [m]
    omega

  refine ⟨m,?_,?_,?_,?_⟩
  all_goals
    intro k hk
    rw [mem_threeNatInterval_iff_bounds] at hk
    rw [mem_fiveNatInterval_iff_bounds]
  · omega
  · omega
  · omega
  · omega

#print axioms four_threeNatIntervals_pairwise_intersect_five_envelope

end JSP000404Research
