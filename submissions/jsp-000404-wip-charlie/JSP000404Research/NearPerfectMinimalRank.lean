import JSP000404Research.NearPerfectRefinedHardMatching
import Mathlib.Tactic

/-!
# Minimal-rank form of the near-perfect contradiction

The global rank-descent criterion can be weakened substantially.

Choose a hard word x0 of minimal natural-number rank.  Exact-one overweight
gives a bijection from all hard words except x0 onto the complete refined
credit space.  Therefore every refined credit has an occupant distinct from
x0.

To contradict exact-one overweight it is enough to construct one refined
credit for x0 whose occupant has strictly smaller rank.  No global choice of a
credit for every hard word is required.

This is the form best suited to the current local-outlet analysis.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Every nonempty finite hard-word set has a rank-minimizing member. -/
theorem exists_minRank_hardProjectionWord
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (rank : (Fin n → Bool) → ℕ)
    (hne : (hardProjectionWords C exponent).Nonempty) :
    ∃ x0 : HardProjectionWord C exponent,
      ∀ x : HardProjectionWord C exponent,
        rank x0.1 ≤ rank x.1 := by
  classical
  let rset : Finset ℕ :=
    (hardProjectionWords C exponent).image rank
  have hrne : rset.Nonempty := by
    obtain ⟨x,hx⟩ := hne
    exact ⟨rank x, Finset.mem_image.mpr ⟨x,hx,rfl⟩⟩
  let m : ℕ := rset.min' hrne
  have hm : m ∈ rset :=
    Finset.min'_mem rset hrne
  obtain ⟨x0,hx0,hrank⟩ := Finset.mem_image.mp hm
  let X0 : HardProjectionWord C exponent := ⟨x0,hx0⟩
  refine ⟨X0, ?_⟩
  intro x
  have hxRank : rank x.1 ∈ rset := by
    exact Finset.mem_image.mpr ⟨x.1,x.2,rfl⟩
  have hmin := Finset.min'_le rset (rank x.1) hxRank
  simpa [X0,m,hrank] using hmin


/-- Exact-one overweight automatically makes the hard-word set nonempty. -/
theorem hardProjectionWords_nonempty_of_target_eq_bound_add_one
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (htarget :
      (∑ v, 2 ^ exponent v) = 2 ^ n + 1) :
    (hardProjectionWords C exponent).Nonempty := by
  have hcard :=
    hardProjectionWords_card_eq_holes_add_remainingSurplus_add_one
      C exponent hexp honeLoss htarget
  apply Finset.card_pos.mp
  omega

/-- Exact-one overweight therefore has a rank-minimal hard word for every
natural-valued rank. -/
theorem exists_minRank_hardProjectionWord_of_target_eq_bound_add_one
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (htarget :
      (∑ v, 2 ^ exponent v) = 2 ^ n + 1)
    (rank : (Fin n → Bool) → ℕ) :
    ∃ x0 : HardProjectionWord C exponent,
      ∀ x : HardProjectionWord C exponent,
        rank x0.1 ≤ rank x.1 := by
  exact exists_minRank_hardProjectionWord
    C exponent rank
    (hardProjectionWords_nonempty_of_target_eq_bound_add_one
      C exponent hexp honeLoss htarget)

/-- Minimal-rank near-perfect contradiction.

After deleting a rank-minimal hard word x0, any refined credit is occupied by
another hard word.  If one such occupant has smaller rank, contradiction. -/
theorem false_of_minRank_nearPerfect_credit_descent
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (htarget :
      (∑ v, 2 ^ exponent v) = 2 ^ n + 1)
    (rank : (Fin n → Bool) → ℕ)
    (x0 : HardProjectionWord C exponent)
    (hmin :
      ∀ x : HardProjectionWord C exponent,
        rank x0.1 ≤ rank x.1)
    (credit : ProjectionHoleOrRemainingSurplus C exponent)
    (hdesc :
      rank
        ((hardExcept_equiv_refinedTarget_of_target_eq_bound_add_one
          C exponent hexp honeLoss htarget x0).symm credit).1
        < rank x0.1) :
    False := by
  let e :=
    hardExcept_equiv_refinedTarget_of_target_eq_bound_add_one
      C exponent hexp honeLoss htarget x0
  let y : HardProjectionWord C exponent :=
    ⟨(e.symm credit).1,
      (Finset.mem_erase.mp (e.symm credit).2).2⟩
  have hle : rank x0.1 ≤ rank y.1 := hmin y
  have hlt : rank y.1 < rank x0.1 := by
    simpa [e,y] using hdesc
  exact (not_lt_of_ge hle) hlt

/-- Combined existential form: it is enough to choose a minimal hard word and
produce one descending refined credit for that word. -/
theorem false_of_exists_minRank_descending_credit
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (htarget :
      (∑ v, 2 ^ exponent v) = 2 ^ n + 1)
    (rank : (Fin n → Bool) → ℕ)
    (hcredit :
      ∀ x0 : HardProjectionWord C exponent,
        (∀ x : HardProjectionWord C exponent,
          rank x0.1 ≤ rank x.1) →
        ∃ credit : ProjectionHoleOrRemainingSurplus C exponent,
          rank
            ((hardExcept_equiv_refinedTarget_of_target_eq_bound_add_one
              C exponent hexp honeLoss htarget x0).symm credit).1
            < rank x0.1) :
    False := by
  obtain ⟨x0,hmin⟩ :=
    exists_minRank_hardProjectionWord_of_target_eq_bound_add_one
      C exponent hexp honeLoss htarget rank
  obtain ⟨credit,hdesc⟩ := hcredit x0 hmin
  exact false_of_minRank_nearPerfect_credit_descent
    C exponent hexp honeLoss htarget rank x0 hmin credit hdesc

#print axioms exists_minRank_hardProjectionWord
#print axioms hardProjectionWords_nonempty_of_target_eq_bound_add_one
#print axioms exists_minRank_hardProjectionWord_of_target_eq_bound_add_one
#print axioms false_of_minRank_nearPerfect_credit_descent
#print axioms false_of_exists_minRank_descending_credit

end OrderedEdgeColoring
end JSP000404Research
