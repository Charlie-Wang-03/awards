import JSP000404Research.SaturatedWrapDescent
import JSP000404Research.LinearBandGapCapacity
import Mathlib.Tactic

/-!
# Two-band rigidity from a zero-quotient unit crossing

A zero-quotient unit step is an adjacent pair x,y with

  floor(y) = floor(x)+1,
  floor(y-x) = 0.

If the whole local value list occupies only two natural floor bands, the
existence of such a step forces those two bands to be exactly consecutive:

  {m,m+1}.

This is the one-dimensional core of the top-bad six-point branch.
-/

namespace JSP000404Research

theorem hasZeroQuotientUnitStep_exists_floor_pair
    {a : ℝ} {xs : List ℝ}
    (hstep : HasZeroQuotientUnitStep a xs) :
    ∃ x y : ℝ,
      x ∈ a :: xs ∧
      y ∈ a :: xs ∧
      Nat.floor y = Nat.floor x + 1 ∧
      Nat.floor (y - x) = 0 := by
  induction xs generalizing a with
  | nil =>
      simp [HasZeroQuotientUnitStep] at hstep
  | cons b bs ih =>
      rw [hasZeroQuotientUnitStep_cons] at hstep
      rcases hstep with hhere | htail
      · exact ⟨a, b, by simp, by simp, hhere.1, hhere.2⟩
      · obtain ⟨x, y, hx, hy, hfloor, hgap⟩ :=
          ih (a := b) htail
        refine ⟨x, y, ?_, ?_, hfloor, hgap⟩
        · simpa only [List.mem_cons] using Or.inr hx
        · simpa only [List.mem_cons] using Or.inr hy

theorem occupiedNatBands_eq_adjacent_pair_of_card_two_zeroUnit
    {a : ℝ} {xs : List ℝ}
    (hcard : (occupiedNatBands (a :: xs)).card = 2)
    (hstep : HasZeroQuotientUnitStep a xs) :
    ∃ m : ℕ,
      occupiedNatBands (a :: xs) = {m, m + 1} := by
  classical
  obtain ⟨x, y, hx, hy, hfloor, _hgap⟩ :=
    hasZeroQuotientUnitStep_exists_floor_pair hstep
  let m := Nat.floor x
  have hm :
      m ∈ occupiedNatBands (a :: xs) := by
    unfold occupiedNatBands
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨x, hx, rfl⟩
  have hm1 :
      m + 1 ∈ occupiedNatBands (a :: xs) := by
    unfold occupiedNatBands
    rw [List.mem_toFinset, List.mem_map]
    refine ⟨y, hy, ?_⟩
    simpa [m] using hfloor
  have hsub :
      ({m, m + 1} : Finset ℕ) ⊆
        occupiedNatBands (a :: xs) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hm
    · exact hm1
  have hpairCard :
      ({m, m + 1} : Finset ℕ).card = 2 := by
    simp
  have heq :
      ({m, m + 1} : Finset ℕ) =
        occupiedNatBands (a :: xs) := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hcard, hpairCard]
  exact ⟨m, heq.symm⟩

#print axioms hasZeroQuotientUnitStep_exists_floor_pair
#print axioms occupiedNatBands_eq_adjacent_pair_of_card_two_zeroUnit

end JSP000404Research
