import JSP000404Research.OverweightTightLocalBand
import Mathlib.Tactic

/-!
# Rigidity of a saturated cyclic unit-band budget

Pointwise cyclic real-gap quotients are bounded by the corresponding
integer-band jumps. Equality of the total Sendov floor-excess forces
pointwise equality of the excesses; in particular every band jump >= 2
must equal the actual natural floor of its real angular gap.

Consequently a hypothetical overweight direction configuration possesses
a centre where *all* large cyclic band jumps are exactly floor-aligned.
This strengthens the necessary local-saturation obstruction without
asserting the still-unproved exclusion of such centres.
-/

namespace JSP000404Research

/-- Equality of total Sendov excess under componentwise domination
forces equality at every coordinate where the upper jump is at least two. -/
theorem forall₂_large_eq_of_le_and_listExponent_eq
    {qs bs : List ℕ}
    (h : List.Forall₂ (· ≤ ·) qs bs)
    (heq : listExponent qs = listExponent bs) :
    List.Forall₂ (fun q b => 2 ≤ b → q = b) qs bs := by
  induction h with
  | nil =>
      exact List.Forall₂.nil
  | @cons q b qs bs hqb hrest ih =>
      have hqEx : excess q ≤ excess b := by
        unfold excess
        omega
      have htailLe : listExponent qs ≤ listExponent bs :=
        listExponent_le_of_forall₂_le hrest
      have heq' :
          excess q + listExponent qs =
            excess b + listExponent bs := by
        simpa [listExponent, List.map_cons, List.sum_cons] using heq
      have hqExEq : excess q = excess b := by
        omega
      have htailEq : listExponent qs = listExponent bs := by
        omega
      apply List.Forall₂.cons
      · intro hb
        unfold excess at hqExEq
        omega
      · exact ih htailEq

namespace DirectionData
namespace LocalDirectionCycle

/-- At a locally saturated centre, every integer-band jump >= 2 is
exactly realized by the floored physical cyclic angular gap. -/
theorem large_band_jumps_floor_exact_of_local_tight
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    {D : DirectionData V t} {i : V}
    (C : LocalDirectionCycle D i)
    (ht : t < (n : ℝ) + 1)
    (htight :
      C.exponent + (D.incidentBands (n + 1) i).card = n + 1) :
    List.Forall₂ (fun q b => 2 ≤ b → q = b)
      ((cyclicRealGapsAt t C.values).map Nat.floor)
      (cyclicBandJumps n (C.values.map Nat.floor)) := by
  obtain ⟨a, xs, hvalues⟩ :
      ∃ a xs, C.values = a :: xs := by
    cases h : C.values with
    | nil => exact False.elim (C.values_nonempty h)
    | cons a xs => exact ⟨a, xs, rfl⟩
  have hsorted :
      (a :: xs).Pairwise (· ≤ ·) := by
    simpa [hvalues] using C.values_pairwise
  have hallt :
      ∀ x ∈ a :: xs, x < t := by
    intro x hx
    exact (C.value_mem_bounds
      (by simpa [hvalues] using hx)).2
  have ha0 : 0 ≤ a :=
    (C.value_mem_bounds (by simp [hvalues])).1
  have hcomp :
      List.Forall₂ (· ≤ ·)
        ((cyclicRealGapsAt t C.values).map Nat.floor)
        (cyclicBandJumps n (C.values.map Nat.floor)) := by
    simpa only [hvalues] using
      (cyclicFloorGaps_le_cyclicBandJumps
        a xs n ha0 hsorted hallt ht)
  have hnotStrict :
      ¬ (listExponent
          ((cyclicRealGapsAt t C.values).map Nat.floor) <
        listExponent
          (cyclicBandJumps n (C.values.map Nat.floor))) := by
    intro hs
    have hbudget :=
      C.exponent_add_incidentBands_card_le_n_of_strict
        ht hs
    omega
  have hle := listExponent_le_of_forall₂_le hcomp
  have heq :
      listExponent
        ((cyclicRealGapsAt t C.values).map Nat.floor) =
      listExponent
        (cyclicBandJumps n (C.values.map Nat.floor)) := by
    omega
  exact forall₂_large_eq_of_le_and_listExponent_eq hcomp heq

end LocalDirectionCycle

/-- Any hypothetical overweight direction configuration has at least
one centre at which all large band jumps are floor-exact. -/
theorem overweight_exists_large_band_jump_rigid_centre
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    (hover : 2 ^ n < ∑ i : V, 2 ^ (cycles i).exponent) :
    ∃ i : V,
      List.Forall₂ (fun q b => 2 ≤ b → q = b)
        ((cyclicRealGapsAt t (cycles i).values).map Nat.floor)
        (cyclicBandJumps n ((cycles i).values.map Nat.floor)) := by
  obtain ⟨i, htight⟩ :=
    overweight_exists_tight_local_band_centre
      D ht cycles hover
  exact ⟨i,
    (cycles i).large_band_jumps_floor_exact_of_local_tight ht htight⟩

#print axioms forall₂_large_eq_of_le_and_listExponent_eq
#print axioms LocalDirectionCycle.large_band_jumps_floor_exact_of_local_tight
#print axioms overweight_exists_large_band_jump_rigid_centre

end DirectionData
end JSP000404Research
