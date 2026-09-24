
import JSP000404Research.LinearBandSaturation
import Mathlib.Tactic

/-!
# Head-step rigidity under saturated interior band capacity

For a sorted list a::b::bs, suppose the interior estimate is saturated:

  interiorExponent(a::b::bs) + occupiedBands(a::b::bs)
    = floor(last)-floor(a)+1.

The proof of LinearBandGapCapacity is inductive.  Saturation therefore
propagates to the tail b::bs and forces equality in the local head-step
inequality.

* If floor(a)=floor(b), then floor(b-a)=0 and the head contributes no slack.
* If floor(a)<floor(b), then

    excess(floor(b-a))+1 = floor(b)-floor(a).

In particular a floor-band jump of at least two forces the exact gap quotient

    floor(b-a) = floor(b)-floor(a).

Iterating this theorem exposes the complete local equality structure of a
saturated endpoint.
-/

namespace JSP000404Research

open Real

theorem interior_saturation_head_step
    (a b : ℝ) (bs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: b :: bs).Pairwise (· ≤ ·))
    (hsat :
      listExponent
          ((successiveDiffsFrom a (b :: bs)).map Nat.floor) +
        (occupiedNatBands (a :: b :: bs)).card
      =
      Nat.floor (bs.getLastD b) - Nat.floor a + 1) :
    let tailSat :=
      listExponent
          ((successiveDiffsFrom b bs).map Nat.floor) +
        (occupiedNatBands (b :: bs)).card
      =
      Nat.floor (bs.getLastD b) - Nat.floor b + 1
    tailSat ∧
      (
        (Nat.floor a = Nat.floor b ∧
          Nat.floor (b - a) = 0)
        ∨
        (Nat.floor a < Nat.floor b ∧
          excess (Nat.floor (b - a)) + 1 =
            Nat.floor b - Nat.floor a)
      ) := by
  dsimp
  have hpair := List.pairwise_cons.mp hsorted
  have hab : a ≤ b := hpair.1 b (by simp)
  have hb0 : 0 ≤ b := ha0.trans hab
  have htail :
      (b :: bs).Pairwise (· ≤ ·) :=
    hpair.2
  have htailBound :=
    interior_gapExponent_add_occupied_le_span
      b bs hb0 htail
  have hAB :
      Nat.floor a ≤ Nat.floor b :=
    Nat.floor_mono hab
  by_cases hEq :
      Nat.floor a = Nat.floor b
  · have hq0 :
        Nat.floor (b - a) = 0 :=
      natFloor_sub_eq_zero_of_floor_eq
        ha0 hab hEq
    have hbands :
        occupiedNatBands (a :: b :: bs) =
          occupiedNatBands (b :: bs) := by
      simp [occupiedNatBands, hEq]
    have hsatTail :
        listExponent
            ((successiveDiffsFrom b bs).map Nat.floor) +
          (occupiedNatBands (b :: bs)).card
        =
        Nat.floor (bs.getLastD b) - Nat.floor b + 1 := by
      simp only [successiveDiffsFrom, List.map_cons,
        listExponent, List.map_cons, List.sum_cons] at hsat
      rw [hbands, hq0] at hsat
      simp [excess, hEq] at hsat
      exact hsat
    exact ⟨hsatTail, Or.inl ⟨hEq, hq0⟩⟩
  · have hLt :
        Nat.floor a < Nat.floor b := by
      omega
    have hnotmem :
        Nat.floor a ∉ occupiedNatBands (b :: bs) := by
      intro hmem
      rw [occupiedNatBands, List.mem_toFinset,
          List.mem_map] at hmem
      obtain ⟨x, hx, hxFloor⟩ := hmem
      have hBx :
          Nat.floor b ≤ Nat.floor x :=
        head_floor_le_of_mem_sorted htail hx
      rw [← hxFloor] at hBx
      omega
    have hbands :
        (occupiedNatBands (a :: b :: bs)).card =
          (occupiedNatBands (b :: bs)).card + 1 := by
      rw [occupiedNatBands_cons,
          Finset.card_insert_of_not_mem hnotmem]
    have hstep :
        excess (Nat.floor (b - a)) + 1 ≤
          Nat.floor b - Nat.floor a :=
      excess_natFloor_sub_add_one_le_floor_sub_of_floor_lt
        ha0 hab hLt
    have hsatExpanded :
        excess (Nat.floor (b - a)) +
          listExponent
            ((successiveDiffsFrom b bs).map Nat.floor) +
          ((occupiedNatBands (b :: bs)).card + 1)
        =
        Nat.floor (bs.getLastD b) - Nat.floor a + 1 := by
      simpa [successiveDiffsFrom, listExponent,
        hbands, add_assoc, add_left_comm, add_comm] using hsat
    have hstepEq :
        excess (Nat.floor (b - a)) + 1 =
          Nat.floor b - Nat.floor a := by
      omega
    have htailEq :
        listExponent
            ((successiveDiffsFrom b bs).map Nat.floor) +
          (occupiedNatBands (b :: bs)).card
        =
        Nat.floor (bs.getLastD b) - Nat.floor b + 1 := by
      omega
    exact ⟨htailEq, Or.inr ⟨hLt, hstepEq⟩⟩

/-- At a saturated head step, a jump across at least two integer bands has
gap quotient exactly equal to the integer band jump. -/
theorem interior_saturation_head_large_jump_quotient_eq
    (a b : ℝ) (bs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: b :: bs).Pairwise (· ≤ ·))
    (hsat :
      listExponent
          ((successiveDiffsFrom a (b :: bs)).map Nat.floor) +
        (occupiedNatBands (a :: b :: bs)).card
      =
      Nat.floor (bs.getLastD b) - Nat.floor a + 1)
    (hjump :
      2 ≤ Nat.floor b - Nat.floor a) :
    Nat.floor (b - a) =
      Nat.floor b - Nat.floor a := by
  have hrig :=
    interior_saturation_head_step
      a b bs ha0 hsorted hsat
  rcases hrig.2 with hsame | hstrict
  · rw [hsame.1] at hjump
    simp at hjump
  · have hqPos :
        1 ≤ Nat.floor (b - a) := by
      by_contra hnot
      have hq0 : Nat.floor (b - a) = 0 := by omega
      rw [hq0] at hstrict
      simp [excess] at hstrict
      omega
    unfold excess at hstrict
    omega

#print axioms interior_saturation_head_step
#print axioms interior_saturation_head_large_jump_quotient_eq

end JSP000404Research
