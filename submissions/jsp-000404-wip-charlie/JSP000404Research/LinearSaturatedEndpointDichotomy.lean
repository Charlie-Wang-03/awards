import JSP000404Research.SaturatedWrapDescent
import JSP000404Research.LinearBandGapEquality
import JSP000404Research.LinearBandGapStepTight
import Mathlib.Tactic

/-!
# Pure one-dimensional dichotomy for a saturated top-band endpoint

Let

  0 <= a <= ... <= z < t = n + delta,

and suppose the local cyclic floor-gap exponent plus the number of occupied
unit bands saturates the full n+1 band bound.

If the top band n occurs, sortedness forces floor(z)=n.  Equality then gives

* stepwise interior tightness;
* wrap excess = floor(a).

In the lower branch delta<1/2, either floor(a)=0 or the saturated-wrap descent
forces an actual zero-quotient step crossing one unit-band boundary.

This is the projection-independent arithmetic core of
ProjectionSaturatedEndpointDichotomy and is suitable for arbitrary projective
cuts.
-/

namespace JSP000404Research

/-- In a sorted nonempty value list bounded by t<n+1, occurrence of floor n
forces the final floor to be exactly n. -/
theorem sorted_last_floor_eq_top_of_top_mem
    {t : ℝ} {n : ℕ}
    (a : ℝ) (xs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall : ∀ x ∈ a :: xs, x < t)
    (htop : t < (n : ℝ) + 1)
    (hmem :
      ∃ x ∈ a :: xs, Nat.floor x = n) :
    Nat.floor (xs.getLastD a) = n := by
  obtain ⟨x, hx, hxfloor⟩ := hmem
  have hxle :
      x ≤ xs.getLastD a := by
    induction xs generalizing a with
    | nil =>
        simp at hx
        subst x
        simp
    | cons b bs ih =>
        have hp := List.pairwise_cons.mp hsorted
        simp only [List.mem_cons] at hx
        rcases hx with hxa | hxtail
        · subst x
          exact head_le_getLastD_of_pairwise a (b :: bs) hsorted
        · have htail :
              (b :: bs).Pairwise (· ≤ ·) := hp.2
          have hle :
              x ≤ bs.getLastD b := ih b htail hxtail
          simpa [List.getLastD_cons] using hle
  have hlast0 :
      0 ≤ xs.getLastD a :=
    ha0.trans
      (head_le_getLastD_of_pairwise a xs hsorted)
  have hlower :
      n ≤ Nat.floor (xs.getLastD a) := by
    rw [← hxfloor]
    exact Nat.floor_mono hxle
  have hlastLt :
      xs.getLastD a < t :=
    hall _ (List.getLastD_mem_cons a xs)
  have hlastTop :
      Nat.floor (xs.getLastD a) < n + 1 := by
    apply (Nat.floor_lt hlast0).2
    have hreal :
        xs.getLastD a < ((n + 1 : ℕ) : ℝ) := by
      push_cast
      exact hlastLt.trans htop
    exact hreal
  omega

/-- Main projection-independent saturated endpoint dichotomy. -/
theorem saturated_topBand_zeroFirst_or_zeroUnitStep
    {t delta : ℝ} {n : ℕ}
    (a : ℝ) (xs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall : ∀ x ∈ a :: xs, x < t)
    (ht : t = (n : ℝ) + delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (heq :
      listExponent
          (linearCyclicGapQuotients t (a :: xs)) +
        (occupiedNatBands (a :: xs)).card
        =
      n + 1)
    (htopMem :
      ∃ x ∈ a :: xs, Nat.floor x = n) :
    Nat.floor a = 0 ∨
      HasZeroQuotientUnitStep a xs := by
  have htTop :
      t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  have hlast :
      Nat.floor (xs.getLastD a) = n :=
    sorted_last_floor_eq_top_of_top_mem
      a xs ha0 hsorted hall htTop htopMem
  have htight :
      InteriorBandGapTight a xs :=
    linear_cyclic_gapEquality_implies_stepwise_tight
      a xs ha0 hsorted hall htTop heq
  have hwrap :
      excess (Nat.floor (a + t - xs.getLastD a)) =
        Nat.floor a :=
    wrap_gap_excess_eq_floor_head_of_global_equality_top_last
      a xs ha0 hsorted hall htTop heq hlast
  by_cases hzero : Nat.floor a = 0
  · exact Or.inl hzero
  · right
    have hpos : 1 ≤ Nat.floor a := by omega
    exact saturated_wrap_positive_first_has_zeroUnitStep
      xs ha0 hsorted hall ht hlast hwrap
      hpos hdeltaHalf htight

/-- Strong boundary-free form: any saturated equality case either occupies
both cyclic boundary bands 0 and n, or contains a zero-quotient unit-band
crossing.  No prior assumption that either boundary band is occupied is
needed. -/
theorem saturated_boundaryBands_or_zeroUnitStep
    {t delta : ℝ} {n : ℕ}
    (a : ℝ) (xs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall : ∀ x ∈ a :: xs, x < t)
    (ht : t = (n : ℝ) + delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (heq :
      listExponent
          (linearCyclicGapQuotients t (a :: xs)) +
        (occupiedNatBands (a :: xs)).card
        =
      n + 1) :
    (Nat.floor a = 0 ∧
      Nat.floor (xs.getLastD a) = n)
      ∨
    HasZeroQuotientUnitStep a xs := by
  have htTop :
      t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  have haz :
      a ≤ xs.getLastD a :=
    head_le_getLastD_of_pairwise a xs hsorted
  have hz0 :
      0 ≤ xs.getLastD a := ha0.trans haz
  have hzlt :
      xs.getLastD a < t :=
    hall _ (List.getLastD_mem_cons a xs)
  have hfloorAZ :
      Nat.floor a ≤ Nat.floor (xs.getLastD a) :=
    Nat.floor_mono haz
  have hlastN :
      Nat.floor (xs.getLastD a) ≤ n := by
    have hlt :
        xs.getLastD a < ((n + 1 : ℕ) : ℝ) := by
      push_cast
      exact hzlt.trans htTop
    have hf :
        Nat.floor (xs.getLastD a) < n + 1 :=
      (Nat.floor_lt hz0).2 hlt
    omega
  have htight :
      InteriorBandGapTight a xs :=
    linear_cyclic_gapEquality_implies_stepwise_tight
      a xs ha0 hsorted hall htTop heq
  have hwrap :
      excess (Nat.floor (a + t - xs.getLastD a))
        =
      n - Nat.floor (xs.getLastD a) + Nat.floor a :=
    wrap_gap_excess_eq_outer_empty_of_global_equality
      a xs ha0 hsorted hall htTop heq
  by_cases hboundary :
      Nat.floor a = 0 ∧
        Nat.floor (xs.getLastD a) = n
  · exact Or.inl hboundary
  · right
    let E : ℕ :=
      n - Nat.floor (xs.getLastD a) + Nat.floor a
    have hEpos : 1 ≤ E := by
      dsimp [E]
      by_cases haFloor : Nat.floor a = 0
      · have hlastNe :
            Nat.floor (xs.getLastD a) ≠ n := by
          intro hlast
          exact hboundary ⟨haFloor, hlast⟩
        have hlastLt :
            Nat.floor (xs.getLastD a) < n := by
          omega
        omega
      · have haPos : 1 ≤ Nat.floor a := by omega
        omega
    have hq :
        Nat.floor (a + t - xs.getLastD a) = E + 1 := by
      apply floor_wrap_eq_first_add_one_of_positive_excess
        hEpos
      simpa [E] using hwrap
    have hgap0 :
        0 ≤ a + t - xs.getLastD a := by
      linarith
    have hfloorGap :
        ((Nat.floor (a + t - xs.getLastD a) : ℕ) : ℝ)
          ≤
        a + t - xs.getLastD a :=
      Nat.floor_le hgap0
    have hEcast :
        (E : ℝ) =
          (n : ℝ) -
            (Nat.floor (xs.getLastD a) : ℝ) +
            (Nat.floor a : ℝ) := by
      dsimp [E]
      rw [Nat.cast_add, Nat.cast_sub hlastN]
      push_cast
      ring
    have hqcast :
        ((Nat.floor (a + t - xs.getLastD a) : ℕ) : ℝ)
          =
        (E : ℝ) + 1 := by
      exact_mod_cast hq
    rw [hqcast, hEcast, ht] at hfloorGap
    have hdrop :
        floorRemainder (xs.getLastD a) <
          floorRemainder a := by
      unfold floorRemainder
      linarith
    exact hasZeroQuotientUnitStep_of_fractional_drop
      a xs ha0 hsorted htight hdrop

/-- Symmetric corollary: if saturation sees the top band but not band zero,
a zero-quotient unit-band crossing is forced. -/
theorem saturated_topBand_forces_zeroUnitStep_of_first_positive
    {t delta : ℝ} {n : ℕ}
    (a : ℝ) (xs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall : ∀ x ∈ a :: xs, x < t)
    (ht : t = (n : ℝ) + delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (heq :
      listExponent
          (linearCyclicGapQuotients t (a :: xs)) +
        (occupiedNatBands (a :: xs)).card
        =
      n + 1)
    (htopMem :
      ∃ x ∈ a :: xs, Nat.floor x = n)
    (hfirstPos : 1 ≤ Nat.floor a) :
    HasZeroQuotientUnitStep a xs := by
  rcases saturated_topBand_zeroFirst_or_zeroUnitStep
      a xs ha0 hsorted hall ht hdeltaHalf heq htopMem
    with hzero | hstep
  · omega
  · exact hstep

#print axioms sorted_last_floor_eq_top_of_top_mem
#print axioms saturated_topBand_zeroFirst_or_zeroUnitStep
#print axioms saturated_topBand_forces_zeroUnitStep_of_first_positive

end JSP000404Research
