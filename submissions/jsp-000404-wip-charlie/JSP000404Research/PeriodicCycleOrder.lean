import JSP000404Research.MobiusReturnOrder
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# One lifted circuit and its reflected period pieces

A lifted circuit of winding `r` splits into `r` translated graph paths. After alternating
vertical reflection, their return permutation is `finRotate r`. If the graph paths are
pairwise disjoint, the reflected-strip theorem forces `r ≤ 2`.

The hypotheses describe the full lifted curve and its disjoint period pieces. Constructing
that curve and proving disjointness from a simple consecutive-wire cycle remains separate.
-/

namespace JSP000404Research

theorem winding_le_two_of_disjoint_period_pieces
    {r : ℕ} (hr : 0 < r) {start period : ℝ} (hperiod : 0 < period) (curve : ℝ → ℝ)
    (hcontinuous : ContinuousOn curve (Set.Icc start (start + (r : ℝ) * period)))
    (hboundary : curve (start + (r : ℝ) * period) = (-1 : ℝ) ^ r * curve start)
    (hdisjoint : ∀ i j : Fin r, i ≠ j → ∀ x ∈ Set.Ico start (start + period),
      (-1 : ℝ) ^ i.val * curve (x + (i.val : ℝ) * period) ≠
        (-1 : ℝ) ^ j.val * curve (x + (j.val : ℝ) * period)) : r ≤ 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hr)
  let path (i : Fin (m + 1)) (x : ℝ) :=
    (-1 : ℝ) ^ i.val * curve (x + (i.val : ℝ) * period)
  have hpaths (i : Fin (m + 1)) : ContinuousOn (path i) (Set.Icc start (start + period)) := by
    have hmaps : Set.MapsTo (fun x : ℝ ↦ x + (i.val : ℝ) * period)
        (Set.Icc start (start + period)) (Set.Icc start (start + ((m + 1 : ℕ) : ℝ) * period)) := by
      intro x hx
      have hi : i.val ≤ m := Nat.le_of_lt_succ i.isLt
      have hireal : (i.val : ℝ) ≤ m := by exact_mod_cast hi
      have hzero : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
      constructor <;> push_cast <;> nlinarith [hx.1, hx.2]
    exact continuous_const.continuousOn.mul
      (hcontinuous.comp (continuous_id.add continuous_const).continuousOn hmaps)
  have hreturn (i : Fin (m + 1)) : path i (start + period) = -path (finRotate (m + 1) i) start := by
    have htime : start + period + (i.val : ℝ) * period =
        start + ((i.val + 1 : ℕ) : ℝ) * period := by push_cast; ring
    by_cases hlast : i = Fin.last m
    · subst i
      rw [finRotate_last]
      dsimp only [path, Fin.val_last, Fin.val_zero]
      have hlasttime : start + period + (m : ℝ) * period =
          start + ((m + 1 : ℕ) : ℝ) * period := by push_cast; ring
      rw [hlasttime, hboundary]
      have hsquare : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by
        rw [← mul_pow]
        norm_num
      rw [pow_succ]
      simp only [pow_zero, Nat.cast_zero, zero_mul, add_zero, one_mul]
      linear_combination -(curve start) * hsquare
    · have hnext := coe_finRotate_of_ne_last hlast
      dsimp only [path]
      rw [hnext, htime, pow_succ]
      ring
  have hstart_injective : Function.Injective (fun i : Fin (m + 1) ↦ path i start) := by
    intro i j heq
    by_contra hne
    exact hdisjoint i j hne start ⟨le_rfl, by linarith⟩ heq
  have hclosed (i j : Fin (m + 1)) (hne : i ≠ j) (x : ℝ)
      (hx : x ∈ Set.Icc start (start + period)) : path i x ≠ path j x := by
    by_cases hend : x = start + period
    · subst x
      rw [hreturn, hreturn]
      exact fun heq ↦ hne ((finRotate (m + 1)).injective (hstart_injective (neg_injective heq)))
    · exact hdisjoint i j hne x ⟨hx.1, lt_of_le_of_ne hx.2 hend⟩
  let startOrder : LinearOrder (Fin (m + 1)) :=
    LinearOrder.lift' (fun i ↦ path i start) hstart_injective
  let := startOrder
  have hstart : @StrictMono (Fin (m + 1)) ℝ startOrder.toPreorder _
      (fun i ↦ path i start) := fun _ _ h ↦ h
  have horbit (j : Fin (m + 1)) : ∃ k : ℕ, (finRotate (m + 1))^[k] 0 = j := by
    refine ⟨j.val, ?_⟩
    have h := congrFun (finCycle_eq_finRotate_iterate (k := j)) 0
    simpa only [finCycle_apply, zero_add] using h.symm
  have hcard := @reflected_strip_single_orbit_card_le_two (Fin (m + 1)) startOrder _
    path (finRotate (m + 1)) start (start + period)
    (by linarith : start ≤ start + period) hpaths hclosed hstart hreturn 0 horbit
  simpa using hcard

#print axioms winding_le_two_of_disjoint_period_pieces

end JSP000404Research
