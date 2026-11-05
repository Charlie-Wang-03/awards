import JSP000404Research.CyclicGraphPotential
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Half-grid retiming from one- and two-turn simple cycles

For integral edge delays and windings, a strict schedule of period `(k + 1) / 2` admits an
integral doubled schedule of period `k / 2`, provided every nonempty simple cycle has winding
one or two. The theorem supplies the potential. The planar embedding and the transport of
the projection cut order remain explicit tasks outside this algebraic module.
-/

namespace JSP000404Research
namespace CyclicGraph

open Quiver

variable {V : Type*} [Quiver V]

theorem pathWeight_le_potential_difference
    {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]
    (weight : ∀ {u v : V}, (u ⟶ v) → R) (potential : V → R)
    (hedge : ∀ {u v : V} (e : u ⟶ v), weight e ≤ potential v - potential u)
    {u v : V} (p : Path u v) : pathWeight weight p ≤ potential v - potential u := by
  induction p with
  | nil => simp
  | cons p e ih =>
    have h := add_le_add ih (hedge e)
    convert h using 1 <;> simp [pathWeight_cons]

theorem pathWeight_lt_potential_difference
    {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]
    (weight : ∀ {u v : V}, (u ⟶ v) → R) (potential : V → R)
    (hedge : ∀ {u v : V} (e : u ⟶ v), weight e < potential v - potential u)
    {u v : V} (p : Path u v) (hpos : p.length ≠ 0) :
    pathWeight weight p < potential v - potential u := by
  cases p with
  | nil => exact (hpos rfl).elim
  | cons p e =>
    have hle := pathWeight_le_potential_difference weight potential (fun e ↦ (hedge e).le) p
    have h := add_lt_add_of_le_of_lt hle (hedge e)
    convert h using 1 <;> simp [pathWeight_cons]

private theorem pathWeight_int_combination
    (delay wrap : ∀ {u v : V}, (u ⟶ v) → ℤ) (k : ℤ) {u v : V} (p : Path u v) :
    pathWeight (fun e ↦ 2 * delay e - k * wrap e) p =
      2 * pathWeight delay p - k * pathWeight wrap p := by
  induction p with
  | nil => simp
  | cons p e ih => simp only [pathWeight_cons, ih]; ring

private theorem pathWeight_real_combination
    (delay wrap : ∀ {u v : V}, (u ⟶ v) → ℤ) (period : ℝ) {u v : V} (p : Path u v) :
    pathWeight (fun e ↦ (delay e : ℝ) - (wrap e : ℝ) * period) p =
      (pathWeight (R := ℤ) delay p : ℝ) - (pathWeight (R := ℤ) wrap p : ℝ) * period := by
  induction p with
  | nil => simp
  | cons p e ih => simp only [pathWeight_cons, ih, Int.cast_add]; ring

/-- Integral doubled event times exist one half-unit below a strict source period. -/
theorem exists_half_grid_retiming
    (delay wrap : ∀ {u v : V}, (u ⟶ v) → ℤ) (halfUnits : ℤ)
    (original : V → ℝ) (root : V)
    (hconnected : ∀ u v : V, Nonempty (Path u v))
    (hsource : ∀ {u v : V} (e : u ⟶ v),
      (delay e : ℝ) < original v - original u + (wrap e : ℝ) * ((halfUnits : ℝ) + 1) / 2)
    (hwinding : ∀ (v : V) (p : Path v v), p.vertices.dropLast.Nodup → p.length ≠ 0 →
      pathWeight wrap p = 1 ∨ pathWeight wrap p = 2) :
    ∃ doubledTime : V → ℤ, ∀ {u v : V} (e : u ⟶ v),
      2 * delay e ≤ doubledTime v - doubledTime u + halfUnits * wrap e := by
  let period : ℝ := ((halfUnits : ℝ) + 1) / 2
  have hstrict : ∀ {u v : V} (e : u ⟶ v),
      (delay e : ℝ) - (wrap e : ℝ) * period < original v - original u := by
    intro u v e
    have h := hsource e
    dsimp [period]
    linarith
  have hsimple (v : V) (p : Path v v) (hsimple : p.vertices.dropLast.Nodup) :
      pathWeight (fun e ↦ 2 * delay e - halfUnits * wrap e) p ≤ 0 := by
    by_cases hzero : p.length = 0
    · have hp := p.eq_nil_of_length_zero hzero
      simp [hp]
    have hlt := pathWeight_lt_potential_difference
      (fun e ↦ (delay e : ℝ) - (wrap e : ℝ) * period) original hstrict p hzero
    rw [pathWeight_real_combination, sub_self] at hlt
    rw [pathWeight_int_combination]
    rcases hwinding v p hsimple hzero with hw | hw
    · rw [hw] at hlt ⊢
      have hint : 2 * pathWeight delay p < halfUnits + 1 := by
        exact_mod_cast (show (2 : ℝ) * (pathWeight (R := ℤ) delay p : ℝ) < (halfUnits : ℝ) + 1 by
          dsimp [period] at hlt
          norm_num at hlt
          linarith)
      omega
    · rw [hw] at hlt ⊢
      have hint : pathWeight delay p < halfUnits + 1 := by
        exact_mod_cast (show (pathWeight (R := ℤ) delay p : ℝ) < (halfUnits : ℝ) + 1 by
          dsimp [period] at hlt
          norm_num at hlt
          linarith)
      omega
  obtain ⟨potential, hpotential⟩ := exists_potential_of_simple_closed_nonpos
    (fun e ↦ 2 * delay e - halfUnits * wrap e) root hconnected hsimple
  refine ⟨potential, fun e ↦ ?_⟩
  exact sub_le_iff_le_add.mp (hpotential e)

#print axioms pathWeight_le_potential_difference
#print axioms pathWeight_lt_potential_difference
#print axioms exists_half_grid_retiming

end CyclicGraph
end JSP000404Research
