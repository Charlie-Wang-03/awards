import JSP000404Research.ExactProjectedLossIffTightInactive
import JSP000404Research.ResidualLossTranslatedConflict
import Mathlib.Tactic

/-!
# Universal one-layer profile bounds for genuine DirectionData cycles

A LocalDirectionCycle is nonempty, hence every centre uses at least one
integer band in the full (n+1)-colour palette. Its local full-band
budget then forces its exponent at most n. The same budget, together
with the exact standard residual colouring/activity identification,
gives the one-layer palette profile bound

  card (active B i) <= n - exponent i + 1.

These are derived rather than assumed, for arbitrary t<n+1 and for
all centres simultaneously. Consequently the established global
translated-loss collision theorems can be invoked on any such direction
family without an extra lower-branch fractional-width restriction.

No global Boolean injection or JSP-000404 capacity bound follows
solely from these one-layer inequalities.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

/-- The full (n+1)-band activity at a centre is nonempty, because
its complete local direction cycle contains an actual ray. -/
theorem incidentBands_succ_nonempty_of_localCycle
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (i : V)
    (C : LocalDirectionCycle D i) :
    (D.incidentBands (n + 1) i).Nonempty := by
  classical
  obtain ⟨a, tail, hrays⟩ :
      ∃ a tail, C.rays = a :: tail := by
    cases h : C.rays with
    | nil =>
        exact False.elim (C.nonempty h)
    | cons a tail =>
        exact ⟨a, tail, rfl⟩
  have ha0 : 0 ≤ D.localDirectionValue i a :=
    D.localDirectionValue_nonneg i a
  have haLt : D.localDirectionValue i a <
      ((n + 1 : ℕ) : ℝ) := by
    have ht' : t < ((n + 1 : ℕ) : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one] using ht
    exact (D.localDirectionValue_lt i a).trans ht'
  have hafloor : Nat.floor (D.localDirectionValue i a) < n + 1 :=
    (Nat.floor_lt ha0).2 haLt
  let c : Fin (n + 1) :=
    ⟨Nat.floor (D.localDirectionValue i a), hafloor⟩
  refine ⟨c, ?_⟩
  exact (mem_incidentBands_iff_exists_local_floor
    D (n + 1) i c).2 ⟨a, rfl⟩

/-- Every valid local direction-cycle exponent is bounded by n
when the full palette contains n+1 colours. -/
theorem localCycle_exponent_le_n_of_width_lt_succ
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (i : V)
    (C : LocalDirectionCycle D i) :
    C.exponent ≤ n := by
  have hnonempty :=
    incidentBands_succ_nonempty_of_localCycle D ht i C
  have hpositive : 0 < (D.incidentBands (n + 1) i).card :=
    Finset.card_pos.mpr hnonempty
  have hbudget := C.exponent_add_incidentBands_card_le ht
  omega

/-- The n-bit residual projection has an unconditional one-layer
activity profile on actual local direction cycles, at every centre. -/
theorem localCycles_standardResidual_oneLayer_profile
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i) :
    let B := standardResidualColoring D n
      (by exact_mod_cast ht)
    (∀ i, (cycles i).exponent ≤ n) ∧
      (∀ i, (active B i).card ≤ n - (cycles i).exponent + 1) := by
  let B : OrderedEdgeColoring V (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast ht)
  constructor
  · intro i
    exact localCycle_exponent_le_n_of_width_lt_succ
      D ht i (cycles i)
  · intro i
    have hbound :=
      (cycles i).exponent_add_incidentBands_card_le ht
    have hexp :=
      localCycle_exponent_le_n_of_width_lt_succ
        D ht i (cycles i)
    have heq : active B i = D.incidentBands (n + 1) i :=
      standardResidual_active_eq_incidentBands_succ
        D n (by exact_mod_cast ht) i
    rw [heq]
    omega

#print axioms incidentBands_succ_nonempty_of_localCycle
#print axioms localCycle_exponent_le_n_of_width_lt_succ
#print axioms localCycles_standardResidual_oneLayer_profile

end DirectionData
end JSP000404Research
