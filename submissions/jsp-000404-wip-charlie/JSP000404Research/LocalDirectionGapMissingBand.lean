import JSP000404Research.CyclicBandGapDomination
import JSP000404Research.LocalDirectionCycle
import Mathlib.Tactic

/-!
# A large local angular gap leaves an unused incident direction band

The cyclic gap-to-band budget is an abstract one-dimensional statement.
For a concrete local direction cycle of an ordered direction colouring,
we identify the abstract occupied floor labels with the actual
incident-band Finset.

A gap with natural quotient at least two therefore produces a concrete
missing incident band. This is a local direction-band witness; it does
not assert a Boolean completion-cube hole or a global hard-word matching.
-/

namespace JSP000404Research
namespace DirectionData
namespace LocalDirectionCycle

/-- A large gap in a concrete local direction cycle leaves an actual
unused direction-colour band at its centre. -/
theorem large_gap_exists_missing_incident_band
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    {D : DirectionData V t} {i : V}
    (C : LocalDirectionCycle D i)
    (ht : t < (n : ℝ) + 1)
    {gap : ℝ}
    (hgap : gap ∈ cyclicRealGapsAt t C.values)
    (hlarge : 2 ≤ Nat.floor gap) :
    ∃ c : Fin (n + 1),
      c ∉ D.incidentBands (n + 1) i := by
  classical
  obtain ⟨a, xs, hvalues⟩ :
      ∃ a xs, C.values = a :: xs := by
    cases h : C.values with
    | nil =>
        exact False.elim (C.values_nonempty h)
    | cons a xs =>
        exact ⟨a, xs, rfl⟩
  have hsorted :
      (a :: xs).Pairwise (· ≤ ·) := by
    simpa [hvalues] using C.values_pairwise
  have hall0 :
      ∀ x ∈ a :: xs, 0 ≤ x := by
    intro x hx
    exact (C.value_mem_bounds
      (by simpa [hvalues] using hx)).1
  have hallt :
      ∀ x ∈ a :: xs, x < t := by
    intro x hx
    exact (C.value_mem_bounds
      (by simpa [hvalues] using hx)).2
  have ha0 : 0 ≤ a := hall0 a (by simp)
  have hgap' :
      gap ∈ cyclicRealGapsAt t (a :: xs) := by
    simpa [hvalues] using hgap
  obtain ⟨c, hc, hcNot⟩ :=
    cyclicRealGap_large_exists_missing_band
      a xs n ha0 hsorted hall0 hallt ht hgap' hlarge
  let band : Fin (n + 1) :=
    ⟨c, Nat.lt_succ_of_le hc⟩
  refine ⟨band, ?_⟩
  intro hmem
  have hwidth :
      t ≤ ((n + 1 : ℕ) : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using (le_of_lt ht)
  have heq :=
    C.occupiedNatBands_values_eq_incident_val_map
      (n + 1) hwidth
  have himage :
      c ∈ (D.incidentBands (n + 1) i).map
        Fin.valEmbedding := by
    exact Finset.mem_map.mpr ⟨band, hmem, rfl⟩
  have hoccupied : c ∈ occupiedNatBands C.values := by
    rw [heq]
    exact himage
  exact hcNot (by
    simpa [occupiedNatBands, hvalues] using hoccupied)

#print axioms large_gap_exists_missing_incident_band

end LocalDirectionCycle
end DirectionData
end JSP000404Research
