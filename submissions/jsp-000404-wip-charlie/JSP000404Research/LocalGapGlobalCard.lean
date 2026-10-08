import JSP000404Research.LocalDirectionGapMissingBand
import JSP000404Research.StandardBandColor
import Mathlib.Tactic

/-!
# A local angular gap criterion for the global vertex-count bound

A large cyclic gap (floor quotient at least two) leaves an unused actual
standard-band colour at its centre. When this holds at *every* vertex,
the all-missing-colour form of the weighted Hansel inequality implies the
sharper bound |V| <= 2^n rather than merely |V| <= 2^(n+1).

The hypothesis concerns every vertex. This is a conditional theorem and
does not settle the unrestricted weighted Sendov capacity.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

/-- A sufficiently large local cyclic gap makes an actual standard
(n+1)-band colour inactive at its centre. -/
theorem standardBand_inactive_of_large_local_gap
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (i : V)
    (C : LocalDirectionCycle D i)
    (ht : t < (n : ℝ) + 1)
    {gap : ℝ}
    (hgap : gap ∈ cyclicRealGapsAt t C.values)
    (hlarge : 2 ≤ Nat.floor gap) :
    ∃ c : Fin (n + 1),
      c ∉ active
        (standardBandColoring D (n + 1) (Nat.succ_pos n)
          (by exact_mod_cast ht)) i := by
  obtain ⟨c, hc⟩ :=
    C.large_gap_exists_missing_incident_band ht hgap hlarge
  refine ⟨c, ?_⟩
  rw [standardBand_active_eq_incidentBands]
  exact hc

/-- Conditional global improvement: if every centre has a cyclic
local gap spanning at least two unit bands, then |V| <= 2^n. -/
theorem card_le_two_pow_of_large_local_gap_everywhere
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    (hlarge : ∀ i : V, ∃ gap : ℝ,
      gap ∈ cyclicRealGapsAt t (cycles i).values ∧
        2 ≤ Nat.floor gap) :
    Fintype.card V ≤ 2 ^ n := by
  let R : OrderedEdgeColoring V (n + 1) :=
    standardBandColoring D (n + 1) (Nat.succ_pos n)
      (by exact_mod_cast ht)
  have hmissing : ∀ i : V, active R i ≠ Finset.univ := by
    intro i hfull
    obtain ⟨gap, hgap, hq⟩ := hlarge i
    obtain ⟨c, hc⟩ :=
      standardBand_inactive_of_large_local_gap
        D i (cycles i) ht hgap hq
    have hcR : c ∉ active R i := by
      simpa only [R] using hc
    exact hcR (by rw [hfull]; simp)
  have hcapacity := all_missing R hmissing
  have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
    simp [pow_succ, mul_comm]
  rw [hpow] at hcapacity
  omega

#print axioms standardBand_inactive_of_large_local_gap
#print axioms card_le_two_pow_of_large_local_gap_everywhere

end DirectionData
end JSP000404Research
