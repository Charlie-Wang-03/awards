import JSP000404Research.OneLayerProfileLoss
import Mathlib.Tactic

/-!
# Adjacent-level charging criterion for a one-loss phase profile

Assume four natural profiles on a finite vertex set:

  k(v)   target Sendov exponent,
  nu(v)  free-coordinate count of one n-colour certificate,
  d(v)   fixed floor defect,
  z(v)   zero-gap hits at the chosen phase,

with the exact local conservation law

  nu(v) + z(v) = k(v) + d(v)

and the one-exception bound

  z(v) <= d(v)+1.

Then an exact one-layer loss at threshold r is equivalent to

  k(v)=r+1 and z(v)=d(v)+1.

A particularly simple surplus vertex at the same threshold is

  k(v)=r and z(v)<d(v),

because the balance gives nu(v)>=r+1.

Therefore a levelwise injection

  {k=r+1, z=d+1} -> {k=r, z<d}

for every r<n is sufficient for the complete dyadic capacity.

This is a concrete charging target for the remaining phase geometry.  It
matches the comb-like adjacent exponent descent asserted in Sendov's printed
extremal profiles, without assuming those profiles.
-/

namespace JSP000404Research

open scoped BigOperators

def badLevelSet
    {V : Type*} [Fintype V]
    (k d z : V → ℕ) (r : ℕ) : Finset V :=
  (Finset.univ : Finset V).filter fun v =>
    k v = r + 1 ∧ z v = d v + 1

def surplusPrevLevelSet
    {V : Type*} [Fintype V]
    (k d z : V → ℕ) (r : ℕ) : Finset V :=
  (Finset.univ : Finset V).filter fun v =>
    k v = r ∧ z v < d v

theorem layerLossSet_eq_badLevelSet_of_balance
    {V : Type*} [Fintype V]
    (k nu d z : V → ℕ)
    (hbalance : ∀ v, nu v + z v = k v + d v)
    (hone : ∀ v, z v ≤ d v + 1)
    (r : ℕ) :
    layerLossSet k nu r = badLevelSet k d z r := by
  classical
  ext v
  have hkNu : k v ≤ nu v + 1 := by
    have hb := hbalance v
    have ho := hone v
    omega
  rw [mem_layerLossSet_iff_exact_one_loss
    k nu (fun w => by
      have hb := hbalance w
      have ho := hone w
      omega) r v]
  simp only [badLevelSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hk, hnu⟩
    have hb := hbalance v
    have ho := hone v
    constructor
    · exact hk
    · omega
  · rintro ⟨hk, hz⟩
    have hb := hbalance v
    constructor
    · exact hk
    · omega

theorem surplusPrevLevelSet_subset_layerSurplusSet
    {V : Type*} [Fintype V]
    (k nu d z : V → ℕ)
    (hbalance : ∀ v, nu v + z v = k v + d v)
    (r : ℕ) :
    surplusPrevLevelSet k d z r ⊆
      layerSurplusSet k nu r := by
  classical
  intro v hv
  have hv' :
      k v = r ∧ z v < d v := by
    simpa [surplusPrevLevelSet] using hv
  have hb := hbalance v
  apply (mem_layerSurplusSet_iff k nu r v).2
  constructor
  · omega
  · omega

/-- An injection from bad level r+1 centres to exponent-r surplus centres
gives the threshold-r tail inequality. -/
theorem tailCount_le_of_adjacent_level_charge
    {V : Type*} [Fintype V]
    (k nu d z : V → ℕ)
    (hbalance : ∀ v, nu v + z v = k v + d v)
    (hone : ∀ v, z v ≤ d v + 1)
    (r : ℕ)
    (charge :
      {v // v ∈ badLevelSet k d z r} →
        {v // v ∈ surplusPrevLevelSet k d z r})
    (hinj : Function.Injective charge) :
    tailCount k r ≤ tailCount nu r := by
  have hLoss :
      layerLossSet k nu r = badLevelSet k d z r :=
    layerLossSet_eq_badLevelSet_of_balance
      k nu d z hbalance hone r
  have hsub :=
    surplusPrevLevelSet_subset_layerSurplusSet
      k nu d z hbalance r
  rw [tailCount_le_iff_loss_le_surplus]
  rw [hLoss]
  have hcardCharge :
      (badLevelSet k d z r).card ≤
        (surplusPrevLevelSet k d z r).card :=
    Fintype.card_le_of_injective charge hinj
  exact hcardCharge.trans (Finset.card_le_card hsub)

/-- Levelwise adjacent charging closes the full dyadic profile inequality. -/
theorem dyadic_sum_le_of_adjacent_level_charges
    {V : Type*} [Fintype V]
    (k nu d z : V → ℕ) (n : ℕ)
    (hk : ∀ v, k v ≤ n)
    (hnu : ∀ v, nu v ≤ n)
    (hbalance : ∀ v, nu v + z v = k v + d v)
    (hone : ∀ v, z v ≤ d v + 1)
    (charge :
      ∀ r, r < n →
        {v // v ∈ badLevelSet k d z r} →
          {v // v ∈ surplusPrevLevelSet k d z r})
    (hinj :
      ∀ r (hr : r < n),
        Function.Injective (charge r hr)) :
    (∑ v : V, 2 ^ k v) ≤
      ∑ v : V, 2 ^ nu v := by
  apply dyadic_sum_le_of_tailCount_le
    k nu n hk hnu
  intro r hr
  exact tailCount_le_of_adjacent_level_charge
    k nu d z hbalance hone r
    (charge r hr) (hinj r hr)

#print axioms layerLossSet_eq_badLevelSet_of_balance
#print axioms surplusPrevLevelSet_subset_layerSurplusSet
#print axioms tailCount_le_of_adjacent_level_charge
#print axioms dyadic_sum_le_of_adjacent_level_charges

end JSP000404Research
