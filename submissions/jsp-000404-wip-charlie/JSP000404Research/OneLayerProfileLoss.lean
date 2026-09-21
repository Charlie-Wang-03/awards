import JSP000404Research.TailMajorizationCapacity
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Exact one-layer loss after deleting one Boolean coordinate

Suppose a target exponent profile k and an available free-coordinate profile
nu satisfy

  k(v) <= nu(v) + 1.

This is exactly the situation obtained by projecting an (n+1)-coordinate
partial code to n coordinates: deleting one coordinate can reduce the free
count by at most one.

At threshold r define

  K_r = {v | r < k(v)},
  N_r = {v | r < nu(v)}.

Tail domination K_r.card <= N_r.card is equivalent to saying that the vertices
lost at threshold r can be paid by the surplus vertices at that threshold.

Under the one-layer-loss assumption, the lost set has an exact description:

  K_r \ N_r = {v | k(v)=r+1 and nu(v)=r}.

Thus the remaining geometric/combinatorial task may be formulated as an
injection from these exact one-layer losses into threshold-surplus vertices

  {v | k(v)<=r and r<nu(v)}.

This is substantially weaker than pointwise palette domination.
-/

namespace JSP000404Research

def aboveSet
    {V : Type*} [Fintype V]
    (f : V → ℕ) (r : ℕ) : Finset V :=
  (Finset.univ : Finset V).filter fun v => r < f v

@[simp] theorem card_aboveSet_eq_tailCount
    {V : Type*} [Fintype V]
    (f : V → ℕ) (r : ℕ) :
    (aboveSet f r).card = tailCount f r := by
  rfl

def layerLossSet
    {V : Type*} [Fintype V]
    (k nu : V → ℕ) (r : ℕ) : Finset V :=
  aboveSet k r \ aboveSet nu r

def layerSurplusSet
    {V : Type*} [Fintype V]
    (k nu : V → ℕ) (r : ℕ) : Finset V :=
  aboveSet nu r \ aboveSet k r

theorem tailCount_le_iff_loss_le_surplus
    {V : Type*} [Fintype V]
    (k nu : V → ℕ) (r : ℕ) :
    tailCount k r ≤ tailCount nu r ↔
      (layerLossSet k nu r).card ≤
        (layerSurplusSet k nu r).card := by
  simpa [layerLossSet, layerSurplusSet, aboveSet, tailCount] using
    (Finset.card_sdiff_le_card_sdiff_iff
      (s := aboveSet k r) (t := aboveSet nu r))

theorem mem_layerLossSet_iff_exact_one_loss
    {V : Type*} [Fintype V]
    (k nu : V → ℕ)
    (hone : ∀ v, k v ≤ nu v + 1)
    (r : ℕ) (v : V) :
    v ∈ layerLossSet k nu r ↔
      k v = r + 1 ∧ nu v = r := by
  classical
  simp only [layerLossSet, Finset.mem_sdiff, aboveSet,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hrk, hrnu⟩
    have hnu : nu v ≤ r := by omega
    have hk := hone v
    constructor <;> omega
  · rintro ⟨hk, hnu⟩
    subst hk
    subst hnu
    omega

theorem mem_layerSurplusSet_iff
    {V : Type*} [Fintype V]
    (k nu : V → ℕ)
    (r : ℕ) (v : V) :
    v ∈ layerSurplusSet k nu r ↔
      k v ≤ r ∧ r < nu v := by
  classical
  simp [layerSurplusSet, aboveSet]
  omega

/-- A threshold-wise injection from exact one-layer losses to surplus vertices
is sufficient for tail domination. -/
theorem tailCount_le_of_loss_injection
    {V : Type*} [Fintype V]
    (k nu : V → ℕ)
    (hone : ∀ v, k v ≤ nu v + 1)
    (r : ℕ)
    (repair :
      {v // v ∈ layerLossSet k nu r} →
        {v // v ∈ layerSurplusSet k nu r})
    (hinj : Function.Injective repair) :
    tailCount k r ≤ tailCount nu r := by
  rw [tailCount_le_iff_loss_le_surplus]
  exact Fintype.card_le_of_injective repair hinj

/-- All thresholds at once yield the dyadic profile inequality. -/
theorem dyadic_sum_le_of_one_layer_repairs
    {V : Type*} [Fintype V]
    (k nu : V → ℕ) (n : ℕ)
    (hk : ∀ v, k v ≤ n)
    (hnu : ∀ v, nu v ≤ n)
    (hone : ∀ v, k v ≤ nu v + 1)
    (repair :
      ∀ r, r < n →
        {v // v ∈ layerLossSet k nu r} →
          {v // v ∈ layerSurplusSet k nu r})
    (hinj :
      ∀ r (hr : r < n),
        Function.Injective (repair r hr)) :
    (∑ v : V, 2 ^ k v) ≤
      ∑ v : V, 2 ^ nu v := by
  apply dyadic_sum_le_of_tailCount_le k nu n hk hnu
  intro r hr
  exact tailCount_le_of_loss_injection
    k nu hone r (repair r hr) (hinj r hr)

namespace OrderedEdgeColoring

/-- n-colour capacity from one-layer profile loss plus threshold repair
injections. -/
theorem exponent_capacity_of_one_layer_repairs
    {V : Type*} [LinearOrder V] [Fintype V]
    {n : ℕ}
    (C : OrderedEdgeColoring V n)
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (hone :
      ∀ v,
        exponent v ≤
          (n - (active C v).card) + 1)
    (repair :
      ∀ r, r < n →
        {v // v ∈
          layerLossSet exponent
            (fun w => n - (active C w).card) r} →
        {v // v ∈
          layerSurplusSet exponent
            (fun w => n - (active C w).card) r})
    (hinj :
      ∀ r (hr : r < n),
        Function.Injective (repair r hr)) :
    (∑ v : V, 2 ^ exponent v) ≤ 2 ^ n := by
  have hnu :
      ∀ v, n - (active C v).card ≤ n := by
    intro v
    omega
  have hprofile :=
    dyadic_sum_le_of_one_layer_repairs
      exponent
      (fun v => n - (active C v).card)
      n hexp hnu hone repair hinj
  exact hprofile.trans C.weighted_capacity

#print axioms exponent_capacity_of_one_layer_repairs

end OrderedEdgeColoring

#print axioms tailCount_le_iff_loss_le_surplus
#print axioms mem_layerLossSet_iff_exact_one_loss
#print axioms tailCount_le_of_loss_injection
#print axioms dyadic_sum_le_of_one_layer_repairs

end JSP000404Research
