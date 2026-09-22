import JSP000404Research.WeightedProfileRepair
import Mathlib.Tactic

/-!
# Weighted injection criterion for one-layer profile losses

The aggregate repair theorem in WeightedProfileRepair does not require
threshold-wise tail domination.  This file gives a concrete sufficient
certificate which is substantially weaker than AdjacentLevelChargeCapacity.

Let

  L = {v | k(v) = nu(v)+1}

be the exact one-layer losses and

  S = {v | k(v)+1 <= nu(v)}

the vertices with at least one full surplus layer.

A loss vertex v costs exactly

  2^nu(v) = 2^(k(v)-1),

while a surplus vertex w contributes at least 2^k(w) credit.

Therefore it is enough to inject loss vertices into surplus vertices with the
single weight condition

  nu(v) <= k(charge(v)).

Equivalently, the charged surplus exponent may lie at any level at least
k(v)-1.  No exact adjacent-level matching is required.

This is the natural combinatorial outlet for non-comb Kraft profiles.
-/

namespace JSP000404Research

open scoped BigOperators

def oneLayerLossVertices
    {V : Type*} [Fintype V]
    (k nu : V → ℕ) : Finset V :=
  (Finset.univ : Finset V).filter fun v =>
    k v = nu v + 1

def oneLayerSurplusVertices
    {V : Type*} [Fintype V]
    (k nu : V → ℕ) : Finset V :=
  (Finset.univ : Finset V).filter fun v =>
    k v + 1 ≤ nu v

@[simp] theorem mem_oneLayerLossVertices
    {V : Type*} [Fintype V]
    (k nu : V → ℕ) (v : V) :
    v ∈ oneLayerLossVertices k nu ↔
      k v = nu v + 1 := by
  classical
  simp [oneLayerLossVertices]

@[simp] theorem mem_oneLayerSurplusVertices
    {V : Type*} [Fintype V]
    (k nu : V → ℕ) (v : V) :
    v ∈ oneLayerSurplusVertices k nu ↔
      k v + 1 ≤ nu v := by
  classical
  simp [oneLayerSurplusVertices]

theorem oneLayerLossWeight_eq_sum_lossVertices
    {V : Type*} [Fintype V]
    (k nu : V → ℕ) :
    oneLayerLossWeight k nu =
      ∑ v ∈ oneLayerLossVertices k nu, 2 ^ nu v := by
  classical
  unfold oneLayerLossWeight oneLayerLossVertices
  rw [Finset.sum_filter]

theorem oneLayerSurplusCredit_eq_sum_surplusVertices
    {V : Type*} [Fintype V]
    (k nu : V → ℕ) :
    oneLayerSurplusCredit k nu =
      ∑ v ∈ oneLayerSurplusVertices k nu, 2 ^ k v := by
  classical
  unfold oneLayerSurplusCredit oneLayerSurplusVertices
  rw [Finset.sum_filter]

/-- A weighted injection from exact one-layer losses into arbitrary
one-layer-or-better surplus vertices pays the entire one-layer loss mass. -/
theorem oneLayerLossWeight_le_surplusCredit_of_weighted_injection
    {V : Type*} [Fintype V]
    (k nu : V → ℕ)
    (charge : V → V)
    (hmem :
      ∀ v, v ∈ oneLayerLossVertices k nu →
        charge v ∈ oneLayerSurplusVertices k nu)
    (hinj :
      Set.InjOn charge
        (oneLayerLossVertices k nu : Set V))
    (hweight :
      ∀ v, v ∈ oneLayerLossVertices k nu →
        nu v ≤ k (charge v)) :
    oneLayerLossWeight k nu ≤
      oneLayerSurplusCredit k nu := by
  classical
  let L := oneLayerLossVertices k nu
  let S := oneLayerSurplusVertices k nu
  have himage :
      L.image charge ⊆ S := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨v, hvL, rfl⟩
    exact hmem v hvL
  have hpoint :
      ∀ v ∈ L,
        2 ^ nu v ≤ 2 ^ k (charge v) := by
    intro v hv
    exact Nat.pow_le_pow_right
      (by norm_num : 0 < 2)
      (hweight v hv)
  have hsumPoint :
      (∑ v ∈ L, 2 ^ nu v) ≤
        ∑ v ∈ L, 2 ^ k (charge v) := by
    exact Finset.sum_le_sum hpoint
  have hsumImage :
      (∑ v ∈ L, 2 ^ k (charge v)) =
        ∑ w ∈ L.image charge, 2 ^ k w := by
    symm
    exact Finset.sum_image
      (fun a ha b hb hab =>
        hinj ha hb hab)
  rw [oneLayerLossWeight_eq_sum_lossVertices,
      oneLayerSurplusCredit_eq_sum_surplusVertices]
  change
    (∑ v ∈ L, 2 ^ nu v) ≤
      ∑ w ∈ S, 2 ^ k w
  exact hsumPoint.trans_eq hsumImage |>.trans
    (Finset.sum_le_sum_of_subset himage)

/-- Combined profile comparison: one-layer loss, plus one weighted injection,
is enough for the full dyadic inequality. -/
theorem dyadic_sum_le_of_oneLayer_weighted_injection
    {V : Type*} [Fintype V]
    (k nu : V → ℕ)
    (hone : ∀ v, k v ≤ nu v + 1)
    (charge : V → V)
    (hmem :
      ∀ v, v ∈ oneLayerLossVertices k nu →
        charge v ∈ oneLayerSurplusVertices k nu)
    (hinj :
      Set.InjOn charge
        (oneLayerLossVertices k nu : Set V))
    (hweight :
      ∀ v, v ∈ oneLayerLossVertices k nu →
        nu v ≤ k (charge v)) :
    (∑ v, 2 ^ k v) ≤ ∑ v, 2 ^ nu v := by
  apply dyadic_sum_le_of_oneLayer_weighted_repair
    k nu hone
  exact oneLayerLossWeight_le_surplusCredit_of_weighted_injection
    k nu charge hmem hinj hweight

namespace OrderedEdgeColoring

/-- Ordered-colouring specialization.  Geometry may charge each exact bad
centre to any distinct surplus centre whose exponent is at least the bad
centre's free count. -/
theorem exponent_capacity_of_oneLayer_weighted_injection
    {V : Type*} [LinearOrder V] [Fintype V]
    {n : ℕ}
    (C : OrderedEdgeColoring V n)
    (exponent : V → ℕ)
    (hone :
      ∀ v,
        exponent v ≤
          (n - (active C v).card) + 1)
    (charge : V → V)
    (hmem :
      ∀ v,
        v ∈ oneLayerLossVertices exponent
          (fun w => n - (active C w).card) →
        charge v ∈ oneLayerSurplusVertices exponent
          (fun w => n - (active C w).card))
    (hinj :
      Set.InjOn charge
        (oneLayerLossVertices exponent
          (fun w => n - (active C w).card) : Set V))
    (hweight :
      ∀ v,
        v ∈ oneLayerLossVertices exponent
          (fun w => n - (active C w).card) →
        n - (active C v).card ≤ exponent (charge v)) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n := by
  have hprofile :
      (∑ v, 2 ^ exponent v) ≤
        ∑ v, 2 ^ (n - (active C v).card) := by
    exact dyadic_sum_le_of_oneLayer_weighted_injection
      exponent
      (fun v => n - (active C v).card)
      hone charge hmem hinj hweight
  exact hprofile.trans C.weighted_capacity

#print axioms exponent_capacity_of_oneLayer_weighted_injection

end OrderedEdgeColoring

#print axioms oneLayerLossWeight_le_surplusCredit_of_weighted_injection
#print axioms dyadic_sum_le_of_oneLayer_weighted_injection

end JSP000404Research
