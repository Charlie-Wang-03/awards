import JSP000404Research.ResidualLossFibreRankBudget
import Mathlib.Tactic

/-!
# Endpoint restrictions for high-exponent translated-loss fibres

The rank-to-palette injection forces any true-labelled fibre vertex that has
an earlier fibre predecessor to lose at least one unit of maximal exponent.
Dually a false-labelled vertex with a later fibre successor cannot have
maximal exponent. These restrictions use genuine geometric owner-edge
classification: they are not cardinality-only surrogate Hall matchings.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem translatedLossFibre_true_successor_exponent_lt_n
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (word : Fin n → Bool)
    (hactive :
      ∀ x, x ∈ translatedLossFibre C exponent choice word →
        choice x ∈ retainedActive C x)
    {v w : V}
    (hv : v ∈ translatedLossFibre C exponent choice word)
    (hw : w ∈ translatedLossFibre C exponent choice word)
    (hvw : v < w)
    (hwTrue : word (choice w) = true) :
    exponent w < n := by
  have hbudget :=
    translatedLossFibre_true_prefix_exponent_budget
      C exponent hexp honeLoss choice word hactive hw hwTrue
  have hvPrefix :
      v ∈ translatedLossFibrePrefix C exponent choice word w :=
    (mem_translatedLossFibrePrefix C exponent choice word w v).2
      ⟨hv, hvw.le⟩
  have hwPrefix :
      w ∈ translatedLossFibrePrefix C exponent choice word w :=
    (mem_translatedLossFibrePrefix C exponent choice word w w).2
      ⟨hw, le_refl w⟩
  have hsubset :
      ({v, w} : Finset V) ⊆
        translatedLossFibrePrefix C exponent choice word w := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hvPrefix
    · exact hwPrefix
  have htwo :
      2 ≤ (translatedLossFibrePrefix C exponent choice word w).card := by
    have h := Finset.card_le_card hsubset
    simpa [ne_of_lt hvw] using h
  omega

theorem translatedLossFibre_false_predecessor_exponent_lt_n
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (word : Fin n → Bool)
    (hactive :
      ∀ x, x ∈ translatedLossFibre C exponent choice word →
        choice x ∈ retainedActive C x)
    {v w : V}
    (hv : v ∈ translatedLossFibre C exponent choice word)
    (hw : w ∈ translatedLossFibre C exponent choice word)
    (hvw : v < w)
    (hvFalse : word (choice v) = false) :
    exponent v < n := by
  have hbudget :=
    translatedLossFibre_false_suffix_exponent_budget
      C exponent hexp honeLoss choice word hactive hv hvFalse
  have hvSuffix :
      v ∈ translatedLossFibreSuffix C exponent choice word v :=
    (mem_translatedLossFibreSuffix C exponent choice word v v).2
      ⟨hv, le_refl v⟩
  have hwSuffix :
      w ∈ translatedLossFibreSuffix C exponent choice word v :=
    (mem_translatedLossFibreSuffix C exponent choice word v w).2
      ⟨hw, hvw.le⟩
  have hsubset :
      ({v, w} : Finset V) ⊆
        translatedLossFibreSuffix C exponent choice word v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hvSuffix
    · exact hwSuffix
  have htwo :
      2 ≤ (translatedLossFibreSuffix C exponent choice word v).card := by
    have h := Finset.card_le_card hsubset
    simpa [ne_of_lt hvw] using h
  omega

#print axioms translatedLossFibre_true_successor_exponent_lt_n
#print axioms translatedLossFibre_false_predecessor_exponent_lt_n

end OrderedEdgeColoring
end JSP000404Research
