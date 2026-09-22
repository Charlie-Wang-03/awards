import JSP000404Research.WeightedDefect
import Mathlib.Tactic

/-!
# Weighted coding from ordered edge colours

The regular unit-band grid is not essential.  What the Hansel/Erdős--Szekeres
argument really needs is a colouring of every increasing edge by one of `k`
coordinates such that no increasing path of length two is monochromatic.

For one colour, a vertex is labelled by whether it has an incoming edge of
that colour.  If `v < w` has colour `c`, then `w` has incoming bit `true`;
the no-two-path condition forces `v` to have incoming bit `false`.  Both
endpoints have colour `c` active, so the corresponding partial Boolean words
separate.

This abstraction is designed for adaptive/modified direction partitions:
regular unit bands are one instance, but edge intervals may be reassigned
between colours as long as monochromatic increasing two-paths remain forbidden.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Colouring of increasing edges.  Values on non-increasing pairs are ignored. -/
structure OrderedEdgeColoring (V : Type*) [LinearOrder V] (k : ℕ) where
  color : V → V → Fin k
  noMonoTwoPath : ∀ {a v w : V}, a < v → v < w →
    color a v ≠ color v w

namespace OrderedEdgeColoring

private def incoming {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V k) (c : Fin k) (v : V) : Prop :=
  ∃ a, a < v ∧ C.color a v = c

/-- Colours incident to at least one edge at a vertex. -/
noncomputable def active {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V k) (v : V) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun c ↦
    (∃ a, a < v ∧ C.color a v = c) ∨
    (∃ w, v < w ∧ C.color v w = c)

/-- Canonical source/sink bit of an active colour. -/
noncomputable def bit {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V k) : V → Fin k → Bool :=
  fun v c ↦ decide (incoming C c v)

/-- Exact characterization of the canonical incoming bit. -/
theorem bit_eq_true_iff
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V k)
    (v : V) (c : Fin k) :
    bit C v c = true ↔
      ∃ a, a < v ∧ C.color a v = c := by
  simp [bit, incoming]

/-- Dually, false means that no incoming edge of that colour exists. -/
theorem bit_eq_false_iff
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V k)
    (v : V) (c : Fin k) :
    bit C v c = false ↔
      ¬ ∃ a, a < v ∧ C.color a v = c := by
  simp [bit, incoming]

/-- The canonical incoming bit of an increasing edge's own colour is false
at its lower endpoint. -/
theorem edgeColor_bit_lower_eq_false
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V k)
    {v w : V} (hvw : v < w) :
    bit C v (C.color v w) = false := by
  have hnotin_v : ¬ incoming C (C.color v w) v := by
    rintro ⟨a, hav, hac⟩
    apply C.noMonoTwoPath hav hvw
    simpa using hac
  simp [bit, hnotin_v]

/-- The canonical incoming bit of an increasing edge's own colour is true
at its upper endpoint. -/
theorem edgeColor_bit_upper_eq_true
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V k)
    {v w : V} (hvw : v < w) :
    bit C w (C.color v w) = true := by
  have hin_w : incoming C (C.color v w) w := ⟨v, hvw, rfl⟩
  simp [bit, hin_w]

/-- Hence an increasing edge's own colour separates its endpoint bits. -/
theorem edgeColor_bit_ne
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V k)
    {v w : V} (hvw : v < w) :
    bit C v (C.color v w) ≠ bit C w (C.color v w) := by
  rw [edgeColor_bit_lower_eq_false C hvw,
      edgeColor_bit_upper_eq_true C hvw]
  decide

/-- If a colour is inactive at a vertex, its canonical incoming bit is false. -/
theorem bit_eq_false_of_not_mem_active
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V k)
    (v : V) (c : Fin k)
    (hc : c ∉ active C v) :
    bit C v c = false := by
  have hnotin : ¬ incoming C c v := by
    intro hin
    apply hc
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inl hin
  simp [bit, hnotin]

/-- The colour of an edge separates its two endpoint partial words. -/
theorem separates
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (C : OrderedEdgeColoring V k) :
    ∀ v w, v ≠ w → ∃ c,
      c ∈ active C v ∧ c ∈ active C w ∧ bit C v c ≠ bit C w c := by
  classical
  intro v w hvw
  wlog hvwlt : v < w generalizing v w
  · have hwv : w < v := lt_of_le_of_ne (not_lt.mp hvwlt) hvw.symm
    obtain ⟨c, hcw, hcv, hbit⟩ := this w v hvw.symm hwv
    exact ⟨c, hcv, hcw, hbit.symm⟩

  let c : Fin k := C.color v w
  have hcv : c ∈ active C v := by
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inr ⟨w, hvwlt, rfl⟩
  have hcw : c ∈ active C w := by
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inl ⟨v, hvwlt, rfl⟩

  have hin_w : incoming C c w := ⟨v, hvwlt, rfl⟩
  have hnotin_v : ¬ incoming C c v := by
    rintro ⟨a, hav, hac⟩
    apply C.noMonoTwoPath hav hvwlt
    simpa [c] using hac

  refine ⟨c, hcv, hcw, ?_⟩
  simp [bit, hnotin_v, hin_w]

/-- Weighted Hansel capacity for an arbitrary admissible ordered edge colouring. -/
theorem weighted_capacity
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (C : OrderedEdgeColoring V k) :
    ∑ v, 2 ^ (k - (active C v).card) ≤ 2 ^ k := by
  exact weighted_hansel (bit C) (active C) (separates C)

/-- Exact missing-colour defect form. -/
theorem defect
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (C : OrderedEdgeColoring V k) :
    ∑ v, (2 ^ (k - (active C v).card) - 1) ≤
      2 ^ k - Fintype.card V := by
  exact weighted_hansel_defect (bit C) (active C) (separates C)

/-- One vertex missing one colour already yields a strict cardinality gain. -/
theorem one_missing
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (C : OrderedEdgeColoring V k)
    (v : V) (hmissing : active C v ≠ Finset.univ) :
    Fintype.card V + 1 ≤ 2 ^ k := by
  exact weighted_hansel_one_missing (bit C) (active C)
    (separates C) v hmissing

/-- If every vertex misses a colour, the ambient Boolean capacity halves. -/
theorem all_missing
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (C : OrderedEdgeColoring V k)
    (hmissing : ∀ v, active C v ≠ Finset.univ) :
    2 * Fintype.card V ≤ 2 ^ k := by
  exact weighted_hansel_all_missing (bit C) (active C)
    (separates C) hmissing

/-- If every vertex uses at most a prescribed number of colours, the free
coordinates supply the corresponding Kraft weight. -/
theorem expected_weight_le
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (C : OrderedEdgeColoring V k) (ell : V → ℕ)
    (hactive : ∀ v, (active C v).card ≤ ell v) :
    ∑ v, 2 ^ (k - ell v) ≤
      ∑ v, 2 ^ (k - (active C v).card) := by
  apply Finset.sum_le_sum
  intro v _
  apply Nat.pow_le_pow_right
  · norm_num
  · omega

/-- Local active-colour bounds imply the weighted Kraft inequality. -/
theorem capacity_of_active_le
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (C : OrderedEdgeColoring V k) (ell : V → ℕ)
    (hactive : ∀ v, (active C v).card ≤ ell v) :
    ∑ v, 2 ^ (k - ell v) ≤ 2 ^ k :=
  (expected_weight_le C ell hactive).trans (weighted_capacity C)

/-- Sendov cluster-exponent specialization. -/
theorem cluster_capacity_of_active_le
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (C : OrderedEdgeColoring V k)
    (exponent ell : V → ℕ)
    (hexponent : ∀ v, exponent v ≤ k)
    (hell : ∀ v, ell v = k - exponent v)
    (hactive : ∀ v, (active C v).card ≤ ell v) :
    ∑ v, 2 ^ exponent v ≤ 2 ^ k := by
  calc
    ∑ v, 2 ^ exponent v =
        ∑ v, 2 ^ (k - ell v) := by
          apply Finset.sum_congr rfl
          intro v _
          rw [hell v, Nat.sub_sub_cancel (hexponent v)]
    _ ≤ 2 ^ k := capacity_of_active_le C ell hactive

/-- Any admissible colouring by `k` ordered edge colours gives the
ordinary `2^k` vertex bound. -/
theorem card_le_two_pow
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (C : OrderedEdgeColoring V k) :
    Fintype.card V ≤ 2 ^ k := by
  have hcap := weighted_capacity C
  have hone :
      Fintype.card V ≤ ∑ v, 2 ^ (k - (active C v).card) := by
    simpa using
      (Finset.sum_le_sum (s := (Finset.univ : Finset V))
        (fun v _ => Nat.one_le_pow _ _))
  exact hone.trans hcap

#print axioms bit_eq_true_iff
#print axioms bit_eq_false_iff
#print axioms edgeColor_bit_lower_eq_false
#print axioms edgeColor_bit_upper_eq_true
#print axioms edgeColor_bit_ne
#print axioms bit_eq_false_of_not_mem_active
#print axioms separates
#print axioms weighted_capacity
#print axioms card_le_two_pow
#print axioms expected_weight_le
#print axioms capacity_of_active_le
#print axioms cluster_capacity_of_active_le
#print axioms defect
#print axioms one_missing
#print axioms all_missing

end OrderedEdgeColoring
end JSP000404Research
