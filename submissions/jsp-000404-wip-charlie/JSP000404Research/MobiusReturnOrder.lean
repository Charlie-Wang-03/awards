import Mathlib.Order.Preorder.Finite
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
# Noncrossing return paths in a reflected strip

Disjoint continuous graphs preserve their vertical order. If their right endpoints are
identified with reflected left endpoints, the return map reverses that order. A finite
order-reversing map is involutive, so a single orbit contains at most two paths.

This is the analytic and finite-order part of the proposed cyclic-wire argument. Constructing
these paths from every simple cycle of a planar projection arrangement remains a separate
geometric obligation. No arbitrary-configuration capacity theorem is asserted here.
-/

namespace JSP000404Research

theorem disjoint_graphs_preserve_order {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hne : ∀ x ∈ Set.Icc a b, f x ≠ g x) (hstart : f a < g a) :
    f b < g b := by
  by_contra h
  have hend : g b ≤ f b := le_of_not_gt h
  have hzero : (0 : ℝ) ∈ Set.Icc (f a - g a) (f b - g b) := by
    constructor <;> linarith
  obtain ⟨x, hx, hvalue⟩ := intermediate_value_Icc hab (hf.sub hg) hzero
  exact hne x hx (sub_eq_zero.mp hvalue)

theorem finite_strictAnti_involutive {V : Type*} [LinearOrder V] [Finite V]
    {next : V → V} (hnext : StrictAnti next) : Function.Involutive next := by
  intro v
  exact (hnext.comp hnext).apply_eq

theorem finite_strictAnti_orbit_card_le_two {V : Type*} [LinearOrder V] [Fintype V]
    {next : V → V} (hnext : StrictAnti next) (start : V)
    (horbit : ∀ v, ∃ k : ℕ, next^[k] start = v) : Fintype.card V ≤ 2 := by
  classical
  have hinv := finite_strictAnti_involutive hnext
  have hiter (k : ℕ) : next^[k] start = start ∨ next^[k] start = next start := by
    induction k with
    | zero => exact Or.inl rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with h | h
      · exact Or.inr (congrArg next h)
      · exact Or.inl ((congrArg next h).trans (hinv start))
  have hcover : (Finset.univ : Finset V) ⊆ {start, next start} := by
    intro v _
    obtain ⟨k, rfl⟩ := horbit v
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hiter k
  have hpair : ({start, next start} : Finset V).card ≤ 2 := by
    simpa using Finset.card_insert_le start ({next start} : Finset V)
  exact (Finset.card_le_card hcover).trans hpair

/-- The return of disjoint graph paths through a reflected strip is order reversing. -/
theorem reflected_strip_return_strictAnti {V : Type*} [LinearOrder V]
    (path : V → ℝ → ℝ) (next : V → V) {a b : ℝ} (hab : a ≤ b)
    (hcont : ∀ v, ContinuousOn (path v) (Set.Icc a b))
    (hdisjoint : ∀ v w, v ≠ w → ∀ x ∈ Set.Icc a b, path v x ≠ path w x)
    (hstart : StrictMono (fun v ↦ path v a))
    (hreturn : ∀ v, path v b = -path (next v) a) : StrictAnti next := by
  intro v w hvw
  have hend := disjoint_graphs_preserve_order hab (hcont v) (hcont w)
    (hdisjoint v w (ne_of_lt hvw)) (hstart hvw)
  rw [hreturn v, hreturn w] at hend
  exact hstart.lt_iff_lt.mp (by linarith : path (next w) a < path (next v) a)

/-- A single return orbit in a reflected strip has at most two disjoint paths. -/
theorem reflected_strip_single_orbit_card_le_two {V : Type*} [LinearOrder V] [Fintype V]
    (path : V → ℝ → ℝ) (next : V → V) {a b : ℝ} (hab : a ≤ b)
    (hcont : ∀ v, ContinuousOn (path v) (Set.Icc a b))
    (hdisjoint : ∀ v w, v ≠ w → ∀ x ∈ Set.Icc a b, path v x ≠ path w x)
    (hstart : StrictMono (fun v ↦ path v a))
    (hreturn : ∀ v, path v b = -path (next v) a)
    (start : V) (horbit : ∀ v, ∃ k : ℕ, next^[k] start = v) :
    Fintype.card V ≤ 2 := by
  exact finite_strictAnti_orbit_card_le_two
    (reflected_strip_return_strictAnti path next hab hcont hdisjoint hstart hreturn) start horbit

#print axioms disjoint_graphs_preserve_order
#print axioms finite_strictAnti_involutive
#print axioms finite_strictAnti_orbit_card_le_two
#print axioms reflected_strip_return_strictAnti
#print axioms reflected_strip_single_orbit_card_le_two

end JSP000404Research
