import Mathlib.Combinatorics.Quiver.Path.Vertices
import Mathlib.Data.List.Nodup
import Mathlib.Order.ConditionallyCompleteLattice.Group
import Mathlib.Tactic

/-!
# Potentials for cyclic difference constraints

On a strongly connected quiver, nonpositive weight on every closed walk gives a potential
dominating every edge weight. A return path bounds all path weights from a chosen root, so
their supremum provides the potential. The ordered group can be `ℤ`, which also supplies
integer potentials for half-grid retiming after multiplying all delays by two.

Loop erasure reduces the closed-walk condition to simple cycles. Constructing the actual
planar projection quiver and its embedded-cycle bounds remains a separate obligation.
-/

namespace JSP000404Research
namespace CyclicGraph

open Quiver

variable {V : Type*} [Quiver V]
variable {R : Type*} [AddCommGroup R]

/-- Add the weights of all arrows in a directed walk. -/
def pathWeight (weight : ∀ {u v : V}, (u ⟶ v) → R) {u : V} : ∀ {v}, Path u v → R
  | _, .nil => 0
  | _, .cons p e => pathWeight weight p + weight e

@[simp]
theorem pathWeight_nil (weight : ∀ {u v : V}, (u ⟶ v) → R) (u : V) :
    pathWeight weight (.nil : Path u u) = 0 := rfl

@[simp]
theorem pathWeight_cons (weight : ∀ {u v : V}, (u ⟶ v) → R)
    {u v w : V} (p : Path u v) (e : v ⟶ w) :
    pathWeight weight (p.cons e) = pathWeight weight p + weight e := rfl

@[simp]
theorem pathWeight_comp (weight : ∀ {u v : V}, (u ⟶ v) → R)
    {u v w : V} (p : Path u v) (q : Path v w) :
    pathWeight weight (p.comp q) = pathWeight weight p + pathWeight weight q := by
  induction q with
  | nil => simp
  | cons q e ih => simp [ih, add_assoc]

private theorem vertices_sublist_comp_left {u v w : V} (p : Path u v) (q : Path v w) :
    p.vertices.Sublist (p.comp q).vertices := by
  induction q with
  | nil => simp
  | cons q e ih =>
    apply ih.trans
    simpa only [Quiver.Path.comp_cons, Quiver.Path.vertices_cons, List.concat_eq_append] using
      List.sublist_append_left (p.comp q).vertices [_]

/-- Removing simple nonpositive closed subwalks leaves a simple path of at least the weight. -/
theorem exists_nodup_path_of_simple_closed_nonpos [LinearOrder R] [IsOrderedAddMonoid R]
    (weight : ∀ {u v : V}, (u ⟶ v) → R)
    (hsimple : ∀ (v : V) (p : Path v v), p.vertices.dropLast.Nodup →
      pathWeight weight p ≤ 0) {u v : V} (p : Path u v) :
    ∃ q : Path u v, q.vertices.Nodup ∧ pathWeight weight p ≤ pathWeight weight q := by
  classical
  induction p with
  | nil => exact ⟨.nil, by simp, le_rfl⟩
  | @cons v w p e ih =>
    obtain ⟨q, hq, hweight⟩ := ih
    by_cases hmem : w ∈ q.vertices
    · obtain ⟨q₁, q₂, hsplit⟩ := q.exists_eq_comp_of_mem_vertices hmem
      have hq₁ : q₁.vertices.Nodup := by
        rw [hsplit] at hq
        exact hq.sublist (vertices_sublist_comp_left q₁ q₂)
      have hq₂ : q₂.vertices.Nodup := by
        rw [hsplit, Quiver.Path.vertices_comp] at hq
        exact hq.sublist (List.sublist_append_right _ _)
      have hcycle := hsimple w (q₂.cons e) (by simpa using hq₂)
      refine ⟨q₁, hq₁, ?_⟩
      calc
        pathWeight weight (p.cons e) ≤ pathWeight weight q + weight e :=
          add_le_add hweight (le_rfl : weight e ≤ weight e)
        _ = pathWeight weight q₁ + (pathWeight weight q₂ + weight e) := by
          rw [hsplit, pathWeight_comp, add_assoc]
        _ ≤ pathWeight weight q₁ := by simpa using add_le_add_left hcycle (pathWeight weight q₁)
    · refine ⟨q.cons e, ?_, add_le_add hweight (le_rfl : weight e ≤ weight e)⟩
      simpa only [Quiver.Path.vertices_cons, List.nodup_concat] using And.intro hmem hq

/-- It suffices to check nonpositive weight on closed paths with no repeated internal vertex. -/
theorem closed_walk_nonpos_of_simple_closed_nonpos [LinearOrder R] [IsOrderedAddMonoid R]
    (weight : ∀ {u v : V}, (u ⟶ v) → R)
    (hsimple : ∀ (v : V) (p : Path v v), p.vertices.dropLast.Nodup →
      pathWeight weight p ≤ 0) (v : V) (p : Path v v) : pathWeight weight p ≤ 0 := by
  obtain ⟨q, hq, hweight⟩ := exists_nodup_path_of_simple_closed_nonpos weight hsimple p
  cases q with
  | nil => simpa using hweight
  | cons q e =>
    have hnot := (List.nodup_concat _ _).mp hq
    exact (hnot.1 q.start_mem_vertices).elim

/-- Nonpositive closed walks imply a feasible system of edge difference inequalities. -/
theorem exists_potential_of_closed_walk_nonpos
    [ConditionallyCompleteLinearOrder R] [IsOrderedAddMonoid R]
    (weight : ∀ {u v : V}, (u ⟶ v) → R) (root : V)
    (hconnected : ∀ u v : V, Nonempty (Path u v))
    (hclosed : ∀ (v : V) (p : Path v v), pathWeight weight p ≤ 0) :
    ∃ potential : V → R, ∀ {u v : V} (e : u ⟶ v),
      weight e ≤ potential v - potential u := by
  classical
  let values (v : V) : Set R := {x | ∃ p : Path root v, pathWeight weight p = x}
  have hnonempty (v : V) : (values v).Nonempty := by
    obtain ⟨p⟩ := hconnected root v
    exact ⟨pathWeight weight p, p, rfl⟩
  have hbounded (v : V) : BddAbove (values v) := by
    obtain ⟨q⟩ := hconnected v root
    refine ⟨-pathWeight weight q, ?_⟩
    rintro x ⟨p, rfl⟩
    have h := hclosed root (p.comp q)
    rw [pathWeight_comp] at h
    apply le_neg_iff_add_nonpos_left.mpr
    simpa [add_comm] using h
  refine ⟨fun v ↦ sSup (values v), ?_⟩
  intro u v e
  have hupper : sSup (values u) ≤ sSup (values v) - weight e := by
    apply csSup_le (hnonempty u)
    rintro x ⟨p, rfl⟩
    apply le_sub_iff_add_le.mpr
    exact le_csSup (hbounded v) ⟨p.cons e, rfl⟩
  apply le_sub_iff_add_le.mpr
  simpa [add_comm] using le_sub_iff_add_le.mp hupper

/-- Simple-cycle bounds give a feasible difference potential on a strongly connected quiver. -/
theorem exists_potential_of_simple_closed_nonpos
    [ConditionallyCompleteLinearOrder R] [IsOrderedAddMonoid R]
    (weight : ∀ {u v : V}, (u ⟶ v) → R) (root : V)
    (hconnected : ∀ u v : V, Nonempty (Path u v))
    (hsimple : ∀ (v : V) (p : Path v v), p.vertices.dropLast.Nodup →
      pathWeight weight p ≤ 0) :
    ∃ potential : V → R, ∀ {u v : V} (e : u ⟶ v),
      weight e ≤ potential v - potential u := by
  exact exists_potential_of_closed_walk_nonpos weight root hconnected
    (closed_walk_nonpos_of_simple_closed_nonpos weight hsimple)

#print axioms pathWeight_comp
#print axioms exists_nodup_path_of_simple_closed_nonpos
#print axioms closed_walk_nonpos_of_simple_closed_nonpos
#print axioms exists_potential_of_closed_walk_nonpos
#print axioms exists_potential_of_simple_closed_nonpos

end CyclicGraph
end JSP000404Research
