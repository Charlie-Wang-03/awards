import JSP000404Research.ResidualNetCollisionRainbowPairObstruction
import Mathlib.Tactic

/-!
# Candidate-level four-endpoint separation for DISJOINT transport colour pairs

Every candidate target-exact eligible bridge (b,v) has exactly ONE
retained-active violation at b and exactly ONE at v. An edge's
original forward colour is that unique violation at b; its
original reverse colour is the unique violation at v.

This gives a candidate GRAPH theorem, not merely an actual-source
theorem: if two candidate edges have DISJOINT unordered two-flip
colour supports, they CANNOT share any original soft-bridge vertex,
in the same role or in opposite roles. Four cross-edge inequalities
follow purely from the certified exact singleton-shell conditions.

No assumption that candidate edges are actual NET sources, and
no geometric claim that disjoint-colour edges are forbidden under
AngleCap. Their continued existence is an honest open possibility.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Two elements of a cardinality-one finite set are equal. -/
private theorem target_exact_shell_unique_colour
    {n : ℕ} (A : Finset (Fin n)) (hA : A.card = 1)
    {a b : Fin n} (ha : a ∈ A) (hb : b ∈ A) :
    a = b := by
  classical
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hA
  rw [hx] at ha hb
  exact (Finset.mem_singleton.mp ha).trans
    (Finset.mem_singleton.mp hb).symm

/-- Opposite source flip colour labels are certified members of
each corresponding unordered two-colour candidate edge support. -/
private theorem target_edge_reverse_colour_mem_support
    {V : Type*} {n : ℕ}
    (e : (V × Fin n) × (V × Fin n)) :
    e.1.2 ∈ targetExactShellEdgeColourSupport e := by
  simp [targetExactShellEdgeColourSupport]

private theorem target_edge_forward_colour_mem_support
    {V : Type*} {n : ℕ}
    (e : (V × Fin n) × (V × Fin n)) :
    e.2.2 ∈ targetExactShellEdgeColourSupport e := by
  simp [targetExactShellEdgeColourSupport]

/-- Two target-compatible candidate bridge edges with pairwise
DISJOINT unordered flip-colour supports have ALL FOUR cross-edge
original bridge endpoints distinct. This is true even for
candidate edges which are not certified actual NET sources. -/
theorem target_exact_shell_disjoint_colours_force_four_cross_endpoints_distinct
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool)
    (e f : (V × Fin n) × (V × Fin n))
    (he : e ∈ targetExactShellSlotEdges C exponent d)
    (hf : f ∈ targetExactShellSlotEdges C exponent d)
    (hdis : Disjoint
      (targetExactShellEdgeColourSupport e)
      (targetExactShellEdgeColourSupport f)) :
    e.1.1 ≠ f.1.1 ∧ e.2.1 ≠ f.2.1 ∧
    e.1.1 ≠ f.2.1 ∧ e.2.1 ≠ f.1.1 := by
  classical
  obtain ⟨heBase, heB, heCR, heCF, _, _⟩ :=
    Finset.mem_filter.mp he
  obtain ⟨hfBase, hfB, hfCR, hfCF, _, _⟩ :=
    Finset.mem_filter.mp hf
  have hcardEL : (retainedActiveViolationCoords C e.1.1 d).card = 1 :=
    (Finset.mem_filter.mp heB).2.1
  have hcardEU : (retainedActiveViolationCoords C e.2.1 d).card = 1 :=
    (Finset.mem_filter.mp heB).2.2.1
  have hdis' := Finset.disjoint_left.mp hdis
  have heF : e.2.2 ∈ targetExactShellEdgeColourSupport e :=
    target_edge_forward_colour_mem_support e
  have heR : e.1.2 ∈ targetExactShellEdgeColourSupport e :=
    target_edge_reverse_colour_mem_support e
  have hfF : f.2.2 ∈ targetExactShellEdgeColourSupport f :=
    target_edge_forward_colour_mem_support f
  have hfR : f.1.2 ∈ targetExactShellEdgeColourSupport f :=
    target_edge_reverse_colour_mem_support f
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hv
    have hfCF' : f.2.2 ∈ retainedActiveViolationCoords C e.1.1 d := by
      rw [hv]
      exact hfCF
    have hc : e.2.2 = f.2.2 :=
      target_exact_shell_unique_colour
        (retainedActiveViolationCoords C e.1.1 d)
        hcardEL heCF hfCF'
    exact hdis' heF (hc ▸ hfF)
  · intro hv
    have hfCR' : f.1.2 ∈ retainedActiveViolationCoords C e.2.1 d := by
      rw [hv]
      exact hfCR
    have hc : e.1.2 = f.1.2 :=
      target_exact_shell_unique_colour
        (retainedActiveViolationCoords C e.2.1 d)
        hcardEU heCR hfCR'
    exact hdis' heR (hc ▸ hfR)
  · intro hv
    have hfCR' : f.1.2 ∈ retainedActiveViolationCoords C e.1.1 d := by
      rw [hv]
      exact hfCR
    have hc : e.2.2 = f.1.2 :=
      target_exact_shell_unique_colour
        (retainedActiveViolationCoords C e.1.1 d)
        hcardEL heCF hfCR'
    exact hdis' heF (hc ▸ hfR)
  · intro hv
    have hfCF' : f.2.2 ∈ retainedActiveViolationCoords C e.2.1 d := by
      rw [hv]
      exact hfCF
    have hc : e.1.2 = f.2.2 :=
      target_exact_shell_unique_colour
        (retainedActiveViolationCoords C e.2.1 d)
        hcardEU heCR hfCF'
    exact hdis' heR (hc ▸ hfF)

/-- Contrapositive candidate-graph formulation: shared ANY source
bridge vertex forces non-disjoint unordered original flip supports,
so true four-bit collision geometry never arises at that vertex. -/
theorem target_exact_shell_shared_endpoint_forces_common_colour
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool)
    (e f : (V × Fin n) × (V × Fin n))
    (he : e ∈ targetExactShellSlotEdges C exponent d)
    (hf : f ∈ targetExactShellSlotEdges C exponent d)
    (hshare : e.1.1 = f.1.1 ∨ e.2.1 = f.2.1 ∨
      e.1.1 = f.2.1 ∨ e.2.1 = f.1.1) :
    (targetExactShellEdgeColourSupport e ∩
      targetExactShellEdgeColourSupport f).Nonempty := by
  classical
  by_contra hempty
  have hdis : Disjoint
      (targetExactShellEdgeColourSupport e)
      (targetExactShellEdgeColourSupport f) := by
    apply Finset.disjoint_iff_inter_eq_empty.mpr
    exact Finset.not_nonempty_iff_eq_empty.mp hempty
  obtain ⟨hll, huu, hlu, hul⟩ :=
    target_exact_shell_disjoint_colours_force_four_cross_endpoints_distinct
      C exponent d e f he hf hdis
  rcases hshare with h | h | h | h
  · exact hll h
  · exact huu h
  · exact hlu h
  · exact hul h

#print axioms target_exact_shell_disjoint_colours_force_four_cross_endpoints_distinct
#print axioms target_exact_shell_shared_endpoint_forces_common_colour

end OrderedEdgeColoring
end JSP000404Research
