import JSP000404Research.ResidualNetCollisionEightCentreBarrier
import Mathlib.Tactic

/-!
# Quantitative real NET collision fibre cost: four vertices per source

The preceding theorem proved that TWO distinct same-target original
NET sources require FOUR distinct original hard carriers, hence at
least EIGHT vertices. This module strengthens that pairwise
obstruction to an ENTIRE finite fibre:

  4 * |actual NET source fibre(d)| <= |original vertices|.

Proof: the two original hard carriers of EACH actual source are
in a global vertex matching. Within a fixed canonical diagonal
fibre, the forward carrier map and the reverse rigid carrier map
are EACH injective; their images are disjoint by the safe-outgoing
dichotomy. Thus the fibre of size m uses at least 2m distinct
hard carrier pairs, hence at least 4m distinct vertices.

This is a genuinely new, universally quantified numeric capacity,
not an equivalent rainbow graph bound, and imposes NO n<=2 or
n<=3 restriction. The card bound on same-target fibres and its
derived duplicate-image excess upper bound are a finite geometry
obstruction, NOT payment from Boolean holes.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- EVERY genuine NET source fibre over a single canonical diagonal
costs at least four distinct ORIGINAL vertices per source,
even in arbitrarily high Boolean dimension. -/
theorem net_collision_fibre_four_mul_card_le_vertices
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (d : Fin n → Bool) :
    4 * (netCollisionCertifiedDiagonalFibre
      C exponent hexp honeLoss d).card ≤ Fintype.card V := by
  classical
  let F := netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d
  let S := {w : Fin n → Bool //
    w ∈ netActualForwardReverseCollisionWords C exponent hexp honeLoss}
  let E := {s : S // s ∈ F}
  let f : E → V × V :=
    fun s => netCollisionForwardHardPair C exponent hexp honeLoss s.1
  let g : E → V × V :=
    fun s => netCollisionReverseHardPair C exponent hexp honeLoss s.1
  have hfinj : Function.Injective f := by
    intro s t h
    apply Subtype.ext
    by_contra hne
    have hs : netCollisionCertifiedDiagonal C exponent hexp honeLoss
        s.1 = d := (Finset.mem_filter.mp s.2).2
    have ht : netCollisionCertifiedDiagonal C exponent hexp honeLoss
        t.1 = d := (Finset.mem_filter.mp t.2).2
    exact (net_collision_distinct_same_target_forward_hard_pairs_ne
      C exponent hexp honeLoss s.1 t.1 (hs.trans ht.symm) hne) h
  have hginj : Function.Injective g := by
    intro s t h
    apply Subtype.ext
    by_contra hne
    have hs : netCollisionCertifiedDiagonal C exponent hexp honeLoss
        s.1 = d := (Finset.mem_filter.mp s.2).2
    have ht : netCollisionCertifiedDiagonal C exponent hexp honeLoss
        t.1 = d := (Finset.mem_filter.mp t.2).2
    exact (net_collision_distinct_same_target_reverse_hard_pairs_ne
      C exponent hexp honeLoss s.1 t.1 (hs.trans ht.symm) hne) h
  let A := (Finset.univ : Finset E).image f
  let B := (Finset.univ : Finset E).image g
  have hcardA : A.card = F.card := by
    dsimp [A]
    rw [Finset.card_image_of_injective _ hfinj]
    simp [E]
  have hcardB : B.card = F.card := by
    dsimp [B]
    rw [Finset.card_image_of_injective _ hginj]
    simp [E]
  have hdisj : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro pair ha hb
    obtain ⟨s, _, hs⟩ := Finset.mem_image.mp ha
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hb
    exact (net_collision_forward_reverse_hard_pairs_ne
      C exponent hexp honeLoss s.1 t.1) (hs.trans ht.symm)
  have hsub : A ∪ B ⊆ hardOverlapCarrierPairs C := by
    intro pair hpair
    rcases Finset.mem_union.mp hpair with hA | hB
    · obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hA
      rw [← hs]
      exact (net_collision_forward_hard_pair_safe
        C exponent hexp honeLoss s.1).1
    · obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hB
      rw [← hs]
      exact (net_collision_reverse_hard_pair_rigid
        C exponent hexp honeLoss s.1).1
  have hunion : (A ∪ B).card = 2 * F.card := by
    rw [Finset.card_union_of_disjoint hdisj, hcardA, hcardB]
    omega
  have hsize := hardOverlapCarrierPairs_two_mul_card_le_vertices C
  have hle := Finset.card_le_card hsub
  omega

/-- A uniform per-target bound from actual HARD carrier matching:
|F_d| <= floor(number_of_vertices/4), independent of n. -/
theorem net_collision_fibre_card_le_vertex_quarter
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (d : Fin n → Bool) :
    (netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d).card ≤
      Fintype.card V / 4 := by
  have hfour :=
    net_collision_fibre_four_mul_card_le_vertices
      C exponent hexp honeLoss d
  omega

/-- A new global upper bound on actual NET duplicate-image excess
from the FOUR-VERTICES-PER-SOURCE constraint. Every actually hit
target contributes at most floor(|V|/4)-1 duplicates. This bound
may be sharper than the dimension-dependent choose(n,2) cap,
but is not necessarily better than target-exact matching bounds. -/
theorem net_collision_duplicate_debt_le_vertex_quarter_excess
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss ≤
      ∑ d ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
        (Fintype.card V / 4 - 1) := by
  rw [net_collision_certified_duplicate_debt_eq_sum_fibre_excess
    C exponent hexp honeLoss]
  apply Finset.sum_le_sum
  intro d hd
  have hbound :=
    net_collision_fibre_card_le_vertex_quarter
      C exponent hexp honeLoss d
  omega

#print axioms net_collision_fibre_four_mul_card_le_vertices
#print axioms net_collision_fibre_card_le_vertex_quarter
#print axioms net_collision_duplicate_debt_le_vertex_quarter_excess

end OrderedEdgeColoring
end JSP000404Research
