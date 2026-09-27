import JSP000404Research.SixPointMergedEqualityRoot
import Mathlib.Tactic

/-!
# A repeated non-root colour at every exceptional minimum

In the exact root-factorized six-point equality terminal, fix one exceptional
minimum b.  There are four vertices distinct from both top and b.  Every edge
from b to one of those four vertices avoids the unique top root colour, hence
its incident colour lies in

  active(b) \ {root}.

For an exceptional minimum this reduced active set has cardinality three.
Therefore two of the four minimum--minimum incident edges at b have the same
colour.

The statement is purely combinatorial and does not yet use projective bands.
-/

namespace JSP000404Research

open BinaryEdgePartition

noncomputable def localIncidentColor
    {V : Type*} [LinearOrder V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (i j : V) : Fin k :=
  if h : i < j then P.edgeColor i j else P.edgeColor j i

theorem localIncidentColor_mem_active
    {V : Type*} [LinearOrder V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    {i j : V}
    (hij : i ≠ j) :
    localIncidentColor P i j ∈ active P i := by
  unfold localIncidentColor
  split_ifs with h
  · exact edgeColor_mem_active_lower P h
  · have hji : j < i := by
      rcases lt_or_gt_of_ne hij with hij' | hji'
      · exact False.elim (h hij')
      · exact hji'
    exact edgeColor_mem_active_upper P hji

theorem localIncidentColor_ne_root_of_nonTop
    {V : Type*} [LinearOrder V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    {top root i j}
    (hit : i ≠ top)
    (hjt : j ≠ top)
    (hij : i ≠ j)
    (hrootEdges :
      ∀ {u v : V}, u < v →
        u ≠ top → v ≠ top →
        P.edgeColor u v ≠ root) :
    localIncidentColor P i j ≠ root := by
  unfold localIncidentColor
  split_ifs with h
  · exact hrootEdges h hit hjt
  · have hji : j < i := by
      rcases lt_or_gt_of_ne hij with hij' | hji'
      · exact False.elim (h hij')
      · exact hji'
    exact hrootEdges hji hjt hit

theorem four_nonTop_edges_three_nonroot_colours_repeat
    {V : Type*} [LinearOrder V] [Fintype V]
    {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top b : V)
    (root : Fin k)
    (hbt : b ≠ top)
    (hcard : Fintype.card V = 6)
    (hrootEdges :
      ∀ {u v : V}, u < v →
        u ≠ top → v ≠ top →
        P.edgeColor u v ≠ root)
    (hreduced :
      ((active P b).erase root).card = 3) :
    ∃ x y : V,
      x ≠ top ∧ x ≠ b ∧
      y ≠ top ∧ y ≠ b ∧
      x ≠ y ∧
      localIncidentColor P b x =
        localIncidentColor P b y := by
  classical
  let S : Finset V :=
    ((Finset.univ.erase top).erase b)
  have hbMem :
      b ∈ (Finset.univ.erase top : Finset V) := by
    simp [hbt]
  have hScard : S.card = 4 := by
    dsimp [S]
    rw [Finset.card_erase_of_mem hbMem,
        Finset.card_erase_of_mem (Finset.mem_univ top)]
    simp [hcard]
  let f : V → Fin k := fun v => localIncidentColor P b v
  have hfmem :
      ∀ v ∈ S, f v ∈ (active P b).erase root := by
    intro v hv
    have hvErase := Finset.mem_erase.mp hv
    have hvTopErase := Finset.mem_erase.mp hvErase.2
    have hvb : v ≠ b := hvErase.1
    have hvt : v ≠ top := hvTopErase.1
    apply Finset.mem_erase.mpr
    constructor
    · exact localIncidentColor_ne_root_of_nonTop
        P hbt hvt hvb.symm hrootEdges
    · exact localIncidentColor_mem_active P hvb.symm
  by_contra hnone
  push_neg at hnone
  have hinj : Set.InjOn f (S : Set V) := by
    intro x hx y hy hxy
    by_contra hne
    exact (hnone x
      (by
        have h := Finset.mem_erase.mp hx
        exact (Finset.mem_erase.mp h.2).1)
      (Finset.mem_erase.mp hx).1
      y
      (by
        have h := Finset.mem_erase.mp hy
        exact (Finset.mem_erase.mp h.2).1)
      (Finset.mem_erase.mp hy).1
      hne) hxy
  have hcardImage :
      (S.image f).card = S.card :=
    Finset.card_image_iff.mpr hinj
  have hsubset :
      S.image f ⊆ (active P b).erase root := by
    intro c hc
    obtain ⟨v, hvS, rfl⟩ := Finset.mem_image.mp hc
    exact hfmem v hvS
  have hle :
      (S.image f).card ≤ ((active P b).erase root).card :=
    Finset.card_le_card hsubset
  rw [hcardImage, hScard, hreduced] at hle
  omega

#print axioms localIncidentColor_mem_active
#print axioms localIncidentColor_ne_root_of_nonTop
#print axioms four_nonTop_edges_three_nonroot_colours_repeat

end JSP000404Research
