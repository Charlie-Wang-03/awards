import JSP000404Research.AdaptiveDeficitCapacity
import Mathlib.Tactic

/-!
# Local-palette certificates for adaptive Sendov colouring

The remaining geometric problem is easier to state with vertex-local palettes.

For each vertex v choose a finite set of global colours palette(v), with
cardinality at most the Sendov deficit ell(v).  Every increasing edge v<w must
receive one colour lying in both endpoint palettes.  Finally, if two
consecutive increasing edges receive the same colour, their normalized
directions must be less than one unit apart.

These hypotheses immediately produce an AdaptiveColoring.  Since every colour
incident to v belongs to palette(v), the active-colour count is at most ell(v).
The weighted Hansel / adaptive-capacity theorem then gives the sharp dyadic
bound.

Thus geometry no longer has to construct Boolean words or a Kraft tree
directly.  It may instead construct shared local palette slots.
-/

namespace JSP000404Research
namespace DirectionData

structure LocalPaletteCertificate
    {V : Type*} [LinearOrder V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ)
    (ell : V → ℕ) where
  palette : V → Finset (Fin n)
  color : V → V → Fin n
  palette_card_le : ∀ v, (palette v).card ≤ ell v
  edge_mem_left :
    ∀ {v w : V}, v < w → color v w ∈ palette v
  edge_mem_right :
    ∀ {v w : V}, v < w → color v w ∈ palette w
  sameColor_close :
    ∀ {a v w : V}, a < v → v < w →
      color a v = color v w →
      |D.value a v - D.value v w| < 1

namespace LocalPaletteCertificate

noncomputable def toAdaptiveColoring
    {V : Type*} [LinearOrder V]
    {width : ℝ} {n : ℕ}
    {D : DirectionData V width}
    {ell : V → ℕ}
    (C : LocalPaletteCertificate D n ell) :
    AdaptiveColoring D n where
  color := C.color
  sameColor_close := C.sameColor_close

/-- Every active colour at v belongs to the prescribed local palette. -/
theorem active_subset_palette
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ} {n : ℕ}
    {D : DirectionData V width}
    {ell : V → ℕ}
    (C : LocalPaletteCertificate D n ell)
    (v : V) :
    OrderedEdgeColoring.active
        C.toAdaptiveColoring.toOrderedEdgeColoring v
      ⊆ C.palette v := by
  classical
  intro c hc
  simp only [OrderedEdgeColoring.active, Finset.mem_filter,
    Finset.mem_univ, true_and] at hc
  rcases hc with ⟨a, hav, hcol⟩ | ⟨w, hvw, hcol⟩
  · have hmem := C.edge_mem_right hav
    simpa [toAdaptiveColoring, hcol] using hmem
  · have hmem := C.edge_mem_left hvw
    simpa [toAdaptiveColoring, hcol] using hmem

/-- Hence the adaptive active palette is bounded by the prescribed deficit. -/
theorem active_card_le_deficit
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ} {n : ℕ}
    {D : DirectionData V width}
    {ell : V → ℕ}
    (C : LocalPaletteCertificate D n ell)
    (v : V) :
    (OrderedEdgeColoring.active
      C.toAdaptiveColoring.toOrderedEdgeColoring v).card ≤ ell v := by
  exact (Finset.card_le_card (C.active_subset_palette v)).trans
    (C.palette_card_le v)

/-- Local palettes immediately close the weighted deficit capacity. -/
theorem deficit_capacity
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ} {n : ℕ}
    {D : DirectionData V width}
    {ell : V → ℕ}
    (C : LocalPaletteCertificate D n ell) :
    (∑ v, 2 ^ (n - ell v)) ≤ 2 ^ n := by
  exact AdaptiveColoring.deficit_capacity
    C.toAdaptiveColoring ell C.active_card_le_deficit

/-- Exponent form used in Sendov Lemma 4.12. -/
theorem exponent_capacity
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ} {n : ℕ}
    {D : DirectionData V width}
    (exponent ell : V → ℕ)
    (C : LocalPaletteCertificate D n ell)
    (hexp : ∀ v, exponent v ≤ n)
    (hell : ∀ v, ell v = n - exponent v) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n := by
  exact AdaptiveColoring.exponent_capacity
    C.toAdaptiveColoring exponent ell
    hexp hell C.active_card_le_deficit

#print axioms active_subset_palette
#print axioms active_card_le_deficit
#print axioms deficit_capacity
#print axioms exponent_capacity

end LocalPaletteCertificate
end DirectionData
end JSP000404Research
