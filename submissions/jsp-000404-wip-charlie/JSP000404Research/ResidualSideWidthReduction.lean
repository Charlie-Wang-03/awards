
import JSP000404Research.OrderedDirections
import Mathlib.Tactic

/-!
# One-unit width reduction on the two sides of the residual band

Let the normalized direction width be

  width = n + delta

with delta < 1.  Call an increasing edge high when its direction value is at
least n; in the standard (n+1)-band colouring these are exactly the residual
edges.

The ordered-direction axioms already imply a strong recursive structure.

* If u<v<w and vw is high, then uv < n-1+delta.
* If u<v<w and uv is high, then vw < n-1+delta.
* If the outer edge uw is high, at least one of uv,vw is high.

Consequently all vertices which have an outgoing high edge ("sources") have
pairwise direction width < n-1+delta; the same is true for vertices which have
an incoming high edge ("sinks").

This is the first genuine one-unit geometric width drop behind a binary Kraft
recursion.  It uses no profile guess and no deletion-gain conjecture.
-/

namespace JSP000404Research
namespace DirectionData

def HighEdge
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (u v : V) : Prop :=
  u < v ∧ (n : ℝ) ≤ D.value u v

def HighSource
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (v : V) : Prop :=
  ∃ w, v < w ∧ (n : ℝ) ≤ D.value v w

def HighSink
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (v : V) : Prop :=
  ∃ u, u < v ∧ (n : ℝ) ≤ D.value u v

/-- A high second edge forces a full one-unit drop on the first edge. -/
theorem value_lt_pred_width_of_second_high
    {V : Type*} [LinearOrder V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    {u v w : V}
    (huv : u < v) (hvw : v < w)
    (hhigh : (n : ℝ) ≤ D.value v w) :
    D.value u v < (n : ℝ) - 1 + delta := by
  have hvwUpper : D.value v w < (n : ℝ) + delta := by
    simpa [hwidth] using D.belowWidth hvw
  have huvUpper : D.value u v < (n : ℝ) + delta := by
    simpa [hwidth] using D.belowWidth huv
  have hnotHighUV : D.value u v < (n : ℝ) := by
    by_contra hnot
    have hhighUV : (n : ℝ) ≤ D.value u v := le_of_not_gt hnot
    have hdiffSmall :
        |D.value u v - D.value v w| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    exact (not_lt_of_ge (D.middleSeparated huv hvw)) hdiffSmall
  have horder : D.value u v ≤ D.value v w := by
    linarith
  have hsep := D.middleSeparated huv hvw
  rw [abs_of_nonpos (sub_nonpos.mpr horder)] at hsep
  linarith

/-- Symmetric one-unit drop when the first edge is high. -/
theorem value_lt_pred_width_of_first_high
    {V : Type*} [LinearOrder V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    {u v w : V}
    (huv : u < v) (hvw : v < w)
    (hhigh : (n : ℝ) ≤ D.value u v) :
    D.value v w < (n : ℝ) - 1 + delta := by
  have huvUpper : D.value u v < (n : ℝ) + delta := by
    simpa [hwidth] using D.belowWidth huv
  have hvwUpper : D.value v w < (n : ℝ) + delta := by
    simpa [hwidth] using D.belowWidth hvw
  have hnotHighVW : D.value v w < (n : ℝ) := by
    by_contra hnot
    have hhighVW : (n : ℝ) ≤ D.value v w := le_of_not_gt hnot
    have hdiffSmall :
        |D.value u v - D.value v w| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    exact (not_lt_of_ge (D.middleSeparated huv hvw)) hdiffSmall
  have horder : D.value v w ≤ D.value u v := by
    linarith
  have hsep := D.middleSeparated huv hvw
  rw [abs_of_nonneg (sub_nonneg.mpr horder)] at hsep
  linarith

/-- A high outer edge cannot jump over a vertex with both adjacent edges
below the high threshold. -/
theorem first_high_or_second_high_of_outer_high
    {V : Type*} [LinearOrder V]
    {width : ℝ} {n : ℕ}
    (D : DirectionData V width)
    {u v w : V}
    (huv : u < v) (hvw : v < w)
    (houter : (n : ℝ) ≤ D.value u w) :
    (n : ℝ) ≤ D.value u v ∨
      (n : ℝ) ≤ D.value v w := by
  rcases D.between huv hvw with hforward | hreverse
  · by_cases hhigh : (n : ℝ) ≤ D.value v w
    · exact Or.inr hhigh
    · have hvwLow : D.value v w < (n : ℝ) := lt_of_not_ge hhigh
      have huwLe : D.value u w ≤ D.value v w := hforward.2
      linarith
  · by_cases hhigh : (n : ℝ) ≤ D.value u v
    · exact Or.inl hhigh
    · have huvLow : D.value u v < (n : ℝ) := lt_of_not_ge hhigh
      have huwLe : D.value u w ≤ D.value u v := hreverse.2
      linarith

/-- Two high sources already form a configuration of one-unit smaller
direction width. -/
theorem source_pair_value_lt_pred_width
    {V : Type*} [LinearOrder V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    {u v : V}
    (huv : u < v)
    (_hu : HighSource D n u)
    (hv : HighSource D n v) :
    D.value u v < (n : ℝ) - 1 + delta := by
  obtain ⟨w, hvw, hhigh⟩ := hv
  exact value_lt_pred_width_of_second_high
    D hwidth hdelta huv hvw hhigh

/-- Two high sinks also have one-unit smaller pairwise direction width. -/
theorem sink_pair_value_lt_pred_width
    {V : Type*} [LinearOrder V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    {u v : V}
    (huv : u < v)
    (hu : HighSink D n u)
    (_hv : HighSink D n v) :
    D.value u v < (n : ℝ) - 1 + delta := by
  obtain ⟨a, hau, hhigh⟩ := hu
  exact value_lt_pred_width_of_first_high
    D hwidth hdelta hau huv hhigh

/-- No high edge can contain a vertex which is neither a high source nor a
high sink relative to the two adjacent subedges. -/
theorem middle_of_high_edge_has_adjacent_high
    {V : Type*} [LinearOrder V]
    {width : ℝ} {n : ℕ}
    (D : DirectionData V width)
    {u v w : V}
    (huv : u < v) (hvw : v < w)
    (houter : (n : ℝ) ≤ D.value u w) :
    HighSource D n v ∨ HighSink D n v := by
  rcases first_high_or_second_high_of_outer_high
      D huv hvw houter with huvHigh | hvwHigh
  · exact Or.inr ⟨u, huv, huvHigh⟩
  · exact Or.inl ⟨w, hvw, hvwHigh⟩


/-- A vertex cannot simultaneously receive and emit high edges when the high
band has width < 1. -/
theorem not_highSource_and_highSink
    {V : Type*} [LinearOrder V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (v : V) :
    ¬ (HighSource D n v ∧ HighSink D n v) := by
  rintro ⟨⟨w, hvw, hvwHigh⟩, ⟨u, huv, huvHigh⟩⟩
  have huvUpper : D.value u v < (n : ℝ) + delta := by
    simpa [hwidth] using D.belowWidth huv
  have hvwUpper : D.value v w < (n : ℝ) + delta := by
    simpa [hwidth] using D.belowWidth hvw
  have hsmall :
      |D.value u v - D.value v w| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  exact (not_lt_of_ge (D.middleSeparated huv hvw)) hsmall

/-- Every high edge points from a high source to a high sink. -/
theorem highEdge_gives_source_sink
    {V : Type*} [LinearOrder V]
    {width : ℝ} {n : ℕ}
    (D : DirectionData V width)
    {u v : V}
    (huv : u < v)
    (hhigh : (n : ℝ) ≤ D.value u v) :
    HighSource D n u ∧ HighSink D n v :=
  ⟨⟨v, huv, hhigh⟩, ⟨u, huv, hhigh⟩⟩

/-- An interior vertex of a high edge belongs to exactly one of the two high
sides. -/
theorem middle_of_high_edge_exclusive_side
    {V : Type*} [LinearOrder V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    {u v w : V}
    (huv : u < v) (hvw : v < w)
    (houter : (n : ℝ) ≤ D.value u w) :
    (HighSource D n v ∨ HighSink D n v) ∧
      ¬ (HighSource D n v ∧ HighSink D n v) := by
  exact ⟨middle_of_high_edge_has_adjacent_high D huv hvw houter,
    not_highSource_and_highSink D hwidth hdelta v⟩

/-- Interleaving high edges are joined by a cross high edge. -/
theorem interleaving_high_edges_cross
    {V : Type*} [LinearOrder V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    {u x v y : V}
    (hux : u < x) (hxv : x < v) (hvy : v < y)
    (huvHigh : (n : ℝ) ≤ D.value u v)
    (hxyHigh : (n : ℝ) ≤ D.value x y) :
    (n : ℝ) ≤ D.value x v := by
  have hxy : x < y := hxv.trans hvy
  have hxSource : HighSource D n x :=
    ⟨y, hxy, hxyHigh⟩
  rcases first_high_or_second_high_of_outer_high
      D hux hxv huvHigh with huxHigh | hxvHigh
  · have hxSink : HighSink D n x :=
      ⟨u, hux, huxHigh⟩
    exact False.elim
      ((not_highSource_and_highSink
        D hwidth hdelta x) ⟨hxSource, hxSink⟩)
  · exact hxvHigh

/-- Nested high edges are also connected by a cross high edge. -/
theorem nested_high_edges_cross
    {V : Type*} [LinearOrder V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    {u x y v : V}
    (hux : u < x) (hxy : x < y) (hyv : y < v)
    (huvHigh : (n : ℝ) ≤ D.value u v)
    (hxyHigh : (n : ℝ) ≤ D.value x y) :
    (n : ℝ) ≤ D.value x v := by
  have hxv : x < v := hxy.trans hyv
  have hxSource : HighSource D n x :=
    ⟨y, hxy, hxyHigh⟩
  rcases first_high_or_second_high_of_outer_high
      D hux hxv huvHigh with huxHigh | hxvHigh
  · have hxSink : HighSink D n x :=
      ⟨u, hux, huxHigh⟩
    exact False.elim
      ((not_highSource_and_highSink
        D hwidth hdelta x) ⟨hxSource, hxSink⟩)
  · exact hxvHigh

#print axioms value_lt_pred_width_of_second_high
#print axioms value_lt_pred_width_of_first_high
#print axioms first_high_or_second_high_of_outer_high
#print axioms source_pair_value_lt_pred_width
#print axioms sink_pair_value_lt_pred_width
#print axioms middle_of_high_edge_has_adjacent_high

end DirectionData
end JSP000404Research
