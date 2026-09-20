import JSP000404Research.BinaryEdgePartition
import JSP000404Research.OrderedBandCode
import JSP000404Research.WrapBipartite
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

/-!
# Fixed-phase lower-branch capacity

Fix the direction cut at zero and write the normalized width as

  width = n + delta.

Use exactly n Boolean colours:

* colour 0 is the merged wrap band [0,1) union [n,width);
* colours 1,...,n-1 are the ordinary unit bands [m,m+1).

If the wrap graph is triangle-free, WrapBipartite supplies its Boolean
vertex colour. Every ordinary band uses the canonical incoming/outgoing bit
from OrderedBandCode.

Every increasing edge belongs to one of these n colours, and its endpoints
have opposite bits in that colour. Hence we obtain a BinaryEdgePartition
and the Hansel bound |V| <= 2^n.

Thus the only remaining geometric issue for the lower branch is to find a
phase (a projective direction cut) for which the corresponding wrap graph is
triangle-free.
-/

namespace JSP000404Research
namespace DirectionData

noncomputable def fixedPhaseBit
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) (n : ℕ) :
    V → Fin n → Bool :=
  fun v c =>
    if c.val = 0 then
      wrapVertexColor D n v
    else
      bandBit D n v c

theorem exists_fixedPhase_separating_color
    {V : Type*} [LinearOrder V] {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (hn : 1 ≤ n)
    (htri : WrapTriangleFree D n)
    {i j : V} (hij : i < j) :
    ∃ c : Fin n,
      fixedPhaseBit D n i c ≠ fixedPhaseBit D n j c := by
  have hnpos : 0 < n := by omega
  let c0 : Fin n := ⟨0, hnpos⟩
  by_cases hlow : D.value i j < 1
  · have hadj : (wrapGraph D n).Adj i j := by
      refine ⟨ne_of_lt hij, Or.inl ?_⟩
      simpa [EdgeLow, edgeValue, hij] using hlow
    refine ⟨c0, ?_⟩
    have hcol :=
      wrapVertexColor_ne_of_adj D hwidth hdelta hn htri hadj
    simpa [fixedPhaseBit, c0] using hcol
  · by_cases hhigh : (n : ℝ) ≤ D.value i j
    · have hadj : (wrapGraph D n).Adj i j := by
        refine ⟨ne_of_lt hij, Or.inr ?_⟩
        simpa [EdgeHigh, edgeValue, hij] using hhigh
      refine ⟨c0, ?_⟩
      have hcol :=
        wrapVertexColor_ne_of_adj D hwidth hdelta hn htri hadj
      simpa [fixedPhaseBit, c0] using hcol
    · have hx0 : 0 ≤ D.value i j := D.nonnegative hij
      have hx1 : (1 : ℝ) ≤ D.value i j := le_of_not_gt hlow
      have hxn : D.value i j < (n : ℝ) := lt_of_not_ge hhigh
      have hm_lt : Nat.floor (D.value i j) < n :=
        (Nat.floor_lt hx0).2 hxn
      let m : Fin n := ⟨Nat.floor (D.value i j), hm_lt⟩
      have hmlo : (m : ℝ) ≤ D.value i j := by
        simpa [m] using Nat.floor_le hx0
      have hmhi : D.value i j < (m : ℝ) + 1 := by
        simpa [m] using Nat.lt_floor_add_one (D.value i j)
      have hmpos : 1 ≤ Nat.floor (D.value i j) := by
        exact Nat.le_floor hx1
      have hmne : m.val ≠ 0 := by
        dsimp [m]
        omega
      refine ⟨m, ?_⟩
      have hbit :=
        bandBit_ne_of_edge_mem_band D n hij m hmlo hmhi
      simpa [fixedPhaseBit, hmne] using hbit

/-- Deterministic merged-band colour: wrap directions receive colour zero,
while a middle direction x in [1,n) receives floor(x).  Values on
non-increasing pairs are irrelevant. -/
noncomputable def fixedPhaseEdgeColor
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) (n : ℕ)
    (hn : 1 ≤ n) :
    V → V → Fin n :=
  fun u v =>
    if h : u < v then
      if hwrap : D.value u v < 1 ∨ (n : ℝ) ≤ D.value u v then
        ⟨0, by omega⟩
      else
        ⟨Nat.floor (D.value u v), by
          have hx0 : 0 ≤ D.value u v := D.nonnegative h
          have hxn : D.value u v < (n : ℝ) := by
            push_neg at hwrap
            exact hwrap.2
          exact (Nat.floor_lt hx0).2 hxn⟩
    else
      ⟨0, by omega⟩

/-- On a wrap edge the deterministic colour is zero. -/
theorem fixedPhaseEdgeColor_eq_zero_of_wrap
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) {n : ℕ}
    (hn : 1 ≤ n)
    {u v : V} (huv : u < v)
    (hwrap : D.value u v < 1 ∨ (n : ℝ) ≤ D.value u v) :
    (fixedPhaseEdgeColor D n hn u v).val = 0 := by
  simp [fixedPhaseEdgeColor, huv, hwrap]

/-- On a middle edge the deterministic colour is its natural unit-band floor. -/
theorem fixedPhaseEdgeColor_eq_floor_of_middle
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) {n : ℕ}
    (hn : 1 ≤ n)
    {u v : V} (huv : u < v)
    (hmid : 1 ≤ D.value u v)
    (hhigh : D.value u v < (n : ℝ)) :
    (fixedPhaseEdgeColor D n hn u v).val =
      Nat.floor (D.value u v) := by
  have hnot :
      ¬ (D.value u v < 1 ∨ (n : ℝ) ≤ D.value u v) := by
    push_neg
    exact ⟨hmid, hhigh⟩
  simp [fixedPhaseEdgeColor, huv, hnot]

/-- The deterministic merged-band colour always separates the fixed-phase
Boolean endpoint bits when the wrap graph is triangle-free. -/
theorem fixedPhaseEdgeColor_bit_ne
    {V : Type*} [LinearOrder V] {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (hn : 1 ≤ n)
    (htri : WrapTriangleFree D n)
    {u v : V} (huv : u < v) :
    fixedPhaseBit D n u (fixedPhaseEdgeColor D n hn u v) ≠
      fixedPhaseBit D n v (fixedPhaseEdgeColor D n hn u v) := by
  by_cases hlow : D.value u v < 1
  · have hadj : (wrapGraph D n).Adj u v := by
      refine ⟨ne_of_lt huv, Or.inl ?_⟩
      simpa [EdgeLow, edgeValue, huv] using hlow
    have hcol :=
      wrapVertexColor_ne_of_adj D hwidth hdelta hn htri hadj
    have hc0 :
        (fixedPhaseEdgeColor D n hn u v).val = 0 :=
      fixedPhaseEdgeColor_eq_zero_of_wrap
        D hn huv (Or.inl hlow)
    simpa [fixedPhaseBit, hc0] using hcol
  · by_cases hhigh : (n : ℝ) ≤ D.value u v
    · have hadj : (wrapGraph D n).Adj u v := by
        refine ⟨ne_of_lt huv, Or.inr ?_⟩
        simpa [EdgeHigh, edgeValue, huv] using hhigh
      have hcol :=
        wrapVertexColor_ne_of_adj D hwidth hdelta hn htri hadj
      have hc0 :
          (fixedPhaseEdgeColor D n hn u v).val = 0 :=
        fixedPhaseEdgeColor_eq_zero_of_wrap
          D hn huv (Or.inr hhigh)
      simpa [fixedPhaseBit, hc0] using hcol
    · have hmid : (1 : ℝ) ≤ D.value u v := le_of_not_gt hlow
      have htop : D.value u v < (n : ℝ) := lt_of_not_ge hhigh
      let m := fixedPhaseEdgeColor D n hn u v
      have hmval : m.val = Nat.floor (D.value u v) :=
        fixedPhaseEdgeColor_eq_floor_of_middle
          D hn huv hmid htop
      have hmpos : m.val ≠ 0 := by
        rw [hmval]
        have hf : 1 ≤ Nat.floor (D.value u v) :=
          Nat.le_floor hmid
        omega
      have hmlo : (m : ℝ) ≤ D.value u v := by
        rw [show (m : ℝ) = (Nat.floor (D.value u v) : ℕ) by
          exact_mod_cast hmval]
        exact Nat.floor_le (D.nonnegative huv)
      have hmhi : D.value u v < (m : ℝ) + 1 := by
        rw [show (m : ℝ) = (Nat.floor (D.value u v) : ℕ) by
          exact_mod_cast hmval]
        exact Nat.lt_floor_add_one _
      have hbit :=
        bandBit_ne_of_edge_mem_band D n huv m hmlo hmhi
      simpa [fixedPhaseBit, hmpos, m] using hbit

/-- Deterministic version of the fixed-phase binary edge partition.  Unlike
the earlier choice-based construction, this one exposes the actual merged-band
colour of every edge and can therefore be used for local active-palette
counting. -/
noncomputable def canonicalFixedPhasePartition
    {V : Type*} [LinearOrder V] {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (hn : 1 ≤ n)
    (htri : WrapTriangleFree D n) :
    BinaryEdgePartition V n where
  edgeColor := fixedPhaseEdgeColor D n hn
  bit := fixedPhaseBit D n
  proper := by
    intro v w hvw
    exact fixedPhaseEdgeColor_bit_ne
      D hwidth hdelta hn htri hvw

noncomputable def fixedPhasePartition
    {V : Type*} [LinearOrder V] {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (hn : 1 ≤ n)
    (htri : WrapTriangleFree D n) :
    BinaryEdgePartition V n where
  edgeColor v w :=
    if h : v < w then
      Classical.choose
        (exists_fixedPhase_separating_color
          D hwidth hdelta hn htri h)
    else
      ⟨0, by omega⟩
  bit := fixedPhaseBit D n
  proper := by
    intro v w hvw
    simp only [dite_true, hvw]
    exact Classical.choose_spec
      (exists_fixedPhase_separating_color
        D hwidth hdelta hn htri hvw)

theorem card_le_two_pow_of_wrapTriangleFree
    {V : Type*} [LinearOrder V] [Fintype V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (hn : 1 ≤ n)
    (htri : WrapTriangleFree D n) :
    Fintype.card V ≤ 2 ^ n := by
  exact BinaryEdgePartition.card_le_two_pow
    (fixedPhasePartition D hwidth hdelta hn htri)

#print axioms exists_fixedPhase_separating_color
#print axioms fixedPhasePartition
#print axioms card_le_two_pow_of_wrapTriangleFree

end DirectionData
end JSP000404Research
