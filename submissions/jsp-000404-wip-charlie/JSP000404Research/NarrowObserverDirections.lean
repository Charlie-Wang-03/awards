import JSP000404Research.DirectionRestriction
import JSP000404Research.OrderedEdgeColor
import Mathlib.Tactic

/-!
# Direction intervals forced by narrow observers

The real edge values in `DirectionData` use one angle unit for the forbidden
supplement. A low observer has every ray to the selected set in the first unit
interval. A high observer has them in the last unit interval.

Along the selected order, the low observer's bearings increase and the high
observer's bearings decrease. With both observers, the first selected point
therefore controls every later edge. Its two incoming rays differ by at most
`width - 1`, leaving an interval of length at most `width - 3` for those edges.

The interval colouring below uses only middle separation. It does not assert
that restricting edge values to a shorter interval gives `DirectionData` at a
smaller width. The cardinality theorems retain explicit observer hypotheses.
-/

namespace JSP000404Research

/-- Equal floor bands force distance strictly less than one. -/
theorem floor_ne_of_unit_separated {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hsep : 1 ≤ |x - y|) : Nat.floor x ≠ Nat.floor y := by
  intro hf
  have hxl := Nat.floor_le hx
  have hxu := Nat.lt_floor_add_one x
  have hyl := Nat.floor_le hy
  have hyu := Nat.lt_floor_add_one y
  rw [hf] at hxl hxu
  have hsmall : |x - y| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  exact (not_lt_of_ge hsep) hsmall

/-- Unit bands for edge values in an arbitrary translated interval. -/
noncomputable def edgeIntervalColoring
    {V : Type*} [LinearOrder V]
    (value : V → V → ℝ) (lower : ℝ) (k : ℕ) (hk : 0 < k)
    (hinterval : ∀ i j, i < j → lower ≤ value i j ∧ value i j < lower + k)
    (hsep : ∀ i j l, i < j → j < l → 1 ≤ |value i j - value j l|) :
    OrderedEdgeColoring V k := by
  classical
  let color : V → V → Fin k := fun i j ↦
    if h : i < j then
      ⟨Nat.floor (value i j - lower),
        (Nat.floor_lt (by linarith [(hinterval i j h).1])).mpr
          (by linarith [(hinterval i j h).2])⟩
    else ⟨0, hk⟩
  exact
    { color := color
      noMonoTwoPath := by
        intro i j l hij hjl heq
        have hf : Nat.floor (value i j - lower) = Nat.floor (value j l - lower) := by
          simpa [color, hij, hjl] using congrArg Fin.val heq
        have hi0 : 0 ≤ value i j - lower := by linarith [(hinterval i j hij).1]
        have hj0 : 0 ≤ value j l - lower := by linarith [(hinterval j l hjl).1]
        apply floor_ne_of_unit_separated hi0 hj0 _ hf
        simpa only [sub_sub_sub_cancel_right] using hsep i j l hij hjl }

/-- Middle-separated real edge values in an interval of length `k` give `k` bits. -/
theorem card_le_two_pow_of_edge_interval
    {V : Type*} [LinearOrder V] [Fintype V]
    (value : V → V → ℝ) (lower : ℝ) (k : ℕ)
    (hinterval : ∀ i j, i < j → lower ≤ value i j ∧ value i j < lower + k)
    (hsep : ∀ i j l, i < j → j < l → 1 ≤ |value i j - value j l|) :
    Fintype.card V ≤ 2 ^ k := by
  classical
  by_cases hk : k = 0
  · subst k
    simp only [pow_zero]
    apply Fintype.card_le_one_iff_subsingleton.mpr
    refine ⟨fun i j ↦ ?_⟩
    rcases lt_trichotomy i j with hij | hij | hji
    · obtain ⟨hlo, hhi⟩ := hinterval i j hij
      simp only [Nat.cast_zero, add_zero] at hhi
      exact False.elim (not_lt_of_ge hlo hhi)
    · exact hij
    · obtain ⟨hlo, hhi⟩ := hinterval j i hji
      simp only [Nat.cast_zero, add_zero] at hhi
      exact False.elim (not_lt_of_ge hlo hhi)
  exact OrderedEdgeColoring.card_le_two_pow
    (edgeIntervalColoring value lower k (Nat.pos_of_ne_zero hk) hinterval hsep)

namespace DirectionData

/-- A low observer confines all selected edges to a common interval. -/
theorem low_observer_edge_interval
    {V : Type*} [LinearOrder V] {width : ℝ} (D : DirectionData V width)
    {a i j : V} {lo hi : ℝ} (hai : a < i) (hij : i < j)
    (hlower : lo ≤ D.value a i) (hupper : D.value a j ≤ hi)
    (hlow : D.value a i < 1) :
    lo + 1 ≤ D.value i j ∧ D.value i j ≤ hi + width - 1 := by
  have hnonneg := D.nonnegative hij
  have hsep := D.middleSeparated hai hij
  have hgap := neg_le_of_abs_le (D.lastGap hai hij)
  rcases le_total (D.value a i) (D.value i j) with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hsep
    constructor <;> linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hsep
    exfalso
    linarith

/-- The single-observer cardinality bound keeps the cone width in the budget. -/
theorem low_observer_card_le
    {V : Type*} [LinearOrder V] {width : ℝ} (D : DirectionData V width)
    (S : Finset V) {a : V} {lo hi : ℝ}
    (hbefore : ∀ i ∈ S, a < i)
    (hview : ∀ i ∈ S, lo ≤ D.value a i ∧ D.value a i ≤ hi)
    (hhi : hi < 1) (k : ℕ) (hwidth : width - 2 + (hi - lo) < k) :
    S.card ≤ 2 ^ k := by
  classical
  have hbound := card_le_two_pow_of_edge_interval
    (fun i j : S ↦ D.value i.1 j.1) (lo + 1) k
    (fun i j hij ↦ by
      have h := D.low_observer_edge_interval (hbefore i.1 i.2) hij
        (hview i.1 i.2).1 (hview j.1 j.2).2 ((hview i.1 i.2).2.trans_lt hhi)
      exact ⟨h.1, by linarith [h.2]⟩)
    (fun i j l hij hjl ↦ D.middleSeparated hij hjl)
  simpa using hbound

/-- A first-band incoming ray forces the next edge above it by one unit. -/
theorem edge_above_low_observer
    {V : Type*} [LinearOrder V] {width : ℝ} (D : DirectionData V width)
    {a i j : V} (hai : a < i) (hij : i < j) (hlow : D.value a i < 1) :
    D.value a i + 1 ≤ D.value i j := by
  have hnonneg := D.nonnegative hij
  have hsep := D.middleSeparated hai hij
  rcases le_total (D.value a i) (D.value i j) with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hsep
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hsep
    linarith

/-- Low observer bearings increase along a selected sequence. -/
theorem low_observer_monotone
    {V : Type*} [LinearOrder V] {width : ℝ} (D : DirectionData V width)
    {a i j : V} (hai : a < i) (hij : i < j) (hlow : D.value a i < 1) :
    D.value a i ≤ D.value a j := by
  have hnext := D.edge_above_low_observer hai hij hlow
  rcases D.between hai hij with h | h
  · exact h.1
  · linarith [h.1, h.2]

/-- A last-band incoming ray forces the next edge below it by one unit. -/
theorem edge_below_high_observer
    {V : Type*} [LinearOrder V] {width : ℝ} (D : DirectionData V width)
    {b i j : V} (hbi : b < i) (hij : i < j) (hhigh : width - 1 < D.value b i) :
    D.value i j ≤ D.value b i - 1 := by
  have hbound := D.belowWidth hij
  have hsep := D.middleSeparated hbi hij
  rcases le_total (D.value b i) (D.value i j) with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hsep
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hsep
    linarith

/-- High observer bearings decrease along a selected sequence. -/
theorem high_observer_antitone
    {V : Type*} [LinearOrder V] {width : ℝ} (D : DirectionData V width)
    {b i j : V} (hbi : b < i) (hij : i < j) (hhigh : width - 1 < D.value b i) :
    D.value b j ≤ D.value b i := by
  have hnext := D.edge_below_high_observer hbi hij hhigh
  rcases D.between hbi hij with h | h
  · linarith [h.1, h.2]
  · exact h.2

/-- Two observers confine every selected edge using the first selected vertex. -/
theorem two_observer_edge_interval
    {V : Type*} [LinearOrder V] {width : ℝ} (D : DirectionData V width)
    {a b r i j : V} (hab : a < b) (hbr : b < r) (hri : r ≤ i) (hij : i < j)
    (hlowr : D.value a r < 1) (hlowi : D.value a i < 1)
    (hhighr : width - 1 < D.value b r) (hhighi : width - 1 < D.value b i) :
    D.value a r + 1 ≤ D.value i j ∧
      D.value i j ≤ D.value a r + 1 + (width - 3) := by
  have hbi : b < i := hbr.trans_le hri
  have hai : a < i := hab.trans hbi
  have hlow := D.edge_above_low_observer hai hij hlowi
  have hhigh := D.edge_below_high_observer hbi hij hhighi
  have hmono : D.value a r ≤ D.value a i := by
    rcases hri.eq_or_lt with h | h
    · subst i
      exact le_rfl
    · exact D.low_observer_monotone (hab.trans hbr) h hlowr
  have hanti : D.value b i ≤ D.value b r := by
    rcases hri.eq_or_lt with h | h
    · subst i
      exact le_rfl
    · exact D.high_observer_antitone hbr h hhighr
  have hgap := D.lastGap hab hbr
  have hgap' := neg_le_of_abs_le hgap
  constructor <;> linarith

/-- Cardinality bound for any subset with common low and high observers. -/
theorem two_observer_card_le
    {V : Type*} [LinearOrder V] {width : ℝ} (D : DirectionData V width)
    (S : Finset V) {a b : V} (hab : a < b)
    (hbefore : ∀ i ∈ S, b < i)
    (hlow : ∀ i ∈ S, D.value a i < 1)
    (hhigh : ∀ i ∈ S, width - 1 < D.value b i)
    (k : ℕ) (hwidth : width - 3 < k) : S.card ≤ 2 ^ k := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  let r := S.min' hS
  have hr : r ∈ S := Finset.min'_mem S hS
  have hbound := card_le_two_pow_of_edge_interval
    (fun i j : S ↦ D.value i.1 j.1) (D.value a r + 1) k
    (fun i j hij ↦ by
      have h := D.two_observer_edge_interval hab (hbefore r hr)
        (Finset.min'_le S i.1 i.2) hij (hlow r hr) (hlow i.1 i.2)
        (hhigh r hr) (hhigh i.1 i.2)
      exact ⟨h.1, by linarith [h.2]⟩)
    (fun i j l hij hjl ↦ D.middleSeparated hij hjl)
  simpa using hbound

end DirectionData

#print axioms card_le_two_pow_of_edge_interval
#print axioms DirectionData.low_observer_card_le
#print axioms DirectionData.two_observer_edge_interval
#print axioms DirectionData.two_observer_card_le

end JSP000404Research
