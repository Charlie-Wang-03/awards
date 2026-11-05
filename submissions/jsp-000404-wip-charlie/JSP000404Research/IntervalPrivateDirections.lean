import JSP000404Research.NarrowObserverDirections

/-!
# Weighted interval packing from private directions

Unit-separated private directions occupy distinct unused bands. Combining this
with the existing weighted Hansel theorem bounds the sum of their powers of two.
All interval and separation hypotheses are explicit. This module does not yet
identify the private-direction count with the canonical centre gap exponent.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Private directions in the same interval as the edges produce a weighted
capacity bound. Separation includes private/private and private/incident pairs. -/
theorem weighted_capacity_of_private_directions
    {V : Type*} [LinearOrder V] [Fintype V]
    (value : V → V → ℝ) (lower : ℝ) (k : ℕ) (hk : 0 < k)
    (hinterval : ∀ i j, i < j → lower ≤ value i j ∧ value i j < lower + k)
    (hsep : ∀ i j l, i < j → j < l → 1 ≤ |value i j - value j l|)
    (slots : V → Finset ℝ)
    (hslots : ∀ v x, x ∈ slots v → lower ≤ x ∧ x < lower + k)
    (hprivate : ∀ v x y, x ∈ slots v → y ∈ slots v → x ≠ y → 1 ≤ |x - y|)
    (havoid : ∀ i j, i < j → ∀ x, x ∈ slots i ∨ x ∈ slots j →
      1 ≤ |x - value i j|) :
    ∑ v, 2 ^ (slots v).card ≤ 2 ^ k := by
  classical
  let C := edgeIntervalColoring value lower k hk hinterval hsep
  let label (v : V) (x : {x // x ∈ slots v}) : Fin k :=
    ⟨Nat.floor (x.1 - lower),
      (Nat.floor_lt (by linarith [(hslots v x.1 x.2).1])).mpr
        (by linarith [(hslots v x.1 x.2).2])⟩
  let available (v : V) := (slots v).attach.image (label v)
  have hlabel (v : V) : Function.Injective (label v) := by
    intro x y hxy
    apply Subtype.ext
    by_contra hne
    have hfloor := congrArg Fin.val hxy
    have hx : 0 ≤ x.1 - lower := by linarith [(hslots v x.1 x.2).1]
    have hy : 0 ≤ y.1 - lower := by linarith [(hslots v y.1 y.2).1]
    have hdist : 1 ≤ |(x.1 - lower) - (y.1 - lower)| := by
      simpa only [sub_sub_sub_cancel_right] using hprivate v x.1 y.1 x.2 y.2 hne
    exact floor_ne_of_unit_separated hx hy hdist hfloor
  have hcard (v : V) : (available v).card = (slots v).card := by
    dsimp [available]
    rw [Finset.card_image_of_injective _ (hlabel v), Finset.card_attach]
  have hnot (i j : V) (hij : i < j) (v : V) (x : {x // x ∈ slots v})
      (hmem : x.1 ∈ slots i ∨ x.1 ∈ slots j) : C.color i j ≠ label v x := by
    intro heq
    have hfloor : Nat.floor (value i j - lower) = Nat.floor (x.1 - lower) := by
      simpa [C, edgeIntervalColoring, label, hij] using congrArg Fin.val heq
    have hx : 0 ≤ x.1 - lower := by linarith [(hslots v x.1 x.2).1]
    have he : 0 ≤ value i j - lower := by linarith [(hinterval i j hij).1]
    have hdist : 1 ≤ |(x.1 - lower) - (value i j - lower)| := by
      simpa only [sub_sub_sub_cancel_right] using havoid i j hij x.1 hmem
    exact floor_ne_of_unit_separated hx he hdist hfloor.symm
  have hdisjoint (v : V) : Disjoint (OrderedEdgeColoring.active C v) (available v) := by
    apply Finset.disjoint_left.mpr
    intro c hc hfree
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hfree
    simp only [OrderedEdgeColoring.active, Finset.mem_filter,
      Finset.mem_univ, true_and] at hc
    rcases hc with ⟨u, huv, heq⟩ | ⟨w, hvw, heq⟩
    · exact hnot u v huv v x (Or.inr x.2) heq
    · exact hnot v w hvw v x (Or.inl x.2) heq
  have hsum (v : V) : (OrderedEdgeColoring.active C v).card + (slots v).card ≤ k := by
    rw [← hcard v, ← Finset.card_union_of_disjoint (hdisjoint v)]
    exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin k)
  apply OrderedEdgeColoring.cluster_capacity_of_active_le C (fun v ↦ (slots v).card)
    (fun v ↦ k - (slots v).card)
  · intro v
    have h := hsum v
    omega
  · intro v
    rfl
  · intro v
    have h := hsum v
    omega

#print axioms weighted_capacity_of_private_directions

namespace DirectionData

/-- Private projective directions, normalized to the same period as the edges.
The circular separation from incident lines is recorded as two inequalities. -/
structure PrivateDirections {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) where
  directions : V → Finset ℝ
  nonnegative : ∀ v x, x ∈ directions v → 0 ≤ x
  belowWidth : ∀ v x, x ∈ directions v → x < width
  separated : ∀ v x y, x ∈ directions v → y ∈ directions v → x ≠ y → 1 ≤ |x - y|
  incident : ∀ i j, i < j → ∀ x, x ∈ directions i ∨ x ∈ directions j →
    1 ≤ |x - D.value i j| ∧ |x - D.value i j| ≤ width - 1

namespace PrivateDirections

private theorem above_low {x a : ℝ} (hx : 0 ≤ x) (ha : a < 1)
    (hsep : 1 ≤ |x - a|) : a + 1 ≤ x := by
  rcases le_total a x with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hsep
    linarith
  · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hsep
    linarith

private theorem below_high {x b width : ℝ} (hx : x < width) (hb : width - 1 < b)
    (hsep : 1 ≤ |x - b|) : x ≤ b - 1 := by
  rcases le_total b x with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hsep
    linarith
  · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hsep
    linarith

/-- Weighted packing on a selected set once its edge and private directions
are in one short interval. -/
theorem capacity_in_interval
    {V : Type*} [LinearOrder V] {width : ℝ} {D : DirectionData V width}
    (P : PrivateDirections D) (S : Finset V) (lower : ℝ) (k : ℕ) (hk : 0 < k)
    (hedges : ∀ i ∈ S, ∀ j ∈ S, i < j →
      lower ≤ D.value i j ∧ D.value i j < lower + k)
    (hprivate : ∀ i ∈ S, ∀ x ∈ P.directions i, lower ≤ x ∧ x < lower + k) :
    ∑ i ∈ S, 2 ^ (P.directions i).card ≤ 2 ^ k := by
  classical
  have h := weighted_capacity_of_private_directions
    (fun i j : S ↦ D.value i.1 j.1) lower k hk
    (fun i j hij ↦ hedges i.1 i.2 j.1 j.2 hij)
    (fun i j l hij hjl ↦ D.middleSeparated hij hjl)
    (fun i : S ↦ P.directions i.1)
    (fun i x hx ↦ hprivate i.1 i.2 x hx)
    (fun i x y hx hy hne ↦ P.separated i.1 x y hx hy hne)
    (fun i j hij x hx ↦ (P.incident i.1 j.1 hij x hx).1)
  rw [← Finset.sum_coe_sort S (fun i ↦ 2 ^ (P.directions i).card)]
  exact h

/-- The single narrow observer bounds the full dyadic weight of its selected
centres and their private directions. -/
theorem low_observer_capacity
    {V : Type*} [LinearOrder V] {width : ℝ} {D : DirectionData V width}
    (P : PrivateDirections D) (S : Finset V) {a : V} {lo hi : ℝ}
    (hbefore : ∀ i ∈ S, a < i)
    (hview : ∀ i ∈ S, lo ≤ D.value a i ∧ D.value a i ≤ hi)
    (hhi : hi < 1) (k : ℕ) (hk : 0 < k) (hwidth : width - 2 + (hi - lo) < k) :
    ∑ i ∈ S, 2 ^ (P.directions i).card ≤ 2 ^ k := by
  apply P.capacity_in_interval S (lo + 1) k hk
  · intro i hiS j hjS hij
    have h := D.low_observer_edge_interval (hbefore i hiS) hij
      (hview i hiS).1 (hview j hjS).2 ((hview i hiS).2.trans_lt hhi)
    exact ⟨h.1, by linarith [h.2]⟩
  · intro i hiS x hx
    have h := P.incident a i (hbefore i hiS) x (Or.inr hx)
    have hlower := above_low (P.nonnegative i x hx) ((hview i hiS).2.trans_lt hhi) h.1
    have hupper := le_of_abs_le h.2
    constructor <;> linarith [(hview i hiS).1, (hview i hiS).2]

/-- Two narrow observers bound the full residual dyadic weight. -/
theorem two_observer_capacity
    {V : Type*} [LinearOrder V] {width : ℝ} {D : DirectionData V width}
    (P : PrivateDirections D) (S : Finset V) {a b : V} (hab : a < b)
    (hbefore : ∀ i ∈ S, b < i)
    (hlow : ∀ i ∈ S, D.value a i < 1)
    (hhigh : ∀ i ∈ S, width - 1 < D.value b i)
    (k : ℕ) (hk : 0 < k) (hwidth : width - 3 < k) :
    ∑ i ∈ S, 2 ^ (P.directions i).card ≤ 2 ^ k := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  let r := S.min' hS
  have hr : r ∈ S := Finset.min'_mem S hS
  apply P.capacity_in_interval S (D.value a r + 1) k hk
  · intro i hi j hj hij
    have h := D.two_observer_edge_interval hab (hbefore r hr)
      (Finset.min'_le S i hi) hij (hlow r hr) (hlow i hi) (hhigh r hr) (hhigh i hi)
    exact ⟨h.1, by linarith [h.2]⟩
  · intro i hi x hx
    have hlower := above_low (P.nonnegative i x hx) (hlow i hi)
      (P.incident a i (hab.trans (hbefore i hi)) x (Or.inr hx)).1
    have hupper := below_high (P.belowWidth i x hx) (hhigh i hi)
      (P.incident b i (hbefore i hi) x (Or.inr hx)).1
    have hmono : D.value a r ≤ D.value a i := by
      rcases (Finset.min'_le S i hi).eq_or_lt with h | h
      · change r = i at h
        simp [h]
      · exact D.low_observer_monotone (hab.trans (hbefore r hr)) h (hlow r hr)
    have hanti : D.value b i ≤ D.value b r := by
      rcases (Finset.min'_le S i hi).eq_or_lt with h | h
      · change r = i at h
        simp [h]
      · exact D.high_observer_antitone (hbefore r hr) h (hhigh r hr)
    have hgap := neg_le_of_abs_le (D.lastGap hab (hbefore r hr))
    constructor <;> linarith

#print axioms capacity_in_interval
#print axioms low_observer_capacity
#print axioms two_observer_capacity

end PrivateDirections
end DirectionData

end JSP000404Research
