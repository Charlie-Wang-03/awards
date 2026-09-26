
import JSP000404Research.ProjectiveBandOneLayerCapacity
import Mathlib.Tactic

/-!
# Eliminating the last projective band by a certified 0/n merge

The direct projective-band certificate has n+1 colours.  This file isolates
the exact final compression step.

Merge the last colour n into colour 0.  Middle colours 1,...,n-1 keep their
old projective-band bits.  The merged wrap colour is allowed to use an
arbitrary Boolean vertex bit, provided it separates every old edge whose
colour was 0 or n.

On local palette size there are only two cases.

* If the old one-layer active bound is strict, merging cannot increase the
  active palette, so the desired n-colour budget already holds.

* If the old bound is saturated, it is enough that both old colours 0 and n
  are active.  Their collision under the merge removes one active colour.

Thus the remaining geometric obligations are exactly:

1. a Boolean colouring of the union of projective bands 0 and n;
2. every saturated centre occupies both boundary bands.

No comb-profile or threshold-majorization hypothesis is used.
-/

namespace JSP000404Research

open scoped BigOperators

namespace BinaryEdgePartition

def mergeLastColor
    {n : ℕ} (hn : 1 ≤ n) :
    Fin (n + 1) → Fin n :=
  fun c =>
    if h : c.val < n then
      ⟨c.val, h⟩
    else
      ⟨0, hn⟩

@[simp] theorem mergeLastColor_last
    {n : ℕ} (hn : 1 ≤ n) :
    mergeLastColor hn (Fin.last n) =
      (0 : Fin n) := by
  apply Fin.ext
  simp [mergeLastColor]

@[simp] theorem mergeLastColor_zero
    {n : ℕ} (hn : 1 ≤ n) :
    mergeLastColor hn (0 : Fin (n + 1)) =
      (0 : Fin n) := by
  apply Fin.ext
  simp [mergeLastColor, hn]

@[simp] theorem mergeLastColor_castSucc
    {n : ℕ} (hn : 1 ≤ n)
    (c : Fin n) :
    mergeLastColor hn c.castSucc = c := by
  apply Fin.ext
  simp [mergeLastColor, c.isLt]

/-- Binary partition obtained by merging old colours 0 and n. -/
noncomputable def mergeLastPartition
    {V : Type*} [LinearOrder V] {n : ℕ}
    (hn : 1 ≤ n)
    (P : BinaryEdgePartition V (n + 1))
    (wrapBit : V → Bool)
    (hwrap :
      ∀ {u v : V}, u < v →
        ((P.edgeColor u v).val = 0 ∨
          (P.edgeColor u v).val = n) →
        wrapBit u ≠ wrapBit v) :
    BinaryEdgePartition V n where
  edgeColor := fun u v =>
    mergeLastColor hn (P.edgeColor u v)
  bit := fun v c =>
    if c.val = 0 then
      wrapBit v
    else
      P.bit v c.castSucc
  proper := by
    intro u v huv
    let old := P.edgeColor u v
    by_cases hlast : old.val = n
    · have hmerged :
          mergeLastColor hn old = (0 : Fin n) := by
        apply Fin.ext
        simp [mergeLastColor, hlast]
      rw [hmerged]
      simp only [Fin.val_zero, if_pos]
      exact hwrap huv (Or.inr hlast)
    · have holdlt : old.val < n := by
        have holdBound := old.isLt
        omega
      let c : Fin n := ⟨old.val, holdlt⟩
      have hmerged :
          mergeLastColor hn old = c := by
        apply Fin.ext
        simp [mergeLastColor, holdlt, c]
      rw [hmerged]
      by_cases hzero : old.val = 0
      · have hc0 : c.val = 0 := by simpa [c] using hzero
        simp only [hc0, if_pos]
        exact hwrap huv (Or.inl hzero)
      · have hc0 : c.val ≠ 0 := by
          simpa [c] using hzero
        simp only [hc0, if_neg]
        have hcast : c.castSucc = old := by
          apply Fin.ext
          rfl
        rw [hcast]
        exact P.proper huv

/-- Every new active colour is the image of an old active colour. -/
theorem mergeLastPartition_active_subset_image
    {V : Type*} [LinearOrder V] {n : ℕ}
    (hn : 1 ≤ n)
    (P : BinaryEdgePartition V (n + 1))
    (wrapBit : V → Bool)
    (hwrap :
      ∀ {u v : V}, u < v →
        ((P.edgeColor u v).val = 0 ∨
          (P.edgeColor u v).val = n) →
        wrapBit u ≠ wrapBit v)
    (v : V) :
    active (mergeLastPartition hn P wrapBit hwrap) v ⊆
      (active P v).image (mergeLastColor hn) := by
  classical
  intro c hc
  simp only [active, Finset.mem_filter, Finset.mem_univ,
    true_and] at hc
  simp only [Finset.mem_image]
  rcases hc with ⟨a, hav, hcol⟩ | ⟨w, hvw, hcol⟩
  · refine ⟨P.edgeColor a v, ?_, ?_⟩
    · simp only [active, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact Or.inl ⟨a, hav, rfl⟩
    · simpa [mergeLastPartition] using hcol
  · refine ⟨P.edgeColor v w, ?_, ?_⟩
    · simp only [active, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact Or.inr ⟨w, hvw, rfl⟩
    · simpa [mergeLastPartition] using hcol

/-- General merge never increases local palette cardinality. -/
theorem mergeLastPartition_active_card_le
    {V : Type*} [LinearOrder V] {n : ℕ}
    (hn : 1 ≤ n)
    (P : BinaryEdgePartition V (n + 1))
    (wrapBit : V → Bool)
    (hwrap :
      ∀ {u v : V}, u < v →
        ((P.edgeColor u v).val = 0 ∨
          (P.edgeColor u v).val = n) →
        wrapBit u ≠ wrapBit v)
    (v : V) :
    (active (mergeLastPartition hn P wrapBit hwrap) v).card ≤
      (active P v).card := by
  classical
  calc
    (active (mergeLastPartition hn P wrapBit hwrap) v).card
        ≤ ((active P v).image (mergeLastColor hn)).card :=
      Finset.card_le_card
        (mergeLastPartition_active_subset_image
          hn P wrapBit hwrap v)
    _ ≤ (active P v).card := Finset.card_image_le

/-- If both boundary colours occur locally, the merge saves at least one
active colour. -/
theorem mergeLastPartition_active_card_add_one_le
    {V : Type*} [LinearOrder V] {n : ℕ}
    (hn : 1 ≤ n)
    (P : BinaryEdgePartition V (n + 1))
    (wrapBit : V → Bool)
    (hwrap :
      ∀ {u v : V}, u < v →
        ((P.edgeColor u v).val = 0 ∨
          (P.edgeColor u v).val = n) →
        wrapBit u ≠ wrapBit v)
    (v : V)
    (hzero : (0 : Fin (n + 1)) ∈ active P v)
    (hlast : Fin.last n ∈ active P v) :
    (active (mergeLastPartition hn P wrapBit hwrap) v).card + 1 ≤
      (active P v).card := by
  classical
  let S := active P v
  let f := mergeLastColor hn
  have hsub :
      active (mergeLastPartition hn P wrapBit hwrap) v ⊆
        S.image f :=
    mergeLastPartition_active_subset_image
      hn P wrapBit hwrap v
  have himageEq :
      S.image f = (S.erase (Fin.last n)).image f := by
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨c, hcS, rfl⟩ := Finset.mem_image.mp hx
      by_cases hcLast : c = Fin.last n
      · subst c
        apply Finset.mem_image.mpr
        refine ⟨(0 : Fin (n + 1)), ?_, ?_⟩
        · exact Finset.mem_erase.mpr ⟨by
            intro h
            have hval := congrArg Fin.val h
            simp at hval
            omega, hzero⟩
        · simp [f, hn]
      · apply Finset.mem_image.mpr
        exact ⟨c, Finset.mem_erase.mpr ⟨hcLast, hcS⟩, rfl⟩
    · exact Finset.image_subset_image (Finset.erase_subset _ _)
  have hcardImage :
      (S.image f).card ≤ S.card - 1 := by
    rw [himageEq]
    calc
      ((S.erase (Fin.last n)).image f).card
          ≤ (S.erase (Fin.last n)).card := Finset.card_image_le
      _ = S.card - 1 := by
        rw [Finset.card_erase_of_mem]
        exact hlast
  have hnew :
      (active (mergeLastPartition hn P wrapBit hwrap) v).card ≤
        (S.image f).card :=
    Finset.card_le_card hsub
  have hSpos : 1 ≤ S.card := by
    exact Finset.card_pos.mpr ⟨Fin.last n, hlast⟩
  omega

/-- Generic n+1 to n weighted compression theorem. -/
theorem cluster_capacity_of_last_merge
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (hn : 1 ≤ n)
    (P : BinaryEdgePartition V (n + 1))
    (exponent : V → ℕ)
    (hexponent : ∀ v, exponent v ≤ n)
    (hold :
      ∀ v, (active P v).card ≤
        (n + 1) - exponent v)
    (wrapBit : V → Bool)
    (hwrap :
      ∀ {u v : V}, u < v →
        ((P.edgeColor u v).val = 0 ∨
          (P.edgeColor u v).val = n) →
        wrapBit u ≠ wrapBit v)
    (hsaturated :
      ∀ v,
        (active P v).card = (n + 1) - exponent v →
        (0 : Fin (n + 1)) ∈ active P v ∧
        Fin.last n ∈ active P v) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n := by
  let M := mergeLastPartition hn P wrapBit hwrap
  have hactive :
      ∀ v, (active M v).card ≤ n - exponent v := by
    intro v
    by_cases hsat :
        (active P v).card = (n + 1) - exponent v
    · have hb := hsaturated v hsat
      have hdrop :=
        mergeLastPartition_active_card_add_one_le
          hn P wrapBit hwrap v hb.1 hb.2
      omega
    · have holdv := hold v
      have hstrict :
          (active P v).card < (n + 1) - exponent v := by
        omega
      have hmono :=
        mergeLastPartition_active_card_le
          hn P wrapBit hwrap v
      omega
  exact BinaryEdgePartition.cluster_capacity_of_active_le
    M exponent (fun v => n - exponent v)
    hexponent (fun v => rfl) hactive

#print axioms mergeLastPartition
#print axioms mergeLastPartition_active_card_le
#print axioms mergeLastPartition_active_card_add_one_le
#print axioms cluster_capacity_of_last_merge

end BinaryEdgePartition

/-- Concrete projective-band specialization of the final one-bit compression
outlet. -/
theorem projectiveBand_capacity_of_last_merge
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {t delta lam : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (wrapBit : V → Bool)
    (hwrap :
      let P :=
        projectiveBandPartition hp hcap htpos hlam n
          (by
            rw [ht]
            push_cast
            linarith)
      ∀ {u v : V}, u < v →
        ((P.edgeColor u v).val = 0 ∨
          (P.edgeColor u v).val = n) →
        wrapBit u ≠ wrapBit v)
    (hsaturated :
      let P :=
        projectiveBandPartition hp hcap htpos hlam n
          (by
            rw [ht]
            push_cast
            linarith)
      ∀ i,
        (BinaryEdgePartition.active P i).card =
            (n + 1) - centreExponent (C i) t →
        (0 : Fin (n + 1)) ∈ BinaryEdgePartition.active P i ∧
        Fin.last n ∈ BinaryEdgePartition.active P i) :
    (∑ i : V, 2 ^ centreExponent (C i) t) ≤ 2 ^ n := by
  let htop : t < (n + 1 : ℕ) := by
    rw [ht]
    push_cast
    linarith
  let P :=
    projectiveBandPartition hp hcap htpos hlam n htop
  have hold :
      ∀ i, (BinaryEdgePartition.active P i).card ≤
        (n + 1) - centreExponent (C i) t := by
    intro i
    dsimp [P]
    exact projectiveBandPartition_active_card_le_deficit
      hp hcap htpos hlam ht hdelta0 hdelta1 C i
  have hexp :
      ∀ i, centreExponent (C i) t ≤ n := by
    intro i
    exact centreExponent_le_n
      (C i) n delta t hn hdelta0 hdelta1 ht
  apply BinaryEdgePartition.cluster_capacity_of_last_merge
    hn P (fun i => centreExponent (C i) t)
    hexp hold wrapBit
  · simpa [P, htop] using hwrap
  · simpa [P, htop] using hsaturated

#print axioms projectiveBand_capacity_of_last_merge

end JSP000404Research
