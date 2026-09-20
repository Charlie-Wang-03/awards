import JSP000404Research.WrapCapacity
import JSP000404Research.StandardBandColor
import Mathlib.Tactic

/-!
# Merging the two wrap unit bands

For width=n+delta with delta<1, the ordinary (n+1)-band colouring uses bands

  0,1,...,n.

The fixed lower-branch colouring merges the two wrap pieces, band 0 and the
truncated top band n, into one colour 0 while leaving bands 1,...,n-1
unchanged.

This file makes that quotient map explicit and proves that the deterministic
fixed-phase edge colour is exactly the image of the standard (n+1)-band
colour.  It is the algebraic bridge needed to identify fixed-phase active
colours with merged incident-band occupancy.
-/

namespace JSP000404Research
namespace DirectionData

/-- Quotient map identifying the top band n with band zero. -/
def mergeWrapBand
    {n : ℕ} (hn : 1 ≤ n) :
    Fin (n + 1) → Fin n :=
  fun c =>
    if htop : c.val = n then
      ⟨0, by omega⟩
    else
      ⟨c.val, by
        have hle : c.val ≤ n := by omega
        omega⟩

@[simp] theorem mergeWrapBand_zero
    {n : ℕ} (hn : 1 ≤ n) :
    mergeWrapBand hn (0 : Fin (n + 1)) = (0 : Fin n) := by
  apply Fin.ext
  simp [mergeWrapBand]
  omega

theorem mergeWrapBand_top
    {n : ℕ} (hn : 1 ≤ n) :
    mergeWrapBand hn ⟨n, by omega⟩ = (0 : Fin n) := by
  apply Fin.ext
  simp [mergeWrapBand]

theorem mergeWrapBand_of_lt
    {n : ℕ} (hn : 1 ≤ n)
    (c : Fin (n + 1))
    (hc : c.val < n) :
    (mergeWrapBand hn c).val = c.val := by
  simp [mergeWrapBand, ne_of_lt hc]

/-- In the lower branch the total width is strictly below n+1, so the
standard (n+1)-band colour is available. -/
theorem width_lt_n_add_one
    {width delta : ℝ} {n : ℕ}
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1) :
    width < ((n + 1 : ℕ) : ℝ) := by
  rw [hwidth]
  push_cast
  linarith

/-- The deterministic merged colour is exactly the quotient of the standard
(n+1)-band colour by mergeWrapBand. -/
theorem fixedPhaseEdgeColor_eq_merge_standard
    {V : Type*} [LinearOrder V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (hn : 1 ≤ n)
    {u v : V} (huv : u < v) :
    fixedPhaseEdgeColor D n hn u v =
      mergeWrapBand hn
        (standardBandColor D (n + 1)
          (by omega)
          (width_lt_n_add_one hwidth hdelta)
          u v) := by
  let x := D.value u v
  have hx0 : 0 ≤ x := D.nonnegative huv
  have hxTop : x < (n : ℝ) + delta := by
    simpa [x, hwidth] using D.belowWidth huv
  by_cases hlow : x < 1
  · have hfloor0 : Nat.floor x = 0 := by
      exact Nat.floor_eq_zero.mpr ⟨hx0, hlow⟩
    apply Fin.ext
    have hwrap : x < 1 ∨ (n : ℝ) ≤ x := Or.inl hlow
    rw [fixedPhaseEdgeColor_eq_zero_of_wrap D hn huv
      (by simpa [x] using hwrap)]
    simp [standardBandColor, huv, mergeWrapBand, x, hfloor0]
  · by_cases hhigh : (n : ℝ) ≤ x
    · have hfloorN : Nat.floor x = n := by
        have hxn1 : x < (n : ℝ) + 1 := by linarith
        exact (Nat.floor_eq_iff hx0).2
          (by
            constructor
            · exact hhigh
            · simpa using hxn1)
      apply Fin.ext
      have hwrap : x < 1 ∨ (n : ℝ) ≤ x := Or.inr hhigh
      rw [fixedPhaseEdgeColor_eq_zero_of_wrap D hn huv
        (by simpa [x] using hwrap)]
      simp [standardBandColor, huv, mergeWrapBand, x, hfloorN]
    · have hmid : 1 ≤ x := le_of_not_gt hlow
      have hxn : x < (n : ℝ) := lt_of_not_ge hhigh
      have hfloorLt : Nat.floor x < n :=
        (Nat.floor_lt hx0).2 hxn
      apply Fin.ext
      rw [fixedPhaseEdgeColor_eq_floor_of_middle
        D hn huv (by simpa [x] using hmid) (by simpa [x] using hxn)]
      simp [standardBandColor, huv, mergeWrapBand, x,
        ne_of_lt hfloorLt]


/-- The active colours of the deterministic merged partition are exactly the
image, under mergeWrapBand, of the standard (n+1)-band active colours. -/
theorem canonicalFixedPhase_active_eq_image_standard
    {V : Type*} [LinearOrder V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (hn : 1 ≤ n)
    (htri : WrapTriangleFree D n)
    (v : V) :
    BinaryEdgePartition.active
        (canonicalFixedPhasePartition D hwidth hdelta hn htri) v
      =
    (OrderedEdgeColoring.active
        (standardBandColoring D (n + 1)
          (by omega)
          (width_lt_n_add_one hwidth hdelta)) v).image
      (mergeWrapBand hn) := by
  classical
  ext c
  simp only [BinaryEdgePartition.active, OrderedEdgeColoring.active,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hc
    rcases hc with ⟨a, hav, hcol⟩ | ⟨w, hvw, hcol⟩
    · let d :=
        standardBandColor D (n + 1)
          (by omega)
          (width_lt_n_add_one hwidth hdelta) a v
      refine ⟨d, ?_, ?_⟩
      · left
        exact ⟨a, hav, rfl⟩
      · have hmerge :=
          fixedPhaseEdgeColor_eq_merge_standard
            D hwidth hdelta hn hav
        have hcanon :
            (canonicalFixedPhasePartition
              D hwidth hdelta hn htri).edgeColor a v =
              fixedPhaseEdgeColor D n hn a v := rfl
        rw [hcanon, hmerge] at hcol
        exact hcol.symm
    · let d :=
        standardBandColor D (n + 1)
          (by omega)
          (width_lt_n_add_one hwidth hdelta) v w
      refine ⟨d, ?_, ?_⟩
      · right
        exact ⟨w, hvw, rfl⟩
      · have hmerge :=
          fixedPhaseEdgeColor_eq_merge_standard
            D hwidth hdelta hn hvw
        have hcanon :
            (canonicalFixedPhasePartition
              D hwidth hdelta hn htri).edgeColor v w =
              fixedPhaseEdgeColor D n hn v w := rfl
        rw [hcanon, hmerge] at hcol
        exact hcol.symm
  · rintro ⟨d, hdactive, hdc⟩
    rcases hdactive with ⟨a, hav, hstd⟩ | ⟨w, hvw, hstd⟩
    · left
      refine ⟨a, hav, ?_⟩
      have hmerge :=
        fixedPhaseEdgeColor_eq_merge_standard
          D hwidth hdelta hn hav
      have hstd' :
          standardBandColor D (n + 1)
              (by omega)
              (width_lt_n_add_one hwidth hdelta) a v = d := by
        exact hstd
      change fixedPhaseEdgeColor D n hn a v = c
      rw [hmerge, hstd', hdc]
    · right
      refine ⟨w, hvw, ?_⟩
      have hmerge :=
        fixedPhaseEdgeColor_eq_merge_standard
          D hwidth hdelta hn hvw
      have hstd' :
          standardBandColor D (n + 1)
              (by omega)
              (width_lt_n_add_one hwidth hdelta) v w = d := by
        exact hstd
      change fixedPhaseEdgeColor D n hn v w = c
      rw [hmerge, hstd', hdc]

/-- Rewriting the preceding identity using the existing incidentBands
characterization of standard active colours. -/
theorem canonicalFixedPhase_active_eq_image_incidentBands
    {V : Type*} [LinearOrder V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (hn : 1 ≤ n)
    (htri : WrapTriangleFree D n)
    (v : V) :
    BinaryEdgePartition.active
        (canonicalFixedPhasePartition D hwidth hdelta hn htri) v
      =
    (incidentBands D (n + 1) v).image (mergeWrapBand hn) := by
  rw [canonicalFixedPhase_active_eq_image_standard
      D hwidth hdelta hn htri v,
    standardBand_active_eq_incidentBands]

/-- Merging never increases the number of active colours. -/
theorem canonicalFixedPhase_active_card_le_standard
    {V : Type*} [LinearOrder V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (hn : 1 ≤ n)
    (htri : WrapTriangleFree D n)
    (v : V) :
    (BinaryEdgePartition.active
      (canonicalFixedPhasePartition D hwidth hdelta hn htri) v).card
      ≤
    (incidentBands D (n + 1) v).card := by
  rw [canonicalFixedPhase_active_eq_image_incidentBands
      D hwidth hdelta hn htri v]
  exact Finset.card_image_le


/-- Away from the top band, mergeWrapBand is injective. -/
theorem mergeWrapBand_injOn_erase_top
    {n : ℕ} (hn : 1 ≤ n)
    (S : Finset (Fin (n + 1))) :
    Set.InjOn (mergeWrapBand hn)
      (S.erase ⟨n, by omega⟩) := by
  intro a ha b hb hab
  have hatop : a.val ≠ n := by
    intro h
    have haeq : a = (⟨n, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      exact h
    subst a
    exact (Finset.not_mem_erase _ _) ha
  have hbtop : b.val ≠ n := by
    intro h
    have hbeq : b = (⟨n, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      exact h
    subst b
    exact (Finset.not_mem_erase _ _) hb
  have halt : a.val < n := by
    have ha_le : a.val ≤ n := by omega
    omega
  have hblt : b.val < n := by
    have hb_le : b.val ≤ n := by omega
    omega
  have hava :
      (mergeWrapBand hn a).val = a.val :=
    mergeWrapBand_of_lt hn a halt
  have havb :
      (mergeWrapBand hn b).val = b.val :=
    mergeWrapBand_of_lt hn b hblt
  apply Fin.ext
  have hv := congrArg Fin.val hab
  simpa [hava, havb] using hv

/-- If both wrap representatives 0 and n are present, deleting the top one
does not change the merged image: it was already represented by band zero. -/
theorem image_mergeWrapBand_erase_top_eq_of_zero_mem
    {n : ℕ} (hn : 1 ≤ n)
    (S : Finset (Fin (n + 1)))
    (hzero : (0 : Fin (n + 1)) ∈ S) :
    S.image (mergeWrapBand hn) =
      (S.erase ⟨n, by omega⟩).image (mergeWrapBand hn) := by
  classical
  let top : Fin (n + 1) := ⟨n, by omega⟩
  ext c
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨x, hxS, rfl⟩
    by_cases hxtop : x = top
    · subst x
      refine ⟨(0 : Fin (n + 1)), ?_, ?_⟩
      · apply Finset.mem_erase.mpr
        constructor
        · intro h
          have hv := congrArg Fin.val h
          dsimp [top] at hv
          omega
        · exact hzero
      · simpa [top] using (mergeWrapBand_top hn)
    · exact ⟨x, Finset.mem_erase.mpr ⟨hxtop, hxS⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, (Finset.mem_erase.mp hx).2, rfl⟩

/-- Exact one-colour compression: if standard bands 0 and n are both active,
merging them reduces palette cardinality by exactly one. -/
theorem card_image_mergeWrapBand_eq_sub_one
    {n : ℕ} (hn : 1 ≤ n)
    (S : Finset (Fin (n + 1)))
    (hzero : (0 : Fin (n + 1)) ∈ S)
    (htop : (⟨n, by omega⟩ : Fin (n + 1)) ∈ S) :
    (S.image (mergeWrapBand hn)).card = S.card - 1 := by
  classical
  rw [image_mergeWrapBand_erase_top_eq_of_zero_mem hn S hzero]
  have hinj := mergeWrapBand_injOn_erase_top hn S
  rw [Finset.card_image_iff.mpr hinj]
  rw [Finset.card_erase_of_mem htop]

/-- Specialized active-palette form of the exact one-colour compression. -/
theorem canonicalFixedPhase_active_card_eq_standard_sub_one
    {V : Type*} [LinearOrder V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (hn : 1 ≤ n)
    (htri : WrapTriangleFree D n)
    (v : V)
    (hzero : (0 : Fin (n + 1)) ∈ incidentBands D (n + 1) v)
    (htop : (⟨n, by omega⟩ : Fin (n + 1)) ∈
      incidentBands D (n + 1) v) :
    (BinaryEdgePartition.active
      (canonicalFixedPhasePartition D hwidth hdelta hn htri) v).card
      =
    (incidentBands D (n + 1) v).card - 1 := by
  rw [canonicalFixedPhase_active_eq_image_incidentBands
      D hwidth hdelta hn htri v]
  exact card_image_mergeWrapBand_eq_sub_one
    hn (incidentBands D (n + 1) v) hzero htop

#print axioms mergeWrapBand
#print axioms width_lt_n_add_one
#print axioms fixedPhaseEdgeColor_eq_merge_standard
#print axioms canonicalFixedPhase_active_eq_image_incidentBands
#print axioms canonicalFixedPhase_active_card_le_standard
#print axioms card_image_mergeWrapBand_eq_sub_one
#print axioms canonicalFixedPhase_active_card_eq_standard_sub_one

end DirectionData
end JSP000404Research
