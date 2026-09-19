import JSP000404Research.WrapLocal
import Mathlib.Tactic

/-!
# Symmetric wrap-edge labels

DirectionData.value i j is only meaningful in the chosen increasing order
i < j. Cycle arguments are cleaner with a canonical unoriented edge
direction. This module symmetrizes the low/high/middle predicates and lifts
local parity rules from WrapLocal to arbitrary distinct neighbours.

The resulting rule is exactly what the odd-cycle argument needs:

* if a cycle vertex lies between its two neighbours in the ambient order, its
  two wrap edges have opposite L/H types;
* if it is a local minimum or maximum and the chord between the neighbours is
  a middle edge, its two wrap edges have the same L/H type.
-/

namespace JSP000404Research
namespace DirectionData

noncomputable def edgeValue
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) (u v : V) : ℝ :=
  if u < v then D.value u v else D.value v u

theorem edgeValue_symm
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) {u v : V} (huv : u ≠ v) :
    edgeValue D u v = edgeValue D v u := by
  unfold edgeValue
  rcases lt_or_gt_of_ne huv with huvlt | hvult
  · simp [huvlt, not_lt.mpr huvlt.le]
  · simp [hvult, not_lt.mpr hvult.le]

def EdgeLow
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) (u v : V) : Prop :=
  edgeValue D u v < 1

def EdgeHigh
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) (n : ℕ) (u v : V) : Prop :=
  (n : ℝ) ≤ edgeValue D u v

def EdgeMiddle
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) (n : ℕ) (u v : V) : Prop :=
  1 ≤ edgeValue D u v ∧ edgeValue D u v < n

theorem edgeLow_symm
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) {u v : V} (huv : u ≠ v) :
    EdgeLow D u v ↔ EdgeLow D v u := by
  unfold EdgeLow
  rw [edgeValue_symm D huv]

theorem edgeHigh_symm
    {V : Type*} [LinearOrder V] {width : ℝ} {n : ℕ}
    (D : DirectionData V width) {u v : V} (huv : u ≠ v) :
    EdgeHigh D n u v ↔ EdgeHigh D n v u := by
  unfold EdgeHigh
  rw [edgeValue_symm D huv]

theorem edgeMiddle_symm
    {V : Type*} [LinearOrder V] {width : ℝ} {n : ℕ}
    (D : DirectionData V width) {u v : V} (huv : u ≠ v) :
    EdgeMiddle D n u v ↔ EdgeMiddle D n v u := by
  unfold EdgeMiddle
  rw [edgeValue_symm D huv]

theorem edgeWrap_opposite_at_between
    {V : Type*} [LinearOrder V] {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    {x v y : V}
    (hxv : x ≠ v) (hvy : v ≠ y) (hxy : x ≠ y)
    (hbetween : (x < v ∧ v < y) ∨ (y < v ∧ v < x))
    (hxWrap : EdgeLow D x v ∨ EdgeHigh D n x v)
    (hyWrap : EdgeLow D v y ∨ EdgeHigh D n v y) :
    (EdgeLow D x v ∧ EdgeHigh D n v y) ∨
      (EdgeHigh D n x v ∧ EdgeLow D v y) := by
  rcases hbetween with ⟨hxvlt, hvylt⟩ | ⟨hyvlt, hvxlt⟩
  · have hxWrap' : IsLow D x v ∨ IsHigh D n x v := by
      simpa [EdgeLow, EdgeHigh, edgeValue, hxvlt] using hxWrap
    have hyWrap' : IsLow D v y ∨ IsHigh D n v y := by
      simpa [EdgeLow, EdgeHigh, edgeValue, hvylt] using hyWrap
    simpa [EdgeLow, EdgeHigh, edgeValue, hxvlt, hvylt] using
      wrap_opposite_at_middle D hwidth hdelta hxvlt hvylt hxWrap' hyWrap'
  · have hyWrap' : IsLow D y v ∨ IsHigh D n y v := by
      rcases hyWrap with h | h
      · have hs : EdgeLow D y v := (edgeLow_symm D hvy).mpr h
        simpa [EdgeLow, edgeValue, hyvlt] using hs
      · have hs : EdgeHigh D n y v := (edgeHigh_symm D hvy).mpr h
        simpa [EdgeHigh, edgeValue, hyvlt] using hs
    have hxWrap' : IsLow D v x ∨ IsHigh D n v x := by
      rcases hxWrap with h | h
      · have hs : EdgeLow D v x := (edgeLow_symm D hxv).mp h
        simpa [EdgeLow, edgeValue, hvxlt] using hs
      · have hs : EdgeHigh D n v x := (edgeHigh_symm D hxv).mp h
        simpa [EdgeHigh, edgeValue, hvxlt] using hs
    have h :=
      wrap_opposite_at_middle D hwidth hdelta hyvlt hvxlt hyWrap' hxWrap'
    rcases h with h | h
    · exact Or.inr ⟨
        (edgeHigh_symm D hxv).mpr (by
          simpa [EdgeHigh, edgeValue, hvxlt] using h.2),
        (edgeLow_symm D hvy).mpr (by
          simpa [EdgeLow, edgeValue, hyvlt] using h.1)⟩
    · exact Or.inl ⟨
        (edgeLow_symm D hxv).mpr (by
          simpa [EdgeLow, edgeValue, hvxlt] using h.2),
        (edgeHigh_symm D hvy).mpr (by
          simpa [EdgeHigh, edgeValue, hyvlt] using h.1)⟩

theorem edgeWrap_same_at_local_min
    {V : Type*} [LinearOrder V] {width : ℝ} {n : ℕ}
    (D : DirectionData V width)
    {v x y : V}
    (hvx : v < x) (hvy : v < y) (hxy : x ≠ y)
    (hxWrap : EdgeLow D v x ∨ EdgeHigh D n v x)
    (hyWrap : EdgeLow D v y ∨ EdgeHigh D n v y)
    (hxyMid : EdgeMiddle D n x y) :
    (EdgeLow D v x ∧ EdgeLow D v y) ∨
      (EdgeHigh D n v x ∧ EdgeHigh D n v y) := by
  rcases lt_or_gt_of_ne hxy with hxylt | hyxlt
  · have hxWrap' : IsLow D v x ∨ IsHigh D n v x := by
      simpa [EdgeLow, EdgeHigh, edgeValue, hvx] using hxWrap
    have hyWrap' : IsLow D v y ∨ IsHigh D n v y := by
      simpa [EdgeLow, EdgeHigh, edgeValue, hvy] using hyWrap
    have hxyMid' : IsMiddle D n x y := by
      simpa [EdgeMiddle, edgeValue, hxylt] using hxyMid
    simpa [EdgeLow, EdgeHigh, edgeValue, hvx, hvy] using
      wrap_same_at_local_min D hvx hxylt hxWrap' hyWrap' hxyMid'
  · have hyWrap' : IsLow D v y ∨ IsHigh D n v y := by
      simpa [EdgeLow, EdgeHigh, edgeValue, hvy] using hyWrap
    have hxWrap' : IsLow D v x ∨ IsHigh D n v x := by
      simpa [EdgeLow, EdgeHigh, edgeValue, hvx] using hxWrap
    have hmid : EdgeMiddle D n y x :=
      (edgeMiddle_symm D hxy).mp hxyMid
    have hmid' : IsMiddle D n y x := by
      simpa [EdgeMiddle, edgeValue, hyxlt] using hmid
    have h :=
      wrap_same_at_local_min D hvy hyxlt hyWrap' hxWrap' hmid'
    rcases h with h | h
    · exact Or.inl ⟨
        (by simpa [EdgeLow, edgeValue, hvx] using h.2),
        (by simpa [EdgeLow, edgeValue, hvy] using h.1)⟩
    · exact Or.inr ⟨
        (by simpa [EdgeHigh, edgeValue, hvx] using h.2),
        (by simpa [EdgeHigh, edgeValue, hvy] using h.1)⟩

theorem edgeWrap_same_at_local_max
    {V : Type*} [LinearOrder V] {width : ℝ} {n : ℕ}
    (D : DirectionData V width)
    {v x y : V}
    (hxv : x < v) (hyv : y < v) (hxy : x ≠ y)
    (hxWrap : EdgeLow D x v ∨ EdgeHigh D n x v)
    (hyWrap : EdgeLow D y v ∨ EdgeHigh D n y v)
    (hxyMid : EdgeMiddle D n x y) :
    (EdgeLow D x v ∧ EdgeLow D y v) ∨
      (EdgeHigh D n x v ∧ EdgeHigh D n y v) := by
  rcases lt_or_gt_of_ne hxy with hxylt | hyxlt
  · have hxWrap' : IsLow D x v ∨ IsHigh D n x v := by
      simpa [EdgeLow, EdgeHigh, edgeValue, hxv] using hxWrap
    have hyWrap' : IsLow D y v ∨ IsHigh D n y v := by
      simpa [EdgeLow, EdgeHigh, edgeValue, hyv] using hyWrap
    have hxyMid' : IsMiddle D n x y := by
      simpa [EdgeMiddle, edgeValue, hxylt] using hxyMid
    simpa [EdgeLow, EdgeHigh, edgeValue, hxv, hyv] using
      wrap_same_at_local_max D hxylt hyv hxWrap' hyWrap' hxyMid'
  · have hyWrap' : IsLow D y v ∨ IsHigh D n y v := by
      simpa [EdgeLow, EdgeHigh, edgeValue, hyv] using hyWrap
    have hxWrap' : IsLow D x v ∨ IsHigh D n x v := by
      simpa [EdgeLow, EdgeHigh, edgeValue, hxv] using hxWrap
    have hmid : EdgeMiddle D n y x :=
      (edgeMiddle_symm D hxy).mp hxyMid
    have hmid' : IsMiddle D n y x := by
      simpa [EdgeMiddle, edgeValue, hyxlt] using hmid
    have h :=
      wrap_same_at_local_max D hyxlt hxv hyWrap' hxWrap' hmid'
    rcases h with h | h
    · exact Or.inl ⟨
        (by simpa [EdgeLow, edgeValue, hxv] using h.2),
        (by simpa [EdgeLow, edgeValue, hyv] using h.1)⟩
    · exact Or.inr ⟨
        (by simpa [EdgeHigh, edgeValue, hxv] using h.2),
        (by simpa [EdgeHigh, edgeValue, hyv] using h.1)⟩

#print axioms edgeValue_symm
#print axioms edgeWrap_opposite_at_between
#print axioms edgeWrap_same_at_local_min
#print axioms edgeWrap_same_at_local_max

end DirectionData
end JSP000404Research
