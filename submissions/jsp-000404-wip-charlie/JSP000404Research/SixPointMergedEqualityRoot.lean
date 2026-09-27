import JSP000404Research.SixPointMergedTwoExceptionEquality
import Mathlib.Tactic

/-!
# Root-colour factorization of the two-exception equality terminal

At the exact six-point profile

  active(top) = 1,
  active(bad1) = active(bad2) = 4,
  active(other minima) = 3,

the unique colour active at the top is a genuine root coordinate.

Every top--minimum edge has that colour, hence every minimum is active on the
root coordinate and has the Boolean bit opposite to the top.  Therefore all
five minima have the same root bit and no minimum--minimum edge can use the
root colour.

Erasing the root coordinate leaves the exact five-point profile

  3,3,2,2,2

on the two exceptional and three ordinary minima respectively.
-/

namespace JSP000404Research

open BinaryEdgePartition

theorem edgeColor_mem_active_lower
    {V : Type*} [LinearOrder V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    {u v : V} (huv : u < v) :
    P.edgeColor u v ∈ active P u := by
  classical
  simp only [active, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact Or.inr ⟨v, huv, rfl⟩

theorem edgeColor_mem_active_upper
    {V : Type*} [LinearOrder V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    {u v : V} (huv : u < v) :
    P.edgeColor u v ∈ active P v := by
  classical
  simp only [active, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact Or.inl ⟨u, huv, rfl⟩

theorem exists_rootColour_of_top_active_card_one
    {V : Type*} [LinearOrder V]
    {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top : V)
    (hTop : (active P top).card = 1) :
    ∃ c : Fin k,
      active P top = {c} ∧
      ∀ v : V, v ≠ top →
        c ∈ active P v ∧
        P.bit v c ≠ P.bit top c := by
  classical
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hTop
  refine ⟨c, hc, ?_⟩
  intro v hvt
  rcases lt_or_gt_of_ne hvt with htv | hvt'
  · have hcTop :
        P.edgeColor top v ∈ active P top :=
      edgeColor_mem_active_lower P htv
    have hcol :
        P.edgeColor top v = c := by
      rw [hc] at hcTop
      simpa using hcTop
    have hcV :
        c ∈ active P v := by
      rw [← hcol]
      exact edgeColor_mem_active_upper P htv
    have hproper := P.proper htv
    rw [hcol] at hproper
    exact ⟨hcV, hproper.symm⟩
  · have hcTop :
        P.edgeColor v top ∈ active P top :=
      edgeColor_mem_active_upper P hvt'
    have hcol :
        P.edgeColor v top = c := by
      rw [hc] at hcTop
      simpa using hcTop
    have hcV :
        c ∈ active P v := by
      rw [← hcol]
      exact edgeColor_mem_active_lower P hvt'
    have hproper := P.proper hvt'
    rw [hcol] at hproper
    exact ⟨hcV, hproper⟩

theorem nonTop_rootBit_eq
    {V : Type*} [LinearOrder V]
    {k : ℕ}
    (P : BinaryEdgePartition V k)
    {top : V} {c : Fin k}
    (hroot :
      ∀ v : V, v ≠ top →
        c ∈ active P v ∧
        P.bit v c ≠ P.bit top c)
    {u v : V}
    (hut : u ≠ top)
    (hvt : v ≠ top) :
    P.bit u c = P.bit v c := by
  have hu := (hroot u hut).2
  have hv := (hroot v hvt).2
  cases hutBit : P.bit u c <;>
    cases hvtBit : P.bit v c <;>
    cases htopBit : P.bit top c <;>
    simp_all

theorem nonTop_edgeColor_ne_root
    {V : Type*} [LinearOrder V]
    {k : ℕ}
    (P : BinaryEdgePartition V k)
    {top : V} {c : Fin k}
    (hroot :
      ∀ v : V, v ≠ top →
        c ∈ active P v ∧
        P.bit v c ≠ P.bit top c)
    {u v : V}
    (huv : u < v)
    (hut : u ≠ top)
    (hvt : v ≠ top) :
    P.edgeColor u v ≠ c := by
  intro hcol
  have hproper := P.proper huv
  rw [hcol] at hproper
  exact hproper
    (nonTop_rootBit_eq P hroot hut hvt)

theorem six_point_two_exception_root_factorization
    {V : Type*} [LinearOrder V] [Fintype V]
    {n : ℕ}
    (hn : 4 ≤ n)
    (P : BinaryEdgePartition V n)
    (top bad₁ bad₂ : V)
    (htb₁ : top ≠ bad₁)
    (htb₂ : top ≠ bad₂)
    (hb₁₂ : bad₁ ≠ bad₂)
    (hcard : Fintype.card V = 6)
    (hTop : (active P top).card ≤ 1)
    (hBad₁ : (active P bad₁).card ≤ 4)
    (hBad₂ : (active P bad₂).card ≤ 4)
    (hOther :
      ∀ v : V,
        v ≠ top → v ≠ bad₁ → v ≠ bad₂ →
        (active P v).card ≤ 3) :
    ∃ c : Fin n,
      active P top = {c} ∧
      (∀ v : V, v ≠ top →
        c ∈ active P v ∧
        P.bit v c ≠ P.bit top c) ∧
      (∀ {u v : V}, u < v →
        u ≠ top → v ≠ top →
        P.edgeColor u v ≠ c) ∧
      ((active P bad₁).erase c).card = 3 ∧
      ((active P bad₂).erase c).card = 3 ∧
      (∀ v : V,
        v ≠ top → v ≠ bad₁ → v ≠ bad₂ →
        ((active P v).erase c).card = 2) := by
  classical
  have hexact :=
    six_point_two_min_exceptions_active_exact
      hn P top bad₁ bad₂ htb₁ htb₂ hb₁₂ hcard
      hTop hBad₁ hBad₂ hOther
  obtain ⟨c, htopSet, hroot⟩ :=
    exists_rootColour_of_top_active_card_one
      P top hexact.1
  refine ⟨c, htopSet, hroot, ?_, ?_, ?_, ?_⟩
  · intro u v huv hut hvt
    exact nonTop_edgeColor_ne_root
      P hroot huv hut hvt
  · have hc := (hroot bad₁ htb₁.symm).1
    rw [Finset.card_erase_of_mem hc, hexact.2.1]
    norm_num
  · have hc := (hroot bad₂ htb₂.symm).1
    rw [Finset.card_erase_of_mem hc, hexact.2.2.1]
    norm_num
  · intro v hvt hvb₁ hvb₂
    have hc := (hroot v hvt).1
    rw [Finset.card_erase_of_mem hc,
      hexact.2.2.2 v hvt hvb₁ hvb₂]
    norm_num

#print axioms exists_rootColour_of_top_active_card_one
#print axioms nonTop_rootBit_eq
#print axioms nonTop_edgeColor_ne_root
#print axioms six_point_two_exception_root_factorization

end JSP000404Research
