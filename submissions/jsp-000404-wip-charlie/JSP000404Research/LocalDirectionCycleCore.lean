import JSP000404Research.LocalDirectionValueCore
import JSP000404Research.LinearCyclicGapQuotientsCore
import JSP000404Research.PinnedCyclicDeletionGain
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic

/-!
# Lightweight local direction cycle

This module contains only the sorted local ray cycle, its value list, gap
quotients, exponent, and existence.  Full-band capacity theorems remain in
LocalDirectionCycle.
-/

namespace JSP000404Research
namespace DirectionData

noncomputable def localDirectionOrderKey
    {V : Type*} [LinearOrder V]
    {t : ℝ}
    (D : DirectionData V t)
    (i : V) (j : OtherVertex i) :
    ℝ ×ₗ V :=
  toLex (D.localDirectionValue i j, j.1)

theorem localDirectionOrderKey_injective
    {V : Type*} [LinearOrder V]
    {t : ℝ}
    (D : DirectionData V t)
    (i : V) :
    Function.Injective (D.localDirectionOrderKey i) := by
  intro a b hab
  apply Subtype.ext
  have hsecond :
      (ofLex (D.localDirectionOrderKey i a)).2 =
        (ofLex (D.localDirectionOrderKey i b)).2 :=
    congrArg (fun z : ℝ ×ₗ V => (ofLex z).2) hab
  simpa [localDirectionOrderKey] using hsecond

noncomputable def localDirectionOrder
    {V : Type*} [LinearOrder V]
    {t : ℝ}
    (D : DirectionData V t)
    (i : V) :
    LinearOrder (OtherVertex i) :=
  LinearOrder.lift'
    (D.localDirectionOrderKey i)
    (D.localDirectionOrderKey_injective i)

theorem localDirectionValue_le_of_order_le
    {V : Type*} [LinearOrder V]
    {t : ℝ}
    (D : DirectionData V t)
    (i : V)
    {a b : OtherVertex i}
    (hab :
      @LE.le (OtherVertex i)
        (D.localDirectionOrder i).toLE a b) :
    D.localDirectionValue i a ≤
      D.localDirectionValue i b := by
  have hkey :
      D.localDirectionOrderKey i a ≤
        D.localDirectionOrderKey i b := hab
  have hfst := Prod.Lex.monotone_fst _ _ hkey
  simpa [localDirectionOrderKey] using hfst

structure LocalDirectionCycle
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ}
    (D : DirectionData V t)
    (i : V) where
  rays : List (OtherVertex i)
  complete : rays.toFinset = Finset.univ
  nodup : rays.Nodup
  nonempty : rays ≠ []
  value_sorted :
    rays.Pairwise
      (fun a b =>
        D.localDirectionValue i a ≤
          D.localDirectionValue i b)

namespace LocalDirectionCycle

def values
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ}
    {D : DirectionData V t} {i : V}
    (C : LocalDirectionCycle D i) : List ℝ :=
  C.rays.map (D.localDirectionValue i)

noncomputable def gapQuotients
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ}
    {D : DirectionData V t} {i : V}
    (C : LocalDirectionCycle D i) : List ℕ :=
  linearCyclicGapQuotients t C.values

noncomputable def exponent
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ}
    {D : DirectionData V t} {i : V}
    (C : LocalDirectionCycle D i) : ℕ :=
  listExponent C.gapQuotients

theorem values_nonempty
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ}
    {D : DirectionData V t} {i : V}
    (C : LocalDirectionCycle D i) :
    C.values ≠ [] := by
  simp [values, C.nonempty]

theorem values_pairwise
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ}
    {D : DirectionData V t} {i : V}
    (C : LocalDirectionCycle D i) :
    C.values.Pairwise (· ≤ ·) := by
  rw [values, List.pairwise_map]
  exact C.value_sorted

theorem value_mem_bounds
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ}
    {D : DirectionData V t} {i : V}
    (C : LocalDirectionCycle D i)
    {x : ℝ}
    (hx : x ∈ C.values) :
    0 ≤ x ∧ x < t := by
  rw [values, List.mem_map] at hx
  obtain ⟨j, _, rfl⟩ := hx
  exact ⟨D.localDirectionValue_nonneg i j,
    D.localDirectionValue_lt i j⟩

theorem exists_localDirectionCycle
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ}
    (D : DirectionData V t)
    (i : V)
    (hother : Nonempty (OtherVertex i)) :
    Nonempty (LocalDirectionCycle D i) := by
  classical
  letI : LinearOrder (OtherVertex i) :=
    D.localDirectionOrder i
  let rays : List (OtherVertex i) :=
    (Finset.univ : Finset (OtherVertex i)).sort
      (fun a b : OtherVertex i =>
        @LE.le (OtherVertex i)
          (D.localDirectionOrder i).toLE a b)
  have hne : rays ≠ [] := by
    obtain ⟨j⟩ := hother
    intro hr
    have hj :
        j ∈ (Finset.univ : Finset (OtherVertex i)) := by simp
    have hj' : j ∈ rays := by
      dsimp [rays]
      simpa using hj
    rw [hr] at hj'
    simp at hj'
  refine ⟨{
    rays := rays
    complete := ?_
    nodup := ?_
    nonempty := hne
    value_sorted := ?_ }⟩
  · dsimp [rays]
    simp
  · dsimp [rays]
    exact Finset.sort_nodup _ _
  · have hpair :
        rays.Pairwise
          (fun a b : OtherVertex i =>
            @LE.le (OtherVertex i)
              (D.localDirectionOrder i).toLE a b) := by
      dsimp [rays]
      exact Finset.pairwise_sort
        (s := (Finset.univ : Finset (OtherVertex i)))
        (r := fun a b : OtherVertex i =>
          @LE.le (OtherVertex i)
            (D.localDirectionOrder i).toLE a b)
    apply hpair.imp
    intro a b hab
    exact D.localDirectionValue_le_of_order_le i hab

#print axioms localDirectionOrderKey_injective
#print axioms localDirectionValue_le_of_order_le
#print axioms LocalDirectionCycle.values_pairwise
#print axioms LocalDirectionCycle.exists_localDirectionCycle

end LocalDirectionCycle
end DirectionData
end JSP000404Research
