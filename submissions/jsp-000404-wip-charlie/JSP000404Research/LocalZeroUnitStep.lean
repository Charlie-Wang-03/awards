import JSP000404Research.SaturatedWrapDescent
import JSP000404Research.LocalDirectionCycle
import Mathlib.Tactic

/-!
# Zero-quotient unit steps come from two rays on the same side of the centre

A saturated positive-first value profile contains a zero-quotient unit-band
crossing.  This file pulls that list witness back to the actual rays of a
LocalDirectionCycle.

For adjacent sorted local rays j,k, a zero-quotient unit step means

  floor(value k) = floor(value j)+1,
  floor(value k - value j) = 0.

Hence value k-value j < 1.

If j and k lay on opposite sides of the centre in the ambient linear order,
the DirectionData middleSeparated axiom would force their two incident
direction values to differ by at least one.  Therefore every such crossing
uses two vertices on the same side of the centre.
-/

namespace JSP000404Research
namespace DirectionData

def HasZeroQuotientUnitRayStepFrom
    {V : Type*} [LinearOrder V]
    {t : ℝ}
    (D : DirectionData V t)
    (i : V) :
    OtherVertex i → List (OtherVertex i) → Prop
  | _, [] => False
  | j, k :: ks =>
      (
        Nat.floor (D.localDirectionValue i k) =
            Nat.floor (D.localDirectionValue i j) + 1
        ∧
        Nat.floor
          (D.localDirectionValue i k -
            D.localDirectionValue i j) = 0
      )
      ∨
      HasZeroQuotientUnitRayStepFrom D i k ks

@[simp] theorem hasZeroQuotientUnitRayStepFrom_nil
    {V : Type*} [LinearOrder V]
    {t : ℝ}
    (D : DirectionData V t)
    (i : V) (j : OtherVertex i) :
    ¬ HasZeroQuotientUnitRayStepFrom D i j [] := by
  simp [HasZeroQuotientUnitRayStepFrom]

@[simp] theorem hasZeroQuotientUnitRayStepFrom_cons
    {V : Type*} [LinearOrder V]
    {t : ℝ}
    (D : DirectionData V t)
    (i : V)
    (j k : OtherVertex i)
    (ks : List (OtherVertex i)) :
    HasZeroQuotientUnitRayStepFrom D i j (k :: ks) ↔
      (
        Nat.floor (D.localDirectionValue i k) =
            Nat.floor (D.localDirectionValue i j) + 1
        ∧
        Nat.floor
          (D.localDirectionValue i k -
            D.localDirectionValue i j) = 0
      )
      ∨
      HasZeroQuotientUnitRayStepFrom D i k ks := by
  rfl

/-- Mapping local rays to local values preserves the recursive zero-unit-step
predicate exactly. -/
theorem hasZeroQuotientUnitStep_map_iff_rayStep
    {V : Type*} [LinearOrder V]
    {t : ℝ}
    (D : DirectionData V t)
    (i : V)
    (j : OtherVertex i)
    (js : List (OtherVertex i)) :
    HasZeroQuotientUnitStep
        (D.localDirectionValue i j)
        (js.map (D.localDirectionValue i))
      ↔
    HasZeroQuotientUnitRayStepFrom D i j js := by
  induction js generalizing j with
  | nil =>
      simp [HasZeroQuotientUnitStep,
        HasZeroQuotientUnitRayStepFrom]
  | cons k ks ih =>
      simp only [List.map_cons,
        hasZeroQuotientUnitStep_cons,
        hasZeroQuotientUnitRayStepFrom_cons]
      rw [ih]

/-- A single sorted zero-quotient unit step cannot cross the centre in the
ambient vertex order. -/
theorem zeroQuotientUnitRayStep_same_side
    {V : Type*} [LinearOrder V]
    {t : ℝ}
    (D : DirectionData V t)
    (i : V)
    (j k : OtherVertex i)
    (hle :
      D.localDirectionValue i j ≤
        D.localDirectionValue i k)
    (hzero :
      Nat.floor
        (D.localDirectionValue i k -
          D.localDirectionValue i j) = 0) :
    (j.1 < i ∧ k.1 < i) ∨
      (i < j.1 ∧ i < k.1) := by
  have hgap0 :
      0 ≤
        D.localDirectionValue i k -
          D.localDirectionValue i j :=
    sub_nonneg.mpr hle
  have hgapLt :
      D.localDirectionValue i k -
          D.localDirectionValue i j < 1 := by
    have h :=
      Nat.lt_floor_add_one
        (D.localDirectionValue i k -
          D.localDirectionValue i j)
    rw [hzero] at h
    norm_num at h ⊢
    exact h
  by_cases hjLeft : j.1 < i
  · by_cases hkLeft : k.1 < i
    · exact Or.inl ⟨hjLeft, hkLeft⟩
    · have hiK : i < k.1 := by
        exact lt_of_le_of_ne
          (not_lt.mp hkLeft) k.2.symm
      have hjVal :
          D.localDirectionValue i j =
            D.value j.1 i := by
        simp [localDirectionValue, hjLeft]
      have hkVal :
          D.localDirectionValue i k =
            D.value i k.1 := by
        simp [localDirectionValue, hkLeft]
      have hsep :=
        D.middleSeparated hjLeft hiK
      rw [← hjVal, ← hkVal] at hsep
      rw [abs_of_nonpos
        (sub_nonpos.mpr hle)] at hsep
      linarith
  · have hiJ : i < j.1 := by
      exact lt_of_le_of_ne
        (not_lt.mp hjLeft) j.2.symm
    by_cases hkLeft : k.1 < i
    · have hjVal :
          D.localDirectionValue i j =
            D.value i j.1 := by
        simp [localDirectionValue, hjLeft]
      have hkVal :
          D.localDirectionValue i k =
            D.value k.1 i := by
        simp [localDirectionValue, hkLeft]
      have hsep :=
        D.middleSeparated hkLeft hiJ
      rw [← hkVal, ← hjVal] at hsep
      rw [abs_of_nonneg
        (sub_nonneg.mpr hle)] at hsep
      linarith
    · have hiK : i < k.1 := by
        exact lt_of_le_of_ne
          (not_lt.mp hkLeft) k.2.symm
      exact Or.inr ⟨hiJ, hiK⟩

/-- A zero-unit ray-step witness in a sorted ray list yields two actual
same-side rays carrying that adjacent step. -/
theorem exists_same_side_zeroUnit_pair_of_rayStep
    {V : Type*} [LinearOrder V]
    {t : ℝ}
    (D : DirectionData V t)
    (i : V)
    (j : OtherVertex i)
    (js : List (OtherVertex i))
    (hsorted :
      (j :: js).Pairwise
        (fun a b =>
          D.localDirectionValue i a ≤
            D.localDirectionValue i b))
    (hstep :
      HasZeroQuotientUnitRayStepFrom D i j js) :
    ∃ a b : OtherVertex i,
      a ∈ j :: js ∧
      b ∈ j :: js ∧
      D.localDirectionValue i a ≤
        D.localDirectionValue i b ∧
      Nat.floor (D.localDirectionValue i b) =
        Nat.floor (D.localDirectionValue i a) + 1 ∧
      Nat.floor
        (D.localDirectionValue i b -
          D.localDirectionValue i a) = 0 ∧
      ((a.1 < i ∧ b.1 < i) ∨
        (i < a.1 ∧ i < b.1)) := by
  induction js generalizing j with
  | nil =>
      simp [HasZeroQuotientUnitRayStepFrom] at hstep
  | cons k ks ih =>
      have hp := List.pairwise_cons.mp hsorted
      have hjk :
          D.localDirectionValue i j ≤
            D.localDirectionValue i k :=
        hp.1 k (by simp)
      have htail :
          (k :: ks).Pairwise
            (fun a b =>
              D.localDirectionValue i a ≤
                D.localDirectionValue i b) :=
        hp.2
      rw [hasZeroQuotientUnitRayStepFrom_cons] at hstep
      rcases hstep with hhead | htailStep
      · have hside :=
          zeroQuotientUnitRayStep_same_side
            D i j k hjk hhead.2
        exact ⟨j, k, by simp, by simp,
          hjk, hhead.1, hhead.2, hside⟩
      · obtain ⟨a, b, ha, hb, hab,
          hfloor, hzero, hside⟩ :=
          ih k htail htailStep
        refine ⟨a, b, ?_, ?_, hab,
          hfloor, hzero, hside⟩
        · simp only [List.mem_cons]
          exact Or.inr ha
        · simp only [List.mem_cons]
          exact Or.inr hb

namespace LocalDirectionCycle

/-- Value-level zero-unit descent in a complete local cycle produces two actual
same-side incident rays. -/
theorem exists_same_side_zeroUnit_pair
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ}
    {D : DirectionData V t} {i : V}
    (L : LocalDirectionCycle D i)
    (hstep :
      match L.values with
      | [] => False
      | a :: xs => HasZeroQuotientUnitStep a xs) :
    ∃ a b : OtherVertex i,
      a ∈ L.rays ∧
      b ∈ L.rays ∧
      D.localDirectionValue i a ≤
        D.localDirectionValue i b ∧
      Nat.floor (D.localDirectionValue i b) =
        Nat.floor (D.localDirectionValue i a) + 1 ∧
      Nat.floor
        (D.localDirectionValue i b -
          D.localDirectionValue i a) = 0 ∧
      ((a.1 < i ∧ b.1 < i) ∨
        (i < a.1 ∧ i < b.1)) := by
  cases hrays : L.rays with
  | nil =>
      exact False.elim (L.nonempty hrays)
  | cons j js =>
      have hvalues :
          L.values =
            D.localDirectionValue i j ::
              js.map (D.localDirectionValue i) := by
        simp [LocalDirectionCycle.values, hrays]
      have hstep' :
          HasZeroQuotientUnitStep
            (D.localDirectionValue i j)
            (js.map (D.localDirectionValue i)) := by
        simpa [hvalues] using hstep
      have hrayStep :
          HasZeroQuotientUnitRayStepFrom D i j js :=
        (hasZeroQuotientUnitStep_map_iff_rayStep
          D i j js).1 hstep'
      have hsorted :
          (j :: js).Pairwise
            (fun a b =>
              D.localDirectionValue i a ≤
                D.localDirectionValue i b) := by
        simpa [hrays] using L.value_sorted
      obtain ⟨a, b, ha, hb, hab,
          hfloor, hzero, hside⟩ :=
        exists_same_side_zeroUnit_pair_of_rayStep
          D i j js hsorted hrayStep
      exact ⟨a, b,
        by simpa [hrays] using ha,
        by simpa [hrays] using hb,
        hab, hfloor, hzero, hside⟩

#print axioms exists_same_side_zeroUnit_pair

end LocalDirectionCycle

#print axioms zeroQuotientUnitRayStep_same_side
#print axioms exists_same_side_zeroUnit_pair_of_rayStep

end DirectionData
end JSP000404Research
