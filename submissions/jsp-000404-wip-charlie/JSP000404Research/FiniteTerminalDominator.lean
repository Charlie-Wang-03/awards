import JSP000404Research.MinimumDominatingPhaseCover
import Mathlib.Tactic

/-!
# Compression by a finite terminal-dominator map

MinimumDominatingPhaseCover phrases the compression through an abstract finite
slot type with one distinguished top obstruction in every slot.  For the
geometric application it is more convenient to work directly with a finite
obstruction family and a terminalization map.

Assume tau sends every obstruction in S to another obstruction in S and the
bad set of tau(i) contains the bad set of i.  Then tau is injective on any
minimum-cardinality subcover: if two selected obstructions have the same
terminal dominator, one can delete one of them (when the terminal is already
selected) or replace both by their common terminal dominator.

Consequently

  card(minimum cover) <= card(S.image tau).

Thus the final geometry only has to bound the number of distinct terminal
adjacent transition gaps produced by the refinement map.
-/

namespace JSP000404Research

structure FiniteTerminalDominator
    {I Phase : Type*} [DecidableEq I]
    (A : I → Phase → Prop)
    (S : Finset I) where
  terminal : I → I
  terminal_mem : ∀ i, i ∈ S → terminal i ∈ S
  dominates :
    ∀ i, i ∈ S → ∀ x, A i x → A (terminal i) x

/-- A minimum cover cannot contain two distinct obstructions with the same
terminal dominator. -/
theorem terminal_injective_on_minimum_cover
    {I Phase : Type*} [DecidableEq I]
    (A : I → Phase → Prop)
    (S T : Finset I)
    (hmin : MinimumCardCover A S T)
    (D : FiniteTerminalDominator A S) :
    ∀ {i j : I}, i ∈ T → j ∈ T →
      D.terminal i = D.terminal j → i = j := by
  classical
  intro i j hi hj hterm
  by_contra hij
  let k := D.terminal i
  have hiS : i ∈ S := hmin.1 hi
  have hjS : j ∈ S := hmin.1 hj
  have hkS : k ∈ S := D.terminal_mem i hiS
  have hdomI : ∀ x, A i x → A k x := by
    intro x hx
    exact D.dominates i hiS x hx
  have hdomJ : ∀ x, A j x → A k x := by
    intro x hx
    have h := D.dominates j hjS x hx
    simpa [k, hterm] using h
  by_cases hkT : k ∈ T
  · by_cases hki : k = i
    · have hkj : k ≠ j := by
        intro h
        apply hij
        rw [← hki, h]
      let U := T.erase j
      have hUS : U ⊆ S :=
        (Finset.erase_subset j T).trans hmin.1
      have hUCover : PredicateCovers A U := by
        intro x
        obtain ⟨r, hrT, hrA⟩ := hmin.2.1 x
        by_cases hrj : r = j
        · subst r
          exact ⟨k, Finset.mem_erase.mpr ⟨hkj, hkT⟩,
            hdomJ x hrA⟩
        · exact ⟨r, Finset.mem_erase.mpr ⟨hrj, hrT⟩, hrA⟩
      have hc := hmin.2.2 U hUS hUCover
      have he := Finset.card_erase_of_mem hj
      dsimp [U] at hc
      rw [he] at hc
      omega
    · let U := T.erase i
      have hUS : U ⊆ S :=
        (Finset.erase_subset i T).trans hmin.1
      have hUCover : PredicateCovers A U := by
        intro x
        obtain ⟨r, hrT, hrA⟩ := hmin.2.1 x
        by_cases hri : r = i
        · subst r
          exact ⟨k, Finset.mem_erase.mpr ⟨hki, hkT⟩,
            hdomI x hrA⟩
        · exact ⟨r, Finset.mem_erase.mpr ⟨hri, hrT⟩, hrA⟩
      have hc := hmin.2.2 U hUS hUCover
      have he := Finset.card_erase_of_mem hi
      dsimp [U] at hc
      rw [he] at hc
      omega
  · let U := insert k ((T.erase i).erase j)
    have hUS : U ⊆ S := by
      intro r hr
      simp only [U, Finset.mem_insert, Finset.mem_erase] at hr
      rcases hr with rfl | hr
      · exact hkS
      · exact hmin.1 hr.2.2
    have hUCover : PredicateCovers A U := by
      intro x
      obtain ⟨r, hrT, hrA⟩ := hmin.2.1 x
      by_cases hri : r = i
      · subst r
        exact ⟨k, by simp [U], hdomI x hrA⟩
      · by_cases hrj : r = j
        · subst r
          exact ⟨k, by simp [U], hdomJ x hrA⟩
        · exact ⟨r, by simp [U, hri, hrj, hrT], hrA⟩
    have hjErase : j ∈ T.erase i :=
      Finset.mem_erase.mpr ⟨hij.symm, hj⟩
    have hkNot : k ∉ (T.erase i).erase j := by
      intro hk
      exact hkT (Finset.mem_of_mem_erase
        (Finset.mem_of_mem_erase hk))
    have hcardU : U.card = T.card - 1 := by
      dsimp [U]
      rw [Finset.card_insert_of_notMem hkNot,
          Finset.card_erase_of_mem hjErase,
          Finset.card_erase_of_mem hi]
      omega
    have hc := hmin.2.2 U hUS hUCover
    rw [hcardU] at hc
    omega

/-- Minimum-cover size is bounded by the number of distinct terminal
dominators occurring in the original finite family. -/
theorem minimum_cover_card_le_terminal_image
    {I Phase : Type*} [DecidableEq I]
    (A : I → Phase → Prop)
    (S T : Finset I)
    (hmin : MinimumCardCover A S T)
    (D : FiniteTerminalDominator A S) :
    T.card ≤ (S.image D.terminal).card := by
  classical
  have hinj :
      Set.InjOn D.terminal (↑T : Set I) := by
    intro i hi j hj hij
    exact terminal_injective_on_minimum_cover
      A S T hmin D hi hj hij
  have hcardImage :
      (T.image D.terminal).card = T.card :=
    Finset.card_image_iff.mpr hinj
  have hsubset :
      T.image D.terminal ⊆ S.image D.terminal := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hiT, rfl⟩
    exact Finset.mem_image.mpr ⟨i, hmin.1 hiT, rfl⟩
  rw [← hcardImage]
  exact Finset.card_le_card hsubset

/-- Final contradiction once the distinct terminal image itself fits into the
global lower-branch turn budget. -/
theorem no_phase_cover_of_terminal_image_budget
    {I : Type*} [DecidableEq I]
    (L R : I → ℝ)
    (S : Finset I)
    (D : FiniteTerminalDominator
      (InClosedInterval L R) S)
    (n : ℕ) (delta : ℝ)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hterminalBudget :
      ((S.image D.terminal).card : ℝ) ≤
        2 * ((n : ℝ) + delta))
    (hcoverLower :
      ∀ T : Finset I, T ⊆ S →
        PredicateCovers (InClosedInterval L R) T →
        (n : ℝ) + delta ≤ (T.card : ℝ) * delta) :
    ¬ PredicateCovers (InClosedInterval L R) S := by
  intro hcover
  obtain ⟨T, hmin⟩ :=
    exists_minimum_card_subcover
      (InClosedInterval L R) S hcover
  have hcardTerm :
      T.card ≤ (S.image D.terminal).card :=
    minimum_cover_card_le_terminal_image
      (InClosedInterval L R) S T hmin D
  have htermNat :
      (S.image D.terminal).card ≤ 2 * n :=
    hull_count_upper hdeltaHalf hterminalBudget
  have hupper : T.card ≤ 2 * n :=
    hcardTerm.trans htermNat
  have hcoverReal :=
    hcoverLower T hmin.1 hmin.2.1
  have hlower :=
    phase_cover_count_lower
      hn hdelta0 hdeltaHalf hcoverReal
  omega

#print axioms terminal_injective_on_minimum_cover
#print axioms minimum_cover_card_le_terminal_image
#print axioms no_phase_cover_of_terminal_image_budget

end JSP000404Research
