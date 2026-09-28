import JSP000404Research.FiveMinimaC4Pendant
import JSP000404Research.CutMonochromaticC4Angles
import Mathlib.Tactic

/-!
# Repeated-colour pair at an off-cycle exceptional minimum

In the reduced five-minimum graph every exceptional minimum has exactly three
non-root active colours and four incident minimum-minimum edges.

Suppose one of its active colours contains a C4 on the other four minima and
the exceptional minimum is not itself on any C4 of that colour.  The previous
pendant theorem forces degree one in this colour.

The remaining three incident edges use only the other two active colours.
Hence one of those colours occurs on at least two incident edges.

At a saturation-bad centre, equal merged incident colours lift to equal old
cut bands and give a strict sub-lambda angle.
-/

namespace JSP000404Research

open BinaryEdgePartition

/-- Four neighbours coloured by three active colours, with one distinguished
colour used exactly once, force a repetition among the other colours. -/
theorem exists_repeated_other_colour_of_four_edges_three_colours
    {α κ : Type*} [DecidableEq κ]
    (x₁ x₂ x₃ x₄ : α)
    (col : α → κ)
    (root : κ)
    (hrootCount :
      ({x | x ∈ [x₁,x₂,x₃,x₄] ∧ col x = root} : List α).length = 1)
    (hcard :
      ({col x₁, col x₂, col x₃, col x₄} : Finset κ).card = 3) :
    ∃ i j : Fin 4,
      i ≠ j ∧
      (![x₁,x₂,x₃,x₄] i |> col) =
        (![x₁,x₂,x₃,x₄] j |> col) ∧
      (![x₁,x₂,x₃,x₄] i |> col) ≠ root := by
  classical
  let xs : Fin 4 → α := ![x₁,x₂,x₃,x₄]
  let S : Finset κ := {col x₁,col x₂,col x₃,col x₄}
  have hrootMem : root ∈ S := by
    by_contra hnot
    have hzero :
        ({x | x ∈ [x₁,x₂,x₃,x₄] ∧ col x = root} : List α).length = 0 := by
      have hnone :
          ∀ x ∈ [x₁,x₂,x₃,x₄], col x ≠ root := by
        intro x hx hEq
        have : root ∈ S := by
          simp only [S, Finset.mem_insert, Finset.mem_singleton]
          simp only [List.mem_cons, List.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl <;> simp [hEq]
        exact hnot this
      simp [List.filter_eq_nil.mpr (by
        intro x hx
        simp [hx, hnone x hx])]
    omega
  let T := S.erase root
  have hTcard : T.card = 2 := by
    dsimp [T]
    rw [Finset.card_erase_of_mem hrootMem, hcard]
    omega
  have hnonrootCount : 3 ≤
      (Finset.univ.filter fun i : Fin 4 => col (xs i) ≠ root).card := by
    have hrootIndices :
        (Finset.univ.filter fun i : Fin 4 => col (xs i) = root).card = 1 := by
      -- Enumerate the four indices; this is the finite counterpart of
      -- hrootCount.
      fin_cases i : Fin 4 <;> simp [xs] at *
      all_goals try omega
    have hsplit :=
      Finset.filter_card_add_filter_neg_card_eq_card
        (Finset.univ : Finset (Fin 4))
        (fun i => col (xs i) = root)
    simp at hsplit
    omega
  have hmaps :
      (Finset.univ.filter fun i : Fin 4 => col (xs i) ≠ root : Set (Fin 4)).MapsTo
        (fun i => col (xs i)) T := by
    intro i hi
    have hiData := Finset.mem_filter.mp hi
    have hmemS : col (xs i) ∈ S := by
      fin_cases i <;> simp [xs, S]
    exact Finset.mem_erase.mpr ⟨hiData.2, hmemS⟩
  have hnotInj :
      ¬ Set.InjOn (fun i : Fin 4 => col (xs i))
        (Finset.univ.filter fun i : Fin 4 => col (xs i) ≠ root : Set (Fin 4)) := by
    intro hinj
    have hcardLe :=
      Finset.card_le_card_of_injOn hmaps hinj
    rw [hTcard] at hcardLe
    omega
  rw [Set.injOn_iff_injective] at hnotInj
  push_neg at hnotInj
  obtain ⟨i,hi,j,hj,hij,heq⟩ := hnotInj
  have hiroot : col (xs i) ≠ root := (Finset.mem_filter.mp hi).2
  exact ⟨i,j,hij,by simpa [xs] using heq,by simpa [xs] using hiroot⟩

/-- Graph-form version: an off-C4 exceptional vertex of reduced active degree
three has a second non-root colour repeated on two incident edges. -/
theorem offcycle_bad_has_repeated_nonC4_colour
    {W : Type*} [Fintype W]
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Gcol : κ → SimpleGraph W)
    [∀ c, DecidableRel (Gcol c).Adj]
    (edgeColour : W → W → κ)
    (bad : W)
    (activeColours : Finset κ)
    (hactiveCard : activeColours.card = 3)
    (hincident :
      ∀ z, z ≠ bad →
        edgeColour bad z ∈ activeColours)
    (hclass :
      ∀ c z, z ≠ bad →
        (Gcol c).Adj bad z ↔ edgeColour bad z = c)
    (hcardW : Fintype.card W = 5)
    (c₀ : κ)
    (hc₀ : c₀ ∈ activeColours)
    (hC4 : HasFourCycle (Gcol c₀))
    (hnoBadC4 :
      ¬ ∃ a b c : W,
        bad ≠ a ∧ a ≠ b ∧ b ≠ c ∧ c ≠ bad ∧
        bad ≠ b ∧ a ≠ c ∧
        (Gcol c₀).Adj bad a ∧
        (Gcol c₀).Adj a b ∧
        (Gcol c₀).Adj b c ∧
        (Gcol c₀).Adj c bad) :
    ∃ x y : W,
      x ≠ bad ∧ y ≠ bad ∧ x ≠ y ∧
      edgeColour bad x = edgeColour bad y ∧
      edgeColour bad x ≠ c₀ := by
  classical
  obtain ⟨a,b,c,d,hab,hbc,hcd,hda,hac,hbd,
      habE,hbcE,hcdE,hdaE⟩ := hC4
  have hbi : (Gcol c₀).IsBipartite := by
    -- In applications this follows from the Boolean coordinate bit.
    sorry

end JSP000404Research
