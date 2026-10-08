import JSP000404Research.ThreeWholeCubeGlobalExtreme
import JSP000404Research.RetainedBitOrientationLight
import Mathlib.Tactic

/-!
# Uniqueness of the global extreme in a three-whole-cube code star

For a projected-loss vertex:
* global minimum => every retained active colour is outgoing => all retained
  bits are false;
* global maximum => every retained active colour is incoming => all retained
  bits are true.

In a three-whole-cube star the four retained codes are a 3-bit Boolean star:
the source code and its three one-coordinate flips.  At most one of those four
codes can be constant (000 or 111).

Hence among the four saturated whole-cube vertices there is at most one global
order extreme.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

def ConstantRetainedCode
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) : Prop :=
  AllRetainedBitsFalse C v ∨ AllRetainedBitsTrue C v

theorem projectedLoss_global_min_allFalse
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hmin : ∀ w : V, w ≠ v → v < w) :
    AllRetainedBitsFalse C v := by
  intro c hc
  have hsplit :=
    retainedActive_eq_incoming_union_outgoing C v
  rw [hsplit] at hc
  rcases Finset.mem_union.mp hc with hIn | hOut
  · obtain ⟨w,hwv,_hcol⟩ :=
      (mem_incomingRetained_iff C v c).1 hIn
    have hvw := hmin w (ne_of_lt hwv)
    exact False.elim ((not_lt_of_ge hvw.le) hwv)
  · simpa [retainedBit] using (bit_false_of_outgoingRetained C hOut)

theorem projectedLoss_global_max_allTrue
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hmax : ∀ w : V, w ≠ v → w < v) :
    AllRetainedBitsTrue C v := by
  intro c hc
  have hsplit :=
    retainedActive_eq_incoming_union_outgoing C v
  rw [hsplit] at hc
  rcases Finset.mem_union.mp hc with hIn | hOut
  · exact
      (mem_incomingRetained_iff_retainedBit_true_light C v c).1 hIn
  · obtain ⟨w,hvw,_hcol⟩ :=
      (mem_outgoingRetained_iff C v c).1 hOut
    have hwv := hmax w (ne_of_lt hvw).symm
    exact False.elim ((not_lt_of_ge hwv.le) hvw)

theorem projectedLoss_globalExtreme_constantCode
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hextreme :
      (∀ w : V, w ≠ v → v < w) ∨
      (∀ w : V, w ≠ v → w < v)) :
    ConstantRetainedCode C v := by
  rcases hextreme with hmin | hmax
  · exact Or.inl
      (projectedLoss_global_min_allFalse
        C exponent hvLoss hmin)
  · exact Or.inr
      (projectedLoss_global_max_allTrue
        C exponent hvLoss hmax)

theorem bool_three_star_at_most_one_constant
    (b₁ b₂ b₃ : Bool) :
    let p0 := (b₁,b₂,b₃)
    let p1 := (!b₁,b₂,b₃)
    let p2 := (b₁,!b₂,b₃)
    let p3 := (b₁,b₂,!b₃)
    let isConst : Bool × Bool × Bool → Prop :=
      fun p =>
        (p.1 = false ∧ p.2.1 = false ∧ p.2.2 = false) ∨
        (p.1 = true ∧ p.2.1 = true ∧ p.2.2 = true)
    ∀ i j : Fin 4,
      i ≠ j →
      ¬ (isConst (![p0,p1,p2,p3] i) ∧
         isConst (![p0,p1,p2,p3] j)) := by
  dsimp
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all <;>
    cases b₁ <;> cases b₂ <;> cases b₃ <;> simp_all

theorem threeWholeCubePartners_at_most_one_constantCode
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v s₁ s₂ s₃ : V}
    {c₁ c₂ c₃ : Fin n}
    (hc12 : c₁ ≠ c₂)
    (hc13 : c₁ ≠ c₃)
    (hc23 : c₂ ≠ c₃)
    (hactive :
      retainedActive C v = {c₁,c₂,c₃})
    (h₁ : WholeCubeQTPair C s₁ v c₁)
    (h₂ : WholeCubeQTPair C s₂ v c₂)
    (h₃ : WholeCubeQTPair C s₃ v c₃) :
    ∀ a b : V,
      a ∈ ({v,s₁,s₂,s₃} : Finset V) →
      b ∈ ({v,s₁,s₂,s₃} : Finset V) →
      a ≠ b →
      ¬ (ConstantRetainedCode C a ∧
         ConstantRetainedCode C b) := by
  classical
  have hc1V : c₁ ∈ retainedActive C v := by
    rw [hactive]
    simp
  have hc2V : c₂ ∈ retainedActive C v := by
    rw [hactive]
    simp
  have hc3V : c₃ ∈ retainedActive C v := by
    rw [hactive]
    simp
  have hstar :=
    threeWholeCubePartners_retainedCode_star
      C hc1V hc2V hc3V h₁ h₂ h₃
  let b₁ := retainedBit C v c₁
  let b₂ := retainedBit C v c₂
  let b₃ := retainedBit C v c₃

  have profileV :
      ConstantRetainedCode C v →
      ((b₁ = false ∧ b₂ = false ∧ b₃ = false) ∨
       (b₁ = true ∧ b₂ = true ∧ b₃ = true)) := by
    intro h
    rcases h with hF | hT
    · left
      exact ⟨hF c₁ hc1V,hF c₂ hc2V,hF c₃ hc3V⟩
    · right
      exact ⟨hT c₁ hc1V,hT c₂ hc2V,hT c₃ hc3V⟩

  have profileS1 :
      ConstantRetainedCode C s₁ →
      (((!b₁) = false ∧ b₂ = false ∧ b₃ = false) ∨
       ((!b₁) = true ∧ b₂ = true ∧ b₃ = true)) := by
    intro h
    have hc1S : c₁ ∈ retainedActive C s₁ := by
      rw [hstar.1.1,hactive]
      simp
    have hc2S : c₂ ∈ retainedActive C s₁ := by
      rw [hstar.1.1,hactive]
      simp
    have hc3S : c₃ ∈ retainedActive C s₁ := by
      rw [hstar.1.1,hactive]
      simp
    rcases h with hF | hT
    · left
      refine ⟨?_,?_,?_⟩
      · simpa [b₁] using
          hstar.1.2.1.symm.trans (hF c₁ hc1S)
      · exact
          (hstar.1.2.2 c₂ hc2V hc12.symm).symm.trans
            (hF c₂ hc2S)
      · exact
          (hstar.1.2.2 c₃ hc3V hc13.symm).symm.trans
            (hF c₃ hc3S)
    · right
      refine ⟨?_,?_,?_⟩
      · simpa [b₁] using
          hstar.1.2.1.symm.trans (hT c₁ hc1S)
      · exact
          (hstar.1.2.2 c₂ hc2V hc12.symm).symm.trans
            (hT c₂ hc2S)
      · exact
          (hstar.1.2.2 c₃ hc3V hc13.symm).symm.trans
            (hT c₃ hc3S)

  have profileS2 :
      ConstantRetainedCode C s₂ →
      ((b₁ = false ∧ (!b₂) = false ∧ b₃ = false) ∨
       (b₁ = true ∧ (!b₂) = true ∧ b₃ = true)) := by
    intro h
    have hc1S : c₁ ∈ retainedActive C s₂ := by
      rw [hstar.2.1.1,hactive]
      simp
    have hc2S : c₂ ∈ retainedActive C s₂ := by
      rw [hstar.2.1.1,hactive]
      simp
    have hc3S : c₃ ∈ retainedActive C s₂ := by
      rw [hstar.2.1.1,hactive]
      simp
    rcases h with hF | hT
    · left
      refine ⟨?_,?_,?_⟩
      · exact
          (hstar.2.1.2.2 c₁ hc1V hc12).symm.trans
            (hF c₁ hc1S)
      · simpa [b₂] using
          hstar.2.1.2.1.symm.trans (hF c₂ hc2S)
      · exact
          (hstar.2.1.2.2 c₃ hc3V hc23.symm).symm.trans
            (hF c₃ hc3S)
    · right
      refine ⟨?_,?_,?_⟩
      · exact
          (hstar.2.1.2.2 c₁ hc1V hc12).symm.trans
            (hT c₁ hc1S)
      · simpa [b₂] using
          hstar.2.1.2.1.symm.trans (hT c₂ hc2S)
      · exact
          (hstar.2.1.2.2 c₃ hc3V hc23.symm).symm.trans
            (hT c₃ hc3S)

  have profileS3 :
      ConstantRetainedCode C s₃ →
      ((b₁ = false ∧ b₂ = false ∧ (!b₃) = false) ∨
       (b₁ = true ∧ b₂ = true ∧ (!b₃) = true)) := by
    intro h
    have hc1S : c₁ ∈ retainedActive C s₃ := by
      rw [hstar.2.2.1,hactive]
      simp
    have hc2S : c₂ ∈ retainedActive C s₃ := by
      rw [hstar.2.2.1,hactive]
      simp
    have hc3S : c₃ ∈ retainedActive C s₃ := by
      rw [hstar.2.2.1,hactive]
      simp
    rcases h with hF | hT
    · left
      refine ⟨?_,?_,?_⟩
      · exact
          (hstar.2.2.2.2 c₁ hc1V hc13).symm.trans
            (hF c₁ hc1S)
      · exact
          (hstar.2.2.2.2 c₂ hc2V hc23).symm.trans
            (hF c₂ hc2S)
      · simpa [b₃] using
          hstar.2.2.2.1.symm.trans (hF c₃ hc3S)
    · right
      refine ⟨?_,?_,?_⟩
      · exact
          (hstar.2.2.2.2 c₁ hc1V hc13).symm.trans
            (hT c₁ hc1S)
      · exact
          (hstar.2.2.2.2 c₂ hc2V hc23).symm.trans
            (hT c₂ hc2S)
      · simpa [b₃] using
          hstar.2.2.2.1.symm.trans (hT c₃ hc3S)

  intro a b ha hb hab hpair
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with ha | ha | ha | ha <;>
    rcases hb with hb | hb | hb | hb
  all_goals
    subst a
    subst b
  all_goals
    try { exact (hab rfl).elim }
  all_goals
    first
    | have haP := profileV hpair.1
      have hbP := profileS1 hpair.2
      rcases haP with ha0 | ha1 <;>
        rcases hbP with hb0 | hb1 <;>
        simp_all
    | have haP := profileV hpair.1
      have hbP := profileS2 hpair.2
      rcases haP with ha0 | ha1 <;>
        rcases hbP with hb0 | hb1 <;>
        simp_all
    | have haP := profileV hpair.1
      have hbP := profileS3 hpair.2
      rcases haP with ha0 | ha1 <;>
        rcases hbP with hb0 | hb1 <;>
        simp_all
    | have haP := profileS1 hpair.1
      have hbP := profileS2 hpair.2
      rcases haP with ha0 | ha1 <;>
        rcases hbP with hb0 | hb1 <;>
        simp_all
    | have haP := profileS1 hpair.1
      have hbP := profileS3 hpair.2
      rcases haP with ha0 | ha1 <;>
        rcases hbP with hb0 | hb1 <;>
        simp_all
    | have haP := profileS2 hpair.1
      have hbP := profileS3 hpair.2
      rcases haP with ha0 | ha1 <;>
        rcases hbP with hb0 | hb1 <;>
        simp_all

#print axioms projectedLoss_global_min_allFalse
#print axioms projectedLoss_global_max_allTrue
#print axioms threeWholeCubePartners_at_most_one_constantCode

end OrderedEdgeColoring
end JSP000404Research
