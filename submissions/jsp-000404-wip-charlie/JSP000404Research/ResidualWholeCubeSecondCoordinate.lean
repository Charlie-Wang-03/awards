import JSP000404Research.ResidualQTTTWholeCubeAugmentingTerminal
import JSP000404Research.ResidualLossAllActiveCandidateBlock
import JSP000404Research.ResidualLossAllActiveSlices
import Mathlib.Tactic

/-!
# Extra whole-cube shared words come from a second translated coordinate

Let v be a projected-loss vertex and suppose (s,v,c) is a WholeCubeQTPair:
the c-translated slice of v is exactly the base completion cube of s.

If a word lies in the enlarged block of v but lies in neither Q_v nor Q_s,
then it cannot belong to the base slice and it cannot belong to the
c-translated slice.  Hence it belongs to a translated slice indexed by some
other active coordinate d != c.

Applied to WholeCubeThirdSourceWitness, every augmenting witness therefore
carries a genuine second translated-coordinate incidence at the whole-cube
partner.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem wholeCube_extra_word_has_other_translated_coordinate
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {s v : V} {c : Fin n}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwhole : WholeCubeQTPair C s v c)
    {word : Fin n → Bool}
    (hvBlock :
      word ∈ enlargedProjectedCandidateBlock C exponent v)
    (hnotV :
      word ∉ retainedCompletionWords C v)
    (hnotS :
      word ∉ retainedCompletionWords C s) :
    ∃ d : Fin n,
      d ∈ retainedActive C v ∧
      d ≠ c ∧
      word ∈ translatedCompletionWords C v d := by
  rw [enlargedProjectedCandidateBlock_loss C exponent hvLoss] at hvBlock
  unfold allActiveLossCandidateBlock at hvBlock
  rcases Finset.mem_union.mp hvBlock with hbase | htrans
  · exact False.elim (hnotV hbase)
  · unfold allActiveTranslatedWords at htrans
    obtain ⟨d,hdActive,hdWord⟩ :=
      Finset.mem_biUnion.mp htrans
    have hdc : d ≠ c := by
      intro hdc
      subst d
      rcases hwhole with ⟨_hactiveEq,htransEq⟩
      rw [htransEq] at hdWord
      exact hnotS hdWord
    exact ⟨d,hdActive,hdc,hdWord⟩

theorem wholeCubeThirdSourceWitness_has_other_translated_coordinate
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T : Finset V}
    {s v : V} {c : Fin n}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwhole : WholeCubeQTPair C s v c)
    (hwit : WholeCubeThirdSourceWitness C exponent T s v) :
    ∃ word : Fin n → Bool,
    ∃ w : V,
    ∃ d : Fin n,
      d ∈ retainedActive C v ∧
      d ≠ c ∧
      word ∈ translatedCompletionWords C v d ∧
      word ∈ enlargedProjectedCandidateBlock C exponent w ∧
      w ∈ T ∧
      w ≠ v ∧
      w ≠ s := by
  obtain ⟨word,w,hvBlock,hwBlock,hnotV,hnotS,
      hwT,hwNeV,hwNeS⟩ := hwit
  obtain ⟨d,hdActive,hdc,hdWord⟩ :=
    wholeCube_extra_word_has_other_translated_coordinate
      C exponent hvLoss hwhole hvBlock hnotV hnotS
  exact ⟨word,w,d,hdActive,hdc,hdWord,
    hwBlock,hwT,hwNeV,hwNeS⟩

/-- In the second-layer case, the new translated coordinate is one of exactly
two active coordinates other than the whole-cube owner coordinate. -/
theorem secondLayer_wholeCubeThirdSource_has_two_choice_coordinate
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hn3 : 3 ≤ n)
    {T : Finset V}
    {s v : V} {c : Fin n}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2)
    (hc : c ∈ retainedActive C v)
    (hwhole : WholeCubeQTPair C s v c)
    (hwit : WholeCubeThirdSourceWitness C exponent T s v) :
    ∃ word : Fin n → Bool,
    ∃ w : V,
    ∃ d : Fin n,
      d ∈ (retainedActive C v).erase c ∧
      ((retainedActive C v).erase c).card = 2 ∧
      word ∈ translatedCompletionWords C v d ∧
      word ∈ enlargedProjectedCandidateBlock C exponent w ∧
      w ∈ T ∧
      w ≠ v ∧
      w ≠ s := by
  obtain ⟨word,w,d,hdActive,hdc,hdWord,
      hwBlock,hwT,hwNeV,hwNeS⟩ :=
    wholeCubeThirdSourceWitness_has_other_translated_coordinate
      C exponent hvLoss hwhole hwit
  have hcard :
      (retainedActive C v).card = 3 :=
    secondLayer_projectedLoss_retainedActive_card_eq_three
      C exponent hn3 hvLoss hvSecond
  have herase :
      ((retainedActive C v).erase c).card = 2 := by
    rw [Finset.card_erase_of_mem hc,hcard]
  exact ⟨word,w,d,
    Finset.mem_erase.mpr ⟨hdc,hdActive⟩,
    herase,hdWord,hwBlock,hwT,hwNeV,hwNeS⟩

#print axioms wholeCube_extra_word_has_other_translated_coordinate
#print axioms wholeCubeThirdSourceWitness_has_other_translated_coordinate
#print axioms secondLayer_wholeCubeThirdSource_has_two_choice_coordinate

end OrderedEdgeColoring
end JSP000404Research
