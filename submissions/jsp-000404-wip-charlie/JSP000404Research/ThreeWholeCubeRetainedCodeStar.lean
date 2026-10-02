import JSP000404Research.ResidualWholeCubeTQOrientation
import JSP000404Research.ResidualQTTWholeCubeEquality
import Mathlib.Tactic

/-!
# Retained-code star of three whole-cube partners

For a WholeCubeQTPair (s,v,c), the retained palettes agree and the retained
codes differ at exactly the owner coordinate c.

Consequently, if one second-layer source v has whole-cube partners s1,s2,s3
at three distinct active coordinates c1,c2,c3, their retained codes form the
Boolean star obtained from the code of v by the three single-coordinate flips.

This is the exact discrete input carried by the saturated four-vertex
whole-cube terminal.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem wholeCube_owner_retainedBit_flip
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s v : V} {c : Fin n}
    (hcV : c ∈ retainedActive C v)
    (hwhole : WholeCubeQTPair C s v c) :
    retainedBit C s c = !(retainedBit C v c) := by
  obtain ⟨hactive,hcube⟩ := hwhole
  have hnon :
      (retainedCompletionWords C s).Nonempty := by
    rw [retainedCompletionWords_nonempty_iff]
  obtain ⟨word,hsQ⟩ := hnon
  have hvT :
      word ∈ translatedCompletionWords C v c := by
    rw [hcube]
    exact hsQ
  have hcode :=
    QTT_equal_palette_oneBit_code
      C hactive hcV hsQ hvT
  cases hv : retainedBit C v c <;>
    cases hs : retainedBit C s c <;>
    simp_all

theorem wholeCube_retainedCode_single_flip
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s v : V} {c : Fin n}
    (hcV : c ∈ retainedActive C v)
    (hwhole : WholeCubeQTPair C s v c) :
    retainedActive C s = retainedActive C v ∧
    retainedBit C s c = !(retainedBit C v c) ∧
    ∀ d : Fin n,
      d ∈ retainedActive C v →
      d ≠ c →
      retainedBit C s d = retainedBit C v d := by
  obtain ⟨hactive,hcube⟩ := hwhole
  have hoff :
      ∀ d : Fin n,
        d ∈ retainedActive C v →
        d ≠ c →
        retainedBit C s d = retainedBit C v d := by
    intro d hd hdc
    exact wholeCube_off_owner_retainedBit_eq
      C ⟨hactive,hcube⟩ hd hdc
  exact ⟨hactive.symm,
    wholeCube_owner_retainedBit_flip C hcV ⟨hactive,hcube⟩,
    hoff⟩

theorem threeWholeCubePartners_retainedCode_star
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v s₁ s₂ s₃ : V}
    {c₁ c₂ c₃ : Fin n}
    (hc1V : c₁ ∈ retainedActive C v)
    (hc2V : c₂ ∈ retainedActive C v)
    (hc3V : c₃ ∈ retainedActive C v)
    (h₁ : WholeCubeQTPair C s₁ v c₁)
    (h₂ : WholeCubeQTPair C s₂ v c₂)
    (h₃ : WholeCubeQTPair C s₃ v c₃) :
    (
      retainedActive C s₁ = retainedActive C v ∧
      retainedBit C s₁ c₁ = !(retainedBit C v c₁) ∧
      ∀ d : Fin n,
        d ∈ retainedActive C v →
        d ≠ c₁ →
        retainedBit C s₁ d = retainedBit C v d
    )
    ∧
    (
      retainedActive C s₂ = retainedActive C v ∧
      retainedBit C s₂ c₂ = !(retainedBit C v c₂) ∧
      ∀ d : Fin n,
        d ∈ retainedActive C v →
        d ≠ c₂ →
        retainedBit C s₂ d = retainedBit C v d
    )
    ∧
    (
      retainedActive C s₃ = retainedActive C v ∧
      retainedBit C s₃ c₃ = !(retainedBit C v c₃) ∧
      ∀ d : Fin n,
        d ∈ retainedActive C v →
        d ≠ c₃ →
        retainedBit C s₃ d = retainedBit C v d
    ) := by
  exact ⟨
    wholeCube_retainedCode_single_flip C hc1V h₁,
    wholeCube_retainedCode_single_flip C hc2V h₂,
    wholeCube_retainedCode_single_flip C hc3V h₃
  ⟩

#print axioms wholeCube_owner_retainedBit_flip
#print axioms wholeCube_retainedCode_single_flip
#print axioms threeWholeCubePartners_retainedCode_star

end OrderedEdgeColoring
end JSP000404Research
