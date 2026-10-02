import JSP000404Research.ResidualWholeCubeCoordinateUniqueness
import JSP000404Research.ResidualLossAllActiveSlices
import Mathlib.Tactic

/-!
# Distinctness of whole-cube partners

An active translated slice T_c(v) is disjoint from the base cube Q_v, so it
cannot equal Q_v.  Hence a WholeCubeQTPair (s,v,c) with c active at v has
s != v.

Moreover, for a fixed translated endpoint v, partners attached through two
different active owner coordinates must be different; otherwise coordinate
uniqueness for the same ordered pair would force the coordinates equal.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem wholeCubeQTPair_ne_of_active
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s v : V} {c : Fin n}
    (hcV : c ∈ retainedActive C v)
    (hwhole : WholeCubeQTPair C s v c) :
    s ≠ v := by
  intro hsv
  subst s
  rcases hwhole with ⟨_hactive,hEq⟩
  have hdisj :=
    translatedCompletionWords_disjoint_original_of_active C hcV
  have hnonempty :
      (retainedCompletionWords C v).Nonempty := by
    rw [retainedCompletionWords_nonempty_iff]
  obtain ⟨word,hword⟩ := hnonempty
  have hT :
      word ∈ translatedCompletionWords C v c := by
    rw [hEq]
    exact hword
  exact Finset.disjoint_left.mp hdisj hT hword

theorem wholeCubeQTPair_partners_ne_of_coordinates_ne
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v s₁ s₂ : V} {c₁ c₂ : Fin n}
    (hc1V : c₁ ∈ retainedActive C v)
    (hc2V : c₂ ∈ retainedActive C v)
    (hc12 : c₁ ≠ c₂)
    (h₁ : WholeCubeQTPair C s₁ v c₁)
    (h₂ : WholeCubeQTPair C s₂ v c₂) :
    s₁ ≠ s₂ := by
  intro hEq
  subst s₂
  have hcEq :=
    wholeCubeQTPair_coordinate_unique
      C hc1V hc2V h₁ h₂
  exact hc12 hcEq

#print axioms wholeCubeQTPair_ne_of_active
#print axioms wholeCubeQTPair_partners_ne_of_coordinates_ne

end OrderedEdgeColoring
end JSP000404Research
