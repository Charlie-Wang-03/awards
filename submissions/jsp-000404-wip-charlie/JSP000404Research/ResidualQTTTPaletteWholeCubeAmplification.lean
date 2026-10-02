import JSP000404Research.ResidualSamePaletteCubeAmplification
import JSP000404Research.ResidualSecondLayerTripleCanonical
import Mathlib.Tactic

/-!
# Palette equality upgrades a Q/T/T/T translated owner to a whole-cube partner

In a saturated Q/T/T/T state the common word lies in Q_s and in the translated
slice T_c(v) of each translated owner v.

If such an owner v has the same retained-active palette as s, the one-word
intersection T_c(v) ∩ Q_s is enough to identify all fixed Boolean coordinates.
Hence T_c(v)=Q_s, i.e. (s,v,c) is a WholeCubeQTPair.

Thus, inside Q/T/T/T, repeated retained palettes and whole-cube Q/T partners
are interchangeable notions once the owner coordinate is known active.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem QTT_palette_eq_upgrades_to_wholeCube
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s v : V}
    {word : Fin n → Bool}
    {c : Fin n}
    (hactiveEq :
      retainedActive C v = retainedActive C s)
    (hcV : c ∈ retainedActive C v)
    (hsQ : word ∈ retainedCompletionWords C s)
    (hvT : word ∈ translatedCompletionWords C v c) :
    WholeCubeQTPair C s v c := by
  apply wholeCubeQTPair_of_same_palette_translated_intersection
    C hactiveEq hcV
  exact ⟨word,Finset.mem_inter.mpr ⟨hvT,hsQ⟩⟩

theorem QTTT_palette_equal_owners_are_wholeCube_partners
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s x y z : V}
    {word : Fin n → Bool}
    {cx cy cz : Fin n}
    (hcx : cx ∈ retainedActive C x)
    (hcy : cy ∈ retainedActive C y)
    (hcz : cz ∈ retainedActive C z)
    (hsQ : word ∈ retainedCompletionWords C s)
    (hxT : word ∈ translatedCompletionWords C x cx)
    (hyT : word ∈ translatedCompletionWords C y cy)
    (hzT : word ∈ translatedCompletionWords C z cz) :
    (
      retainedActive C x = retainedActive C s →
        WholeCubeQTPair C s x cx
    )
    ∧
    (
      retainedActive C y = retainedActive C s →
        WholeCubeQTPair C s y cy
    )
    ∧
    (
      retainedActive C z = retainedActive C s →
        WholeCubeQTPair C s z cz
    ) := by
  exact ⟨
    fun hxEq =>
      QTT_palette_eq_upgrades_to_wholeCube
        C hxEq hcx hsQ hxT,
    fun hyEq =>
      QTT_palette_eq_upgrades_to_wholeCube
        C hyEq hcy hsQ hyT,
    fun hzEq =>
      QTT_palette_eq_upgrades_to_wholeCube
        C hzEq hcz hsQ hzT
  ⟩

#print axioms QTT_palette_eq_upgrades_to_wholeCube
#print axioms QTTT_palette_equal_owners_are_wholeCube_partners

end OrderedEdgeColoring
end JSP000404Research
