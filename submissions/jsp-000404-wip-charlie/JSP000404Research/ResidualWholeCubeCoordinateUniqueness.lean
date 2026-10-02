import JSP000404Research.ResidualQTTTWholeCubeCoreSplit
import JSP000404Research.ResidualLossAllActiveSlices
import Mathlib.Tactic

/-!
# Whole-cube Q/T owner coordinate is unique for a fixed ordered pair

For a fixed pair (s,v), two distinct active translated coordinates at v have
pairwise-disjoint translated completion slices.  A WholeCubeQTPair identifies
one such slice with the nonempty completion cube Q_s.  Therefore the same
ordered pair cannot be whole-cube at two distinct active coordinates.

This removes immediate coordinate ping-pong in the lossless whole-cube
rematching recursion.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem wholeCubeQTPair_coordinate_unique
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s v : V} {c d : Fin n}
    (hcV : c ∈ retainedActive C v)
    (hdV : d ∈ retainedActive C v)
    (hc : WholeCubeQTPair C s v c)
    (hd : WholeCubeQTPair C s v d) :
    c = d := by
  by_contra hcd
  have hdisj :=
    translatedCompletionWords_disjoint_same_owner_distinct_active
      C hcV hcd
  rcases hc with ⟨_hcActive,hcEq⟩
  rcases hd with ⟨_hdActive,hdEq⟩
  have hnonempty :
      (retainedCompletionWords C s).Nonempty := by
    rw [retainedCompletionWords_nonempty_iff]
  obtain ⟨word,hword⟩ := hnonempty
  have hcWord :
      word ∈ translatedCompletionWords C v c := by
    rw [hcEq]
    exact hword
  have hdWord :
      word ∈ translatedCompletionWords C v d := by
    rw [hdEq]
    exact hword
  exact Finset.disjoint_left.mp hdisj hcWord hdWord

theorem wholeCubeQTPair_coordinate_unique_symm
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s v : V} {c d : Fin n}
    (hcS : c ∈ retainedActive C s)
    (hdS : d ∈ retainedActive C s)
    (hc : WholeCubeQTPair C s v c)
    (hd : WholeCubeQTPair C s v d) :
    c = d := by
  have hc' :
      WholeCubeQTPair C v s c :=
    wholeCubeQTPair_symm_of_active C
      (by
        rcases hc with ⟨hactive,_⟩
        rw [hactive]
        exact hcS)
      hc
  have hd' :
      WholeCubeQTPair C v s d :=
    wholeCubeQTPair_symm_of_active C
      (by
        rcases hd with ⟨hactive,_⟩
        rw [hactive]
        exact hdS)
      hd
  exact wholeCubeQTPair_coordinate_unique
    C hcS hdS hc' hd'

#print axioms wholeCubeQTPair_coordinate_unique
#print axioms wholeCubeQTPair_coordinate_unique_symm

end OrderedEdgeColoring
end JSP000404Research
