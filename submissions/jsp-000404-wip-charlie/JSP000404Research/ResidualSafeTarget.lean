import JSP000404Research.ResidualRecolor
import Mathlib.Tactic

/-!
# Residual edges reduce to independent local target choices

Let `C` be an admissible ordered-edge colouring with `k+1` colours and
regard the final colour as residual.

Two consecutive increasing edges can never both be residual: both would have
old colour value exactly `k`, contradicting the no-monochromatic-two-path
axiom of `C`. Consequently, at every vertex residual incidence is one-sided:
there cannot simultaneously be an incoming residual edge and an outgoing
residual edge.

This removes the apparent global interaction between residual edges. To build
a safe recolouring it is enough to choose, independently for each residual
edge `u<v`, a target colour which avoids

* retained incoming colours at `u`, and
* retained outgoing colours at `v`.

No compatibility condition between two residual targets is needed, because
two residual edges never form an increasing two-path.

The remaining JSP-000404 geometry is therefore reduced to proving local
non-emptiness / active-colour budget statements for these target lists.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- An old edge has the unique residual colour of a `k+1` colouring. -/
def IsResidual
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1)) (u v : V) : Prop :=
  ¬ (C.color u v).val < k

/-- A non-retained colour in `Fin (k+1)` must have value exactly `k`. -/
theorem residual_val_eq
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1))
    {u v : V} (hres : IsResidual C u v) :
    (C.color u v).val = k := by
  unfold IsResidual at hres
  have hlt := (C.color u v).isLt
  omega

/-- Two consecutive increasing edges cannot both be residual. -/
theorem no_two_residual_on_path
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1))
    {a v w : V} (hav : a < v) (hvw : v < w)
    (havRes : IsResidual C a v)
    (hvwRes : IsResidual C v w) :
    False := by
  apply C.noMonoTwoPath hav hvw
  apply Fin.ext
  rw [residual_val_eq C havRes, residual_val_eq C hvwRes]

/-- Residual incidence at a vertex is one-sided: either there is no incoming
residual edge or there is no outgoing residual edge. -/
theorem residual_incidence_one_sided
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1)) (v : V) :
    (¬ ∃ a, a < v ∧ IsResidual C a v) ∨
      (¬ ∃ w, v < w ∧ IsResidual C v w) := by
  by_cases hin : ∃ a, a < v ∧ IsResidual C a v
  · right
    rintro ⟨w, hvw, hwRes⟩
    obtain ⟨a, hav, haRes⟩ := hin
    exact no_two_residual_on_path C hav hvw haRes hwRes
  · exact Or.inl hin

/-- Local compatibility condition for independently recolouring a residual
edge `u<v`.

At its lower endpoint `u`, the target must avoid every retained incoming
colour. At its upper endpoint `v`, it must avoid every retained outgoing
colour. These are exactly the mixed retained/residual two-path conflicts. -/
def ResidualTargetCompatible
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1))
    (target : V → V → Fin k) : Prop :=
  ∀ {u v : V}, u < v → IsResidual C u v →
    (∀ {a : V} (hau : a < u)
        (haRet : (C.color a u).val < k),
      target u v ≠ retainedColor C a u haRet) ∧
    (∀ {w : V} (hvw : v < w)
        (hwRet : (C.color v w).val < k),
      target u v ≠ retainedColor C v w hwRet)

/-- Independent locally compatible target choices produce a valid residual
recolouring. No residual/residual compatibility hypothesis is required. -/
noncomputable def residualRecoloringOfCompatible
    {V : Type*} [LinearOrder V] {k : ℕ}
    {C : OrderedEdgeColoring V (k + 1)}
    (target : V → V → Fin k)
    (hcompat : ResidualTargetCompatible C target) :
    ResidualRecoloring C where
  target := target
  safe_touching_residual := by
    intro a v w hav hvw htouch
    rcases htouch with havRes | hvwRes
    · by_cases hvwRet : (C.color v w).val < k
      · simp only [recoloredColor, dif_neg havRes, dif_pos hvwRet]
        exact (hcompat hav havRes).2 hvw hvwRet
      · exact False.elim
          (no_two_residual_on_path C hav hvw havRes hvwRet)
    · by_cases havRet : (C.color a v).val < k
      · simp only [recoloredColor, dif_pos havRet, dif_neg hvwRes]
        exact ((hcompat hvw hvwRes).1 hav havRet).symm
      · exact False.elim
          (no_two_residual_on_path C hav hvw havRet hvwRes)

#print axioms residual_val_eq
#print axioms no_two_residual_on_path
#print axioms residual_incidence_one_sided
#print axioms residualRecoloringOfCompatible

end OrderedEdgeColoring
end JSP000404Research
