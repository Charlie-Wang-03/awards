import JSP000404Research.ResidualBitMerge
import Mathlib.Tactic

/-!
# Unseparated residual edges are vertical pairs

For an OrderedEdgeColoring with n+1 colours, the full canonical Boolean code

  v |-> (bit C v c)_c

is injective: the colour of the edge joining two distinct vertices separates
their bits.

If two vertices agree on all retained n bits, their only remaining possible
difference is the residual bit.  Hence every retained-code fibre has size at
most two.

Consequently residual edges which are not separated by any retained bit form
a matching: a vertex cannot have two distinct such neighbours.

This turns the hard part of residual-colour elimination from an arbitrary
graph into a family of disjoint vertical pairs in the Boolean cube.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- The final old colour, viewed as a Fin (n+1) coordinate. -/
def residualCoord (n : ℕ) : Fin (n + 1) :=
  ⟨n, Nat.lt_succ_self n⟩

/-- Full canonical old-colour code. -/
noncomputable def fullBitCode
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    V → (Fin (n + 1) → Bool) :=
  fun v c => bit C v c

/-- The full canonical bit code is injective. -/
theorem fullBitCode_injective
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Function.Injective (fullBitCode C) := by
  intro u v huvbits
  by_contra huv
  obtain ⟨c, _hcu, _hcv, hbit⟩ := separates C u v huv
  have heq : bit C u c = bit C v c := by
    exact congrFun huvbits c
  exact hbit heq

/-- Agreement on all retained bits plus agreement on the residual bit forces
the vertices to be equal. -/
theorem eq_of_retainedBits_eq_of_residualBit_eq
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hret : ∀ c : Fin n, retainedBit C u c = retainedBit C v c)
    (hres :
      bit C u (residualCoord n) =
        bit C v (residualCoord n)) :
    u = v := by
  apply fullBitCode_injective C
  funext c
  by_cases hc : c.val < n
  · let d : Fin n := ⟨c.val, hc⟩
    have hcast : d.castSucc = c := by
      apply Fin.ext
      rfl
    have hd := hret d
    simpa [retainedBit, hcast] using hd
  · have hcval : c.val = n := by
      have hlt := c.isLt
      omega
    have hcoord : c = residualCoord n := by
      apply Fin.ext
      simpa [residualCoord] using hcval
    simpa [hcoord] using hres

/-- In a fixed retained-code fibre, two vertices distinct from the same base
vertex must coincide: Bool has only one value opposite to the base residual
bit. -/
theorem retainedFiber_other_unique
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V}
    (huv : u ≠ v) (huw : u ≠ w)
    (huvRet : ∀ c : Fin n, retainedBit C u c = retainedBit C v c)
    (huwRet : ∀ c : Fin n, retainedBit C u c = retainedBit C w c) :
    v = w := by
  apply eq_of_retainedBits_eq_of_residualBit_eq C
  · intro c
    exact (huvRet c).symm.trans (huwRet c)
  · have huvRes :
        bit C u (residualCoord n) ≠ bit C v (residualCoord n) := by
      intro heq
      exact huv (eq_of_retainedBits_eq_of_residualBit_eq C huvRet heq)
    have huwRes :
        bit C u (residualCoord n) ≠ bit C w (residualCoord n) := by
      intro heq
      exact huw (eq_of_retainedBits_eq_of_residualBit_eq C huwRet heq)
    cases hu : bit C u (residualCoord n) <;>
      cases hv : bit C v (residualCoord n) <;>
      cases hw : bit C w (residualCoord n) <;>
      simp_all

/-- A hard residual edge: residual and not already separated by any retained
bit. -/
def HardResidual
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) (u v : V) : Prop :=
  IsResidual C u v ∧ ¬ RetainedSeparated C u v

/-- Hard residual neighbours of a fixed vertex are unique. -/
theorem hardResidual_neighbour_unique
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V}
    (huv : u ≠ v) (huw : u ≠ w)
    (huvHard : HardResidual C u v)
    (huwHard : HardResidual C u w) :
    v = w := by
  have huvRet :
      ∀ c : Fin n, retainedBit C u c = retainedBit C v c :=
    (not_retainedSeparated_iff C u v).1 huvHard.2
  have huwRet :
      ∀ c : Fin n, retainedBit C u c = retainedBit C w c :=
    (not_retainedSeparated_iff C u w).1 huwHard.2
  exact retainedFiber_other_unique C huv huw huvRet huwRet

/-- Symmetric code-theoretic matching formulation, independent of edge
orientation: among vertices sharing a retained code, there are at most two. -/
theorem three_same_retained_codes_force_collision
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V}
    (huvRet : ∀ c : Fin n, retainedBit C u c = retainedBit C v c)
    (huwRet : ∀ c : Fin n, retainedBit C u c = retainedBit C w c) :
    u = v ∨ u = w ∨ v = w := by
  by_cases huv : u = v
  · exact Or.inl huv
  · by_cases huw : u = w
    · exact Or.inr (Or.inl huw)
    · exact Or.inr (Or.inr
        (retainedFiber_other_unique C huv huw huvRet huwRet))

#print axioms fullBitCode_injective
#print axioms eq_of_retainedBits_eq_of_residualBit_eq
#print axioms retainedFiber_other_unique
#print axioms hardResidual_neighbour_unique
#print axioms three_same_retained_codes_force_collision

end OrderedEdgeColoring
end JSP000404Research
