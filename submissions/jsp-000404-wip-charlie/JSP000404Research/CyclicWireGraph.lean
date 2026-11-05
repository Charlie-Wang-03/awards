import JSP000404Research.CyclicWireLocalGaps

/-!
# The consecutive-event quiver of finite wires

Every wire contains its consecutive arrows and one closing arrow. This module constructs
the quiver, proves its strong connectivity from shared events, and combines integer retiming
with the cyclic local gap bound. The simple-cycle winding hypothesis stays explicit until
the ordered projection-network construction is complete.
-/

namespace JSP000404Research
namespace WireGraph

open Quiver

universe u v

variable {V : Type u} {E : Type v} {m : ℕ}

/-- Distinguish event types carrying different wire quivers on the same underlying set. -/
def Event (_wire : V → Fin (m + 1) → E) := E

/-- Arrows along consecutive events and through the reflected closing seam. -/
inductive Arc (wire : V → Fin (m + 1) → E) : E → E → Type (max u v)
  | adjacent (v : V) (i : Fin m) : Arc wire (wire v i.castSucc) (wire v i.succ)
  | closing (v : V) : Arc wire (wire v (Fin.last m)) (wire v 0)

instance eventQuiver (wire : V → Fin (m + 1) → E) : Quiver (Event wire) where
  Hom a b := Arc wire a b

def winding (wire : V → Fin (m + 1) → E) :
    ∀ {a b : Event wire}, (a ⟶ b) → ℤ
  | _, _, .adjacent _ _ => 0
  | _, _, .closing _ => 1

def delay (wire : V → Fin (m + 1) → E) (sign : V → E → Bool) :
    ∀ {a b : Event wire}, (a ⟶ b) → ℤ
  | _, _, .adjacent v i => if sign v (wire v i.castSucc) = sign v (wire v i.succ) then 0 else 1
  | _, _, .closing v => if sign v (wire v (Fin.last m)) = sign v (wire v 0) then 1 else 0

theorem path_from_first (wire : V → Fin (m + 1) → E) (v : V) (j : Fin (m + 1)) :
    Nonempty (Quiver.Path (V := Event wire) (wire v 0) (wire v j)) := by
  induction j using Fin.induction with
  | zero => exact ⟨.nil⟩
  | succ j ih =>
    obtain ⟨p⟩ := ih
    exact ⟨p.cons (.adjacent v j)⟩

theorem path_to_last (wire : V → Fin (m + 1) → E) (v : V) (i : Fin (m + 1)) :
    Nonempty (Quiver.Path (V := Event wire) (wire v i) (wire v (Fin.last m))) := by
  induction i using Fin.reverseInduction with
  | last => exact ⟨.nil⟩
  | cast i ih =>
    obtain ⟨p⟩ := ih
    exact ⟨(Quiver.Hom.toPath (V := Event wire) (Arc.adjacent v i)).comp p⟩

theorem path_on_wire (wire : V → Fin (m + 1) → E) (v : V) (i j : Fin (m + 1)) :
    Nonempty (Quiver.Path (V := Event wire) (wire v i) (wire v j)) := by
  obtain ⟨first⟩ := path_to_last wire v i
  obtain ⟨last⟩ := path_from_first wire v j
  exact ⟨first.comp ((Quiver.Hom.toPath (V := Event wire) (Arc.closing v)).comp last)⟩

theorem strongly_connected (wire : V → Fin (m + 1) → E)
    (hcover : ∀ e : E, ∃ v i, wire v i = e)
    (hshared : ∀ v w, v ≠ w → ∃ i j, wire v i = wire w j)
    (a b : Event wire) : Nonempty (Quiver.Path (V := Event wire) a b) := by
  obtain ⟨v, i, rfl⟩ := hcover a
  obtain ⟨w, j, rfl⟩ := hcover b
  by_cases heq : v = w
  · subst w
    exact path_on_wire wire v i j
  · obtain ⟨k, l, hsame⟩ := hshared v w heq
    obtain ⟨first⟩ := path_on_wire wire v i k
    obtain ⟨last⟩ := path_on_wire wire w l j
    rw [← hsame] at last
    exact ⟨first.comp last⟩

/-- The complete combinatorial capacity implication for a consecutive-wire graph. -/
theorem card_le_two_pow_of_simple_cycle_winding
    [Fintype V] (period : ℕ) (hperiod : 0 < period)
    (wire : V → Fin (m + 1) → E) (sign : V → E → Bool) (original : E → ℝ)
    (hcover : ∀ e : E, ∃ v i, wire v i = e)
    (hpair : ∀ v w, v ≠ w → ∃ i j, wire v i = wire w j ∧
      sign v (wire v i) ≠ sign w (wire w j))
    (hadjacent : ∀ v (i : Fin m),
      (if sign v (wire v i.castSucc) = sign v (wire v i.succ) then (0 : ℝ) else 1) <
        original (wire v i.succ) - original (wire v i.castSucc))
    (hclosing : ∀ v,
      (if sign v (wire v (Fin.last m)) = sign v (wire v 0) then (1 : ℝ) else 0) <
        original (wire v 0) - original (wire v (Fin.last m)) + ((period : ℝ) + 1 / 2))
    (hcycles : ∀ (e : Event wire) (p : Quiver.Path (V := Event wire) e e),
      p.vertices.dropLast.Nodup → p.length ≠ 0 →
        CyclicGraph.pathWeight (winding wire) p = 1 ∨
        CyclicGraph.pathWeight (winding wire) p = 2) : Fintype.card V ≤ 2 ^ period := by
  classical
  cases isEmpty_or_nonempty V with
  | inl hempty => simp
  | inr hnonempty =>
    obtain ⟨v₀⟩ := hnonempty
    have hconnected := strongly_connected wire hcover (by
      intro v w hvw
      obtain ⟨i, j, heq, _⟩ := hpair v w hvw
      exact ⟨i, j, heq⟩)
    have hsource : ∀ {a b : Event wire} (e : a ⟶ b),
        (delay wire sign e : ℝ) < original b - original a +
          (winding wire e : ℝ) * ((period : ℝ) + 1 / 2) := by
      intro a b e
      cases e with
      | adjacent v i => simpa only [delay, winding, Int.cast_ite, Int.cast_zero, Int.cast_one,
          zero_mul, add_zero] using hadjacent v i
      | closing v => simpa only [delay, winding, Int.cast_ite, Int.cast_zero, Int.cast_one,
          one_mul] using hclosing v
    obtain ⟨time, htime⟩ := IntegralWire.exists_integer_retiming
      (delay wire sign) (winding wire) period original (wire v₀ 0) hconnected hsource hcycles
    apply IntegralWire.card_le_two_pow_of_cyclic_wire_schedules period hperiod time wire sign
    · intro v i
      simpa only [delay, winding, mul_zero, add_zero] using htime (Arc.adjacent v i)
    · intro v
      simpa only [delay, winding, mul_one] using htime (Arc.closing v)
    · exact hpair

#print axioms path_on_wire
#print axioms strongly_connected
#print axioms card_le_two_pow_of_simple_cycle_winding

end WireGraph
end JSP000404Research
