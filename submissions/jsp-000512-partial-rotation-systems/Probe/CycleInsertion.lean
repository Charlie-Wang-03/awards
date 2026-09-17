import Probe.SwapCycles
import Mathlib.GroupTheory.Perm.Option

namespace JSP512Probe.CycleSurgery
variable {α : Type*} [DecidableEq α] [Finite α]

/-- Insert a fresh element immediately after `a` in its cyclic order. -/
def insertAfter (σ : Equiv.Perm α) (a : α) : Equiv.Perm (Option α) :=
  Equiv.swap none (some (σ a)) * σ.optionCongr

omit [Finite α] in
@[simp] theorem insertAfter_new (σ : Equiv.Perm α) (a : α) :
    insertAfter σ a none = some (σ a) := by
  simp [insertAfter, Equiv.Perm.mul_apply]

omit [Finite α] in
@[simp] theorem insertAfter_anchor (σ : Equiv.Perm α) (a : α) :
    insertAfter σ a (some a) = none := by
  simp [insertAfter, Equiv.Perm.mul_apply]

omit [Finite α] in
/-- Deleting the new element exactly recovers the lifted original permutation. -/
theorem erase_insertAfter (σ : Equiv.Perm α) (a : α) :
    eraseAt (insertAfter σ a) none = σ.optionCongr := by
  rw [eraseAt, insertAfter_new]
  unfold insertAfter
  rw [← mul_assoc, Equiv.swap_mul_self, one_mul]

omit [DecidableEq α] in
theorem lifted_sameCycle (σ : Equiv.Perm α) (x y : α) :
    Equiv.Perm.SameCycle σ.optionCongr (some x) (some y) ↔ σ.SameCycle x y := by
  exact sameCycle_embedding σ σ.optionCongr some (Option.some_injective α) (fun _ => rfl) x y

/-- Inserting a dart does not change the orbit relation of existing darts. -/
theorem insertAfter_sameCycle (σ : Equiv.Perm α) (a x y : α) :
    (insertAfter σ a).SameCycle (some x) (some y) ↔ σ.SameCycle x y := by
  rw [← eraseAt_sameCycle_iff (insertAfter σ a) none (some x) (some y)
    (Option.some_ne_none x) (Option.some_ne_none y), erase_insertAfter, lifted_sameCycle]

/-- The inserted element belongs precisely to the anchor's original orbit. -/
theorem insertAfter_new_cycle (σ : Equiv.Perm α) (a y : α) :
    (insertAfter σ a).SameCycle none (some y) ↔ σ.SameCycle a y := by
  rw [← insertAfter_anchor σ a, Equiv.Perm.sameCycle_apply_left, insertAfter_sameCycle]

omit [DecidableEq α] in
theorem option_orbit_count (σ : Equiv.Perm α) :
    Nat.card (Quotient (Equiv.Perm.SameCycle.setoid σ.optionCongr)) =
      Nat.card (Quotient (Equiv.Perm.SameCycle.setoid σ)) + 1 := by
  apply quotient_card_remove_class _ _ none some
  · exact lifted_sameCycle σ
  · intro y
    have hf : σ.optionCongr none = none := rfl
    constructor
    · rintro ⟨x, rfl⟩ h
      exact Option.some_ne_none x (h.eq_of_left hf).symm
    · intro h
      cases y with
      | none => exact False.elim (h Equiv.Perm.SameCycle.rfl)
      | some y => exact ⟨y, rfl⟩

theorem insertAfter_orbit_count (σ : Equiv.Perm α) (a : α) :
    Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (insertAfter σ a))) =
      Nat.card (Quotient (Equiv.Perm.SameCycle.setoid σ)) := by
  have hn : ¬Equiv.Perm.SameCycle σ.optionCongr none (some (σ a)) := by
    intro h
    exact Option.some_ne_none (σ a) (h.eq_of_left (show σ.optionCongr none = none from rfl)).symm
  have hm := swap_cycle_count σ.optionCongr none (some (σ a)) hn
  have ho := option_orbit_count σ
  unfold insertAfter
  omega

/-- Give the new element the source label of its anchor. -/
def insertedLabel {β : Type*} (label : α → β) (a : α) : Option α → β :=
  fun x => x.elim (label a) label

/-- One cyclic orbit per source label is preserved by inserting at that source. -/
theorem insertAfter_fiber_cycles {β : Type*} (σ : Equiv.Perm α) (label : α → β)
    (hl : ∀ x y, σ.SameCycle x y ↔ label x = label y) (a : α) (x y : Option α) :
    (insertAfter σ a).SameCycle x y ↔ insertedLabel label a x = insertedLabel label a y := by
  cases x with
  | none =>
    cases y with
    | none => simp [insertedLabel, Equiv.Perm.SameCycle.rfl]
    | some y => exact (insertAfter_new_cycle σ a y).trans (hl a y)
  | some x =>
    cases y with
    | none =>
      rw [Equiv.Perm.sameCycle_comm, insertAfter_new_cycle, hl]
      exact eq_comm
    | some y => exact (insertAfter_sameCycle σ a x y).trans (hl x y)

theorem insertAfter_preserves_label {β : Type*} (σ : Equiv.Perm α) (label : α → β)
    (hl : ∀ x y, σ.SameCycle x y ↔ label x = label y) (a : α) (x : Option α) :
    insertedLabel label a (insertAfter σ a x) = insertedLabel label a x :=
  (insertAfter_fiber_cycles σ label hl a _ _).mp Equiv.Perm.SameCycle.rfl.apply_left

omit [DecidableEq α] in
/-- Adding the first dart at a previously isolated source creates a new singleton
orbit, instead of inserting into an existing orbit. -/
theorem fresh_source_fiber_cycles {β : Type*} (σ : Equiv.Perm α) (label : α → β)
    (hl : ∀ x y, σ.SameCycle x y ↔ label x = label y)
    (fresh : β) (hn : ∀ x, label x ≠ fresh) (x y : Option α) :
    Equiv.Perm.SameCycle σ.optionCongr x y ↔
      x.elim fresh label = y.elim fresh label := by
  cases x with
  | none =>
    cases y with
    | none => simp [Equiv.Perm.SameCycle.rfl]
    | some y =>
      constructor
      · intro h
        exact False.elim (Option.some_ne_none y (h.eq_of_left rfl).symm)
      · intro h
        exact False.elim (hn y h.symm)
  | some x =>
    cases y with
    | none =>
      constructor
      · intro h
        exact False.elim (Option.some_ne_none x (h.eq_of_right rfl))
      · intro h
        exact False.elim (hn x h)
    | some y => exact (lifted_sameCycle σ x y).trans (hl x y)

end JSP512Probe.CycleSurgery
