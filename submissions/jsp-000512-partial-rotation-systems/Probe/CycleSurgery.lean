import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Logic.Equiv.Basic

namespace JSP512Probe.CycleSurgery
variable {α : Type*} [DecidableEq α]

/-- Bypass `a` in its cycle and leave it as a fixed point. -/
def eraseAt (σ : Equiv.Perm α) (a : α) : Equiv.Perm α :=
  Equiv.swap a (σ a) * σ

@[simp] theorem eraseAt_self (σ : Equiv.Perm α) (a : α) : eraseAt σ a a = a := by
  simp [eraseAt, Equiv.Perm.mul_apply]

theorem eraseAt_apply (σ : Equiv.Perm α) (a x : α) (hx : x ≠ a) :
    eraseAt σ a x = if σ x = a then σ a else σ x := by
  by_cases h : σ x = a
  · simp [eraseAt, Equiv.Perm.mul_apply, h]
  · have h' : σ x ≠ σ a := fun hh => hx (σ.injective hh)
    simp [eraseAt, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h h', h]

theorem eraseAt_ne (σ : Equiv.Perm α) (a x : α) :
    eraseAt σ a x ≠ a ↔ x ≠ a := by
  have h := (eraseAt σ a).injective.ne_iff (x := x) (y := a)
  simpa only [eraseAt_self] using h

/-- Permutation of the remaining elements, including the singleton-cycle case. -/
def delete (σ : Equiv.Perm α) (a : α) : Equiv.Perm {x : α // x ≠ a} :=
  (eraseAt σ a).subtypeEquiv (fun x => (eraseAt_ne σ a x).symm)

variable [Finite α]

omit [DecidableEq α] in
/-- Single-step checks suffice for inclusion of finite permutation orbits. -/
theorem sameCycle_of_steps (σ τ : Equiv.Perm α)
    (h : ∀ x, σ.SameCycle x (τ x)) {x y : α} (hxy : τ.SameCycle x y) :
    σ.SameCycle x y := by
  obtain ⟨n, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => exact Equiv.Perm.SameCycle.rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ih.trans (h _)

/-- Bypassing an element does not merge distinct cycles. -/
theorem eraseAt_sameCycle_imp (σ : Equiv.Perm α) (a x y : α)
    (h : (eraseAt σ a).SameCycle x y) : σ.SameCycle x y := by
  apply sameCycle_of_steps σ (eraseAt σ a) _ h
  intro z
  by_cases hz : z = a
  · subst z
    rw [eraseAt_self]
  · rw [eraseAt_apply σ a z hz]
    split_ifs with hza
    · have h₁ : σ.SameCycle z a := by
        rw [← hza]
        exact Equiv.Perm.SameCycle.rfl.apply_right
      exact h₁.apply_right
    · exact Equiv.Perm.SameCycle.rfl.apply_right

/-- Bypassing an element preserves the cycles among remaining elements. -/
theorem eraseAt_sameCycle_iff (σ : Equiv.Perm α) (a x y : α)
    (hx : x ≠ a) (hy : y ≠ a) :
    (eraseAt σ a).SameCycle x y ↔ σ.SameCycle x y := by
  constructor
  · exact eraseAt_sameCycle_imp σ a x y
  · intro hxy
    by_cases ha : σ a = a
    · have he : eraseAt σ a = σ := by
        ext z
        simp [eraseAt, ha, Equiv.Perm.mul_apply]
      rw [he]
      exact hxy
    let p : α → α := fun z => if z = a then σ a else z
    have step : ∀ z, (eraseAt σ a).SameCycle (p z) (p (σ z)) := by
      intro z
      by_cases hz : z = a
      · subst z
        simp only [p, ite_eq_left rfl, ite_eq_right ha]
        exact Equiv.Perm.SameCycle.rfl
      · have heq : eraseAt σ a z = p (σ z) := eraseAt_apply σ a z hz
        change (eraseAt σ a).SameCycle (p z) (p (σ z))
        rw [show p z = z by simp [p, hz], ← heq]
        exact Equiv.Perm.SameCycle.rfl.apply_right
    obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
    have walk : ∀ n : ℕ, (eraseAt σ a).SameCycle (p x) (p ((σ ^ n) x)) := by
      intro n
      induction n with
      | zero => exact Equiv.Perm.SameCycle.rfl
      | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact ih.trans (step _)
    have hh := walk n
    rw [hn] at hh
    simpa [p, hx, hy] using hh

omit [Finite α] in
theorem delete_pow_val (σ : Equiv.Perm α) (a : α)
    (x : {x : α // x ≠ a}) (n : ℕ) :
    (((delete σ a) ^ n) x).val = ((eraseAt σ a) ^ n) x.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', Equiv.Perm.mul_apply]
    change eraseAt σ a ((((delete σ a) ^ n) x).val) = _
    rw [ih]

/-- Deletion on the smaller type preserves exactly the old orbit relation. -/
theorem delete_sameCycle_iff (σ : Equiv.Perm α) (a : α)
    (x y : {x : α // x ≠ a}) :
    (delete σ a).SameCycle x y ↔ σ.SameCycle x.val y.val := by
  rw [← eraseAt_sameCycle_iff σ a x.val y.val x.property y.property]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    have hv := congrArg Subtype.val hn
    rw [delete_pow_val] at hv
    exact ⟨(n : ℤ), by simpa using hv⟩
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    have hs : ((delete σ a) ^ n) x = y := by
      apply Subtype.ext
      rw [delete_pow_val, hn]
    exact ⟨(n : ℤ), by simpa using hs⟩

/-- A rotation with one orbit per vertex retains that property after deletion.
The label may be the source vertex of a dart; no planar hypothesis is needed. -/
theorem delete_fiber_cycles {β : Type*} (σ : Equiv.Perm α) (label : α → β)
    (h : ∀ x y, σ.SameCycle x y ↔ label x = label y) (a : α)
    (x y : {x : α // x ≠ a}) :
    (delete σ a).SameCycle x y ↔ label x.val = label y.val := by
  rw [delete_sameCycle_iff, h]

end JSP512Probe.CycleSurgery
