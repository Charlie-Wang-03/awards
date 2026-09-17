import Probe.CycleSurgery

namespace JSP512Probe.CycleSurgery
variable {α β : Type*} (label : α → β) (σ : β → Equiv.Perm α)
  (hs : ∀ b x, label (σ b x) = label x)

/-- Combine permutations fiberwise when each preserves the common labeling. -/
def fiberPermutation : Equiv.Perm α where
  toFun x := σ (label x) x
  invFun x := (σ (label x)).symm x
  left_inv x := by
    change (σ (label (σ (label x) x))).symm (σ (label x) x) = x
    rw [hs, Equiv.symm_apply_apply]
  right_inv x := by
    have hi : label ((σ (label x)).symm x) = label x := by
      have h := hs (label x) ((σ (label x)).symm x)
      simpa only [Equiv.apply_symm_apply] using h.symm
    change σ (label ((σ (label x)).symm x)) ((σ (label x)).symm x) = x
    rw [hi, Equiv.apply_symm_apply]

theorem fiberPermutation_label (x : α) :
    label (fiberPermutation label σ hs x) = label x := hs _ _

include hs in
theorem fiber_pow_label (b : β) (x : α) (n : ℕ) :
    label ((σ b ^ n) x) = label x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, hs, ih]

theorem fiberPermutation_pow (x : α) (n : ℕ) :
    ((fiberPermutation label σ hs) ^ n) x = (σ (label x) ^ n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih]
    change σ (label ((σ (label x) ^ n) x)) ((σ (label x) ^ n) x) = _
    rw [fiber_pow_label label σ hs]

variable [Finite α]

theorem fiberPermutation_cycles (x y : α) :
    (fiberPermutation label σ hs).SameCycle x y ↔ (σ (label x)).SameCycle x y := by
  constructor
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    rw [fiberPermutation_pow] at hn
    exact ⟨(n : ℤ),by simpa using hn⟩
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    have hp : ((fiberPermutation label σ hs) ^ n) x = y := by
      rw [fiberPermutation_pow, hn]
    exact ⟨(n : ℤ),by simpa using hp⟩

end JSP512Probe.CycleSurgery
