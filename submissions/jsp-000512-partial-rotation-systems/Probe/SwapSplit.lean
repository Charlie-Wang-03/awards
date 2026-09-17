import Probe.SwapCycles

namespace JSP512Probe.CycleSurgery
variable {α : Type*} [DecidableEq α] [Finite α]

/-- Swapping two distinct targets on one cycle separates the marked points. -/
theorem swap_splits (σ : Equiv.Perm α) (a b : α) (hne : a ≠ b)
    (hab : σ.SameCycle a b) : ¬(Equiv.swap a b * σ).SameCycle a b := by
  classical
  have hex := hab.exists_nat_pow_eq
  let n := Nat.find hex
  have hn : (σ ^ n) a = b := Nat.find_spec hex
  have hmin : ∀ k < n, (σ ^ k) a ≠ b := by
    intro k hk
    exact Nat.find_min hex hk
  have hnpos : 0 < n := by
    by_contra h
    have hz : n = 0 := by omega
    simp only [hz, pow_zero, Equiv.Perm.one_apply] at hn
    exact hne hn
  have hreturn : ∀ k, 0 < k → k < n → (σ ^ k) a ≠ a := by
    intro k hk hkn he
    have hh : (σ ^ (n-k)) a = b := by
      calc
        (σ ^ (n-k)) a = (σ ^ (n-k)) ((σ ^ k) a) := congrArg _ he.symm
        _ = (σ ^ ((n-k)+k)) a := by rw [pow_add, Equiv.Perm.mul_apply]
        _ = b := by rw [Nat.sub_add_cancel (Nat.le_of_lt hkn), hn]
    exact hmin (n-k) (by omega) hh
  let S : α → Prop := fun x => ∃ i < n, (σ ^ i) a = x
  have hSa : S a := ⟨0, hnpos, rfl⟩
  have hSb : ¬S b := by
    rintro ⟨i, hi, he⟩
    exact hmin i hi he
  let τ := Equiv.swap a b * σ
  have hstep : ∀ x, S x → S (τ x) := by
    rintro x ⟨i, hi, rfl⟩
    have he : σ ((σ ^ i) a) = (σ ^ (i+1)) a := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    change S (Equiv.swap a b (σ ((σ ^ i) a)))
    rw [he]
    by_cases hit : i+1 = n
    · rw [hit, hn, Equiv.swap_apply_right]
      exact hSa
    · have hlt : i+1 < n := by omega
      rw [Equiv.swap_apply_of_ne_of_ne (hreturn (i+1) (by omega) hlt) (hmin _ hlt)]
      exact ⟨i+1, hlt, rfl⟩
  intro h
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  have hp : ∀ k : ℕ, S ((τ ^ k) a) := by
    intro k
    induction k with
    | zero => exact hSa
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact hstep _ ih
  exact hSb (hk ▸ hp k)

/-- The inverse of a merge is a split, hence the exact increment is one. -/
theorem swap_split_count (σ : Equiv.Perm α) (a b : α) (hne : a ≠ b)
    (hab : σ.SameCycle a b) :
    Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (Equiv.swap a b * σ))) =
      Nat.card (Quotient (Equiv.Perm.SameCycle.setoid σ)) + 1 := by
  have h := swap_cycle_count (Equiv.swap a b * σ) a b (swap_splits σ a b hne hab)
  simpa only [← mul_assoc, Equiv.swap_mul_self, one_mul] using h

end JSP512Probe.CycleSurgery
