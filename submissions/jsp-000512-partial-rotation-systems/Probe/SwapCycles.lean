import Probe.OrbitCounting

namespace JSP512Probe.CycleSurgery
variable {α : Type*} [DecidableEq α] [Finite α]

/-- Swapping destinations in two distinct cycles joins the two marked elements. -/
theorem swap_joins (σ : Equiv.Perm α) (a b : α)
    (hab : ¬σ.SameCycle a b) : (Equiv.swap a b * σ).SameCycle a b := by
  let τ := Equiv.swap a b * σ
  by_contra h
  have hp : ∀ n : ℕ, σ.SameCycle a ((τ ^ n) a) := by
    intro n
    induction n with
    | zero => exact Equiv.Perm.SameCycle.rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      let z := (τ ^ n) a
      have hi : σ.SameCycle a (σ z) := ih.apply_right
      by_cases ha : σ z = a
      · have ht : τ z = b := by simp [τ, Equiv.Perm.mul_apply, ha]
        have hz : τ.SameCycle a z := Equiv.Perm.SameCycle.rfl.pow_right
        have hh := hz.apply_right
        rw [ht] at hh
        exact False.elim (h hh)
      · by_cases hb : σ z = b
        · exact False.elim (hab (hb ▸ hi))
        · change σ.SameCycle a (Equiv.swap a b (σ z))
          rw [Equiv.swap_apply_of_ne_of_ne ha hb]
          exact hi
  have ht : τ.SameCycle a (τ.symm a) := Equiv.Perm.SameCycle.rfl.symm_apply_right
  obtain ⟨n, hn⟩ := ht.exists_nat_pow_eq
  have hi := (hp n).apply_right
  rw [hn] at hi
  have he : σ (τ.symm a) = b := by
    change σ (σ.symm ((Equiv.swap a b).symm a)) = b
    simp
  exact hab (he ▸ hi)

/-- Every original cycle is contained in the joined cycle decomposition. -/
theorem swap_preserves_old_cycles (σ : Equiv.Perm α) (a b : α)
    (hab : ¬σ.SameCycle a b) {x y : α} (hxy : σ.SameCycle x y) :
    (Equiv.swap a b * σ).SameCycle x y := by
  let τ := Equiv.swap a b * σ
  have hj := swap_joins σ a b hab
  apply sameCycle_of_steps τ σ _ hxy
  intro z
  have hz : τ.SameCycle z (τ z) := Equiv.Perm.SameCycle.rfl.apply_right
  by_cases ha : σ z = a
  · have ht : τ z = b := by simp [τ, Equiv.Perm.mul_apply, ha]
    rw [ha]
    exact (ht ▸ hz).trans hj.symm
  · by_cases hb : σ z = b
    · have ht : τ z = a := by simp [τ, Equiv.Perm.mul_apply, hb]
      rw [hb]
      exact (ht ▸ hz).trans hj
    · have ht : τ z = σ z := Equiv.swap_apply_of_ne_of_ne ha hb
      exact ht ▸ hz

/-- Normalize the two old orbit labels to a single label. -/
noncomputable def joinedLabel (σ : Equiv.Perm α) (a b x : α) :
    Quotient (Equiv.Perm.SameCycle.setoid σ) := by
  classical
  exact if (Quotient.mk (Equiv.Perm.SameCycle.setoid σ) x) = Quotient.mk _ b
    then Quotient.mk _ a else Quotient.mk _ x

theorem swap_cycles_label (σ : Equiv.Perm α) (a b : α)
    (hab : ¬σ.SameCycle a b) (x y : α) :
    (Equiv.swap a b * σ).SameCycle x y ↔ joinedLabel σ a b x = joinedLabel σ a b y := by
  classical
  let τ := Equiv.swap a b * σ
  let q : α → Quotient (Equiv.Perm.SameCycle.setoid σ) := Quotient.mk _
  have qab : q a ≠ q b := fun h => hab (Quotient.exact h)
  have hq : ∀ z, q (σ z) = q z := fun z =>
    Quotient.sound Equiv.Perm.SameCycle.rfl.apply_left
  have hl : ∀ z, joinedLabel σ a b (σ z) = joinedLabel σ a b z := by
    intro z
    unfold joinedLabel
    change (if q (σ z) = q b then q a else q (σ z)) = _
    rw [hq]
  have hs : ∀ z, joinedLabel σ a b (Equiv.swap a b z) = joinedLabel σ a b z := by
    intro z
    by_cases ha : z = a
    · subst z
      simp [joinedLabel, Equiv.swap_apply_left]
    · by_cases hb : z = b
      · subst z
        simp [joinedLabel, Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne ha hb]
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      change joinedLabel σ a b x = joinedLabel σ a b (Equiv.swap a b (σ _))
      rw [hs, hl]
      exact ih
  · intro h
    have old : ∀ u v, q u = q v → τ.SameCycle u v := by
      intro u v huv
      exact swap_preserves_old_cycles σ a b hab (Quotient.exact huv)
    have hj : τ.SameCycle a b := swap_joins σ a b hab
    change (if q x = q b then q a else q x) = (if q y = q b then q a else q y) at h
    by_cases hx : q x = q b
    · by_cases hy : q y = q b
      · exact (old x b hx).trans (old y b hy).symm
      · simp only [ite_eq_left hx, ite_eq_right hy] at h
        exact ((old x b hx).trans hj.symm).trans (old a y h)
    · by_cases hy : q y = q b
      · simp only [ite_eq_right hx, ite_eq_left hy] at h
        exact ((old x a h).trans hj).trans (old y b hy).symm
      · simp only [ite_eq_right hx, ite_eq_right hy] at h
        exact old x y h

/-- Joining distinct cycles deletes precisely one label from the orbit quotient. -/
noncomputable def swapOrbitEquiv (σ : Equiv.Perm α) (a b : α)
    (hab : ¬σ.SameCycle a b) :
    Quotient (Equiv.Perm.SameCycle.setoid (Equiv.swap a b * σ)) ≃
      {q : Quotient (Equiv.Perm.SameCycle.setoid σ) // q ≠ Quotient.mk _ b} := by
  classical
  have qab : (Quotient.mk _ a : Quotient (Equiv.Perm.SameCycle.setoid σ)) ≠
      Quotient.mk _ b := fun h => hab (Quotient.exact h)
  let f : Quotient (Equiv.Perm.SameCycle.setoid (Equiv.swap a b * σ)) →
      {q : Quotient (Equiv.Perm.SameCycle.setoid σ) // q ≠ Quotient.mk _ b} :=
    Quotient.lift (fun x => ⟨joinedLabel σ a b x, by
      unfold joinedLabel
      split_ifs with h
      · exact qab
      · exact h⟩)
      (by
        intro x y h
        apply Subtype.ext
        exact (swap_cycles_label σ a b hab x y).mp h)
  apply Equiv.ofBijective f
  constructor
  · intro x y
    induction x using Quotient.inductionOn with
    | h x =>
      induction y using Quotient.inductionOn with
      | h y =>
        intro h
        exact Quotient.sound ((swap_cycles_label σ a b hab x y).mpr (congrArg Subtype.val h))
  · intro q
    obtain ⟨x, hx⟩ := Quotient.exists_rep q.val
    refine ⟨Quotient.mk _ x, ?_⟩
    apply Subtype.ext
    change joinedLabel σ a b x = q.val
    unfold joinedLabel
    rw [hx, ite_eq_right q.property]

theorem swap_cycle_count (σ : Equiv.Perm α) (a b : α)
    (hab : ¬σ.SameCycle a b) :
    Nat.card (Quotient (Equiv.Perm.SameCycle.setoid σ)) =
      Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (Equiv.swap a b * σ))) + 1 := by
  classical
  let Q := Quotient (Equiv.Perm.SameCycle.setoid σ)
  let := Fintype.ofFinite Q
  let := Fintype.ofFinite (Quotient (Equiv.Perm.SameCycle.setoid (Equiv.swap a b * σ)))
  have he := Nat.card_congr (swapOrbitEquiv σ a b hab)
  have hc := Fintype.card_subtype_compl (fun q : Q => q = Quotient.mk _ b)
  have hp : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨Quotient.mk _ b⟩
  simp only [Nat.card_eq_fintype_card] at he ⊢
  simp only [Fintype.card_unique] at hc
  change Fintype.card {q : Q // q ≠ Quotient.mk _ b} = Fintype.card Q - 1 at hc
  dsimp only [Q] at hc hp
  simp only [ne_eq] at he hc
  omega

end JSP512Probe.CycleSurgery
