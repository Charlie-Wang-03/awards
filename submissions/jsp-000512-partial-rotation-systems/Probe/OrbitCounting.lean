import Probe.EdgeDeletion
import Mathlib.Data.Fintype.Card

namespace JSP512Probe

/-- Removing exactly one equivalence class decreases the quotient cardinal by one.
The embedding hypotheses explicitly rule out losing or merging other classes. -/
noncomputable def quotientWithoutClass {α β : Type*} (s : Setoid α) (t : Setoid β)
    (a : β) (f : α → β)
    (hf : ∀ x y, t.r (f x) (f y) ↔ s.r x y)
    (hr : ∀ y, (∃ x, f x = y) ↔ ¬t.r a y) :
    Quotient s ≃ {q : Quotient t // q ≠ Quotient.mk t a} := by
  let g : Quotient s → {q : Quotient t // q ≠ Quotient.mk t a} :=
    Quotient.lift (fun x => ⟨Quotient.mk t (f x), by
      intro h
      have hx := (hr (f x)).mp ⟨x, rfl⟩
      exact hx (t.symm (Quotient.exact h))⟩)
      (by
        intro x y h
        apply Subtype.ext
        exact Quotient.sound ((hf x y).mpr h))
  apply Equiv.ofBijective g
  constructor
  · intro x y
    induction x using Quotient.inductionOn with
    | h x =>
      induction y using Quotient.inductionOn with
      | h y =>
        intro h
        exact Quotient.sound ((hf x y).mp (Quotient.exact (congrArg Subtype.val h)))
  · intro q
    obtain ⟨b, hb⟩ := Quotient.exists_rep q.val
    have hn : ¬t.r a b := by
      intro h
      apply q.property
      rw [← hb]
      exact Quotient.sound (t.symm h)
    obtain ⟨x, hx⟩ := (hr b).mpr hn
    refine ⟨Quotient.mk s x, ?_⟩
    apply Subtype.ext
    change Quotient.mk t (f x) = q.val
    rw [hx, hb]

theorem quotient_card_remove_class {α β : Type*} [Finite α] [Finite β]
    (s : Setoid α) (t : Setoid β) (a : β) (f : α → β)
    (hf : ∀ x y, t.r (f x) (f y) ↔ s.r x y)
    (hr : ∀ y, (∃ x, f x = y) ↔ ¬t.r a y) :
    Nat.card (Quotient t) = Nat.card (Quotient s) + 1 := by
  classical
  have he := Nat.card_congr (quotientWithoutClass s t a f hf hr)
  let := Fintype.ofFinite (Quotient t)
  let := Fintype.ofFinite (Quotient s)
  have hc := Fintype.card_subtype_compl (fun q : Quotient t => q = Quotient.mk t a)
  have hp : 0 < Fintype.card (Quotient t) := Fintype.card_pos_iff.mpr ⟨Quotient.mk t a⟩
  simp only [Nat.card_eq_fintype_card] at he ⊢
  simp only [Fintype.card_unique] at hc
  change Fintype.card {q : Quotient t // q ≠ Quotient.mk t a} =
    Fintype.card (Quotient t) - 1 at hc
  omega

/-- An injective map commuting with finite permutations reflects their orbits. -/
theorem sameCycle_embedding {α β : Type*} [Finite α] [Finite β]
    (σ : Equiv.Perm α) (τ : Equiv.Perm β) (f : α → β)
    (hf : Function.Injective f) (hc : ∀ x, f (σ x) = τ (f x)) (x y : α) :
    τ.SameCycle (f x) (f y) ↔ σ.SameCycle x y := by
  have hp : ∀ (n : ℕ) (z : α), f ((σ ^ n) z) = (τ ^ n) (f z) := by
    intro n z
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', pow_succ', Equiv.Perm.mul_apply,
        Equiv.Perm.mul_apply, hc, ih]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    have hs : (σ ^ n) x = y := hf (by rw [hp, hn])
    exact ⟨(n : ℤ), by simpa using hs⟩
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    have ht : (τ ^ n) (f x) = f y := by rw [← hp, hn]
    exact ⟨(n : ℤ), by simpa using ht⟩

namespace RotationSystem
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V]
  [DecidableRel G.Adj] (R : RotationSystem G) (d : G.Dart)

/-- Exact correction for the extra face retained on the old dart carrier. -/
theorem ambient_face_count :
    Nat.card (Quotient (Equiv.Perm.SameCycle.setoid
      (R.erasedRotation d * (reverseDart : Equiv.Perm G.Dart)))) =
      (R.deleteEdge d).faceCount + 1 := by
  let f : (DeletedGraph d).Dart → G.Dart := fun x => ((deletedDartEquiv d) x).val
  have hf : Function.Injective f := Subtype.val_injective.comp (deletedDartEquiv d).injective
  apply quotient_card_remove_class _ _ d f
  · intro x y
    exact sameCycle_embedding (R.deleteEdge d).face
      (R.erasedRotation d * reverseDart) f hf (R.deleted_face d) x y
  · intro y
    change (∃ x, f x = y) ↔ ¬(R.erasedRotation d * reverseDart).SameCycle d y
    rw [R.removed_face_orbit d]
    constructor
    · rintro ⟨x, rfl⟩
      exact not_or.mpr (survivor_ne d ((deletedDartEquiv d) x))
    · intro h
      have hy : y.edge ≠ d.edge := by
        change ¬y.edge = d.edge
        rw [SimpleGraph.dart_edge_eq_iff y d]
        exact h
      refine ⟨(deletedDartEquiv d).symm ⟨y, hy⟩, ?_⟩
      change ((deletedDartEquiv d) ((deletedDartEquiv d).symm ⟨y, hy⟩)).val = y
      rw [Equiv.apply_symm_apply]

end RotationSystem
end JSP512Probe
