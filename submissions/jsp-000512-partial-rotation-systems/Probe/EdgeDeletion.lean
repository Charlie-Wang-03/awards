import Probe.RotationSystem
import Probe.CycleSurgery
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

namespace JSP512Probe
namespace CycleSurgery
variable {α : Type*} [DecidableEq α] [Finite α]

/-- Two deletions on the original carrier, with both removed elements fixed. -/
def erasePair (σ : Equiv.Perm α) (a b : α) : Equiv.Perm α :=
  eraseAt (eraseAt σ a) b

omit [Finite α] in
@[simp] theorem erasePair_left (σ : Equiv.Perm α) (a b : α) :
    erasePair σ a b a = a := by
  by_cases h : a = b
  · subst b; exact eraseAt_self _ _
  · rw [erasePair, eraseAt_apply _ b a h, eraseAt_self]
    simp [h]

omit [Finite α] in
@[simp] theorem erasePair_right (σ : Equiv.Perm α) (a b : α) :
    erasePair σ a b b = b := eraseAt_self _ _

theorem erasePair_cycles (σ : Equiv.Perm α) (a b x y : α)
    (hx : x ≠ a ∧ x ≠ b) (hy : y ≠ a ∧ y ≠ b) :
    (erasePair σ a b).SameCycle x y ↔ σ.SameCycle x y := by
  rw [erasePair, eraseAt_sameCycle_iff _ b x y hx.2 hy.2,
    eraseAt_sameCycle_iff _ a x y hx.1 hy.1]

omit [DecidableEq α] in
/-- Restriction of a permutation preserves its orbit relation. -/
theorem subtype_cycles (σ : Equiv.Perm α) (p : α → Prop)
    (hp : ∀ x, p x ↔ p (σ x)) (x y : Subtype p) :
    Equiv.Perm.SameCycle (σ.subtypeEquiv hp) x y ↔ σ.SameCycle x.val y.val := by
  have hpw : ∀ (n : ℕ) (z : Subtype p),
      (((σ.subtypeEquiv hp) ^ n) z).val = (σ ^ n) z.val := by
    intro n z
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [pow_succ', Equiv.Perm.mul_apply]
      change σ ((((σ.subtypeEquiv hp) ^ n) z).val) = _
      rw [ih]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    have hv := congrArg Subtype.val hn
    rw [hpw] at hv
    exact ⟨(n : ℤ), by simpa using hv⟩
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    have hs : ((σ.subtypeEquiv hp) ^ n) x = y := by
      apply Subtype.ext
      rw [hpw, hn]
    exact ⟨(n : ℤ), by simpa using hs⟩

omit [DecidableEq α] in
/-- Transport of permutations between equivalent carriers preserves orbits. -/
theorem transport_cycles {β : Type*} (e : β ≃ α) (σ : Equiv.Perm α)
    (x y : β) :
    Equiv.Perm.SameCycle ((e.trans σ).trans e.symm) x y ↔ σ.SameCycle (e x) (e y) := by
  let τ := (e.trans σ).trans e.symm
  have hpw : ∀ (n : ℕ) (z : β), e ((τ ^ n) z) = (σ ^ n) (e z) := by
    intro n z
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [pow_succ', Equiv.Perm.mul_apply]
      change e (e.symm (σ (e ((τ ^ n) z)))) = _
      rw [e.apply_symm_apply, ih]
  have : Finite β := Finite.of_equiv α e.symm
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    have hv := congrArg e hn
    rw [hpw] at hv
    exact ⟨(n : ℤ), by simpa using hv⟩
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    have hs : (τ ^ n) x = y := e.injective (by rw [hpw, hn])
    exact ⟨(n : ℤ), by simpa using hs⟩
end CycleSurgery
namespace RotationSystem
open CycleSurgery
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V]
  [DecidableRel G.Adj] (R : RotationSystem G) (d : G.Dart)

abbrev EdgeSurvivor := {x : G.Dart // x.edge ≠ d.edge}
abbrev DeletedGraph := G.deleteEdges {d.edge}

/-- The darts of the graph with one edge removed are exactly its surviving darts. -/
def deletedDartEquiv : (DeletedGraph d).Dart ≃ EdgeSurvivor d where
  toFun x := ⟨⟨x.toProd, x.adj.1⟩, by
    have h := (SimpleGraph.deleteEdges_adj.mp x.adj).2
    simpa only [Set.mem_singleton_iff, SimpleGraph.Dart.edge, ne_eq] using h⟩
  invFun x := ⟨x.val.toProd, SimpleGraph.deleteEdges_adj.mpr ⟨x.val.adj, by
    simpa only [Set.mem_singleton_iff, SimpleGraph.Dart.edge, ne_eq] using x.property⟩⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem survivor_ne (x : EdgeSurvivor d) : x.val ≠ d ∧ x.val ≠ d.symm := by
  have h := x.property
  change ¬ x.val.edge = d.edge at h
  rw [SimpleGraph.dart_edge_eq_iff x.val d] at h
  exact not_or.mp h

def erasedRotation : Equiv.Perm G.Dart := erasePair R.rotate d d.symm

omit [Fintype V] [DecidableRel G.Adj] in
theorem erased_survives (x : G.Dart) :
    x.edge ≠ d.edge ↔ (R.erasedRotation d x).edge ≠ d.edge := by
  have h₁ := (R.erasedRotation d).injective.ne_iff (x := x) (y := d)
  have h₂ := (R.erasedRotation d).injective.ne_iff (x := x) (y := d.symm)
  simp only [erasedRotation, erasePair_left, erasePair_right] at h₁ h₂
  simp only [ne_eq, SimpleGraph.dart_edge_eq_iff x d,
    SimpleGraph.dart_edge_eq_iff (R.erasedRotation d x) d, not_or]
  exact and_congr h₁.symm h₂.symm

def survivorRotation : Equiv.Perm (EdgeSurvivor d) :=
  (R.erasedRotation d).subtypeEquiv (R.erased_survives d)

theorem survivor_cycles (x y : EdgeSurvivor d) :
    (R.survivorRotation d).SameCycle x y ↔ x.val.fst = y.val.fst := by
  rw [survivorRotation, subtype_cycles]
  rw [erasedRotation, erasePair_cycles _ _ _ _ _ (survivor_ne d x) (survivor_ne d y)]
  exact R.sameCycle_iff_source _ _

/-- Rotation on the actual graph after deleting an undirected edge. -/
def deletedRotation : Equiv.Perm (DeletedGraph d).Dart :=
  ((deletedDartEquiv d).trans (R.survivorRotation d)).trans (deletedDartEquiv d).symm

theorem deleted_cycles (x y : (DeletedGraph d).Dart) :
    (R.deletedRotation d).SameCycle x y ↔ x.fst = y.fst := by
  rw [deletedRotation, transport_cycles, survivor_cycles]
  rfl

/-- Every rotation system induces a genuine rotation system after edge deletion.
This is a local cyclic-order theorem, not yet a genus-preservation theorem. -/
def deleteEdge : RotationSystem (DeletedGraph d) where
  rotate := R.deletedRotation d
  source _x := (R.deleted_cycles d _ _).mp Equiv.Perm.SameCycle.rfl.apply_left
  local_cycle x y h := (R.deleted_cycles d x y).mpr h

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Reversing a surviving dart is the same before and after graph deletion. -/
theorem deleted_reverse (x : (DeletedGraph d).Dart) :
    ((deletedDartEquiv d) x.symm).val = ((deletedDartEquiv d) x).val.symm := rfl

/-- The face successor on the deleted graph has the expected ambient formula. -/
theorem deleted_face (x : (DeletedGraph d).Dart) :
    ((deletedDartEquiv d) ((R.deleteEdge d).face x)).val =
      R.erasedRotation d (((deletedDartEquiv d) x).val.symm) := by
  change ((deletedDartEquiv d)
    ((deletedDartEquiv d).symm ((R.survivorRotation d)
      ((deletedDartEquiv d) x.symm)))).val = _
  rw [Equiv.apply_symm_apply]
  rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Rotating at the opposite endpoint never arrives at the first deleted dart. -/
theorem rotate_reverse_ne : R.rotate d.symm ≠ d := by
  intro h
  have hs := congrArg (fun x : G.Dart => x.fst) h
  rw [R.source] at hs
  exact d.snd_ne_fst hs

omit [Fintype V] [DecidableRel G.Adj] in
/-- The full-carrier face permutation changes by two explicit transpositions.
The two deleted darts remain an artificial orbit on this carrier; the actual
face permutation is on the smaller dart type in `deleted_face`. -/
theorem ambient_face_surgery :
    R.erasedRotation d * (reverseDart : Equiv.Perm G.Dart) =
      Equiv.swap d.symm (R.rotate d.symm) * Equiv.swap d (R.rotate d) * R.face := by
  have hb : eraseAt R.rotate d d.symm = R.rotate d.symm := by
    rw [eraseAt_apply _ _ _ d.symm_ne]
    simp only [ite_eq_right (R.rotate_reverse_ne d)]
  simp only [erasedRotation, erasePair, eraseAt, Equiv.Perm.mul_apply] at hb ⊢
  rw [hb]
  simp only [face, mul_assoc]

/-- On the old carrier, the removed darts form a spurious two-element face.
It must be excluded when counting faces of the actual deleted graph. -/
theorem removed_face_orbit (x : G.Dart) :
    (R.erasedRotation d * (reverseDart : Equiv.Perm G.Dart)).SameCycle d x ↔
      x = d ∨ x = d.symm := by
  let τ := R.erasedRotation d * (reverseDart : Equiv.Perm G.Dart)
  have hl : τ d = d.symm := by
    change erasePair R.rotate d d.symm d.symm = d.symm
    exact erasePair_right _ _ _
  have hr : τ d.symm = d := by
    change erasePair R.rotate d d.symm d.symm.symm = d
    rw [SimpleGraph.Dart.symm_symm, erasePair_left]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    have hp : ∀ n : ℕ, (τ ^ n) d = d ∨ (τ ^ n) d = d.symm := by
      intro k
      induction k with
      | zero => exact Or.inl rfl
      | succ k ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        rcases ih with ih | ih
        · exact Or.inr (by rw [ih, hl])
        · exact Or.inl (by rw [ih, hr])
    have hh := hp n
    rw [hn] at hh
    exact hh
  · intro h
    rcases h with rfl | rfl
    · exact Equiv.Perm.SameCycle.rfl
    · change τ.SameCycle d d.symm
      rw [← hl]
      exact Equiv.Perm.SameCycle.rfl.apply_right

end RotationSystem
end JSP512Probe
