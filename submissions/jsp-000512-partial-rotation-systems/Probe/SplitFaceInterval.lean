import Probe.SplitFaceStructure
import Probe.FiniteFan

namespace JSP512Probe.CycleSurgery
variable {α : Type*} [DecidableEq α] [Finite α]

/-- A split cycle is exactly the nonrepeating original traversal from the
first marked point up to, but excluding, the second marked point. -/
theorem split_cycle_interval (σ : Equiv.Perm α) (a b : α) (hne : a ≠ b)
    (hab : σ.SameCycle a b) :
    ∃ n : ℕ, 0 < n ∧ (σ ^ n) a = b ∧
      Function.Injective (fun i : Fin n => (σ ^ i.val) a) ∧
      (∀ k < n, ((Equiv.swap a b * σ) ^ k) a = (σ ^ k) a) ∧
      ∀ x, (Equiv.swap a b * σ).SameCycle a x ↔ ∃ i < n, (σ ^ i) a = x := by
  classical
  have hex := hab.exists_nat_pow_eq
  let n := Nat.find hex
  have hn : (σ ^ n) a = b := Nat.find_spec hex
  have hmin : ∀ k < n, (σ ^ k) a ≠ b := fun k hk => Nat.find_min hex hk
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
  let τ := Equiv.swap a b * σ
  have hp : ∀ k < n, (τ ^ k) a = (σ ^ k) a := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega)]
      change Equiv.swap a b (σ ((σ ^ k) a)) = _
      rw [show σ ((σ ^ k) a) = (σ ^ (k+1)) a by rw [pow_succ', Equiv.Perm.mul_apply]]
      exact Equiv.swap_apply_of_ne_of_ne (hreturn (k+1) (by omega) hk) (hmin (k+1) hk)
  have hinj : Function.Injective (fun i : Fin n => (σ ^ i.val) a) := by
    have lt_impossible : ∀ i j : Fin n, i.val < j.val → (σ ^ i.val) a ≠ (σ ^ j.val) a := by
      intro i j hij he
      have hh := congrArg (fun x => (σ ^ (n-j.val)) x) he
      have hl : (σ ^ (n-j.val)) ((σ ^ i.val) a) = (σ ^ (n-j.val+i.val)) a := by
        rw [pow_add, Equiv.Perm.mul_apply]
      have hr : (σ ^ (n-j.val)) ((σ ^ j.val) a) = b := by
        rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel (Nat.le_of_lt j.isLt), hn]
      rw [hl, hr] at hh
      exact hmin (n-j.val+i.val) (by omega) hh
    intro i j he
    apply Fin.ext
    rcases lt_trichotomy i.val j.val with hij | hij | hij
    · exact False.elim (lt_impossible i j hij he)
    · exact hij
    · exact False.elim (lt_impossible j i hij he.symm)
  let P := fun x => ∃ i < n, (σ ^ i) a = x
  have hPa : P a := ⟨0, hnpos, rfl⟩
  have hstep : ∀ x, P x → P (τ x) := by
    rintro x ⟨i, hi, rfl⟩
    change P (Equiv.swap a b (σ ((σ ^ i) a)))
    rw [show σ ((σ ^ i) a) = (σ ^ (i+1)) a by rw [pow_succ', Equiv.Perm.mul_apply]]
    by_cases hit : i+1 = n
    · rw [hit, hn, Equiv.swap_apply_right]
      exact hPa
    · have hlt : i+1 < n := by omega
      rw [Equiv.swap_apply_of_ne_of_ne (hreturn (i+1) (by omega) hlt) (hmin _ hlt)]
      exact ⟨i+1, hlt, rfl⟩
  refine ⟨n, hnpos, hn, hinj, hp, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := hx.exists_nat_pow_eq
    clear hx
    induction k with
    | zero => exact hPa
    | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply]; exact hstep _ ih
  · rintro ⟨i, hi, rfl⟩
    rw [← hp i hi]
    exact Equiv.Perm.SameCycle.rfl.pow_right

end JSP512Probe.CycleSurgery

namespace JSP512Probe.RotationSystem
open CycleSurgery
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)
  (a b : G.Dart) (hab : a.fst = b.fst)

/-- An explicit nonrepeating ordering of the actual first split outer face,
with exact coverage and its closing facial step. -/
theorem split_outer_interval (hne : a ≠ b) (hf : R.face.SameCycle a b) :
    let S := RefinedRotation.rotation G (R.splitRotation a b) (R.split_source a b hab)
    let E := RefinedRotation.dartEquiv G (R.splitRotation a b) (R.split_source a b hab)
    ∃ n : ℕ, 0 < n ∧ (R.face ^ n) a = b ∧
      Function.Injective (fun i : Fin n => E ((R.face ^ i.val) a)) ∧
      (∀ k < n, (S.face ^ k) (E a) = E ((R.face ^ k) a)) ∧
      (∀ d, S.face.SameCycle (E a) (E d) ↔ ∃ i < n, (R.face ^ i) a = d) ∧
      S.face (E ((R.face ^ (n-1)) a)) = E a := by
  dsimp only
  let S := RefinedRotation.rotation G (R.splitRotation a b) (R.split_source a b hab)
  let E := RefinedRotation.dartEquiv G (R.splitRotation a b) (R.split_source a b hab)
  let τ := Equiv.swap a b * R.face
  obtain ⟨n, hn, hnb, hinj, hp, hmem⟩ := split_cycle_interval R.face a b hne hf
  have hpow : ∀ k : ℕ, (S.face ^ k) (E a) = E ((τ ^ k) a) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih]
      rw [RefinedRotation.face_dart]
      change E (τ ((τ ^ k) a)) = E ((τ ^ (k+1)) a)
      rw [pow_succ', Equiv.Perm.mul_apply]
      rfl
  refine ⟨n, hn, hnb, fun i j hij => hinj (E.injective hij), ?_, ?_, ?_⟩
  · intro k hk
    rw [hpow, hp k hk]
  · intro d
    exact (R.split_face_cycles a b hab a d).trans (hmem d)
  · rw [RefinedRotation.face_dart]
    change E (Equiv.swap a b (R.face ((R.face ^ (n-1)) a))) = E a
    rw [show R.face ((R.face ^ (n-1)) a) = (R.face ^ n) a by
      rw [← Equiv.Perm.mul_apply, ← pow_succ']; congr 2; omega]
    rw [hnb, Equiv.swap_apply_right]

end JSP512Probe.RotationSystem

namespace JSP512Probe.EdgeInsertion
/-- Convert a finite indexed facial traversal to the list route consumed by
the fan-restoration interface. -/
theorem FaceRoute.power_list {α : Type*} (σ : Equiv.Perm α) (n : ℕ) (a : α) :
    FaceRoute σ (σ.symm a) (List.ofFn (fun i : Fin n => (σ ^ i.val) a)) := by
  induction n generalizing a with
  | zero => trivial
  | succ n ih =>
    rw [List.ofFn_succ]
    constructor
    · exact σ.apply_symm_apply a
    · have hh := ih (σ a)
      rw [σ.symm_apply_apply] at hh
      have he : (fun i : Fin n => (σ ^ i.succ.val) a) =
          (fun i : Fin n => (σ ^ i.val) (σ a)) := by
        funext i
        simp only [Fin.val_succ, pow_succ, Equiv.Perm.mul_apply]
      rw [he]
      exact hh
end JSP512Probe.EdgeInsertion
