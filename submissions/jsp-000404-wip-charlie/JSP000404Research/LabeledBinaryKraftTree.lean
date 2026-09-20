import JSP000404Research.BinaryKraftTree
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Vertex-labelled binary Kraft trees

BinaryKraftTree records only a multiset of leaf depths.  Geometry needs to
remember which original centre occupies each leaf.

A labelled full binary tree carries one vertex at every leaf.  Its profile is a
list of (vertex, depth) pairs.  If every finite vertex appears exactly once and
its tree depth is at most its Sendov deficit ell(v), then Kraft's identity gives

  sum_v 2^(n-ell(v)) <= 2^n.

This is the exact outlet for a recursive binary-split proof: every successful
split consumes one unit of available deficit for every centre descending into
that child.
-/

namespace JSP000404Research

inductive LabeledBinaryKraftTree (V : Type*) where
  | leaf : V → LabeledBinaryKraftTree V
  | node :
      LabeledBinaryKraftTree V →
      LabeledBinaryKraftTree V →
      LabeledBinaryKraftTree V

namespace LabeledBinaryKraftTree

def shape {V : Type*} : LabeledBinaryKraftTree V → BinaryKraftTree
  | leaf _ => .leaf
  | node L R => .node L.shape R.shape

def labels {V : Type*} : LabeledBinaryKraftTree V → List V
  | leaf v => [v]
  | node L R => L.labels ++ R.labels

def profile {V : Type*} :
    LabeledBinaryKraftTree V → List (V × ℕ)
  | leaf v => [(v, 0)]
  | node L R =>
      (L.profile.map fun vd => (vd.1, vd.2 + 1)) ++
      (R.profile.map fun vd => (vd.1, vd.2 + 1))

def depths {V : Type*} (T : LabeledBinaryKraftTree V) : List ℕ :=
  T.profile.map Prod.snd

@[simp] theorem shape_depths_eq
    {V : Type*} (T : LabeledBinaryKraftTree V) :
    T.shape.depths = T.depths := by
  induction T with
  | leaf v =>
      simp [shape, depths, profile, BinaryKraftTree.depths]
  | node L R ihL ihR =>
      simp [shape, depths, profile, BinaryKraftTree.depths,
        ihL, ihR, List.map_append, List.map_map]

@[simp] theorem profile_labels_eq
    {V : Type*} (T : LabeledBinaryKraftTree V) :
    T.profile.map Prod.fst = T.labels := by
  induction T with
  | leaf v =>
      simp [profile, labels]
  | node L R ihL ihR =>
      simp [profile, labels, List.map_append, List.map_map, ihL, ihR]

/-- Exact Kraft identity for a labelled tree, after forgetting the labels. -/
theorem dyadic_profile_sum_eq
    {V : Type*}
    (T : LabeledBinaryKraftTree V)
    (n : ℕ)
    (hdepth : ∀ vd ∈ T.profile, vd.2 ≤ n) :
    (T.profile.map (fun vd => 2 ^ (n - vd.2))).sum = 2 ^ n := by
  have hshape :
      ∀ d ∈ T.shape.depths, d ≤ n := by
    intro d hd
    rw [shape_depths_eq] at hd
    rcases List.mem_map.mp hd with ⟨vd, hvd, rfl⟩
    exact hdepth vd hvd
  have h :=
    BinaryKraftTree.dyadic_depth_sum_eq T.shape n hshape
  rw [shape_depths_eq] at h
  simpa [depths, List.map_map] using h

/-- Pointwise depth slack decreases the dyadic leaf mass. -/
theorem profile_target_weight_le
    {V : Type*}
    (xs : List (V × ℕ))
    (ell : V → ℕ) (n : ℕ)
    (hdepth : ∀ vd ∈ xs, vd.2 ≤ ell vd.1) :
    (xs.map (fun vd => 2 ^ (n - ell vd.1))).sum ≤
      (xs.map (fun vd => 2 ^ (n - vd.2))).sum := by
  induction xs with
  | nil =>
      simp
  | cons vd xs ih =>
      have hvd : vd.2 ≤ ell vd.1 :=
        hdepth vd (by simp)
      have htail :
          ∀ x ∈ xs, x.2 ≤ ell x.1 := by
        intro x hx
        exact hdepth x (by simp [hx])
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add
        (BinaryKraftTree.dyadic_term_antitone hvd)
        (ih htail)

/-- The profile target sum is the same as the leaf-label target sum, because
the target weight ignores tree depth. -/
theorem profile_target_sum_eq_labels
    {V : Type*}
    (T : LabeledBinaryKraftTree V)
    (ell : V → ℕ) (n : ℕ) :
    (T.profile.map (fun vd => 2 ^ (n - ell vd.1))).sum =
      (T.labels.map (fun v => 2 ^ (n - ell v))).sum := by
  have hlabels := T.profile_labels_eq
  calc
    (T.profile.map (fun vd => 2 ^ (n - ell vd.1))).sum
        =
      ((T.profile.map Prod.fst).map
        (fun v => 2 ^ (n - ell v))).sum := by
          simp [List.map_map]
    _ = (T.labels.map (fun v => 2 ^ (n - ell v))).sum := by
          rw [hlabels]

/-- Concrete labelled-tree certificate for a finite vertex family. -/
structure Certificate
    (V : Type*) [Fintype V]
    (n : ℕ) (ell : V → ℕ) where
  tree : LabeledBinaryKraftTree V
  nodup : tree.labels.Nodup
  complete : tree.labels.toFinset = Finset.univ
  depth_le :
    ∀ vd ∈ tree.profile, vd.2 ≤ ell vd.1
  ell_le_n : ∀ v, ell v ≤ n

namespace Certificate

/-- Kraft capacity in leaf-list form. -/
theorem list_capacity
    {V : Type*} [Fintype V]
    {n : ℕ} {ell : V → ℕ}
    (C : Certificate V n ell) :
    (C.tree.labels.map (fun v => 2 ^ (n - ell v))).sum ≤ 2 ^ n := by
  have hdepthN :
      ∀ vd ∈ C.tree.profile, vd.2 ≤ n := by
    intro vd hvd
    exact (C.depth_le vd hvd).trans (C.ell_le_n vd.1)
  have hpoint :=
    profile_target_weight_le
      C.tree.profile ell n C.depth_le
  have hkraft :=
    C.tree.dyadic_profile_sum_eq n hdepthN
  rw [C.tree.profile_target_sum_eq_labels ell n] at hpoint
  exact hpoint.trans_eq hkraft

/-- Main finite-vertex Kraft capacity theorem. -/
theorem capacity
    {V : Type*} [Fintype V]
    {n : ℕ} {ell : V → ℕ}
    (C : Certificate V n ell) :
    (∑ v : V, 2 ^ (n - ell v)) ≤ 2 ^ n := by
  classical
  have hlist := C.list_capacity
  have hsum :=
    List.sum_toFinset
      (fun v : V => 2 ^ (n - ell v))
      C.nodup
  rw [C.complete] at hsum
  rw [hsum]
  exact hlist

/-- Exponent form when ell(v)=n-exponent(v). -/
theorem exponent_capacity
    {V : Type*} [Fintype V]
    {n : ℕ}
    (exponent ell : V → ℕ)
    (C : Certificate V n ell)
    (hexp : ∀ v, exponent v ≤ n)
    (hell : ∀ v, ell v = n - exponent v) :
    (∑ v : V, 2 ^ exponent v) ≤ 2 ^ n := by
  calc
    (∑ v : V, 2 ^ exponent v)
        =
      ∑ v : V, 2 ^ (n - ell v) := by
        apply Finset.sum_congr rfl
        intro v _
        rw [hell v, Nat.sub_sub_cancel (hexp v)]
    _ ≤ 2 ^ n := C.capacity

end Certificate

#print axioms dyadic_profile_sum_eq
#print axioms profile_target_weight_le
#print axioms Certificate.capacity
#print axioms Certificate.exponent_capacity

end LabeledBinaryKraftTree
end JSP000404Research
