import Mathlib.Tactic

/-!
# Binary Kraft profiles behind the Sendov dyadic bound

The lower-branch target

  sum_i 2^(n-ell_i) <= 2^n

is exactly Kraft's inequality for code lengths ell_i.

Sendov's displayed extremal profile
  [1,2,3,3]
is only one full binary-tree leaf-depth profile (a comb).
The equally valid profile
  [2,2,2,2]
is the balanced depth-two tree.

This file records the correct combinatorial invariant: every full binary tree
has dyadic leaf mass exactly one.  In integer form, if n dominates every leaf
depth, then

  sum_{leaf depths d} 2^(n-d) = 2^n.

The remaining JSP-000404 geometry may therefore aim to construct a recursive
binary separation tree (possibly with extra depth slack), rather than prove one
specific sorted deficit profile.
-/

namespace JSP000404Research

inductive BinaryKraftTree where
  | leaf : BinaryKraftTree
  | node : BinaryKraftTree → BinaryKraftTree → BinaryKraftTree
deriving DecidableEq, Repr

namespace BinaryKraftTree

def depths : BinaryKraftTree → List ℕ
  | leaf => [0]
  | node L R =>
      (depths L).map Nat.succ ++
        (depths R).map Nat.succ

theorem depths_nonempty (T : BinaryKraftTree) :
    T.depths ≠ [] := by
  induction T with
  | leaf => simp [depths]
  | node L R ihL ihR =>
      simp [depths, ihL]

theorem exists_mem_depths (T : BinaryKraftTree) :
    ∃ d, d ∈ T.depths := by
  exact List.exists_mem_of_ne_nil T.depths_nonempty

/-- Exact integer Kraft identity for leaf depths of a full binary tree. -/
theorem dyadic_depth_sum_eq
    (T : BinaryKraftTree) (n : ℕ)
    (hdepth : ∀ d ∈ T.depths, d ≤ n) :
    (T.depths.map (fun d => 2 ^ (n - d))).sum = 2 ^ n := by
  induction T generalizing n with
  | leaf =>
      simp [depths]
  | node L R ihL ihR =>
      cases n with
      | zero =>
          obtain ⟨d, hd⟩ := L.exists_mem_depths
          have hsucc :
              d + 1 ∈ (node L R).depths := by
            simp [depths, hd]
          have := hdepth (d + 1) hsucc
          omega
      | succ n =>
          have hL :
              ∀ d ∈ L.depths, d ≤ n := by
            intro d hd
            have hsucc :
                d + 1 ∈ (node L R).depths := by
              simp [depths, hd]
            have hh := hdepth (d + 1) hsucc
            omega
          have hR :
              ∀ d ∈ R.depths, d ≤ n := by
            intro d hd
            have hsucc :
                d + 1 ∈ (node L R).depths := by
              simp [depths, hd]
            have hh := hdepth (d + 1) hsucc
            omega
          have ihL' := ihL n hL
          have ihR' := ihR n hR
          simp only [depths, List.map_append, List.sum_append,
            List.map_map]
          have hmapL :
              ((L.depths.map Nat.succ).map
                  (fun d => 2 ^ (Nat.succ n - d))).sum
                =
              (L.depths.map
                  (fun d => 2 ^ (n - d))).sum := by
            apply congrArg List.sum
            rw [List.map_map]
            apply List.map_congr_left
            intro d hd
            simp
          have hmapR :
              ((R.depths.map Nat.succ).map
                  (fun d => 2 ^ (Nat.succ n - d))).sum
                =
              (R.depths.map
                  (fun d => 2 ^ (n - d))).sum := by
            apply congrArg List.sum
            rw [List.map_map]
            apply List.map_congr_left
            intro d hd
            simp
          rw [hmapL, hmapR, ihL', ihR', pow_succ]
          omega

/-- A pointwise depth increase can only decrease the integer dyadic mass. -/
theorem dyadic_term_antitone
    {n d e : ℕ}
    (hde : d ≤ e) :
    2 ^ (n - e) ≤ 2 ^ (n - d) := by
  apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
  omega

/-- Listwise weakening of a Kraft profile. -/
theorem dyadic_sum_le_of_pairwise_depth_ge
    (treeDepth actualDepth : List ℕ)
    (n : ℕ)
    (halign :
      List.Forall₂ (fun d e => d ≤ e)
        treeDepth actualDepth) :
    (actualDepth.map (fun e => 2 ^ (n - e))).sum ≤
      (treeDepth.map (fun d => 2 ^ (n - d))).sum := by
  induction halign with
  | nil =>
      simp
  | cons d e ds es hde hrest ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add
        (dyadic_term_antitone hde) ih

/-- Tree certificate with depth slack gives the sharp Sendov dyadic bound. -/
theorem dyadic_sum_le_of_tree_profile
    (T : BinaryKraftTree)
    (actualDepth : List ℕ)
    (n : ℕ)
    (htree : ∀ d ∈ T.depths, d ≤ n)
    (halign :
      List.Forall₂ (fun d e => d ≤ e)
        T.depths actualDepth) :
    (actualDepth.map (fun e => 2 ^ (n - e))).sum ≤ 2 ^ n := by
  calc
    (actualDepth.map (fun e => 2 ^ (n - e))).sum
        ≤ (T.depths.map (fun d => 2 ^ (n - d))).sum :=
          dyadic_sum_le_of_pairwise_depth_ge
            T.depths actualDepth n halign
    _ = 2 ^ n := dyadic_depth_sum_eq T n htree

def sendovComb4 : BinaryKraftTree :=
  node leaf (node leaf (node leaf leaf))

def balanced4 : BinaryKraftTree :=
  node (node leaf leaf) (node leaf leaf)

@[simp] theorem sendovComb4_depths :
    sendovComb4.depths = [1,2,3,3] := by
  decide

@[simp] theorem balanced4_depths :
    balanced4.depths = [2,2,2,2] := by
  decide

/-- Both the profile printed by Sendov and the balanced four-centre profile
are exact Kraft extremizers. -/
theorem two_distinct_four_leaf_extremizers :
    (sendovComb4.depths.map (fun d => 2 ^ (3 - d))).sum = 2 ^ 3 ∧
    (balanced4.depths.map (fun d => 2 ^ (3 - d))).sum = 2 ^ 3 := by
  native_decide

#print axioms dyadic_depth_sum_eq
#print axioms dyadic_sum_le_of_tree_profile
#print axioms two_distinct_four_leaf_extremizers

end BinaryKraftTree
end JSP000404Research
