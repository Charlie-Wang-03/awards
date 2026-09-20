import JSP000404Research.UniqueTransitionGap
import Mathlib.Tactic

/-!
# Pulling the Boolean transition blocks back to the ray list

The concrete lifted sign path has the form

  map sign rest ++ [!a].

The unique-transition theorem returns

  replicate p a ++ replicate (q+1) (!a).

Removing the common final [!a] shows that the actual noninitial ray list
splits after p entries into

  before ++ after,

where all before-rays have sign a and all after-rays have sign !a.

This is the exact list bridge needed by the ordinary/wrap transition exposure
lemmas.
-/

namespace JSP000404Research

/-- Replication by n+1 may be viewed as replication by n followed by one final
copy. -/
theorem replicate_succ_eq_append_singleton
    {α : Type*} (n : ℕ) (x : α) :
    List.replicate (n + 1) x =
      List.replicate n x ++ [x] := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, ih]
      simp [List.replicate_succ, List.cons_append]

/-- Remove the final antiperiodic sign from the lifted sign-path block
decomposition. -/
theorem strip_final_antiperiodic_sign
    (a : Bool) (xs : List Bool) (p q : ℕ)
    (h :
      xs ++ [!a] =
        List.replicate p a ++
          List.replicate (q + 1) (!a)) :
    xs =
      List.replicate p a ++
        List.replicate q (!a) := by
  have hrhs :
      List.replicate p a ++
          List.replicate (q + 1) (!a)
        =
      (List.replicate p a ++
          List.replicate q (!a)) ++ [!a] := by
    rw [replicate_succ_eq_append_singleton]
    simp [List.append_assoc]
  rw [hrhs] at h
  exact List.append_left_injective [!a] h

/-- Generic pullback of a two-block mapped sign decomposition to the source
list itself. -/
theorem exists_source_split_of_mapped_two_blocks
    {α : Type*}
    (sign : α → Bool)
    (a : Bool) (xs : List α)
    (p q : ℕ)
    (hmap :
      xs.map sign =
        List.replicate p a ++
          List.replicate q (!a)) :
    ∃ before after : List α,
      xs = before ++ after ∧
      before.length = p ∧
      after.length = q ∧
      before.map sign = List.replicate p a ∧
      after.map sign = List.replicate q (!a) := by
  let before := xs.take p
  let after := xs.drop p
  have hlen : xs.length = p + q := by
    have := congrArg List.length hmap
    simpa using this
  have hpLen : p ≤ xs.length := by omega
  refine ⟨before, after, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [before, after]
    exact (List.take_append_drop p xs).symm
  · dsimp [before]
    rw [List.length_take, Nat.min_eq_left hpLen]
  · dsimp [after]
    rw [List.length_drop, hlen]
    omega
  · dsimp [before]
    calc
      (xs.take p).map sign =
          (xs.map sign).take p := by simp
      _ =
          (List.replicate p a ++
            List.replicate q (!a)).take p := by rw [hmap]
      _ = List.replicate p a := by simp
  · dsimp [after]
    calc
      (xs.drop p).map sign =
          (xs.map sign).drop p := by simp
      _ =
          (List.replicate p a ++
            List.replicate q (!a)).drop p := by rw [hmap]
      _ = List.replicate q (!a) := by simp

/-- Specialized form for a lifted path
map sign rest ++ [!a] = a^p ++ (!a)^(q+1). -/
theorem exists_ray_split_of_lifted_sign_blocks
    {α : Type*}
    (sign : α → Bool)
    (a : Bool) (rest : List α)
    (p q : ℕ)
    (hlift :
      rest.map sign ++ [!a] =
        List.replicate p a ++
          List.replicate (q + 1) (!a)) :
    ∃ before after : List α,
      rest = before ++ after ∧
      before.length = p ∧
      after.length = q ∧
      before.map sign = List.replicate p a ∧
      after.map sign = List.replicate q (!a) := by
  have hmap :=
    strip_final_antiperiodic_sign
      a (rest.map sign) p q hlift
  exact exists_source_split_of_mapped_two_blocks
    sign a rest p q hmap

/-- Membership in a source block whose sign map is a replicate forces the
pointwise sign. -/
theorem sign_eq_of_mem_map_replicate
    {α : Type*}
    (sign : α → Bool)
    (a : Bool) (xs : List α)
    (hmap : xs.map sign = List.replicate xs.length a)
    {x : α} (hx : x ∈ xs) :
    sign x = a := by
  have hmem : sign x ∈ xs.map sign := by
    exact List.mem_map_of_mem sign hx
  rw [hmap] at hmem
  simpa using hmem

#print axioms strip_final_antiperiodic_sign
#print axioms exists_source_split_of_mapped_two_blocks
#print axioms exists_ray_split_of_lifted_sign_blocks
#print axioms sign_eq_of_mem_map_replicate

end JSP000404Research
