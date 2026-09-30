import JSP000404Research.ResidualSafeCommonInactiveNested
import JSP000404Research.ResidualPairLocalFlip
import Mathlib.Tactic

/-!
# Uniform one-bit exit from a one-sided reduced-zero nested overlap

Assume the left endpoint is reduced-zero in a no-active-safe saturated pair.
Then Q_u is contained in Q_v.

If the upper endpoint exponent is strictly below n, exact projected budget
implies retainedActive(v) is nonempty.  Because retainedActive(v) is contained
in retainedActive(u), any active coordinate c at v is active at both endpoints.

Flipping c therefore moves every word of the entire hard overlap block Q_u
outside both endpoint completion cubes.  The same coordinate gives one fixed
injective translation of the whole nested block into pairLocalHoles.

The right reduced-zero case is symmetric.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem retainedActive_nonempty_of_exact_lt_n
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hsat : ExactProjectedBudget C exponent v)
    (hlt : exponent v < n) :
    (retainedActive C v).Nonempty := by
  have hcard :
      (retainedActive C v).card = n - exponent v := by
    unfold ExactProjectedBudget projectedFree at hsat
    have hle :
        (retainedActive C v).card ≤ n := by
      simpa using Finset.card_le_univ (retainedActive C v)
    omega
  apply Finset.card_pos.mp
  rw [hcard]
  omega

theorem exists_nested_left_reducedZero_oneFlip_exit
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {base : Fin n → Bool}
    (hno : NoActiveSafeCoordinate C u v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v)
    (huZero :
      exponent u = (commonInactiveRetained C u v).card)
    (hvLt : exponent v < n) :
    ∃ c : Fin n,
      c ∈ retainedActive C u ∧
      c ∈ retainedActive C v ∧
      ∃ f :
        {word : Fin n → Bool //
          word ∈ retainedCompletionWords C u ∩
            retainedCompletionWords C v} →
        {word : Fin n → Bool //
          word ∈ pairLocalHoles C u v},
        Function.Injective f ∧
        ∀ word,
          (f word).1 = flipBoolWordAt word.1 c := by
  have hsub :=
    retainedActive_right_subset_left_of_noActiveSafe_reducedZero_left
      C exponent hno huBase hvBase huSat huZero
  obtain ⟨c,hcv⟩ :=
    retainedActive_nonempty_of_exact_lt_n
      C exponent hvSat hvLt
  have hcu := hsub hcv
  let f :
      {word : Fin n → Bool //
        word ∈ retainedCompletionWords C u ∩
          retainedCompletionWords C v} →
      {word : Fin n → Bool //
        word ∈ pairLocalHoles C u v} :=
    fun word => ⟨flipBoolWordAt word.1 c, by
      have hparts := Finset.mem_inter.mp word.2
      simp only [pairLocalHoles, Finset.mem_sdiff,
        Finset.mem_univ, true_and]
      rw [Finset.mem_union]
      push_neg
      exact ⟨
        flip_active_not_mem_completion C hparts.1 hcu,
        flip_active_not_mem_completion C hparts.2 hcv⟩⟩
  refine ⟨c,hcu,hcv,f,?_,?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply flipBoolWordAt_injective c
    exact congrArg Subtype.val hxy
  · intro word
    rfl

theorem exists_nested_right_reducedZero_oneFlip_exit
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {base : Fin n → Bool}
    (hno : NoActiveSafeCoordinate C u v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v)
    (hvZero :
      exponent v = (commonInactiveRetained C u v).card)
    (huLt : exponent u < n) :
    ∃ c : Fin n,
      c ∈ retainedActive C u ∧
      c ∈ retainedActive C v ∧
      ∃ f :
        {word : Fin n → Bool //
          word ∈ retainedCompletionWords C u ∩
            retainedCompletionWords C v} →
        {word : Fin n → Bool //
          word ∈ pairLocalHoles C u v},
        Function.Injective f ∧
        ∀ word,
          (f word).1 = flipBoolWordAt word.1 c := by
  have hsub :=
    retainedActive_left_subset_right_of_noActiveSafe_reducedZero_right
      C exponent hno huBase hvBase hvSat hvZero
  obtain ⟨c,hcu⟩ :=
    retainedActive_nonempty_of_exact_lt_n
      C exponent huSat huLt
  have hcv := hsub hcu
  let f :
      {word : Fin n → Bool //
        word ∈ retainedCompletionWords C u ∩
          retainedCompletionWords C v} →
      {word : Fin n → Bool //
        word ∈ pairLocalHoles C u v} :=
    fun word => ⟨flipBoolWordAt word.1 c, by
      have hparts := Finset.mem_inter.mp word.2
      simp only [pairLocalHoles, Finset.mem_sdiff,
        Finset.mem_univ, true_and]
      rw [Finset.mem_union]
      push_neg
      exact ⟨
        flip_active_not_mem_completion C hparts.1 hcu,
        flip_active_not_mem_completion C hparts.2 hcv⟩⟩
  refine ⟨c,hcu,hcv,f,?_,?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply flipBoolWordAt_injective c
    exact congrArg Subtype.val hxy
  · intro word
    rfl

#print axioms retainedActive_nonempty_of_exact_lt_n
#print axioms exists_nested_left_reducedZero_oneFlip_exit
#print axioms exists_nested_right_reducedZero_oneFlip_exit

end OrderedEdgeColoring
end JSP000404Research
