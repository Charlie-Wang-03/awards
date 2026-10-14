import JSP000404Research.ResidualNetCollisionCandidateColourVertexSeparation
import Mathlib.Tactic

/-!
# Every eligible target-exact soft-bridge edge has a covered shadow word

The exact double-shell candidate constraint does more than control
matching conflicts. If target d violates exactly one retained-active
coordinate at each bridge endpoint, and the other endpoint's flip
coordinate is retained-inactive there, then flipping BOTH selected
original colours in d produces a word lying in BOTH endpoint
completion cubes.

This construction is for every eligible candidate edge, whether or
not that edge is the source of a genuine NET collision. It
establishes that its two-flip shadow word is COVERED (indeed SOFT)
by two distinct source-compatible bridge vertices. The witness is
NOT a TRUE Boolean hole. Nothing here makes the candidate edge
itself a genuine hard-source collision, nor makes candidate shadows
injective across targets or globally payable.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A singleton retained-active violation coordinate can be
corrected by flipping it. A second flip on an INACTIVE coordinate
does not alter any of the vertex's retained constraints. -/
theorem two_flip_corrects_singleton_retained_violation
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) (ca ci : Fin n) (d : Fin n → Bool)
    (hviol : retainedActiveViolationCoords C v d = {ca})
    (hi : ci ∉ retainedActive C v) :
    flipCompletionWord ca (flipCompletionWord ci d) ∈
      retainedCompletionWords C v := by
  classical
  have hmem : ca ∈ retainedActiveViolationCoords C v d := by
    rw [hviol]
    simp
  have ha : ca ∈ retainedActive C v :=
    (Finset.mem_filter.mp hmem).2.1
  have hdiff : d ca ≠ retainedBit C v ca :=
    (Finset.mem_filter.mp hmem).2.2
  have hne : ca ≠ ci := by
    intro h
    exact hi (h ▸ ha)
  apply (mem_retainedCompletionWords C v _).2
  intro c hc
  by_cases heq : c = ca
  · subst c
    rw [flipCompletionWord_at, flipCompletionWord_off ci ca d hne]
    cases hd : d ca <;> cases hr : retainedBit C v ca <;> simp_all
  · have hci : c ≠ ci := by
      intro h
      exact hi (h ▸ hc)
    rw [flipCompletionWord_off ca c _ heq,
      flipCompletionWord_off ci c d hci]
    by_contra hbad
    have hmemBad : c ∈ retainedActiveViolationCoords C v d :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hc, hbad⟩
    rw [hviol] at hmemBad
    exact heq (Finset.mem_singleton.mp hmemBad)

/-- An element of a finite one-element set is its unique element. -/
private theorem target_shell_eq_singleton_of_mem
    {n : ℕ} (S : Finset (Fin n)) (hcard : S.card = 1)
    (c : Fin n) (hc : c ∈ S) :
    S = {c} := by
  classical
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hcard
  have h : c = k := by
    rw [hk] at hc
    exact Finset.mem_singleton.mp hc
  simpa [h] using hk

/-- Every eligible target-exact candidate edge defines a
reverse-two-flip SHADOW word that is simultaneously contained
in BOTH original bridge endpoint retained completion cubes.
This result requires only the candidate graph predicate,
not certification of any genuine NET source. -/
theorem target_exact_shell_candidate_shadow_mem_both_endpoint_cubes
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool)
    (e : (V × Fin n) × (V × Fin n))
    (he : e ∈ targetExactShellSlotEdges C exponent d) :
    let b := e.1.1
    let v := e.2.1
    let cr := e.1.2
    let cf := e.2.2
    let shadow := flipCompletionWord cf (flipCompletionWord cr d)
    shadow ∈ retainedCompletionWords C b ∧
      shadow ∈ retainedCompletionWords C v := by
  classical
  obtain ⟨_, hbridge, hcr, hcf, hncr, hncf⟩ :=
    Finset.mem_filter.mp he
  have hbridgeShell := (Finset.mem_filter.mp hbridge).2
  have hcardB :
      (retainedActiveViolationCoords C e.1.1 d).card = 1 :=
    hbridgeShell.1
  have hcardV :
      (retainedActiveViolationCoords C e.2.1 d).card = 1 :=
    hbridgeShell.2.1
  have hb :
      retainedActiveViolationCoords C e.1.1 d = {e.2.2} :=
    target_shell_eq_singleton_of_mem _ hcardB _ hcf
  have hv :
      retainedActiveViolationCoords C e.2.1 d = {e.1.2} :=
    target_shell_eq_singleton_of_mem _ hcardV _ hcr
  have hcfActive : e.2.2 ∈ retainedActive C e.1.1 :=
    (Finset.mem_filter.mp hcf).2.1
  have hne : e.2.2 ≠ e.1.2 := by
    intro h
    exact hncr (h ▸ hcfActive)
  change
    flipCompletionWord e.2.2 (flipCompletionWord e.1.2 d) ∈
        retainedCompletionWords C e.1.1 ∧
    flipCompletionWord e.2.2 (flipCompletionWord e.1.2 d) ∈
        retainedCompletionWords C e.2.1
  constructor
  · exact two_flip_corrects_singleton_retained_violation
      C e.1.1 e.2.2 e.1.2 d hb hncr
  · rw [flipCompletionWord_comm e.2.2 e.1.2 d hne]
    exact two_flip_corrects_singleton_retained_violation
      C e.2.1 e.1.2 e.2.2 d hv hncf

/-- In particular, the candidate shadow is NOT a true Boolean
hole: it is already covered by at least its lower bridge endpoint.
This is a verified no-double-counting barrier. -/
theorem target_exact_shell_candidate_shadow_mem_covered
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool)
    (e : (V × Fin n) × (V × Fin n))
    (he : e ∈ targetExactShellSlotEdges C exponent d) :
    flipCompletionWord e.2.2 (flipCompletionWord e.1.2 d) ∈
      coveredCompletionWords C := by
  have hb := (target_exact_shell_candidate_shadow_mem_both_endpoint_cubes
    C exponent d e he).1
  apply (mem_coveredCompletionWords C _).2
  exact ⟨e.1.1, (mem_completionFibre C _ _).2 hb⟩

#print axioms two_flip_corrects_singleton_retained_violation
#print axioms target_exact_shell_candidate_shadow_mem_both_endpoint_cubes
#print axioms target_exact_shell_candidate_shadow_mem_covered

end OrderedEdgeColoring
end JSP000404Research
