import JSP000404Research.StandardResidualCrossingSafeFlipDescent
import Mathlib.Tactic

/-!
# Exact finite termination interface for strict-colour flip descent

A local crossing hard-pair theorem now establishes a three-way outlet:
* no vertex realizes the flipped retained CODE;
* an interior residual overlap is retained-separated;
* an exterior blocker occurs, with a new retained edge colour STRICTLY
  below the flipped retained coordinate.

A strict decrease of colours in Fin n rules out infinite descent, but
that alone does NOT show that the exterior blocker satisfies all the
hypotheses required to apply another safe-flip step. This module
separates the genuine finite-termination fact from that missing
geometric transition-closure hypothesis.

A state is represented abstractly; its numerical rank is in Fin n.
If every nonterminal state really has a successor with strictly
decreasing rank, an endpoint with no successor is reachable. If all
nonterminal states have a successor, that endpoint must be terminal.

No axiom, sorry, or subset-Hall G1 is used. This is NOT a proof that
a terminal state corresponds to a global UNUSED Boolean completion
word, and does NOT establish JSP-000404.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A finite derivation of geometrically admissible blocker transitions.
The transition relation itself is intentionally supplied, never assumed
to be closed under the exterior-blocker branch. -/
inductive RankedFlipReach {S : Type*} (step : S → S → Prop) : S → S → Prop where
  | refl (s : S) : RankedFlipReach step s s
  | cons {s u v : S} :
      step s u → RankedFlipReach step u v → RankedFlipReach step s v

/-- Strict natural-number decrease terminates at a state with no further
successor, assuming every state with a successor really can be followed. -/
theorem rankedFlipReach_terminal
    {S : Type*} {n : ℕ}
    (rank : S → Fin n)
    (step : S → S → Prop)
    (hdecrease : ∀ s u, step s u → (rank u).val < (rank s).val)
    (start : S) :
    ∃ endpoint : S,
      RankedFlipReach step start endpoint ∧
      ¬ ∃ u : S, step endpoint u := by
  have hmain :
      ∀ m : ℕ, ∀ s : S, (rank s).val = m →
        ∃ endpoint : S,
          RankedFlipReach step s endpoint ∧
          ¬ ∃ u : S, step endpoint u := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro s hrank
      by_cases hnext : ∃ u : S, step s u
      · obtain ⟨u, hsu⟩ := hnext
        have hless : (rank u).val < m := by
          have hd := hdecrease s u hsu
          omega
        obtain ⟨endpoint, hreached, hterminal⟩ :=
          ih (rank u).val hless u rfl
        exact ⟨endpoint,
          RankedFlipReach.cons hsu hreached, hterminal⟩
      · exact ⟨s, RankedFlipReach.refl s, hnext⟩
  exact hmain (rank start).val start rfl

/-- With a declared terminal predicate and an actual successor at
every nonterminal state, every start reaches a terminal state.
The NEXT-STATE-CLOSURE premise is explicit in hprogress. -/
theorem rankedFlipReach_eventually_terminal
    {S : Type*} {n : ℕ}
    (rank : S → Fin n)
    (step : S → S → Prop)
    (terminal : S → Prop)
    (hdecrease : ∀ s u, step s u → (rank u).val < (rank s).val)
    (hprogress : ∀ s, ¬ terminal s → ∃ u : S, step s u)
    (start : S) :
    ∃ endpoint : S,
      RankedFlipReach step start endpoint ∧
      terminal endpoint := by
  obtain ⟨endpoint, hreached, hno⟩ :=
    rankedFlipReach_terminal rank step hdecrease start
  refine ⟨endpoint, hreached, ?_⟩
  by_contra hbad
  exact hno (hprogress endpoint hbad)

/-- Any proposed n-step sequence of successor colours must fail to
decrease strictly at some step: a finite quantitative audit condition. -/
theorem no_unbounded_strict_colour_blocker_descent
    {n : ℕ} (colour : ℕ → Fin n)
    (hstep : ∀ i : ℕ,
      (colour (i + 1)).val < (colour i).val) : False := by
  have hbound : ∀ i : ℕ,
      (colour i).val + i ≤ (colour 0).val := by
    intro i
    induction i with
    | zero => omega
    | succ i ih =>
      have hs := hstep i
      omega
  have hn := hbound n
  have hlimit := (colour 0).isLt
  omega


/-- A length-indexed record of a sequence of admissible blocker steps. -/
inductive RankedFlipReachSteps {S : Type*}
    (step : S → S → Prop) : S → S → ℕ → Prop where
  | refl (s : S) : RankedFlipReachSteps step s s 0
  | cons {s u v : S} {steps : ℕ} :
      step s u →
      RankedFlipReachSteps step u v steps →
      RankedFlipReachSteps step s v (steps + 1)

/-- Every genuine chain spends at least one unit of finite colour rank
per step. In particular, the endpoint's remaining rank cannot become
negative; no claim of transition closure is made here. -/
theorem rankedFlipReachSteps_rank_budget
    {S : Type*} {n : ℕ}
    (rank : S → Fin n)
    (step : S → S → Prop)
    (hdecrease : ∀ s u, step s u →
      (rank u).val < (rank s).val)
    {start endpoint : S} {steps : ℕ}
    (hpath : RankedFlipReachSteps step start endpoint steps) :
    (rank endpoint).val + steps ≤ (rank start).val := by
  induction hpath with
  | refl s =>
      omega
  | @cons s u v steps hsu hrest ih =>
      have hdrop := hdecrease s u hsu
      omega

/-- A concrete bound on the maximum number of strict-colour
external-blocker transitions: fewer than n steps. -/
theorem rankedFlipReachSteps_lt_color_count
    {S : Type*} {n : ℕ}
    (rank : S → Fin n)
    (step : S → S → Prop)
    (hdecrease : ∀ s u, step s u →
      (rank u).val < (rank s).val)
    {start endpoint : S} {steps : ℕ}
    (hpath : RankedFlipReachSteps step start endpoint steps) :
    steps < n := by
  have hbudget :=
    rankedFlipReachSteps_rank_budget rank step hdecrease hpath
  have htop := (rank start).isLt
  omega

/-- The exterior blocker colour found in the genuine safe-flip descent
has value below the retained coordinate c < n. Thus the edge joining
the old upper endpoint to the blocker is RETAINED, not residual.
This prevents interpreting that edge as an immediately reusable hard
residual overlap without another geometric transition argument. -/
theorem exterior_blocker_descending_edge_not_residual
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v w : V) (c : Fin n)
    (hdesc : (C.color v w).val < c.val) :
    ¬ IsResidual C v w := by
  intro hres
  exact hres (lt_trans hdesc c.isLt)

/-- At the bottom retained colour, a strict-descending external blocker
cannot occur. This closes only the rank-zero endpoint of the LOCAL safe-flip
trichotomy; it says nothing about holes in the union of completion cubes. -/
theorem zero_colour_flip_no_external_blocker
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) (c : Fin n) (hc : c.val = 0) :
    ¬ ∃ w : V, v < w ∧ (C.color v w).val < c.val := by
  rintro ⟨w, _hvw, hlt⟩
  omega

/-- The established local safe-flip alternatives collapse from three to
two if the chosen safe coordinate is the least possible retained colour.
The first disjunct concerns canonical VERTEX CODES, not global Boolean
completion holes; the second concerns a locally separated residual edge. -/
theorem zero_colour_flip_code_hole_or_separation
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (a v : V) (c : Fin n) (hc : c.val = 0)
    (houtlet :
      (¬ ∃ w : V,
        (fun d => retainedBit C w d) = flippedRetainedCode C a c) ∨
      (∃ w : V,
        a < w ∧ w < v ∧
        IsResidual C w v ∧ RetainedSeparated C w v) ∨
      (∃ w : V,
        v < w ∧
        (fun d => retainedBit C w d) = flippedRetainedCode C a c ∧
        (C.color v w).val < c.val)) :
    (¬ ∃ w : V,
      (fun d => retainedBit C w d) = flippedRetainedCode C a c) ∨
    (∃ w : V,
      a < w ∧ w < v ∧
      IsResidual C w v ∧ RetainedSeparated C w v) := by
  rcases houtlet with hhole | hresolved | hext
  · exact Or.inl hhole
  · exact Or.inr hresolved
  · obtain ⟨w, hvw, _, hlt⟩ := hext
    exact False.elim
      ((zero_colour_flip_no_external_blocker C v c hc) ⟨w, hvw, hlt⟩)

/-- At rank zero there are no further strictly decreasing transitions.
The rank-zero observation does not supply the missing global payment. -/
theorem rankedFlipReach_zero_rank_terminal
    {S : Type*} {n : ℕ}
    (rank : S → Fin n)
    (step : S → S → Prop)
    (hdecrease : ∀ s u, step s u →
      (rank u).val < (rank s).val)
    (s : S) (hzero : (rank s).val = 0) :
    ¬ ∃ u : S, step s u := by
  rintro ⟨u, hsu⟩
  have hd := hdecrease s u hsu
  omega

#print axioms zero_colour_flip_no_external_blocker
#print axioms zero_colour_flip_code_hole_or_separation
#print axioms rankedFlipReach_zero_rank_terminal

#print axioms rankedFlipReachSteps_rank_budget
#print axioms rankedFlipReachSteps_lt_color_count
#print axioms exterior_blocker_descending_edge_not_residual

#print axioms rankedFlipReach_terminal
#print axioms rankedFlipReach_eventually_terminal
#print axioms no_unbounded_strict_colour_blocker_descent

end OrderedEdgeColoring
end JSP000404Research
