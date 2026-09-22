import JSP000404Research.ResidualBlocker
import JSP000404Research.ResidualHoleInjection
import Mathlib.Tactic

/-!
# Density forced by blocked one-coordinate repairs

Let u<v be a hard retained-code pair.  For every retained coordinate c which
is inactive at u, flip c in the common retained code.

ResidualBlocker proves that if this neighbouring Boolean code is occupied,
every blocker lies strictly to the right of v.

There is a second rigidity: one vertex cannot block two different coordinates.
Indeed, a c-blocker differs from u at c and agrees with u away from c.

Consequently, if every inactive one-coordinate neighbour of u is occupied,
the inactive coordinates inject into vertices strictly to the right of v.

Under a retained activity budget

  card(retainedActive u) <= n - exponent(u),

the number of inactive coordinates is at least exponent(u).  Therefore

  exponent(u) <= #{w | v < w}.

This turns failure of the Boolean-hole repair into monotone combinatorial
growth to the right.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Retained coordinates inactive at a vertex. -/
noncomputable def retainedInactive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u : V) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun c => c ∉ retainedActive C u

@[simp] theorem mem_retainedInactive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u : V) (c : Fin n) :
    c ∈ retainedInactive C u ↔
      c ∉ retainedActive C u := by
  classical
  simp [retainedInactive]

/-- Vertices strictly to the right of v. -/
noncomputable def strictRightVertices
    {V : Type*} [LinearOrder V] [Fintype V]
    (v : V) : Finset V := by
  classical
  exact Finset.univ.filter fun w => v < w

@[simp] theorem mem_strictRightVertices
    {V : Type*} [LinearOrder V] [Fintype V]
    (v w : V) :
    w ∈ strictRightVertices v ↔ v < w := by
  classical
  simp [strictRightVertices]

/-- A blocker is exactly a vertex realizing the one-coordinate flipped
retained code. -/
theorem retainedCode_eq_flipped_iff_blocker
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u w : V) (c : Fin n) :
    (fun d => retainedBit C w d) =
        flippedRetainedCode C u c ↔
      RetainedNeighbourBlocker C u c w := by
  constructor
  · intro h
    constructor
    · have hc := congrFun h c
      have hne := flippedRetainedCode_at_ne C u c
      intro heq
      apply hne
      calc
        flippedRetainedCode C u c c
            = retainedBit C w c := hc.symm
        _ = retainedBit C u c := heq
    · intro d hdc
      have hd := congrFun h d
      rw [flippedRetainedCode_off C u c d hdc] at hd
      exact hd.symm
  · intro hblock
    funext d
    by_cases hdc : d = c
    · subst d
      have hne := hblock.1
      cases hw : retainedBit C w c <;>
        cases hu : retainedBit C u c <;>
        simp_all [flippedRetainedCode]
    · have heq := hblock.2 d hdc
      rw [flippedRetainedCode_off C u c d hdc]
      exact heq.symm

/-- One vertex cannot block two different one-coordinate neighbours of the
same base retained code. -/
theorem blocker_coordinate_unique
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u w : V} {c d : Fin n}
    (hc : RetainedNeighbourBlocker C u c w)
    (hd : RetainedNeighbourBlocker C u d w) :
    c = d := by
  by_contra hcd
  have heq : retainedBit C u c = retainedBit C w c :=
    hd.2 c hcd
  exact hc.1 heq.symm

/-- Exact complement count for inactive retained coordinates. -/
theorem retainedInactive_card
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u : V) :
    (retainedInactive C u).card =
      n - (retainedActive C u).card := by
  classical
  have hsub :
      retainedInactive C u =
        (Finset.univ : Finset (Fin n)) \ retainedActive C u := by
    ext c
    simp [retainedInactive]
  rw [hsub, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp

/-- A local retained-activity budget already gives the inactive-coordinate
lower bound; no global exact budget is needed. -/
theorem exponent_le_retainedInactive_card_of_local_bound
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {k : ℕ} {u : V}
    (hk : k ≤ n)
    (hretu :
      (retainedActive C u).card ≤ n - k) :
    k ≤ (retainedInactive C u).card := by
  rw [retainedInactive_card]
  omega

/-- Sendov-style activity budget gives at least exponent(u) inactive retained
coordinates. -/
theorem exponent_le_retainedInactive_card
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (hret :
      ∀ x,
        (retainedActive C x).card ≤ n - exponent x)
    (u : V) :
    exponent u ≤ (retainedInactive C u).card := by
  exact exponent_le_retainedInactive_card_of_local_bound
    C (hexp u) (hret u)

/-- If every inactive one-coordinate neighbour of the lower endpoint is
occupied, the inactive coordinates inject into vertices strictly to the right
of the upper endpoint. -/
theorem retainedInactive_card_le_right_of_blocked
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (huv : u < v)
    (hsame : SameRetained C u v)
    (hblocked :
      ∀ c, c ∈ retainedInactive C u →
        ∃ w : V, RetainedNeighbourBlocker C u c w) :
    (retainedInactive C u).card ≤
      (strictRightVertices v).card := by
  classical
  let chooseBlocker :
      {c : Fin n // c ∈ retainedInactive C u} → V :=
    fun c => Classical.choose (hblocked c.1 c.2)
  have hchoose :
      ∀ c : {c : Fin n // c ∈ retainedInactive C u},
        RetainedNeighbourBlocker C u c.1 (chooseBlocker c) := by
    intro c
    exact Classical.choose_spec (hblocked c.1 c.2)
  let f :
      {c : Fin n // c ∈ retainedInactive C u} →
        {w : V // w ∈ strictRightVertices v} :=
    fun c => ⟨chooseBlocker c, by
      rw [mem_strictRightVertices]
      apply blocker_after_other_of_lower_inactive
        C huv hsame
      · intro hc
        exact c.2
          ((castSucc_mem_active_iff_mem_retainedActive
            C u c.1).1 hc)
      · exact hchoose c⟩
  have hf : Function.Injective f := by
    intro c d hcd
    apply Subtype.ext
    have hw : chooseBlocker c = chooseBlocker d :=
      congrArg Subtype.val hcd
    have hd' :
        RetainedNeighbourBlocker C u d.1 (chooseBlocker c) := by
      rw [hw]
      exact hchoose d
    exact blocker_coordinate_unique
      C (hchoose c) hd'
  have hcard :=
    Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe] using hcard

/-- Main density consequence: if every inactive one-coordinate repair is
blocked, the lower endpoint's exponent is bounded by the number of vertices
strictly to the right of the hard pair. -/
theorem exponent_le_right_count_of_all_inactive_blocked
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (hret :
      ∀ x,
        (retainedActive C x).card ≤ n - exponent x)
    {u v : V}
    (huv : u < v)
    (hsame : SameRetained C u v)
    (hblocked :
      ∀ c, c ∈ retainedInactive C u →
        ∃ w : V, RetainedNeighbourBlocker C u c w) :
    exponent u ≤ (strictRightVertices v).card := by
  exact (exponent_le_retainedInactive_card C exponent hexp hret u).trans
    (retainedInactive_card_le_right_of_blocked
      C huv hsame hblocked)

/-- Occupancy formulation using the exact flipped retained code. -/
theorem exponent_le_right_count_of_all_flips_occupied
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (hret :
      ∀ x,
        (retainedActive C x).card ≤ n - exponent x)
    {u v : V}
    (huv : u < v)
    (hsame : SameRetained C u v)
    (hoccupied :
      ∀ c, c ∈ retainedInactive C u →
        ∃ w : V,
          (fun d => retainedBit C w d) =
            flippedRetainedCode C u c) :
    exponent u ≤ (strictRightVertices v).card := by
  apply exponent_le_right_count_of_all_inactive_blocked
    C exponent hexp hret huv hsame
  intro c hc
  obtain ⟨w, hw⟩ := hoccupied c hc
  exact ⟨w, (retainedCode_eq_flipped_iff_blocker C u w c).1 hw⟩

#print axioms retainedCode_eq_flipped_iff_blocker
#print axioms blocker_coordinate_unique
#print axioms retainedInactive_card
#print axioms exponent_le_retainedInactive_card_of_local_bound
#print axioms exponent_le_retainedInactive_card
#print axioms retainedInactive_card_le_right_of_blocked
#print axioms exponent_le_right_count_of_all_inactive_blocked
#print axioms exponent_le_right_count_of_all_flips_occupied

end OrderedEdgeColoring
end JSP000404Research
