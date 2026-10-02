import JSP000404Research.ResidualWholeCubePairSharedMass
import JSP000404Research.MinimalBlockSharedDeficit
import Mathlib.Tactic

/-!
# Extra shared word beyond a whole-cube Q/T pair

For a projected-loss second-layer vertex v, the enlarged all-active candidate
block has exact size 2^(n-1), while its dyadic demand is 2^(n-2).  Hence its
local slack is exactly 2^(n-2).

In an inclusion-minimal deficient core, minimality forces at least

  slack + 1 = 2^(n-2) + 1

shared words at v.

If v has a whole-cube Q/T partner s inside the same core, the two whole cubes
Q_v and Q_s already form exactly 2^(n-2) shared words.  Therefore at least one
additional shared word must exist outside Q_v ∪ Q_s.  This is the first
genuine augmenting witness beyond the whole-cube collision.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem secondLayer_projectedLoss_retainedActive_card_eq_three
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hn3 : 3 ≤ n)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2) :
    (retainedActive C v).card = 3 := by
  have hloss :=
    (mem_projectedLossVertices C exponent v).1 hvLoss
  unfold projectedFree at hloss
  rw [hvSecond] at hloss
  have hcardLe :
      (retainedActive C v).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive C v)
  omega

theorem secondLayer_projectedLoss_completion_card_eq
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hn3 : 3 ≤ n)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2) :
    (retainedCompletionWords C v).card = 2 ^ (n - 3) := by
  rw [retainedCompletionWords_card]
  have hloss :=
    (mem_projectedLossVertices C exponent v).1 hvLoss
  rw [hvSecond] at hloss
  omega

theorem secondLayer_projectedLoss_enlargedBlock_card_eq
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hn3 : 3 ≤ n)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2) :
    (enlargedProjectedCandidateBlock C exponent v).card =
      2 ^ (n - 1) := by
  rw [enlargedProjectedCandidateBlock_loss C exponent hvLoss,
      allActiveLossCandidateBlock_card,
      secondLayer_projectedLoss_retainedActive_card_eq_three
        C exponent hn3 hvLoss hvSecond,
      secondLayer_projectedLoss_completion_card_eq
        C exponent hn3 hvLoss hvSecond]
  have hshift : n - 3 + 2 = n - 1 := by omega
  calc
    (3 + 1) * 2 ^ (n - 3)
        = 2 ^ 2 * 2 ^ (n - 3) := by norm_num
    _ = 2 ^ ((n - 3) + 2) := by
      rw [pow_add]
      ring
    _ = 2 ^ (n - 1) := by rw [hshift]

theorem secondLayer_projectedLoss_enlargedBlock_slack_eq
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hn3 : 3 ≤ n)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2) :
    (enlargedProjectedCandidateBlock C exponent v).card -
        2 ^ exponent v
      =
    2 ^ (n - 2) := by
  rw [secondLayer_projectedLoss_enlargedBlock_card_eq
        C exponent hn3 hvLoss hvSecond,
      hvSecond]
  have hpow :
      2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    have hs : n - 2 + 1 = n - 1 := by omega
    rw [← hs, pow_succ]
  rw [hpow]
  omega

theorem wholeCubeQTPair_two_cubes_shared_in_core
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T : Finset V}
    {s v : V} {c : Fin n}
    (hsT : s ∈ T)
    (hsv : s ≠ v)
    (hsLoss : s ∈ projectedLossVertices C exponent)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hcV : c ∈ retainedActive C v)
    (hwhole : WholeCubeQTPair C s v c) :
    retainedCompletionWords C v ∪ retainedCompletionWords C s
      ⊆
    sharedBlockWords
      (enlargedProjectedCandidateBlock C exponent) T v := by
  have hpair :=
    wholeCubeQTPair_two_cubes_subset_block_intersection
      C exponent hsLoss hvLoss hcV hwhole
  intro word hword
  have hboth := hpair hword
  rw [Finset.mem_inter] at hboth
  rw [sharedBlockWords, Finset.mem_inter]
  refine ⟨hboth.1,?_⟩
  apply Finset.mem_biUnion.mpr
  exact ⟨s,Finset.mem_erase.mpr ⟨hsv,hsT⟩,hboth.2⟩

theorem wholeCubeQTPair_secondLayer_two_cubes_card_eq_demand
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hn3 : 3 ≤ n)
    {s v : V} {c : Fin n}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2)
    (hcV : c ∈ retainedActive C v)
    (hwhole : WholeCubeQTPair C s v c) :
    (retainedCompletionWords C v ∪
      retainedCompletionWords C s).card
      =
    2 ^ exponent v := by
  rcases hwhole with ⟨_hactiveEq,htransEq⟩
  have hdisj :
      Disjoint
        (retainedCompletionWords C v)
        (retainedCompletionWords C s) := by
    have h :=
      translatedCompletionWords_disjoint_original_of_active C hcV
    rw [htransEq] at h
    exact h.symm
  have hcardS :
      (retainedCompletionWords C s).card =
        (retainedCompletionWords C v).card := by
    rw [← htransEq, translatedCompletionWords_card]
  rw [Finset.card_union_of_disjoint hdisj,hcardS,
      secondLayer_projectedLoss_completion_card_eq
        C exponent hn3 hvLoss hvSecond,
      hvSecond]
  have hs : n - 3 + 1 = n - 2 := by omega
  rw [← hs,pow_succ]

/-- Minimality forces a genuinely new shared word outside the two whole cubes
already explained by a core whole-cube Q/T partner. -/
theorem minimal_core_wholeCubeQTPair_has_extra_shared_word
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hn3 : 3 ≤ n)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient
          (fun x => 2 ^ exponent x)
          (enlargedProjectedCandidateBlock C exponent)
          U)
    {s v : V} {c : Fin n}
    (hvT : v ∈ T)
    (hsT : s ∈ T)
    (hsv : s ≠ v)
    (hsLoss : s ∈ projectedLossVertices C exponent)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2)
    (hcV : c ∈ retainedActive C v)
    (hwhole : WholeCubeQTPair C s v c) :
    ∃ word : Fin n → Bool,
      word ∈
        sharedBlockWords
          (enlargedProjectedCandidateBlock C exponent) T v
      ∧
      word ∉ retainedCompletionWords C v
      ∧
      word ∉ retainedCompletionWords C s := by
  let blocks :=
    enlargedProjectedCandidateBlock C exponent
  have hblockCard :=
    secondLayer_projectedLoss_enlargedBlock_card_eq
      C exponent hn3 hvLoss hvSecond
  have hslack :=
    secondLayer_projectedLoss_enlargedBlock_slack_eq
      C exponent hn3 hvLoss hvSecond
  have hlocal :
      2 ^ exponent v ≤ (blocks v).card := by
    dsimp [blocks]
    rw [hblockCard,hvSecond]
    exact Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  have hsharedLower :=
    minimal_deficient_shared_card_ge_slack_add_one
      (fun x : V => 2 ^ exponent x)
      blocks hdef hmin hvT hlocal
  have hslack' :
      (blocks v).card - 2 ^ exponent v = 2 ^ exponent v := by
    dsimp [blocks]
    rw [hslack,hvSecond]
  rw [hslack'] at hsharedLower

  let twoCubes :=
    retainedCompletionWords C v ∪ retainedCompletionWords C s
  have htwoCard :
      twoCubes.card = 2 ^ exponent v := by
    dsimp [twoCubes]
    exact wholeCubeQTPair_secondLayer_two_cubes_card_eq_demand
      C exponent hn3 hvLoss hvSecond hcV hwhole

  by_contra hno
  push_neg at hno
  have hsub :
      sharedBlockWords blocks T v ⊆ twoCubes := by
    intro word hword
    by_contra hout
    have hvNot : word ∉ retainedCompletionWords C v := by
      intro hv
      exact hout (Finset.mem_union_left _ hv)
    have hsNot : word ∉ retainedCompletionWords C s := by
      intro hs
      exact hout (Finset.mem_union_right _ hs)
    exact hno word hword hvNot hsNot
  have hcardUpper :=
    Finset.card_le_card hsub
  rw [htwoCard] at hcardUpper
  omega

#print axioms secondLayer_projectedLoss_retainedActive_card_eq_three
#print axioms secondLayer_projectedLoss_enlargedBlock_card_eq
#print axioms secondLayer_projectedLoss_enlargedBlock_slack_eq
#print axioms minimal_core_wholeCubeQTPair_has_extra_shared_word


/-- The extra shared word forced by minimality cannot be supplied by the
whole-cube partner itself.  Hence it has a third core source. -/
theorem minimal_core_wholeCubeQTPair_has_third_source
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hn3 : 3 ≤ n)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient
          (fun x => 2 ^ exponent x)
          (enlargedProjectedCandidateBlock C exponent)
          U)
    {s v : V} {c : Fin n}
    (hvT : v ∈ T)
    (hsT : s ∈ T)
    (hsv : s ≠ v)
    (hsLoss : s ∈ projectedLossVertices C exponent)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2)
    (hcV : c ∈ retainedActive C v)
    (hwhole : WholeCubeQTPair C s v c) :
    ∃ word : Fin n → Bool,
    ∃ w : V,
      word ∈
        enlargedProjectedCandidateBlock C exponent v
      ∧
      word ∈
        enlargedProjectedCandidateBlock C exponent w
      ∧
      word ∉ retainedCompletionWords C v
      ∧
      word ∉ retainedCompletionWords C s
      ∧
      w ∈ T
      ∧
      w ≠ v
      ∧
      w ≠ s := by
  obtain ⟨word,hshared,hnotV,hnotS⟩ :=
    minimal_core_wholeCubeQTPair_has_extra_shared_word
      C exponent hn3 hdef hmin
      hvT hsT hsv hsLoss hvLoss hvSecond hcV hwhole

  have hparts := Finset.mem_inter.mp hshared
  have hvBlock :
      word ∈ enlargedProjectedCandidateBlock C exponent v :=
    hparts.1
  obtain ⟨w,hwErase,hwBlock⟩ :=
    Finset.mem_biUnion.mp hparts.2
  have hwNeV : w ≠ v :=
    (Finset.mem_erase.mp hwErase).1
  have hwT : w ∈ T :=
    (Finset.mem_erase.mp hwErase).2

  have hwNeS : w ≠ s := by
    intro hws
    subst w
    have hinter :
        word ∈
          enlargedProjectedCandidateBlock C exponent v ∩
            enlargedProjectedCandidateBlock C exponent s :=
      Finset.mem_inter.mpr ⟨hvBlock,hwBlock⟩
    have htwo :
        word ∈
          retainedCompletionWords C v ∪
            retainedCompletionWords C s := by
      rw [← wholeCubeQTPair_enlargedBlock_inter_eq_two_cubes
        C exponent hsLoss hvLoss hcV hwhole]
      exact hinter
    rcases Finset.mem_union.mp htwo with hV | hS
    · exact hnotV hV
    · exact hnotS hS

  exact ⟨word,w,hvBlock,hwBlock,hnotV,hnotS,hwT,hwNeV,hwNeS⟩

#print axioms minimal_core_wholeCubeQTPair_has_third_source

end OrderedEdgeColoring
end JSP000404Research
