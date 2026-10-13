import JSP000404Research.ResidualNetCollisionFibreDebtPartition
import JSP000404Research.ResidualActualCollisionTwoBitBridgePool
import JSP000404Research.ResidualTwoFlipExactSymmetricDifference
import Mathlib.Tactic

/-!
# Genuine NET canonical diagonals are INJECTIVE WITHIN each original soft bridge

Two actual hard-transport sink collision words lying in the SAME
original-source reverse-lower / forward-upper bridge necessarily
agree at ALL retained active coordinates of BOTH bridge endpoints.

Each of the four canonical hard-transport flip colours is ACTIVE at
one of those same two bridge endpoints. If the chosen double-flip
diagonals coincide, the exact symmetric-difference source disagreement
identity forces any different source bit to be at one of those colours.
This contradicts agreement of their bridge completion words.

Hence actual canonical diagonal reuse is possible ONLY ACROSS
DIFFERENT original soft bridge owners, an unconditional strengthening
of the previous same-unordered-flip-pair injection.

No assumption that the opposite diagonal is globally uncovered,
or that different bridges cannot hit it, is introduced.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A double-flip map is injective BETWEEN different chosen colour
pairs as long as both original words lie in a common bridge face
and every selected flip is active at one of its endpoints. -/
theorem two_flip_same_bridge_equal_target_source_eq
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (b v : V) (w z : Fin n → Bool)
    (cfS crS cfT crT : Fin n)
    (hS : cfS ≠ crS) (hT : cfT ≠ crT)
    (hcfS : cfS ∈ retainedActive C b)
    (hcrS : crS ∈ retainedActive C v)
    (hcfT : cfT ∈ retainedActive C b)
    (hcrT : crT ∈ retainedActive C v)
    (hwB : w ∈ retainedCompletionWords C b)
    (hwV : w ∈ retainedCompletionWords C v)
    (hzB : z ∈ retainedCompletionWords C b)
    (hzV : z ∈ retainedCompletionWords C v)
    (hdiag :
      flipCompletionWord cfS (flipCompletionWord crS w) =
      flipCompletionWord cfT (flipCompletionWord crT z)) :
    w = z := by
  have hagree :
      ∀ e : Fin n,
        e ∈ retainedActive C b ∨ e ∈ retainedActive C v →
          w e = z e := by
    intro e he
    rcases he with hb | hv
    · exact ((mem_retainedCompletionWords C b w).1 hwB e hb).trans
        (((mem_retainedCompletionWords C b z).1 hzB e hb).symm)
    · exact ((mem_retainedCompletionWords C v w).1 hwV e hv).trans
        (((mem_retainedCompletionWords C v z).1 hzV e hv).symm)
  funext e
  by_contra hne
  have hdiff :=
    (two_flip_target_eq_source_diff_iff_pair_exclusive
      w z cfS crS cfT crT hS hT hdiag e).mp hne
  have hin : e ∈ retainedActive C b ∨
      e ∈ retainedActive C v := by
    rcases hdiff with ⟨hs, _⟩ | ⟨_, ht⟩
    · rcases hs with he | he
      · subst e
        exact Or.inl hcfS
      · subst e
        exact Or.inr hcrS
    · rcases ht with he | he
      · subst e
        exact Or.inl hcfT
      · subst e
        exact Or.inr hcrT
  exact hne (hagree e hin)

/-- TRUE original soft bridge owner associated with the uniquely
certified forward and reverse hard sources of an ACTUAL NET collision. -/
noncomputable def netCollisionCertifiedBridgeOwner
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss}) : V × V :=
  let x := netCollisionCertifiedForwardSource C exponent hexp honeLoss s
  let y := netCollisionCertifiedReverseSource C exponent hexp honeLoss s
  ((strictDescentRigidWordCarrier C exponent y).1.1,
   (transportableWordCarrier C x).1.2)

/-- Two actual NET collision sink words with the SAME original bridge
and the SAME canonical opposite diagonal are equal.
This is stronger than the previously proved fixed-colour-pair
injection; the original flip COLOURS MAY VARY on that bridge. -/
theorem net_collision_same_bridge_same_diagonal_source_eq
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s t : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss})
    (hdiag : netCollisionCertifiedDiagonal C exponent hexp honeLoss s =
      netCollisionCertifiedDiagonal C exponent hexp honeLoss t)
    (hbridge : netCollisionCertifiedBridgeOwner
        C exponent hexp honeLoss s =
      netCollisionCertifiedBridgeOwner
        C exponent hexp honeLoss t) :
    s = t := by
  let xS := netCollisionCertifiedForwardSource C exponent hexp honeLoss s
  let yS := netCollisionCertifiedReverseSource C exponent hexp honeLoss s
  let pS := transportableWordCarrier C xS
  let qS := strictDescentRigidWordCarrier C exponent yS
  let xT := netCollisionCertifiedForwardSource C exponent hexp honeLoss t
  let yT := netCollisionCertifiedReverseSource C exponent hexp honeLoss t
  let pT := transportableWordCarrier C xT
  let qT := strictDescentRigidWordCarrier C exponent yT
  let cfS := transportablePairColor C pS
  let crS := strictDescentRigidPairColor C exponent hexp honeLoss qS
  let cfT := transportablePairColor C pT
  let crT := strictDescentRigidPairColor C exponent hexp honeLoss qT

  have hsrcS := net_collision_certified_sources_same_sink
    C exponent hexp honeLoss s
  have hsrcT := net_collision_certified_sources_same_sink
    C exponent hexp honeLoss t
  have hcollS : (transportableHardWordToSingletonOrSoft C xS).1 =
      (strictDescentRigidWordToSingletonOrSoft
        C exponent hexp honeLoss yS).1 := hsrcS.1.trans hsrcS.2.symm
  have hcollT : (transportableHardWordToSingletonOrSoft C xT).1 =
      (strictDescentRigidWordToSingletonOrSoft
        C exponent hexp honeLoss yT).1 := hsrcT.1.trans hsrcT.2.symm

  have hbridge' : (qS.1.1, pS.1.2) = (qT.1.1, pT.1.2) := by
    exact hbridge
  have hb : qS.1.1 = qT.1.1 :=
    congrArg (fun r : V × V => r.1) hbridge'
  have hv : pS.1.2 = pT.1.2 :=
    congrArg (fun r : V × V => r.2) hbridge'

  have hcrossS :=
    forward_reverse_collision_cross_active_flip_colors
      C exponent hexp honeLoss xS yS hcollS
  have hcrossT :=
    forward_reverse_collision_cross_active_flip_colors
      C exponent hexp honeLoss xT yT hcollT
  change cfS ∈ retainedActive C qS.1.1 ∧
    crS ∈ retainedActive C pS.1.2 at hcrossS
  change cfT ∈ retainedActive C qT.1.1 ∧
    crT ∈ retainedActive C pT.1.2 at hcrossT

  have hsB : s.1 ∈ retainedCompletionWords C qS.1.1 := by
    rw [← hsrcS.2]
    exact strictDescentRigidWordToSingletonOrSoft_mem_lower
      C exponent hexp honeLoss yS
  have hsV : s.1 ∈ retainedCompletionWords C pS.1.2 := by
    rw [← hsrcS.1]
    exact transportableHardWordToSingletonOrSoft_mem_upper C xS
  have htB : t.1 ∈ retainedCompletionWords C qS.1.1 := by
    rw [hb]
    rw [← hsrcT.2]
    exact strictDescentRigidWordToSingletonOrSoft_mem_lower
      C exponent hexp honeLoss yT
  have htV : t.1 ∈ retainedCompletionWords C pS.1.2 := by
    rw [hv]
    rw [← hsrcT.1]
    exact transportableHardWordToSingletonOrSoft_mem_upper C xT
  have hcolT_B : cfT ∈ retainedActive C qS.1.1 := by
    rw [hb]
    exact hcrossT.1
  have hcolT_V : crT ∈ retainedActive C pS.1.2 := by
    rw [hv]
    exact hcrossT.2
  have hcolS_ne : cfS ≠ crS :=
    net_collision_certified_forward_reverse_colours_distinct
      C exponent hexp honeLoss s
  have hcolT_ne : cfT ≠ crT :=
    net_collision_certified_forward_reverse_colours_distinct
      C exponent hexp honeLoss t
  have heq : flipCompletionWord cfS (flipCompletionWord crS s.1) =
      flipCompletionWord cfT (flipCompletionWord crT t.1) := by
    simpa only [netCollisionCertifiedDiagonal] using hdiag
  apply Subtype.ext
  exact two_flip_same_bridge_equal_target_source_eq
    C qS.1.1 pS.1.2 s.1 t.1 cfS crS cfT crT
    hcolS_ne hcolT_ne hcrossS.1 hcrossS.2
    hcolT_B hcolT_V hsB hsV htB htV heq

/-- Any positive ACTUAL canonical diagonal duplication debt
requires two different source words, with the same diagonal but
DIFFERENT true original soft bridge owners. Within each bridge
such reuse is impossible, even if flip colours vary. -/
theorem net_collision_positive_duplicate_requires_distinct_bridges
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hpositive : 0 < netCollisionCertifiedDuplicateDebt
      C exponent hexp honeLoss) :
    ∃ s t : {w : Fin n → Bool //
        w ∈ netActualForwardReverseCollisionWords
          C exponent hexp honeLoss},
      s ≠ t ∧
      netCollisionCertifiedDiagonal C exponent hexp honeLoss s =
        netCollisionCertifiedDiagonal C exponent hexp honeLoss t ∧
      netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s ≠
        netCollisionCertifiedBridgeOwner C exponent hexp honeLoss t := by
  obtain ⟨s, t, hne, heq⟩ :=
    net_collision_positive_duplicate_has_distinct_source_pair
      C exponent hexp honeLoss hpositive
  refine ⟨s, t, hne, heq, ?_⟩
  intro hsame
  exact hne (net_collision_same_bridge_same_diagonal_source_eq
    C exponent hexp honeLoss s t heq hsame)

#print axioms two_flip_same_bridge_equal_target_source_eq
#print axioms net_collision_same_bridge_same_diagonal_source_eq
#print axioms net_collision_positive_duplicate_requires_distinct_bridges

end OrderedEdgeColoring
end JSP000404Research
