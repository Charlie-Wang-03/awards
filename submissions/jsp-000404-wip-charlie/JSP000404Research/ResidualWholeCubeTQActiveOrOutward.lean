import JSP000404Research.ResidualWholeCubeTQTwoFlip
import JSP000404Research.ResidualWholeCubeTQOrientation
import JSP000404Research.ResidualLossTranslatedBlock
import JSP000404Research.ResidualLossDirectionalWitness
import Mathlib.Tactic

/-!
# Active-or-outward dichotomy for a whole-cube T/Q augmentation

Let (s,v,c) be a whole-cube pair and let an augmenting word lie in

  T_d(v) ∩ Q_w,   d != c.

Assume s,v,w are projected-loss vertices.  The v--w edge has colour d.

If c is inactive at w, flipping c preserves membership in Q_w.  On the other
hand whole-cube equality T_c(v)=Q_s converts that c-flipped word into a
d-translated word of s.  Hence the s--w edge also has colour d.

The ordered-edge-colouring no-monochromatic-two-path axiom then forbids w from
lying strictly between s and v.

Therefore every T/Q augmentation satisfies a sharp dichotomy:

* c is active at the new source w; or
* w lies outside the open interval between s and v.

This gives a monotone progress measure for fresh whole-cube augmentations:
palette growth or order-interval expansion.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem wholeCube_TQ_inactive_owner_propagates_to_partner_translation
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s v w : V}
    {c d : Fin n}
    (hcV : c ∈ retainedActive C v)
    (hdV : d ∈ retainedActive C v)
    (hdc : d ≠ c)
    (hwhole : WholeCubeQTPair C s v c)
    (hcW : c ∉ retainedActive C w)
    {word : Fin n → Bool}
    (hvT : word ∈ translatedCompletionWords C v d)
    (hwQ : word ∈ retainedCompletionWords C w) :
    flipBoolWordAt word c ∈
      translatedCompletionWords C s d ∧
    flipBoolWordAt word c ∈
      retainedCompletionWords C w := by
  obtain ⟨_hwQ,hsTwoFlip,_hcS,hdS⟩ :=
    wholeCube_TQ_gives_twoFlip_into_partner_cube
      C hcV hdV hdc hwhole hvT hwQ

  have hwFlipC :
      flipBoolWordAt word c ∈ retainedCompletionWords C w :=
    (mem_completion_iff_flip_of_inactive C hcW).2 hwQ

  have hsTd :
      flipBoolWordAt word c ∈
        translatedCompletionWords C s d := by
    apply (mem_translatedCompletionWords C s d _).2
    have hcomm :
        flipBoolWordAt (flipBoolWordAt word c) d =
          flipBoolWordAt (flipBoolWordAt word d) c := by
      exact flipBoolWordAt_commute word hdc.symm
    rw [hcomm]
    exact hsTwoFlip

  exact ⟨hsTd,hwFlipC⟩

theorem wholeCube_TQ_inactive_owner_forces_two_d_edges
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {s v w : V}
    (hsv : s ≠ v)
    (hsw : s ≠ w)
    (hvw : v ≠ w)
    (hsLoss : s ∈ projectedLossVertices C exponent)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    {c d : Fin n}
    (hcV : c ∈ retainedActive C v)
    (hdV : d ∈ retainedActive C v)
    (hdc : d ≠ c)
    (hwhole : WholeCubeQTPair C s v c)
    (hcW : c ∉ retainedActive C w)
    {word : Fin n → Bool}
    (hvT : word ∈ translatedCompletionWords C v d)
    (hwQ : word ∈ retainedCompletionWords C w) :
    (
      ((∃ hsvlt : s < w,
          ∃ hret : (C.color s w).val < n,
            retainedColor C s w hret = d)
        ∨
        (∃ hwsl : w < s,
          ∃ hret : (C.color w s).val < n,
            retainedColor C w s hret = d))
    )
    ∧
    (
      (∃ hvwlt : v < w,
          ∃ hret : (C.color v w).val < n,
            retainedColor C v w hret = d)
        ∨
        (∃ hwvl : w < v,
          ∃ hret : (C.color w v).val < n,
            retainedColor C w v hret = d)
    ) := by
  obtain ⟨hsTd,hwFlipC⟩ :=
    wholeCube_TQ_inactive_owner_propagates_to_partner_translation
      C hcV hdV hdc hwhole hcW hvT hwQ

  have hdS : d ∈ retainedActive C s := by
    rcases hwhole with ⟨hactiveEq,_⟩
    rw [← hactiveEq]
    exact hdV

  have hswInter :
      (translatedCompletionWords C s d ∩
        retainedCompletionWords C w).Nonempty :=
    ⟨flipBoolWordAt word c,
      Finset.mem_inter.mpr ⟨hsTd,hwFlipC⟩⟩
  have hsvInter :
      (translatedCompletionWords C v d ∩
        retainedCompletionWords C w).Nonempty :=
    ⟨word,Finset.mem_inter.mpr ⟨hvT,hwQ⟩⟩

  have hswEdge :=
    loss_translated_intersection_forces_edge_colour
      C exponent hexp honeLoss
      hsLoss hsw hdS hswInter
  have hvwEdge :=
    loss_translated_intersection_forces_edge_colour
      C exponent hexp honeLoss
      hvLoss hvw hdV hsvInter

  exact ⟨hswEdge,hvwEdge⟩

theorem wholeCube_TQ_active_owner_or_source_outside_interval
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {s v w : V}
    (hsv : s ≠ v)
    (hsw : s ≠ w)
    (hvw : v ≠ w)
    (hsLoss : s ∈ projectedLossVertices C exponent)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    {c d : Fin n}
    (hcV : c ∈ retainedActive C v)
    (hdV : d ∈ retainedActive C v)
    (hdc : d ≠ c)
    (hwhole : WholeCubeQTPair C s v c)
    {word : Fin n → Bool}
    (hvT : word ∈ translatedCompletionWords C v d)
    (hwQ : word ∈ retainedCompletionWords C w) :
    c ∈ retainedActive C w
    ∨
    ¬ ((s < w ∧ w < v) ∨ (v < w ∧ w < s)) := by
  by_cases hcW : c ∈ retainedActive C w
  · exact Or.inl hcW
  · right
    have hedges :=
      wholeCube_TQ_inactive_owner_forces_two_d_edges
        C exponent hexp honeLoss
        hsv hsw hvw hsLoss hvLoss
        hcV hdV hdc hwhole hcW hvT hwQ
    intro hbetween
    rcases hbetween with hswv | hvws
    · obtain ⟨hswlt,hwvlt⟩ := hswv
      rcases hedges.1 with hswE | hwsE
      · obtain ⟨_,hretSW,hcolSW⟩ := hswE
        rcases hedges.2 with hvwE | hwvE
        · exact False.elim
            ((not_lt_of_ge hwvlt.le) hvwE.choose)
        · obtain ⟨_,hretWV,hcolWV⟩ := hwvE
          have hfullSW :
              C.color s w = d.castSucc := by
            apply Fin.ext
            have hv := congrArg Fin.val hcolSW
            simpa [retainedColor] using hv
          have hfullWV :
              C.color w v = d.castSucc := by
            apply Fin.ext
            have hv := congrArg Fin.val hcolWV
            simpa [retainedColor] using hv
          exact C.noMonoTwoPath hswlt hwvlt
            (by rw [hfullSW,hfullWV])
      · exact False.elim
          ((not_lt_of_ge hswlt.le) hwsE.choose)
    · obtain ⟨hvwlt,hwsl⟩ := hvws
      rcases hedges.2 with hvwE | hwvE
      · obtain ⟨_,hretVW,hcolVW⟩ := hvwE
        rcases hedges.1 with hswE | hwsE
        · exact False.elim
            ((not_lt_of_ge hwsl.le) hswE.choose)
        · obtain ⟨_,hretWS,hcolWS⟩ := hwsE
          have hfullVW :
              C.color v w = d.castSucc := by
            apply Fin.ext
            have hv := congrArg Fin.val hcolVW
            simpa [retainedColor] using hv
          have hfullWS :
              C.color w s = d.castSucc := by
            apply Fin.ext
            have hv := congrArg Fin.val hcolWS
            simpa [retainedColor] using hv
          exact C.noMonoTwoPath hvwlt hwsl
            (by rw [hfullVW,hfullWS])
      · exact False.elim
          ((not_lt_of_ge hvwlt.le) hwvE.choose)

#print axioms wholeCube_TQ_inactive_owner_propagates_to_partner_translation
#print axioms wholeCube_TQ_active_owner_or_source_outside_interval

end OrderedEdgeColoring
end JSP000404Research
