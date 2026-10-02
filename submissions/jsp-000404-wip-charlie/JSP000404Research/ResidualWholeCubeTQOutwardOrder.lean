import JSP000404Research.ResidualWholeCubeTQCoordinateIdentification
import JSP000404Research.ResidualQTTTOrderRigidity
import Mathlib.Tactic

/-!
# Same-side outward direction of a known-owner T/Q augmentation

In a canonical Q/T/T state

  common ∈ Q_s ∩ T_c(x) ∩ T_b(y),   c != b,

suppose an additional T/Q collision from x to y uses a coordinate d != c.
Coordinate identification forces d=b, hence the actual retained edge colour
xy is b.

The Q/T/T order-rigidity lemmas then exclude exactly the two same-side orders
in which x lies farther from s than y:

  x < y < s,   s < y < x.

Thus, whenever x and y lie on the same side of the completion owner s, the
whole-cube/augmenting source x is the one closer to s:

  y < x < s  or  s < x < y.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem QTT_second_TQ_forces_partner_closer_on_same_side
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {s x y : V}
    (hsx : s ≠ x)
    (hsy : s ≠ y)
    (hxy : x ≠ y)
    (hxLoss : x ∈ projectedLossVertices C exponent)
    (hyLoss : y ∈ projectedLossVertices C exponent)
    {common extra : Fin n → Bool}
    {cx cy d : Fin n}
    (hcx : cx ∈ retainedActive C x)
    (hcy : cy ∈ retainedActive C y)
    (hcxy : cx ≠ cy)
    (hdx : d ∈ retainedActive C x)
    (hdcx : d ≠ cx)
    (hsQ : common ∈ retainedCompletionWords C s)
    (hxT : common ∈ translatedCompletionWords C x cx)
    (hyT : common ∈ translatedCompletionWords C y cy)
    (hxExtra : extra ∈ translatedCompletionWords C x d)
    (hyExtra : extra ∈ retainedCompletionWords C y) :
    ¬ ((x < y ∧ y < s) ∨ (s < y ∧ y < x)) := by
  have hdeq :
      d = cy :=
    second_TQ_coordinate_eq_known_translated_owner
      C exponent hexp honeLoss
      hxy hxLoss hyLoss
      hcxy hdcx
      hxT hyT
      hdx hxExtra hyExtra

  rintro hbad
  rcases hbad with hleft | hright
  · obtain ⟨hxylt,hys⟩ := hleft
    obtain ⟨hretRig,hcolRig⟩ :=
      QTT_same_left_side_outer_edge_eq_left_owner
        C exponent hexp honeLoss
        hxylt hys
        hxLoss hyLoss
        hcx hcy hcxy hsQ hxT hyT
    have hnewInter :
        (translatedCompletionWords C x d ∩
          retainedCompletionWords C y).Nonempty :=
      ⟨extra,Finset.mem_inter.mpr ⟨hxExtra,hyExtra⟩⟩
    have hnew :=
      loss_translated_intersection_forces_edge_colour
        C exponent hexp honeLoss
        hxLoss hxy hdx hnewInter
    obtain ⟨_hxy2,hretNew,hcolNew⟩ :=
      hnew.resolve_right (by
        rintro ⟨hyx,_⟩
        exact (not_lt_of_ge hxylt.le) hyx)
    have heq :
        retainedColor C x y hretRig =
          retainedColor C x y hretNew := by
      apply Fin.ext
      rfl
    rw [hcolRig,hcolNew,hdeq] at heq
    exact hcxy heq
  · obtain ⟨hsy,hyx⟩ := hright
    obtain ⟨hretRig,hcolRig⟩ :=
      QTT_same_right_side_outer_edge_eq_right_owner
        C exponent hexp honeLoss
        hsy hyx
        hyLoss hxLoss
        hcy hcx hcxy.symm hsQ hyT hxT
    have hnewInter :
        (translatedCompletionWords C x d ∩
          retainedCompletionWords C y).Nonempty :=
      ⟨extra,Finset.mem_inter.mpr ⟨hxExtra,hyExtra⟩⟩
    have hnew :=
      loss_translated_intersection_forces_edge_colour
        C exponent hexp honeLoss
        hxLoss hxy hdx hnewInter
    obtain ⟨_hyx2,hretNew,hcolNew⟩ :=
      hnew.resolve_left (by
        rintro ⟨hxy2,_⟩
        exact (not_lt_of_ge hyx.le) hxy2)
    have heq :
        retainedColor C y x hretRig =
          retainedColor C y x hretNew := by
      apply Fin.ext
      rfl
    rw [hcolRig,hcolNew,hdeq] at heq
    exact hcxy heq.symm

#print axioms QTT_second_TQ_forces_partner_closer_on_same_side

end OrderedEdgeColoring
end JSP000404Research
