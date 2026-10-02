import JSP000404Research.ResidualWholeCubeSecondCoordinateCollision
import JSP000404Research.ResidualLossTranslatedConflict
import Mathlib.Tactic

/-!
# Coordinate identification for a T/Q augmentation hitting a known translated owner

Suppose distinct projected-loss vertices v,w already carry a common translated
word through coordinates c and b:

  common ∈ T_c(v) ∩ T_b(w),   c != b.

Hence the retained edge vw has colour c or b.

Suppose a second word gives a T/Q collision

  extra ∈ T_d(v) ∩ Q_w.

Then the same edge vw has retained colour exactly d.  If d != c, uniqueness
of the retained edge colour forces d=b.

This is the key coordinate-identification step when a whole-cube augmenting
third source is one of the already-known Q/T/T/T translated owners.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem second_TQ_coordinate_eq_known_translated_owner
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {v w : V}
    (hvw : v ≠ w)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwLoss : w ∈ projectedLossVertices C exponent)
    {common extra : Fin n → Bool}
    {c b d : Fin n}
    (hcb : c ≠ b)
    (hdc : d ≠ c)
    (hvCommon : common ∈ translatedCompletionWords C v c)
    (hwCommon : common ∈ translatedCompletionWords C w b)
    (hdV : d ∈ retainedActive C v)
    (hvExtra : extra ∈ translatedCompletionWords C v d)
    (hwExtra : extra ∈ retainedCompletionWords C w) :
    d = b := by
  have hOld :=
    translated_loss_conflict_edge_colour
      C exponent hexp honeLoss
      hvLoss hwLoss hvw hvCommon hwCommon

  have hNewInter :
      (translatedCompletionWords C v d ∩
        retainedCompletionWords C w).Nonempty :=
    ⟨extra,Finset.mem_inter.mpr ⟨hvExtra,hwExtra⟩⟩
  have hNew :=
    loss_translated_intersection_forces_edge_colour
      C exponent hexp honeLoss
      hvLoss hvw hdV hNewInter

  rcases lt_or_gt_of_ne hvw with hvwlt | hwvlt
  · obtain ⟨_,hretNew,hcolNew⟩ :=
      hNew.resolve_right (by
        rintro ⟨h,_⟩
        exact (not_lt_of_ge hvwlt.le) h)
    obtain ⟨_,hretOld,hcolOld⟩ :=
      hOld.resolve_right (by
        rintro ⟨h,_⟩
        exact (not_lt_of_ge hvwlt.le) h)
    have heq :
        retainedColor C v w hretNew =
          retainedColor C v w hretOld := by
      apply Fin.ext
      rfl
    rw [hcolNew] at heq
    rcases hcolOld with hc | hb
    · rw [hc] at heq
      exact False.elim (hdc heq)
    · rw [hb] at heq
      exact heq
  · obtain ⟨_,hretNew,hcolNew⟩ :=
      hNew.resolve_left (by
        rintro ⟨h,_⟩
        exact (not_lt_of_ge hwvlt.le) h)
    obtain ⟨_,hretOld,hcolOld⟩ :=
      hOld.resolve_left (by
        rintro ⟨h,_⟩
        exact (not_lt_of_ge hwvlt.le) h)
    have heq :
        retainedColor C w v hretNew =
          retainedColor C w v hretOld := by
      apply Fin.ext
      rfl
    rw [hcolNew] at heq
    rcases hcolOld with hc | hb
    · rw [hc] at heq
      exact False.elim (hdc heq)
    · rw [hb] at heq
      exact heq

#print axioms second_TQ_coordinate_eq_known_translated_owner

end OrderedEdgeColoring
end JSP000404Research
