import JSP000404Research.OriginalProblemStatement
import Jsp000404.UpperBound

/-!
# All-N ordinary sharpness, transported from the attributed construction

The construction is by superpilot69 and ChatGPT 6 Astra, vendored with its
MIT license in aznikline/jsp-000404-lean at the pinned dependency revision.
Aznikline supplies the all-cardinality formula and list interface. This
module only transports that checked theorem to our injective Fin N model.

No certificate premise from the external lower-bound development is used.
This is the upper-bound half of the original problem, not a complete proof.
-/

namespace JSP000404Research

theorem original_sharpness_allN (N : ℕ) (hN : 3 ≤ N) : OriginalSharpness N := by
  classical
  intro ε hε
  obtain ⟨C, hcard, hangle⟩ := Jsp404.sendov_upper N hN ε hε
  let e : Fin N ≃ Fin C.pts.length := finCongr hcard.symm
  let p : Fin N → Plane := fun i => C.pts.get (e i)
  have hp : Function.Injective p := by
    exact (List.nodup_iff_injective_get.mp C.nodup).comp e.injective
  refine ⟨p, hp, ?_⟩
  intro a b c hab hac hbc
  exact hangle (p a) (p b) (p c)
    (List.get_mem C.pts (e a)) (List.get_mem C.pts (e b))
    (List.get_mem C.pts (e c)) (hp.ne hab) (hp.ne hbc.symm) (hp.ne hac)

/-- With sharpness proved, the outstanding all-N task is exactly the
unconditional original lower bound. This equivalence supplies no such bound. -/
theorem originalProblem_iff_all_lower :
    OriginalProblem ↔ ∀ N : ℕ, 3 ≤ N → OriginalLowerBound N := by
  constructor
  · intro h N hN
    exact (h N hN).1
  · intro h N hN
    exact ⟨h N hN, original_sharpness_allN N hN⟩

/-- The injective enumeration and finite-set formulations quantify over
exactly the same ordinary configurations, including collinear ones. -/
theorem originalLowerBound_iff_guaranteed (N : ℕ) :
    OriginalLowerBound N ↔ JSP404.Guaranteed N (Jsp404.alphaN N) := by
  classical
  constructor
  · intro h s hs
    let e : Fin N ≃ s := (s.equivFinOfCardEq hs).symm
    let p : Fin N → Plane := fun i => (e i).val
    have hp : Function.Injective p := Subtype.val_injective.comp e.injective
    obtain ⟨a, b, c, hab, hac, hbc, hangle⟩ := h p hp
    exact ⟨p a, (e a).property, p b, (e b).property, p c, (e c).property,
      hp.ne hab, hp.ne hac, hp.ne hbc, hangle⟩
  · intro h p hp
    let s : Finset Plane := Finset.univ.image p
    have hs : s.card = N := by
      dsimp [s]
      rw [Finset.card_image_of_injective _ hp]
      simp
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hangle⟩ := h s hs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
    exact ⟨i, j, k, (fun hij => hab (congrArg p hij)),
      (fun hik => hac (congrArg p hik)), (fun hjk => hbc (congrArg p hjk)), hangle⟩

/-- Exact correspondence with the genuine supremum of universally forced
angles (equivalently, the infimum of configuration maxima). The equality on
the right remains unproved for arbitrary N; this theorem is only an iff. -/
theorem originalProblem_iff_geometric_alpha_eq :
    OriginalProblem ↔
      ∀ N : ℕ, 3 ≤ N → JSP404.alpha N = Jsp404.alphaN N := by
  rw [originalProblem_iff_all_lower]
  constructor
  · intro h N hN
    apply le_antisymm (Jsp404.alpha_le_alphaN N hN)
    exact JSP404.le_alpha ((originalLowerBound_iff_guaranteed N).1 (h N hN))
  · intro h N hN
    apply (originalLowerBound_iff_guaranteed N).2
    apply (JSP404.guaranteed_iff_le_alpha hN).2
    rw [h N hN]

#print axioms original_sharpness_allN
#print axioms originalProblem_iff_all_lower
#print axioms originalLowerBound_iff_guaranteed
#print axioms originalProblem_iff_geometric_alpha_eq

end JSP000404Research
