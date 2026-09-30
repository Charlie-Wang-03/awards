import Mathlib.Data.Finset.Order
import Mathlib.Tactic

/-!
# Geometric sum from ordered suffix ranks

Dual to OrderedPrefixGeometricSum.

Let S be a finite subset of a linear order. If

  card {w in S | v <= w} <= a(v) <= n

for every v in S, then

  sum_{v in S} 2^(n-a(v))
    <= 2^n - 2^(n-card S).

The proof removes the minimum element and uses strong induction on card S.
-/

namespace JSP000404Research

theorem ordered_suffix_geometric_sum_bound
    {V : Type*} [LinearOrder V]
    (S : Finset V)
    (a : V → ℕ)
    (n : ℕ)
    (haN : ∀ v ∈ S, a v ≤ n)
    (hrank :
      ∀ v ∈ S,
        (S.filter fun w => v ≤ w).card ≤ a v) :
    (∑ v ∈ S, 2 ^ (n - a v))
      ≤
    2 ^ n - 2 ^ (n - S.card) := by
  classical
  induction hcard : S.card using Nat.strong_induction_on generalizing S with
  | h m ih =>
      by_cases hS : S.Nonempty
      · let M := S.min' hS
        have hMmem : M ∈ S := Finset.min'_mem S hS
        let T := S.erase M
        have hTsub : T ⊆ S := Finset.erase_subset _ _
        have hMnotT : M ∉ T := by simp [T]
        have hcardT : T.card + 1 = S.card := by
          rw [← Finset.card_erase_add_one hMmem]
          rfl
        have hTlt : T.card < m := by
          rw [← hcard]
          omega
        have hmin :
            ∀ x ∈ T, M ≤ x := by
          intro x hx
          exact Finset.min'_le S x (hTsub hx)
        have hsuffixM :
            (S.filter fun w => M ≤ w) = S := by
          apply Finset.filter_eq_self.2
          intro x hx
          exact Finset.min'_le S x hx
        have haM : S.card ≤ a M := by
          have h := hrank M hMmem
          rw [hsuffixM] at h
          exact h
        have haMN : a M ≤ n := haN M hMmem
        have htermM :
            2 ^ (n - a M) ≤ 2 ^ (n - S.card) := by
          apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
          omega

        have hsuffixT :
            ∀ v ∈ T,
              (T.filter fun w => v ≤ w).card =
                (S.filter fun w => v ≤ w).card := by
          intro v hv
          have hMleV := hmin v hv
          have hvneM : v ≠ M := by
            intro h
            subst v
            exact hMnotT hv
          have hMltV : M < v := lt_of_le_of_ne hMleV (Ne.symm hvneM)
          apply congrArg Finset.card
          apply Finset.ext
          intro x
          constructor
          · intro hx
            have hxData := Finset.mem_filter.mp hx
            exact Finset.mem_filter.mpr
              ⟨hTsub hxData.1, hxData.2⟩
          · intro hx
            have hxData := Finset.mem_filter.mp hx
            have hxneM : x ≠ M := by
              intro h
              subst x
              exact (not_le_of_gt hMltV) hxData.2
            have hxT : x ∈ T :=
              Finset.mem_erase.mpr ⟨hxneM,hxData.1⟩
            exact Finset.mem_filter.mpr ⟨hxT,hxData.2⟩

        have haNT :
            ∀ v ∈ T, a v ≤ n := by
          intro v hv
          exact haN v (hTsub hv)
        have hrankT :
            ∀ v ∈ T,
              (T.filter fun w => v ≤ w).card ≤ a v := by
          intro v hv
          rw [hsuffixT v hv]
          exact hrank v (hTsub hv)
        have ihT :
            (∑ v ∈ T, 2 ^ (n - a v))
              ≤
            2 ^ n - 2 ^ (n - T.card) :=
          ih T.card hTlt T rfl haNT hrankT

        have hsumSplit :
            (∑ v ∈ S, 2 ^ (n - a v)) =
              2 ^ (n - a M) +
                ∑ v ∈ T, 2 ^ (n - a v) := by
          rw [← Finset.sum_erase_add _ hMmem]
          rfl

        have hpowStep :
            2 ^ (n - T.card) =
              2 * 2 ^ (n - S.card) := by
          have hTcardLtN : T.card < n := by
            have hcardN : S.card ≤ n := haM.trans haMN
            omega
          have hsub :
              n - T.card = (n - S.card) + 1 := by
            have hcardN : S.card ≤ n := haM.trans haMN
            omega
          rw [hsub, pow_succ]
          omega

        rw [hsumSplit]
        omega
      · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
        subst S
        simp

#print axioms ordered_suffix_geometric_sum_bound

end JSP000404Research
