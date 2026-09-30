import Mathlib.Data.Finset.Order
import Mathlib.Tactic

/-!
# Geometric sum from ordered prefix ranks

Let S be a finite subset of a linear order. Suppose a nonnegative integer
parameter a(v) dominates the prefix rank of every v in S,

  card {u in S | u <= v} <= a(v) <= n.

Then

  sum_{v in S} 2^(n-a(v))
    <= 2^n - 2^(n-card S).

The proof removes the maximum element. Its prefix rank is card S, so its term
is at most 2^(n-card S). Earlier prefix ranks are unchanged after deleting the
maximum, giving the sharp geometric induction.

This is the abstract summation lemma needed for one-sided translated-loss
fibres.
-/

namespace JSP000404Research

theorem ordered_prefix_geometric_sum_bound
    {V : Type*} [LinearOrder V]
    (S : Finset V)
    (a : V → ℕ)
    (n : ℕ)
    (haN : ∀ v ∈ S, a v ≤ n)
    (hrank :
      ∀ v ∈ S,
        (S.filter fun u => u ≤ v).card ≤ a v) :
    (∑ v ∈ S, 2 ^ (n - a v))
      ≤
    2 ^ n - 2 ^ (n - S.card) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp
  | @insert w S hw ih =>
      let M := (insert w S).max' (by simp)
      have hMmem : M ∈ insert w S := Finset.max'_mem _ _
      let T := (insert w S).erase M
      have hTM :
          insert w S = insert M T := by
        apply Finset.ext
        intro x
        by_cases hx : x = M
        · subst x
          simp [T, hMmem]
        · simp [T, hx]
      have hMnotT : M ∉ T := by
        simp [T]
      have hcardT :
          T.card + 1 = (insert w S).card := by
        rw [← Finset.card_erase_add_one hMmem]
      have hTsub : T ⊆ insert w S := by
        exact Finset.erase_subset _ _
      have hmax :
          ∀ x ∈ T, x ≤ M := by
        intro x hx
        exact Finset.le_max' (insert w S) x (hTsub hx)
      have hprefixM :
          ((insert w S).filter fun u => u ≤ M) =
            insert w S := by
        apply Finset.filter_eq_self.2
        intro x hx
        exact Finset.le_max' (insert w S) x hx
      have haM : (insert w S).card ≤ a M := by
        have h := hrank M hMmem
        rw [hprefixM] at h
        exact h
      have haMN : a M ≤ n := haN M hMmem
      have hcardN : (insert w S).card ≤ n := haM.trans haMN
      have htermM :
          2 ^ (n - a M) ≤
            2 ^ (n - (insert w S).card) := by
        apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
        omega
      have hprefixT :
          ∀ v ∈ T,
            (T.filter fun u => u ≤ v).card =
              ((insert w S).filter fun u => u ≤ v).card := by
        intro v hv
        have hvleM := hmax v hv
        have hvneM : v ≠ M := by
          intro h
          subst v
          exact hMnotT hv
        apply congrArg Finset.card
        apply Finset.ext
        intro x
        constructor
        · intro hx
          have hxData := Finset.mem_filter.mp hx
          have hxBig : x ∈ insert w S := hTsub hxData.1
          exact Finset.mem_filter.mpr ⟨hxBig,hxData.2⟩
        · intro hx
          have hxData := Finset.mem_filter.mp hx
          have hxneM : x ≠ M := by
            intro h
            subst x
            exact (not_le_of_gt (lt_of_le_of_ne hvleM hvneM)).elim hxData.2
          have hxT : x ∈ T := by
            exact Finset.mem_erase.mpr ⟨hxneM,hxData.1⟩
          exact Finset.mem_filter.mpr ⟨hxT,hxData.2⟩
      have ihT :
          (∑ v ∈ T, 2 ^ (n - a v))
            ≤
          2 ^ n - 2 ^ (n - T.card) := by
        apply ih
        · intro v hv
          exact haN v (hTsub hv)
        · intro v hv
          rw [hprefixT v hv]
          exact hrank v (hTsub hv)
      rw [hTM, Finset.sum_insert hMnotT]
      have hpowStep :
          2 ^ (n - T.card) =
            2 * 2 ^ (n - (insert w S).card) := by
        have hsucc :
            T.card + 1 = (insert w S).card := hcardT
        have hTN : T.card < n := by omega
        have hsub :
            n - T.card =
              (n - (insert w S).card) + 1 := by
          omega
        rw [hsub, pow_succ]
        omega
      omega

#print axioms ordered_prefix_geometric_sum_bound

end JSP000404Research
