import JSP000404Research.ThreeWholeCubeInteriorExtremeExclusion
import Mathlib.Tactic

/-!
# Interior-source extreme orientation and retained-bit profiles

For an ordered whole-cube star a<b<c<d, the retained-code star already forces
one of the four vertices to be a global order extreme.

Once the ordered-adjacent small-angle terminal has forced the two-colour
partner-edge staircase, the wrong endpoint extreme is impossible:

* source=b: d cannot be the global maximum, so a is the global minimum;
* source=c: a cannot be the global minimum, so d is the global maximum.

The source retained code is then forced:

* source=b: (x,y,z) = (true,false,false);
* source=c: (x,y,z) = (true,true,false).

This module is purely combinatorial / retained-code.  Projection geometry is
used only by the separate staircase-producing module.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem source_second_staircase_forces_left_min_and_100
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (hone :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {a b c d : V}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    {x y z : Fin n}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hactive : retainedActive C b = {x,y,z})
    (haLoss : a ∈ projectedLossVertices C exponent)
    (hbLoss : b ∈ projectedLossVertices C exponent)
    (hcLoss : c ∈ projectedLossVertices C exponent)
    (hdLoss : d ∈ projectedLossVertices C exponent)
    (ha : WholeCubeQTPair C a b x)
    (hc : WholeCubeQTPair C c b y)
    (hd : WholeCubeQTPair C d b z)
    (hretAC : (C.color a c).val < n)
    (hstairAC : retainedColor C a c hretAC = y) :
    (∀ w : V, w ≠ a → a < w) ∧
    retainedBit C b x = true ∧
    retainedBit C b y = false ∧
    retainedBit C b z = false := by
  have hxB : x ∈ retainedActive C b := by
    rw [hactive]
    simp
  have hyB : y ∈ retainedActive C b := by
    rw [hactive]
    simp
  have hzB : z ∈ retainedActive C b := by
    rw [hactive]
    simp

  have hextreme :=
    threeWholeCubePartners_has_global_extreme
      C exponent hexp hone
      hxy hxz hyz
      hbLoss haLoss hcLoss hdLoss
      hactive ha hc hd

  have hminA : ∀ w : V, w ≠ a → a < w := by
    rcases hextreme with hbExt | haExt | hcExt | hdExt
    · rcases hbExt with hmin | hmax
      · have hba : b < a := hmin a (ne_of_lt hab)
        exact False.elim (lt_asymm hab hba)
      · have hcb : c < b := hmax c (ne_of_lt hbc).symm
        exact False.elim (lt_asymm hbc hcb)
    · rcases haExt with hmin | hmax
      · exact hmin
      · have hba : b < a := hmax b (ne_of_lt hab).symm
        exact False.elim (lt_asymm hab hba)
    · rcases hcExt with hmin | hmax
      · have hcb : c < b := hmin b (ne_of_lt hbc)
        exact False.elim (lt_asymm hbc hcb)
      · have hdc : d < c := hmax d (ne_of_lt hcd).symm
        exact False.elim (lt_asymm hcd hdc)
    · rcases hdExt with hmin | hmax
      · have hdc : d < c := hmin c (ne_of_lt hcd)
        exact False.elim (lt_asymm hcd hdc)
      · exact False.elim
          (source_second_staircase_impossible_of_max_right_partner
            C exponent
            hxy hxz hyz
            hxB hyB hzB
            ha hc hd
            hdLoss hmax
            (hab.trans hbc)
            hretAC hstairAC)

  have hstar :=
    threeWholeCubePartners_retainedCode_star
      C hxB hyB hzB ha hc hd

  have hxA : x ∈ retainedActive C a := by
    rw [hstar.1.1]
    exact hxB
  have hyA : y ∈ retainedActive C a := by
    rw [hstar.1.1]
    exact hyB
  have hzA : z ∈ retainedActive C a := by
    rw [hstar.1.1]
    exact hzB

  have haFalse :=
    projectedLoss_global_min_allFalse
      C exponent haLoss hminA

  have hxAFalse : retainedBit C a x = false :=
    haFalse x hxA
  have hyAFalse : retainedBit C a y = false :=
    haFalse y hyA
  have hzAFalse : retainedBit C a z = false :=
    haFalse z hzA

  have hxFlip :
      retainedBit C a x = !(retainedBit C b x) :=
    hstar.1.2.1
  have hySame :
      retainedBit C a y = retainedBit C b y :=
    hstar.1.2.2 y hyB hxy.symm
  have hzSame :
      retainedBit C a z = retainedBit C b z :=
    hstar.1.2.2 z hzB hxz.symm

  have hxBTrue : retainedBit C b x = true := by
    cases hx : retainedBit C b x <;> simp_all
  have hyBFalse : retainedBit C b y = false :=
    hySame.symm.trans hyAFalse
  have hzBFalse : retainedBit C b z = false :=
    hzSame.symm.trans hzAFalse

  exact ⟨hminA,hxBTrue,hyBFalse,hzBFalse⟩

theorem source_third_staircase_forces_right_max_and_110
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (hone :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {a b c d : V}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    {x y z : Fin n}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hactive : retainedActive C c = {x,y,z})
    (haLoss : a ∈ projectedLossVertices C exponent)
    (hbLoss : b ∈ projectedLossVertices C exponent)
    (hcLoss : c ∈ projectedLossVertices C exponent)
    (hdLoss : d ∈ projectedLossVertices C exponent)
    (ha : WholeCubeQTPair C a c x)
    (hb : WholeCubeQTPair C b c y)
    (hd : WholeCubeQTPair C d c z)
    (hretBD : (C.color b d).val < n)
    (hstairBD : retainedColor C b d hretBD = y) :
    (∀ w : V, w ≠ d → w < d) ∧
    retainedBit C c x = true ∧
    retainedBit C c y = true ∧
    retainedBit C c z = false := by
  have hxC : x ∈ retainedActive C c := by
    rw [hactive]
    simp
  have hyC : y ∈ retainedActive C c := by
    rw [hactive]
    simp
  have hzC : z ∈ retainedActive C c := by
    rw [hactive]
    simp

  have hextreme :=
    threeWholeCubePartners_has_global_extreme
      C exponent hexp hone
      hxy hxz hyz
      hcLoss haLoss hbLoss hdLoss
      hactive ha hb hd

  have hmaxD : ∀ w : V, w ≠ d → w < d := by
    rcases hextreme with hcExt | haExt | hbExt | hdExt
    · rcases hcExt with hmin | hmax
      · have hcb : c < b := hmin b (ne_of_lt hbc)
        exact False.elim (lt_asymm hbc hcb)
      · have hdc : d < c := hmax d (ne_of_lt hcd).symm
        exact False.elim (lt_asymm hcd hdc)
    · rcases haExt with hmin | hmax
      · exact False.elim
          (source_third_staircase_impossible_of_min_left_partner
            C exponent
            hxy hxz hyz
            hxC hyC hzC
            ha hb hd
            haLoss hmin
            (hbc.trans hcd)
            hretBD hstairBD)
      · have hba : b < a := hmax b (ne_of_lt hab).symm
        exact False.elim (lt_asymm hab hba)
    · rcases hbExt with hmin | hmax
      · have hba : b < a := hmin a (ne_of_lt hab)
        exact False.elim (lt_asymm hab hba)
      · have hcb : c < b := hmax c (ne_of_lt hbc).symm
        exact False.elim (lt_asymm hbc hcb)
    · rcases hdExt with hmin | hmax
      · have hdc : d < c := hmin c (ne_of_lt hcd)
        exact False.elim (lt_asymm hcd hdc)
      · exact hmax

  have hstar :=
    threeWholeCubePartners_retainedCode_star
      C hxC hyC hzC ha hb hd

  have hxD : x ∈ retainedActive C d := by
    rw [hstar.2.2.1]
    exact hxC
  have hyD : y ∈ retainedActive C d := by
    rw [hstar.2.2.1]
    exact hyC
  have hzD : z ∈ retainedActive C d := by
    rw [hstar.2.2.1]
    exact hzC

  have hdTrue :=
    projectedLoss_global_max_allTrue
      C exponent hdLoss hmaxD

  have hxDTrue : retainedBit C d x = true :=
    hdTrue x hxD
  have hyDTrue : retainedBit C d y = true :=
    hdTrue y hyD
  have hzDTrue : retainedBit C d z = true :=
    hdTrue z hzD

  have hxSame :
      retainedBit C d x = retainedBit C c x :=
    hstar.2.2.2.2 x hxC hxz
  have hySame :
      retainedBit C d y = retainedBit C c y :=
    hstar.2.2.2.2 y hyC hyz
  have hzFlip :
      retainedBit C d z = !(retainedBit C c z) :=
    hstar.2.2.2.1

  have hxCTrue : retainedBit C c x = true :=
    hxSame.symm.trans hxDTrue
  have hyCTrue : retainedBit C c y = true :=
    hySame.symm.trans hyDTrue
  have hzCFalse : retainedBit C c z = false := by
    cases hz : retainedBit C c z <;> simp_all

  exact ⟨hmaxD,hxCTrue,hyCTrue,hzCFalse⟩

#print axioms source_second_staircase_forces_left_min_and_100
#print axioms source_third_staircase_forces_right_max_and_110

end OrderedEdgeColoring
end JSP000404Research
