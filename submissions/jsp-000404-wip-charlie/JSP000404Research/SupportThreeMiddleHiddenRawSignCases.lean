import JSP000404Research.SaturatedTransitionSupport
import Mathlib.Tactic

/-!
# Raw canonical sign shapes for the five middle-hidden wrap positions

The top-pinned middle-hidden quotient cycle is

  [qFirst, 0, qHidden, 0, qLast],

with all three displayed positive quotients nonzero.

When the old canonical projective wrap is moved through the five possible
positions, the same cyclic quotient data appears in five canonical linear
forms.  If sign changes occur exactly on the positive positions, each form
forces one Boolean pattern on the raw canonical ray signs.

The results are stated relative to the sign at the top ray.  They are purely
finite Boolean lemmas and contain no geometric assumptions.
-/

namespace JSP000404Research

theorem middle_hidden_raw_sign_shape_wrap0
    (top r b c d : Bool)
    (qFirst qHidden qLast : ℕ)
    (hFirst : qFirst ≠ 0)
    (hHidden : qHidden ≠ 0)
    (hLast : qLast ≠ 0)
    (h :
      ChangesExactlyOnPositive
        r [b,c,d,top,!r]
        [0,qHidden,0,qLast,qFirst]) :
    r = top ∧ b = top ∧ c = !top ∧ d = !top := by
  cases top <;> cases r <;> cases b <;> cases c <;> cases d <;>
    simp_all [ChangesExactlyOnPositive]

theorem middle_hidden_raw_sign_shape_wrap1
    (top r b c d : Bool)
    (qFirst qHidden qLast : ℕ)
    (hFirst : qFirst ≠ 0)
    (hHidden : qHidden ≠ 0)
    (hLast : qLast ≠ 0)
    (h :
      ChangesExactlyOnPositive
        b [c,d,top,r,!b]
        [qHidden,0,qLast,qFirst,0]) :
    r = !top ∧ b = top ∧ c = !top ∧ d = !top := by
  cases top <;> cases r <;> cases b <;> cases c <;> cases d <;>
    simp_all [ChangesExactlyOnPositive]

theorem middle_hidden_raw_sign_shape_wrap2
    (top r b c d : Bool)
    (qFirst qHidden qLast : ℕ)
    (hFirst : qFirst ≠ 0)
    (hHidden : qHidden ≠ 0)
    (hLast : qLast ≠ 0)
    (h :
      ChangesExactlyOnPositive
        c [d,top,r,b,!c]
        [0,qLast,qFirst,0,qHidden]) :
    r = !top ∧ b = !top ∧ c = !top ∧ d = !top := by
  cases top <;> cases r <;> cases b <;> cases c <;> cases d <;>
    simp_all [ChangesExactlyOnPositive]

theorem middle_hidden_raw_sign_shape_wrap3
    (top r b c d : Bool)
    (qFirst qHidden qLast : ℕ)
    (hFirst : qFirst ≠ 0)
    (hHidden : qHidden ≠ 0)
    (hLast : qLast ≠ 0)
    (h :
      ChangesExactlyOnPositive
        d [top,r,b,c,!d]
        [qLast,qFirst,0,qHidden,0]) :
    r = !top ∧ b = !top ∧ c = top ∧ d = !top := by
  cases top <;> cases r <;> cases b <;> cases c <;> cases d <;>
    simp_all [ChangesExactlyOnPositive]

theorem middle_hidden_raw_sign_shape_wrap4
    (top r b c d : Bool)
    (qFirst qHidden qLast : ℕ)
    (hFirst : qFirst ≠ 0)
    (hHidden : qHidden ≠ 0)
    (hLast : qLast ≠ 0)
    (h :
      ChangesExactlyOnPositive
        top [r,b,c,d,!top]
        [qFirst,0,qHidden,0,qLast]) :
    r = !top ∧ b = !top ∧ c = top ∧ d = top := by
  cases top <;> cases r <;> cases b <;> cases c <;> cases d <;>
    simp_all [ChangesExactlyOnPositive]

#print axioms middle_hidden_raw_sign_shape_wrap0
#print axioms middle_hidden_raw_sign_shape_wrap1
#print axioms middle_hidden_raw_sign_shape_wrap2
#print axioms middle_hidden_raw_sign_shape_wrap3
#print axioms middle_hidden_raw_sign_shape_wrap4

end JSP000404Research
