module

public import PaperVerification.AlternatingFormsOddExteriorBasis

/-!
# The printed one-based inequalities in every exterior degree

The formal basis uses zero-based finite indices and moves the upper
inequality across subtraction.  This lemma proves its equivalence to the
printed inequalities over the integers.  In particular, no truncated natural
subtraction can create extra good indices above the middle degree.
-/

@[expose] public section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

theorem goodOddIndex_printed_inequalities (k s : ℕ)
    (I : PluckerIndex s (2*k+1)) :
    (∀ i,2*i.val≤(I.val i).val ∧
      (I.val i).val+2*s≤2*k+2+2*i.val) ↔
    (∀ i : Fin s,
      2*((i.val : ℤ)+1)-1≤((I.val i).val : ℤ)+1 ∧
      ((I.val i).val : ℤ)+1≤
        (2*(k : ℤ)+1)-2*(s : ℤ)+2*((i.val : ℤ)+1)) := by
  constructor
  · intro h i
    have hi := h i
    constructor <;> omega
  · intro h i
    have hi := h i
    constructor <;> omega

theorem goodOddIndex_printed_bounds (k s : ℕ) (I : GoodOddIndex k s) :
    ∀ i : Fin s,
      2*((i.val : ℤ)+1)-1≤((I.val.val i).val : ℤ)+1 ∧
      ((I.val.val i).val : ℤ)+1≤
        (2*(k : ℤ)+1)-2*(s : ℤ)+2*((i.val : ℤ)+1) :=
  (goodOddIndex_printed_inequalities k s I.val).mp I.property

end PaperVerification.AlternatingForms
