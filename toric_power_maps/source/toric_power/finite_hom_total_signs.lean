module

public import ToricPower.LinearHomToSingleCoefficients

@[expose] public section

namespace ToricPower

def finiteHomTotalSign (p : ℕ) (a : ℤ) : ℤˣ :=
  homDualSign p * ((p : ℤ)*a).negOnePow

theorem finiteHomTotalSign_vertical (p : ℕ) (a : ℤ) :
    finiteHomTotalSign p (a+1) * (p : ℤ).negOnePow = finiteHomTotalSign p a := by
  simp only [finiteHomTotalSign,mul_add,mul_one,Int.negOnePow_add,mul_assoc,
    Int.units_mul_self,mul_one]

theorem finiteHomTotalSign_horizontal (p : ℕ) (a : ℤ) :
    finiteHomTotalSign (p+1) a * (a+1).negOnePow = finiteHomTotalSign p (a+1) := by
  simp only [finiteHomTotalSign,homDualSign,Nat.cast_add,Nat.cast_one,
    add_mul,mul_add,one_mul,mul_one,Int.negOnePow_add,Int.negOnePow_one]
  have rearrange :
      (((p : ℤ).negOnePow * (-1)) * homDualSign p *
        (((p : ℤ)*a).negOnePow * a.negOnePow)) * (a.negOnePow * (-1)) =
      homDualSign p * (((p : ℤ)*a).negOnePow * (p : ℤ).negOnePow) *
        (a.negOnePow * a.negOnePow) * ((-1 : ℤˣ) * (-1)) := by
    ac_rfl
  rw [rearrange,Int.units_mul_self,Int.units_mul_self,mul_one,mul_one]

end ToricPower

end

