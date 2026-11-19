module
prelude
public import RawGrowthCacheCertificate
public import RawBoundaryMatch

@[expose] public section

/-! Exact finite-family comparison by a natural-number bitset. The theorem
holds for arbitrary lists, including repeated masks and unbounded masks. -/

namespace Papers.RationalityTen.BitsetFamilyCheck

open RawNatGrowthCheck RawGrowthCacheCertificate RawBoundaryMatch

theorem sameSetCheck_iff (A B : List Nat) :
    sameSetCheck A B = true ↔ ∀ x, x ∈ A ↔ x ∈ B := by
  constructor
  · exact sameSetCheck_sound A B
  · intro h
    apply Bool.and_eq_true_iff.mpr
    constructor
    · exact List.all_eq_true.mpr fun x hx => decide_eq_true ((h x).mp hx)
    · exact List.all_eq_true.mpr fun x hx => decide_eq_true ((h x).mpr hx)

theorem mask_eq_iff (A B : List Nat) :
    mask A = mask B ↔ ∀ x, x ∈ A ↔ x ∈ B := by
  constructor
  · intro h x
    have hbit := congrArg (fun m => m.testBit x) h
    rw [mask_bit, mask_bit] at hbit
    rw [← hasNat_true A x, ← hasNat_true B x, hbit]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro x
    rw [mask_bit, mask_bit]
    apply Bool.eq_iff_iff.mpr
    rw [hasNat_true, hasNat_true]
    exact h x

def check (A B : List Nat) : Bool := decide (mask A = mask B)

theorem check_eq (A B : List Nat) : check A B = sameSetCheck A B := by
  apply Bool.eq_iff_iff.mpr
  rw [check, decide_eq_true_eq, mask_eq_iff, sameSetCheck_iff]

#print axioms check_eq

end Papers.RationalityTen.BitsetFamilyCheck
