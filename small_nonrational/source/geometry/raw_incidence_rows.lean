module
prelude
public import RawGrowthCacheCertificate
public import IntersectionIncompatibilityRows

@[expose] public section

/-!
# Exact sparse incidence transposes

An incidence table is checked by its listed incidences in both directions.
This avoids checking every pair of a cell and an absent feature. The separate
vertex-row construction recognizes containment of any mask from the ten
individual vertex rows, without another quadratic certificate.
-/

namespace Papers.RationalityTen.RawIncidenceRows

open ConcreteGrowth GrowthBitsets FiniteMaskSets RawNatGrowthSoundness
open RawGrowthCacheCertificate IntersectionIncompatibilityRows

variable {n v bound : Nat}

def boundedRow (rows : Nat → Nat) (bound q : Nat) : Nat :=
  if q < bound then rows q else 0

theorem boundedRow_exact (sets : Nat → List Nat)
    (rows : Nat → Nat) (supports : Nat → List Nat)
    (hrange : ∀ c : Fin n, listBounds bound (sets c.val) = true)
    (hmasks : ∀ q : Fin bound, rows q.val = RawNatGrowthCheck.mask (supports q.val))
    (hcover : ∀ c : Fin n,
      (sets c.val).all (fun q => hasNat (supports q) c.val) = true)
    (hsound : ∀ q : Fin bound,
      (supports q.val).all (fun c => hasNat (sets c) q.val) = true)
    (q : Nat) (c : Fin n) :
    (boundedRow rows bound q).testBit c.val = hasNat (sets c.val) q := by
  by_cases hq : q < bound
  · rw [boundedRow, ite_eq_left hq, hmasks ⟨q,hq⟩, mask_bit]
    apply Bool.eq_iff_iff.mpr
    rw [hasNat_true, hasNat_true]
    constructor
    · intro h
      exact (hasNat_true _ _).mp (List.all_eq_true.mp (hsound ⟨q,hq⟩) c.val h)
    · intro h
      exact (hasNat_true _ _).mp (List.all_eq_true.mp (hcover c) q h)
  · rw [boundedRow, ite_eq_right hq, Nat.zero_testBit]
    symm
    apply Bool.eq_false_of_ne_true
    intro h
    exact hq (of_decide_eq_true (List.all_eq_true.mp (hrange c) q
      ((hasNat_true _ _).mp h)))

/-- All cells containing every vertex of the given mask. A mask beyond the
declared vertex range cannot be contained in a bounded cell. -/
def containsRow (vertexRows : Fin v → Nat) (mask : Nat) : Nat :=
  if mask < 2 ^ v then
    meetRows n (fun j : Fin v => if mask.testBit j.val then vertexRows j else allMask n)
      (List.finRange v)
  else 0

theorem containsRow_exact (vertices : Fin n → Nat) (vertexRows : Fin v → Nat)
    (hvertices : ∀ c, vertices c < 2 ^ v)
    (hrows : ∀ j c, (vertexRows j).testBit c.val = (vertices c).testBit j.val)
    (mask : Nat) (c : Fin n) :
    (containsRow (n := n) vertexRows mask).testBit c.val =
      decide (Nat.land mask (vertices c) = mask) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  by_cases hm : mask < 2 ^ v
  · simp only [containsRow, hm, ite_true, meetRows_bit, List.mem_finRange, true_implies]
    constructor
    · intro h
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j < v
      · cases hb : mask.testBit j with
        | false => simp only [testBit_land, hb, Bool.false_and]
        | true =>
          have hc := h ⟨j,hj⟩
          have hcv : (vertices c).testBit j = true := by
            simpa only [hb, ite_true, hrows] using hc
          simp only [testBit_land, hb, hcv, Bool.and_self]
      · have hpow : 2 ^ v ≤ 2 ^ j :=
          Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hj)
        have hbit : mask.testBit j = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm hpow)
        simp only [testBit_land, hbit, Bool.false_and]
    · intro h j
      cases hb : mask.testBit j.val with
      | false => exact allMask_bit c
      | true =>
        have hc := congrArg (fun x => x.testBit j.val) h
        have hcv : (vertices c).testBit j.val = true := by
          simpa only [testBit_land, hb, Bool.true_and] using hc
        change (vertexRows j).testBit c.val = true
        rw [hrows]
        exact hcv
  · rw [containsRow, ite_eq_right hm, Nat.zero_testBit]
    constructor
    · intro h
      exact False.elim (Bool.noConfusion h)
    · intro h
      have hle : mask ≤ vertices c := by
        rw [← h]
        exact Nat.and_le_right
      exact False.elim (hm (Nat.lt_of_le_of_lt hle (hvertices c)))

#print axioms boundedRow_exact
#print axioms containsRow_exact

end Papers.RationalityTen.RawIncidenceRows
