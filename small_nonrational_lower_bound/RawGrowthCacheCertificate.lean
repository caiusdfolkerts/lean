module
prelude
public import RawNatGrowthSoundness

@[expose] public section

/-!
# Cache laws checked directly on natural-number rows

The sparse row certificates are ordinary lists of natural numbers.  The proof
below relates those lists to the exact finite cell universe.  Only the ridge
labels stored in a cell need a range check; extra high bits in a cache row do
not describe any cell in `Fin n` and cannot remove a genuine target cell.
-/

namespace Papers.RationalityTen.RawGrowthCacheCertificate

open GrowthDAG SparseGrowthDAG GrowthBitsets ConcreteGrowth BatchedGrowthPruning
open RawNatGrowthSoundness

variable {n r : Nat}

def hasNat (xs : List Nat) (a : Nat) : Bool := xs.any (fun x => decide (x = a))

theorem hasNat_true (xs : List Nat) (a : Nat) : hasNat xs a = true ↔ a ∈ xs := by
  simp only [hasNat, List.any_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨x, hx, hxa⟩ => hxa ▸ hx, fun ha => ⟨a, ha, rfl⟩⟩

theorem mask_bit (xs : List Nat) (a : Nat) :
    (RawNatGrowthCheck.mask xs).testBit a = hasNat xs a := by
  induction xs with
  | nil => simp only [RawNatGrowthCheck.mask, RawNatGrowthCheck.union,
      Nat.zero_testBit, hasNat, List.any_nil]
  | cons x xs ih =>
      change (Nat.lor (Nat.shiftLeft 1 x) (RawNatGrowthCheck.mask xs)).testBit a = _
      have hs : (Nat.shiftLeft 1 x).testBit a = decide (x = a) := by
        change (PrimitiveBitsetGrowth.singleton x).testBit a = _
        rw [PrimitiveBitsetGrowth.singleton_eq, Nat.testBit_two_pow]
      have hor : (Nat.lor (Nat.shiftLeft 1 x) (RawNatGrowthCheck.mask xs)).testBit a =
          ((Nat.shiftLeft 1 x).testBit a || (RawNatGrowthCheck.mask xs).testBit a) :=
        Nat.testBit_or _ _ _
      rw [hor, hs, ih]
      rfl

theorem has_decoded [NeZero r] (xs : List Nat) (hbound : listBounds r xs = true)
    (q : Fin r) : has (xs.map (Fin.ofNat r)) q = hasNat xs q.val := by
  apply Bool.eq_iff_iff.mpr
  rw [has_true, hasNat_true]
  constructor
  · intro h
    obtain ⟨x, hx, heq⟩ := List.mem_map.mp h
    have hlt := of_decide_eq_true (List.all_eq_true.mp hbound x hx)
    have hv := congrArg Fin.val heq
    rw [Fin.val_ofNat, Nat.mod_eq_of_lt hlt] at hv
    exact hv ▸ hx
  · intro h
    exact List.mem_map.mpr ⟨q.val, h, Fin.ofNat_val_eq_self q⟩

/-- All incidence and exclusion properties are derived from finite executable
row checks. No compatibility matrix or complete-search assertion is assumed. -/
noncomputable def ofChecks
    (cells : Nat → Cell)
    (candidates bad kinds : Nat → Nat)
    (candidateRows badRows kindRows : Nat → List Nat)
    (keys : List Nat)
    (hridgeBounds : ∀ c : Fin n, listBounds 1024 (cells c.val).ridgeMasks = true)
    (hcandidateMasks : ∀ q : Fin 1024,
      candidates q.val = RawNatGrowthCheck.mask (candidateRows q.val))
    (hcandidateCoverage : ∀ c : Fin n,
      (cells c.val).ridgeMasks.all (fun q => hasNat (candidateRows q) c.val) = true)
    (hcandidateSound : ∀ q : Fin 1024,
      (candidateRows q.val).all (fun c => hasNat (cells c).ridgeMasks q.val) = true)
    (hbadMasks : ∀ c : Fin n, bad c.val = RawNatGrowthCheck.mask (badRows c.val))
    (hbadSound : ∀ a : Fin n,
      (badRows a.val).all (fun c => !(compatible (cells a.val) (cells c))) = true)
    (hkindMasks : ∀ j, j ∈ keys → kinds j = RawNatGrowthCheck.mask (kindRows j))
    (hkindSound : ∀ j, j ∈ keys →
      (kindRows j).all (fun c => decide ((cells c).kind = j)) = true) :
    Cache (ConcreteGrowth.ridgeList (fun c : Fin n => cells c.val))
      (fun a b : Fin n => compatible (cells a.val) (cells b.val))
      (fun c : Fin n => (cells c.val).kind) where
  candidates q := candidates q.val
  incompatible c := bad c.val
  kinds := kinds
  keys := keys
  candidates_exact := by
    intro q c
    rw [bitAt_eq_testBit, hcandidateMasks q, mask_bit]
    rw [ConcreteGrowth.ridgeList, has_decoded _ (hridgeBounds c)]
    apply Bool.eq_iff_iff.mpr
    rw [hasNat_true, hasNat_true]
    constructor
    · intro h
      exact (hasNat_true _ _).mp (List.all_eq_true.mp (hcandidateSound q) c.val h)
    · intro h
      exact (hasNat_true _ _).mp (List.all_eq_true.mp (hcandidateCoverage c) q.val h)
  incompatible_sound := by
    intro a c h
    rw [bitAt_eq_testBit, hbadMasks a, mask_bit, hasNat_true] at h
    have hh := List.all_eq_true.mp (hbadSound a) c.val h
    cases hbc : compatible (cells a.val) (cells c.val) with
    | false => rfl
    | true =>
        have hfalse : false = true := by simpa only [hbc, Bool.not_true] using hh
        exact False.elim (Bool.noConfusion hfalse)
  kind_sound := by
    intro j hj c h
    rw [bitAt_eq_testBit, hkindMasks j hj, mask_bit, hasNat_true] at h
    exact of_decide_eq_true (List.all_eq_true.mp (hkindSound j hj) c.val h)

#print axioms ofChecks

end Papers.RationalityTen.RawGrowthCacheCertificate
