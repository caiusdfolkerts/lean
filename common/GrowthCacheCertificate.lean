module
prelude
public import BatchedGrowthPruning

@[expose] public section

/-!
# Sparse certificates for the bitset cache

Each bitset has an explicit finite support. The candidate rows are checked in
both directions against literal ridge membership; incompatibility and kind rows
need only the direction used to justify an exclusion. No complete compatibility
matrix is assumed or trusted.
-/

namespace Papers.RationalityTen.GrowthCacheCertificate

open GrowthDAG SparseGrowthDAG GrowthPruning ConcreteGrowth GrowthBitsets
open BatchedGrowthPruning

variable {n r : Nat}

theorem candidate_exact
    (ridgeList : Fin n → List (Fin r))
    (candidates : Fin r → List (Fin n)) (candidateMasks : Fin r → Nat)
    (hmasks : ∀ q, candidateMasks q = ofList (candidates q))
    (hcoverage : ∀ c, (ridgeList c).all (fun q => has (candidates q) c) = true)
    (hsound : ∀ q, (candidates q).all (fun c => has (ridgeList c) q) = true)
    (q : Fin r) (c : Fin n) :
    bitAt (candidateMasks q) c.val = has (ridgeList c) q := by
  rw [hmasks, bitAt_ofList_eq_has]
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    exact List.all_eq_true.mp (hsound q) c ((has_true _ _).mp h)
  · intro h
    exact List.all_eq_true.mp (hcoverage c) q ((has_true _ _).mp h)

theorem incompatible_sound
    (compatible testCompatible : Fin n → Fin n → Bool)
    (necessary : ∀ a c, compatible a c = true → testCompatible a c = true)
    (support : Fin n → List (Fin n)) (masks : Fin n → Nat)
    (hmasks : ∀ a, masks a = ofList (support a))
    (hsound : ∀ a, (support a).all (fun c => !(testCompatible a c)) = true)
    (a c : Fin n) (hbit : bitAt (masks a) c.val = true) :
    compatible a c = false := by
  rw [hmasks, bitAt_ofList] at hbit
  have hnot := List.all_eq_true.mp (hsound a) c hbit
  have hfalse : testCompatible a c = false := by
    cases hvalue : testCompatible a c with
    | false => rfl
    | true =>
      simp only [hvalue, Bool.not_true] at hnot
      exact False.elim (Bool.noConfusion hnot)
  cases hgood : compatible a c with
  | false => rfl
  | true => exact False.elim (Bool.noConfusion (hfalse.symm.trans (necessary a c hgood)))

theorem kind_sound
    (kind : Fin n → Nat) (support : Nat → List (Fin n)) (masks : Nat → Nat)
    (keys : List Nat)
    (hmasks : ∀ k, k ∈ keys → masks k = ofList (support k))
    (hsound : ∀ k, k ∈ keys → (support k).all (fun c => decide (kind c = k)) = true)
    (k : Nat) (hk : k ∈ keys) (c : Fin n) (hbit : bitAt (masks k) c.val = true) :
    kind c = k := by
  rw [hmasks k hk, bitAt_ofList] at hbit
  exact of_decide_eq_true (List.all_eq_true.mp (hsound k hk) c hbit)

def ofChecks
    (ridgeList : Fin n → List (Fin r))
    (compatible testCompatible : Fin n → Fin n → Bool) (kind : Fin n → Nat)
    (necessary : ∀ a c, compatible a c = true → testCompatible a c = true)
    (candidateLists : Fin r → List (Fin n)) (candidateMasks : Fin r → Nat)
    (incompatibleLists : Fin n → List (Fin n)) (incompatibleMasks : Fin n → Nat)
    (kindLists : Nat → List (Fin n)) (kindMasks : Nat → Nat) (keys : List Nat)
    (hcandidateMasks : ∀ q, candidateMasks q = ofList (candidateLists q))
    (hcoverage : ∀ c, (ridgeList c).all (fun q => has (candidateLists q) c) = true)
    (hcandidateSound : ∀ q, (candidateLists q).all (fun c => has (ridgeList c) q) = true)
    (hincompatibleMasks : ∀ a, incompatibleMasks a = ofList (incompatibleLists a))
    (hincompatibleSound : ∀ a,
      (incompatibleLists a).all (fun c => !(testCompatible a c)) = true)
    (hkindMasks : ∀ k, k ∈ keys → kindMasks k = ofList (kindLists k))
    (hkindSound : ∀ k, k ∈ keys → (kindLists k).all (fun c => decide (kind c = k)) = true) :
    Cache ridgeList compatible kind where
  candidates := candidateMasks
  incompatible := incompatibleMasks
  kinds := kindMasks
  keys := keys
  candidates_exact := candidate_exact ridgeList candidateLists candidateMasks
    hcandidateMasks hcoverage hcandidateSound
  incompatible_sound := incompatible_sound compatible testCompatible necessary
    incompatibleLists incompatibleMasks hincompatibleMasks hincompatibleSound
  kind_sound := kind_sound kind kindLists kindMasks keys hkindMasks hkindSound

#print axioms ofChecks

end Papers.RationalityTen.GrowthCacheCertificate
