module
public import MatroidChecked.FastSemanticChecks

@[expose] public section
noncomputable section

/-!
# Exact bit-set comparison for basis-family relabelings

A natural number records the set of masks occurring in a finite list.
The equivalence below holds for arbitrary lists and arbitrary natural masks;
it needs neither a size bound nor a no-duplicates premise. The catalogue
witness statements and their finite input data are unchanged.
-/

namespace Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks

open BasisReconstruction BasisCertificates BasisExtensionCNF FastSemanticChecks

def familyCode (L : List ℕ) : ℕ :=
  L.foldr (fun mask code => (2 ^ mask) ||| code) 0

theorem familyCode_testBit (L : List ℕ) (i : ℕ) :
    (familyCode L).testBit i = true ↔ i ∈ L := by
  induction L with
  | nil => simp [familyCode]
  | cons a L ih =>
      simp only [familyCode, List.foldr_cons, Nat.testBit_or, Bool.or_eq_true,
        Nat.testBit_two_pow, decide_eq_true_eq, List.mem_cons]
      simpa only [familyCode] using or_congr (eq_comm (a := a) (b := i)) ih

theorem familyCode_eq_iff (L M : List ℕ) :
    familyCode L = familyCode M ↔ L.toFinset = M.toFinset := by
  constructor
  · intro h
    ext i
    simp only [List.mem_toFinset, ← familyCode_testBit, h]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    apply Bool.eq_iff_iff.mpr
    change (familyCode L).testBit i = true ↔ (familyCode M).testBit i = true
    rw [familyCode_testBit, familyCode_testBit]
    have hm : i ∈ L.toFinset ↔ i ∈ M.toFinset := by rw [h]
    simpa only [List.mem_toFinset] using hm

def BitsetRawWitness {k t : ℕ} (n : ℕ) (old : List ℕ) (grid : Fin k → ℕ)
    (newIndex : Fin t → Fin k) (model : ℕ) (target : List ℕ) (permutation : ℕ) : Prop :=
  ValidPermutation n permutation ∧
    familyCode ((extensionMasks old grid newIndex model).map (permutedMask permutation)) =
      familyCode target

instance {k t : ℕ} (n : ℕ) (old : List ℕ) (grid : Fin k → ℕ)
    (newIndex : Fin t → Fin k) (model : ℕ) (target : List ℕ) (permutation : ℕ) :
    Decidable (BitsetRawWitness n old grid newIndex model target permutation) := by
  unfold BitsetRawWitness
  infer_instance

theorem bitsetRawWitness_iff {k t : ℕ} (n : ℕ) (old : List ℕ) (grid : Fin k → ℕ)
    (newIndex : Fin t → Fin k) (model : ℕ) (target : List ℕ) (permutation : ℕ) :
    BitsetRawWitness n old grid newIndex model target permutation ↔
      RawWitness n old grid newIndex model target permutation := by
  simp only [BitsetRawWitness, RawWitness, familyCode_eq_iff]

theorem bitsetRawWitness_sound {k t : ℕ} (n : ℕ) (old : List ℕ) (grid : Fin k → ℕ)
    (newIndex : Fin t → Fin k) (model : ℕ) (target : List ℕ) (permutation : ℕ)
    (h : BitsetRawWitness n old grid newIndex model target permutation) :
    ValidWitness n
      (extensionFamily (familyOfMasks old) (fun i => maskPoints (grid i)) newIndex model)
      (familyOfMasks target) permutation :=
  rawWitness_sound n old grid newIndex model target permutation
    ((bitsetRawWitness_iff n old grid newIndex model target permutation).mp h)

end Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks
