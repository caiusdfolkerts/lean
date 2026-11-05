import bier.hadamard
import bier.encoding
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Lex
import Mathlib.Order.Prod.Lex.Basic

/-! # The specified integer and lexicographic orders in the explicit examples -/

noncomputable section

namespace Bier

open scoped BigOperators

/-- The usual little-endian binary integer of a finite bit vector. -/
def binaryValue {n : ℕ} (x : Fin n → Fin 2) : ℕ :=
  Nat.ofDigits 2 (List.ofFn (fun i => (x i).val))

theorem binaryValue_injective (n : ℕ) :
    Function.Injective (binaryValue : (Fin n → Fin 2) → ℕ) := by
  intro x y h
  have hl : List.ofFn (fun i => (x i).val) = List.ofFn (fun i => (y i).val) := by
    apply Nat.ofDigits_inj_of_len_eq (by norm_num) ?_ ?_ ?_ h
    · simp
    · intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact (x i).isLt
    · intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact (y i).isLt
  have hf := List.ofFn_injective hl
  funext i
  exact Fin.ext (congrFun hf i)

structure ExplicitLabel where
  first : Fin 12
  second : Fin 12
  bits : Fin 10 → Fin 2
  deriving DecidableEq, Fintype

def explicitLabelEquiv : ExplicitLabel ≃ ExplicitIndex where
  toFun x := ((x.first, x.second), x.bits)
  invFun x := ⟨x.1.1, x.1.2, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def explicitLabelKey (x : ExplicitLabel) : Lex (Fin 12 × Lex (Fin 12 × ℕ)) :=
  toLex (x.first, toLex (x.second, binaryValue x.bits))

theorem explicitLabelKey_injective : Function.Injective explicitLabelKey := by
  intro x y h
  have h1 := congrArg (fun z => (ofLex z).1) h
  have h2 := congrArg (fun z => (ofLex (ofLex z).2).1) h
  have h3 := congrArg (fun z => (ofLex (ofLex z).2).2) h
  have hb := binaryValue_injective 10 h3
  cases x
  cases y
  simp only [explicitLabelKey, ofLex_toLex] at h1 h2
  cases h1
  cases h2
  cases hb
  rfl

instance : LinearOrder ExplicitLabel :=
  LinearOrder.lift' explicitLabelKey explicitLabelKey_injective

theorem explicitLabel_card : Fintype.card ExplicitLabel = 147456 :=
  (Fintype.card_congr explicitLabelEquiv).trans explicitIndex_card

/-- Increasing enumeration by the exact Paley, Paley, binary-integer order. -/
def explicitEnumeration : Fin 147456 ≃o ExplicitLabel :=
  Fintype.orderIsoFinOfCardEq ExplicitLabel explicitLabel_card

def explicitRowEquiv : Fin 147456 ≃ ExplicitIndex :=
  explicitEnumeration.toEquiv.trans explicitLabelEquiv

def orderedHadamard : Matrix (Fin 147456) (Fin 147456) ℝ :=
  explicitHadamard.submatrix explicitRowEquiv explicitRowEquiv

theorem orderedHadamard_hadamard : orderedHadamard.IsHadamard := by
  exact (Matrix.isHadamard_submatrix_equiv_iff explicitRowEquiv explicitRowEquiv).mpr
    explicitHadamard_hadamard

/-- Exactly the first `381²+1` columns in the specified order. -/
def principalSigns : Matrix (Fin 147456) (Fin 145162) ℝ :=
  orderedHadamard.submatrix id (Fin.castLE (by norm_num : 145162 ≤ 147456))

theorem principalSigns_sign : IsSignMatrix principalSigns := by
  intro r c
  exact explicitHadamard_sign _ _

theorem principalSigns_positive : ∃ r c, principalSigns r c = 1 := by
  let z : ExplicitIndex := ((0, 0), fun _ => 0)
  refine ⟨explicitRowEquiv.symm z, 0, ?_⟩
  simp only [principalSigns, orderedHadamard, Matrix.submatrix_apply, id_eq,
    Equiv.apply_symm_apply]
  change explicitHadamard z _ = 1
  simp [z, explicitHadamard, Matrix.kroneckerMap_apply, paley, paleyInt,
    walsh, bitSign]

/-- A k-subset is ordered by its increasing list, hence by ordinary lexicographic order. -/
def KSubset (m k : ℕ) := {A : Finset (Fin m) // A.card = k}

instance (m k : ℕ) : Fintype (KSubset m k) :=
  inferInstanceAs (Fintype {A : Finset (Fin m) // A.card = k})

instance (m k : ℕ) : DecidableEq (KSubset m k) :=
  inferInstanceAs (DecidableEq {A : Finset (Fin m) // A.card = k})

def subsetLexKey {m k : ℕ} (A : KSubset m k) : List (Fin m) := A.val.sort

theorem subsetLexKey_injective (m k : ℕ) :
    Function.Injective (subsetLexKey : KSubset m k → List (Fin m)) := by
  intro A B h
  apply Subtype.ext
  simpa only [subsetLexKey, Finset.sort_toFinset] using congrArg List.toFinset h

instance subsetLexOrder (m k : ℕ) : LinearOrder (KSubset m k) :=
  LinearOrder.lift' subsetLexKey (subsetLexKey_injective m k)

theorem kSubset_card (m k : ℕ) : Fintype.card (KSubset m k) = m.choose k := by
  let e : KSubset m k ≃ {A : Finset (Fin m) // A.card = k} := Equiv.refl _
  exact (Fintype.card_congr e).trans (by
    simpa only [Fintype.card_fin] using Fintype.card_finset_len (α := Fin m) k)

/-- The first r k-subsets, in the increasing-list lexicographic order. -/
def firstSubsets (m k r : ℕ) (h : r ≤ m.choose k) (i : Fin r) : Finset (Fin m) :=
  (Fintype.orderIsoFinOfCardEq (KSubset m k) (kSubset_card m k)
    (Fin.castLE h i)).val

theorem firstSubsets_card (m k r : ℕ) (h : r ≤ m.choose k) (i : Fin r) :
    (firstSubsets m k r h i).card = k :=
  (Fintype.orderIsoFinOfCardEq (KSubset m k) (kSubset_card m k)
    (Fin.castLE h i)).property

theorem firstSubsets_injective (m k r : ℕ) (h : r ≤ m.choose k) :
    Function.Injective (firstSubsets m k r h) := by
  intro i j hij
  have hs : Fintype.orderIsoFinOfCardEq (KSubset m k) (kSubset_card m k) (Fin.castLE h i) =
      Fintype.orderIsoFinOfCardEq (KSubset m k) (kSubset_card m k) (Fin.castLE h j) :=
    Subtype.ext hij
  have he := (Fintype.orderIsoFinOfCardEq (KSubset m k) (kSubset_card m k)).injective hs
  exact Fin.ext (congrArg (fun z : Fin (m.choose k) => z.val) he)

theorem enough_nine_subsets : 147456 ≤ Nat.choose 20 9 := by decide

def principalRows : Fin 147456 → Finset (Fin 20) :=
  firstSubsets 20 9 147456 enough_nine_subsets

theorem principalRows_card (r : Fin 147456) : (principalRows r).card = 9 :=
  firstSubsets_card _ _ _ _ _

theorem principalRows_injective : Function.Injective principalRows :=
  firstSubsets_injective _ _ _ _

def principalCore : Complex (Fin 20 ⊕ Fin 145162) :=
  signComplex 9 principalRows principalRows_card principalSigns

def principalInput : Complex (Option (Fin 20 ⊕ Fin 145162)) := principalCore.ghost

theorem principalCore_proper : principalCore.Proper :=
  signComplex_proper 9 (by norm_num) principalRows principalRows_card principalSigns

theorem principalCore_vertices : principalCore.vertices = Finset.univ :=
  signComplex_all_vertices 9 (by norm_num) principalRows principalRows_card principalSigns

theorem principalCore_dimension : principalCore.dimension = 9 :=
  signComplex_dimension 9 principalRows principalRows_card principalSigns principalSigns_positive

end Bier
