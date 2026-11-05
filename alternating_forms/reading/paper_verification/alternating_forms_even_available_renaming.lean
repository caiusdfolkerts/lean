module

public import PaperVerification.AlternatingFormsEvenDegreeBlocks
public import PaperVerification.AlternatingFormsBooleanRenaming
public import PaperVerification.AlternatingFormsBooleanGoodSubsets

/-!
# Increasing coordinates on the unoccupied pairs

The block variables are the actual complement of the singleton positions.
They are enumerated in their inherited order.  This file records both the
ordinary quotient equivalence under that enumeration and the injective
pullback of a polynomial genericity condition to the original parameters.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.EvenSingletons

open scoped BigOperators Classical

variable {K ι : Type*} [Field K] [LinearOrder ι] [Fintype ι]

theorem singletonDegree_le (S : SingletonState ι) : singletonDegree S ≤ Fintype.card ι := by
  rw [singletonDegree, ← Finset.card_union_of_disjoint S.property]
  exact Finset.card_le_univ _

theorem card_available (S : SingletonState ι) :
    Fintype.card (Available S) = Fintype.card ι - singletonDegree S := by
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_coe, Finset.card_union_of_disjoint S.property, singletonDegree]

theorem card_available_add_singletonDegree (S : SingletonState ι) :
    Fintype.card (Available S) + singletonDegree S = Fintype.card ι := by
  rw [card_available, Nat.sub_add_cancel (singletonDegree_le S)]

/-- The order-preserving enumeration, rather than an arbitrary finite equivalence. -/
def availableOrderEquiv (S : SingletonState ι) :
    Fin (Fintype.card (Available S)) ≃o Available S :=
  Fintype.orderIsoFinOfCardEq (Available S) rfl

def availableEmbedding (S : SingletonState ι) :
    Fin (Fintype.card (Available S)) ↪ ι :=
  (availableOrderEquiv S).toEquiv.toEmbedding.trans (Function.Embedding.subtype _)

theorem availableEmbedding_strictMono (S : SingletonState ι) :
    StrictMono (availableEmbedding S) :=
  (fun _ _ h => (availableOrderEquiv S).strictMono h)

def availablePieceEquiv (S : SingletonState ι) (b c : ι → K) (q : ℕ) :
    BooleanQuotient.piece (fun i : Available S => b i.val)
      (fun i : Available S => c i.val) q ≃ₗ[K]
        BooleanQuotient.piece (fun i => b (availableEmbedding S i))
          (fun i => c (availableEmbedding S i)) q :=
  BooleanQuotient.pieceRenameEquiv (availableOrderEquiv S).symm.toEquiv _ _ q

theorem finrank_availablePiece (S : SingletonState ι) (b c : ι → K) (q : ℕ) :
    Module.finrank K (BooleanQuotient.piece (fun i : Available S => b i.val)
      (fun i : Available S => c i.val) q) =
        Module.finrank K (BooleanQuotient.piece (fun i => b (availableEmbedding S i))
          (fun i => c (availableEmbedding S i)) q) :=
  (availablePieceEquiv S b c q).finrank_eq

def blockParameterPullback (S : SingletonState ι) :
    MvPolynomial (Bool × Fin (Fintype.card (Available S))) K →ₐ[K]
      MvPolynomial (Bool × ι) K :=
  MvPolynomial.rename (BooleanQuotient.pairVariableEmbedding (availableEmbedding S))

theorem blockParameterPullback_ne_zero (S : SingletonState ι)
    {p : MvPolynomial (Bool × Fin (Fintype.card (Available S))) K} (hp : p ≠ 0) :
    blockParameterPullback S p ≠ 0 :=
  BooleanQuotient.pairParameterRename_ne_zero (availableEmbedding S) hp

theorem blockParameterPullback_evaluate (S : SingletonState ι) (b c : ι → K)
    (p : MvPolynomial (Bool × Fin (Fintype.card (Available S))) K) :
    BooleanQuotient.pairParameterEvaluation b c (blockParameterPullback S p) =
      BooleanQuotient.pairParameterEvaluation
        (fun i => b (availableEmbedding S i)) (fun i => c (availableEmbedding S i)) p :=
  BooleanQuotient.pairParameterEvaluation_rename (availableEmbedding S) b c p

/-- The exact good-index set attached to an exterior degree block. -/
abbrev BlockGoodSubsets {s : ℕ} (J : DegreeBlock ι s) :=
  BooleanWalks.GoodSubset (Fintype.card (Available J.val.1)) J.val.2.val

theorem block_good_degree_le {s : ℕ} (J : DegreeBlock ι s) (P : BlockGoodSubsets J) :
    s ≤ Fintype.card ι := by
  have hq := BooleanWalks.good_degree_bound P
  have hcard := card_available_add_singletonDegree J.val.1
  have hdeg := J.property
  omega

def blockGoodSubsets_isEmpty {s : ℕ} (hs : Fintype.card ι < s)
    (J : DegreeBlock ι s) : IsEmpty (BlockGoodSubsets J) :=
  ⟨fun P => (Nat.not_le_of_gt hs) (block_good_degree_le J P)⟩

theorem card_blockGoodSubsets_zero {s : ℕ} (hs : Fintype.card ι < s)
    (J : DegreeBlock ι s) : Fintype.card (BlockGoodSubsets J) = 0 := by
  letI := blockGoodSubsets_isEmpty hs J
  exact Fintype.card_eq_zero

end PaperVerification.AlternatingForms.EvenSingletons
