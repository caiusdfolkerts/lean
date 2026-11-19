module

public import PaperVerification.AlternatingFormsEvenSingletonBasis
public import PaperVerification.AlternatingFormsBooleanMultiplication

/-!
# Boolean multiplication on actual exterior singleton blocks

The matching two-form acts on each fixed singleton block by the weighted
Boolean inclusion matrix.  Both the block embedding and the two-form are
literal exterior-algebra constructions, and the embedding is proved injective.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.EvenSingletons

open scoped BigOperators

variable {K M ι : Type*} [Field K] [AddCommGroup M] [Module K M]
  [LinearOrder ι] [Fintype ι]
local notation "E" => ExteriorAlgebra K M

def matchingForm (b : Module.Basis (ι ⊕ ι) K M) (a : ι → K) : ⋀[K]^2 M :=
  ∑ i, a i • exteriorPair (K := K) (b (Sum.inl i)) (b (Sum.inr i))

@[simp] theorem matchingForm_coe (b : Module.Basis (ι ⊕ ι) K M) (a : ι → K) :
    (matchingForm b a : E) =
      ∑ i, a i • (exteriorPair (K := K) (b (Sum.inl i)) (b (Sum.inr i)) : E) := by
  simp only [matchingForm, AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul]

def pairVariables (b : Module.Basis (ι ⊕ ι) K M) (S : SingletonState ι) :
    Available S → Subalgebra.center K E :=
  fun i => exteriorPairCentral (K := K) (b (Sum.inl i.val)) (b (Sum.inr i.val))

theorem pairedMonomial_available (b : Module.Basis (ι ⊕ ι) K M)
    (S : SingletonState ι) (P : Finset (Available S)) :
    pairedMonomial (K := K) (fun i : Available S => b (Sum.inl i.val))
      (fun i : Available S => b (Sum.inr i.val)) P =
    pairedMonomial (K := K) (fun i => b (Sum.inl i)) (fun i => b (Sum.inr i)) (pairSupport S P) := by
  simp only [pairedMonomial, pairSupport, Finset.prod_map, Function.Embedding.coe_subtype]

def blockEvaluation (b : Module.Basis (ι ⊕ ι) K M) (S : SingletonState ι) (q : ℕ) :
    (FixedSubsets (Available S) q → K) →ₗ[K] E where
  toFun v := singletonMonomial b S * (squarefreeEvaluation (pairVariables b S) q v : E)
  map_add' v w := by simp only [map_add, Subalgebra.coe_add, mul_add]
  map_smul' a v := by simp only [map_smul, Subalgebra.coe_smul, mul_smul_comm, RingHom.id_apply]

theorem blockEvaluation_apply (b : Module.Basis (ι ⊕ ι) K M) (S : SingletonState ι)
    (q : ℕ) (v : FixedSubsets (Available S) q → K) :
    blockEvaluation b S q v =
      ∑ P : FixedSubsets (Available S) q, v P • stateMonomial b ⟨S, P.val⟩ := by
  change singletonMonomial b S *
      ((∑ P : FixedSubsets (Available S) q,
        v P • ∏ i ∈ P.val, pairVariables b S i : Subalgebra.center K E) : E) = _
  simp only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul, Finset.mul_sum,
    mul_smul_comm]
  apply Finset.sum_congr rfl
  intro P hP
  congr 1
  change singletonMonomial b S * pairedMonomial
    (fun i : Available S => b (Sum.inl i.val)) (fun i : Available S => b (Sum.inr i.val)) P.val = _
  rw [pairedMonomial_available]
  rfl

theorem blockEvaluation_coordinate (b : Module.Basis (ι ⊕ ι) K M) (S : SingletonState ι)
    (q : ℕ) (v : FixedSubsets (Available S) q → K) (P : FixedSubsets (Available S) q) :
    (stateBasis b).repr (blockEvaluation b S q v) ⟨S, P.val⟩ = v P := by
  rw [blockEvaluation_apply]
  simp only [← stateBasis_apply, map_sum, map_smul, Finset.sum_apply', Finsupp.smul_apply,
    Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
  have hinj : Function.Injective
      (fun Q : FixedSubsets (Available S) q => (⟨S, Q.val⟩ : PairedState ι)) := by
    intro Q R hQR
    apply Subtype.ext
    exact sigma_mk_injective (β := fun T : SingletonState ι => Finset (Available T))
      (i := S) hQR
  simp only [hinj.eq_iff, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem blockEvaluation_injective (b : Module.Basis (ι ⊕ ι) K M)
    (S : SingletonState ι) (q : ℕ) : Function.Injective (blockEvaluation b S q) := by
  intro v w h
  ext P
  have hc := congrArg (fun x : E => (stateBasis b).repr x ⟨S, P.val⟩) h
  simpa only [blockEvaluation_coordinate] using hc

theorem blockEvaluation_homogeneous (b : Module.Basis (ι ⊕ ι) K M)
    (S : SingletonState ι) (q : ℕ) (v : FixedSubsets (Available S) q → K) :
    blockEvaluation b S q v ∈ ⋀[K]^(singletonDegree S + 2 * q) M := by
  rw [blockEvaluation_apply]
  apply Submodule.sum_mem
  intro P hP
  apply Submodule.smul_mem
  simpa only [degree, P.property] using stateMonomial_homogeneous b ⟨S, P.val⟩

def blockEvaluationDegree (b : Module.Basis (ι ⊕ ι) K M)
    (S : SingletonState ι) (q : ℕ) :
    (FixedSubsets (Available S) q → K) →ₗ[K] (⋀[K]^(singletonDegree S + 2 * q) M) :=
  (blockEvaluation b S q).codRestrict _ (blockEvaluation_homogeneous b S q)

theorem pair_mul_singleton_eq_zero (b : Module.Basis (ι ⊕ ι) K M)
    (S : SingletonState ι) (i : ι) (hi : i ∈ S.val.1 ∪ S.val.2) :
    (exteriorPair (K := K) (b (Sum.inl i)) (b (Sum.inr i)) : E) * singletonMonomial b S = 0 := by
  rcases Finset.mem_union.mp hi with hA | hB
  · apply twoForm_mul_word_eq_zero_of_mem _ (b (Sum.inl i))
      (exteriorPair_mul_left_generator _ _)
    exact List.mem_map.mpr ⟨Sum.inl i, by simp [singletonWord, selectionWord, hA], rfl⟩
  · apply twoForm_mul_word_eq_zero_of_mem _ (b (Sum.inr i))
      (exteriorPair_mul_right_generator _ _)
    exact List.mem_map.mpr ⟨Sum.inr i, by simp [singletonWord, selectionWord, hB], rfl⟩

theorem matching_mul_singleton (b : Module.Basis (ι ⊕ ι) K M) (a : ι → K)
    (S : SingletonState ι) :
    (matchingForm b a : E) * singletonMonomial b S =
      singletonMonomial b S *
        ((∑ i : Available S, a i.val • pairVariables b S i : Subalgebra.center K E) : E) := by
  let z := singletonMonomial b S
  let y (i : ι) : E := exteriorPair (K := K) (b (Sum.inl i)) (b (Sum.inr i))
  have hrestrict : (∑ i : ι, a i • (y i * z)) =
      ∑ i : Available S, a i.val • (y i.val * z) := by
    calc
      _ = ∑ i ∈ Finset.univ.filter (fun i : ι => i ∉ S.val.1 ∪ S.val.2),
          a i • (y i * z) := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro i hi hn
        have hmem : i ∈ S.val.1 ∪ S.val.2 := by
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hn
        rw [show y i * z = 0 from pair_mul_singleton_eq_zero b S i hmem, smul_zero]
      _ = _ := Finset.sum_subtype _ (fun i => by simp) _
  rw [matchingForm_coe, Finset.sum_mul]
  simp only [smul_mul_assoc]
  change (∑ i, a i • (y i * z)) = _
  rw [hrestrict]
  simp only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul, Finset.mul_sum,
    mul_smul_comm]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  exact (twoForm_commute (exteriorPair (K := K) (b (Sum.inl i.val)) (b (Sum.inr i.val))) z).eq

/-- On every fixed singleton block, the original matching form is exactly
the weighted incidence map.  No pair coefficient is required to be nonzero. -/
theorem matching_mul_blockEvaluation (b : Module.Basis (ι ⊕ ι) K M) (a : ι → K)
    (S : SingletonState ι) (q : ℕ) (v : FixedSubsets (Available S) q → K) :
    (matchingForm b a : E) * blockEvaluation b S q v =
      blockEvaluation b S (q + 1)
        (weightedInclusionOperator (fun i : Available S => a i.val) q v) := by
  change (matchingForm b a : E) *
      (singletonMonomial b S * (squarefreeEvaluation (pairVariables b S) q v : E)) = _
  rw [← mul_assoc, matching_mul_singleton, mul_assoc]
  have h := BooleanQuotient.squarefreeEvaluation_weighted_inclusion
    (pairVariables b S)
    (fun i => exteriorPairCentral_square_zero (b (Sum.inl i.val)) (b (Sum.inr i.val)))
    (fun i : Available S => a i.val) q v
  exact congrArg (fun x : Subalgebra.center K E => singletonMonomial b S * (x : E)) h

end PaperVerification.AlternatingForms.EvenSingletons
