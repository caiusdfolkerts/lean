module

public import PaperVerification.AlternatingFormsLefschetz
public import PaperVerification.AlternatingFormsFirstInitial
public import PaperVerification.AlternatingFormsDuality

/-!
# The actual exterior quotient in every degree above the odd middle

The first canonical form already kills every exterior degree greater than
`k+1` in `2k+1` variables.  An increasing word of that length has its first
`k+1` letters among the first `2k` variables.  The full symplectic-prefix
division theorem applies to precisely those letters; the complete remaining
suffix is retained.  Thus this cutoff concerns the generated exterior ideal,
not a polynomial presentation or an anticipated dimension formula.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace PaperVerification.AlternatingForms

open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K] {k r s : ℕ}

private theorem odd_long_prefix_bound
    (I : PluckerIndex (k+1+(r+1)) (2*k+1)) (i : Fin (k+1)) :
    (I.val (Fin.castAdd (r+1) i)).val<2*k := by
  have hi : Fin.castAdd (r+1) i < Fin.natAdd (k+1) (0 : Fin (r+1)) := by
    change i.val<k+1+0
    simpa only [Nat.add_zero] using i.isLt
  have hstrict := I.property hi
  have hlast := (I.val (Fin.natAdd (k+1) (0 : Fin (r+1)))).isLt
  change (I.val (Fin.castAdd (r+1) i)).val<
    (I.val (Fin.natAdd (k+1) (0 : Fin (r+1)))).val at hstrict
  omega

set_option pp.all true in
/-- Normalize the finite prefix size before entering a dependent Plücker-index
context.  This is the same division theorem, with the cardinality of `Fin k`
written as `k`. -/
private theorem odd_prefix_division (u v : Fin k → (Fin (2*k+1) → K)) :
    ∀ b : Fin (k+1) → Fin k ⊕ Fin k,
      ∃ η : ⋀[K]^(k-1) (Fin (2*k+1) → K),
        η ∈ LinearMap.range (exteriorPower.map (k-1) (pairedEvaluation u v)) ∧
        (∑ j : Fin k, ExteriorAlgebra.ι K (u j) * ExteriorAlgebra.ι K (v j)) *
          (η : ExteriorAlgebra K (Fin (2*k+1) → K)) =
          ExteriorAlgebra.ιMulti K (k+1) (Sum.elim u v ∘ b) := by
  have h := prefix_monomial_division (K := K) u v
  rw [Fintype.card_fin] at h
  exact h

/-- The literal increasing word is a multiple of the first canonical
quadratic, with every suffix letter preserved. -/
theorem odd_long_word_division
    (I : PluckerIndex (k+1+(r+1)) (2*k+1)) :
    ∃ a : ExteriorAlgebra K (Fin (2*k+1) → K),
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))) :
        ExteriorAlgebra K (Fin (2*k+1) → K))*a=
          indexExteriorWord (List.ofFn I.val) := by
  let z := Pi.basisFun K (Fin (2*k+1))
  let u : Fin k → (Fin (2*k+1) → K) := fun j => z (oddPathFirstLeft j)
  let v : Fin k → (Fin (2*k+1) → K) := fun j => z (oddPathMiddle j)
  let a : Fin (k+1) → Fin (2*k) := fun i =>
    ⟨(I.val (Fin.castAdd (r+1) i)).val,odd_long_prefix_bound I i⟩
  let b : Fin (k+1) → Fin k ⊕ Fin k := fun i => (evenOddPrefixEquiv k).symm (a i)
  have htuple : Sum.elim u v ∘ b=
      fun i => z (I.val (Fin.castAdd (r+1) i)) := by
    funext i
    have he : evenOddPrefixEquiv k (b i)=a i :=
      (evenOddPrefixEquiv k).apply_symm_apply (a i)
    change Sum.elim u v (b i)=_
    rcases hb : b i with j | j
    · rw [hb] at he
      change z (oddPathFirstLeft j)=_
      congr 1
      apply Fin.ext
      simpa only [evenOddPrefixEquiv_inl,a,oddPathFirstLeft] using congrArg Fin.val he
    · rw [hb] at he
      change z (oddPathMiddle j)=_
      congr 1
      apply Fin.ext
      simpa only [evenOddPrefixEquiv_inr,a,oddPathMiddle] using congrArg Fin.val he
  have hdiv := odd_prefix_division (K := K) u v
  obtain ⟨η,hηsupport,hη⟩ := hdiv b
  have hη' : (∑ j : Fin k,ExteriorAlgebra.ι K (u j)*ExteriorAlgebra.ι K (v j)) *
      (η : ExteriorAlgebra K (Fin (2*k+1) → K)) =
      ExteriorAlgebra.ιMulti K (k+1) (Sum.elim u v ∘ b) := by
    exact hη
  have hform : (oddPathFirstQuadratic (K := K) z : ExteriorAlgebra K (Fin (2*k+1) → K))=
      ∑ j : Fin k,ExteriorAlgebra.ι K (u j)*ExteriorAlgebra.ι K (v j) := by
    simp only [oddPathFirstQuadratic,matchingQuadratic_coe,u,v]
  have hprefix :
      (oddPathFirstQuadratic (K := K) z : ExteriorAlgebra K (Fin (2*k+1) → K))*
        (η : ExteriorAlgebra K (Fin (2*k+1) → K))=
        indexExteriorWord (List.ofFn (fun i : Fin (k+1) => I.val (Fin.castAdd (r+1) i))) := by
    rw [hform,hη',htuple]
    simp only [ExteriorAlgebra.ιMulti_apply,indexExteriorWord,List.map_ofFn,z,
      List.map_map,Function.comp_def]
  let L := List.ofFn (fun i : Fin (r+1) => I.val (Fin.natAdd (k+1) i))
  refine ⟨(η : ExteriorAlgebra K (Fin (2*k+1) → K))*indexExteriorWord L,?_⟩
  change (oddPathFirstQuadratic (K := K) z : ExteriorAlgebra K (Fin (2*k+1) → K))*
    ((η : ExteriorAlgebra K (Fin (2*k+1) → K))*indexExteriorWord L)=_
  rw [←mul_assoc,hprefix,←indexExteriorWord_append]
  congr 1
  exact (List.ofFn_add (f := I.val)).symm

private theorem odd_exteriorDegreeRelations_eq_top_add
    (g : ⋀[K]^2 (Fin (2*k+1) → K)) (r : ℕ) :
    exteriorDegreeRelations
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) g
      (k+1+(r+1))=⊤ := by
  apply eq_top_iff.mpr
  rw [←(exteriorPluckerBasis (K := K) (k+1+(r+1)) (2*k+1)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨I,rfl⟩
  change ((exteriorPluckerBasis (K := K) (k+1+(r+1)) (2*k+1) I) :
    ExteriorAlgebra K (Fin (2*k+1) → K))∈exteriorRelationIdeal _ g
  obtain ⟨a,ha⟩ := odd_long_word_division (K := K) I
  apply Ideal.mem_span_pair.mpr
  refine ⟨a,0,?_⟩
  rw [zero_mul,add_zero,
    ←(twoForm_commute (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) a).eq,ha]
  rw [exteriorPluckerBasis_apply]
  simp only [indexExteriorWord,exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.ιMulti_apply,List.map_ofFn,List.map_map,Function.comp_def]

/-- Full high-degree vanishing for the actual generated exterior ideal.
The second quadratic may be arbitrary; no upper bound on `s` is imposed. -/
theorem odd_exteriorDegreeRelations_eq_top
    (g : ⋀[K]^2 (Fin (2*k+1) → K)) (hs : k+1<s) :
    exteriorDegreeRelations
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) g s=⊤ := by
  let r := s-(k+2)
  have he : s=k+1+(r+1) := by dsimp only [r]; omega
  rw [he]
  exact odd_exteriorDegreeRelations_eq_top_add g r

theorem odd_exteriorQuotientDegree_subsingleton
    (g : ⋀[K]^2 (Fin (2*k+1) → K)) (hs : k+1<s) :
    Subsingleton (ExteriorQuotientDegree
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) g s) := by
  change Subsingleton ((⋀[K]^s (Fin (2*k+1) → K))⧸exteriorDegreeRelations _ g s)
  rw [odd_exteriorDegreeRelations_eq_top g hs]
  infer_instance

theorem odd_exteriorQuotientDegree_finrank_eq_zero
    (g : ⋀[K]^2 (Fin (2*k+1) → K)) (hs : k+1<s) :
    Module.finrank K (ExteriorQuotientDegree
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) g s)=0 := by
  letI := odd_exteriorQuotientDegree_subsingleton g hs
  exact Module.finrank_zero_of_subsingleton

end PaperVerification.AlternatingForms
