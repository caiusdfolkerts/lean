module

public import PaperVerification.AlternatingFormsFirstInitial

/-!
# The reflected forbidden coordinates in the same initial ideal

Reflection sends the first canonical form to the negative of the second.
The two letters inside a reflected pair are retained in their reflected
order, including that sign.  The lower-weight calculation uses the same
vertex weights as the left-prefix argument.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace PaperVerification.AlternatingForms

open scoped BigOperators
open PaperVerification.WeightedInitialFiber
open MvPolynomial

variable {K : Type*} [Field K] {k h s t : ℕ}

def reflectedPrefixLeft (hk : h≤k) (i : Fin h) : Fin (2*k+1) :=
  (oddPrefixLeft hk i).rev

def reflectedPrefixRight (hk : h≤k) (i : Fin h) : Fin (2*k+1) :=
  (oddPrefixRight hk i).rev

def reflectedPrefixWord (I : PluckerIndex s (2*k+1)) (hk : h≤k) :
    List (Fin (2*k+1)) :=
  (tuplePrefixWord (reflectSelection I.val)
    (reflectSelection_strictMono I.val I.property) hk).map Fin.rev

theorem reflectedPrefixWord_perm (I : PluckerIndex s (2*k+1)) (hk : h≤k) :
    (reflectedPrefixWord I hk).Perm (List.ofFn I.val) := by
  apply ((tuplePrefixWord_perm (reflectSelection I.val)
    (reflectSelection_strictMono I.val I.property) hk).map Fin.rev).trans
  simpa only [List.map_ofFn,reflectSelection,Fin.rev_rev,Fin.revPerm_apply,Function.comp_def] using
    (Equiv.Perm.ofFn_comp_perm Fin.revPerm I.val)

theorem reflectedPrefixWord_length (I : PluckerIndex s (2*k+1)) (hk : h≤k) :
    (reflectedPrefixWord I hk).length=s := by
  simpa only [List.length_ofFn] using (reflectedPrefixWord_perm I hk).length_eq

theorem reflectedPrefixWord_weight {R : Type*} [AddCommMonoid R]
    (I : PluckerIndex s (2*k+1)) (hk : h≤k) (w : Fin (2*k+1) → R) :
    ((reflectedPrefixWord I hk).map w).sum=∑ i,w (I.val i) := by
  rw [((reflectedPrefixWord_perm I hk).map w).sum_eq,List.map_ofFn,List.sum_ofFn]
  rfl

theorem reflectedPrefixWord_coordinates (I : PluckerIndex s (2*k+1)) (hk : h≤k) :
    ∃ ε : K,ε≠0 ∧
      totalExteriorPluckerCoordinates (K := K) s (2*k+1)
        (indexExteriorWord (reflectedPrefixWord I hk))=ε • X I := by
  obtain ⟨ε,hε,he⟩ := exterior_word_permutation (K := K)
    ((reflectedPrefixWord_perm I hk).map (Pi.basisFun K (Fin (2*k+1))))
  have he' : indexExteriorWord (K := K) (reflectedPrefixWord I hk)=
      ε • indexExteriorWord (List.ofFn I.val) := by
    simpa only [indexExteriorWord,List.map_map,Function.comp_def] using he
  exact ⟨ε,hε,by rw [he',map_smul,totalExteriorPluckerCoordinates_ofFn]⟩

/-- The reflected pairs have the same increasing binary pair costs as the
left prefix, in the single common original weight vector. -/
theorem reflectedPrefix_replacement_cost (hk : h≤k) (A B : Finset (Fin h))
    (hdegree : A.card+B.card=h+1)
    (T : FixedSubsets (PrefixFreePair A B) ((A∩B).card-1))
    (j : Fin k) (hj : h≤j.val) :
    (∑ i∈T.val,(oddNatVertexWeight k (reflectedPrefixLeft hk i.val)+
      oddNatVertexWeight k (reflectedPrefixRight hk i.val)))+
      (oddNatVertexWeight k (oddPathFirstLeft j).rev+
        oddNatVertexWeight k (oddPathMiddle j).rev) <
    ∑ i∈A∩B,(oddNatVertexWeight k (reflectedPrefixLeft hk i)+
      oddNatVertexWeight k (reflectedPrefixRight hk i)) := by
  let P := (A∩B).map (prefixPairEmbedding hk)
  let U := T.val.map (prefixFreeEmbedding hk A B)
  have hpos : 0<(A∩B).card := (prefix_occupancy_counts A B
    (by simpa only [Fintype.card_fin] using hdegree)).1
  have hcard : P.card=U.card+1 := by
    simp only [P,U,Finset.card_map,T.property]
    omega
  have hP : ∀ i∈P,i.val<h := by
    rintro i hi
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hi
    exact a.isLt
  have he := oddSecond_replacement_weight_strict P U h j hP hj hcard
  have hz :
      (∑ i∈T.val,(oddPathVertexWeight k (reflectedPrefixLeft hk i.val)+
        oddPathVertexWeight k (reflectedPrefixRight hk i.val)))+
        (oddPathVertexWeight k (oddPathFirstLeft j).rev+
          oddPathVertexWeight k (oddPathMiddle j).rev) <
      ∑ i∈A∩B,(oddPathVertexWeight k (reflectedPrefixLeft hk i)+
        oddPathVertexWeight k (reflectedPrefixRight hk i)) := by
    simpa only [P,U,Finset.sum_map,prefixPairEmbedding_apply,prefixFreeEmbedding_apply,
      reflectedPrefixLeft,reflectedPrefixRight,
      oddPrefixLeft,oddPrefixRight,oddPathFirstLeft_rev,oddPathMiddle_rev,add_comm] using he
  have hc :
      (((∑ i∈T.val,(oddNatVertexWeight k (reflectedPrefixLeft hk i.val)+
        oddNatVertexWeight k (reflectedPrefixRight hk i.val)))+
        (oddNatVertexWeight k (oddPathFirstLeft j).rev+
          oddNatVertexWeight k (oddPathMiddle j).rev) : ℕ) : ℤ) <
      ((∑ i∈A∩B,(oddNatVertexWeight k (reflectedPrefixLeft hk i)+
        oddNatVertexWeight k (reflectedPrefixRight hk i)) : ℕ) : ℤ) := by
    simpa only [Nat.cast_add,Nat.cast_sum,oddNatVertexWeight_cast] using hz
  exact_mod_cast hc

theorem reflectedPrefix_supported_correction_lower
    (hk : h≤k) (A B : Finset (Fin h)) (hdegree : A.card+B.card=h+1)
    (j : Fin k) (hj : h≤j.val) (L : List (Fin (2*k+1)))
    (hs : (A.toList.map (reflectedPrefixLeft hk)++
      B.toList.map (reflectedPrefixRight hk)++L).length=s)
    (η : ExteriorAlgebra K (Fin (2*k+1) → K))
    (hη : η∈prefixInverseSpace
      (fun i => Pi.basisFun K (Fin (2*k+1)) (reflectedPrefixLeft hk i))
      (fun i => Pi.basisFun K (Fin (2*k+1)) (reflectedPrefixRight hk i)) A B) :
    prefixCorrectionCoordinates (K := K) s (2*k+1)
      (oddPathFirstLeft j).rev (oddPathMiddle j).rev L η ∈
      lowerWeightSpace (pluckerVertexWeight (oddNatVertexWeight k))
        (((A.toList.map (reflectedPrefixLeft hk)++
          B.toList.map (reflectedPrefixRight hk)++L).map (oddNatVertexWeight k)).sum) := by
  apply supported_prefix_transport_lower _ _ A B _ _ _ _ η hη
  intro T
  exact prefix_state_correction_lower_of_cost _ _ A B hdegree T _ _ _ L hs
    (reflectedPrefix_replacement_cost hk A B hdegree T j hj)

theorem reflectedFirst_split_prefix (hk : h≤k) :
    (oddPathFirstQuadratic (K := K) (fun i => Pi.basisFun K (Fin (2*k+1)) i.rev) :
      ExteriorAlgebra K (Fin (2*k+1) → K))=
      (∑ i : Fin h,indexExteriorWord [reflectedPrefixLeft hk i,reflectedPrefixRight hk i])+
        ∑ j∈(oddPrefixPairs hk)ᶜ,
          indexExteriorWord [(oddPathFirstLeft j).rev,(oddPathMiddle j).rev] := by
  rw [oddPathFirstQuadratic,matchingQuadratic_coe]
  have he := (Finset.sum_add_sum_compl (oddPrefixPairs hk)
    (fun j : Fin k => indexExteriorWord (K := K)
      [(oddPathFirstLeft j).rev,(oddPathMiddle j).rev])).symm
  simpa only [oddPrefixPairs,Finset.sum_map,prefixPairEmbedding_apply,reflectedPrefixLeft,reflectedPrefixRight,
    oddPrefixLeft,oddPrefixRight,indexExteriorWord_pair] using he

theorem reflectedPrefix_actual_lower_relation [CharZero K]
    (hk : h≤k) (hpos : 0<h) (A B : Finset (Fin h))
    (hdegree : A.card+B.card=h+1) (L : List (Fin (2*k+1)))
    (hs : (A.toList.map (reflectedPrefixLeft hk)++
      B.toList.map (reflectedPrefixRight hk)++L).length=t+2) :
    ∃ g : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K,
      g∈lowerWeightSpace (pluckerVertexWeight (oddNatVertexWeight k))
        (((A.toList.map (reflectedPrefixLeft hk)++
          B.toList.map (reflectedPrefixRight hk)++L).map (oddNatVertexWeight k)).sum) ∧
      totalExteriorPluckerCoordinates (K := K) (t+2) (2*k+1)
        (indexExteriorWord (A.toList.map (reflectedPrefixLeft hk)++
          B.toList.map (reflectedPrefixRight hk)++L))+g ∈
        isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k) := by
  let u : Fin h → (Fin (2*k+1) → K) :=
    fun i => Pi.basisFun K (Fin (2*k+1)) (reflectedPrefixLeft hk i)
  let v : Fin h → (Fin (2*k+1) → K) :=
    fun i => Pi.basisFun K (Fin (2*k+1)) (reflectedPrefixRight hk i)
  obtain ⟨η,hη,hηsupport⟩ := prefix_selection_division_with_support (K := K) u v A B
    (by simpa only [Fintype.card_fin] using hdegree)
  have hηdegree : (η : ExteriorAlgebra K (Fin (2*k+1) → K))∈
      ⋀[K]^(h-1) (Fin (2*k+1) → K) := by
    simpa only [Fintype.card_fin] using η.property
  have hηidentity :
      (∑ i : Fin h,indexExteriorWord (K := K) [reflectedPrefixLeft hk i,reflectedPrefixRight hk i])*
        (η : ExteriorAlgebra K (Fin (2*k+1) → K))=
      indexExteriorWord (A.toList.map (reflectedPrefixLeft hk)++
        B.toList.map (reflectedPrefixRight hk)) := by
    simpa only [indexExteriorWord_pair,u,v,indexExteriorWord,List.map_append,
      List.map_map,Function.comp_def,List.map_cons,List.map_nil,
      List.prod_cons,List.prod_nil,mul_one] using hη
  have hlen : h-1+L.length=t := by
    simp only [List.length_append,List.length_map,Finset.length_toList] at hs
    omega
  let x : ExteriorAlgebra K (Fin (2*k+1) → K) :=
    (η : ExteriorAlgebra K (Fin (2*k+1) → K))*indexExteriorWord (K := K) L
  have hx : x∈⋀[K]^t (Fin (2*k+1) → K) := by
    rw [←hlen]
    exact SetLike.mul_mem_graded hηdegree (indexExteriorWord_mem (K := K) L)
  let g : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K :=
    ∑ j∈(oddPrefixPairs hk)ᶜ,prefixCorrectionCoordinates (K := K) (t+2) (2*k+1)
      (oddPathFirstLeft j).rev (oddPathMiddle j).rev L
        (η : ExteriorAlgebra K (Fin (2*k+1) → K))
  have hg : g∈lowerWeightSpace (pluckerVertexWeight (oddNatVertexWeight k))
      (((A.toList.map (reflectedPrefixLeft hk)++
        B.toList.map (reflectedPrefixRight hk)++L).map (oddNatVertexWeight k)).sum) := by
    apply Submodule.sum_mem
    intro j hj
    have hj' : h≤j.val := by
      have hn := Finset.mem_compl.mp hj
      rw [mem_oddPrefixPairs] at hn
      omega
    exact reflectedPrefix_supported_correction_lower hk A B hdegree j hj' L hs
      (η : ExteriorAlgebra K (Fin (2*k+1) → K)) hηsupport
  refine ⟨g,hg,?_⟩
  have hmemSecond := totalExteriorPluckerCoordinates_wedge_mem (K := K) (t := t)
    (oddPluckerForms (K := K) k) (1 : Fin 2) x hx
  rw [oddPluckerForms_second] at hmemSecond
  have hmem : totalExteriorPluckerCoordinates (K := K) (t+2) (2*k+1)
      ((oddPathFirstQuadratic (K := K) (fun i => Pi.basisFun K (Fin (2*k+1)) i.rev) :
        ExteriorAlgebra K (Fin (2*k+1) → K))*x)∈
      isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k) := by
    rw [oddPath_reflection,Submodule.coe_neg,neg_mul,map_neg]
    exact (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)).neg_mem hmemSecond
  have he :
      (oddPathFirstQuadratic (K := K) (fun i => Pi.basisFun K (Fin (2*k+1)) i.rev) :
        ExteriorAlgebra K (Fin (2*k+1) → K))*x=
      indexExteriorWord (A.toList.map (reflectedPrefixLeft hk)++
        B.toList.map (reflectedPrefixRight hk)++L)+
        ∑ j∈(oddPrefixPairs hk)ᶜ,
          (indexExteriorWord (K := K) [(oddPathFirstLeft j).rev,(oddPathMiddle j).rev]*
            (η : ExteriorAlgebra K (Fin (2*k+1) → K)))*indexExteriorWord (K := K) L := by
    rw [reflectedFirst_split_prefix hk,add_mul]
    dsimp only [x]
    rw [←mul_assoc,hηidentity,←indexExteriorWord_append]
    simp only [Finset.sum_mul,mul_assoc,List.append_assoc]
  rw [he,map_add,map_sum] at hmem
  simpa only [g,prefixCorrectionCoordinates,LinearMap.comp_apply,
    LinearMap.mulRight_apply,LinearMap.mulLeft_apply] using hmem

/-- The right-half containment uses the same initial ideal and the same
weight vector as the left-half theorem.  The arithmetic failure is written
without truncated subtraction, so the assertion is meaningful in every size. -/
theorem odd_right_variable_mem_initial [CharZero K]
    (I : PluckerIndex (t+2) (2*k+1))
    (hbad : ∃ i,2*k+2+2*i.val<(I.val i).val+2*(t+2)) :
    X I∈initialIdeal (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))
      (pluckerVertexWeight (oddNatVertexWeight k)) := by
  let J := reflectSelection I.val
  have hJ : StrictMono J := reflectSelection_strictMono I.val I.property
  have hbadJ : ∃ i,(J i).val<2*i.val := by
    apply right_failure_becomes_left I.val
    obtain ⟨i,hi⟩ := hbad
    exact ⟨i,by omega⟩
  obtain ⟨h,hpos,hk,hdegree⟩ := odd_left_failure_matching_selection J hJ hbadJ
  let A := tuplePrefixLeft J hJ h
  let B := tuplePrefixRight J hJ h
  let L := (tuplePrefixSuffix J h).toList.map Fin.rev
  have hword : A.toList.map (reflectedPrefixLeft hk)++
      B.toList.map (reflectedPrefixRight hk)++L=reflectedPrefixWord I hk := by
    simp only [A,B,L,J,reflectedPrefixWord,tuplePrefixWord,reflectedPrefixLeft,
      reflectedPrefixRight,List.map_append,List.map_map,Function.comp_def,List.append_assoc]
    rfl
  have hs : (A.toList.map (reflectedPrefixLeft hk)++
      B.toList.map (reflectedPrefixRight hk)++L).length=t+2 := by
    rw [hword,reflectedPrefixWord_length]
  obtain ⟨g,hg,hrel⟩ := reflectedPrefix_actual_lower_relation (K := K) hk hpos A B hdegree L hs
  obtain ⟨ε,hε,hlead⟩ := reflectedPrefixWord_coordinates (K := K) I hk
  have hw : ((A.toList.map (reflectedPrefixLeft hk)++
      B.toList.map (reflectedPrefixRight hk)++L).map (oddNatVertexWeight k)).sum=
      pluckerVertexWeight (oddNatVertexWeight k) I := by
    rw [hword,reflectedPrefixWord_weight]
    rfl
  rw [hw] at hg
  rw [hword,hlead] at hrel
  exact variable_mem_initialIdeal_of_lower_relation _ _ I ε hε g hg hrel

end PaperVerification.AlternatingForms
