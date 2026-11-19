module

public import PaperVerification.AlternatingFormsPrefixCharacteristic
public import PaperVerification.AlternatingFormsReflectedInitial

/-!
# Both initial containments with only the required factorial inverses

Every relation below belongs to the actual isotropy ideal.  The common
vertex weight, retained suffix, singleton support, and nonzero exterior
reordering sign are the same as in the characteristic-zero argument.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open scoped BigOperators
open PaperVerification.WeightedInitialFiber
open MvPolynomial

variable {K : Type*} [Field K] {k h s t : ℕ}

/-- Exactly the local factorials that may occur in exterior degree `s`. -/
def DegreeFactorials (K : Type*) [Field K] (s : ℕ) : Prop :=
  ∀ r : ℕ, 2*r≤s → (r.factorial : K) ≠ 0

theorem degreeFactorials_of_lt_twice_characteristic (p s : ℕ)
    [Fact p.Prime] [CharP K p] (hs : s<2*p) : DegreeFactorials K s := by
  intro r hr
  apply factorial_cast_ne_zero_of_lt_char p
  omega

theorem degreeFactorials_charZero [CharZero K] (s : ℕ) : DegreeFactorials K s := by
  intro r hr
  exact_mod_cast Nat.factorial_ne_zero r

set_option maxHeartbeats 800000 in
theorem oddPrefix_actual_lower_relation_of_factorial
    (hk : h≤k) (hpos : 0<h) (A B : Finset (Fin h))
    (hdegree : A.card+B.card=h+1) (L : List (Fin (2*k+1)))
    (hs : (A.toList.map (oddPrefixLeft hk)++
      B.toList.map (oddPrefixRight hk)++L).length=t+2)
    (hfac : ((A ∩ B).card.factorial : K) ≠ 0) :
    ∃ g : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K,
      g∈lowerWeightSpace (pluckerVertexWeight (oddNatVertexWeight k))
        (((A.toList.map (oddPrefixLeft hk)++
          B.toList.map (oddPrefixRight hk)++L).map (oddNatVertexWeight k)).sum) ∧
      totalExteriorPluckerCoordinates (K := K) (t+2) (2*k+1)
        (indexExteriorWord (A.toList.map (oddPrefixLeft hk)++
          B.toList.map (oddPrefixRight hk)++L))+g ∈
        isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k) := by
  let u : Fin h → (Fin (2*k+1) → K) :=
    fun i => Pi.basisFun K (Fin (2*k+1)) (oddPrefixLeft hk i)
  let v : Fin h → (Fin (2*k+1) → K) :=
    fun i => Pi.basisFun K (Fin (2*k+1)) (oddPrefixRight hk i)
  obtain ⟨η,hη,hηsupport⟩ := prefix_selection_division_with_support_of_factorial (K := K) u v A B
    (by simpa only [Fintype.card_fin] using hdegree) hfac
  let ηE : ExteriorAlgebra K (Fin (2*k+1) → K) := η
  have hηdegree : (η : ExteriorAlgebra K (Fin (2*k+1) → K))∈
      ⋀[K]^(h-1) (Fin (2*k+1) → K) := by
    simpa only [Fintype.card_fin] using η.property
  have hηidentity :
      (∑ i : Fin h,indexExteriorWord (K := K) [oddPrefixLeft hk i,oddPrefixRight hk i])*
        (η : ExteriorAlgebra K (Fin (2*k+1) → K))=
      indexExteriorWord (A.toList.map (oddPrefixLeft hk)++
        B.toList.map (oddPrefixRight hk)) := by
    simpa only [u,v,indexExteriorWord,List.map_append,List.map_map,Function.comp_def,
      List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] using hη
  have hlen : h-1+L.length=t := by
    simp only [List.length_append,List.length_map,Finset.length_toList] at hs
    omega
  let x : ExteriorAlgebra K (Fin (2*k+1) → K) := ηE*indexExteriorWord (K := K) L
  have hx : x∈⋀[K]^t (Fin (2*k+1) → K) := by
    rw [←hlen]
    exact SetLike.mul_mem_graded hηdegree (indexExteriorWord_mem L)
  let g : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K :=
    ∑ j∈(oddPrefixPairs hk)ᶜ,prefixCorrectionCoordinates (K := K) (t+2) (2*k+1)
      (oddPathFirstLeft j) (oddPathMiddle j) L ηE
  have hg : g∈lowerWeightSpace (pluckerVertexWeight (oddNatVertexWeight k))
      (((A.toList.map (oddPrefixLeft hk)++
        B.toList.map (oddPrefixRight hk)++L).map (oddNatVertexWeight k)).sum) := by
    apply Submodule.sum_mem
    intro j hj
    have hj' : h≤j.val := by
      have hn := Finset.mem_compl.mp hj
      rw [mem_oddPrefixPairs] at hn
      omega
    exact oddPrefix_supported_correction_lower (K := K) hk A B hdegree j hj' L hs ηE hηsupport
  refine ⟨g,hg,?_⟩
  have hmem := totalExteriorPluckerCoordinates_wedge_mem
    (oddPluckerForms (K := K) k) (0 : Fin 2) x hx
  rw [oddPluckerForms_first] at hmem
  have he :
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))) :
        ExteriorAlgebra K (Fin (2*k+1) → K))*x=
      indexExteriorWord (A.toList.map (oddPrefixLeft hk)++
        B.toList.map (oddPrefixRight hk)++L)+
        ∑ j∈(oddPrefixPairs hk)ᶜ,
          (indexExteriorWord (K := K) [oddPathFirstLeft j,oddPathMiddle j]*ηE)*indexExteriorWord L := by
    rw [oddPathFirst_split_prefix (K := K) hk,add_mul]
    dsimp only [x]
    rw [←mul_assoc,hηidentity,←indexExteriorWord_append]
    simp only [Finset.sum_mul,mul_assoc,List.append_assoc]
  rw [he,map_add,map_sum] at hmem
  simpa only [g,prefixCorrectionCoordinates,LinearMap.comp_apply,
    LinearMap.mulRight_apply,LinearMap.mulLeft_apply] using hmem

theorem odd_left_variable_mem_initial_of_degree_factorials
    (hfac : DegreeFactorials K (t+2))
    (I : PluckerIndex (t+2) (2*k+1))
    (hbad : ∃ i,(I.val i).val<2*i.val) :
    X I∈initialIdeal (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))
      (pluckerVertexWeight (oddNatVertexWeight k)) := by
  obtain ⟨h,hpos,hk,hdegree⟩ := odd_left_failure_matching_selection I.val I.property hbad
  let A := tuplePrefixLeft I.val I.property h
  let B := tuplePrefixRight I.val I.property h
  let L := (tuplePrefixSuffix I.val h).toList
  have hs : (A.toList.map (oddPrefixLeft hk)++
      B.toList.map (oddPrefixRight hk)++L).length=t+2 := by
    simpa only [A,B,L,tuplePrefixWord,List.append_assoc] using
      (tuplePrefixWord_length I.val I.property hk)
  have hfac' : ((A ∩ B).card.factorial : K) ≠ 0 := by
    apply hfac
    have hpair := prefix_double_pair_bound A B
    have hsize := hs
    simp only [List.length_append,List.length_map,Finset.length_toList] at hsize
    omega
  obtain ⟨g,hg,hrel⟩ := oddPrefix_actual_lower_relation_of_factorial
    hk hpos A B hdegree L hs hfac' 
  obtain ⟨ε,hε,hlead⟩ := tuplePrefixWord_coordinates (K := K) I hk
  have hw : ((A.toList.map (oddPrefixLeft hk)++
      B.toList.map (oddPrefixRight hk)++L).map (oddNatVertexWeight k)).sum=
      pluckerVertexWeight (oddNatVertexWeight k) I := by
    simpa only [A,B,L,tuplePrefixWord,List.append_assoc,pluckerVertexWeight] using
      (tuplePrefixWord_weight I.val I.property hk (oddNatVertexWeight k))
  have hlead' : totalExteriorPluckerCoordinates (K := K) (t+2) (2*k+1)
      (indexExteriorWord (A.toList.map (oddPrefixLeft hk)++
        B.toList.map (oddPrefixRight hk)++L))=ε • X I := by
    simpa only [A,B,L,tuplePrefixWord,List.append_assoc] using hlead
  rw [hw] at hg
  rw [hlead'] at hrel
  exact variable_mem_initialIdeal_of_lower_relation _ _ I ε hε g hg hrel

set_option maxHeartbeats 800000 in
theorem reflectedPrefix_actual_lower_relation_of_factorial
    (hk : h≤k) (hpos : 0<h) (A B : Finset (Fin h))
    (hdegree : A.card+B.card=h+1) (L : List (Fin (2*k+1)))
    (hs : (A.toList.map (reflectedPrefixLeft hk)++
      B.toList.map (reflectedPrefixRight hk)++L).length=t+2)
    (hfac : ((A ∩ B).card.factorial : K) ≠ 0) :
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
  obtain ⟨η,hη,hηsupport⟩ := prefix_selection_division_with_support_of_factorial (K := K) u v A B
    (by simpa only [Fintype.card_fin] using hdegree) hfac
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

theorem odd_right_variable_mem_initial_of_degree_factorials
    (hfac : DegreeFactorials K (t+2))
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
  have hfac' : ((A ∩ B).card.factorial : K) ≠ 0 := by
    apply hfac
    have hpair := prefix_double_pair_bound A B
    have hsize := hs
    simp only [List.length_append,List.length_map,Finset.length_toList] at hsize
    omega
  obtain ⟨g,hg,hrel⟩ := reflectedPrefix_actual_lower_relation_of_factorial
    hk hpos A B hdegree L hs hfac' 
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
