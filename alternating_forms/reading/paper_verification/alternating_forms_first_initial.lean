module

public import PaperVerification.AlternatingFormsPrefixCorrections
public import PaperVerification.AlternatingFormsPluckerInitial

/-!
# Every forbidden left coordinate lies in the actual initial isotropy ideal

The first failed path inequality supplies the prefix, its two selections,
and the exact excess occupancy.  The actual supported inverse is multiplied
by the complete suffix.  Its product with the full canonical form is an
actual isotropy relation, whose unique greatest-weight variable is the
original Plücker coordinate.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace PaperVerification.AlternatingForms

open scoped BigOperators
open PaperVerification.WeightedInitialFiber
open MvPolynomial

variable {K : Type*} [Field K] {k h s t n : ℕ}

@[simp] theorem indexExteriorWord_pair (a b : Fin n) :
    indexExteriorWord (K := K) [a,b]=
      ExteriorAlgebra.ι K (Pi.basisFun K (Fin n) a)*
        ExteriorAlgebra.ι K (Pi.basisFun K (Fin n) b) := by
  simp only [indexExteriorWord,List.map_cons,List.map_nil,List.prod_cons,
    List.prod_nil,mul_one]

theorem indexExteriorWord_mem (L : List (Fin n)) :
    indexExteriorWord (K := K) L∈⋀[K]^L.length (Fin n → K) := by
  simpa only [List.length_map,List.map_map,Function.comp_def,indexExteriorWord] using
    (exteriorWord_mem (K := K) (L.map (Pi.basisFun K (Fin n))))

def oddPrefixPairs (hk : h≤k) : Finset (Fin k) :=
  Finset.univ.map (prefixPairEmbedding hk)

theorem mem_oddPrefixPairs (hk : h≤k) (j : Fin k) :
    j∈oddPrefixPairs hk ↔ j.val<h := by
  constructor
  · intro hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
    exact i.isLt
  · intro hj
    exact Finset.mem_map.mpr ⟨⟨j.val,hj⟩,Finset.mem_univ _,Fin.ext rfl⟩

theorem oddPathFirst_split_prefix (hk : h≤k) :
    (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))) :
      ExteriorAlgebra K (Fin (2*k+1) → K))=
      (∑ i : Fin h,indexExteriorWord [oddPrefixLeft hk i,oddPrefixRight hk i])+
        ∑ j∈(oddPrefixPairs hk)ᶜ,indexExteriorWord [oddPathFirstLeft j,oddPathMiddle j] := by
  rw [oddPathFirstQuadratic,matchingQuadratic_coe]
  have he := (Finset.sum_add_sum_compl (oddPrefixPairs hk)
    (fun j : Fin k => indexExteriorWord (K := K) [oddPathFirstLeft j,oddPathMiddle j])).symm
  simpa only [oddPrefixPairs,Finset.sum_map,prefixPairEmbedding_apply,oddPrefixLeft,oddPrefixRight,indexExteriorWord_pair] using he

set_option maxHeartbeats 800000 in
/-- The supported inverse gives a relation modulo the first form, with
corrections lower in the common Plücker weight. -/
theorem oddPrefix_actual_lower_relation [CharZero K]
    (hk : h≤k) (hpos : 0<h) (A B : Finset (Fin h))
    (hdegree : A.card+B.card=h+1) (L : List (Fin (2*k+1)))
    (hs : (A.toList.map (oddPrefixLeft hk)++
      B.toList.map (oddPrefixRight hk)++L).length=t+2) :
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
  obtain ⟨η,hη,hηsupport⟩ := prefix_selection_division_with_support (K := K) u v A B
    (by simpa only [Fintype.card_fin] using hdegree)
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

/-- The unrestricted first-half initial containment from Lemma 3.2.
The first-failure prefix, its supported inverse, the complete suffix, and
the nonzero leading scalar are all derived from the actual forbidden tuple. -/
theorem odd_left_variable_mem_initial [CharZero K]
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
  obtain ⟨g,hg,hrel⟩ := oddPrefix_actual_lower_relation (K := K) hk hpos A B hdegree L hs
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

end PaperVerification.AlternatingForms
