module

public import PaperVerification.AlternatingFormsPrefixPermutation

/-!
# Lower weight of every actual supported prefix correction

The free-pair subtype in the Boolean inverse is embedded into the original
matching.  Its cardinality, the fixed singleton letters, and the complete
suffix are retained.  The resulting strict inequality is transported through
the actual exterior coordinate map, for each support state and then for its
entire linear span.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace PaperVerification.AlternatingForms

open scoped BigOperators
open PaperVerification.WeightedInitialFiber

variable {ι α : Type*} [DecidableEq ι] [Fintype ι]

theorem prefix_selection_word_weight {R : Type*} [AddCommMonoid R]
    (u v : ι → α) (A B : Finset ι) (w : α → R) :
    ((A.toList.map u++B.toList.map v).map w).sum=
      ((prefixSingletonWord u v A B).map w).sum+
        ∑ i∈A∩B,(w (u i)+w (v i)) := by
  have he := ((singleton_pair_word_permutation u v A B).map w).sum_eq
  change _ = ((prefixSingletonWord u v A B++matchingIndexWord u v (A∩B)).map w).sum at he
  simpa only [List.map_append,List.sum_append,matchingIndexWord_weight] using he

variable {K : Type*} [Field K] {n s k h : ℕ}

theorem indexExteriorWord_matching (u v : ι → Fin n) (T : Finset ι) :
    indexExteriorWord (K := K) (matchingIndexWord u v T)=
      pairedMonomial (fun i => Pi.basisFun K (Fin n) (u i))
        (fun i => Pi.basisFun K (Fin n) (v i)) T := by
  simpa only [indexExteriorWord,matchingIndexWord,List.map_flatMap,List.map_cons,
    List.map_nil,List.map_map,Function.comp_def] using
      (pair_word_product (K := K) (fun i => Pi.basisFun K (Fin n) (u i))
        (fun i => Pi.basisFun K (Fin n) (v i)) T)

theorem prefixInverseState_word (u v : ι → Fin n) (A B : Finset ι)
    (T : FixedSubsets (PrefixFreePair A B) ((A∩B).card-1)) :
    indexExteriorWord (K := K)
      (prefixSingletonWord u v A B++
        matchingIndexWord (fun i : PrefixFreePair A B => u i.val)
          (fun i : PrefixFreePair A B => v i.val) T.val)=
      prefixInverseState (fun i => Pi.basisFun K (Fin n) (u i))
        (fun i => Pi.basisFun K (Fin n) (v i)) A B T := by
  rw [indexExteriorWord_append,indexExteriorWord_matching]
  simp only [prefixInverseState,prefixSingletonWord,indexExteriorWord,List.map_append,
    List.map_map,Function.comp_def]

def prefixPairEmbedding (hk : h≤k) : Fin h ↪ Fin k where
  toFun := Fin.castLE hk
  inj' a b hab := Fin.ext (congrArg (fun z : Fin k => z.val) hab)

def prefixFreeEmbedding (hk : h≤k) (A B : Finset (Fin h)) :
    PrefixFreePair A B ↪ Fin k where
  toFun i := Fin.castLE hk i.val
  inj' a b hab := Subtype.ext (Fin.ext (congrArg (fun z : Fin k => z.val) hab))

@[simp] theorem prefixPairEmbedding_apply (hk : h≤k) (i : Fin h) :
    prefixPairEmbedding hk i = Fin.castLE hk i := rfl

@[simp] theorem prefixFreeEmbedding_apply (hk : h≤k) (A B : Finset (Fin h))
    (i : PrefixFreePair A B) : prefixFreeEmbedding hk A B i = Fin.castLE hk i.val := rfl

/-- The exact free-pair support has one pair fewer than the original double
occupancy.  Embedding it into the original matching gives the strict cost
comparison without a separately supplied weight or support hypothesis. -/
theorem oddPrefix_replacement_cost (hk : h≤k) (A B : Finset (Fin h))
    (hdegree : A.card+B.card=h+1)
    (T : FixedSubsets (PrefixFreePair A B) ((A∩B).card-1))
    (j : Fin k) (hj : h≤j.val) :
    (∑ i∈T.val,(oddPathVertexWeight k (oddPrefixLeft hk i.val)+
      oddPathVertexWeight k (oddPrefixRight hk i.val)))+
      (oddPathVertexWeight k (oddPathFirstLeft j)+
        oddPathVertexWeight k (oddPathMiddle j)) <
    ∑ i∈A∩B,(oddPathVertexWeight k (oddPrefixLeft hk i)+
      oddPathVertexWeight k (oddPrefixRight hk i)) := by
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
  have he := oddFirst_replacement_weight_strict P U h j hP hj hcard
  simp only [P,U,Finset.sum_map] at he
  exact he

def prefixCorrectionCoordinates (s n : ℕ) (a b : Fin n) (L : List (Fin n)) :
    ExteriorAlgebra K (Fin n → K) →ₗ[K] MvPolynomial (PluckerIndex s n) K :=
  (totalExteriorPluckerCoordinates s n).comp
    ((LinearMap.mulRight K (indexExteriorWord L)).comp
      (LinearMap.mulLeft K (indexExteriorWord [a,b])))

theorem prefixCorrectionCoordinates_state (u v : ι → Fin n) (A B : Finset ι)
    (T : FixedSubsets (PrefixFreePair A B) ((A∩B).card-1))
    (a b : Fin n) (L : List (Fin n)) :
    prefixCorrectionCoordinates (K := K) s n a b L
      (prefixInverseState (fun i => Pi.basisFun K (Fin n) (u i))
        (fun i => Pi.basisFun K (Fin n) (v i)) A B T)=
      totalExteriorPluckerCoordinates s n (indexExteriorWord
        ([a,b]++prefixSingletonWord u v A B++
          matchingIndexWord (fun i : PrefixFreePair A B => u i.val)
            (fun i : PrefixFreePair A B => v i.val) T.val++L)) := by
  simp only [prefixCorrectionCoordinates,LinearMap.comp_apply,LinearMap.mulRight_apply,
    LinearMap.mulLeft_apply,←prefixInverseState_word u v A B T,
    indexExteriorWord_append,mul_assoc]

/-- A coefficient-independent transport lemma. Its numerical premise is
the actual pair-weight inequality for the displayed support state; the two
canonical applications below and in the reflected branch prove that premise. -/
theorem prefix_state_correction_lower_of_cost
    (u v : Fin h → Fin n) (A B : Finset (Fin h))
    (hdegree : A.card+B.card=h+1)
    (T : FixedSubsets (PrefixFreePair A B) ((A∩B).card-1))
    (w : Fin n → ℕ) (a b : Fin n) (L : List (Fin n))
    (hs : (A.toList.map u++B.toList.map v++L).length=s)
    (hcost : (∑ i∈T.val,(w (u i.val)+w (v i.val)))+(w a+w b)<
      ∑ i∈A∩B,(w (u i)+w (v i))) :
    prefixCorrectionCoordinates (K := K) s n a b L
      (prefixInverseState (fun i => Pi.basisFun K (Fin n) (u i))
        (fun i => Pi.basisFun K (Fin n) (v i)) A B T) ∈
      lowerWeightSpace (pluckerVertexWeight w)
        (((A.toList.map u++B.toList.map v++L).map w).sum) := by
  let S := prefixSingletonWord u v A B
  let W := [a,b]++S++matchingIndexWord
    (fun i : PrefixFreePair A B => u i.val)
    (fun i : PrefixFreePair A B => v i.val) T.val++L
  have hcounts := prefix_occupancy_counts A B
    (by simpa only [Fintype.card_fin] using hdegree)
  have hA := Finset.card_le_univ A
  have hB := Finset.card_le_univ B
  simp only [Finset.card_univ,Fintype.card_fin] at hA hB
  have hh : 0<h := by omega
  have hlen : W.length=s := by
    have hsingle : S.length+2*T.val.card=h-1 := by
      simpa only [S,prefixSingletonWord,List.length_append,List.length_map,
        Finset.length_toList,T.property,Fintype.card_fin] using hcounts.2.2
    simp only [List.length_append,List.length_map,Finset.length_toList] at hs
    simp only [W,List.length_append,List.length_cons,List.length_nil,matchingIndexWord_length]
    omega
  rw [prefixCorrectionCoordinates_state]
  apply totalExteriorPluckerCoordinates_word_lower w W hlen
  have hlead := prefix_selection_word_weight u v A B w
  simp only [W,List.map_append,List.sum_append,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,matchingIndexWord_weight]
  simp only [List.map_append,List.sum_append] at hlead
  dsimp only [S]
  omega

theorem oddPrefix_state_correction_lower (hk : h≤k) (A B : Finset (Fin h))
    (hdegree : A.card+B.card=h+1)
    (T : FixedSubsets (PrefixFreePair A B) ((A∩B).card-1))
    (j : Fin k) (hj : h≤j.val) (L : List (Fin (2*k+1)))
    (hs : (A.toList.map (oddPrefixLeft hk)++
      B.toList.map (oddPrefixRight hk)++L).length=s) :
    prefixCorrectionCoordinates (K := K) s (2*k+1)
      (oddPathFirstLeft j) (oddPathMiddle j) L
      (prefixInverseState
        (fun i => Pi.basisFun K (Fin (2*k+1)) (oddPrefixLeft hk i))
        (fun i => Pi.basisFun K (Fin (2*k+1)) (oddPrefixRight hk i)) A B T) ∈
      lowerWeightSpace (pluckerVertexWeight (oddNatVertexWeight k))
        (((A.toList.map (oddPrefixLeft hk)++
          B.toList.map (oddPrefixRight hk)++L).map (oddNatVertexWeight k)).sum) := by
  let S := prefixSingletonWord (oddPrefixLeft hk) (oddPrefixRight hk) A B
  let W := [oddPathFirstLeft j,oddPathMiddle j]++S++
    matchingIndexWord (fun i : PrefixFreePair A B => oddPrefixLeft hk i.val)
      (fun i : PrefixFreePair A B => oddPrefixRight hk i.val) T.val++L
  have hcounts := prefix_occupancy_counts A B
    (by simpa only [Fintype.card_fin] using hdegree)
  have hA := Finset.card_le_univ A
  have hB := Finset.card_le_univ B
  simp only [Finset.card_univ,Fintype.card_fin] at hA hB
  have hh : 0<h := by omega
  have hlen : W.length=s := by
    have hsingle : S.length+2*T.val.card=h-1 := by
      simpa only [S,prefixSingletonWord,List.length_append,List.length_map,
        Finset.length_toList,T.property,Fintype.card_fin] using hcounts.2.2
    simp only [List.length_append,List.length_map,Finset.length_toList] at hs
    simp only [W,List.length_append,List.length_cons,List.length_nil,matchingIndexWord_length]
    omega
  rw [prefixCorrectionCoordinates_state]
  apply totalExteriorPluckerCoordinates_word_lower (oddNatVertexWeight k) W hlen
  have hcost := oddPrefix_replacement_cost hk A B hdegree T j hj
  have hlead := prefix_selection_word_weight (oddPrefixLeft hk) (oddPrefixRight hk)
    A B (oddPathVertexWeight k)
  have hz : (W.map (oddPathVertexWeight k)).sum <
      ((A.toList.map (oddPrefixLeft hk)++
        B.toList.map (oddPrefixRight hk)++L).map (oddPathVertexWeight k)).sum := by
    simp only [W,List.map_append,List.sum_append,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,matchingIndexWord_weight]
    simp only [List.map_append,List.sum_append] at hlead
    dsimp only [S]
    omega
  have hc : (((W.map (oddNatVertexWeight k)).sum : ℕ) : ℤ) <
      ((((A.toList.map (oddPrefixLeft hk)++
        B.toList.map (oddPrefixRight hk)++L).map (oddNatVertexWeight k)).sum : ℕ) : ℤ) := by
    simpa only [wordWeight_nat_cast] using hz
  exact_mod_cast hc

/-- The same strict bound holds for the actual inverse supplied by the
Boolean formula, by linearity on its completely proved support. -/
theorem oddPrefix_supported_correction_lower
    (hk : h≤k) (A B : Finset (Fin h)) (hdegree : A.card+B.card=h+1)
    (j : Fin k) (hj : h≤j.val) (L : List (Fin (2*k+1)))
    (hs : (A.toList.map (oddPrefixLeft hk)++
      B.toList.map (oddPrefixRight hk)++L).length=s)
    (η : ExteriorAlgebra K (Fin (2*k+1) → K))
    (hη : η∈prefixInverseSpace
      (fun i => Pi.basisFun K (Fin (2*k+1)) (oddPrefixLeft hk i))
      (fun i => Pi.basisFun K (Fin (2*k+1)) (oddPrefixRight hk i)) A B) :
    prefixCorrectionCoordinates (K := K) s (2*k+1)
      (oddPathFirstLeft j) (oddPathMiddle j) L η ∈
      lowerWeightSpace (pluckerVertexWeight (oddNatVertexWeight k))
        (((A.toList.map (oddPrefixLeft hk)++
          B.toList.map (oddPrefixRight hk)++L).map (oddNatVertexWeight k)).sum) := by
  exact supported_prefix_transport_lower _ _ A B _ _ _
    (fun T => oddPrefix_state_correction_lower hk A B hdegree T j hj L hs) η hη

end PaperVerification.AlternatingForms
