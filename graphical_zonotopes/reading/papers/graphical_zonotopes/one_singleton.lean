module

public import Papers.GraphicalZonotopes.DoubledDeletionKernel
public import Papers.GraphicalZonotopes.GraphFunctionRestriction
public import Papers.GraphicalZonotopes.DoubledGeometry

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset BooleanFourier
open scoped Pointwise
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev SingletonVertices (a : I) := VertexDeletion.Retained (a,(1 : Fin 2))

def singletonGraph (a : I) : SimpleGraph (SingletonVertices a) :=
  (graph I).comap (VertexDeletion.embedding (a,(1 : Fin 2)))

abbrev singletonFunction (a : I) (z : SetFunction (I×Fin 2)) : SetFunction (SingletonVertices a) :=
  SetFunctionEmbedding.restrict (VertexDeletion.embedding (a,(1 : Fin 2))) z

theorem singletonGraph_connected (hI : 2≤Fintype.card I) (a : I) :
    (singletonGraph a).Connected := by
  letI : Nonempty (SingletonVertices a) := ⟨⟨(a,0),by simp⟩⟩
  refine ⟨?_⟩
  intro u v
  by_cases huv : u.1.1≠v.1.1
  · exact SimpleGraph.Adj.reachable huv
  · have hp : u.1.1=v.1.1 := not_not.mp huv
    obtain ⟨i,hi,hn⟩ := exists_mem_notMem_of_card_lt_card
      (show ({u.1.1} : Finset I).card<(univ : Finset I).card by simp only [card_singleton,card_univ]; omega)
    have hiu : i≠u.1.1 := by simpa using hn
    let w : SingletonVertices a := ⟨(i,0),by simp⟩
    exact (SimpleGraph.Adj.reachable (show (singletonGraph a).Adj u w from Ne.symm hiu)).trans
      (SimpleGraph.Adj.reachable (show (singletonGraph a).Adj w v from by change i≠v.1.1; rwa [← hp]))

theorem singletonGraph_has_edge (hI : 2≤Fintype.card I) (a : I) :
    ∃ u v : SingletonVertices a,(singletonGraph a).Adj u v := by
  obtain ⟨v⟩ := exists_star_vertex hI (a,0)
  have hv : v.1≠(a,1) := by
    intro he
    exact v.2 (congrArg Prod.fst he).symm
  exact ⟨⟨(a,0),by simp⟩,⟨v.1,hv⟩,v.2⟩

theorem singleton_nonzero_slack (hI : 4≤Fintype.card I) (a : I)
    {z : SetFunction (I×Fin 2)} (hphase : CompleteQuadraticRows z)
    {u v : SingletonVertices a} (huv : (singletonGraph a).Adj u v) :
    ∃ S : Finset (SingletonVertices a),u∉S ∧ v∉S ∧
      delta (singletonFunction a z) u v S≠0 := by
  let d : I×Fin 2 := (a,1)
  let e := VertexDeletion.embedding d
  have hadj : (graph I).Adj u.1 v.1 := huv
  have transfer (S : Finset (I×Fin 2)) (hu : u.1∉S) (hv : v.1∉S) (hd : d∉S)
      (hz : delta z u.1 v.1 S≠0) :
      ∃ T : Finset (SingletonVertices a),u∉T ∧ v∉T ∧
        delta (singletonFunction a z) u v T≠0 := by
    have heu : e u=u.1 := rfl
    have hev : e v=v.1 := rfl
    refine ⟨SetFunctionEmbedding.pullSet e S,?_,?_,?_⟩
    · rw [SetFunctionEmbedding.mem_pullSet,heu]
      exact hu
    · rw [SetFunctionEmbedding.mem_pullSet,hev]
      exact hv
    · rw [singletonFunction,SetFunctionEmbedding.delta_restrict,
        VertexDeletion.map_pullSet,erase_eq_of_notMem hd]
      exact hz
  obtain ⟨c,L,hc,hprofile⟩ := hphase u.1 v.1 hadj
  have hc0 : c≠0 := by rcases hc with rfl | rfl <;> norm_num
  by_cases hparts : u.1.1=a ∨ v.1.1=a
  · letI := remaining_nonempty (by omega : 3≤Fintype.card I) u.1 v.1
    have hne := faceFunction_ne_zero (completePhase_isSign hc L)
    obtain ⟨uv,huv'⟩ : ∃ uv,faceFunction (completePhase c L) uv≠0 := by
      by_contra! h
      exact hne (funext h)
    apply transfer (edgeContext u.1 v.1 (coordinateChange.symm uv))
      (left_not_mem_edgeContext _ _ _) (right_not_mem_edgeContext _ _ _) _
      (by rwa [hprofile])
    intro hm
    obtain ⟨w,hw,he⟩ := mem_map.mp hm
    have hwa : w.1.1=a := congrArg Prod.fst he
    rcases hparts with hu | hv
    · exact w.1.2.1 (hwa.trans hu.symm)
    · exact w.1.2.2 (hwa.trans hv.symm)
  · have hparts' : u.1.1≠a ∧ v.1.1≠a := not_or.mp hparts
    let a' : Remaining u.1 v.1 := ⟨a,Ne.symm hparts'.1,Ne.symm hparts'.2⟩
    letI := remaining_deleted_nonempty hI u.1 v.1 a'
    have hne := faceFunction_ne_zero (slicePhase_isSign a' hc L false)
    obtain ⟨uv,huv'⟩ : ∃ uv,faceFunction (slicePhase a' c L false) uv≠0 := by
      by_contra! h
      exact hne (funext h)
    apply transfer (edgeContext u.1 v.1 (coordinateChange.symm (slicedPair a' false uv)))
      (left_not_mem_edgeContext _ _ _) (right_not_mem_edgeContext _ _ _)
      (missing_one_not_mem_edge_slice _ _ a' false uv)
    rw [hprofile,slicedPair,faceFunction_slice]
    exact huv'

theorem singleton_extreme (hI : 4≤Fintype.card I) (a : I)
    {z : SetFunction (I×Fin 2)} (hzn : TranslationNormalized z) (hzs : Supermodular z)
    (hzG : Graphical (graph I) z) (hphase : CompleteQuadraticRows z)
    (hfour : ∀ C : Finset (I×Fin 2),C.card=4 → (graph I).IsClique C → mobius z C≠0) :
    ExtremeSupermodular (singletonFunction a z) := by
  have hn := SetFunctionEmbedding.restrict_translationNormalized (VertexDeletion.embedding (a,(1 : Fin 2))) hzn
  have hs := SetFunctionEmbedding.restrict_supermodular (VertexDeletion.embedding (a,(1 : Fin 2))) hzs
  have hne : singletonFunction a z≠0 := by
    obtain ⟨u,v,huv⟩ := singletonGraph_has_edge (by omega : 2≤Fintype.card I) a
    obtain ⟨S,hu,hv,hd⟩ := singleton_nonzero_slack hI a hphase huv
    intro he
    rw [he] at hd
    exact hd (by simp [delta])
  apply extremeSupermodular_of_tightEquations hn hs hne
  exact one_singleton_tight_kernel hI a hzn hzG hphase hfour

def singletonPolytope (a : I) : Set (SingletonVertices a → ℝ) :=
  basePolytope (singletonFunction a setFunction)

def singletonComplementPolytope (a : I) : Set (SingletonVertices a → ℝ) :=
  basePolytope (singletonFunction a complementFunction)

theorem singleton_pair_sum (a : I) :
    singletonPolytope a+singletonComplementPolytope a=graphicalZonotope (singletonGraph a) := by
  let e := VertexDeletion.embedding (a,(1 : Fin 2))
  have hn := SetFunctionEmbedding.restrict_translationNormalized e setFunction_translationNormalized
  have hn' := SetFunctionEmbedding.restrict_translationNormalized e complementFunction_translationNormalized
  have hs := SetFunctionEmbedding.restrict_supermodular e setFunction_supermodular
  have hs' := SetFunctionEmbedding.restrict_supermodular e complementFunction_supermodular
  rw [singletonPolytope,singletonComplementPolytope,← basePolytope_add hn.1 hn'.1 hs hs']
  have he : singletonFunction a setFunction+singletonFunction a complementFunction=
      graphFunction (singletonGraph a) := by
    rw [singletonFunction,singletonFunction,← SetFunctionEmbedding.restrict_add]
    rw [show setFunction+complementFunction=graphFunction (graph I) by unfold complementFunction; abel]
    exact SetFunctionEmbedding.graphFunction_restrict e (graph I)
  rw [he,baseGraphFunction_eq_graphicalZonotope]

/-- Corollary9.10 for an arbitrary finite part set and a specified singleton
part. The two summands are the actual restricted lower base polytopes. -/
theorem one_singleton_decomposition (hI : 4≤Fintype.card I) (a : I) :
    LatticePolytope (singletonPolytope a) ∧
    LatticePolytope (singletonComplementPolytope a) ∧
    MinkowskiIndecomposable (singletonPolytope a) ∧
    MinkowskiIndecomposable (singletonComplementPolytope a) ∧
    FullDimension (singletonPolytope a) ∧ FullDimension (singletonComplementPolytope a) ∧
    singletonPolytope a+singletonComplementPolytope a=graphicalZonotope (singletonGraph a) ∧
    actualDirectionGraph (singletonPolytope a)=singletonGraph a ∧
    actualDirectionGraph (singletonComplementPolytope a)=singletonGraph a ∧
    BooleanElemental (singletonPolytope a) ∧ BooleanElemental (singletonComplementPolytope a) := by
  let e := VertexDeletion.embedding (a,(1 : Fin 2))
  have hn := SetFunctionEmbedding.restrict_translationNormalized e setFunction_translationNormalized
  have hn' := SetFunctionEmbedding.restrict_translationNormalized e complementFunction_translationNormalized
  have hs := SetFunctionEmbedding.restrict_supermodular e setFunction_supermodular
  have hs' := SetFunctionEmbedding.restrict_supermodular e complementFunction_supermodular
  have hQ : MinkowskiIndecomposable (singletonPolytope a) :=
    (singleton_extreme hI a setFunction_translationNormalized setFunction_supermodular
      setFunction_graphical setFunction_completeQuadraticRows
      (fun C hc hC => mobius_setFunction_four_ne_zero hc hC)).minkowskiIndecomposable
  have hR : MinkowskiIndecomposable (singletonComplementPolytope a) :=
    (singleton_extreme hI a complementFunction_translationNormalized complementFunction_supermodular
      complementFunction_graphical complementFunction_completeQuadraticRows
      (fun C hc hC => mobius_complementFunction_four_ne_zero hc hC)).minkowskiIndecomposable
  have hconn := singletonGraph_connected (by omega : 2≤Fintype.card I) a
  have hslack {u v : SingletonVertices a} (h : (singletonGraph a).Adj u v) :=
    singleton_nonzero_slack hI a setFunction_completeQuadraticRows h
  have hslack' {u v : SingletonVertices a} (h : (singletonGraph a).Adj u v) :=
    singleton_nonzero_slack hI a complementFunction_completeQuadraticRows h
  have hsum := singleton_pair_sum a
  refine ⟨(SetFunctionEmbedding.integerValued_restrict e setFunction_integerValued).basePolytope hn.1 hs,
    (SetFunctionEmbedding.integerValued_restrict e complementFunction_integerValued).basePolytope hn'.1 hs',
    hQ,hR,finrank_vectorSpan_eq_of_connected_slacks hn.1 hs hconn (fun _ _ h => hslack h),
    finrank_vectorSpan_eq_of_connected_slacks hn'.1 hs' hconn (fun _ _ h => hslack' h),hsum,?_,?_,?_,?_⟩
  · ext u v
    constructor
    · apply basePolytope_summand_actualRootEdge hn.1 hs (singletonGraph a)
        (by norm_num : (0 : ℝ)≤1) (singletonComplementPolytope a)
      simpa only [one_smul,singletonPolytope,singletonFunction,e] using hsum
    · intro huv
      obtain ⟨S,hu,hv,hd⟩ := hslack huv
      apply exposedSegment_of_positive_delta hn.1 hs ((singletonGraph a).ne_of_adj huv) hu hv
      exact lt_of_le_of_ne (hs.elemental u v ((singletonGraph a).ne_of_adj huv) S hu hv) (Ne.symm hd)
  · ext u v
    constructor
    · apply basePolytope_summand_actualRootEdge hn'.1 hs' (singletonGraph a)
        (by norm_num : (0 : ℝ)≤1) (singletonPolytope a)
      have hh : singletonComplementPolytope a+singletonPolytope a=graphicalZonotope (singletonGraph a) := by
        rw [add_comm]
        exact hsum
      simpa only [one_smul,singletonComplementPolytope,singletonFunction,e] using hh
    · intro huv
      obtain ⟨S,hu,hv,hd⟩ := hslack' huv
      apply exposedSegment_of_positive_delta hn'.1 hs' ((singletonGraph a).ne_of_adj huv) hu hv
      exact lt_of_le_of_ne (hs'.elemental u v ((singletonGraph a).ne_of_adj huv) S hu hv) (Ne.symm hd)
  · intro u v huv S hu hv
    rw [singletonPolytope,lowerSupport_basePolytope hn.1 hs,
      SetFunctionEmbedding.delta_restrict]
    exact setFunction_boolean (fun he => huv (Subtype.ext he)) (fun hm => hu ((Finset.mem_map' (VertexDeletion.embedding (a,(1 : Fin 2)))).mp hm)) (fun hm => hv ((Finset.mem_map' (VertexDeletion.embedding (a,(1 : Fin 2)))).mp hm))
  · intro u v huv S hu hv
    rw [singletonComplementPolytope,lowerSupport_basePolytope hn'.1 hs',
      SetFunctionEmbedding.delta_restrict]
    have h : BooleanElemental (complementPolytope (I := I)) := complementPolytope_booleanElemental
    rw [BooleanElemental,complementPolytope,
      lowerSupport_basePolytope complementFunction_translationNormalized.1 complementFunction_supermodular] at h
    exact h (e u) (e v) (fun he => huv (Subtype.ext he)) (S.map e)
      (fun hm => hu ((Finset.mem_map' (VertexDeletion.embedding (a,(1 : Fin 2)))).mp hm)) (fun hm => hv ((Finset.mem_map' (VertexDeletion.embedding (a,(1 : Fin 2)))).mp hm))

theorem singleton_dimension (hI : 4≤Fintype.card I) (a : I) :
    Module.finrank ℝ (vectorSpan ℝ (singletonPolytope a))=2*Fintype.card I-2 ∧
    Module.finrank ℝ (vectorSpan ℝ (singletonComplementPolytope a))=2*Fintype.card I-2 := by
  have h := one_singleton_decomposition hI a
  have hQ := h.2.2.2.2.1
  have hR := h.2.2.2.2.2.1
  have hc : Fintype.card (SingletonVertices a)=Fintype.card I*2-1 := by
    rw [card_ne_subtype]
    simp
  change Module.finrank ℝ (vectorSpan ℝ (singletonPolytope a))=
    Fintype.card (SingletonVertices a)-1 at hQ
  change Module.finrank ℝ (vectorSpan ℝ (singletonComplementPolytope a))=
    Fintype.card (SingletonVertices a)-1 at hR
  rw [hc] at hQ hR
  constructor <;> omega

end DoubledParts
end GraphicalZonotopes
