module

public import Papers.GraphicalZonotopes.TwoHubPartitionGeometry
public import Papers.GraphicalZonotopes.TwoHubDilation
public import Papers.GraphicalZonotopes.TwoHubGraphMaps
public import Papers.GraphicalZonotopes.FourPartSpectrum
public import Papers.GraphicalZonotopes.LatticeSupport

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset SetFunctionEmbedding
open scoped BigOperators Pointwise
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- An integral graphical extreme function with its genuine affine
dimension. Unlike `LatticeExtremeAt`, this predicate specifies no dilation. -/
def IntegralGraphicalExtremeAt (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ f : SetFunction V,TranslationNormalized f ∧ IntegerValued f ∧
    ExtremeSupermodular f ∧ Graphical G f ∧
    Module.finrank ℝ (vectorSpan ℝ (basePolytope f))=d

theorem LatticeExtremeAt.integralGraphical {G : SimpleGraph V} {d M : ℕ}
    (h : LatticeExtremeAt G d M) : IntegralGraphicalExtremeAt G d := by
  obtain ⟨f,hn,hi,he,hG,hd,hb⟩:=h
  exact ⟨f,hn,hi,he,hG,hd⟩

theorem IntegralGraphicalExtremeAt.embed {G : SimpleGraph V} {H : SimpleGraph W} {d : ℕ}
    (h : IntegralGraphicalExtremeAt G d) (e : V↪W) (hGH : G≤H.comap e) :
    IntegralGraphicalExtremeAt H d := by
  obtain ⟨f,hn,hi,he,hG,hd⟩:=h
  refine ⟨extend e f,extend_translationNormalized e hn,extend_integer e hi,
    extend_extreme e he,extend_graphical e (hG.mono_graph hGH),?_⟩
  rw [finrank_vectorSpan_extend e hn,hd]

theorem IntegralGraphicalExtremeAt.polytope {G : SimpleGraph V} {d : ℕ}
    (h : IntegralGraphicalExtremeAt G d) :
    ∃ Q : Set (V→ℝ),IsFinitePolytope Q ∧ LatticePolytope Q ∧
      MinkowskiIndecomposable Q ∧ IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=d := by
  obtain ⟨f,hn,hi,he,hG,hd⟩:=h
  have hgp : IsGeneralizedPermutahedron (basePolytope f):=⟨f,hn.1,he.2.1,rfl⟩
  exact ⟨basePolytope f,hgp.finitePolytope,hi.basePolytope hn.1 he.2.1,
    he.minkowskiIndecomposable,(isWeakMinkowskiSummand_graphical_iff hn.1 he.2.1).mpr hG,hd⟩

theorem IntegralGraphicalExtremeAt.dimension_le {G : SimpleGraph V} {d : ℕ}
    (h : IntegralGraphicalExtremeAt G d) : d≤maximumIndecomposableDimension G := by
  obtain ⟨Q,hf,hl,hi,hw,hd⟩:=h.polytope
  rw [←hd]
  exact dimension_le_maximum hf hi hw

/-- Extracting the integral normalized support function preserves dimension
and exposes every hypothesis needed to transfer a lattice witness. -/
theorem integralGraphicalExtremeAt_of_polytope {G : SimpleGraph V} {d : ℕ}
    (hdpos : 0<d) {Q : Set (V→ℝ)} (hQ : IsFinitePolytope Q) (hl : LatticePolytope Q)
    (hi : MinkowskiIndecomposable Q) (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G))
    (hd : Module.finrank ℝ (vectorSpan ℝ Q)=d) : IntegralGraphicalExtremeAt G d := by
  obtain ⟨M,hM,R,hR,hRc,hnR,hQR⟩:=hw
  obtain ⟨hfn,hfs,hbody,hgraph,hbound⟩:=actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hRc hnR hM.le hQR
  let f:=lowerSupport Q
  let z:=normalize f
  have hn : TranslationNormalized z:=normalize_translationNormalized hfn
  have hint : IntegerValued z:=(hl.lowerSupport_integerValued hi.1).normalize
  have hzg : Graphical G z:=by
    intro u v huv hnon S hu hv
    rw [delta_normalize f huv hu hv]
    exact hgraph u v huv hnon S hu hv
  have hzd : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=d := by
    rw [vectorSpan_basePolytope_normalize,←hbody]
    exact hd
  have hz : z≠0:=by
    intro he
    rw [he,basePolytope_zero,vectorSpan_singleton,finrank_bot] at hzd
    omega
  have he:=MinkowskiIndecomposable.extremeSupermodular_normalize hfn hfs hz (hbody ▸ hi)
  exact ⟨z,hn,hint,he,hzg,hzd⟩

namespace TwoHub

theorem twoSingleton_card (p b : ℕ) :
    Fintype.card (Σ i : Fin 4,Fin (![1,1,p,b] i))=p+b+2 := by
  simp [Fintype.card_sigma,Fin.sum_univ_succ]
  omega

theorem part_sum (p b : ℕ) : (∑ i : Fin 4,(![1,1,p,b] i))=p+b+2 := by
  simp [Fin.sum_univ_succ]
  omega

theorem part_sup (p b : ℕ) (hp : 1≤p) (hpb : p≤b) :
    univ.sup (![1,1,p,b])=b := by
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    fin_cases i <;> simp <;> omega
  · have h:=le_sup (f:=(![1,1,p,b])) (mem_univ (3 : Fin 4))
    simpa using h

/-- The complete low range is supplied by the already verified four-partite
3-tree spectrum. No finite-parameter enumeration is used. -/
theorem low_range_attainment (p b : ℕ) (hp : 1≤p) (hpb : p≤b) (hb : b≤2*p+1) :
    IntegralGraphicalExtremeAt (twoSingletonGraph p b) (p+b+1) := by
  obtain ⟨Q,hQ,hl,hi,hw,hT,hd⟩:=four_partite_threeTree_dimension_attained (![1,1,p,b])
    (by intro i;fin_cases i <;> simp <;> omega)
  rw [part_sum,part_sup p b hp hpb] at hd
  have he : min (p+b+2-1) (3*(p+b+2-b)-4)=p+b+1:=by omega
  rw [he] at hd
  exact integralGraphicalExtremeAt_of_polytope (by omega) hQ hl hi hw hd

/-- A proper partition with k cells yields an integral witness on exactly
k+p vertices in the last independent part. -/
theorem partition_attainment {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : PartitionData I) :
    IntegralGraphicalExtremeAt
      (twoSingletonGraph (Fintype.card I) (P.cells.card+Fintype.card I))
      (Fintype.card I+P.cells.card+Fintype.card I+1) := by
  have h : IntegralGraphicalExtremeAt (graph (I:=I) (J:=P.Index))
      (Fintype.card I+P.cells.card+Fintype.card I+1) := by
    refine ⟨P.construction,P.construction_normalized,P.construction_integer,
      P.construction_extreme,P.construction_graphical,?_⟩
    have hd:=P.construction_fullDimension
    change Module.finrank ℝ (vectorSpan ℝ (basePolytope P.construction))=
      Fintype.card (Hub I⊕P.Index)-1 at hd
    rw [hd]
    simp only [Hub,PartitionData.Index,Fintype.card_sum,Fintype.card_bool,Fintype.card_coe]
    omega
  let e:=graphIso (I:=I) (J:=P.Index)
  have hmap : graph (I:=I) (J:=P.Index)≤
      (twoSingletonGraph (Fintype.card I) (Fintype.card P.Index)).comap e := by
    intro x y hxy
    exact e.map_adj_iff.mpr hxy
  have he:=h.embed e.toEquiv.toEmbedding hmap
  have hcard : Fintype.card P.Index=P.cells.card+Fintype.card I := by
    simp [PartitionData.Index]
  exact Eq.mp (congrArg (fun b : ℕ => IntegralGraphicalExtremeAt
    (twoSingletonGraph (Fintype.card I) b)
    (Fintype.card I+P.cells.card+Fintype.card I+1)) hcard) he

theorem intermediate_attainment (p b : ℕ) (hp : 1≤p)
    (hlo : 2*p+1≤b) (hhi : b≤2^p+p) :
    IntegralGraphicalExtremeAt (twoSingletonGraph p b) (p+b+1) := by
  letI : Nonempty (Fin p):=⟨⟨0,hp⟩⟩
  obtain ⟨F,hF,hcard,huses,hproper⟩:=CubePartition.exists_proper_card (I:=Fin p) (b-p)
    (by simp only [Fintype.card_fin];omega) (by simp only [Fintype.card_fin];omega)
  let P : PartitionData (Fin p):=⟨F,hF,hproper,huses⟩
  have he:=partition_attainment P
  have hbc : F.card+p=b:=by omega
  have hd : p+F.card+p+1=p+b+1:=by omega
  have hdim : Fintype.card (Fin p)+P.cells.card+Fintype.card (Fin p)+1=p+b+1 := by
    simpa only [Fintype.card_fin,P] using hd
  have hpars : (Fintype.card (Fin p),P.cells.card+Fintype.card (Fin p))=(p,b) := by
    simp only [Fintype.card_fin,P,hbc]
  rw [hdim] at he
  exact Eq.mp (congrArg (fun x : ℕ×ℕ => IntegralGraphicalExtremeAt
    (twoSingletonGraph x.1 x.2) (p+b+1)) hpars) he

/-- Enlarging the last part preserves the saturated integral witness by
adding zero coordinates to its support function. -/
theorem saturated_attainment (p b : ℕ) (hp : 1≤p) (hb : 2^p+p≤b) :
    IntegralGraphicalExtremeAt (twoSingletonGraph p b) (2^p+2*p+1) := by
  have h:=(exponential_lattice_summand p hp).integralGraphical
  let e₀:=vertexEmbedding (Function.Embedding.refl (Fin p)) (Fin.castLEEmb hb)
  let e₁:=(finGraphIso p (2^p+p)).symm.toEquiv.toEmbedding
  let e₂:=(finGraphIso p b).toEquiv.toEmbedding
  let e:=e₁.trans (e₀.trans e₂)
  have hmap : twoSingletonGraph p (2^p+p)≤(twoSingletonGraph p b).comap e := by
    intro x y hxy
    have h₁ : (graph (I:=Fin p) (J:=Fin (2^p+p))).Adj (e₁ x) (e₁ y) :=
      (finGraphIso p (2^p+p)).symm.map_adj_iff.mpr hxy
    have h₀:=graph_le_comap (Function.Embedding.refl (Fin p)) (Fin.castLEEmb hb) h₁
    exact (finGraphIso p b).map_adj_iff.mpr h₀
  exact h.embed e hmap

theorem ordered_attainment (p b : ℕ) (hp : 1≤p) (hpb : p≤b) :
    IntegralGraphicalExtremeAt (twoSingletonGraph p b) (min (p+b+1) (2^p+2*p+1)) := by
  by_cases hb : b≤2*p+1
  · have he : p+b+1≤2^p+2*p+1 := by
      have hpow : p+1≤2^p:=Nat.lt_two_pow_self (n:=p)
      omega
    rw [min_eq_left he]
    exact low_range_attainment p b hp hpb hb
  · by_cases hs : b≤2^p+p
    · rw [min_eq_left (by omega)]
      exact intermediate_attainment p b hp (by omega) hs
    · rw [min_eq_right (by omega)]
      exact saturated_attainment p b hp (by omega)

theorem all_attainment (p b : ℕ) (hp : 1≤p) (hb : 1≤b) :
    IntegralGraphicalExtremeAt (twoSingletonGraph p b)
      (min (p+b+1) (2^(min p b)+2*min p b+1)) := by
  by_cases hpb : p≤b
  · simpa only [min_eq_left hpb] using ordered_attainment p b hp hpb
  · have hbp : b≤p:=by omega
    have h:=ordered_attainment b p hb hbp
    let e:=twoSingletonSwap b p
    have hmap : twoSingletonGraph b p≤(twoSingletonGraph p b).comap e:=by
      intro x y hxy
      exact e.map_adj_iff.mpr hxy
    have he:=h.embed e.toEquiv.toEmbedding hmap
    simpa only [min_eq_right hbp,Nat.add_comm b p] using he

end TwoHub
end GraphicalZonotopes
