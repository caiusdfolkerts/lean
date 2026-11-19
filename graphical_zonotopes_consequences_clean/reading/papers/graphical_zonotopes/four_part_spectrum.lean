module

public import Papers.GraphicalZonotopes.FourPartSpanning
public import Papers.GraphicalZonotopes.FourPartCapacity
public import Papers.GraphicalZonotopes.ThreeTreeActiveGeometry
public import Papers.GraphicalZonotopes.SeparatorPaperStatements

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators Pointwise
namespace GraphicalZonotopes
open Finset FourColorResource FourPartThreeTreeCounts FourPartSpanning

/-- The restricted dimension invariant agrees with the ordinary-polytope
notion of indecomposability. The required GP presentation is derived from the
actual weak Minkowski sum for each individual candidate. -/
theorem maximumThreeTreeSupportDimension_eq_polytopal {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    maximumThreeTreeSupportDimension G=
      sSup {d : ℕ | ∃ Q : Set (V → ℝ),IsFinitePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
        (∃ S,ThreeTreeOn S (actualDirectionGraph Q)) ∧
        Module.finrank ℝ (vectorSpan ℝ Q)=d} := by
  unfold maximumThreeTreeSupportDimension
  congr 1
  ext d
  constructor
  · rintro ⟨Q,hQ,hi,hw,hT,hd⟩
    refine ⟨Q,hQ,⟨hi.1,?_⟩,hw,hT,hd⟩
    intro P R hP hR he
    exact hi.2 P R hP.compact hR.compact hP.convex hR.convex he
  · rintro ⟨Q,hQ,hi,hw,hT,hd⟩
    obtain ⟨t,ht,R,hR,hRc,hnR,he⟩ := hw
    obtain ⟨hn,hs,hbody,_,_⟩ := actual_summand_lowerSupport
      hQ.compact hQ.convex hi.1 hR hRc hnR ht.le he
    have hgp : IsGeneralizedPermutahedron Q := ⟨lowerSupport Q,hn,hs,hbody⟩
    exact ⟨Q,hQ,(minkowskiIndecomposable_iff_polytopal hgp).mpr hi,
      ⟨t,ht,R,hR,hRc,hnR,he⟩,hT,hd⟩

/-- The color capacity bound applies to the actual support of every real
indecomposable weak summand. Full dimension on that active support is derived. -/
theorem four_partite_threeTree_dimension_bound (a : Fin 4 → ℕ)
    (ha : ∀ i,1≤a i) {Q : Set ((Σ i : Fin 4,Fin (a i)) → ℝ)}
    (hQ : IsFinitePolytope Q) (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope (fourPartite a)))
    {S : Finset (Σ i : Fin 4,Fin (a i))}
    (hT : ThreeTreeOn S (actualDirectionGraph Q)) :
    Module.finrank ℝ (vectorSpan ℝ Q)≤
      min ((∑ i,a i)-1) (3*((∑ i,a i)-univ.sup a)-4) := by
  let o : LinearOrder (Σ i : Fin 4,Fin (a i)) := Separator.finiteVertexOrder _
  letI : LinearOrder (Σ i : Fin 4,Fin (a i)) :=
    { o with
      toDecidableEq := inferInstance
      compare := fun x y => @compareOfLessAndEq _ x y o.toLT (o.toDecidableLT x y) inferInstance
      compare_eq_compareOfLessAndEq := by intros;rfl }
  obtain ⟨t,ht,R,hR,hRc,hnR,he⟩ := hw
  obtain ⟨hfn,hfs,hbody,hgraph,_⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hRc hnR ht.le he
  let f := lowerSupport Q
  let z := normalize f
  have hzn : TranslationNormalized z := normalize_translationNormalized hfn
  have hzs : Supermodular z := hfs.normalize
  have hzg : Graphical (fourPartite a) z := by
    intro u v huv hnon T hu hv
    rw [delta_normalize f huv hu hv]
    exact hgraph u v huv hnon T hu hv
  have hactual : actualDirectionGraph (basePolytope z)=actualDirectionGraph Q := by
    rw [actualDirectionGraph_normalize,← hbody]
  have hTz : ThreeTreeOn S (actualDirectionGraph (basePolytope z)) := by
    rwa [hactual]
  have hne : z≠0 := threeTree_actual_nonzero hzn.1 hzs hTz
  have hz : ExtremeSupermodular z := by
    apply MinkowskiIndecomposable.extremeSupermodular_normalize hfn hfs hne
    rwa [← hbody]
  obtain ⟨hd,hA⟩ := threeTree_actual_dimension_admissible hz hTz
  let c : (Σ i : Fin 4,Fin (a i)) → Fin 4 := fun v => v.1
  have hc : Proper c (actualDirectionGraph (basePolytope z)) := by
    intro u v huv heq
    obtain ⟨huv',T,hu,hv,hd⟩ := (actualRootEdge_iff_nonzero_delta hzn.1 hzs u v).mp huv
    apply hd (hzg u v huv' ?_ T hu hv)
    exact fun h => h heq
  let b : Fin 4 → ℕ := fun i => (S.filter (fun v => c v=i)).card
  have htotal : total b=S.card := sum_color_counts S c
  have hb : Balanced b := by
    constructor
    · obtain ⟨C,hC⟩ := hTz.tetrahedra_nonempty
      have hcard : C.card=4 := (mem_filter.mp hC).2.1
      have hcl : (actualDirectionGraph (basePolytope z)).IsClique C := (mem_filter.mp hC).2.2
      have hCS : C⊆S := hTz.clique_subset_active (by omega) hcl
      intro i
      have hle := card_le_card (filter_subset_filter (p := fun v => c v=i) hCS)
      rw [color_count_tetrahedron hc hcard hcl i] at hle
      exact lt_of_lt_of_le Nat.zero_lt_one hle
    · intro i
      have hcap := capacity_nonnegative hTz hc hA i
      change (0 : ℤ)≤2*(S.card : ℤ)-3*(b i : ℤ)-3 at hcap
      rw [htotal]
      omega
  have hba : ∀ i,b i≤a i := by
    intro i
    have hle := card_le_card (filter_subset_filter (p := fun v => c v=i) (subset_univ S))
    change b i≤colorSize c i at hle
    simpa only [c,sigma_colorSize] using hle
  have hbound := balanced_dimension_bound (fun i => by have h := ha i;omega) hb hba
  rw [htotal] at hbound
  have hdQ : Module.finrank ℝ (vectorSpan ℝ Q)=S.card-1 := by
    rw [vectorSpan_basePolytope_normalize,← hbody] at hd
    exact hd
  rw [hdQ]
  exact hbound

/-- Optimal balanced subcounts produce a genuine integral polytope whose
actual direction graph is a 3-tree on exactly the constructed active vertices. -/
theorem four_partite_threeTree_dimension_attained (a : Fin 4 → ℕ)
    (ha : ∀ i,1≤a i) :
    ∃ Q : Set ((Σ i : Fin 4,Fin (a i)) → ℝ),
      IsFinitePolytope Q ∧ LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (fourPartite a)) ∧
      (∃ S,ThreeTreeOn S (actualDirectionGraph Q)) ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=
        min ((∑ i,a i)-1) (3*((∑ i,a i)-univ.sup a)-4) := by
  let o : LinearOrder (Σ i : Fin 4,Fin (a i)) := Separator.finiteVertexOrder _
  letI : LinearOrder (Σ i : Fin 4,Fin (a i)) :=
    { o with
      toDecidableEq := inferInstance
      compare := fun x y => @compareOfLessAndEq _ x y o.toLT (o.toDecidableLT x y) inferInstance
      compare_eq_compareOfLessAndEq := by intros;rfl }
  obtain ⟨b,hb,hba,hopt⟩ := optimal_balanced_subcounts a (fun i => by have h := ha i;omega)
  let c : (Σ i : Fin 4,Fin (a i)) → Fin 4 := fun v => v.1
  have hcap : ∀ i,b i≤colorSize c i := by
    intro i
    simpa only [c,sigma_colorSize] using hba i
  obtain ⟨S,G,hT,hA,hc,hcounts⟩ := realize_schedule c (schedule_of_balanced hb) hcap
  have hsize : S.card=total b := by
    rw [← sum_color_counts S c]
    exact sum_congr rfl (fun i _ => hcounts i)
  obtain ⟨f,hf,hint,hd,hactual,hgraph⟩ := admissible_threeTree_active_witness hT hA
  have hgg : Graphical (fourPartite a) f := by
    intro u v huv hnon T hu hv
    exact hgraph u v huv (fun h => hnon (hc u v h)) T hu hv
  have hgp : IsGeneralizedPermutahedron (basePolytope f) := ⟨f,hf.1.1,hf.2.1,rfl⟩
  refine ⟨basePolytope f,hgp.finitePolytope,hint.basePolytope hf.1.1 hf.2.1,
    hf.minkowskiIndecomposable,(isWeakMinkowskiSummand_graphical_iff hf.1.1 hf.2.1).mpr hgg,
    ⟨S,?_⟩,?_⟩
  · rwa [hactual]
  · rw [hd,hsize]
    exact hopt

/-- The exact restricted maximum in Theorem 8.9, including all real weak
summands and without any ambient full-dimension hypothesis. -/
theorem maximum_threeTree_support_fourPartite (a : Fin 4 → ℕ)
    (ha : ∀ i,1≤a i) :
    maximumThreeTreeSupportDimension (fourPartite a)=
      min ((∑ i,a i)-1) (3*((∑ i,a i)-univ.sup a)-4) := by
  let k := min ((∑ i,a i)-1) (3*((∑ i,a i)-univ.sup a)-4)
  let D : Set ℕ := {d | ∃ Q : Set ((Σ i : Fin 4,Fin (a i)) → ℝ),
    IsFinitePolytope Q ∧ MinkowskiIndecomposable Q ∧
    IsWeakMinkowskiSummand Q (graphicalZonotope (fourPartite a)) ∧
    (∃ S,ThreeTreeOn S (actualDirectionGraph Q)) ∧
    Module.finrank ℝ (vectorSpan ℝ Q)=d}
  have hbound : ∀ d∈D,d≤k := by
    rintro d ⟨Q,hQ,hi,hw,⟨S,hT⟩,hd⟩
    rw [← hd]
    exact four_partite_threeTree_dimension_bound a ha hQ hi hw hT
  have hk : k∈D := by
    obtain ⟨Q,hQ,hl,hi,hw,hT,hd⟩ := four_partite_threeTree_dimension_attained a ha
    exact ⟨Q,hQ,hi,hw,hT,hd⟩
  change sSup D=k
  exact le_antisymm (csSup_le ⟨k,hk⟩ hbound) (le_csSup ⟨k,hbound⟩ hk)

/-- Both assertions of the printed Theorem 8.9, with every positive part
size and the actual-support definition of its restricted dimension invariant. -/
theorem four_partite_spanning_threeTrees : Targets.FourPartiteSpanningThreeTrees := by
  intro a ha
  exact ⟨four_partite_spanning_iff a ha,maximum_threeTree_support_fourPartite a ha⟩

end GraphicalZonotopes
