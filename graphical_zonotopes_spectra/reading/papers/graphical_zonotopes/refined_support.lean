module

public import Papers.GraphicalZonotopes.RefinedTriangleComponents
public import Papers.GraphicalZonotopes.SupportGeometry
public import Papers.GraphicalZonotopes.GraphDefinitions
public import Papers.GraphicalZonotopes.SummandEdges

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace RefinedTriangleComponents
open Finset PositiveDecomposition
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [LinearOrder V]

private theorem adjusted_zero_function : adjusted (0 : SetFunction V)=0 := by
  have ha : allocation (0 : SetFunction V)=0 := by
    funext C
    by_cases hC : C.card=2
    · obtain ⟨u,v,huv,rfl⟩ := card_eq_two.mp hC
      rw [allocation_pair _ huv]
      have hm : minimumSlack (0 : SetFunction V) u v=0 :=
        minimumSlack_eq_zero (by intros; simp [delta])
      simp [hm]
    · exact allocation_zero _ hC
  rw [adjusted,ha]
  change 0+zetaLinear 0=0
  simp

theorem higher_right_dependsOn {y : SetFunction V}
    (hdegree : ∀ C,y C≠0 → C.card≤4) (T : Finset V) :
    DependsOn (higherClass y (classOf y) (Sum.inr T)) T := by
  apply zeta_dependsOn
  intro C hC
  by_contra he
  obtain ⟨hc,ha,hyC⟩ := classCoefficients_nonzero he
  obtain ⟨h3,rfl⟩ := right_class_is_triangle hdegree hc hyC ha
  exact hC Subset.rfl

theorem higher_right_zero_of_card_ne_three {y : SetFunction V}
    (hdegree : ∀ C,y C≠0 → C.card≤4) {T : Finset V} (hT : T.card≠3) :
    higherClass y (classOf y) (Sum.inr T)=0 := by
  apply (zeta_eq_zero_iff _).mpr
  funext C
  by_contra he
  obtain ⟨hc,ha,hyC⟩ := classCoefficients_nonzero he
  obtain ⟨h3,rfl⟩ := right_class_is_triangle hdegree hc hyC ha
  exact hT h3

theorem higher_left_dependsOn {y : SetFunction V}
    (hdegree : ∀ C,y C≠0 → C.card≤4) (a : Component y) :
    DependsOn (higherClass y (classOf y) (Sum.inl a)) ((family y).biUnion id) := by
  apply zeta_dependsOn
  intro C hC
  by_contra he
  exact hC (left_coefficients_subset_vertices hdegree a he)

def pieces (y : SetFunction V) : (ClassIndex y ⊕ Finset V) → SetFunction V :=
  Sum.elim (fun a => adjusted (higherClass y (classOf y) a))
    (fun C => residual y (higherClass y (classOf y)) C • setMonomial C)

theorem pieces_positive {y : SetFunction V} (hy : y ∅=0 ∧ ∀ v,y {v}=0)
    (hdegree : ∀ C,y C≠0 → C.card≤4) (hs : Supermodular (zeta y)) :
    (∀ i,TranslationNormalized (pieces y i) ∧ Supermodular (pieces y i)) ∧
    (∑ i,pieces y i)=zeta y := by
  classical
  have hytop : CliqueSupported (⊤ : SimpleGraph V) y := by
    refine ⟨hy.1,hy.2,?_⟩
    intro C u v hu hv huv hnon
    exact False.elim (hnon huv)
  obtain ⟨hp,hr,hrn,hrs,he⟩ := compatible_class_decomposition y hytop hs
    (classOf y) (classOf_compatible hdegree)
  constructor
  · intro i
    cases i with
    | inl a => exact ⟨(hp a).1,(hp a).2.1⟩
    | inr C =>
      refine ⟨?_,(setMonomial_supermodular C).smul (hr C)⟩
      by_cases hC : C.card=2
      · have hn : TranslationNormalized (setMonomial C) := by
          refine ⟨setMonomial_normalized (card_pos.mp (by omega)),?_⟩
          intro v
          have hnot : ¬C⊆{v} := by
            intro hsub
            have hcard:=card_le_card hsub
            simp only [card_singleton] at hcard
            omega
          simp [setMonomial,hnot]
        exact ⟨by change _*setMonomial C ∅=0; rw [hn.1,mul_zero],
          fun v => by change _*setMonomial C {v}=0; rw [hn.2 v,mul_zero]⟩
      · have hz := residual_zero y (higherClass y (classOf y)) hC
        simp only [pieces,Sum.elim_inr,hz,zero_smul]
        exact ⟨rfl,fun _ => rfl⟩
  · rw [Fintype.sum_sum_type]
    change (∑ a,adjusted (higherClass y (classOf y) a))+
      (∑ C,residual y (higherClass y (classOf y)) C • setMonomial C)=_
    rw [← zeta_eq_sum_monomials]
    exact he

theorem extreme_has_positive_component {n : ℕ} (hn : 4≤n)
    {z : SetFunction (Fin n)} (hz : ExtremeSupermodular z)
    (hfull : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=n-1)
    (hdegree : ∀ C,mobius z C≠0 → C.card≤4) :
    ∃ a : Component (mobius z),∃ t : ℝ,0<t ∧
      adjusted (higherClass (mobius z) (classOf (mobius z)) (Sum.inl a))=t • z ∧
      (family (mobius z)).biUnion id=univ := by
  classical
  let y:=mobius z
  have hy : y ∅=0 ∧ ∀ v,y {v}=0 :=
    (zeta_normalized_iff y).mp (by simpa [y] using hz.1)
  obtain ⟨hp,he⟩ := pieces_positive hy hdegree (by simpa [y] using hz.2.1)
  have hez : (∑ i,pieces y i)=z := by simpa [y] using he
  have hex : ∃ i,pieces y i≠0 := by
    by_contra h
    push_neg at h
    have hzero : (∑ i,pieces y i)=0 := sum_eq_zero (fun i hi => h i)
    exact hz.2.2.1 (hez.symm.trans hzero)
  obtain ⟨i,hi⟩ := hex
  obtain ⟨t,ht,hscale⟩ := hz.finite_summand (pieces y)
    (fun i => (hp i).1) (fun i => (hp i).2) hez hi
  have hsupport : ∀ S,DependsOn (pieces y i) S → S=univ := by
    intro S hS
    rw [hscale] at hS
    exact fullDimension_dependsOn_eq_univ (by omega) hz.1 hz.2.1 hfull
      (DependsOn.of_smul (ne_of_gt ht) hS)
  cases i with
  | inr C =>
    have hC : C.card=2 := by
      by_contra hnot
      have hzC := residual_zero y (higherClass y (classOf y)) hnot
      exact hi (by simp [pieces,hzC])
    have hdep : DependsOn (pieces y (Sum.inr C)) C := (setMonomial_dependsOn C).smul _
    have hcard:=congrArg Finset.card (hsupport C hdep)
    simp only [hC,card_univ,Fintype.card_fin] at hcard
    omega
  | inl c =>
    cases c with
    | inr T =>
      have hT : T.card=3 := by
        by_contra hnot
        have hzero:=higher_right_zero_of_card_ne_three hdegree hnot
        exact hi (by simp only [y,pieces,Sum.elim_inl,hzero,adjusted_zero_function])
      have hdep := PositiveDecomposition.DependsOn.adjusted
        (higher_right_dependsOn hdegree T)
      have hcard:=congrArg Finset.card (hsupport T hdep)
      simp only [hT,card_univ,Fintype.card_fin] at hcard
      omega
    | inl a =>
      have hdep := PositiveDecomposition.DependsOn.adjusted
        (higher_left_dependsOn hdegree a)
      exact ⟨a,t,ht,hscale,hsupport _ hdep⟩

theorem actualRootEdge_of_nonzero_coefficient {z : SetFunction V}
    (hn : Normalized z) (hs : Supermodular z) {C : Finset V}
    (hC : mobius z C≠0) {u v : V} (huv : u≠v) (hu : u∈C) (hv : v∈C) :
    ActualRootEdge (basePolytope z) u v := by
  by_contra he
  have hzero : ∀ S : Finset V,u∉S → v∉S → delta z u v S=0 := by
    intro S hSu hSv
    apply le_antisymm _ (hs.elemental u v huv S hSu hSv)
    by_contra h
    exact he (exposedSegment_of_positive_delta hn hs huv hSu hSv (lt_of_not_ge h))
  have hcoeff := (nonedge_coefficients_zero_iff (mobius z) huv).mp
    (by simpa only [zeta_mobius] using hzero) C hu hv
  exact hC hcoeff

theorem actualRootEdge_of_graphical {z : SetFunction V} {G : SimpleGraph V}
    (hn : Normalized z) (hs : Supermodular z) (hG : Graphical G z)
    {u v : V} (h : ActualRootEdge (basePolytope z) u v) : G.Adj u v := by
  obtain ⟨a,ha,R,_,_,_,he⟩ := (isWeakMinkowskiSummand_graphical_iff hn hs).mpr hG
  exact basePolytope_summand_actualRootEdge hn hs G ha.le R he h

/-- Corollary4.4: for a full-dimensional extreme function in a K5-free graph,
the complete nonzero four-coefficient family is nonempty and triangle
connected, covers every vertex, and has precisely the actual direction graph
as its edge union. No zero tetrahedron is added to this family. -/
theorem full_refined_support {n : ℕ} (hn : 4≤n) {G : SimpleGraph (Fin n)}
    (hG : G.CliqueFree 5) {z : SetFunction (Fin n)} (hz : ExtremeSupermodular z)
    (hgraph : Graphical G z)
    (hfull : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=n-1) :
    (family (mobius z)).Nonempty ∧
      (tetrahedronGraph (family (mobius z))).Preconnected ∧
      (family (mobius z)).biUnion id=univ ∧
      actualDirectionGraph (basePolytope z)=edgeGraph (mobius z) := by
  classical
  let y:=mobius z
  have hy : CliqueSupported G y := (mobius_cliqueSupported_iff G z).mpr ⟨hz.1,hgraph⟩
  have hdegree : ∀ C,y C≠0 → C.card≤4 := fun C hC => nonzero_card_le_four hG hy hC
  obtain ⟨a,t,ht,hscale,hcover⟩ := extreme_has_positive_component hn hz hfull hdegree
  have hcomp := same_component_of_positive_piece a (ne_of_gt ht)
    (by simpa only [zeta_mobius] using hscale)
  have hconnected : (tetrahedronGraph (family y)).Preconnected := by
    intro C D
    exact SimpleGraph.ConnectedComponent.exact ((hcomp C).trans (hcomp D).symm)
  have hne : (family y).Nonempty := by
    have hm : (⟨0,by omega⟩ : Fin n)∈(family y).biUnion id := by
      rw [hcover]
      exact mem_univ _
    obtain ⟨C,hC,hv⟩ := mem_biUnion.mp hm
    exact ⟨C,hC⟩
  refine ⟨hne,hconnected,hcover,?_⟩
  have hpiece : Graphical (edgeGraph y)
      (adjusted (higherClass y (classOf y) (Sum.inl a))) :=
    adjusted_graphical ((cliqueSupported_iff _ _).mp (left_coefficients_supported hdegree a)).2
  have hzedge : Graphical (edgeGraph y) z := by
    intro u v huv hnon S hu hv
    have h:=hpiece u v huv hnon S hu hv
    rw [hscale,delta_smul] at h
    exact mul_left_cancel₀ (ne_of_gt ht) (by simpa using h)
  ext u v
  constructor
  · intro h
    exact actualRootEdge_of_graphical hz.1.1 hz.2.1 hzedge h
  · rintro ⟨huv,C,hC,hu,hv⟩
    exact actualRootEdge_of_nonzero_coefficient hz.1.1 hz.2.1
      ((mem_family y C).mp hC).2 huv hu hv

end RefinedTriangleComponents
end GraphicalZonotopes
