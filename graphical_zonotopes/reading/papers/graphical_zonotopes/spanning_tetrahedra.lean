module

public import Papers.GraphicalZonotopes.CliqueComponents
public import Papers.GraphicalZonotopes.SupportGeometry
public import Papers.GraphicalZonotopes.ConeCorrespondence
public import Papers.GraphicalZonotopes.GraphDefinitions
public import Papers.GraphicalZonotopes.GrowthDegree

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
namespace PositiveDecomposition
variable {V : Type*} [Fintype V] [LinearOrder V]

@[simp] theorem allocation_zero_function : allocation (0 : SetFunction V)=0 := by
  funext C
  by_cases hC : C.card = 2
  · obtain ⟨u,v,huv,rfl⟩ := card_eq_two.mp hC
    rw [allocation_pair _ huv]
    have hm : minimumSlack (0 : SetFunction V) u v=0 :=
      minimumSlack_eq_zero (by intros; simp [delta])
    simp [hm]
  · exact allocation_zero _ hC

@[simp] theorem adjusted_zero : adjusted (0 : SetFunction V)=0 := by
  rw [adjusted,allocation_zero_function]
  change 0+zetaLinear 0=0
  simp

theorem higherClass_right_dependsOn {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y) (T : Finset V) :
    GraphicalZonotopes.DependsOn
      (higherClass y (TriangleComponents.classOf G) (Sum.inr T)) T := by
  apply zeta_dependsOn
  intro C hC
  by_contra he
  obtain ⟨hc,ha,hyC⟩ := classCoefficients_nonzero he
  obtain ⟨h3,rfl⟩ := TriangleComponents.right_class_is_triangle hy hc hyC ha
  exact hC Subset.rfl

theorem higherClass_right_zero_of_card_ne_three {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y) {T : Finset V} (hT : T.card ≠ 3) :
    higherClass y (TriangleComponents.classOf G) (Sum.inr T)=0 := by
  apply (zeta_eq_zero_iff _).mpr
  funext C
  by_contra he
  obtain ⟨hc,ha,hyC⟩ := classCoefficients_nonzero he
  obtain ⟨h3,rfl⟩ := TriangleComponents.right_class_is_triangle hy hc hyC ha
  exact hT h3

theorem higherClass_left_dependsOn {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y) (a : (TriangleComponents.cliqueGraph G).ConnectedComponent) :
    GraphicalZonotopes.DependsOn
      (higherClass y (TriangleComponents.classOf G) (Sum.inl a))
      (TriangleComponents.componentVertices G a) := by
  apply zeta_dependsOn
  intro C hC
  by_contra he
  obtain ⟨hc,ha,hyC⟩ := classCoefficients_nonzero he
  apply hC
  by_cases h3 : C.card = 3
  · exact TriangleComponents.triangle_subset_component h3 ha
  · have h4 : 4 ≤ C.card := by omega
    have hcl : G.IsClique C := by
      intro u hu v hv huv
      by_contra hn
      exact hyC (hy.2.2 C u v hu hv huv hn)
    exact TriangleComponents.higher_subset_component h4 hcl ha

def allPieces (G : SimpleGraph V) (y : SetFunction V) :
    (TriangleComponents.ComponentIndex G ⊕ Finset V) → SetFunction V :=
  Sum.elim (fun a => adjusted (higherClass y (TriangleComponents.classOf G) a))
    (fun C => residual y (higherClass y (TriangleComponents.classOf G)) C • setMonomial C)

theorem allPieces_positive {G : SimpleGraph V} (y : SetFunction V)
    (hy : CliqueSupported G y) (hs : Supermodular (zeta y)) :
    (∀ i, TranslationNormalized (allPieces G y i) ∧ Supermodular (allPieces G y i)) ∧
    (∑ i, allPieces G y i)=zeta y := by
  classical
  obtain ⟨hp,hr,hrn,hrs,he⟩ := compatible_class_decomposition y hy hs
    (TriangleComponents.classOf G) (TriangleComponents.classOf_compatible hy)
  constructor
  · intro i
    cases i with
    | inl a => exact ⟨(hp a).1,(hp a).2.1⟩
    | inr C =>
      have hnonneg := hr C
      refine ⟨?_,(setMonomial_supermodular C).smul hnonneg⟩
      by_cases hC : C.card = 2
      · have hn : TranslationNormalized (setMonomial C) := by
          refine ⟨setMonomial_normalized (card_pos.mp (by omega)),?_⟩
          intro v
          have hnot : ¬ C ⊆ {v} := by
            intro hsub
            have hcard := card_le_card hsub
            simp only [card_singleton] at hcard
            omega
          simp [setMonomial,hnot]
        exact ⟨by change _*setMonomial C ∅=0; rw [hn.1,mul_zero],
          fun v => by change _*setMonomial C {v}=0; rw [hn.2 v,mul_zero]⟩
      · have hz := residual_zero y (higherClass y (TriangleComponents.classOf G)) hC
        simp only [allPieces,Sum.elim_inr,hz,zero_smul]
        exact ⟨rfl,fun _ => rfl⟩
  · rw [Fintype.sum_sum_type]
    change (∑ a,adjusted (higherClass y (TriangleComponents.classOf G) a))+
      (∑ C,residual y (higherClass y (TriangleComponents.classOf G)) C • setMonomial C)=_
    rw [← zeta_eq_sum_monomials]
    exact he

end PositiveDecomposition

theorem graphical_actualDirectionGraph {V : Type*} [Fintype V] [DecidableEq V]
    {z : SetFunction V} (hn : Normalized z) (hs : Supermodular z) :
    Graphical (actualDirectionGraph (basePolytope z)) z := by
  intro u v huv hnon S hu hv
  have hnonneg := hs.elemental u v huv S hu hv
  apply le_antisymm _ hnonneg
  by_contra h
  have hpos : 0 < delta z u v S := lt_of_not_ge h
  exact hnon (exposedSegment_of_positive_delta hn hs huv hu hv hpos)

/-- Lemma4.3: the tetrahedral component is constructed from the actual
positive decomposition. No connectivity or coefficient-sign hypothesis has
been added to the indecomposable polytope. -/
theorem ExtremeSupermodular.spanning_tetrahedra {n : ℕ} (hn : 4 ≤ n)
    {z : SetFunction (Fin n)} (hz : ExtremeSupermodular z)
    (hfull : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=n-1)
    {G : SimpleGraph (Fin n)} (hG : Graphical G z) :
    ∃ F : Finset (Finset (Fin n)), F.Nonempty ∧
      (∀ C ∈ F,C.card=4 ∧ G.IsClique C) ∧
      (tetrahedronGraph F).Preconnected ∧ F.biUnion id=univ := by
  classical
  let y := mobius z
  have hy : CliqueSupported G y := (mobius_cliqueSupported_iff G z).mpr ⟨hz.1,hG⟩
  have hys : Supermodular (zeta y) := by simpa [y] using hz.2.1
  obtain ⟨hp,he⟩ := PositiveDecomposition.allPieces_positive y hy hys
  have hez : (∑ i,PositiveDecomposition.allPieces G y i)=z := by simpa [y] using he
  have hex : ∃ i,PositiveDecomposition.allPieces G y i ≠ 0 := by
    by_contra h
    push_neg at h
    have hzero : (∑ i,PositiveDecomposition.allPieces G y i)=0 :=
      sum_eq_zero (fun i hi => h i)
    exact hz.2.2.1 (hez.symm.trans hzero)
  obtain ⟨i,hi⟩ := hex
  obtain ⟨a,ha,hscale⟩ := hz.finite_summand (PositiveDecomposition.allPieces G y)
    (fun i => (hp i).1) (fun i => (hp i).2) hez hi
  have hsupport : ∀ S, DependsOn (PositiveDecomposition.allPieces G y i) S → S=univ := by
    intro S hS
    rw [hscale] at hS
    exact fullDimension_dependsOn_eq_univ (by omega) hz.1 hz.2.1 hfull
      (DependsOn.of_smul (ne_of_gt ha) hS)
  cases i with
  | inr C =>
    have hC : C.card=2 := by
      by_contra hnot
      have hzC := PositiveDecomposition.residual_zero y
        (PositiveDecomposition.higherClass y (TriangleComponents.classOf G)) hnot
      exact hi (by simp [PositiveDecomposition.allPieces,hzC])
    have hdep : DependsOn (PositiveDecomposition.allPieces G y (Sum.inr C)) C :=
      (setMonomial_dependsOn C).smul _
    have hcard := congrArg Finset.card (hsupport C hdep)
    simp only [hC,card_univ,Fintype.card_fin] at hcard
    omega
  | inl c =>
    cases c with
    | inr T =>
      have hT : T.card=3 := by
        by_contra hnot
        have hzero := PositiveDecomposition.higherClass_right_zero_of_card_ne_three hy hnot
        apply hi
        change PositiveDecomposition.adjusted
          (PositiveDecomposition.higherClass y (TriangleComponents.classOf G)
            (Sum.inr T)) = 0
        exact (congrArg PositiveDecomposition.adjusted hzero).trans
          PositiveDecomposition.adjusted_zero
      have hdep := PositiveDecomposition.DependsOn.adjusted
        (PositiveDecomposition.higherClass_right_dependsOn hy T)
      have hcard := congrArg Finset.card (hsupport T hdep)
      simp only [hT,card_univ,Fintype.card_fin] at hcard
      omega
    | inl c =>
      have hdep := PositiveDecomposition.DependsOn.adjusted
        (PositiveDecomposition.higherClass_left_dependsOn hy c)
      have hcover := hsupport (TriangleComponents.componentVertices G c) hdep
      refine ⟨TriangleComponents.componentFamily G c,?_,?_,
        TriangleComponents.componentFamily_preconnected G c,hcover⟩
      · have hm : (⟨0,by omega⟩ : Fin n) ∈ TriangleComponents.componentVertices G c := by
          rw [hcover]
          exact mem_univ _
        obtain ⟨C,hC,hv⟩ := mem_biUnion.mp hm
        exact ⟨C,hC⟩
      · intro C hC
        have hc := TriangleComponents.mem_componentFamily.mp hC
        exact ⟨hc.1,hc.2.1⟩

theorem ExtremeSupermodular.direction_count_bound {n : ℕ} (hn : 4 ≤ n)
    {z : SetFunction (Fin n)} (hz : ExtremeSupermodular z)
    (hfull : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=n-1) :
    3*n-6 ≤ directionCount (basePolytope z) ∧
      (directionCount (basePolytope z)=3*n-6 →
        IsThreeTree (actualDirectionGraph (basePolytope z))) := by
  obtain ⟨F,hne,hcl,hconn,hcover⟩ := hz.spanning_tetrahedra hn hfull
    (graphical_actualDirectionGraph hz.1.1 hz.2.1)
  simpa [directionCount] using edge_bound_of_connected_tetrahedra _ F hne hcl hconn hcover

theorem ExtremeSupermodular.maximum_degree_bound {n : ℕ} (hn : 4 ≤ n)
    {z : SetFunction (Fin n)} (hz : ExtremeSupermodular z)
    (hfull : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=n-1) :
    min (n-1) 6 ≤ maximumDirectionDegree (basePolytope z) := by
  classical
  obtain ⟨F,hne,hcl,hconn,hcover⟩ := hz.spanning_tetrahedra hn hfull
    (graphical_actualDirectionGraph hz.1.1 hz.2.1)
  simpa [maximumDirectionDegree] using
    maximum_degree_bound_of_connected_tetrahedra _ F hne hcl hconn hcover

end GraphicalZonotopes
