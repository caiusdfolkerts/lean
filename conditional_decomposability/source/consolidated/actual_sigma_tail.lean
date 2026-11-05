module
public import consolidated.actual_rigid_seeds

set_option Elab.async false

section BundlePart0
/- Source: Papers/ActualSigmaTail.lean -/




@[expose] public section
noncomputable section
namespace Papers.PolytopeFourRegularTail
open Set Finset Papers.Polytopes Papers.ActualRigidSeedLimits
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical
variable {n : ℕ}

/-- The actual seven-vertex configuration Σ: two triangles meeting at one
vertex and an edge disjoint from their union. -/
structure SigmaTail (P : ConvexPolytope n) (T : Finset (E n)) where
  center : E n
  left : Finset (E n)
  right : Finset (E n)
  edge : Finset (E n)
  left_subset : left⊆T
  right_subset : right⊆T
  edge_subset : edge⊆T
  left_card : left.card=3
  right_card : right.card=3
  edge_card : edge.card=2
  intersection : left∩right={center}
  disjoint : Disjoint (left∪right) edge
  union : left∪right∪edge=T
  left_rigid : RigidInTail P T left
  right_rigid : RigidInTail P T right
  edge_rigid : RigidInTail P T edge

theorem sigmaTail_of_seven_no_rigid_four
    (P : ConvexPolytope n) (T : Finset (E n)) (hTV : T⊆P.vertices)
    (hcard : T.card=7) (hmin : ∀x∈T,3≤(T.filter (GeneralVertexStep P x)).card)
    (hno : ∀A⊆T,A.card=4→¬RigidInTail P T A) : Nonempty (SigmaTail P T) := by
  let G := smallTailGraph P T hTV
  have hc : Fintype.card T=7 := by simpa only [Fintype.card_coe] using hcard
  have hm (v : T) : 3≤G.degree v := by
    rw [smallTailGraph_degree_eq]
    exact hmin v.val v.property
  obtain ⟨v,A,B,C,hA,hB,hC,hint,hdisj,hunion⟩ :=
    Papers.SevenVertexCover.exists_sigma_clique_cover G hc hm
      (common_neighbors_le_two_of_no_rigid_four P T hTV hno)
      (neighbor_matchings_of_no_rigid_four P T hTV hno)
  let e : T ↪ E n := ⟨Subtype.val,Subtype.val_injective⟩
  have sub (S : Finset T) : S.map e⊆T := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hx
    exact y.property
  have tri (S : Finset T) (hS : G.IsNClique 3 S) : RigidInTail P T (S.map e) := by
    obtain ⟨a,b,c,hab,hac,hbc,hS⟩ := SimpleGraph.is3Clique_iff.mp hS
    rw [hS]
    simp only [Finset.map_insert,Finset.map_singleton]
    exact rigid_triangle hTV a.property b.property c.property hab hac hbc
  have edge : RigidInTail P T (C.map e) := by
    obtain ⟨a,b,hab,hCeq⟩ := Finset.card_eq_two.mp hC.card_eq
    have hstep : G.Adj a b := by
      have hcl := hC.isClique
      rw [hCeq] at hcl
      exact SimpleGraph.isClique_pair.mp (by
        simpa only [Finset.coe_insert,Finset.coe_singleton] using hcl) hab
    rw [hCeq]
    simp only [Finset.map_insert,Finset.map_singleton]
    exact rigid_pair a.property b.property hstep
  have huniv : (Finset.univ : Finset T).map e=T := by
    ext x
    simp only [Finset.mem_map,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨y,rfl⟩; exact y.property
    · intro hx; exact ⟨⟨x,hx⟩,rfl⟩
  refine ⟨{ center := v.val, left := A.map e, right := B.map e, edge := C.map e
            left_subset := sub A, right_subset := sub B, edge_subset := sub C
            left_card := ?_, right_card := ?_, edge_card := ?_
            intersection := ?_, disjoint := ?_, union := ?_
            left_rigid := tri A hA, right_rigid := tri B hB, edge_rigid := edge }⟩
  · simpa only [Finset.card_map] using hA.card_eq
  · simpa only [Finset.card_map] using hB.card_eq
  · simpa only [Finset.card_map] using hC.card_eq
  · rw [←Finset.map_inter,hint,Finset.map_singleton]
    rfl
  · rw [←Finset.map_union]
    exact (Finset.disjoint_map e).mpr hdisj
  · rw [←Finset.map_union,←Finset.map_union,hunion,huniv]

theorem two_cover_or_sigma_of_min_three_card_le_seven
    (P : ConvexPolytope n) (T : Finset (E n)) (hTV : T⊆P.vertices)
    (hcard : T.card≤7) (hmin : ∀x∈T,3≤(T.filter (GeneralVertexStep P x)).card) :
    HasRigidCover P T 2 ∨ Nonempty (SigmaTail P T) := by
  by_cases hc6 : T.card≤6
  · exact Or.inl (rigidCover_two_of_min_three_card_le_six P T hTV hc6 hmin)
  have hc7 : T.card=7 := by omega
  by_cases hlarge : ∃B⊆T,4≤B.card ∧ RigidInTail P T B
  · obtain ⟨B,hBT,hBc,hBR⟩ := hlarge
    obtain ⟨A,hA⟩ := exists_largest_rigid P T
    have hAc : 4≤A.card := hBc.trans (hA.largest B hBT hBR)
    have hc := Finset.card_sdiff_add_card_eq_card hA.subset
    have hres := hA.residual_min_degree hTV 2 hmin
    exact Or.inl ((rigidCover_single (rigid_of_min_two_card_le_three P (T\A)
      (Finset.sdiff_subset.trans hTV) (by omega) hres)).adjoin hA.subset hA.rigid)
  · apply Or.inr
    apply sigmaTail_of_seven_no_rigid_four P T hTV hc7 hmin
    intro A hAT hc hr
    exact hlarge ⟨A,hAT,by omega,hr⟩

/-- Boundary data formulated with rigidity in the full actual graph.
For any given parallel map it immediately gives the paper's homothety pieces. -/
structure GlobalRigidBoundaryPieces (P : ConvexPolytope n) (I : Type*)
    (c e j : I) (z : E n) where
  piece : I→Finset (E n)
  within : ∀i,piece i⊆P.vertices
  cover : ∀x∈P.vertices,∃i,x∈piece i
  rigid : ∀i,RigidInTail P P.vertices (piece i)
  card_le_four : ∀i,(piece i).card≤4
  left_card : (piece c).card≤3
  right_card : (piece e).card≤3
  edge_card : (piece j).card≤2
  left_mem : z∈piece c
  right_mem : z∈piece e
  distinct : c≠e ∧ c≠j ∧ e≠j

theorem SigmaTail.to_global_boundary
    {P : ConvexPolytope n} {T : Finset (E n)} (S : SigmaTail P T)
    (hTV : T⊆P.vertices) (m : ℕ) (R : Fin m→Finset (E n))
    (hR : ∀i,R i⊆P.vertices) (hRc : ∀i,(R i).card≤4)
    (hRrigid : ∀i,RigidInTail P P.vertices (R i))
    (hcover : ∀x∈P.vertices,(∃i,x∈R i) ∨ x∈T) :
    Nonempty (GlobalRigidBoundaryPieces P (Fin m⊕Fin 3)
      (Sum.inr 0) (Sum.inr 1) (Sum.inr 2) S.center) := by
  let piece : Fin m⊕Fin 3→Finset (E n) := Sum.elim R ![S.left,S.right,S.edge]
  have hz : S.center∈S.left∩S.right := by rw [S.intersection];simp
  refine ⟨{ piece := piece, within := ?_, cover := ?_, rigid := ?_
            card_le_four := ?_, left_card := ?_, right_card := ?_, edge_card := ?_
            left_mem := ?_, right_mem := ?_, distinct := by simp }⟩
  · intro i
    rcases i with i | i
    · exact hR i
    · fin_cases i
      · exact S.left_subset.trans hTV
      · exact S.right_subset.trans hTV
      · exact S.edge_subset.trans hTV
  · intro x hx
    rcases hcover x hx with ⟨i,hi⟩ | hxT
    · exact ⟨Sum.inl i,hi⟩
    · rw [←S.union] at hxT
      simp only [Finset.mem_union] at hxT
      rcases hxT with (hxL | hxR) | hxE
      · exact ⟨Sum.inr 0,hxL⟩
      · exact ⟨Sum.inr 1,hxR⟩
      · exact ⟨Sum.inr 2,hxE⟩
  · intro i
    rcases i with i | i
    · exact hRrigid i
    · fin_cases i
      · exact S.left_rigid.mono_tail hTV
      · exact S.right_rigid.mono_tail hTV
      · exact S.edge_rigid.mono_tail hTV
  · intro i
    rcases i with i | i
    · exact hRc i
    · fin_cases i
      · exact S.left_card.le.trans (by omega)
      · exact S.right_card.le.trans (by omega)
      · exact S.edge_card.le.trans (by omega)
  · exact S.left_card.le
  · exact S.right_card.le
  · exact S.edge_card.le
  · exact (Finset.mem_inter.mp hz).1
  · exact (Finset.mem_inter.mp hz).2

end Papers.PolytopeFourRegularTail

end
end
end BundlePart0

