module
public import consolidated.actual_rigid_seeds

set_option Elab.async false

section BundlePart0
/- Source: Papers/ActualRigidFiveSeeds.lean -/



@[expose] public section
noncomputable section
namespace Papers.ActualRigidSeedLimits
open Set Finset Papers.Polytopes Papers.PolytopeFourRegularTail
open Papers.NeighborhoodCounts Papers.ActualRigidity Papers.SmallNeighborComponents
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical BigOperators
variable {n : ℕ}

theorem common_neighbors_le_two_of_no_rigid_five
    (P : ConvexPolytope n) (T : Finset (E n)) (hTV : T ⊆ P.vertices)
    (hno : ∀ A : Finset (E n), A ⊆ T → A.card = 5 → ¬ RigidInTail P T A) :
    ∀ v w : T, w ≠ v →
      localDegree (smallTailGraph P T hTV)
        ((smallTailGraph P T hTV).neighborFinset v) w ≤ 2 := by
  intro v w hwv
  let G := smallTailGraph P T hTV
  by_contra hlarge
  have hthree : 3 ≤ ((G.neighborFinset v).filter (G.Adj w)).card := by
    change ¬ ((G.neighborFinset v).filter (G.Adj w)).card ≤ 2 at hlarge
    omega
  obtain ⟨S,hS,hSc⟩ := Finset.exists_subset_card_eq hthree
  let e : Fin 3 ≃ S := (Fintype.equivFinOfCardEq (by simpa using hSc)).symm
  let a : Fin 3 → T := fun i => (e i).val
  let points : Fin 3 → P.vertices := fun i => vertexOfTail P T hTV (a i)
  have ha : ∀ i, a i ∈ (G.neighborFinset v).filter (G.Adj w) :=
    fun i => hS (e i).property
  have hvEdges : ∀ i, GeneralVertexStep P v.val (points i).val :=
    fun i => (G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp (ha i)).1
  have hwEdges : ∀ i, GeneralVertexStep P w.val (points i).val :=
    fun i => (Finset.mem_filter.mp (ha i)).2
  have hinj : Function.Injective points := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    apply Subtype.ext
    change (points i).val = (points j).val
    exact congrArg Subtype.val hij
  have hvw : vertexOfTail P T hTV v ≠ vertexOfTail P T hTV w := by
    intro h
    exact hwv (Subtype.ext (congrArg Subtype.val h).symm)
  let A : Finset (E n) := {v.val,w.val,(points 0).val,(points 1).val,(points 2).val}
  have hp01 : (points 0).val ≠ (points 1).val := by
    intro h
    have hi : (0 : Fin 3) = 1 := hinj (Subtype.ext h)
    exact (by decide : (0 : Fin 3) ≠ 1) hi
  have hp02 : (points 0).val ≠ (points 2).val := by
    intro h
    have hi : (0 : Fin 3) = 2 := hinj (Subtype.ext h)
    exact (by decide : (0 : Fin 3) ≠ 2) hi
  have hp12 : (points 1).val ≠ (points 2).val := by
    intro h
    have hi : (1 : Fin 3) = 2 := hinj (Subtype.ext h)
    exact (by decide : (1 : Fin 3) ≠ 2) hi
  have hAT : A ⊆ T := by
    intro z hz
    simp only [A,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · exact v.property
    · exact w.property
    · exact (a 0).property
    · exact (a 1).property
    · exact (a 2).property
  have hvwval : v.val ≠ w.val := fun h => hwv (Subtype.ext h.symm)
  have hAc : A.card = 5 := by
    have hv0 := (hvEdges 0).2.1
    have hv1 := (hvEdges 1).2.1
    have hv2 := (hvEdges 2).2.1
    have hw0 := (hwEdges 0).2.1
    have hw1 := (hwEdges 1).2.1
    have hw2 := (hwEdges 2).2.1
    simp [A,hvwval,hv0,hv1,hv2,hw0,hw1,hw2,hp01,hp02,hp12,
      Ne.symm hvwval,Ne.symm hv0,Ne.symm hv1,Ne.symm hw0,Ne.symm hw1,Ne.symm hp01]
  apply hno A hAT hAc
  intro f hf
  obtain ⟨α,q,hhom⟩ := k23_homothety P
    (vertexOfTail P T hTV v) (vertexOfTail P T hTV w)
    points hvw hinj hvEdges hwEdges f
    (fun i => hf v.val v.property (points i).val (a i).property (hvEdges i))
    (fun i => hf w.val w.property (points i).val (a i).property (hwEdges i))
  refine ⟨α,q,?_⟩
  intro z hz
  apply hhom z
  simp only [A,Finset.mem_insert,Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨0,rfl⟩)
  · exact Or.inr (Or.inr ⟨1,rfl⟩)
  · exact Or.inr (Or.inr ⟨2,rfl⟩)

theorem rigid_cone_path
    (P : ConvexPolytope n) (T : Finset (E n)) (hTV : T ⊆ P.vertices)
    {x a b c d : E n} (hx : x∈T) (ha : a∈T) (hb : b∈T) (hc : c∈T) (hd : d∈T)
    (hxa : GeneralVertexStep P x a) (hxb : GeneralVertexStep P x b)
    (hxc : GeneralVertexStep P x c) (hxd : GeneralVertexStep P x d)
    (hab : GeneralVertexStep P a b) (hbc : GeneralVertexStep P b c)
    (hcd : GeneralVertexStep P c d) :
    RigidInTail P T (insert d (insert c {x,a,b})) := by
  have hsub3 : ({x,a,b}:Finset (E n)) ⊆ T := by
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> assumption
  have hr3 := rigid_triangle hTV hx ha hb hxa hxb hab
  have hr4 := hr3.insert_two_neighbors hTV hsub3 hc
    (u := x) (v := b) (by simp) (by simp) hxb.2.1
    (actualStep_symm (hTV hx) hxc) (actualStep_symm (hTV hb) hbc)
  exact hr4.insert_two_neighbors hTV (Finset.insert_subset hc hsub3) hd
    (u := x) (v := c) (by simp) (by simp) hxc.2.1
    (actualStep_symm (hTV hx) hxd) (actualStep_symm (hTV hc) hcd)

theorem neighbor_no_four_path_of_no_rigid_five
    (P : ConvexPolytope n) (T : Finset (E n)) (hTV : T ⊆ P.vertices)
    (hno : ∀ A : Finset (E n), A ⊆ T → A.card = 5 → ¬ RigidInTail P T A) :
    ∀ v : T, NoFourVertexPath
      ((smallTailGraph P T hTV).induce
        ((smallTailGraph P T hTV).neighborFinset v : Set T)) := by
  intro v a b c d hab hbc hcd hac hbd
  by_contra had
  let G := smallTailGraph P T hTV
  have hva : GeneralVertexStep P v.val a.val.val := (G.mem_neighborFinset _ _).mp a.property
  have hvb : GeneralVertexStep P v.val b.val.val := (G.mem_neighborFinset _ _).mp b.property
  have hvc : GeneralVertexStep P v.val c.val.val := (G.mem_neighborFinset _ _).mp c.property
  have hvd : GeneralVertexStep P v.val d.val.val := (G.mem_neighborFinset _ _).mp d.property
  have h3 : GeneralVertexStep P a.val.val b.val.val := hab
  have h4 : GeneralVertexStep P b.val.val c.val.val := hbc
  have h5 : GeneralVertexStep P c.val.val d.val.val := hcd
  have hac' : a.val.val ≠ c.val.val := fun h => hac (Subtype.ext (Subtype.ext h))
  have hbd' : b.val.val ≠ d.val.val := fun h => hbd (Subtype.ext (Subtype.ext h))
  have had' : a.val.val ≠ d.val.val := fun h => had (Subtype.ext (Subtype.ext h))
  let A : Finset (E n) := insert d.val.val (insert c.val.val {v.val,a.val.val,b.val.val})
  have hAT : A ⊆ T := by
    intro z hz
    simp only [A,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · exact d.val.property
    · exact c.val.property
    · exact v.property
    · exact a.val.property
    · exact b.val.property
  have hcard : A.card=5 := by
    have h1 := hva.2.1
    have h2 := hvb.2.1
    have h6 := hvc.2.1
    have h7 := hvd.2.1
    have h8 := h3.2.1
    have h9 := h4.2.1
    have h10 := h5.2.1
    simp [A,h1,h2,h6,h7,h8,h9,h10,hac',hbd',had',
      Ne.symm h1,Ne.symm h2,Ne.symm h6,Ne.symm h7,Ne.symm h8,
      Ne.symm h9,Ne.symm h10,Ne.symm hac',Ne.symm hbd',Ne.symm had']
  exact hno A hAT hcard (rigid_cone_path P T hTV v.property
    a.val.property b.val.property c.val.property d.val.property hva hvb hvc hvd h3 h4 h5)

theorem exists_rigid_five_of_nonsimple_min_large
    (P : ConvexPolytope n) (T : Finset (E n)) (hTV : T ⊆ P.vertices)
    (k : ℕ) (hk : 6≤k) (hcard : T.card≤4*k-5)
    (hmin : ∀ x∈T, k≤(T.filter (fun y => GeneralVertexStep P x y)).card)
    (hnonsimple : ∃ x∈T, k+1≤(T.filter (fun y => GeneralVertexStep P x y)).card) :
    ∃ A⊆T, 5≤A.card ∧ RigidInTail P T A := by
  by_contra! hno
  let G := smallTailGraph P T hTV
  have hno5 (A : Finset (E n)) (hAT : A⊆T) (hc : A.card=5) :
      ¬ RigidInTail P T A := hno A hAT (by omega)
  have hcommon := common_neighbors_le_two_of_no_rigid_five P T hTV hno5
  have hcap : ∀ v w : T, w∈outsideStar G v →
      localDegree G (G.neighborFinset v) w≤2 := by
    intro v w hw
    apply hcommon v w
    intro h
    exact (Finset.mem_sdiff.mp hw).2 (Finset.mem_insert.mpr (Or.inl h))
  have hneighbor : ∀ v w : T, w∈G.neighborFinset v →
      localDegree G (G.neighborFinset v) w≤2 := by
    intro v w hw
    exact hcommon v w (Ne.symm ((G.mem_neighborFinset _ _).mp hw).ne)
  have hGmin (v : T) : k≤G.degree v := by
    rw [smallTailGraph_degree_eq]
    exact hmin v.val v.property
  obtain ⟨x,hx,hxlarge⟩ := hnonsimple
  let v : T := ⟨x,hx⟩
  have hbig : k+1≤G.degree v := by
    rw [smallTailGraph_degree_eq]
    exact hxlarge
  have hc : Fintype.card T≤4*k-5 := by simpa only [Fintype.card_coe] using hcard
  by_cases hk6 : k=6
  · subst k
    have hle := min_six_order_nineteen_degree_at_most_six G
      (by omega) hGmin hcap hneighbor
      (neighbor_no_four_path_of_no_rigid_five P T hTV hno5) v
    omega
  · have hk7 : 7≤k := by omega
    have hb := neighborhood_cut_bound G v k 2 hGmin (hcap v)
    rw [outsideStar_card] at hb
    have hlt := G.degree_lt_card_verts v
    have hs : (∑ w∈G.neighborFinset v,
        localDegree G (G.neighborFinset v) w) ≤ 2*G.degree v := by
      calc
        _ ≤ ∑ w∈G.neighborFinset v, (2:ℕ) := Finset.sum_le_sum (hneighbor v)
        _ = _ := by simp [Nat.mul_comm]
    have hbound : G.degree v*(k-1)≤8*k-12 := by
      have hk1 : k-1+1=k := Nat.sub_add_cancel (by omega)
      have hout : Fintype.card T-(G.degree v+1)+(G.degree v+1)=Fintype.card T :=
        Nat.sub_add_cancel (by omega)
      have hsize : 4*k-5+5=4*k := Nat.sub_add_cancel (by omega)
      have htarget : 8*k-12+12=8*k := Nat.sub_add_cancel (by omega)
      nlinarith
    have hsquare := (Nat.mul_le_mul_right (k-1) hbig).trans hbound
    have hnonneg : 0≤(k-7)*(k-1) := Nat.zero_le _
    have h7 : k-7+7=k := Nat.sub_add_cancel hk7
    have h1 : k-1+1=k := Nat.sub_add_cancel (by omega)
    have h12 : 12≤8*k := by omega
    have hsub : 8*k-12+12=8*k := Nat.sub_add_cancel h12
    nlinarith

end Papers.ActualRigidSeedLimits

end
end
end BundlePart0

