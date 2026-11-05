module
public import consolidated.actual_four_tail_geometry
public import consolidated_dev.no_simple_ten_intrinsic

set_option Elab.async false

section BundlePart0
/- Source: Papers/FourTailRigidCover.lean -/





@[expose] public section
noncomputable section
namespace Papers.PolytopeFourRegularTail
open Set Finset Papers.Polytopes Papers.PolytopeVertexCone
open Papers.ActualRigidSeedLimits Papers.NeighborhoodCounts
open Papers.PolytopeSimpleTailFace Papers.PolytopeTailRigidity
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical BigOperators
variable {n : ℕ}

theorem tailNeighbors_eq (P : ConvexPolytope n) (T : Finset (E n))
    (hTV : T ⊆ P.vertices) (x : E n) :
    (actualNeighbors P x).filter (·∈T) = T.filter (GeneralVertexStep P x) := by
  ext y
  simp only [Finset.mem_filter,mem_actualNeighbors_iff]
  tauto

/-- The complete four-regular tail reduction. The simplicity hypothesis is
required only in the exceptional four-regular case. -/
theorem rigidCover_three_of_min_four_card_le_ten
    (P : ConvexPolytope n) (hP : P.IsFullDim)
    (T : Finset (E n)) (hTV : T ⊆ P.vertices) (hcard : T.card≤10)
    (hmin : ∀x∈T,4≤(T.filter (GeneralVertexStep P x)).card)
    (hsimple : (∀x∈T,(T.filter (GeneralVertexStep P x)).card=4) →
      ∀x∈T,(actualNeighbors P x).card=n) :
    HasRigidCover P T 3 := by
  by_cases hne : T.Nonempty
  · by_cases hlarge : ∃ B⊆T,4≤B.card ∧ RigidInTail P T B
    · obtain ⟨B,hBT,hBc,hBR⟩ := hlarge
      obtain ⟨A,hA⟩ := exists_largest_rigid P T
      have hAc : 4≤A.card := hBc.trans (hA.largest B hBT hBR)
      have hc := Finset.card_sdiff_add_card_eq_card hA.subset
      have hres := hA.residual_min_degree hTV 3 hmin
      exact (rigidCover_two_of_min_three_card_le_six P (T\A)
        (Finset.sdiff_subset.trans hTV) (by omega) hres).adjoin hA.subset hA.rigid
    · have hno4 (A : Finset (E n)) (hAT : A⊆T) (hc : A.card=4) :
          ¬ RigidInTail P T A := by
        intro hr
        exact hlarge ⟨A,hAT,by omega,hr⟩
      let G := smallTailGraph P T hTV
      letI : Nonempty T := ⟨⟨hne.choose,hne.choose_spec⟩⟩
      have hGmin (v : T) : 4≤G.degree v := by
        rw [smallTailGraph_degree_eq]
        exact hmin v.val v.property
      have hcap := common_neighbors_le_two_of_no_rigid_four P T hTV hno4
      have hmatch := neighbor_matchings_of_no_rigid_four P T hTV hno4
      have hTc : Fintype.card T≤10 := by simpa only [Fintype.card_coe] using hcard
      obtain ⟨horder,hreg⟩ := Papers.FourRegularTail.regularity_and_order G hTc hGmin hcap hmatch
      have hregular : ∀x∈T,(T.filter (GeneralVertexStep P x)).card=4 := by
        intro x hx
        simpa only [G,smallTailGraph_degree_eq] using hreg (⟨x,hx⟩:T)
      rcases horder with h9 | h10
      · let v : T := Classical.choice inferInstance
        obtain ⟨a,b,hva,hvb,hab⟩ :=
          Papers.FourRegularTail.triangle_in_nine_vertex_tail G h9 hreg hcap v
        have htr := rigid_triangle hTV v.property a.property b.property hva hvb hab
        have hsub : ({v.val,a.val,b.val}:Finset (E n))⊆T := by
          intro x hx
          simp only [Finset.mem_insert,Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl <;> exact Subtype.property _
        have htrc : ({v.val,a.val,b.val}:Finset (E n)).card=3 := by
          have h1 := hva.2.1
          have h2 := hvb.2.1
          have h3 := hab.2.1
          simp [h1,h2,h3,Ne.symm h1,Ne.symm h2,Ne.symm h3]
        obtain ⟨A,hA⟩ := exists_largest_rigid P T
        have hAc : 3≤A.card := by simpa only [htrc] using hA.largest _ hsub htr
        have hc := Finset.card_sdiff_add_card_eq_card hA.subset
        have hT9 : T.card=9 := by simpa only [Fintype.card_coe] using h9
        have hres := hA.residual_min_degree hTV 3 hmin
        exact (rigidCover_two_of_min_three_card_le_six P (T\A)
          (Finset.sdiff_subset.trans hTV) (by omega) hres).adjoin hA.subset hA.rigid
      · have hT10 : T.card=10 := by simpa only [Fintype.card_coe] using h10
        obtain ⟨F,hF,hFd,hFV,hFs⟩ := actual_four_face_of_ten_tail_without_rigid_four
          P hP T hTV hT10 (hsimple hregular)
          (by intro x hx; rw [tailNeighbors_eq P T hTV x]; exact hmin x hx) hno4
        have hdim : (facePolytope P hF).dim=4 := by
          change Module.finrank ℝ (vectorSpan ℝ (facePolytope P hF).toSet)=4
          rw [facePolytope_toSet P hF]
          exact hFd
        exact (Papers.SimpleFour.no_simple_intrinsic_four_polytope_ten_vertices
          (facePolytope P hF) hdim (by rw [hFV];exact hT10) hFs).elim
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    exact rigidCover_empty P 3

/-- At most `r` of each tail vertex's neighbors have already been removed. -/
def TailDegreeBudget (P : ConvexPolytope n) (T : Finset (E n)) (r : ℕ) : Prop :=
  ∀x∈T,(actualNeighbors P x).card≤(T.filter (GeneralVertexStep P x)).card+r

theorem TailDegreeBudget.full (P : ConvexPolytope n) : TailDegreeBudget P P.vertices 0 := by
  intro x hx
  simp only [actualNeighbors,Nat.add_zero,le_refl]

theorem TailDegreeBudget.remove_largest
    {P : ConvexPolytope n} {T A : Finset (E n)} {r : ℕ}
    (hb : TailDegreeBudget P T r) (hTV : T⊆P.vertices) (hA : LargestRigidSet P T A) :
    TailDegreeBudget P (T\A) (r+1) := by
  intro x hx
  obtain ⟨hxT,hxA⟩ := Finset.mem_sdiff.mp hx
  have hsmall := hA.outside_degree_le_one hTV hxT hxA
  change (A.filter (GeneralVertexStep P x)).card≤1 at hsmall
  have hglobal := hb x hxT
  have hsub : A.filter (GeneralVertexStep P x)⊆T.filter (GeneralVertexStep P x) :=
    Finset.filter_subset_filter _ hA.subset
  have he : (T\A).filter (GeneralVertexStep P x) =
      T.filter (GeneralVertexStep P x) \ A.filter (GeneralVertexStep P x) := by
    ext y
    simp only [Finset.mem_filter,Finset.mem_sdiff]
    tauto
  have hc := Finset.card_sdiff_add_card_eq_card hsub
  rw [he]
  omega

theorem TailDegreeBudget.simple_of_four_regular
    {P : ConvexPolytope n} (hP : P.IsFullDim) {T : Finset (E n)}
    (hTV : T⊆P.vertices) {r : ℕ} (hr : 4+r=n) (hb : TailDegreeBudget P T r)
    (hreg : ∀x∈T,(T.filter (GeneralVertexStep P x)).card=4) :
    ∀x∈T,(actualNeighbors P x).card=n := by
  intro x hx
  have hu := hb x hx
  rw [hreg x hx,hr] at hu
  have hl := intrinsic_dim_le_neighbor_card P (hTV hx)
  rw [hP] at hl
  exact le_antisymm hu hl

theorem rigidCover_of_tail_card_degree_budget
    (P : ConvexPolytope n) (hP : P.IsFullDim)
    (k : ℕ) (hk : 4≤k) (T : Finset (E n)) (hTV : T⊆P.vertices)
    (hcard : T.card≤4*k-6)
    (hmin : ∀x∈T,k≤(T.filter (GeneralVertexStep P x)).card)
    (r : ℕ) (hkr : k+r=n) (hb : TailDegreeBudget P T r) :
    HasRigidCover P T (k-1) := by
  induction k using Nat.strong_induction_on generalizing T r with
  | h k ih =>
    by_cases hk4 : k=4
    · subst k
      exact rigidCover_three_of_min_four_card_le_ten P hP T hTV hcard hmin
        (TailDegreeBudget.simple_of_four_regular hP hTV hkr hb)
    · by_cases hne : T.Nonempty
      · have hk5 : 5≤k := by omega
        obtain ⟨B,hBT,hBc,hBR⟩ := exists_rigid_four_of_min_large P T hTV hne k hk5 hcard hmin
        obtain ⟨A,hA⟩ := exists_largest_rigid P T
        have hAc : 4≤A.card := hBc.trans (hA.largest B hBT hBR)
        have hc := Finset.card_sdiff_add_card_eq_card hA.subset
        have hres := hA.residual_min_degree hTV (k-1) (by
          have he : k-1+1=k := Nat.sub_add_cancel (by omega)
          simpa only [he] using hmin)
        have hnext := ih (k-1) (by omega) (by omega) (T\A)
          (Finset.sdiff_subset.trans hTV) (by omega) hres (r+1) (by omega)
          (hb.remove_largest hTV hA)
        have hcover := hnext.adjoin hA.subset hA.rigid
        convert hcover using 1 <;> omega
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
        exact rigidCover_empty P (k-1)

end Papers.PolytopeFourRegularTail

end
end
end BundlePart0

