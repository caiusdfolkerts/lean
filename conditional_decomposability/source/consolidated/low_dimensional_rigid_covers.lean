module
public import consolidated.nonsimple_rigid_covers
public import consolidated.actual_sigma_tail

set_option Elab.async false

section BundlePart0
/- Source: Papers/LowDimensionalRigidCovers.lean -/




@[expose] public section
noncomputable section
namespace Papers.PolytopeFourRegularTail
open Set Finset Papers.Polytopes Papers.PolytopeVertexCone
open Papers.ActualRigidSeedLimits Papers.PolytopeSimpleTailFace
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical
variable {n : ℕ}

def HasRigidBoundaryCover (P : ConvexPolytope n) (m : ℕ) : Prop :=
  ∃z,Nonempty (GlobalRigidBoundaryPieces P (Fin m⊕Fin 3)
    (Sum.inr 0) (Sum.inr 1) (Sum.inr 2) z)

def HasRigidSetContainingNonsimple (P : ConvexPolytope n) : Prop :=
  ∃R : Finset (E n),R⊆P.vertices ∧ 2≤R.card ∧ RigidInTail P P.vertices R ∧
    ∀x∈P.vertices,x∉R→(actualNeighbors P x).card=n

/-- Complete graph-cover routing in dimension four. -/
theorem nonsimple_four_cover_cases
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (hcard : P.vertices.card≤11)
    (hnonsimple : ∃x∈P.vertices,5≤(actualNeighbors P x).card) :
    HasRigidCover P P.vertices 3 ∨ HasRigidBoundaryCover P 1 := by
  have hmin := full_min_degree P hP
  obtain ⟨B,hBT,hBc,hBR⟩ := exists_rigid_four_nonsimple_dimensions_four_five
    P P.vertices (Finset.Subset.refl _) 4 (by omega) (by omega) hcard hmin hnonsimple
  obtain ⟨R,hR⟩ := exists_largest_rigid P P.vertices
  have hRc : 4≤R.card := hBc.trans (hR.largest B hBT hBR)
  have hc := Finset.card_sdiff_add_card_eq_card hR.subset
  have hres := hR.residual_min_degree (Finset.Subset.refl _) 3 hmin
  by_cases hR5 : 5≤R.card
  · exact Or.inl ((rigidCover_two_of_min_three_card_le_six P (P.vertices\R)
      Finset.sdiff_subset (by omega) hres).adjoin hR.subset hR.rigid)
  · have hR4 : R.card=4 := by omega
    rcases two_cover_or_sigma_of_min_three_card_le_seven P (P.vertices\R)
      Finset.sdiff_subset (by omega) hres with hcover | hSigma
    · exact Or.inl (hcover.adjoin hR.subset hR.rigid)
    · let S := Classical.choice hSigma
      refine Or.inr ⟨S.center,?_⟩
      apply S.to_global_boundary Finset.sdiff_subset 1 (fun _=>R)
        (fun _=>hR.subset) (by intro i;omega) (fun _=>hR.rigid)
      intro x hx
      by_cases hxR : x∈R
      · exact Or.inl ⟨0,hxR⟩
      · exact Or.inr (Finset.mem_sdiff.mpr ⟨hx,hxR⟩)

/-- Complete graph-cover routing in dimension five. The last alternative
contains all nonsimple vertices in one rigid set, so actual facet hitting
supplies the Shephard facet without an excess-theorem assumption. -/
theorem nonsimple_five_cover_cases
    (P : ConvexPolytope 5) (hP : P.IsFullDim) (hcard : P.vertices.card≤15)
    (hnonsimple : ∃x∈P.vertices,6≤(actualNeighbors P x).card) :
    HasRigidCover P P.vertices 4 ∨ HasRigidBoundaryCover P 2 ∨
      HasRigidSetContainingNonsimple P := by
  have hmin := full_min_degree P hP
  obtain ⟨B,hBT,hBc,hBR⟩ := exists_rigid_four_nonsimple_dimensions_four_five
    P P.vertices (Finset.Subset.refl _) 5 (by omega) (by omega) hcard hmin hnonsimple
  obtain ⟨R,hR⟩ := exists_largest_rigid P P.vertices
  have hRc : 4≤R.card := hBc.trans (hR.largest B hBT hBR)
  have hcR := Finset.card_sdiff_add_card_eq_card hR.subset
  have hresR := hR.residual_min_degree (Finset.Subset.refl _) 4 hmin
  have hbudgetR := (TailDegreeBudget.full P).remove_largest (Finset.Subset.refl _) hR
  by_cases hR5 : 5≤R.card
  · have hcover := rigidCover_three_of_min_four_card_le_ten P hP (P.vertices\R)
      Finset.sdiff_subset (by omega) hresR
      (TailDegreeBudget.simple_of_four_regular hP Finset.sdiff_subset rfl hbudgetR)
    exact Or.inl (hcover.adjoin hR.subset hR.rigid)
  · have hR4 : R.card=4 := by omega
    by_cases hlarge : ∃B⊆P.vertices\R,4≤B.card ∧ RigidInTail P (P.vertices\R) B
    · obtain ⟨B,hBT,hBc,hBR⟩ := hlarge
      obtain ⟨S,hS⟩ := exists_largest_rigid P (P.vertices\R)
      have hSc : 4≤S.card := hBc.trans (hS.largest B hBT hBR)
      have hcS := Finset.card_sdiff_add_card_eq_card hS.subset
      have hresS := hS.residual_min_degree Finset.sdiff_subset 3 hresR
      by_cases hS5 : 5≤S.card
      · have hcover := rigidCover_two_of_min_three_card_le_six P ((P.vertices\R)\S)
          (Finset.sdiff_subset.trans Finset.sdiff_subset) (by omega) hresS
        exact Or.inl ((hcover.adjoin hS.subset hS.rigid).adjoin hR.subset hR.rigid)
      · have hS4 : S.card=4 := by omega
        rcases two_cover_or_sigma_of_min_three_card_le_seven P ((P.vertices\R)\S)
          (Finset.sdiff_subset.trans Finset.sdiff_subset) (by omega) hresS
          with hcover | hSigma
        · exact Or.inl ((hcover.adjoin hS.subset hS.rigid).adjoin hR.subset hR.rigid)
        · let U := Classical.choice hSigma
          refine Or.inr (Or.inl ⟨U.center,?_⟩)
          apply U.to_global_boundary (Finset.sdiff_subset.trans Finset.sdiff_subset)
            2 ![R,S]
          · intro i
            fin_cases i
            · exact hR.subset
            · exact hS.subset.trans Finset.sdiff_subset
          · intro i
            fin_cases i
            · change R.card≤4
              omega
            · change S.card≤4
              omega
          · intro i
            fin_cases i
            · exact hR.rigid
            · exact hS.rigid.mono_tail Finset.sdiff_subset
          · intro x hx
            by_cases hxR : x∈R
            · exact Or.inl ⟨0,hxR⟩
            by_cases hxS : x∈S
            · exact Or.inl ⟨1,hxS⟩
            · exact Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hx,hxR⟩,hxS⟩)
    · have hno4 (A : Finset (E 5)) (hAT : A⊆P.vertices\R) (hc : A.card=4) :
          ¬RigidInTail P (P.vertices\R) A := by
        intro hr
        exact hlarge ⟨A,hAT,by omega,hr⟩
      have hreg := four_regular_of_min_four_le_eleven_no_rigid_four P (P.vertices\R)
        Finset.sdiff_subset (by omega) hresR hno4
      have hsimple := TailDegreeBudget.simple_of_four_regular hP Finset.sdiff_subset
        rfl hbudgetR hreg
      refine Or.inr (Or.inr ⟨R,hR.subset,by omega,hR.rigid,?_⟩)
      intro x hx hxR
      exact hsimple x (Finset.mem_sdiff.mpr ⟨hx,hxR⟩)

end Papers.PolytopeFourRegularTail

end
end
end BundlePart0

