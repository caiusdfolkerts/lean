module

public import PaperVerification.ToricCartierBoxCoordinates
public import PaperVerification.ToricOutsideBoxes
public import PaperVerification.ToricShiftedBoxes

@[expose] public section

/-!
# Exhaustive assembly of the actual selected-fan boxes

The local statements are applied after the full-cone classification.
The resulting box is expressed in the chosen Cartier basis of each full
cone; no preferred basis ordering remains in the conclusion.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

theorem exists_normal_basis_point («Σ» : SmoothCompleteFan n)
    (hfan : «Σ».realCones = P.normalFan)
    (b : Module.Basis (Fin n) ℤ (Lattice n))
    (hfull : Finset.univ.image b ∈ «Σ».cones) :
    ∃ v ∈ P.carrier, P.normalCone v =
      (latticeRayCone (Finset.univ.image b) : Set (Ambient n)) := by
  have hmem : (latticeRayCone (Finset.univ.image b) : Set (Ambient n)) ∈
      «Σ».realCones := ⟨Finset.univ.image b, hfull, rfl⟩
  rw [hfan] at hmem
  obtain ⟨v, hv, heq⟩ := hmem
  exact ⟨v, hv, heq.symm⟩

end LatticePolytope

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable {ι : Type*} [Fintype ι] (R : ι → «Σ».PrimitiveRelation)
variable (hne : ∀ i, (R i).negative.Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci (fun i => (R i).negative))

/-- Local ordinary and star-chart containments imply the exact full
centered box for every actual selected full cone and its chosen basis. -/
theorem selected_centered_box_of_charts
    (P : LatticePolytope n) (hfan : «Σ».realCones = P.normalFan)
    (c radius : ℝ) (u : ι → ℝ) (A : Set (Ambient n))
    (houtside : ∀ (b : Module.Basis (Fin n) ℤ (Lattice n)),
      Finset.univ.image b ∈ «Σ».cones →
      (∀ i, ¬ (R i).negative ⊆ Finset.univ.image b) →
      ∀ (v : Ambient n), v ∈ P.carrier →
      P.normalCone v = (latticeRayCone (Finset.univ.image b) : Set (Ambient n)) →
      ∀ t : Fin n → ℝ, (∀ k, |t k| ≤ radius) →
        v + ∑ k, (c + t k) • integralBasisReal (integralDualBasis b) k ∈ A)
    (hstar : ∀ (i : ι) (b : Module.Basis (Fin n) ℤ (Lattice n))
      (I : Finset (Fin n)), Finset.univ.image b ∈ «Σ».cones →
      I.image b = (R i).negative → ∀ j ∈ I,
      ∀ (v : Ambient n), v ∈ P.carrier →
      P.normalCone v = (latticeRayCone (Finset.univ.image b) : Set (Ambient n)) →
      ∀ t : Fin n → ℝ, (∀ k, |t k| ≤ radius) →
        v + u i • integralBasisReal (integralDualBasis b) j +
          ∑ k, (c + t k) •
            starShearBasis (integralBasisReal (integralDualBasis b)) I j k ∈ A)
    (s : («Σ».selectedFan R hne hdisj).fullCones)
    (t : Fin n → ℝ) (ht : ∀ k, |t k| ≤ radius) :
    («Σ».selectedFan R hne hdisj).cartierPoint
        («Σ».selectedCenteredSupport R (fun v => (P.integralSupport v : ℝ)) c u) s +
      ∑ k, t k • («Σ».selectedFan R hne hdisj).cartierBasis s k ∈ A := by
  let Γ := «Σ».selectedFan R hne hdisj
  rcases «Σ».selected_full_cone_chart R hne hdisj s with ⟨hs, hnone⟩ |
    ⟨i, b, I, j, hfull, hI, hj, hset⟩
  · let b := Γ.fullConeBasis s
    have hset : (s : Finset (Lattice n)) = Finset.univ.image b := Γ.fullConeBasis_ray_set s
    have hfull : Finset.univ.image b ∈ «Σ».cones := hset ▸ hs
    have hn : ∀ i, ¬ (R i).negative ⊆ Finset.univ.image b := hset ▸ hnone
    obtain ⟨v, hv, hcone⟩ := P.exists_normal_basis_point «Σ» hfan b hfull
    apply Γ.centered_box_in_cartierBasis _ s b hset A radius ?_ t ht
    intro «λ» «hλ»
    rw [«Σ».selected_center_outside_chart R hne hdisj
      (fun v => (P.integralSupport v : ℝ)) c u s hs hnone b hset v
      (P.normal_basis_vertex_active «Σ» v hv b hcone)]
    simpa only [add_smul, Finset.sum_add_distrib, add_assoc] using
      houtside b hfull hn v hv hcone «λ» «hλ»
  · obtain ⟨v, hv, hcone⟩ := P.exists_normal_basis_point «Σ» hfan b hfull
    apply Γ.centered_box_in_cartierBasis _ s (starRayBasis b I j) hset A radius ?_ t ht
    intro «λ» «hλ»
    rw [«Σ».selected_center_star_chart R hne hdisj
      (fun v => (P.integralSupport v : ℝ)) c u s i b I hfull hI j hj hset v
      (P.normal_basis_vertex_active «Σ» v hv b hcone),
      integralBasisReal_dual_starRayBasis b I j hj]
    simpa only [add_smul, Finset.sum_add_distrib, add_assoc] using
      hstar i b I hfull hI j hj v hv hcone «λ» «hλ»

end SmoothCompleteFan

end PaperVerification.ToricGeometry
