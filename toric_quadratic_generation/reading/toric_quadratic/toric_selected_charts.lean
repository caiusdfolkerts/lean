module

public import PaperVerification.ToricSelectedLoci
public import PaperVerification.ToricNefBoxGeometry
public import PaperVerification.ToricFanPolytopeSmoothness

@[expose] public section

/-!
# All full cones of the selected fan

Every full cone is either an unchanged cone outside the selected loci or
an actual integral star chart at exactly one selected locus. A focus with
one ray is included as the identity star chart.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

theorem integralDualBasis_starRayBasis {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (j : Fin n) (hj : j ∈ I) :
    integralDualBasis (starRayBasis b I j) =
      starShearBasis (integralDualBasis b) I j := by
  have h := congrArg integralDualBasis
    (integralDualBasis_starShearBasis (integralDualBasis b) I j hj)
  simpa only [integralDualBasis_involutive] using h.symm

theorem integralBasisReal_dual_starRayBasis {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (j : Fin n) (hj : j ∈ I) :
    integralBasisReal (integralDualBasis (starRayBasis b I j)) =
      starShearBasis (integralBasisReal (integralDualBasis b)) I j := by
  rw [integralDualBasis_starRayBasis b I j hj, integralBasisReal_starShearBasis]

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable {ι : Type*} [Fintype ι] (R : ι → «Σ».PrimitiveRelation)
variable (hne : ∀ i, (R i).negative.Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci (fun i => (R i).negative))

theorem selected_full_cone_chart
    (s : («Σ».selectedFan R hne hdisj).fullCones) :
    ((s : Finset (Lattice n)) ∈ «Σ».cones ∧
      ∀ i, ¬ (R i).negative ⊆ (s : Finset (Lattice n))) ∨
    ∃ (i : ι) (b : Module.Basis (Fin n) ℤ (Lattice n))
      (I : Finset (Fin n)) (j : Fin n),
      Finset.univ.image b ∈ «Σ».cones ∧ I.image b = (R i).negative ∧
      j ∈ I ∧ (s : Finset (Lattice n)) =
        Finset.univ.image (starRayBasis b I j) := by
  let Γ := «Σ».selectedFan R hne hdisj
  have hs : (s : Finset (Lattice n)) ∈ Γ.cones := Γ.fullCones_mem s
  have hcard : (s : Finset (Lattice n)).card = n := Γ.fullCones_card s
  by_cases hex : ∃ i, «Σ».selectedRay R i ∈ (s : Finset (Lattice n))
  · obtain ⟨i, hi⟩ := hex
    right
    by_cases hqi : 2 ≤ (R i).negative.card
    · let i' : «Σ».BlowupIndices R := ⟨i, hqi⟩
      have hsingle := («Σ».simultaneous_cone_over_sum_iff («Σ».selectedStarFocus R)
        (fun k => (R k).negative_cone) (fun k => hne k)
        («Σ».selectedStarFocus_disjoint R hdisj) (fun k => k.property) i' hi).mp hs
      obtain ⟨U, hU, hUcard, hNU, p, hp, hseq⟩ :=
        «Σ».full_star_cone_parent (R i).negative (R i).negative_cone (hne i)
          hqi hsingle hcard hi
      obtain ⟨b, hUb⟩ := «Σ».full_cone_basis hU hUcard
      let I := basisRayIndices b (R i).negative
      have hI : I.image b = (R i).negative :=
        image_basisRayIndices b _ (hUb ▸ hNU)
      obtain ⟨j, hj, hbj⟩ := Finset.mem_image.mp (hI.symm ▸ hp)
      refine ⟨i, b, I, j, hUb ▸ hU, hI, hj, ?_⟩
      rw [hseq, hUb, ← hI, ← hbj,
        lattice_starRaySet_basis b Finset.univ I (Finset.subset_univ I) j hj]
    · have hfocus := «Σ».selected_focus_of_not_blowup R hne i hqi
      have hold := («Σ».selected_divisor_cone_iff R hne hdisj i hqi hi).mp hs
      obtain ⟨b, hsb⟩ := «Σ».full_cone_basis hold hcard
      obtain ⟨j, hj, hbj⟩ := Finset.mem_image.mp (hsb ▸ hi)
      have hstar : starRayBasis b {j} j = b := by
        apply DFunLike.ext
        intro k
        by_cases hkj : k = j <;> simp [starRayBasis_apply, starRayVector, hkj]
      refine ⟨i, b, {j}, j, hsb ▸ hold, ?_, Finset.mem_singleton_self j, ?_⟩
      · simp only [Finset.image_singleton, hbj, hfocus]
      · rw [hstar]
        exact hsb
  · left
    have hnone : ∀ i, «Σ».selectedRay R i ∉ (s : Finset (Lattice n)) := by
      simpa only [not_exists] using hex
    have h := («Σ».simultaneous_cone_without_sums_iff («Σ».selectedStarFocus R)
      (fun i => (R i).negative_cone) (fun i => hne i)
      («Σ».selectedStarFocus_disjoint R hdisj) (fun i => hnone i)).mp hs
    refine ⟨h.1, ?_⟩
    intro i hi
    by_cases hqi : 2 ≤ (R i).negative.card
    · exact h.2 ⟨i, hqi⟩ hi
    · have hfocus := «Σ».selected_focus_of_not_blowup R hne i hqi
      exact hnone i (hi (hfocus.symm ▸ Finset.mem_singleton_self («Σ».selectedRay R i)))

end SmoothCompleteFan

end PaperVerification.ToricGeometry
