module

public import PaperVerification.ToricWallCurves
public import PaperVerification.ToricRankOneDegree
public import PaperVerification.ToricOrbitCartierRestriction
public import PaperVerification.ToricWallPolytopeBounds

@[expose] public section

/-!
# Actual invariant-curve degree equals integral wall slack

The orbit cone is the wall obtained by deleting one basis ray. The
quotient lattice has one coordinate. The original ray projects to `1`
and the opposite ray to `-1`; normalization at the original full cone
makes the first restricted coefficient zero and the second exactly the
integral wall slack. The genuine pullback-sheaf isomorphism and the
proved degree formula on the actual curve give the equality.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (s : «Σ».fullCones) (j : Fin n)

theorem wall_complementaryEmbedding
    (q : Fin (n-(«Σ».wallIndices s j).card)) :
    complementaryEmbedding («Σ».wallIndices s j) q=j := by
  have hnot : complementaryEmbedding («Σ».wallIndices s j) q∉«Σ».wallIndices s j :=
    (mem_range_complementaryEmbedding_iff _ _).mp ⟨q,rfl⟩
  by_contra hne
  exact hnot (Finset.mem_erase.mpr ⟨hne,Finset.mem_univ _⟩)

theorem wall_quotient_coordinate (v : Lattice n)
    (q : Fin (n-(«Σ».wallIndices s j).card)) :
    coneQuotientLattice («Σ».fullConeBasis s) («Σ».wallIndices s j) v q =
      («Σ».fullConeBasis s).repr v j := by
  change («Σ».fullConeBasis s).repr v (complementaryEmbedding («Σ».wallIndices s j) q)=_
  rw [«Σ».wall_complementaryEmbedding]

theorem wallCone_subset_full :
    («Σ».wallIndices s j).image («Σ».fullConeBasis s)⊆s.val := by
  rw [«Σ».fullConeBasis_ray_set]
  exact Finset.image_subset_image (Finset.erase_subset _ _)

theorem fullConeBasis_mem_sdiff_wall :
    «Σ».fullConeBasis s j∈s.val\(«Σ».wallIndices s j).image («Σ».fullConeBasis s) := by
  apply Finset.mem_sdiff.mpr
  constructor
  · rw [«Σ».fullConeBasis_ray_set]
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩
  · intro h
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp h
    have hij := («Σ».fullConeBasis s).injective he
    exact (Finset.mem_erase.mp hi).1 hij

theorem wall_quotient_positive :
    coneQuotientLattice («Σ».fullConeBasis s) («Σ».wallIndices s j)
      («Σ».fullConeBasis s j) = (fun _=>1) := by
  ext q
  rw [«Σ».wall_quotient_coordinate]
  simp

theorem wall_quotient_negative (w : Lattice n)
    (hw : («Σ».fullConeBasis s).repr w j = -1) :
    coneQuotientLattice («Σ».fullConeBasis s) («Σ».wallIndices s j) w = (fun _=>-1) := by
  ext q
  rw [«Σ».wall_quotient_coordinate,hw]

theorem wall_positive_ne_negative :
    (fun _=>1 : Lattice (n-(«Σ».wallIndices s j).card))≠(fun _=>-1) := by
  intro h
  let q : Fin (n-(«Σ».wallIndices s j).card) :=
    ⟨0,by rw [«Σ».wallIndices_codimension]; omega⟩
  have hq := congrFun h q
  norm_num at hq

def wallRestrictionCoefficients (a : Lattice n→ℤ) :
    Lattice (n-(«Σ».wallIndices s j).card)→ℤ :=
  «Σ».orbitRestrictionCoefficients («Σ».fullConeBasis s) («Σ».wallIndices s j)
    («Σ».wallCone_mem s j) a («Σ».cartierLatticePoint a s)

theorem wallRestriction_positive (a : Lattice n→ℤ) :
    «Σ».wallRestrictionCoefficients s j a (fun _=>1)=0 := by
  rw [wallRestrictionCoefficients,← «Σ».wall_quotient_positive s j,
    «Σ».orbitRestrictionCoefficients_projected («Σ».fullConeBasis s) («Σ».wallIndices s j)
      («Σ».wallCone_mem s j) a («Σ».cartierLatticePoint a s) («Σ».fullCones_mem s)
      («Σ».wallCone_subset_full s j) («Σ».fullConeBasis_mem_sdiff_wall s j),
    «Σ».cartierLatticePoint_pairing a s («Σ».fullConeBasis s j)
      (Finset.mem_sdiff.mp («Σ».fullConeBasis_mem_sdiff_wall s j)).1]
  ring

theorem wallRestriction_negative (a : Lattice n→ℤ)
    (t : «Σ».fullCones) (w : Lattice n)
    (ht : t.val=insert w ((«Σ».wallIndices s j).image («Σ».fullConeBasis s)))
    (hwj : («Σ».fullConeBasis s).repr w j = -1) :
    «Σ».wallRestrictionCoefficients s j a (fun _=>-1)=«Σ».integerWallSlack a s w := by
  have hwF : w∉(«Σ».wallIndices s j).image («Σ».fullConeBasis s) := by
    intro hw
    have hzero := basis_wall_coord_zero («Σ».fullConeBasis s) j w hw
    omega
  have hFt : («Σ».wallIndices s j).image («Σ».fullConeBasis s)⊆t.val := by
    rw [ht]
    exact Finset.subset_insert _ _
  have hwt : w∈t.val\(«Σ».wallIndices s j).image («Σ».fullConeBasis s) := by
    rw [ht]
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self _ _,hwF⟩
  rw [wallRestrictionCoefficients,← «Σ».wall_quotient_negative s j w hwj,
    «Σ».orbitRestrictionCoefficients_projected («Σ».fullConeBasis s) («Σ».wallIndices s j)
      («Σ».wallCone_mem s j) a («Σ».cartierLatticePoint a s)
      («Σ».fullCones_mem t) hFt hwt]
  rfl

theorem wallRestriction_sum (a : Lattice n→ℤ)
    (t : «Σ».fullCones) (w : Lattice n)
    (ht : t.val=insert w ((«Σ».wallIndices s j).image («Σ».fullConeBasis s)))
    (hwj : («Σ».fullConeBasis s).repr w j = -1) :
    (∑ u∈(«Σ».wallCurveFan s j).rays,«Σ».wallRestrictionCoefficients s j a u) =
      «Σ».integerWallSlack a s w := by
  rw [(«Σ».wallCurveFan s j).oneDimensional_rays («Σ».wallIndices_codimension s j),
    Finset.sum_pair («Σ».wall_positive_ne_negative s j),
    «Σ».wallRestriction_positive s j a,«Σ».wallRestriction_negative s j a t w ht hwj,zero_add]

variable (k : Type u) [Field k] (hpure : «Σ».IsPure)

/-- The bound in the paper is applied to the genuine restricted line
bundle on the actual invariant curve. Its degree is the wall slack. -/
theorem wallCurve_fanCartier_hasDegree (a : Lattice n→ℤ)
    (t : «Σ».fullCones) (w : Lattice n)
    (ht : t.val=insert w ((«Σ».wallIndices s j).image («Σ».fullConeBasis s)))
    (hwj : («Σ».fullConeBasis s).repr w j = -1) :
    («Σ».wallCurveFan s j).OneDimensionalHasDegree («Σ».wallIndices_codimension s j) k
      ((Scheme.Modules.pullback («Σ».wallCurveInclusion s j k)).obj
        («Σ».fanCartierData k hpure a).sheaf) («Σ».integerWallSlack a s w) := by
  have hm : ∀ u∈(«Σ».wallIndices s j).image («Σ».fullConeBasis s),
      integerPairing u («Σ».cartierLatticePoint a s) = -a u := by
    intro u hu
    exact «Σ».cartierLatticePoint_pairing a s u («Σ».wallCone_subset_full s j hu)
  let F := «Σ».orbitCartierPullbackIso k («Σ».fullConeBasis s) («Σ».wallIndices s j)
    («Σ».wallCone_mem s j) hpure a («Σ».cartierLatticePoint a s) hm
  apply ((«Σ».wallCurveFan s j).oneDimensionalHasDegree_iso
    («Σ».wallIndices_codimension s j) k F _).mpr
  have h := («Σ».wallCurveFan s j).oneDimensionalFanCartier_hasDegree
    («Σ».wallIndices_codimension s j) k
    («Σ».completeQuotientStarFan_isPure hpure («Σ».fullConeBasis s) («Σ».wallIndices s j)
      («Σ».wallCone_mem s j)) («Σ».wallRestrictionCoefficients s j a)
  rwa [«Σ».wallRestriction_sum s j a t w ht hwj] at h

/-- An arbitrary Cartier sheaf is handled through its proved actual
isomorphism to the recovered invariant presentation. -/
theorem wallCurve_cartier_hasDegree (D : CartierData («Σ».fanScheme k))
    (t : «Σ».fullCones) (w : Lattice n)
    (ht : t.val=insert w ((«Σ».wallIndices s j).image («Σ».fullConeBasis s)))
    (hwj : («Σ».fullConeBasis s).repr w j = -1) :
    («Σ».wallCurveFan s j).OneDimensionalHasDegree («Σ».wallIndices_codimension s j) k
      ((Scheme.Modules.pullback («Σ».wallCurveInclusion s j k)).obj D.sheaf)
      («Σ».integerWallSlack («Σ».cartierCoefficients k hpure D) s w) := by
  let F := («Σ».cartierData_linearlyEquivalent_fanCartier k hpure D).some
  apply ((«Σ».wallCurveFan s j).oneDimensionalHasDegree_iso
    («Σ».wallIndices_codimension s j) k
      ((Scheme.Modules.pullback («Σ».wallCurveInclusion s j k)).mapIso F) _).mpr
  exact «Σ».wallCurve_fanCartier_hasDegree s j k hpure _ t w ht hwj

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.wallCurve_fanCartier_hasDegree
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.wallCurve_cartier_hasDegree
