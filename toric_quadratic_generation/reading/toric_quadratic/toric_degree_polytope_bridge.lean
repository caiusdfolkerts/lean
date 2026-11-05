module

public import PaperVerification.ToricWallCurveDegrees

@[expose] public section

/-!
# From actual invariant-curve degrees to actual polytope edge lengths

Every adjacent full-cone pair determines a deleted basis ray. The
quotient fan proves that the other transverse ray is `-1`; its degree is
therefore exactly the wall slack already computed by actual sheaf
restriction. Positive degree bounds consequently give the full smooth
lattice polytope and the same bound on every actual edge.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem adjacentWall_basisIndex (s t : «Σ».fullCones)
    (hst : (s.val∩t.val).card=n-1) (u : Lattice n) (hut : u∈t.val) (hus : u∉s.val) :
    ∃ j : Fin n,
      s.val∩t.val=(«Σ».wallIndices s j).image («Σ».fullConeBasis s) ∧
      t.val=insert u ((«Σ».wallIndices s j).image («Σ».fullConeBasis s)) := by
  have hn : 0<n := by
    have h := Finset.card_pos.mpr (show t.val.Nonempty from ⟨u,hut⟩)
    rwa [«Σ».fullCones_card] at h
  have hcard : (s.val\t.val).card=1 := by
    have h := Finset.card_sdiff_add_card_inter s.val t.val
    rw [hst,«Σ».fullCones_card] at h
    omega
  obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hcard
  have hvst : v∈s.val\t.val := by rw [hv]; exact Finset.mem_singleton_self _
  have hvs := (Finset.mem_sdiff.mp hvst).1
  have hvt := (Finset.mem_sdiff.mp hvst).2
  obtain ⟨j,hj,hbj⟩ := Finset.mem_image.mp ((«Σ».fullConeBasis_ray_set s) ▸ hvs)
  have hmeet : s.val∩t.val=(«Σ».wallIndices s j).image («Σ».fullConeBasis s) := by
    ext w
    constructor
    · intro hw
      obtain ⟨i,hi,hbi⟩ := Finset.mem_image.mp
        ((«Σ».fullConeBasis_ray_set s) ▸ (Finset.mem_inter.mp hw).1)
      have hij : i≠j := by
        intro he
        have hwv : w=v := hbi.symm.trans (he ▸ hbj)
        exact hvt (hwv ▸ (Finset.mem_inter.mp hw).2)
      exact Finset.mem_image.mpr ⟨i,Finset.mem_erase.mpr ⟨hij,hi⟩,hbi⟩
    · intro hw
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hw
      have his : «Σ».fullConeBasis s i∈s.val := by
        rw [«Σ».fullConeBasis_ray_set]
        exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
      refine Finset.mem_inter.mpr ⟨his,?_⟩
      by_contra hit
      have hiv : «Σ».fullConeBasis s i=v :=
        Finset.mem_singleton.mp (hv ▸ Finset.mem_sdiff.mpr ⟨his,hit⟩)
      exact (Finset.mem_erase.mp hi).1
        ((«Σ».fullConeBasis s).injective (hiv.trans hbj.symm))
  have hsub : insert u (s.val∩t.val)⊆t.val :=
    Finset.insert_subset hut Finset.inter_subset_right
  have huinter : u∉s.val∩t.val := fun h=>hus (Finset.mem_inter.mp h).1
  have hc : (insert u (s.val∩t.val)).card=n := by
    rw [Finset.card_insert_of_notMem huinter,hst]
    omega
  have ht : t.val=insert u (s.val∩t.val) :=
    (Finset.eq_of_subset_of_card_le hsub (by rw [«Σ».fullCones_card,hc])).symm
  exact ⟨j,hmeet,by rw [ht,hmeet]⟩

/-- In the quotient rank-one fan an extra ray cannot project to the
original positive ray: injectivity of the actual star-ray projection
would identify the two original rays. Hence its coordinate is `-1`. -/
theorem adjacentWall_transverse (s t : «Σ».fullCones) (j : Fin n)
    (u : Lattice n)
    (ht : t.val=insert u ((«Σ».wallIndices s j).image («Σ».fullConeBasis s)))
    (hus : u∉s.val) : («Σ».fullConeBasis s).repr u j = -1 := by
  let I := «Σ».wallIndices s j
  let b := «Σ».fullConeBasis s
  let Γ := «Σ».wallCurveFan s j
  have hFs : I.image b⊆s.val := «Σ».wallCone_subset_full s j
  have hFt : I.image b⊆t.val := by rw [ht]; exact Finset.subset_insert _ _
  have hu : u∈t.val\I.image b :=
    Finset.mem_sdiff.mpr ⟨by rw [ht]; exact Finset.mem_insert_self _ _,fun h=>hus (hFs h)⟩
  have hp := «Σ».projected_starRay_mem b I («Σ».wallCone_mem s j)
    («Σ».fullCones_mem t) hFt hu
  change coneQuotientLattice b I u ∈ Γ.rays at hp
  rw [Γ.oneDimensional_rays («Σ».wallIndices_codimension s j),
    Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with hp|hp
  · have hueq : u=b j := «Σ».coneQuotient_injective_star_rays b I
      («Σ».fullCones_mem t) («Σ».fullCones_mem s) hFt hFs hu
      («Σ».fullConeBasis_mem_sdiff_wall s j)
      (hp.trans («Σ».wall_quotient_positive s j).symm)
    apply (hus ?_).elim
    rw [hueq]
    exact (Finset.mem_sdiff.mp («Σ».fullConeBasis_mem_sdiff_wall s j)).1
  · let q : Fin (n-I.card) := ⟨0,by rw [«Σ».wallIndices_codimension]; omega⟩
    have hq := congrFun hp q
    rw [«Σ».wall_quotient_coordinate] at hq
    exact hq

variable (k : Type u) [Field k] (hpure : «Σ».IsPure)

/-- The degree condition on the actual invariant wall curves, expressed
using genuine sheaf pullback and the uniquely determined curve degree. -/
def CartierWallDegreesAtLeast (D : CartierData («Σ».fanScheme k)) (bound : ℕ) : Prop :=
  ∀ (s : «Σ».fullCones) (j : Fin n) (degree : ℤ),
    («Σ».wallCurveFan s j).OneDimensionalHasDegree («Σ».wallIndices_codimension s j) k
      ((Scheme.Modules.pullback («Σ».wallCurveInclusion s j k)).obj D.sheaf) degree →
        (bound : ℤ)≤degree

theorem cartierWallDegreesAtLeast_iso (D E : CartierData («Σ».fanScheme k))
    (F : D.sheaf ≅ E.sheaf) (bound : ℕ) :
    «Σ».CartierWallDegreesAtLeast k D bound ↔ «Σ».CartierWallDegreesAtLeast k E bound := by
  constructor
  · intro h s j d hd
    apply h s j d
    exact ((«Σ».wallCurveFan s j).oneDimensionalHasDegree_iso
      («Σ».wallIndices_codimension s j) k
      ((Scheme.Modules.pullback («Σ».wallCurveInclusion s j k)).mapIso F) d).mpr hd
  · intro h s j d hd
    apply h s j d
    exact ((«Σ».wallCurveFan s j).oneDimensionalHasDegree_iso
      («Σ».wallIndices_codimension s j) k
      ((Scheme.Modules.pullback («Σ».wallCurveInclusion s j k)).mapIso F) d).mp hd

theorem cartierCoefficients_hasWallSlacksAtLeast
    (D : CartierData («Σ».fanScheme k)) (bound : ℕ)
    (hD : «Σ».CartierWallDegreesAtLeast k D bound) :
    «Σ».HasWallSlacksAtLeast («Σ».cartierCoefficients k hpure D) bound := by
  intro s t hst u hut hus
  obtain ⟨j,hmeet,ht⟩ := «Σ».adjacentWall_basisIndex s t hst u hut hus
  exact hD s j _ («Σ».wallCurve_cartier_hasDegree s j k hpure D t u ht
    («Σ».adjacentWall_transverse s t j u ht hus))

/-- The recovered divisor polytope has exactly the original normal fan,
is smooth, and satisfies the same lower bound on every actual edge. -/
theorem exists_polytope_of_cartierCurveDegrees
    (D : CartierData («Σ».fanScheme k)) (bound : ℕ) (hbound : 0<bound)
    (hD : «Σ».CartierWallDegreesAtLeast k D bound) :
    ∃ P : LatticePolytope n,
      P.carrier=«Σ».fanPolytope (fun u=>(«Σ».cartierCoefficients k hpure D u : ℝ)) ∧
      P.Smooth ∧ P.normalFan=«Σ».realCones ∧ P.EdgesAtLeast bound :=
  «Σ».exists_smooth_latticePolytope_of_positive_wall_bounds hpure
    («Σ».cartierCoefficients k hpure D) bound hbound
    («Σ».cartierCoefficients_hasWallSlacksAtLeast k hpure D bound hD)

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.cartierCoefficients_hasWallSlacksAtLeast
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.exists_polytope_of_cartierCurveDegrees
