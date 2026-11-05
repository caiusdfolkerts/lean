module

public import PaperVerification.ToricBundleFanStar
public import Mathlib.Topology.MetricSpace.Basic

@[expose] public section

/-!
# Completeness of the actual quotient star

The sum of the deleted cone's primitive rays lies in no cone which fails
to contain that cone. A finite union of closed basis cones stays away from
that point. Small perturbations in any quotient direction therefore lie
in cones containing the deleted cone, and projection followed by positive
rescaling proves completeness in the saturated quotient.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical

theorem isClosed_finiteRayCone_basis {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (Ambient n)) (I : Finset (Fin n)) :
    IsClosed (finiteRayCone (I.image b) : Set (Ambient n)) := by
  have he : (finiteRayCone (I.image b) : Set (Ambient n)) =
      (⋂ i, {x : Ambient n | 0 ≤ b.coord i x}) ∩
      (⋂ i, ⋂ (_ : i ∉ I), {x : Ambient n | b.coord i x = 0}) := by
    have hI : I.image b =
        @Finset.image (Fin n) (Ambient n)
          (fun (x y : Ambient n) => Classical.propDecidable (x = y)) b I := by
      ext y
      simp only [Finset.mem_image]
    ext x
    change (x ∈ finiteRayCone (I.image b)) ↔ _
    rw [hI]
    simpa only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq,
      Module.Basis.coord_apply] using (mem_finiteRayCone_basis_iff b I x)
  rw [he]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro i
    exact isClosed_le continuous_const (b.coord i).continuous_of_finiteDimensional
  · apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro hi
    exact isClosed_eq (b.coord i).continuous_of_finiteDimensional continuous_const

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem isClosed_latticeRayCone {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones) :
    IsClosed (latticeRayCone s : Set (Ambient n)) := by
  obtain ⟨b, I, rfl⟩ := «Σ».smooth s hs
  rw [latticeRayCone_basis]
  exact isClosed_finiteRayCone_basis (integralBasisReal b) I

/-- Every real direction admits a positive small perturbation of the ray
sum inside an actual cone containing the original cone. -/
theorem exists_small_perturbation_in_containing_cone
    {F : Finset (Lattice n)} (hF : F ∈ «Σ».cones) (x : Ambient n) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ s ∈ «Σ».cones, F ⊆ s ∧
      (∑ u ∈ F, embed n u) + ε • x ∈ latticeRayCone s := by
  let w : Ambient n := ∑ u ∈ F, embed n u
  let bad := «Σ».cones.filter (fun s => ¬ F ⊆ s)
  let Z : Set (Ambient n) := ⋃ s ∈ bad, (latticeRayCone s : Set (Ambient n))
  have hclosed : IsClosed Z := by
    apply isClosed_biUnion_finset
    intro s hs
    exact «Σ».isClosed_latticeRayCone (Finset.mem_filter.mp hs).1
  have hw : w ∉ Z := by
    intro hw
    obtain ⟨s, hs, hws⟩ := Set.mem_iUnion₂.mp hw
    exact (Finset.mem_filter.mp hs).2
      («Σ».sum_mem_cone_implies_subset hF (Finset.mem_filter.mp hs).1 hws)
  let φ : ℝ → Ambient n := fun ε => w + ε • x
  have hφ : Continuous φ := continuous_const.add (continuous_id.smul continuous_const)
  have hopen : IsOpen (φ ⁻¹' Zᶜ) := hclosed.isOpen_compl.preimage hφ
  have hzero : (0 : ℝ) ∈ φ ⁻¹' Zᶜ := by
    change w + (0 : ℝ) • x ∉ Z
    simpa only [zero_smul, add_zero] using hw
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen 0 hzero
  let ε : ℝ := δ / 2
  have hε : 0 < ε := div_pos hδ (by norm_num)
  have hεball : ε ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hε]
    dsimp only [ε]
    linarith
  have houtside : φ ε ∉ Z := hball hεball
  obtain ⟨s, hs, hφs⟩ := «Σ».complete (φ ε)
  have hFs : F ⊆ s := by
    by_contra hn
    apply houtside
    exact Set.mem_iUnion₂.mpr ⟨s, Finset.mem_filter.mpr ⟨hs, hn⟩, hφs⟩
  exact ⟨ε, hε, s, hs, hFs, hφs⟩

/-- The literal projected-cover statement required by `quotientStarFan`,
proved for every actual smooth cone, including the empty cone. -/
theorem coneQuotient_projected_cover
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b ∈ «Σ».cones) :
    ∀ y : Ambient (n - I.card), ∃ s ∈ «Σ».cones,
      I.image b ⊆ s ∧ y ∈ (latticeRayCone s).map (coneQuotientReal b I) := by
  intro y
  let F := I.image b
  let w : Ambient n := ∑ u ∈ F, embed n u
  let bad := «Σ».cones.filter (fun s => ¬ F ⊆ s)
  let Z : Set (Ambient n) := ⋃ s ∈ bad, (latticeRayCone s : Set (Ambient n))
  have hclosed : IsClosed Z := by
    apply isClosed_biUnion_finset
    intro s hs
    exact «Σ».isClosed_latticeRayCone (Finset.mem_filter.mp hs).1
  have hw : w ∉ Z := by
    intro hw
    obtain ⟨s, hs, hws⟩ := Set.mem_iUnion₂.mp hw
    have hscone := (Finset.mem_filter.mp hs).1
    have hnsub := (Finset.mem_filter.mp hs).2
    exact hnsub («Σ».sum_mem_cone_implies_subset hF hscone hws)
  let φ : ℝ → Ambient n := fun ε => w + ε • coneQuotientSectionReal b I y
  have hφ : Continuous φ := continuous_const.add (continuous_id.smul continuous_const)
  have hopen : IsOpen (φ ⁻¹' Zᶜ) := hclosed.isOpen_compl.preimage hφ
  have hzero : (0 : ℝ) ∈ φ ⁻¹' Zᶜ := by
    change w + (0 : ℝ) • coneQuotientSectionReal b I y ∉ Z
    simpa only [zero_smul, add_zero] using hw
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen 0 hzero
  let ε : ℝ := δ / 2
  have hε : 0 < ε := div_pos hδ (by norm_num)
  have hεball : ε ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hε]
    dsimp only [ε]
    linarith
  have houtside : φ ε ∉ Z := hball hεball
  obtain ⟨s, hs, hφs⟩ := «Σ».complete (φ ε)
  have hFs : F ⊆ s := by
    by_contra hn
    apply houtside
    exact Set.mem_iUnion₂.mpr ⟨s, Finset.mem_filter.mpr ⟨hs, hn⟩, hφs⟩
  have hwcone : w ∈ latticeRayCone (I.image b) := by
    apply Submodule.sum_mem
    intro u hu
    exact latticeRayCone_generator _ hu
  have hproj : coneQuotientReal b I (φ ε) = ε • y := by
    change coneQuotientReal b I (w + ε • coneQuotientSectionReal b I y) = ε • y
    rw [map_add, coneQuotient_zero_on_cone b I hwcone,
      map_smul, coneQuotient_section_real, zero_add]
  have hmem : ε • y ∈ (latticeRayCone s).map (coneQuotientReal b I) :=
    ⟨φ ε, hφs, hproj⟩
  have hscaled := PointedCone.smul_mem
    ((latticeRayCone s).map (coneQuotientReal b I)) (inv_nonneg.mpr hε.le) hmem
  refine ⟨s, hs, hFs, ?_⟩
  simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt hε), one_smul] using hscaled

/-- The actual saturated quotient star of any cone of a smooth complete
fan is a smooth complete fan, with no completeness premise left over. -/
def completeQuotientStarFan
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b ∈ «Σ».cones) : SmoothCompleteFan (n - I.card) :=
  «Σ».quotientStarFan b I («Σ».coneQuotient_projected_cover b I hF)

theorem completeQuotientStarFan_isPure (hpure : «Σ».IsPure)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b ∈ «Σ».cones) : («Σ».completeQuotientStarFan b I hF).IsPure :=
  «Σ».quotientStarFan_isPure hpure b I («Σ».coneQuotient_projected_cover b I hF)

end SmoothCompleteFan

end PaperVerification.ToricGeometry
