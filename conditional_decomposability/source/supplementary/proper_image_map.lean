module

public import consolidated_dev.minkowski_map_core

@[expose] public section

/-!
# The weak-summand map in Lemma 4

This interface retains the supporting-face compatibility of the signed,
translated original parallel map. It also identifies the complementary
map explicitly, gives a positive scale, and returns actual image-hull
polytopes with their Minkowski equality and the exact image dimension.
-/

noncomputable section

namespace Papers.ProperImageMap

open Set Module AffineSubspace
open Papers.PolytopeFourRegularTail Papers.ParallelSupportEvaluation
open Papers.ParallelExposedFiber Papers.ParallelFaceDirections
open Papers.LinearImageFibers Papers.ProperImageFiberCount
open Papers.ProperImageWeakSummand Papers.CompatibleMinkowskiSummands
open Papers.NonnegativeParallelMaps Papers.FiniteHullPolytope
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical Pointwise

variable {n : ℕ}

/-- The proper-image argument yields support compatibility for a signed
translate of the given map, not merely for an unrelated map with the
same image hull. -/
theorem exists_signed_support_compatible
    (P : ConvexPolytope n) (hP : P.IsFullDim)
    (f : E n → E n) (hf : ParallelOnTail P P.vertices f)
    (hnonconstant : ¬ ∃ b : E n, ∀ x ∈ P.vertices, f x = b)
    (hproper : finrank ℝ (vectorSpan ℝ (f '' (P.vertices : Set (E n)))) < n)
    (hN : P.vertices.card < 4 * n - 4) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∃ c : E n,
      ParallelOnTail P P.vertices (fun x => σ • (f x - c)) ∧
      SupportsCompatible P (fun x => σ • (f x - c)) := by
  obtain ⟨x₀, hx₀⟩ := P.vertices_nonempty
  let c := f x₀
  let g : E n → E n := fun x => f x - c
  let L := vectorSpan ℝ (f '' (P.vertices : Set (E n)))
  let π : E n →L[ℝ] E n := Lᗮ.starProjection
  have hker : π.ker = L := by
    simp only [π, Submodule.ker_starProjection, Submodule.orthogonal_orthogonal]
  have hg : ParallelOnTail P P.vertices g := by
    intro x hx y hy hxy
    obtain ⟨μ, hμ⟩ := hf x hx y hy hxy
    refine ⟨μ, ?_⟩
    change (f y - c) - (f x - c) = _
    calc
      (f y - c) - (f x - c) = f y - f x := by abel
      _ = μ • (y - x) := hμ
  have hgvalues : ∀ x ∈ P.vertices, π (g x) = 0 := by
    intro x hx
    change g x ∈ π.ker
    rw [hker]
    exact vsub_mem_vectorSpan ℝ ⟨x, hx, rfl⟩ ⟨x₀, hx₀, rfl⟩
  have hgimage : vectorSpan ℝ (g '' (P.vertices : Set (E n))) = π.ker :=
    (centered_image_direction P f c).trans hker.symm
  have hg_nonconstant : ¬ ∃ b : E n, ∀ x ∈ P.vertices, g x = b := by
    rintro ⟨b, hb⟩
    apply hnonconstant
    refine ⟨b + c, ?_⟩
    intro x hx
    exact (sub_eq_iff_eq_add).mp (hb x hx)
  have hrpos : 1 ≤ finrank ℝ π.ker := by
    rw [hker]
    by_contra hn
    have hz : finrank ℝ L = 0 := by omega
    have hbot : L = ⊥ := Submodule.finrank_eq_zero.mp hz
    apply hnonconstant
    refine ⟨f x₀, ?_⟩
    intro x hx
    have hmem : f x - f x₀ ∈ L :=
      vsub_mem_vectorSpan ℝ ⟨x, hx, rfl⟩ ⟨x₀, hx₀, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact sub_eq_zero.mp hmem
  have hrproper : finrank ℝ π.ker < n := by rw [hker]; exact hproper
  obtain ⟨q, α, b, hα, hfiber⟩ :=
    exists_nonzero_homothetic_vertexFiber P hP g hg π
      hgimage hgvalues hrpos hrproper hN hg_nonconstant
  let w := fiberFunctional P π q
  have hwg : ∀ x ∈ P.vertices, w (g x) = 0 :=
    fun x hx => fiberFunctional_kernel P π q (g x) (hgvalues x hx)
  have hhom : ∀ x ∈ maxVertices P w, g x = α • x + b := by
    intro x hx
    apply hfiber x
    rw [vertexFiber, maxFace_vertices]
    exact hx
  rcases lt_or_gt_of_ne hα with hαneg | hαpos
  · let gneg : E n → E n := fun x => -g x
    have hgn : ParallelOnTail P P.vertices gneg := by
      intro x hx y hy hxy
      obtain ⟨μ, hμ⟩ := hg x hx y hy hxy
      refine ⟨-μ, ?_⟩
      change -g y - -g x = _
      calc
        -g y - -g x = -(g y - g x) := by abel
        _ = -(μ • (y - x)) := congrArg Neg.neg hμ
        _ = (-μ) • (y - x) := by module
    have hwgn : ∀ x ∈ P.vertices, w (gneg x) = 0 := by
      intro x hx
      change w (-g x) = 0
      rw [map_neg, hwg x hx, neg_zero]
    have hhomn : ∀ x ∈ maxVertices P w, gneg x = (-α) • x + (-b) := by
      intro x hx
      change -g x = _
      rw [hhom x hx]
      module
    have hc := supportsCompatible_of_positive_homothetic_fiber P gneg hgn
      w hwgn (-α) (-b) (neg_pos.mpr hαneg) hhomn
    refine ⟨-1, Or.inr rfl, c, ?_, ?_⟩
    · simpa only [gneg, g, neg_one_smul] using hgn
    · simpa only [gneg, g, neg_one_smul] using hc
  · have hc := supportsCompatible_of_positive_homothetic_fiber P g hg
      w hwg α b hαpos hhom
    refine ⟨1, Or.inl rfl, c, ?_, ?_⟩
    · simpa only [g, one_smul] using hg
    · simpa only [g, one_smul] using hc

/-- Lemma 4 with the map certificate retained explicitly.

For the signed translated map g, the theorem proves support compatibility,
then exhibits a positive scale ε and the complementary map x - ε • g x.
Both scaled maps have nonnegative edge scalars. Their actual convex image
hulls sum to P, and the first hull has precisely the original affine image
dimension.
-/
theorem proper_image_signed_weak_summand_map
    (P : ConvexPolytope n) (hP : P.IsFullDim)
    (f : E n → E n) (hf : ParallelOnTail P P.vertices f)
    (hnonconstant : ¬ ∃ b : E n, ∀ x ∈ P.vertices, f x = b)
    (hproper : finrank ℝ (vectorSpan ℝ (f '' (P.vertices : Set (E n)))) < n)
    (hN : P.vertices.card < 4 * n - 4) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∃ c : E n,
      let g : E n → E n := fun x => σ • (f x - c)
      ParallelOnTail P P.vertices g ∧ SupportsCompatible P g ∧
      ∃ ε : ℝ, 0 < ε ∧
        NonnegativeParallel P (fun x => ε • g x) ∧
        NonnegativeParallel P (fun x => x - ε • g x) ∧
        SupportsCompatible P (fun x => x - ε • g x) ∧
        ∃ A B : ConvexPolytope n,
          A.toSet = convexHull ℝ (g '' (P.vertices : Set (E n))) ∧
          B.toSet = convexHull ℝ
            ((fun x => x - ε • g x) '' (P.vertices : Set (E n))) ∧
          A.dim = finrank ℝ (vectorSpan ℝ (f '' (P.vertices : Set (E n)))) ∧
          P.toSet = ε • A.toSet + B.toSet := by
  obtain ⟨σ, hσ, c, hg, hcompatible⟩ :=
    exists_signed_support_compatible P hP f hf hnonconstant hproper hN
  let g : E n → E n := fun x => σ • (f x - c)
  have hn := nonnegative_of_supportsCompatible P g hg hcompatible
  obtain ⟨ε, hε, hscaled, hcomplement⟩ :=
    exists_scaled_complement_nonnegative P g hn
  have hcomplementSupport :=
    supportsCompatible_of_nonnegative P (fun x => x - ε • g x) hcomplement
  let A := imagePolytope P g
  let B := imagePolytope P (fun x => x - ε • g x)
  have hA : A.toSet = convexHull ℝ (g '' (P.vertices : Set (E n))) :=
    imagePolytope_toSet P g
  have hB : B.toSet = convexHull ℝ
      ((fun x => x - ε • g x) '' (P.vertices : Set (E n))) :=
    imagePolytope_toSet P (fun x => x - ε • g x)
  refine ⟨σ, hσ, c, hg, hcompatible, ε, hε, hscaled, hcomplement,
    hcomplementSupport, A, B, hA, hB, ?_, ?_⟩
  · change finrank ℝ (vectorSpan ℝ A.toSet) = _
    rw [hA, ← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]
    apply signed_shift_image_dimension P f σ
    rcases hσ with rfl | rfl <;> norm_num
  · have hsum := minkowski_eq_of_compatible_maps P
      (fun x => ε • g x) (fun x => x - ε • g x)
      (supportsCompatible_of_nonnegative P _ hscaled) hcomplementSupport
      (by intro x hx; abel)
    simpa only [A, B, imagePolytope_smul] using hsum

end Papers.ProperImageMap

end
