module

public import Unimodular.PositiveQuotients
public import Unimodular.RaySubspaces

@[expose] public section

open scoped Pointwise Topology BigOperators
open Set TauCeti.Toric

namespace Unimodular.RayContractions

variable {N V : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : N →+ V}

/-- Coordinate presentations identify the same actual face cone in the real ambient space. -/
theorem faceCone_eq {I : Type*} [Fintype I] [DecidableEq I]
    (hι : IsIntegralLattice ι) (b : Module.Basis I ℤ N) (A : Finset I) :
    CoordinateQuotients.faceCone ι hι b A =
      PointedCone.hull ℝ (ι '' (b '' (A : Set I))) := by
  unfold CoordinateQuotients.faceCone
  congr 1
  rw [Set.image_image]
  congr 1
  funext i
  exact CoordinateQuotients.realBasis_apply ι hι b i

/-- Lemma 6.4, including existence of the quotient lattice and fan. The real kernel is
exactly the ray-generated subspace; the integral kernel is its intersection with the
original lattice. The surviving coordinates are an explicit presentation of the actual
quotient, whose isomorphism is `CoordinateQuotients.quotientEquiv`.

All ray-generated subspaces, including zero and the entire ambient space, are allowed.
The quotient retains the exact images of primitive rays: only zero images and repeated
vectors disappear. -/
theorem lemma_6_4 (Φ : Fan ι) (hΦ : Φ.IsComplete) (hreg : Φ.IsRegular)
    (hcrit : ConeBases.PositiveCriterion Φ) (U : Set N)
    (hU : U ⊆ {u | ConeBases.IsRay Φ u}) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ N) (A : Finset (Fin n)),
      let q := CoordinateQuotients.projection b A
      let p := CoordinateQuotients.projection
        (CoordinateQuotients.realBasis ι Φ.lattice b) A
      let F := CoordinateQuotients.faceCone ι Φ.lattice b A
      ∃ hF : F ∈ Φ.cones,
        let Ψ := CoordinateQuotients.starFan ι Φ.lattice b A Φ hF
        Submodule.span ℝ (ι '' U) = Submodule.span ℝ (F : Set V) ∧
        LinearMap.ker p = Submodule.span ℝ (ι '' U) ∧
        (∀ u, q u = 0 ↔ ι u ∈ Submodule.span ℝ (ι '' U)) ∧
        Function.Surjective p ∧ Function.Surjective q ∧
        (∀ u, p (ι u) = CoordinateQuotients.quotientEmbedding A (q u)) ∧
        Ψ.IsComplete ∧ Ψ.IsRegular ∧ ConeBases.PositiveCriterion Ψ ∧
        (∀ w, ConeBases.IsRay Ψ w ↔
          ∃ u, ConeBases.IsRay Φ u ∧ q u = w ∧ w ≠ 0) := by
  classical
  obtain ⟨C, hC, hspan⟩ :=
    RaySubspaces.ray_generated_subspace_is_cone_span Φ hΦ hreg hcrit U hU
  obtain ⟨D, hD, hfull, hCD⟩ := FanMaximalCones.exists_full_supercone Φ hΦ hC
  obtain ⟨n, b, A, _, hCA⟩ := ConeBases.exists_basis_with_face Φ.lattice
    (Fan.isRegular_iff.1 hreg D hD) hfull hCD
  have heF : CoordinateQuotients.faceCone ι Φ.lattice b A = C := by
    rw [faceCone_eq, ← hCA]
  have hF : CoordinateQuotients.faceCone ι Φ.lattice b A ∈ Φ.cones := by
    rw [heF]
    exact hC
  refine ⟨n, b, A, hF, ?_⟩
  dsimp only
  have hs : Submodule.span ℝ (ι '' U) =
      Submodule.span ℝ (CoordinateQuotients.faceCone ι Φ.lattice b A : Set V) := by
    rw [heF]
    exact hspan
  have hk := CoordinateQuotients.real_kernel_eq_face_span ι Φ.lattice b A
  have hki (u : N) : CoordinateQuotients.projection b A u = 0 ↔
      ι u ∈ Submodule.span ℝ (ι '' U) := by
    rw [← LinearMap.mem_ker, CoordinateQuotients.ker_projection, hs]
    exact CoordinateQuotients.integer_kernel_iff_real_span ι Φ.lattice b A u
  have hc := PositiveQuotients.contraction_of_cone Φ hΦ hreg
    (CoordinateQuotients.projection (CoordinateQuotients.realBasis ι Φ.lattice b) A)
    (CoordinateQuotients.projection b A).toAddMonoidHom
    (CoordinateQuotients.projections_compatible ι Φ.lattice b A)
    (CoordinateQuotients.quotientEmbedding_isIntegralLattice A)
    (CoordinateQuotients.faceCone ι Φ.lattice b A) hF hk
    (CoordinateQuotients.projection_surjective _ _) (CoordinateQuotients.projection_surjective _ _)
    hcrit
  exact ⟨hs, hk.trans hs.symm, hki,
    CoordinateQuotients.projection_surjective _ _,
    CoordinateQuotients.projection_surjective _ _,
    CoordinateQuotients.projections_compatible ι Φ.lattice b A,
    hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩

/-- Any chosen subset of a lattice basis consisting of primitive fan rays can be
contracted in those exact coordinates. The cone spanned by the chosen basis vectors
need not itself belong to the fan: the positive-coordinate criterion supplies a fan
cone with the same real span. In particular, a pivot basis permits contraction of an
arbitrary specified ray without changing any of the surviving coordinate formulas. -/
theorem exists_coordinate_contraction {I : Type*} [Fintype I] [DecidableEq I]
    (Φ : Fan ι) (hΦ : Φ.IsComplete) (hreg : Φ.IsRegular)
    (hcrit : ConeBases.PositiveCriterion Φ) (b : Module.Basis I ℤ N)
    (A : Finset I) (hA : ∀ i ∈ A, ConeBases.IsRay Φ (b i)) :
    ∃ Ψ : Fan (CoordinateQuotients.quotientEmbedding A),
      Ψ.IsComplete ∧ Ψ.IsRegular ∧ ConeBases.PositiveCriterion Ψ ∧
      ∀ w, ConeBases.IsRay Ψ w ↔
        ∃ u, ConeBases.IsRay Φ u ∧ CoordinateQuotients.projection b A u = w ∧ w ≠ 0 := by
  classical
  let U : Set N := b '' (A : Set I)
  have hU : U ⊆ {u | ConeBases.IsRay Φ u} := by
    rintro u ⟨i, hi, rfl⟩
    exact hA i hi
  obtain ⟨F, hF, hspan⟩ :=
    RaySubspaces.ray_generated_subspace_is_cone_span Φ hΦ hreg hcrit U hU
  let p := CoordinateQuotients.projection (CoordinateQuotients.realBasis ι Φ.lattice b) A
  let q := (CoordinateQuotients.projection b A).toAddMonoidHom
  have hker : LinearMap.ker p = Submodule.span ℝ (F : Set V) := by
    change LinearMap.ker
      (CoordinateQuotients.projection (CoordinateQuotients.realBasis ι Φ.lattice b) A) = _
    rw [CoordinateQuotients.real_kernel_eq_face_span, faceCone_eq,
      RayHyperplanes.span_hull_eq]
    exact hspan
  have hcompat : ∀ u, p (ι u) = CoordinateQuotients.quotientEmbedding A (q u) :=
    CoordinateQuotients.projections_compatible ι Φ.lattice b A
  let Ψ := StarQuotients.starFan (p := p) (hker := hker) (Φ := Φ)
    (q := q) (hq := hcompat)
    (hι' := CoordinateQuotients.quotientEmbedding_isIntegralLattice A) (F := F) (hF := hF)
  refine ⟨Ψ, ?_⟩
  exact PositiveQuotients.contraction_of_cone Φ hΦ hreg p q hcompat
    (CoordinateQuotients.quotientEmbedding_isIntegralLattice A) F hF hker
    (CoordinateQuotients.projection_surjective _ _)
    (CoordinateQuotients.projection_surjective _ _) hcrit

end Unimodular.RayContractions
