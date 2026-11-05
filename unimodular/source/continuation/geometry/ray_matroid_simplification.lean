module

public import Unimodular.RayContractions
public import Continuation.Geometry.VectorMatroidSimplification

set_option autoImplicit false

@[expose] public section

noncomputable section
open Set TauCeti.Toric
open scoped Matroid

namespace Unimodular.RayContractions

variable {N V : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : N →+ V}

/-- The ordinary unoriented matroid of the exact primitive ray vectors.
Opposite rays remain different labels before simplification. -/
def rayMatroid (Φ : Fan ι) : Matroid N :=
  VectorMatroid.onSet (K := ℝ) (fun u => ι u) {u | ConeBases.IsRay Φ u}

/-- The matroid clause of Lemma 6.4 on an actual set of ray labels.
The quotient fan is the genuine integral star fan supplied by the geometric
contraction theorem, and the ordinary matroid contraction has an isomorphic
simplification. Neither a simplification witness nor a quotient realization
is an input. -/
theorem lemma_6_4_simplification_of_subset
    (Φ : Fan ι) (hΦ : Φ.IsComplete) (hreg : Φ.IsRegular)
    (hcrit : ConeBases.PositiveCriterion Φ) (C : Set N)
    (hC : C ⊆ {u | ConeBases.IsRay Φ u}) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ N) (A : Finset (Fin n))
      (Ψ : Fan (CoordinateQuotients.quotientEmbedding A)),
      Ψ.IsComplete ∧ Ψ.IsRegular ∧ ConeBases.PositiveCriterion Ψ ∧
      (∀ w, ConeBases.IsRay Ψ w ↔
        ∃ u, ConeBases.IsRay Φ u ∧ CoordinateQuotients.projection b A u = w ∧ w ≠ 0) ∧
      Nonempty ((rayMatroid Φ ／ C).simplification ≂ (rayMatroid Ψ).simplification) := by
  classical
  obtain ⟨n, b, A, hF, hspan, hker, hzero, hpsurj, hqsurj,
    hcompat, hcomplete, hregular, hpositive, hrays⟩ :=
    lemma_6_4 Φ hΦ hreg hcrit C hC
  let q := CoordinateQuotients.projection b A
  let p := CoordinateQuotients.projection
    (CoordinateQuotients.realBasis ι Φ.lattice b) A
  let e := CoordinateQuotients.quotientEmbedding A
  let Ψ := CoordinateQuotients.starFan ι Φ.lattice b A Φ hF
  let R : Set N := {u | ConeBases.IsRay Φ u}
  have hcontract : rayMatroid Φ ／ C =
      VectorMatroid.onSet (K := ℝ) ((fun w => e w) ∘ q) (R \ C) := by
    change VectorMatroid.onSet (K := ℝ) (fun u => ι u) R ／ C = _
    rw [VectorMatroid.contract_onSet (fun u => ι u) hC p hker]
    apply congrArg (fun v => VectorMatroid.onSet (K := ℝ) v (R \ C))
    funext u
    exact hcompat u
  have himage : {w | w ∈ q '' (R \ C) ∧ e w ≠ 0} =
      {w | ConeBases.IsRay Ψ w} := by
    ext w
    constructor
    · rintro ⟨⟨u, hu, hqu⟩, hne⟩
      apply (hrays w).mpr
      refine ⟨u, hu.1, hqu, ?_⟩
      intro hw
      apply hne
      rw [hw, map_zero]
    · intro hw
      obtain ⟨u, hu, hqu, hne⟩ := (hrays w).mp hw
      have huC : u ∉ C := by
        intro huC
        have hqu0 : q u = 0 :=
          (hzero u).mpr (Submodule.subset_span ⟨u, huC, rfl⟩)
        exact hne (hqu.symm.trans hqu0)
      refine ⟨⟨u, ⟨hu, huC⟩, hqu⟩, ?_⟩
      intro he0
      apply hne
      apply (CoordinateQuotients.quotientEmbedding_isIntegralLattice A).injective
      simpa only [map_zero] using he0
  have htarget :
      VectorMatroid.onSet (K := ℝ) (fun w => e w)
          {w | w ∈ q '' (R \ C) ∧ e w ≠ 0} = rayMatroid Ψ := by
    change VectorMatroid.onSet (K := ℝ) (fun w => e w) _ =
      VectorMatroid.onSet (K := ℝ) (fun w => e w) _
    rw [himage]
  refine ⟨n, b, A, Ψ, hcomplete, hregular, hpositive, hrays, ?_⟩
  rw [hcontract, ← htarget]
  exact ⟨VectorMatroid.simplificationIsoNonzeroImage
    (K := ℝ) (fun w => e w) (fun u => q u) (R \ C)⟩

/-- Every ordinary contraction is covered, without requiring its supplied
set to lie in the ground: intersecting with the actual ray set does not
change a matroid contraction. Empty and full contractions are included. -/
theorem lemma_6_4_every_contraction
    (Φ : Fan ι) (hΦ : Φ.IsComplete) (hreg : Φ.IsRegular)
    (hcrit : ConeBases.PositiveCriterion Φ) (C : Set N) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ N) (A : Finset (Fin n))
      (Ψ : Fan (CoordinateQuotients.quotientEmbedding A)),
      Ψ.IsComplete ∧ Ψ.IsRegular ∧ ConeBases.PositiveCriterion Ψ ∧
      (∀ w, ConeBases.IsRay Ψ w ↔
        ∃ u, ConeBases.IsRay Φ u ∧ CoordinateQuotients.projection b A u = w ∧ w ≠ 0) ∧
      Nonempty ((rayMatroid Φ ／ C).simplification ≂ (rayMatroid Ψ).simplification) := by
  obtain ⟨n, b, A, Ψ, hcomplete, hregular, hpositive, hrays, hiso⟩ :=
    lemma_6_4_simplification_of_subset Φ hΦ hreg hcrit
      (C ∩ {u | ConeBases.IsRay Φ u}) Set.inter_subset_right
  refine ⟨n, b, A, Ψ, hcomplete, hregular, hpositive, hrays, ?_⟩
  change Nonempty (((rayMatroid Φ) ／ (C ∩ (rayMatroid Φ).E)).simplification ≂
    (rayMatroid Ψ).simplification) at hiso
  simpa only [Matroid.contract_inter_ground_eq] using hiso

end Unimodular.RayContractions

#print axioms Unimodular.RayContractions.lemma_6_4_simplification_of_subset
#print axioms Unimodular.RayContractions.lemma_6_4_every_contraction
