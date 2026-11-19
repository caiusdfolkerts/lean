module

public import Unimodular.RankThree
public import Unimodular.Quotients

@[expose] public section

noncomputable section

open scoped BigOperators Pointwise Topology
open Set TauCeti.Toric

namespace Unimodular.RankThree

/-- Every one of the six reference lines belongs to a full independent triple. -/
def completingTriple : Fin 6 → Fin 3 → Fin 6 :=
  ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1], ![3, 0, 2], ![4, 0, 1], ![5, 0, 1]]

theorem completingTriple_first : ∀ j, completingTriple j 0 = j := by decide

theorem completingTriple_det_ne_zero : ∀ j,
    (Pi.basisFun ℤ (Fin 3)).det (baseRoot ∘ completingTriple j) ≠ 0 := by
  intro j
  rw [det_eq_coordinate_rows]
  fin_cases j <;> norm_num [Pi.basisFun_equivFun, completingTriple, baseRoot,
    Function.comp_def, Matrix.det_fin_three]

/-- Nonzero columns are a consequence of the exact K4 dependence pattern. -/
theorem pattern_nonzero {N : Type*} [AddCommGroup N] [Module ℤ N]
    (b : Module.Basis (Fin 3) ℤ N) (U : Fin 6 → N)
    (hpattern : ∀ a : Fin 3 → Fin 6,
      b.det (U ∘ a) = 0 ↔ (Pi.basisFun ℤ (Fin 3)).det (baseRoot ∘ a) = 0) :
    ∀ j, U j ≠ 0 := by
  intro j
  have hd : b.det (U ∘ completingTriple j) ≠ 0 := fun h =>
    completingTriple_det_ne_zero j ((hpattern (completingTriple j)).1 h)
  have hi := (IntegralRigidity.independent_iff_det_ne_zero b _).2 hd
  simpa only [Function.comp_apply, completingTriple_first] using hi.ne_zero (0 : Fin 3)

variable {N V : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : N →+ V}

/-- The rank-three obstruction for an actual finite lattice fan, with its
primitive rays and arbitrary lattice presentation. All coordinate adapters and
the normalization of the six-line restriction are proved in the dependency chain. -/
theorem fan_no_K4_dependence_pattern (Φ : Fan ι)
    (hcomplete : Φ.IsComplete) (hregular : Φ.IsRegular)
    (hcriterion : ConeBases.PositiveCriterion Φ)
    (b : Module.Basis (Fin 3) ℤ N) (U : Fin 6 → N)
    (hrays : ∀ j, ConeBases.IsRay Φ (U j))
    (hpattern : ∀ a : Fin 3 → Fin 6,
      b.det (U ∘ a) = 0 ↔ (Pi.basisFun ℤ (Fin 3)).det (baseRoot ∘ a) = 0) : False := by
  obtain ⟨σ, hσ, hray⟩ :=
    FanBridge.exists_smoothCompleteFan_in_basis Φ hcomplete hregular hcriterion b
  apply no_K4_dependence_pattern σ hσ (fun j => b.equivFun (U j))
    (fun j => (hray (U j)).1 (hrays j))
  intro a
  rw [det_eq_coordinate_rows]
  simp only [Pi.basisFun_equivFun, LinearEquiv.refl_apply]
  change (Matrix.of (fun i => b.equivFun (U (a i)))).det = 0 ↔ _
  have ht := hpattern a
  rw [det_eq_coordinate_rows] at ht
  exact ht

variable {N' W : Type*} [AddCommGroup N']
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {ι' : N' →+ W}

/-- The obstruction persists through every rank-three linear contraction by a
ray-generated subspace, with the exact quotient lattice and all surviving rays.
The six retained rays can be chosen arbitrarily after the contraction; hence
deletions outside the six-line restriction are unrestricted. -/
theorem contracted_fan_no_K4_dependence_pattern (Φ : Fan ι)
    (hcomplete : Φ.IsComplete) (hregular : Φ.IsRegular)
    (hcriterion : ConeBases.PositiveCriterion Φ)
    (S : Set N) (hS : S ⊆ {u | ConeBases.IsRay Φ u})
    (p : V →ₗ[ℝ] W) (q : N →+ N')
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (hcompat : ∀ u, p (ι u) = ι' (q u)) (hι' : IsIntegralLattice ι')
    (hkernel : LinearMap.ker p = Submodule.span ℝ (ι '' S))
    (b : Module.Basis (Fin 3) ℤ N') (U : Fin 6 → N)
    (hrays : ∀ j, ConeBases.IsRay Φ (U j))
    (hpattern : ∀ a : Fin 3 → Fin 6,
      b.det (fun i => q (U (a i))) = 0 ↔
        (Pi.basisFun ℤ (Fin 3)).det (baseRoot ∘ a) = 0) : False := by
  obtain ⟨C, hC, hspan⟩ := RaySubspaces.ray_generated_subspace_is_cone_span
    Φ hcomplete hregular hcriterion S hS
  have hker : LinearMap.ker p = Submodule.span ℝ (C : Set V) := hkernel.trans hspan
  let Ψ := StarQuotients.starFan (p := p) (hker := hker) (Φ := Φ)
    (q := q) (hq := hcompat) (hι' := hι') (F := C) (hF := hC)
  obtain ⟨hΨcomplete, hΨregular, hΨcriterion, hΨrays⟩ :=
    PositiveQuotients.contraction_of_cone Φ hcomplete hregular p q hcompat hι'
      C hC hker hp hq hcriterion
  have hnonzero := pattern_nonzero b (fun j => q (U j)) hpattern
  apply fan_no_K4_dependence_pattern Ψ hΨcomplete hΨregular hΨcriterion b
    (fun j => q (U j)) _ hpattern
  intro j
  exact (hΨrays _).2 ⟨U j, hrays j, rfl, hnonzero j⟩

end Unimodular.RankThree
