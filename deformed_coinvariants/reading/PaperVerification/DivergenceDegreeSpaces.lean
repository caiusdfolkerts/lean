module

public import PaperVerification.DivergenceCocycleComplex
public import PaperVerification.WeightedPolynomialPieces

/-!
# The actual homogeneous divergence--Koszul presentation

The first differential respects the exact shifted polynomial pieces. The
second differential is allowed to be projected to those pieces: the first
map commutes with this projection, so its zero composite is retained. At
parameter zero, regularity produces every relation, and projecting an actual
Koszul preimage gives a preimage in precisely the required shifted degree.

This supporting source has not yet been compiled. The degreewise rank and
equivariant comparisons must still be applied to these actual maps.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.DivergenceDegrees

open MvPolynomial DivergenceCocycle PolynomialDivergence
open PolynomialHomogeneousDerivations WeightedPolynomialPieces
open scoped BigOperators

variable {K ι : Type*} [CommRing K] [Fintype ι]
local notation "P" => MvPolynomial ι K
local notation "Der" => Derivation K P P

variable (L : LieRinehartSubalgebra P Der)
variable {r : ℕ} (b : Module.Basis (Fin r) P L)
variable (w : ι → ℕ) (δ : Fin r → ℕ) (ω : L →ₗ[P] P)

/-- These are the literal homogeneous-basis and degree-zero one-form
conditions on the displayed basis. -/
def HomogeneousFields : Prop :=
  ∀ i, HasDegree (integerWeights w) (b i : Der) (δ i : ℤ)

def HomogeneousValues : Prop := ∀ i, IsWeightedHomogeneous w (ω (b i)) (δ i)

theorem functional_basis_homogeneous
    (hfields : HomogeneousFields L b w δ)
    (hvalues : HomogeneousValues L b w δ ω) (t : K) (i : Fin r) :
    IsWeightedHomogeneous w (functional L ω t (b i)) (δ i) := by
  rw [functional_apply]
  apply IsWeightedHomogeneous.add
  · apply (weightedHomogeneousSubmodule K w (δ i)).smul_mem
    exact (homogeneous_cast_iff w _ (δ i)).mp (divergence_homogeneous (hfields i))
  · exact (weightedHomogeneousSubmodule K w (δ i)).smul_mem _ (hvalues i)

theorem project_operator
    (hfields : HomogeneousFields L b w δ)
    (hvalues : HomogeneousValues L b w δ ω) (t : K) (i : Fin r)
    (s d : ℕ) (p : P) :
    project w s d (operator L ω t (b i) p) =
      operator L ω t (b i) (project w (s+δ i) d p) := by
  rw [operator_apply,operator_apply,map_add,map_smul,
    project_multiply w (functional_basis_homogeneous L b w δ ω hfields hvalues t i),
    project_derivation w (hfields i)]

def projectCoefficients (d : ℕ) : (Fin r → P) →ₗ[K] (Fin r → P) where
  toFun v i := project w (δ i) d (v i)
  map_add' v u := by funext i; exact map_add _ _ _
  map_smul' a v := by funext i; exact map_smul _ _ _

@[simp] theorem projectCoefficients_apply (d : ℕ) (v : Fin r → P) (i : Fin r) :
    projectCoefficients w δ d v i = project w (δ i) d (v i) := rfl

/-- Projection commutes with the first map on arbitrary coefficient vectors,
not only vectors already lying in one homogeneous piece. -/
theorem project_first
    (hfields : HomogeneousFields L b w δ)
    (hvalues : HomogeneousValues L b w δ ω) (t : K) (d : ℕ) (v : Fin r → P) :
    project w 0 d (first L b ω t v) =
      first L b ω t (projectCoefficients w δ d v) := by
  simp only [first_apply,map_sum,projectCoefficients_apply]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [Nat.zero_add] using
    project_operator L b w δ ω hfields hvalues t i 0 d (v i)

/-- Coordinates of the actual second map on the actual vector-field module. -/
def secondCoordinates (t : K) : (Fin r → Fin r → P) →ₗ[K] (Fin r → P) :=
  (b.equivFun.restrictScalars K).toLinearMap.comp (second L b ω t)

theorem secondCoordinates_apply (t : K) (A : Fin r → Fin r → P) :
    secondCoordinates L b ω t A = b.equivFun (second L b ω t A) := rfl

theorem first_secondCoordinates (hω : IsClosed L ω) (t : K)
    (A : Fin r → Fin r → P) : first L b ω t (secondCoordinates L b ω t A)=0 := by
  rw [secondCoordinates_apply,first_eq_functional,b.sum_equivFun]
  exact LinearMap.congr_fun (functional_comp_second L b ω hω t) A

/-- Projecting the relation map introduces no extra premise about the degrees
of the structure coefficients or about equivariance of relation indices. -/
theorem first_projected_secondCoordinates
    (hfields : HomogeneousFields L b w δ)
    (hvalues : HomogeneousValues L b w δ ω) (hω : IsClosed L ω)
    (t : K) (d : ℕ) (A : Fin r → Fin r → P) :
    first L b ω t (projectCoefficients w δ d (secondCoordinates L b ω t A))=0 := by
  rw [←project_first L b w δ ω hfields hvalues,
    first_secondCoordinates L b ω hω,map_zero]

theorem first_zero (v : Fin r → P) :
    first L b ω 0 v = KoszulSyzygies.coefficient (fun i => ω (b i)) v := by
  rw [first_eq_functional,functional_zero]
  congr 1
  rw [←Module.Basis.equivFun_symm_apply]
  exact b.equivFun.apply_symm_apply v

theorem secondCoordinates_zero (A : Fin r → Fin r → P) :
    secondCoordinates L b ω 0 A = KoszulSyzygies.boundary (fun i => ω (b i)) A :=
  second_zero_coordinates L b ω A

def projectRelations (d : ℕ) (A : Fin r → Fin r → P) : Fin r → Fin r → P :=
  fun i j => project w (δ i+δ j) d (A i j)

theorem project_boundary (hvalues : HomogeneousValues L b w δ ω)
    (d : ℕ) (A : Fin r → Fin r → P) :
    projectCoefficients w δ d (KoszulSyzygies.boundary (fun i => ω (b i)) A) =
      KoszulSyzygies.boundary (fun i => ω (b i)) (projectRelations w δ d A) := by
  funext i
  simp only [projectCoefficients_apply,KoszulSyzygies.boundary_apply,map_sum,
    projectRelations]
  apply Finset.sum_congr rfl
  intro j hj
  rw [project_multiply w (hvalues j),map_sub]
  rw [Nat.add_comm (δ i) (δ j)]

/-- Regularity proves actual exactness in every shifted homogeneous degree,
including degrees where some or all coordinate pieces vanish. -/
theorem zero_parameter_degree_preimage
    (hvalues : HomogeneousValues L b w δ ω)
    (hregular : RingTheory.Sequence.IsWeaklyRegular P
      (List.ofFn fun i : Fin r => ω (b i)))
    (d : ℕ) (v : Fin r → P)
    (hv : ∀ i, v i ∈ piece w (δ i) d)
    (hz : first L b ω 0 v=0) :
    ∃ A : Fin r → Fin r → P,
      (∀ i j, A i j ∈ piece w (δ i+δ j) d) ∧
      secondCoordinates L b ω 0 A=v := by
  have hker : v ∈ (KoszulSyzygies.coefficient (fun i => ω (b i))).ker := by
    apply LinearMap.mem_ker.mpr
    rwa [first_zero] at hz
  rw [KoszulSyzygies.kernel_eq_boundary_range _ hregular] at hker
  obtain ⟨A,hA⟩ := hker
  refine ⟨projectRelations w δ d A,fun i j => project_mem _ _ _ _,?_⟩
  rw [secondCoordinates_zero,←project_boundary L b w δ ω hvalues,hA]
  funext i
  exact project_of_mem w (δ i) d (hv i)

end PaperVerification.DivergenceDegrees
