module
public import Papers.RationalKernelCharts
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Data.Fintype.Powerset
public import Papers.FacetSupport
public import Papers.AffineHomogeneousValues
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Papers.FacetNormalization
public import Papers.FacetHalfspaces
public import Papers.FaceVertexDictionary
public import Mathlib.Logic.Equiv.Option
public import Mathlib.Logic.Equiv.Sum
public import Papers.PolytopeIncidenceConfiguration
public import Papers.RationalApproximation
public import Papers.RationalityTenPolygonRelationRanks
public import Papers.FaceVertexCardinality
public import Papers.RationalityTenOrdinaryPolytopeDensity

/-! Canonical source bundle; each original file retains its own scopes. -/

section BundlePart0
/- Source: Papers/SupportedLabelStability.lean -/






@[expose] public section

/-! Compact supporting normals prevent new supported label sets locally. -/

noncomputable section
namespace Papers.SupportedLabelStability
open Matrix Set Filter Topology
variable {I : Type*} [Fintype I] [DecidableEq I] {r : ℕ}

def SupportedLabels (p : I → Fin r → ℝ) (S : Finset I) : Prop :=
  ∃ a : Fin r → ℝ, ‖a‖=1 ∧ (∀ i,0≤a ⬝ᵥ p i) ∧ ∀ i∈S,a ⬝ᵥ p i=0

theorem isClosed_supportedLabels (S : Finset I) :
    IsClosed {p : I → Fin r → ℝ | SupportedLabels p S} := by
  let U := Metric.sphere (0 : Fin r → ℝ) 1
  letI : CompactSpace U := (isCompact_iff_compactSpace).mp (isCompact_sphere 0 1)
  let T : Set ((I → Fin r → ℝ) × U) :=
    {z | (∀ i,0≤z.2.val ⬝ᵥ z.1 i) ∧ ∀ i∈S,z.2.val ⬝ᵥ z.1 i=0}
  have hd (i : I) : Continuous
      (fun z : (I → Fin r → ℝ) × U => z.2.val ⬝ᵥ z.1 i) :=
    (continuous_subtype_val.comp continuous_snd).dotProduct
      ((continuous_apply i).comp continuous_fst)
  have hnonneg : IsClosed (⋂ i : I,
      {z : (I → Fin r → ℝ) × U | 0≤z.2.val ⬝ᵥ z.1 i}) :=
    isClosed_iInter fun i => isClosed_le continuous_const (hd i)
  have hzero : IsClosed (⋂ i : I, ⋂ (_ : i∈S),
      {z : (I → Fin r → ℝ) × U | z.2.val ⬝ᵥ z.1 i=0}) :=
    isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_eq (hd i) continuous_const
  have hT : IsClosed T := by
    convert hnonneg.inter hzero using 1
    ext z
    simp [T]
  have himage : Prod.fst '' T={p : I → Fin r → ℝ | SupportedLabels p S} := by
    ext p
    constructor
    · rintro ⟨⟨q,a⟩,ha,rfl⟩
      exact ⟨a.val,by simpa [U,Metric.mem_sphere,dist_zero_right] using a.property,ha⟩
    · rintro ⟨a,ha,hpos,hzero⟩
      have haU : a∈U := by simpa [U,Metric.mem_sphere,dist_zero_right] using ha
      exact ⟨(p,⟨a,haU⟩),⟨hpos,hzero⟩,rfl⟩
  rw [←himage]
  exact isClosedMap_fst_of_compactSpace T hT

theorem eventually_no_new_supportedLabels (p : I → Fin r → ℝ) :
    ∀ᶠ q in 𝓝 p, ∀ S : Finset I, SupportedLabels q S → SupportedLabels p S := by
  apply eventually_all.mpr
  intro S
  by_cases hS : SupportedLabels p S
  · exact Filter.Eventually.of_forall fun _ _ => hS
  · have hN : {q : I → Fin r → ℝ | ¬SupportedLabels q S}∈𝓝 p :=
      (isClosed_supportedLabels S).isOpen_compl.mem_nhds hS
    filter_upwards [hN] with q hq hqS
    exact False.elim (hq hqS)

theorem supportedLabels_of_nonzero_normal
    (p : I → Fin r → ℝ) (S : Finset I) (a : Fin r → ℝ) (ha : a≠0)
    (hpos : ∀ i,0≤a ⬝ᵥ p i) (hzero : ∀ i∈S,a ⬝ᵥ p i=0) :
    SupportedLabels p S := by
  have hn : ‖a‖≠0 := norm_ne_zero_iff.mpr ha
  have heval (i : I) : (‖a‖⁻¹ • a) ⬝ᵥ p i=‖a‖⁻¹*(a ⬝ᵥ p i) := by
    simp [dotProduct,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]
  refine ⟨‖a‖⁻¹ • a,?_,?_,?_⟩
  · rw [norm_smul_of_nonneg (inv_nonneg.mpr (norm_nonneg a)),inv_mul_cancel₀ hn]
  · intro i
    rw [heval]
    exact mul_nonneg (inv_nonneg.mpr (norm_nonneg a)) (hpos i)
  · intro i hi
    rw [heval,hzero i hi,mul_zero]

end Papers.SupportedLabelStability

end
end
end BundlePart0

section BundlePart1
/- Source: Papers/SimplexFacetCoordinates.lean -/





@[expose] public section

/-!
# Coordinates dual to a simplex facet and its neighboring facets

The triangular evaluation pattern at the simplex vertices proves that the
supporting affine forms are a basis.  The coefficient sign argument then
constructs a homogeneous restoration point which is beyond the simplex
facet, on a prescribed subset of its neighboring hyperplanes, and strictly
inside every other facet halfspace.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open Papers.AffineCoordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι]

def simplexSupportFamily (f₀ : E d →ᵃ[ℝ] ℝ) (f : ι → E d →ᵃ[ℝ] ℝ) :
    Option ι → E d →ᵃ[ℝ] ℝ := fun i => i.elim f₀ f

@[simp] theorem simplexSupportFamily_none (f₀ : E d →ᵃ[ℝ] ℝ)
    (f : ι → E d →ᵃ[ℝ] ℝ) : simplexSupportFamily f₀ f none = f₀ := rfl

@[simp] theorem simplexSupportFamily_some (f₀ : E d →ᵃ[ℝ] ℝ)
    (f : ι → E d →ᵃ[ℝ] ℝ) (i : ι) : simplexSupportFamily f₀ f (some i) = f i := rfl

theorem simplexSupportFamily_linearIndependent
    (f₀ : E d →ᵃ[ℝ] ℝ) (f : ι → E d →ᵃ[ℝ] ℝ)
    (p : ι → E d) (q : E d)
    (h₀ : ∀ i, f₀ (p i) = 0) (hq : f₀ q ≠ 0)
    (hdiag : ∀ i, f i (p i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → f i (p j) = 0) :
    LinearIndependent ℝ (simplexSupportFamily f₀ f) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c heq i
  have hc : ∀ j, c (some j) = 0 := by
    intro j
    have h := congrArg (affineFormEvaluation (p j)) heq
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at h
    change (∑ k, c k * simplexSupportFamily f₀ f k (p j)) = 0 at h
    simp only [Fintype.sum_option, simplexSupportFamily_none,
      simplexSupportFamily_some, h₀ j, mul_zero, zero_add] at h
    have hsum : (∑ k, c (some k) * f k (p j)) = c (some j) * f j (p j) := by
      apply Finset.sum_eq_single j
      · intro k _ hkj
        rw [hoff k j hkj, mul_zero]
      · intro hj
        exact False.elim (hj (Finset.mem_univ _))
    rw [hsum] at h
    exact (mul_eq_zero.mp h).resolve_right (hdiag j)
  cases i with
  | some j => exact hc j
  | none =>
    have h := congrArg (affineFormEvaluation q) heq
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at h
    change (∑ k, c k * simplexSupportFamily f₀ f k q) = 0 at h
    simp only [Fintype.sum_option, simplexSupportFamily_none,
      simplexSupportFamily_some, hc, zero_mul, Finset.sum_const_zero, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_right hq

def simplexSupportBasis
    (hcard : Fintype.card ι = d)
    (f₀ : E d →ᵃ[ℝ] ℝ) (f : ι → E d →ᵃ[ℝ] ℝ)
    (p : ι → E d) (q : E d)
    (h₀ : ∀ i, f₀ (p i) = 0) (hq : f₀ q ≠ 0)
    (hdiag : ∀ i, f i (p i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → f i (p j) = 0) :
    Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank'
    (simplexSupportFamily f₀ f)
    (simplexSupportFamily_linearIndependent f₀ f p q h₀ hq hdiag hoff)
    (by simp [AffineMap.finrank_eq, hcard])

@[simp] theorem simplexSupportBasis_apply
    (hcard : Fintype.card ι = d)
    (f₀ : E d →ᵃ[ℝ] ℝ) (f : ι → E d →ᵃ[ℝ] ℝ)
    (p : ι → E d) (q : E d)
    (h₀ : ∀ i, f₀ (p i) = 0) (hq : f₀ q ≠ 0)
    (hdiag : ∀ i, f i (p i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → f i (p j) = 0) (i : Option ι) :
    simplexSupportBasis hcard f₀ f p q h₀ hq hdiag hoff i =
      simplexSupportFamily f₀ f i := by
  simp only [simplexSupportBasis, coe_basisOfLinearIndependentOfCardEqFinrank']

theorem basis_repr_at_simplex_vertex
    (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ)) (p : ι → E d)
    (h₀ : ∀ i, b none (p i) = 0)
    (hoff : ∀ i j, i ≠ j → b (some i) (p j) = 0)
    (g : E d →ᵃ[ℝ] ℝ) (i : ι) :
    b.repr g (some i) * b (some i) (p i) = g (p i) := by
  have h := congrArg (affineFormEvaluation (p i)) (b.sum_repr g)
  simp only [map_sum, map_smul, smul_eq_mul] at h
  change (∑ j, b.repr g j * b j (p i)) = g (p i) at h
  simp only [Fintype.sum_option, h₀ i, mul_zero, zero_add] at h
  have hsum : (∑ j, b.repr g (some j) * b (some j) (p i)) =
      b.repr g (some i) * b (some i) (p i) := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [hoff j i hji, mul_zero]
    · intro hi
      exact False.elim (hi (Finset.mem_univ _))
  rwa [hsum] at h

theorem basis_repr_some_nonneg
    (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ)) (p : ι → E d)
    (h₀ : ∀ i, b none (p i) = 0)
    (hdiag : ∀ i, 0 < b (some i) (p i))
    (hoff : ∀ i j, i ≠ j → b (some i) (p j) = 0)
    (g : E d →ᵃ[ℝ] ℝ) (hg : ∀ i, 0 ≤ g (p i)) (i : ι) :
    0 ≤ b.repr g (some i) := by
  have heq := basis_repr_at_simplex_vertex b p h₀ hoff g i
  have hnonneg : 0 ≤ b.repr g (some i) * b (some i) (p i) := heq.symm ▸ hg i
  exact (mul_nonneg_iff_of_pos_right (hdiag i)).mp hnonneg

/-- The coefficient with respect to the simplex facet is negative for
every other genuine facet.  All hypotheses refer to ordinary geometric
facets and their vertex evaluations. -/
theorem simplexFacet_other_coefficient_neg
    (P : ConvexPolytope d) (F : Option ι → Set (E d))
    (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ)) (p : ι → E d)
    (hF : ∀ i, IsFacet P (F i)) (hb : ∀ i, SupportsFace P (F i) (b i))
    (hp : ∀ i, p i ∈ P.toSet)
    (h₀ : ∀ i, b none (p i) = 0)
    (hdiag : ∀ i, 0 < b (some i) (p i))
    (hoff : ∀ i j, i ≠ j → b (some i) (p j) = 0)
    (G : Set (E d)) (g : E d →ᵃ[ℝ] ℝ)
    (hG : IsFacet P G) (hg : SupportsFace P G g)
    (hne : ∀ i, G ≠ F i) : b.repr g none < 0 := by
  apply facet_support_distinguished_coordinate_neg P F b hF hb G g hG hg hne none
  intro i hi
  cases i with
  | none => exact False.elim (hi rfl)
  | some j =>
    exact basis_repr_some_nonneg b p h₀ hdiag hoff g (fun k => hg.1 _ (hp k)) j

def restorationValues (t : ι → ℝ) : Option ι → ℝ := fun i => i.elim (-1) t

def restorationVector
    (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ)) (t : ι → ℝ) : E d × ℝ :=
  realizeAffineValues b (restorationValues t)

@[simp] theorem restorationVector_none
    (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ)) (t : ι → ℝ) :
    homogeneousEvaluation (restorationVector b t) (b none) = -1 := by
  change homogeneousEvaluation (realizeAffineValues b (restorationValues t)) (b none) = -1
  exact realizeAffineValues_basis b (restorationValues t) none

@[simp] theorem restorationVector_some
    (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ)) (t : ι → ℝ) (i : ι) :
    homogeneousEvaluation (restorationVector b t) (b (some i)) = t i := by
  change homogeneousEvaluation (realizeAffineValues b (restorationValues t)) (b (some i)) = t i
  exact realizeAffineValues_basis b (restorationValues t) (some i)

theorem restorationVector_other_facet_pos
    (P : ConvexPolytope d) (F : Option ι → Set (E d))
    (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ)) (p : ι → E d)
    (hF : ∀ i, IsFacet P (F i)) (hb : ∀ i, SupportsFace P (F i) (b i))
    (hp : ∀ i, p i ∈ P.toSet)
    (h₀ : ∀ i, b none (p i) = 0)
    (hdiag : ∀ i, 0 < b (some i) (p i))
    (hoff : ∀ i j, i ≠ j → b (some i) (p j) = 0)
    (G : Set (E d)) (g : E d →ᵃ[ℝ] ℝ)
    (hG : IsFacet P G) (hg : SupportsFace P G g)
    (hne : ∀ i, G ≠ F i) (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) :
    0 < homogeneousEvaluation (restorationVector b t) g := by
  have hn := simplexFacet_other_coefficient_neg P F b p hF hb hp h₀ hdiag hoff G g hG hg hne
  have hc := basis_repr_some_nonneg b p h₀ hdiag hoff g (fun i => hg.1 _ (hp i))
  rw [homogeneousEvaluation_expansion b, Fintype.sum_option]
  simp only [restorationVector_none, restorationVector_some, mul_neg_one]
  exact add_pos_of_pos_of_nonneg (neg_pos.mpr hn)
    (Finset.sum_nonneg (fun i _ => mul_nonneg (hc i) (ht i)))

end Papers.Polytopes

end
end
end BundlePart1

section BundlePart2
/- Source: Papers/RestorationCone.lean -/




@[expose] public section

/-!
# The cone over a simplex facet

The supporting forms through a proposed new vertex have a diagonal
evaluation matrix on the old simplex vertices.  This produces an actual
basis of edge vectors.  The cone cut on the exterior side of the simplex
hyperplane is exactly the convex hull of the new vertex and the simplex.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι]

def restorationConeForm (f₀ : E d →ᵃ[ℝ] ℝ)
    (f : ι → E d →ᵃ[ℝ] ℝ) (a : E d) (i : ι) : E d →ᵃ[ℝ] ℝ :=
  f i - (f i a / f₀ a) • f₀

theorem restorationConeForm_at_apex (f₀ : E d →ᵃ[ℝ] ℝ)
    (f : ι → E d →ᵃ[ℝ] ℝ) (a : E d) (ha : f₀ a ≠ 0) (i : ι) :
    restorationConeForm f₀ f a i a = 0 := by
  change f i a - (f i a / f₀ a) * f₀ a = 0
  rw [div_mul_cancel₀ _ ha, sub_self]

theorem restorationConeForm_on_hyperplane (f₀ : E d →ᵃ[ℝ] ℝ)
    (f : ι → E d →ᵃ[ℝ] ℝ) (a x : E d) (hx : f₀ x = 0) (i : ι) :
    restorationConeForm f₀ f a i x = f i x := by
  change f i x - (f i a / f₀ a) * f₀ x = f i x
  rw [hx, mul_zero, sub_zero]

theorem restorationConeForm_nonneg
    (f₀ : E d →ᵃ[ℝ] ℝ) (f : ι → E d →ᵃ[ℝ] ℝ)
    (a x : E d) (ha : f₀ a < 0) (hax : ∀ i, 0 ≤ f i a)
    (hx₀ : 0 ≤ f₀ x) (hx : ∀ i, 0 ≤ f i x) (i : ι) :
    0 ≤ restorationConeForm f₀ f a i x := by
  change 0 ≤ f i x - (f i a / f₀ a) * f₀ x
  have hc : f i a / f₀ a ≤ 0 := div_nonpos_of_nonneg_of_nonpos (hax i) ha.le
  exact sub_nonneg.mpr ((mul_nonpos_of_nonpos_of_nonneg hc hx₀).trans (hx i))

theorem diagonal_edge_family_independent
    (a : E d) (p : ι → E d) (g : ι → E d →ᵃ[ℝ] ℝ)
    (ha : ∀ i, g i a = 0)
    (hdiag : ∀ i, g i (p i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → g i (p j) = 0) :
    LinearIndependent ℝ (fun i => p i - a) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have h := congrArg (g i).linear hc
  simp only [map_sum, map_smul, smul_eq_mul, map_zero,
    ← vsub_eq_sub, AffineMap.linear_apply_vsub, ha i] at h
  simp only [vsub_eq_sub, sub_zero] at h
  have hsum : (∑ j, c j * g i (p j)) = c i * g i (p i) := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [hoff i j hji.symm, mul_zero]
    · intro hi
      exact False.elim (hi (Finset.mem_univ _))
  rw [hsum] at h
  exact (mul_eq_zero.mp h).resolve_right (hdiag i)

def diagonalEdgeBasis (hcard : Fintype.card ι = d)
    (a : E d) (p : ι → E d) (g : ι → E d →ᵃ[ℝ] ℝ)
    (ha : ∀ i, g i a = 0)
    (hdiag : ∀ i, g i (p i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → g i (p j) = 0) : Basis ι ℝ (E d) :=
  basisOfLinearIndependentOfCardEqFinrank'
    (fun i => p i - a)
    (diagonal_edge_family_independent a p g ha hdiag hoff)
    (by simpa only [finrank_euclideanSpace_fin] using hcard)

@[simp] theorem diagonalEdgeBasis_apply (hcard : Fintype.card ι = d)
    (a : E d) (p : ι → E d) (g : ι → E d →ᵃ[ℝ] ℝ)
    (ha : ∀ i, g i a = 0)
    (hdiag : ∀ i, g i (p i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → g i (p j) = 0) (i : ι) :
    diagonalEdgeBasis hcard a p g ha hdiag hoff i = p i - a := by
  simp only [diagonalEdgeBasis, coe_basisOfLinearIndependentOfCardEqFinrank']

theorem diagonal_form_coordinate
    (a : E d) (p : ι → E d) (g : ι → E d →ᵃ[ℝ] ℝ)
    (b : Basis ι ℝ (E d)) (hb : ∀ i, b i = p i - a)
    (ha : ∀ i, g i a = 0)
    (hoff : ∀ i j, i ≠ j → g i (p j) = 0) (x : E d) (i : ι) :
    g i x = b.repr (x - a) i * g i (p i) := by
  have h := congrArg (g i).linear (b.sum_repr (x - a))
  simp only [map_sum, map_smul, smul_eq_mul, hb,
    ← vsub_eq_sub, AffineMap.linear_apply_vsub, ha i] at h
  simp only [vsub_eq_sub, sub_zero] at h
  rw [← h]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rw [hoff i j hji.symm, mul_zero]
  · intro hi
    exact False.elim (hi (Finset.mem_univ _))

theorem affine_height_of_edge_coordinates
    (a : E d) (p : ι → E d) (b : Basis ι ℝ (E d))
    (hb : ∀ i, b i = p i - a) (f₀ : E d →ᵃ[ℝ] ℝ)
    (hp : ∀ i, f₀ (p i) = 0) (x : E d) :
    f₀ x = f₀ a * (1 - ∑ i, b.repr (x - a) i) := by
  have h := congrArg f₀.linear (b.sum_repr (x - a))
  simp only [map_sum, map_smul, smul_eq_mul, hb,
    ← vsub_eq_sub, AffineMap.linear_apply_vsub, hp] at h
  simp only [vsub_eq_sub, zero_sub,
    mul_neg, Finset.sum_neg_distrib, ← Finset.sum_mul] at h
  nlinarith

theorem diagonal_cone_cut_mem_simplex
    (a : E d) (p : ι → E d) (g : ι → E d →ᵃ[ℝ] ℝ)
    (b : Basis ι ℝ (E d)) (hb : ∀ i, b i = p i - a)
    (ha : ∀ i, g i a = 0) (hdiag : ∀ i, 0 < g i (p i))
    (hoff : ∀ i j, i ≠ j → g i (p j) = 0)
    (f₀ : E d →ᵃ[ℝ] ℝ) (hf₀a : f₀ a < 0) (hp₀ : ∀ i, f₀ (p i) = 0)
    (x : E d) (hx : ∀ i, 0 ≤ g i x) (hx₀ : f₀ x ≤ 0) :
    x ∈ convexHull ℝ (insert a (Set.range p)) := by
  let c : ι → ℝ := fun i => b.repr (x - a) i
  have hc : ∀ i, 0 ≤ c i := by
    intro i
    have h := hx i
    rw [diagonal_form_coordinate a p g b hb ha hoff x i] at h
    exact (mul_nonneg_iff_of_pos_right (hdiag i)).mp h
  have hsum : ∑ i, c i ≤ 1 := by
    have h := affine_height_of_edge_coordinates a p b hb f₀ hp₀ x
    change f₀ x = f₀ a * (1 - ∑ i, c i) at h
    nlinarith
  let z : Option ι → E d := fun i => i.elim a p
  let w : Option ι → ℝ := fun i => i.elim (1 - ∑ i, c i) c
  have hw : ∀ i ∈ (Finset.univ : Finset (Option ι)), 0 ≤ w i := by
    intro i _
    cases i with
    | none => exact sub_nonneg.mpr hsum
    | some j => exact hc j
  have htotal : ∑ i : Option ι, w i = 1 := by
    simp only [Fintype.sum_option, w, Option.elim_none, Option.elim_some]
    ring
  have hz : ∀ i ∈ (Finset.univ : Finset (Option ι)),
      z i ∈ convexHull ℝ (insert a (Set.range p)) := by
    intro i _
    apply subset_convexHull ℝ _
    cases i with
    | none => exact Set.mem_insert _ _
    | some j => exact Set.mem_insert_of_mem _ ⟨j, rfl⟩
  have hconv := (convex_convexHull ℝ (insert a (Set.range p))).sum_mem hw htotal hz
  have hrep : (∑ i : Option ι, w i • z i) = x := by
    simp only [Fintype.sum_option, w, z, Option.elim_none, Option.elim_some]
    have h := b.sum_repr (x - a)
    simp only [hb, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul] at h
    change (∑ i, c i • p i) - (∑ i, c i) • a = x - a at h
    calc
      (1 - ∑ i, c i) • a + ∑ i, c i • p i =
          a + ((∑ i, c i • p i) - (∑ i, c i) • a) := by module
      _ = a + (x - a) := by rw [h]
      _ = x := by module
  exact hrep ▸ hconv

end Papers.Polytopes

end
end
end BundlePart2

section BundlePart3
/- Source: Papers/VertexAddition.lean -/



@[expose] public section

/-!
# Adjoining an exterior point while retaining all old vertices

The new point has an explicit strict separating affine form.  For every
old vertex, a supporting form which is positive at the new point can be
added to its old exposing form.  This proves that the displayed generators
are exactly the extreme vertices of the enlarged convex hull.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem polytope_eq_of_vertices_eq {P Q : ConvexPolytope d}
    (h : P.vertices = Q.vertices) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

theorem exterior_point_not_mem_vertices (P : ConvexPolytope d) (a : E d)
    (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.toSet, 0 ≤ f x) (ha : f a < 0) :
    a ∉ P.vertices := by
  intro h
  exact (not_lt_of_ge (hf a (subset_convexHull ℝ _ h))) ha

theorem exposing_form_after_addition (P : ConvexPolytope d) (a : E d)
    (v : VertexType P) (g : E d →ᵃ[ℝ] ℝ)
    (hg : ∀ x ∈ P.toSet, 0 ≤ g x) (hgv : g v.val = 0) (hga : 0 < g a) :
    ∃ f : E d →ᵃ[ℝ] ℝ, f v.val = 0 ∧ 0 < f a ∧
      ∀ w ∈ P.vertices, w ≠ v.val → 0 < f w := by
  obtain ⟨f, hf⟩ := exists_supportsFace P (vertex_isFace P v.property)
  have hfv : f v.val = 0 := hf.eq_zero (Set.mem_singleton _)
  let t : ℝ := (|f a| + 1) / g a
  have ht : 0 < t := div_pos (by positivity) hga
  refine ⟨f + t • g, ?_, ?_, ?_⟩
  · change f v.val + t * g v.val = 0
    rw [hfv, hgv, mul_zero, add_zero]
  · change 0 < f a + t * g a
    have hmul : t * g a = |f a| + 1 := div_mul_cancel₀ _ (ne_of_gt hga)
    rw [hmul]
    have h := neg_abs_le (f a)
    linarith
  · intro w hw hwv
    have hwP : w ∈ P.toSet := subset_convexHull ℝ _ hw
    have hfw : 0 < f w := by
      rcases lt_or_eq_of_le (hf.1 w hwP) with hp | he
      · exact hp
      · have hmem := (hf.mem_iff w).mpr ⟨hwP, he.symm⟩
        exact False.elim (hwv hmem)
    change 0 < f w + t * g w
    exact add_pos_of_pos_of_nonneg hfw (mul_nonneg ht.le (hg w hwP))

/-- Actual convex-hull extension.  The preservation premise asks only for
supporting affine forms and is discharged combinatorially in restoration. -/
def addExteriorVertex (P : ConvexPolytope d) (a : E d)
    (f₀ : E d →ᵃ[ℝ] ℝ) (hf₀ : ∀ x ∈ P.toSet, 0 ≤ f₀ x) (ha : f₀ a < 0)
    (hretain : ∀ v : VertexType P, ∃ g : E d →ᵃ[ℝ] ℝ,
      (∀ x ∈ P.toSet, 0 ≤ g x) ∧ g v.val = 0 ∧ 0 < g a) : ConvexPolytope d := by
  classical
  apply polytopeOfStrictMinima (insert a P.vertices) ⟨a, Finset.mem_insert_self _ _⟩
  intro x hx
  rcases Finset.mem_insert.mp hx with hxa | hx
  · subst x
    refine ⟨f₀.linear.toContinuousLinearMap, ?_⟩
    intro y hy hya
    have hyP := (Finset.mem_insert.mp hy).resolve_left hya
    have hfy := hf₀ y (subset_convexHull ℝ _ hyP)
    have hfa := ha
    rw [affine_form_apply f₀ a] at hfa
    rw [affine_form_apply f₀ y] at hfy
    change f₀.linear a < f₀.linear y
    linarith
  · let v : VertexType P := ⟨x, hx⟩
    obtain ⟨g, hg, hgv, hga⟩ := hretain v
    obtain ⟨f, hfv, hfa, hfw⟩ := exposing_form_after_addition P a v g hg hgv hga
    refine ⟨f.linear.toContinuousLinearMap, ?_⟩
    intro y hy hyx
    have hfy : 0 < f y := by
      rcases Finset.mem_insert.mp hy with rfl | hyP
      · exact hfa
      · exact hfw y hyP hyx
    rw [affine_form_apply f v.val] at hfv
    rw [affine_form_apply f y] at hfy
    change f.linear x < f.linear y
    change f.linear x + f 0 = 0 at hfv
    linarith

@[simp] theorem addExteriorVertex_vertices (P : ConvexPolytope d) (a : E d)
    (f₀ : E d →ᵃ[ℝ] ℝ) (hf₀ : ∀ x ∈ P.toSet, 0 ≤ f₀ x) (ha : f₀ a < 0)
    (hretain : ∀ v : VertexType P, ∃ g : E d →ᵃ[ℝ] ℝ,
      (∀ x ∈ P.toSet, 0 ≤ g x) ∧ g v.val = 0 ∧ 0 < g a) :
    (addExteriorVertex P a f₀ hf₀ ha hretain).vertices = insert a P.vertices := rfl

theorem body_subset_addExteriorVertex (P : ConvexPolytope d) (a : E d)
    (f₀ : E d →ᵃ[ℝ] ℝ) (hf₀ : ∀ x ∈ P.toSet, 0 ≤ f₀ x) (ha : f₀ a < 0)
    (hretain : ∀ v : VertexType P, ∃ g : E d →ᵃ[ℝ] ℝ,
      (∀ x ∈ P.toSet, 0 ≤ g x) ∧ g v.val = 0 ∧ 0 < g a) :
    P.toSet ⊆ (addExteriorVertex P a f₀ hf₀ ha hretain).toSet :=
  convexHull_mono (fun _ hx => Finset.mem_insert_of_mem hx)

theorem addExteriorVertex_fullDim (P : ConvexPolytope d) (hP : P.IsFullDim) (a : E d)
    (f₀ : E d →ᵃ[ℝ] ℝ) (hf₀ : ∀ x ∈ P.toSet, 0 ≤ f₀ x) (ha : f₀ a < 0)
    (hretain : ∀ v : VertexType P, ∃ g : E d →ᵃ[ℝ] ℝ,
      (∀ x ∈ P.toSet, 0 ≤ g x) ∧ g v.val = 0 ∧ 0 < g a) :
    (addExteriorVertex P a f₀ hf₀ ha hretain).IsFullDim := by
  let Q := addExteriorVertex P a f₀ hf₀ ha hretain
  have hle : P.dim ≤ Q.dim := Submodule.finrank_mono
    (vectorSpan_mono ℝ (body_subset_addExteriorVertex P a f₀ hf₀ ha hretain))
  have hupper : Q.dim ≤ d := by
    change finrank ℝ (vectorSpan ℝ Q.toSet) ≤ d
    simpa only [finrank_euclideanSpace_fin] using
      (Submodule.finrank_le (vectorSpan ℝ Q.toSet))
  change Q.dim = d
  have heq : P.dim = d := hP
  exact le_antisymm hupper (le_trans heq.ge hle)

theorem addExteriorVertex_card (P : ConvexPolytope d) (a : E d)
    (f₀ : E d →ᵃ[ℝ] ℝ) (hf₀ : ∀ x ∈ P.toSet, 0 ≤ f₀ x) (ha : f₀ a < 0)
    (hretain : ∀ v : VertexType P, ∃ g : E d →ᵃ[ℝ] ℝ,
      (∀ x ∈ P.toSet, 0 ≤ g x) ∧ g v.val = 0 ∧ 0 < g a) :
    (addExteriorVertex P a f₀ hf₀ ha hretain).vertices.card = P.vertices.card + 1 := by
  rw [addExteriorVertex_vertices, Finset.card_insert_of_notMem
    (exterior_point_not_mem_vertices P a f₀ hf₀ ha)]

theorem addExteriorVertex_delete (P : ConvexPolytope d) (a : E d)
    (f₀ : E d →ᵃ[ℝ] ℝ) (hf₀ : ∀ x ∈ P.toSet, 0 ≤ f₀ x) (ha : f₀ a < 0)
    (hretain : ∀ v : VertexType P, ∃ g : E d →ᵃ[ℝ] ℝ,
      (∀ x ∈ P.toSet, 0 ≤ g x) ∧ g v.val = 0 ∧ 0 < g a)
    (hne : ((addExteriorVertex P a f₀ hf₀ ha hretain).vertices.erase a).Nonempty) :
    deleteVertex (addExteriorVertex P a f₀ hf₀ ha hretain) a hne = P := by
  apply polytope_eq_of_vertices_eq
  rw [deleteVertex_vertices, addExteriorVertex_vertices,
    Finset.erase_insert (exterior_point_not_mem_vertices P a f₀ hf₀ ha)]

theorem addExteriorVertex_coordinates (P : ConvexPolytope d) (a : E d)
    (f₀ : E d →ᵃ[ℝ] ℝ) (hf₀ : ∀ x ∈ P.toSet, 0 ≤ f₀ x) (ha : f₀ a < 0)
    (hretain : ∀ v : VertexType P, ∃ g : E d →ᵃ[ℝ] ℝ,
      (∀ x ∈ P.toSet, 0 ≤ g x) ∧ g v.val = 0 ∧ 0 < g a)
    (K : Subfield ℝ) (hPK : CoordinatesIn K P) (haK : ∀ i, a i ∈ K) :
    CoordinatesIn K (addExteriorVertex P a f₀ hf₀ ha hretain) := by
  intro x hx i
  rcases Finset.mem_insert.mp hx with rfl | hxP
  · exact haK i
  · exact hPK x hxP i

end Papers.Polytopes

end
end
end BundlePart3

section BundlePart4
/- Source: Papers/ExtensionHalfspaces.lean -/




@[expose] public section

/-!
# The exact halfspaces after extension beyond a simplex facet

The old nonvisible facets and the cone facets give the whole enlarged
convex hull.  The proof treats the two sides of the simplex hyperplane
separately and uses the explicit barycentric cone calculation outside.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι]

def ExtensionFacetIndex (Q : ConvexPolytope d) (T : Set (E d)) (ι : Type*) :=
  Sum {F : FacetType Q // F.val.val ≠ T} ι

instance extensionFacetIndexFintype (Q : ConvexPolytope d) (T : Set (E d)) :
    Fintype (ExtensionFacetIndex Q T ι) :=
  inferInstanceAs (Fintype (Sum {F : FacetType Q // F.val.val ≠ T} ι))

def extensionFacetForm (Q : ConvexPolytope d) (T : Set (E d))
    (f₀ : E d →ᵃ[ℝ] ℝ) (f : ι → E d →ᵃ[ℝ] ℝ) (a : E d) :
    ExtensionFacetIndex Q T ι → E d →ᵃ[ℝ] ℝ :=
  Sum.elim (fun F => chosenFacetForm Q F.val) (restorationConeForm f₀ f a)

theorem old_body_subset_extension (Q R : ConvexPolytope d) (a : E d)
    (hvertices : R.vertices = insert a Q.vertices) : Q.toSet ⊆ R.toSet := by
  change convexHull ℝ (Q.vertices : Set (E d)) ⊆ convexHull ℝ (R.vertices : Set (E d))
  rw [hvertices]
  exact convexHull_mono (fun _ hx => Finset.mem_insert_of_mem hx)

theorem extension_fullDim (Q R : ConvexPolytope d) (hQ : Q.IsFullDim) (a : E d)
    (hvertices : R.vertices = insert a Q.vertices) : R.IsFullDim := by
  have hle : Q.dim ≤ R.dim := Submodule.finrank_mono
    (vectorSpan_mono ℝ (old_body_subset_extension Q R a hvertices))
  have hupper : R.dim ≤ d := by
    change finrank ℝ (vectorSpan ℝ R.toSet) ≤ d
    simpa only [finrank_euclideanSpace_fin] using
      (Submodule.finrank_le (vectorSpan ℝ R.toSet))
  have heq : Q.dim = d := hQ
  have hlower : d ≤ R.dim := le_trans heq.ge hle
  exact le_antisymm hupper hlower

theorem affine_nonneg_on_extension (Q R : ConvexPolytope d) (a : E d)
    (hvertices : R.vertices = insert a Q.vertices) (g : E d →ᵃ[ℝ] ℝ)
    (hgQ : ∀ x ∈ Q.toSet, 0 ≤ g x) (hga : 0 ≤ g a) :
    ∀ x ∈ R.toSet, 0 ≤ g x := by
  apply affine_nonneg_on_hull R.vertices g
  intro x hx
  rw [hvertices] at hx
  rcases Finset.mem_insert.mp hx with rfl | hxQ
  · exact hga
  · exact hgQ x (subset_convexHull ℝ _ hxQ)

theorem simplex_hull_subset_extension
    (Q R : ConvexPolytope d) (a : E d)
    (hvertices : R.vertices = insert a Q.vertices)
    (p : ι → E d) (hp : ∀ i, p i ∈ Q.vertices) :
    convexHull ℝ (insert a (Set.range p)) ⊆ R.toSet := by
  apply convexHull_mono
  intro x hx
  rw [hvertices]
  rcases Set.mem_insert_iff.mp hx with rfl | ⟨i, rfl⟩
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (hp i)

theorem extensionFacetForms_nonneg
    (Q R : ConvexPolytope d) (a : E d)
    (hvertices : R.vertices = insert a Q.vertices)
    (T : Set (E d)) (f₀ : E d →ᵃ[ℝ] ℝ) (f : ι → E d →ᵃ[ℝ] ℝ)
    (hf₀ : ∀ x ∈ Q.toSet, 0 ≤ f₀ x)
    (hf : ∀ i x, x ∈ Q.toSet → 0 ≤ f i x)
    (ha₀ : f₀ a < 0) (ha : ∀ i, 0 ≤ f i a)
    (hother : ∀ F : FacetType Q, F.val.val ≠ T → 0 ≤ chosenFacetForm Q F a) :
    ∀ i : ExtensionFacetIndex Q T ι, ∀ x ∈ R.toSet,
      0 ≤ extensionFacetForm Q T f₀ f a i x := by
  intro i
  cases i with
  | inl F =>
    exact affine_nonneg_on_extension Q R a hvertices (chosenFacetForm Q F.val)
      (chosenFacetForm_supports Q F.val).1 (hother F.val F.property)
  | inr i =>
    apply affine_nonneg_on_extension Q R a hvertices (restorationConeForm f₀ f a i)
    · intro x hx
      exact restorationConeForm_nonneg f₀ f a x ha₀ ha (hf₀ x hx) (fun j => hf j x hx) i
    · exact (restorationConeForm_at_apex f₀ f a (ne_of_lt ha₀) i).symm.le

/-- This is equality of subsets of the entire ambient Euclidean space,
not only equality on a prescribed list of generators. -/
theorem extension_body_iff_halfspaces
    (Q R : ConvexPolytope d) (hQ : Q.IsFullDim)
    (a : E d) (hvertices : R.vertices = insert a Q.vertices)
    (T : Set (E d)) (hT : IsFacet Q T)
    (f₀ : E d →ᵃ[ℝ] ℝ) (hf₀ : SupportsFace Q T f₀)
    (f : ι → E d →ᵃ[ℝ] ℝ)
    (hf : ∀ i x, x ∈ Q.toSet → 0 ≤ f i x)
    (p : ι → E d) (hp : ∀ i, p i ∈ Q.vertices)
    (hp₀ : ∀ i, f₀ (p i) = 0)
    (hdiag : ∀ i, 0 < f i (p i))
    (hoff : ∀ i j, i ≠ j → f i (p j) = 0)
    (hcard : Fintype.card ι = d)
    (ha₀ : f₀ a < 0) (ha : ∀ i, 0 ≤ f i a)
    (hother : ∀ F : FacetType Q, F.val.val ≠ T → 0 ≤ chosenFacetForm Q F a)
    (x : E d) :
    x ∈ R.toSet ↔ ∀ i : ExtensionFacetIndex Q T ι,
      0 ≤ extensionFacetForm Q T f₀ f a i x := by
  constructor
  · intro hx i
    exact extensionFacetForms_nonneg Q R a hvertices T f₀ f hf₀.1 hf ha₀ ha hother i x hx
  · intro hx
    by_cases hx₀ : 0 ≤ f₀ x
    · apply old_body_subset_extension Q R a hvertices
      apply (mem_body_iff_chosenFacetForms_nonneg Q hQ x).mpr
      intro F
      by_cases hFT : F.val.val = T
      · obtain ⟨c, hc, heq⟩ := supportsFacet_positive_proportional Q hQ T hT
          (chosenFacetForm Q F) f₀ (hFT ▸ chosenFacetForm_supports Q F) hf₀
        rw [heq]
        exact mul_nonneg hc.le hx₀
      · exact hx (Sum.inl ⟨F, hFT⟩)
    · let g := restorationConeForm f₀ f a
      have hga : ∀ i, g i a = 0 := restorationConeForm_at_apex f₀ f a (ne_of_lt ha₀)
      have hgdiag : ∀ i, 0 < g i (p i) := by
        intro i
        rw [show g i (p i) = f i (p i) from
          restorationConeForm_on_hyperplane f₀ f a (p i) (hp₀ i) i]
        exact hdiag i
      have hgoff : ∀ i j, i ≠ j → g i (p j) = 0 := by
        intro i j hij
        rw [show g i (p j) = f i (p j) from
          restorationConeForm_on_hyperplane f₀ f a (p j) (hp₀ j) i]
        exact hoff i j hij
      let b := diagonalEdgeBasis hcard a p g hga (fun i => ne_of_gt (hgdiag i)) hgoff
      have hb : ∀ i, b i = p i - a :=
        diagonalEdgeBasis_apply hcard a p g hga (fun i => ne_of_gt (hgdiag i)) hgoff
      have hcone := diagonal_cone_cut_mem_simplex a p g b hb hga hgdiag hgoff
        f₀ ha₀ hp₀ x (fun i => hx (Sum.inr i)) (le_of_not_ge hx₀)
      exact simplex_hull_subset_extension Q R a hvertices p hp hcone

end Papers.Polytopes

end
end
end BundlePart4

section BundlePart5
/- Source: Papers/SimplexFacetChart.lean -/



@[expose] public section

/-!
# A positive chart for simplex-facet restoration

A common affine chart is proved to exist on the finite old vertex set and
the proposed homogeneous restoration point.  The exceptional simplex
case is kept explicit: either some neighboring support is positive at the
new point, or there is a further facet.  No chart existence hypothesis is
silently introduced into the restoration argument.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open Papers.AffineCoordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem affine_basis_not_all_zero
    (b : Basis ι ℝ (E d →ᵃ[ℝ] ℝ)) (x : E d) : ¬∀ i, b i x = 0 := by
  intro hz
  have h := congrArg (fun a : E d →ᵃ[ℝ] ℝ => a x)
    (b.sum_repr (AffineMap.const ℝ (E d) (1 : ℝ)))
  simp only [affineForm_sum_apply, AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul,
    hz, mul_zero, Finset.sum_const_zero, AffineMap.coe_const, Function.const_apply] at h
  exact zero_ne_one h

theorem positive_weighted_affine_basis
    (b : Basis ι ℝ (E d →ᵃ[ℝ] ℝ)) (x : E d)
    (hx : ∀ i, 0 ≤ b i x) (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    0 < (∑ i, w i • b i) x := by
  simp only [affineForm_sum_apply, AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul]
  have hn : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ w i * b i x :=
    fun i _ => mul_nonneg (hw i).le (hx i)
  have hsum := Finset.sum_nonneg hn
  by_contra hnot
  have heq : ∑ i, w i * b i x = 0 := le_antisymm (le_of_not_gt hnot) hsum
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hn).mp heq
  apply affine_basis_not_all_zero b x
  intro i
  exact (mul_eq_zero.mp (hz i (Finset.mem_univ _))).resolve_left (ne_of_gt (hw i))

/-- A finite set of strict positive inequalities permits a common small
positive perturbation.  The proof takes a finite minimum of admissible
positive parameters through induction. -/
theorem finite_positive_perturbation {α : Type*} (S : Finset α) (f h : α → ℝ)
    (hf : ∀ x ∈ S, 0 < f x) (hh : ∀ x ∈ S, 0 ≤ h x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ S, ε * h x < f x := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert x S hxS ih =>
    obtain ⟨ε₀, hε₀, hS⟩ := ih
      (fun y hy => hf y (Finset.mem_insert_of_mem hy))
      (fun y hy => hh y (Finset.mem_insert_of_mem hy))
    obtain ⟨ε₁, hε₁, h₁⟩ := exists_pos_mul_lt (hf x (Finset.mem_insert_self _ _)) (h x)
    refine ⟨min ε₀ ε₁, lt_min hε₀ hε₁, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with hy | hy
    · subst y
      calc
        min ε₀ ε₁ * h x ≤ ε₁ * h x :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (hh x (Finset.mem_insert_self _ _))
        _ < f x := by simpa only [mul_comm] using h₁
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _)
        (hh y (Finset.mem_insert_of_mem hy))).trans_lt (hS y hy)

def positiveRestorationChart
    (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ)) (ε : ℝ) : E d →ᵃ[ℝ] ℝ :=
  ε • b none + ∑ i, b (some i)

def negativeRestorationChart
    (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ)) (ε : ℝ) : E d →ᵃ[ℝ] ℝ :=
  ∑ i, b (some i) - ε • b none

theorem restoration_positive_chart_of_some_positive
    (P : ConvexPolytope d) (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ))
    (hb : ∀ i x, x ∈ P.toSet → 0 ≤ b i x)
    (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) (hpos : ∃ i, 0 < t i) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ x ∈ P.toSet, 0 < positiveRestorationChart b ε x) ∧
      0 < homogeneousEvaluation (restorationVector b t) (positiveRestorationChart b ε) := by
  have hs : 0 < ∑ i, t i := by
    obtain ⟨i, hi⟩ := hpos
    exact lt_of_lt_of_le hi (Finset.single_le_sum (fun j _ => ht j) (Finset.mem_univ _))
  let ε : ℝ := (∑ i, t i) / 2
  have hε : 0 < ε := half_pos hs
  refine ⟨ε, hε, ?_, ?_⟩
  · intro x hx
    let w : Option ι → ℝ := fun i => i.elim ε (fun _ => 1)
    have hw : ∀ i, 0 < w i := by
      intro i
      cases i with
      | none => exact hε
      | some _ => exact zero_lt_one
    have h := positive_weighted_affine_basis b x (fun i => hb i x hx) w hw
    simpa only [Fintype.sum_option, w, Option.elim_none, Option.elim_some,
      one_smul, positiveRestorationChart] using h
  · rw [positiveRestorationChart, map_add, map_smul, map_sum]
    simp only [restorationVector_none, restorationVector_some, smul_eq_mul, mul_neg_one]
    dsimp only [ε]
    linarith

theorem neighbor_support_sum_pos_of_other_facet
    (P : ConvexPolytope d) (F : Option ι → Set (E d))
    (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ)) (p : ι → E d)
    (hF : ∀ i, IsFacet P (F i)) (hb : ∀ i, SupportsFace P (F i) (b i))
    (hp : ∀ i, p i ∈ P.toSet)
    (h₀ : ∀ i, b none (p i) = 0)
    (hdiag : ∀ i, 0 < b (some i) (p i))
    (hoff : ∀ i j, i ≠ j → b (some i) (p j) = 0)
    (G : Set (E d)) (g : E d →ᵃ[ℝ] ℝ)
    (hG : IsFacet P G) (hg : SupportsFace P G g)
    (hne : ∀ i, G ≠ F i) (x : E d) (hx : x ∈ P.toSet) :
    0 < ∑ i, b (some i) x := by
  have hnonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ b (some i) x :=
    fun i _ => (hb (some i)).1 x hx
  have hsum := Finset.sum_nonneg hnonneg
  by_contra hnot
  have hz : ∑ i, b (some i) x = 0 := le_antisymm (le_of_not_gt hnot) hsum
  have hzero : ∀ i, b (some i) x = 0 :=
    fun i => (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hz i (Finset.mem_univ _)
  have hrepr := homogeneousEvaluation_expansion b (x, (1 : ℝ)) g
  simp only [homogeneousEvaluation_homogenize, Fintype.sum_option, hzero,
    mul_zero, Finset.sum_const_zero, add_zero] at hrepr
  have ha := simplexFacet_other_coefficient_neg P F b p hF hb hp h₀ hdiag hoff G g hG hg hne
  have hnx := (hb none).1 x hx
  have hgx := hg.1 x hx
  have hnone : b none x = 0 := by nlinarith
  apply affine_basis_not_all_zero b x
  intro i
  cases i with
  | none => exact hnone
  | some j => exact hzero j

theorem restoration_positive_chart_of_other_facet
    (P : ConvexPolytope d) (F : Option ι → Set (E d))
    (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ)) (p : ι → E d)
    (hF : ∀ i, IsFacet P (F i)) (hb : ∀ i, SupportsFace P (F i) (b i))
    (hp : ∀ i, p i ∈ P.toSet)
    (h₀ : ∀ i, b none (p i) = 0)
    (hdiag : ∀ i, 0 < b (some i) (p i))
    (hoff : ∀ i j, i ≠ j → b (some i) (p j) = 0)
    (G : Set (E d)) (g : E d →ᵃ[ℝ] ℝ)
    (hG : IsFacet P G) (hg : SupportsFace P G g)
    (hne : ∀ i, G ≠ F i) (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ x ∈ P.vertices, 0 < negativeRestorationChart b ε x) ∧
      0 < homogeneousEvaluation (restorationVector b t) (negativeRestorationChart b ε) := by
  obtain ⟨ε, hε, hbound⟩ := finite_positive_perturbation P.vertices
    (fun x => ∑ i, b (some i) x) (b none)
    (fun x hx => neighbor_support_sum_pos_of_other_facet P F b p hF hb hp h₀ hdiag hoff
      G g hG hg hne x (subset_convexHull ℝ _ hx))
    (fun x hx => (hb none).1 x (subset_convexHull ℝ _ hx))
  refine ⟨ε, hε, ?_, ?_⟩
  · intro x hx
    change 0 < (∑ i, b (some i)) x - ε * b none x
    rw [affineForm_sum_apply]
    exact sub_pos.mpr (hbound x hx)
  · rw [negativeRestorationChart, map_sub, map_sum, map_smul]
    simp only [restorationVector_none, restorationVector_some, smul_eq_mul, mul_neg_one]
    have hsum : 0 ≤ ∑ i, t i := Finset.sum_nonneg (fun i _ => ht i)
    linarith

end Papers.Polytopes

end
end
end BundlePart5

section BundlePart6
/- Source: Papers/FiniteHalfspaceFacets.lean -/




@[expose] public section

/-!
# Facet completeness for a finite halfspace description

The average of all vertices of a face detects every supporting form
vanishing on the face.  If every defining inequality were strict there,+a small explicit displacement would leave the polytope through the face
while still satisfying all the defining inequalities.  This proves
completeness of the displayed geometric facet list.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

def finitePointAverage (S : Finset (E d)) : E d :=
  (S.card : ℝ)⁻¹ • ∑ x ∈ S, x

theorem finitePointAverage_mem (S : Finset (E d)) (hS : S.Nonempty) :
    finitePointAverage S ∈ convexHull ℝ (S : Set (E d)) := by
  have hn : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  have h := S.centerMass_mem_convexHull
    (s := (S : Set (E d))) (w := fun _ => (1 : ℝ)) (z := id)
    (fun _ _ => zero_le_one) (by simpa using hn) (fun _ hx => hx)
  simpa [Finset.centerMass, finitePointAverage] using h

theorem affine_apply_finitePointAverage (S : Finset (E d)) (hS : S.Nonempty)
    (f : E d →ᵃ[ℝ] ℝ) :
    f (finitePointAverage S) = (S.card : ℝ)⁻¹ * ∑ x ∈ S, f x := by
  have hn : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  rw [affine_form_apply f, finitePointAverage, map_smul, map_sum, smul_eq_mul]
  have hsum : (∑ x ∈ S, f x) = ∑ x ∈ S, (f.linear x + f 0) :=
    Finset.sum_congr rfl (fun x _ => affine_form_apply f x)
  rw [hsum]
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul]
  field_simp <;> ring

theorem affine_zero_on_hull (S : Finset (E d)) (f : E d →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ S, f x = 0) :
    ∀ x ∈ convexHull ℝ (S : Set (E d)), f x = 0 := by
  intro x hx
  have hn := affine_nonneg_on_hull S f (fun y hy => (hf y hy).symm.le) x hx
  have hp := affine_nonneg_on_hull S (-f)
    (fun y hy => by change 0 ≤ -f y; rw [hf y hy, neg_zero]) x hx
  change 0 ≤ -f x at hp
  linarith

theorem affine_average_zero_iff (S : Finset (E d)) (hS : S.Nonempty)
    (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ S, 0 ≤ f x) :
    f (finitePointAverage S) = 0 ↔ ∀ x ∈ S, f x = 0 := by
  have hn : (S.card : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hS.card_pos.ne')
  rw [affine_apply_finitePointAverage S hS f, mul_eq_zero, or_iff_right hn]
  exact Finset.sum_eq_zero_iff_of_nonneg hf

theorem proper_face_has_active_halfspace
    {ι : Type*} [Fintype ι] (P : ConvexPolytope d)
    (f : ι → E d →ᵃ[ℝ] ℝ)
    (hbody : ∀ x, x ∈ P.toSet ↔ ∀ i, 0 ≤ f i x)
    (F : Set (E d)) (hF : P.IsFace F) (hproper : F ≠ P.toSet) :
    ∃ i, ∀ x ∈ F, f i x = 0 := by
  let S := P.vertices.filter (· ∈ F)
  have hS : S.Nonempty := (facePolytope P hF).vertices_nonempty
  let p := finitePointAverage S
  have hpF : p ∈ F := by
    rw [face_eq_hull_vertices P hF]
    exact finitePointAverage_mem S hS
  have hpP : p ∈ P.toSet := face_subset_toSet P hF hpF
  by_cases hz : ∃ i, f i p = 0
  · obtain ⟨i, hi⟩ := hz
    refine ⟨i, ?_⟩
    have hzero : ∀ x ∈ S, f i x = 0 :=
      (affine_average_zero_iff S hS (f i)
        (fun x hx => (hbody x).mp
          (subset_convexHull ℝ _ (Finset.mem_filter.mp hx).1) i)).mp hi
    intro x hx
    rw [face_eq_hull_vertices P hF] at hx
    exact affine_zero_on_hull S (f i) hzero x hx
  · have hpos : ∀ i, 0 < f i p := by
      intro i
      exact lt_of_le_of_ne ((hbody p).mp hpP i) (fun hi => hz ⟨i, hi.symm⟩)
    obtain ⟨g, hg⟩ := exists_supportsFace P hF
    obtain ⟨y, hyP, hyF⟩ : ∃ y, y ∈ P.toSet ∧ y ∉ F := by
      by_contra hy
      push_neg at hy
      exact hproper (Set.Subset.antisymm (face_subset_toSet P hF) hy)
    have hgp : g p = 0 := hg.eq_zero hpF
    have hgy : 0 < g y := by
      have hn := hg.1 y hyP
      exact lt_of_le_of_ne hn (fun hz => hyF ((hg.mem_iff y).mpr ⟨hyP, hz.symm⟩))
    let u : E d := p - y
    obtain ⟨ε, hε, hbound⟩ := finite_positive_perturbation
      (Finset.univ : Finset ι) (fun i => f i p) (fun i => |(f i).linear u|)
      (fun i _ => hpos i) (fun i _ => abs_nonneg _)
    let x := p + ε • u
    have hfx (i : ι) : f i x = f i p + ε * (f i).linear u := by
      rw [affine_form_apply (f i) x, affine_form_apply (f i) p]
      dsimp only [x]
      rw [map_add, map_smul, smul_eq_mul]
      ring
    have hxP : x ∈ P.toSet := by
      apply (hbody x).mpr
      intro i
      rw [hfx i]
      have hb := hbound i (Finset.mem_univ _)
      have hneg := mul_le_mul_of_nonneg_left (neg_abs_le ((f i).linear u)) hε.le
      linarith
    have hgu : g.linear u = -g y := by
      rw [affine_form_apply g p] at hgp
      rw [affine_form_apply g y]
      dsimp only [u]
      rw [map_sub]
      linarith
    have hgx : g x = -ε * g y := by
      rw [affine_form_apply g x]
      dsimp only [x]
      rw [map_add, map_smul, smul_eq_mul, hgu]
      have h := hgp
      rw [affine_form_apply g p] at h
      nlinarith
    have hn := hg.1 x hxP
    rw [hgx] at hn
    have hp := mul_pos hε hgy
    nlinarith

/-- A finite halfspace description whose zero sets are genuine facets
contains every facet of the polytope. -/
theorem facets_exhausted_by_halfspaces
    {ι : Type*} [Fintype ι] (P : ConvexPolytope d)
    (f : ι → E d →ᵃ[ℝ] ℝ)
    (hbody : ∀ x, x ∈ P.toSet ↔ ∀ i, 0 ≤ f i x)
    (hfacet : ∀ i, IsFacet P (affineZeroFace P (f i)))
    (F : Set (E d)) (hF : IsFacet P F) :
    ∃ i, F = affineZeroFace P (f i) := by
  obtain ⟨i, hi⟩ := proper_face_has_active_halfspace P f hbody F hF.1 hF.ne_toSet
  refine ⟨i, hF.eq_of_subset (hfacet i).1 (hfacet i).ne_toSet ?_⟩
  intro x hx
  exact ⟨face_subset_toSet P hF.1 hx, hi x hx⟩

end Papers.Polytopes

end
end
end BundlePart6

section BundlePart7
/- Source: Papers/ExtensionFacets.lean -/




@[expose] public section

/-!
# Every facet of a simplex-facet extension

Old nonvisible facets keep their dimension.  The cone forms are genuine
facets because their zero sets contain the apex and a full codimension-one
family of basis directions.  The exact halfspace representation proves
that these are all facets.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem old_facet_survives_extension
    (Q R : ConvexPolytope d) (hQ : Q.IsFullDim) (hR : R.IsFullDim)
    (hQR : Q.toSet ⊆ R.toSet)
    (F : Set (E d)) (hF : IsFacet Q F)
    (f : E d →ᵃ[ℝ] ℝ) (hf : SupportsFace Q F f)
    (hnonneg : ∀ x ∈ R.toSet, 0 ≤ f x) :
    IsFacet R (affineZeroFace R f) := by
  have hsub : F ⊆ affineZeroFace R f := by
    intro x hx
    exact ⟨hQR (face_subset_toSet Q hF.1 hx), hf.eq_zero hx⟩
  have hG : R.IsFace (affineZeroFace R f) :=
    affineZeroFace_isFace R f hnonneg (hF.1.2.mono hsub)
  have hproper : affineZeroFace R f ≠ R.toSet := by
    intro heq
    apply hF.support_ne_zero hf
    apply affine_eq_zero_of_body R hR f
    intro x hx
    exact (show x ∈ affineZeroFace R f from heq.symm ▸ hx).2
  have hlow : faceDim F ≤ faceDim (affineZeroFace R f) :=
    Submodule.finrank_mono (vectorSpan_mono ℝ hsub)
  have hhigh := faceDim_lt_of_ssubset R hG (toSet_isFace R)
    (Set.ssubset_iff_subset_ne.mpr ⟨face_subset_toSet R hG, hproper⟩)
  have hdF := hF.2
  change faceDim (affineZeroFace R f) < R.dim at hhigh
  refine ⟨hG, ?_⟩
  rw [hQ] at hdF
  rw [hR] at hhigh ⊢
  omega

theorem diagonal_zeroFace_direction
    (R : ConvexPolytope d) (a : E d) (p : ι → E d)
    (haR : a ∈ R.toSet) (hpR : ∀ i, p i ∈ R.toSet)
    (b : Basis ι ℝ (E d)) (hb : ∀ i, b i = p i - a)
    (g : ι → E d →ᵃ[ℝ] ℝ) (ha : ∀ i, g i a = 0)
    (hdiag : ∀ i, g i (p i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → g i (p j) = 0) (i : ι) :
    vectorSpan ℝ (affineZeroFace R (g i)) = (b.coord i).ker := by
  have hzero {x : E d} (hx : g i x = 0) : b.coord i (x - a) = 0 := by
    rw [diagonal_form_coordinate a p g b hb ha hoff x i] at hx
    exact (mul_eq_zero.mp hx).resolve_right (hdiag i)
  apply le_antisymm
  · rw [vectorSpan_def]
    apply Submodule.span_le.mpr
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_vsub.mp hz
    have hx0 := hzero hx.2
    have hy0 := hzero hy.2
    change b.coord i (x - y) = 0
    rw [map_sub] at hx0 hy0 ⊢
    linarith
  · intro z hz
    change b.coord i z = 0 at hz
    rw [← b.sum_repr z]
    apply Submodule.sum_mem
    intro j _
    by_cases hji : j = i
    · subst j
      have hrepr : b.repr z i = 0 := hz
      rw [hrepr, zero_smul]
      exact Submodule.zero_mem _
    · apply Submodule.smul_mem
      rw [hb j]
      exact vsub_mem_vectorSpan ℝ
        (show p j ∈ affineZeroFace R (g i) from ⟨hpR j, hoff i j (Ne.symm hji)⟩)
        (show a ∈ affineZeroFace R (g i) from ⟨haR, ha i⟩)

theorem diagonal_zeroFace_isFacet
    (R : ConvexPolytope d) (hR : R.IsFullDim)
    (a : E d) (p : ι → E d)
    (haR : a ∈ R.toSet) (hpR : ∀ i, p i ∈ R.toSet)
    (b : Basis ι ℝ (E d)) (hb : ∀ i, b i = p i - a)
    (g : ι → E d →ᵃ[ℝ] ℝ) (ha : ∀ i, g i a = 0)
    (hdiag : ∀ i, g i (p i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → g i (p j) = 0)
    (hnonneg : ∀ i x, x ∈ R.toSet → 0 ≤ g i x) (i : ι) :
    IsFacet R (affineZeroFace R (g i)) := by
  have hG := affineZeroFace_isFace R (g i) (hnonneg i) ⟨a, haR, ha i⟩
  have hsur : Function.Surjective (b.coord i) := by
    intro t
    refine ⟨t • b i, ?_⟩
    simp only [map_smul, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply,
      if_pos rfl, if_true, smul_eq_mul, mul_one]
  have hrange : (b.coord i).range = ⊤ := LinearMap.range_eq_top.mpr hsur
  have hdim := (b.coord i).finrank_range_add_finrank_ker
  rw [hrange, finrank_top, finrank_self, finrank_euclideanSpace_fin] at hdim
  refine ⟨hG, ?_⟩
  change finrank ℝ (vectorSpan ℝ (affineZeroFace R (g i))) + 1 = R.dim
  rw [diagonal_zeroFace_direction R a p haR hpR b hb g ha hdiag hoff i, hR]
  omega

theorem extensionFacetForms_are_facets
    (Q R : ConvexPolytope d) (hQ : Q.IsFullDim)
    (a : E d) (hvertices : R.vertices = insert a Q.vertices)
    (T : Set (E d)) (f₀ : E d →ᵃ[ℝ] ℝ)
    (hf₀ : ∀ x ∈ Q.toSet, 0 ≤ f₀ x)
    (f : ι → E d →ᵃ[ℝ] ℝ)
    (hf : ∀ i x, x ∈ Q.toSet → 0 ≤ f i x)
    (p : ι → E d) (hp : ∀ i, p i ∈ Q.vertices)
    (hp₀ : ∀ i, f₀ (p i) = 0)
    (hdiag : ∀ i, 0 < f i (p i))
    (hoff : ∀ i j, i ≠ j → f i (p j) = 0)
    (hcard : Fintype.card ι = d)
    (ha₀ : f₀ a < 0) (ha : ∀ i, 0 ≤ f i a)
    (hother : ∀ F : FacetType Q, F.val.val ≠ T → 0 ≤ chosenFacetForm Q F a) :
    ∀ i : ExtensionFacetIndex Q T ι,
      IsFacet R (affineZeroFace R (extensionFacetForm Q T f₀ f a i)) := by
  have hR := extension_fullDim Q R hQ a hvertices
  have hQR := old_body_subset_extension Q R a hvertices
  have hnonneg := extensionFacetForms_nonneg Q R a hvertices T f₀ f hf₀ hf ha₀ ha hother
  have haR : a ∈ R.toSet := subset_convexHull ℝ _ (by rw [hvertices]; exact Finset.mem_insert_self _ _)
  have hpR : ∀ i, p i ∈ R.toSet :=
    fun i => hQR (subset_convexHull ℝ _ (hp i))
  intro i
  cases i with
  | inl F =>
    exact old_facet_survives_extension Q R hQ hR hQR F.val.val.val F.val.property
      (chosenFacetForm Q F.val) (chosenFacetForm_supports Q F.val) (hnonneg (Sum.inl F))
  | inr i =>
    let g := restorationConeForm f₀ f a
    have hga : ∀ j, g j a = 0 := restorationConeForm_at_apex f₀ f a (ne_of_lt ha₀)
    have hgdiag : ∀ j, g j (p j) ≠ 0 := by
      intro j
      rw [show g j (p j) = f j (p j) from
        restorationConeForm_on_hyperplane f₀ f a (p j) (hp₀ j) j]
      exact ne_of_gt (hdiag j)
    have hgoff : ∀ j k, j ≠ k → g j (p k) = 0 := by
      intro j k hjk
      rw [show g j (p k) = f j (p k) from
        restorationConeForm_on_hyperplane f₀ f a (p k) (hp₀ k) j]
      exact hoff j k hjk
    let b := diagonalEdgeBasis hcard a p g hga hgdiag hgoff
    have hb : ∀ j, b j = p j - a := diagonalEdgeBasis_apply hcard a p g hga hgdiag hgoff
    exact diagonal_zeroFace_isFacet R hR a p haR hpR b hb g hga hgdiag hgoff
      (fun j => hnonneg (Sum.inr j)) i

theorem extension_facets_complete
    (Q R : ConvexPolytope d) (hQ : Q.IsFullDim)
    (a : E d) (hvertices : R.vertices = insert a Q.vertices)
    (T : Set (E d)) (hT : IsFacet Q T)
    (f₀ : E d →ᵃ[ℝ] ℝ) (hf₀ : SupportsFace Q T f₀)
    (f : ι → E d →ᵃ[ℝ] ℝ)
    (hf : ∀ i x, x ∈ Q.toSet → 0 ≤ f i x)
    (p : ι → E d) (hp : ∀ i, p i ∈ Q.vertices)
    (hp₀ : ∀ i, f₀ (p i) = 0)
    (hdiag : ∀ i, 0 < f i (p i))
    (hoff : ∀ i j, i ≠ j → f i (p j) = 0)
    (hcard : Fintype.card ι = d)
    (ha₀ : f₀ a < 0) (ha : ∀ i, 0 ≤ f i a)
    (hother : ∀ F : FacetType Q, F.val.val ≠ T → 0 ≤ chosenFacetForm Q F a)
    (F : Set (E d)) (hF : IsFacet R F) :
    ∃ i : ExtensionFacetIndex Q T ι,
      F = affineZeroFace R (extensionFacetForm Q T f₀ f a i) := by
  apply facets_exhausted_by_halfspaces R (extensionFacetForm Q T f₀ f a)
    (extension_body_iff_halfspaces Q R hQ a hvertices T hT f₀ hf₀ f hf p hp hp₀
      hdiag hoff hcard ha₀ ha hother)
    (extensionFacetForms_are_facets Q R hQ a hvertices T f₀ hf₀.1 f hf p hp hp₀
      hdiag hoff hcard ha₀ ha hother) F hF

end Papers.Polytopes

end
end
end BundlePart7

section BundlePart8
/- Source: Papers/FacetVertexDictionary.lean -/




@[expose] public section

/-!
# Recovering all faces from facet--vertex incidences

Finite intersections of geometric faces are exposed by sums of supporting
affine forms.  The facet-intersection theorem then upgrades a bijection of
vertices preserving the two complete facet families to an ordinary face
order isomorphism.  No abstract incidence object replaces the convex body.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d e : ℕ}

def indexedFaceIntersection {ι : Type*} (P : ConvexPolytope d)
    (S : Finset ι) (F : ι → FaceType P) : Set (E d) :=
  {x ∈ P.toSet | ∀ i ∈ S, x ∈ (F i).val}

theorem indexedFaceIntersection_isFace {ι : Type*} (P : ConvexPolytope d)
    (S : Finset ι) (F : ι → FaceType P)
    (hne : (indexedFaceIntersection P S F).Nonempty) :
    P.IsFace (indexedFaceIntersection P S F) := by
  let f : ι → E d →ᵃ[ℝ] ℝ := fun i => Classical.choose
    (exists_supportsFace P (F i).property)
  have hf (i : ι) : SupportsFace P (F i).val (f i) :=
    Classical.choose_spec (exists_supportsFace P (F i).property)
  let g : E d →ᵃ[ℝ] ℝ := ∑ i ∈ S, f i
  have hg : ∀ x ∈ P.toSet, 0 ≤ g x := by
    intro x hx
    rw [show g x = ∑ i ∈ S, f i x from affineForm_sum_apply S f x]
    exact Finset.sum_nonneg (fun i _ => (hf i).1 x hx)
  have heq : indexedFaceIntersection P S F = affineZeroFace P g := by
    ext x
    change (x ∈ P.toSet ∧ ∀ i ∈ S, x ∈ (F i).val) ↔
      x ∈ P.toSet ∧ g x = 0
    constructor
    · rintro ⟨hx, hall⟩
      refine ⟨hx, ?_⟩
      rw [show g x = ∑ i ∈ S, f i x from affineForm_sum_apply S f x]
      exact Finset.sum_eq_zero (fun i hi => (hf i).eq_zero (hall i hi))
    · rintro ⟨hx, hz⟩
      rw [show g x = ∑ i ∈ S, f i x from affineForm_sum_apply S f x] at hz
      have hall := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i (_ : i ∈ S) => (hf i).1 x hx)).mp hz
      exact ⟨hx, fun i hi => ((hf i).mem_iff x).mpr ⟨hx, hall i hi⟩⟩
  rw [heq]
  exact affineZeroFace_isFace P g hg (heq ▸ hne)

theorem face_forward_of_facet_incidence
    (P : ConvexPolytope d) (hP : P.IsFullDim) (Q : ConvexPolytope e)
    (b : VertexType P ≃ VertexType Q)
    (hfacets : ∀ F : FaceType P, IsFacet P F.val →
      ∃ G : FaceType Q, IsFacet Q G.val ∧
        ∀ v : VertexType P, (b v).val ∈ G.val ↔ v.val ∈ F.val)
    (F : FaceType P) :
    ∃ G : FaceType Q, ∀ v : VertexType P,
      (b v).val ∈ G.val ↔ v.val ∈ F.val := by
  let S : Finset (FaceType P) := Finset.univ.filter
    (fun H => IsFacet P H.val ∧ F.val ⊆ H.val)
  let g : FaceType P → FaceType Q := fun H =>
    if hH : IsFacet P H.val then Classical.choose (hfacets H hH)
    else ⟨Q.toSet, toSet_isFace Q⟩
  have hg (H : FaceType P) (hH : IsFacet P H.val) (v : VertexType P) :
      (b v).val ∈ (g H).val ↔ v.val ∈ H.val := by
    dsimp only [g]
    rw [dif_pos hH]
    exact (Classical.choose_spec (hfacets H hH)).2 v
  have hS (H : FaceType P) : H ∈ S ↔ IsFacet P H.val ∧ F.val ⊆ H.val := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  have hne : (indexedFaceIntersection Q S g).Nonempty := by
    obtain ⟨x, hx⟩ := (facePolytope P F.property).vertices_nonempty
    obtain ⟨hxP, hxF⟩ := Finset.mem_filter.mp hx
    let v : VertexType P := ⟨x, hxP⟩
    refine ⟨(b v).val, subset_convexHull ℝ _ (b v).property, ?_⟩
    intro H hH
    obtain ⟨hfacet, hFH⟩ := (hS H).mp hH
    exact (hg H hfacet v).mpr (hFH hxF)
  refine ⟨⟨indexedFaceIntersection Q S g,
    indexedFaceIntersection_isFace Q S g hne⟩, ?_⟩
  intro v
  change ((b v).val ∈ Q.toSet ∧ ∀ H ∈ S, (b v).val ∈ (g H).val) ↔ v.val ∈ F.val
  constructor
  · rintro ⟨_, hall⟩
    rw [face_eq_inter_facets P hP F.val F.property]
    refine ⟨subset_convexHull ℝ _ v.property, ?_⟩
    intro H hH hFH
    let H' : FaceType P := ⟨H, hH.1⟩
    exact (hg H' hH v).mp (hall H' ((hS H').mpr ⟨hH, hFH⟩))
  · intro hv
    refine ⟨subset_convexHull ℝ _ (b v).property, ?_⟩
    intro H hH
    obtain ⟨hfacet, hFH⟩ := (hS H).mp hH
    exact (hg H hfacet v).mpr (hFH hv)

/-- Two-way coverage of actual facets, with all vertex incidences,
determines the full ordinary geometric face order. -/
def faceOrderIsoOfFacetIncidence
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (Q : ConvexPolytope e) (hQ : Q.IsFullDim)
    (b : VertexType P ≃ VertexType Q)
    (hforward : ∀ F : FaceType P, IsFacet P F.val →
      ∃ G : FaceType Q, IsFacet Q G.val ∧
        ∀ v : VertexType P, (b v).val ∈ G.val ↔ v.val ∈ F.val)
    (hbackward : ∀ G : FaceType Q, IsFacet Q G.val →
      ∃ F : FaceType P, IsFacet P F.val ∧
        ∀ v : VertexType P, (b v).val ∈ G.val ↔ v.val ∈ F.val) :
    FaceType P ≃o FaceType Q := by
  apply faceOrderIsoOfVertexIncidence P Q b
    (face_forward_of_facet_incidence P hP Q b hforward)
  intro G
  have hback : ∀ H : FaceType Q, IsFacet Q H.val →
      ∃ F : FaceType P, IsFacet P F.val ∧
        ∀ w : VertexType Q, (b.symm w).val ∈ F.val ↔ w.val ∈ H.val := by
    intro H hH
    obtain ⟨F, hF, hinc⟩ := hbackward H hH
    refine ⟨F, hF, ?_⟩
    intro w
    simpa only [b.apply_symm_apply] using (hinc (b.symm w)).symm
  obtain ⟨F, hF⟩ := face_forward_of_facet_incidence Q hQ P b.symm hback G
  refine ⟨F, ?_⟩
  intro v
  simpa only [b.symm_apply_apply] using (hF (b v)).symm

end Papers.Polytopes

end
end
end BundlePart8

section BundlePart9
/- Source: Papers/SimplexFacetPresentation.lean -/




@[expose] public section

/-!
# Geometric data at a simplex facet

This structure records actual vertices, actual facets and their supporting
forms.  Its later instances are derived from ordinary face isomorphisms.
The finite diagonal evaluation pattern supplies the affine-form basis;
strict positivity on all other facets is a theorem, not stored data.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open Papers.AffineCoordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι]

structure SimplexFacetPresentation (Q : ConvexPolytope d) (ι : Type*) [Fintype ι] where
  fullDim : Q.IsFullDim
  index_card : Fintype.card ι = d
  facet : Option ι → FacetType Q
  form : Option ι → E d →ᵃ[ℝ] ℝ
  supports : ∀ i, SupportsFace Q (facet i).val.val (form i)
  vertex : ι → VertexType Q
  at_base : ∀ i, form none (vertex i).val = 0
  diagonal : ∀ i, 0 < form (some i) (vertex i).val
  off_diagonal : ∀ i j, i ≠ j → form (some i) (vertex j).val = 0

namespace SimplexFacetPresentation

variable {Q : ConvexPolytope d} (D : SimplexFacetPresentation Q ι)

def base : Set (E d) := (D.facet none).val.val

theorem base_isFacet : IsFacet Q D.base := (D.facet none).property

theorem exists_outside_base : ∃ q : VertexType Q, D.form none q.val ≠ 0 := by
  by_contra h
  push_neg at h
  apply D.base_isFacet.support_ne_zero (D.supports none)
  apply affine_eq_zero_of_vertices Q D.fullDim (D.form none)
  intro x hx
  exact h ⟨x, hx⟩

def outsideVertex : VertexType Q := Classical.choose D.exists_outside_base

theorem outsideVertex_form_ne : D.form none D.outsideVertex.val ≠ 0 :=
  Classical.choose_spec D.exists_outside_base

def basis : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ) :=
  simplexSupportBasis D.index_card (D.form none) (fun i => D.form (some i))
    (fun i => (D.vertex i).val) D.outsideVertex.val D.at_base D.outsideVertex_form_ne
    (fun i => ne_of_gt (D.diagonal i)) D.off_diagonal

@[simp] theorem basis_apply (i : Option ι) : D.basis i = D.form i := by
  rw [basis, simplexSupportBasis_apply]
  cases i <;> rfl

theorem form_nonneg (i : Option ι) (x : E d) (hx : x ∈ Q.toSet) :
    0 ≤ D.form i x := (D.supports i).1 x hx

theorem facet_injective : Function.Injective D.facet := by
  intro i j heq
  by_contra hij
  cases i with
  | none =>
    cases j with
    | none => exact hij rfl
    | some j =>
      have hp : (D.vertex j).val ∈ (D.facet none).val.val :=
        ((D.supports none).mem_iff _).mpr
          ⟨subset_convexHull ℝ _ (D.vertex j).property, D.at_base j⟩
      rw [heq] at hp
      have hz := (D.supports (some j)).eq_zero hp
      exact (ne_of_gt (D.diagonal j)) hz
  | some i =>
    cases j with
    | none =>
      have hp : (D.vertex i).val ∈ (D.facet none).val.val :=
        ((D.supports none).mem_iff _).mpr
          ⟨subset_convexHull ℝ _ (D.vertex i).property, D.at_base i⟩
      rw [← heq] at hp
      exact (ne_of_gt (D.diagonal i)) ((D.supports (some i)).eq_zero hp)
    | some j =>
      have hne : j ≠ i := fun h => hij (congrArg Option.some h.symm)
      have hp : (D.vertex i).val ∈ (D.facet (some j)).val.val :=
        ((D.supports (some j)).mem_iff _).mpr
          ⟨subset_convexHull ℝ _ (D.vertex i).property, D.off_diagonal j i hne⟩
      rw [← heq] at hp
      exact (ne_of_gt (D.diagonal i)) ((D.supports (some i)).eq_zero hp)

theorem facet_set_injective : Function.Injective (fun i => (D.facet i).val.val) := by
  intro i j heq
  apply D.facet_injective
  apply Subtype.ext
  exact Subtype.ext heq

def AdmissiblePoint (a : E d) : Prop :=
  D.form none a < 0 ∧ ∀ i, 0 ≤ D.form (some i) a

theorem other_facet_positive
    (a : E d) (ha : D.AdmissiblePoint a)
    (G : FacetType Q) (hne : ∀ i, G ≠ D.facet i) :
    0 < chosenFacetForm Q G a := by
  let g := chosenFacetForm Q G
  have hne' : ∀ i, G.val.val ≠ (D.facet i).val.val := by
    intro i hi
    exact hne i (Subtype.ext (Subtype.ext hi))
  have hneg := simplexFacet_other_coefficient_neg Q
    (fun i => (D.facet i).val.val) D.basis (fun i => (D.vertex i).val)
    (fun i => (D.facet i).property)
    (fun i => by simpa only [D.basis_apply] using D.supports i)
    (fun i => subset_convexHull ℝ _ (D.vertex i).property)
    (by simpa only [D.basis_apply] using D.at_base)
    (by simpa only [D.basis_apply] using D.diagonal)
    (by simpa only [D.basis_apply] using D.off_diagonal)
    G.val.val g G.property (chosenFacetForm_supports Q G) hne'
  have hcoeff := basis_repr_some_nonneg D.basis (fun i => (D.vertex i).val)
    (by simpa only [D.basis_apply] using D.at_base)
    (by simpa only [D.basis_apply] using D.diagonal)
    (by simpa only [D.basis_apply] using D.off_diagonal)
    g (fun i => (chosenFacetForm_supports Q G).1 _
      (subset_convexHull ℝ _ (D.vertex i).property))
  have heq := homogeneousEvaluation_expansion D.basis (a, (1 : ℝ)) g
  simp only [homogeneousEvaluation_homogenize, Fintype.sum_option, D.basis_apply] at heq
  rw [heq]
  exact add_pos_of_pos_of_nonneg (mul_pos_of_neg_of_neg hneg ha.1)
    (Finset.sum_nonneg (fun i _ => mul_nonneg (hcoeff i) (ha.2 i)))

theorem nonbase_facet_nonneg
    (a : E d) (ha : D.AdmissiblePoint a)
    (G : FacetType Q) (hne : G.val.val ≠ D.base) :
    0 ≤ chosenFacetForm Q G a := by
  by_cases hG : ∃ i, G = D.facet (some i)
  · obtain ⟨i, rfl⟩ := hG
    obtain ⟨c, hc, hform⟩ := supportsFacet_positive_proportional Q D.fullDim
      (D.facet (some i)).val.val (D.facet (some i)).property
      (chosenFacetForm Q (D.facet (some i))) (D.form (some i))
      (chosenFacetForm_supports Q (D.facet (some i))) (D.supports (some i))
    rw [hform]
    exact mul_nonneg hc.le (ha.2 i)
  · apply (D.other_facet_positive a ha G ?_).le
    intro i hi
    cases i with
    | none => exact hne (congrArg (fun F : FacetType Q => F.val.val) hi)
    | some j => exact hG ⟨j, hi⟩

end SimplexFacetPresentation
end Papers.Polytopes

end
end
end BundlePart9

section BundlePart10
/- Source: Papers/SimplexFacetTransport.lean -/



@[expose] public section

/-!
# Transport of simplex-facet data through the ordinary face order

Facet dimensions and vertex incidences are recovered from the order
isomorphism.  Supporting forms are selected afresh in the target
realization.  Their numerical coefficients need not agree; only the
proved geometric incidence pattern is used.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d e : ℕ} {ι : Type*} [Fintype ι]

theorem imageFace_isFacet_iff {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) (F : FaceType P) :
    IsFacet Q (φ F).val ↔ IsFacet P F.val := by
  change (Q.IsFace (φ F).val ∧ faceDim (φ F).val + 1 = Q.dim) ↔
    P.IsFace F.val ∧ faceDim F.val + 1 = P.dim
  rw [faceOrderIso_dimension φ F, faceOrderIso_polytope_dim φ]
  simp only [(φ F).property, F.property, true_and]

def facetEquivOfFaceOrder {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) : FacetType P ≃ FacetType Q where
  toFun F := ⟨φ F.val, (imageFace_isFacet_iff φ F.val).mpr F.property⟩
  invFun G := ⟨φ.symm G.val, (imageFace_isFacet_iff φ.symm G.val).mpr G.property⟩
  left_inv F := by
    apply Subtype.ext
    exact φ.symm_apply_apply F.val
  right_inv G := by
    apply Subtype.ext
    exact φ.apply_symm_apply G.val

@[simp] theorem facetEquivOfFaceOrder_apply_val {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) (F : FacetType P) :
    (facetEquivOfFaceOrder φ F).val = φ F.val := rfl

namespace SimplexFacetPresentation

variable {P Q : ConvexPolytope d}

def transport (D : SimplexFacetPresentation P ι) (φ : FaceType P ≃o FaceType Q) :
    SimplexFacetPresentation Q ι where
  fullDim := (faceOrderIso_polytope_dim φ).trans D.fullDim
  index_card := D.index_card
  facet := fun i => facetEquivOfFaceOrder φ (D.facet i)
  form := fun i => chosenFacetForm Q (facetEquivOfFaceOrder φ (D.facet i))
  supports := fun i => chosenFacetForm_supports Q (facetEquivOfFaceOrder φ (D.facet i))
  vertex := fun i => imageVertex φ (D.vertex i)
  at_base := by
    intro i
    apply (chosenFacetForm_supports Q (facetEquivOfFaceOrder φ (D.facet none))).eq_zero
    apply (imageVertex_mem_iff φ (D.vertex i) (D.facet none).val).mpr
    exact ((D.supports none).mem_iff _).mpr
      ⟨subset_convexHull ℝ _ (D.vertex i).property, D.at_base i⟩
  diagonal := by
    intro i
    let w := imageVertex φ (D.vertex i)
    let F := facetEquivOfFaceOrder φ (D.facet (some i))
    have hw : w.val ∈ Q.toSet := subset_convexHull ℝ _ w.property
    apply lt_of_le_of_ne ((chosenFacetForm_supports Q F).1 w.val hw)
    intro hz
    have hwF := ((chosenFacetForm_supports Q F).mem_iff w.val).mpr ⟨hw, hz.symm⟩
    have hpF := (imageVertex_mem_iff φ (D.vertex i) (D.facet (some i)).val).mp hwF
    exact (ne_of_gt (D.diagonal i)) ((D.supports (some i)).eq_zero hpF)
  off_diagonal := by
    intro i j hij
    apply (chosenFacetForm_supports Q (facetEquivOfFaceOrder φ (D.facet (some i)))).eq_zero
    apply (imageVertex_mem_iff φ (D.vertex j) (D.facet (some i)).val).mpr
    exact ((D.supports (some i)).mem_iff _).mpr
      ⟨subset_convexHull ℝ _ (D.vertex j).property, D.off_diagonal i j hij⟩

/-- Replace the supporting forms by any other proved inward forms for the
same facets.  This permits forms with coefficients in a specified field. -/
def withForms (D : SimplexFacetPresentation P ι)
    (f : Option ι → E d →ᵃ[ℝ] ℝ)
    (hf : ∀ i, SupportsFace P (D.facet i).val.val (f i)) :
    SimplexFacetPresentation P ι where
  fullDim := D.fullDim
  index_card := D.index_card
  facet := D.facet
  form := f
  supports := hf
  vertex := D.vertex
  at_base := fun i => (hf none).eq_zero
    (((D.supports none).mem_iff _).mpr
      ⟨subset_convexHull ℝ _ (D.vertex i).property, D.at_base i⟩)
  diagonal := by
    intro i
    apply lt_of_le_of_ne ((hf (some i)).1 _ (subset_convexHull ℝ _ (D.vertex i).property))
    intro hz
    have hp := ((hf (some i)).mem_iff _).mpr
      ⟨subset_convexHull ℝ _ (D.vertex i).property, hz.symm⟩
    exact (ne_of_gt (D.diagonal i)) ((D.supports (some i)).eq_zero hp)
  off_diagonal := fun i j hij => (hf (some i)).eq_zero
    (((D.supports (some i)).mem_iff _).mpr
      ⟨subset_convexHull ℝ _ (D.vertex j).property, D.off_diagonal i j hij⟩)

def Aligned (D : SimplexFacetPresentation P ι) (D₂ : SimplexFacetPresentation Q ι)
    (φ : FaceType P ≃o FaceType Q) : Prop :=
  (∀ i, D₂.facet i = facetEquivOfFaceOrder φ (D.facet i)) ∧
    ∀ i, D₂.vertex i = imageVertex φ (D.vertex i)

theorem transport_aligned (D : SimplexFacetPresentation P ι)
    (φ : FaceType P ≃o FaceType Q) : D.Aligned (D.transport φ) φ :=
  ⟨fun _ => rfl, fun _ => rfl⟩

theorem chosen_form_zero_iff (D : SimplexFacetPresentation P ι)
    (i : Option ι) (a : E d) :
    chosenFacetForm P (D.facet i) a = 0 ↔ D.form i a = 0 := by
  obtain ⟨c, hc, heq⟩ := supportsFacet_positive_proportional P D.fullDim
    (D.facet i).val.val (D.facet i).property
    (chosenFacetForm P (D.facet i)) (D.form i)
    (chosenFacetForm_supports P (D.facet i)) (D.supports i)
  rw [heq]
  change c * D.form i a = 0 ↔ D.form i a = 0
  exact mul_eq_zero.trans (or_iff_right (ne_of_gt hc))

def SameCoplanar (D : SimplexFacetPresentation P ι) (a : E d)
    (D₂ : SimplexFacetPresentation Q ι) (a' : E d) : Prop :=
  ∀ i, D.form (some i) a = 0 ↔ D₂.form (some i) a' = 0

theorem nonbase_zero_preserved
    (D : SimplexFacetPresentation P ι) (D₂ : SimplexFacetPresentation Q ι)
    (φ : FaceType P ≃o FaceType Q) (hDE : D.Aligned D₂ φ)
    (a a' : E d) (ha : D.AdmissiblePoint a) (ha' : D₂.AdmissiblePoint a')
    (hsame : D.SameCoplanar a D₂ a')
    (F : FacetType P) (hF : F.val.val ≠ D.base) :
    chosenFacetForm P F a = 0 ↔
      chosenFacetForm Q (facetEquivOfFaceOrder φ F) a' = 0 := by
  by_cases hFi : ∃ i, F = D.facet (some i)
  · obtain ⟨i, rfl⟩ := hFi
    rw [← hDE.1 (some i), D.chosen_form_zero_iff, D₂.chosen_form_zero_iff]
    exact hsame i
  · have hne : ∀ i, F ≠ D.facet i := by
      intro i hi
      cases i with
      | none => exact hF (congrArg (fun G : FacetType P => G.val.val) hi)
      | some j => exact hFi ⟨j, hi⟩
    have hne' : ∀ i, facetEquivOfFaceOrder φ F ≠ D₂.facet i := by
      intro i hi
      rw [hDE.1 i] at hi
      exact hne i ((facetEquivOfFaceOrder φ).injective hi)
    have hpos := D.other_facet_positive a ha F hne
    have hpos' := D₂.other_facet_positive a' ha' (facetEquivOfFaceOrder φ F) hne'
    exact iff_of_false (ne_of_gt hpos) (ne_of_gt hpos')

end SimplexFacetPresentation
end Papers.Polytopes

end
end
end BundlePart10

section BundlePart11
/- Source: Papers/PresentedExtension.lean -/



@[expose] public section

/-!
# Complete facets and vertex retention for a presented extension

All assertions here concern an existing actual convex polytope with the
displayed old and new vertices.  The retention witness is extracted from
its ordinary facets.  This witness will be transported to construct a new
extension, avoiding a circular assumption that the construction has kept
the old vertices extreme.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι]

def extensionVertexLabels (Q R : ConvexPolytope d) (a : E d)
    (hvertices : R.vertices = insert a Q.vertices) (ha : a ∉ Q.vertices) :
    Option (VertexType Q) ≃ VertexType R := by
  let f : Option (VertexType Q) → VertexType R := fun u =>
    u.elim ⟨a, by rw [hvertices]; exact Finset.mem_insert_self _ _⟩
      (fun v => ⟨v.val, by rw [hvertices]; exact Finset.mem_insert_of_mem v.property⟩)
  apply Equiv.ofBijective f
  constructor
  · intro u v heq
    have hval := congrArg Subtype.val heq
    cases u with
    | none =>
      cases v with
      | none => rfl
      | some v =>
        have hv : a = v.val := hval
        exact False.elim (ha (hv.symm ▸ v.property))
    | some u =>
      cases v with
      | none =>
        have hu : u.val = a := hval
        exact False.elim (ha (hu ▸ u.property))
      | some v => exact congrArg Option.some (Subtype.ext hval)
  · intro v
    have hv : v.val ∈ insert a Q.vertices :=
      (congrArg (fun s : Finset (E d) => v.val ∈ s) hvertices).mp v.property
    rcases Finset.mem_insert.mp hv with hv | hv
    · refine ⟨none, ?_⟩
      exact Subtype.ext hv.symm
    · refine ⟨some ⟨v.val, hv⟩, ?_⟩
      rfl

@[simp] theorem extensionVertexLabels_none (Q R : ConvexPolytope d) (a : E d)
    (hvertices : R.vertices = insert a Q.vertices) (ha : a ∉ Q.vertices) :
    (extensionVertexLabels Q R a hvertices ha none).val = a := rfl

@[simp] theorem extensionVertexLabels_some (Q R : ConvexPolytope d) (a : E d)
    (hvertices : R.vertices = insert a Q.vertices) (ha : a ∉ Q.vertices)
    (v : VertexType Q) :
    (extensionVertexLabels Q R a hvertices ha (some v)).val = v.val := rfl

namespace SimplexFacetPresentation

variable {Q : ConvexPolytope d} (D : SimplexFacetPresentation Q ι)

def extensionForm (a : E d) : ExtensionFacetIndex Q D.base ι → E d →ᵃ[ℝ] ℝ :=
  extensionFacetForm Q D.base (D.form none) (fun i => D.form (some i)) a

theorem apex_not_mem_vertices (a : E d) (ha : D.AdmissiblePoint a) : a ∉ Q.vertices :=
  exterior_point_not_mem_vertices Q a (D.form none) (D.supports none).1 ha.1

theorem extension_form_nonneg (R : ConvexPolytope d) (a : E d)
    (hvertices : R.vertices = insert a Q.vertices) (ha : D.AdmissiblePoint a) :
    ∀ i, ∀ x ∈ R.toSet, 0 ≤ D.extensionForm a i x :=
  extensionFacetForms_nonneg Q R a hvertices D.base (D.form none)
    (fun i => D.form (some i)) (D.supports none).1
    (fun i => (D.supports (some i)).1) ha.1 ha.2 (D.nonbase_facet_nonneg a ha)

theorem extension_form_isFacet (R : ConvexPolytope d) (a : E d)
    (hvertices : R.vertices = insert a Q.vertices) (ha : D.AdmissiblePoint a) :
    ∀ i, IsFacet R (affineZeroFace R (D.extensionForm a i)) :=
  extensionFacetForms_are_facets Q R D.fullDim a hvertices D.base (D.form none)
    (D.supports none).1 (fun i => D.form (some i))
    (fun i => (D.supports (some i)).1) (fun i => (D.vertex i).val)
    (fun i => (D.vertex i).property) D.at_base D.diagonal D.off_diagonal
    D.index_card ha.1 ha.2 (D.nonbase_facet_nonneg a ha)

theorem extension_facets (R : ConvexPolytope d) (a : E d)
    (hvertices : R.vertices = insert a Q.vertices) (ha : D.AdmissiblePoint a)
    (F : Set (E d)) (hF : IsFacet R F) :
    ∃ i, F = affineZeroFace R (D.extensionForm a i) :=
  extension_facets_complete Q R D.fullDim a hvertices D.base D.base_isFacet
    (D.form none) (D.supports none) (fun i => D.form (some i))
    (fun i => (D.supports (some i)).1) (fun i => (D.vertex i).val)
    (fun i => (D.vertex i).property) D.at_base D.diagonal D.off_diagonal
    D.index_card ha.1 ha.2 (D.nonbase_facet_nonneg a ha) F hF

theorem cone_form_zero_iff (a : E d) (ha : D.AdmissiblePoint a)
    (i : ι) (x : E d) (hx : x ∈ Q.toSet) :
    D.extensionForm a (Sum.inr i) x = 0 ↔
      D.form (some i) x = 0 ∧ (D.form (some i) a = 0 ∨ D.form none x = 0) := by
  change D.form (some i) x -
    (D.form (some i) a / D.form none a) * D.form none x = 0 ↔ _
  by_cases hai : D.form (some i) a = 0
  · simp only [hai, zero_div, zero_mul, sub_zero, true_or, and_true]
  · have hp : 0 < D.form (some i) a := lt_of_le_of_ne (ha.2 i) (Ne.symm hai)
    have hc : D.form (some i) a / D.form none a < 0 := div_neg_of_pos_of_neg hp ha.1
    have hix := D.form_nonneg (some i) x hx
    have h₀x := D.form_nonneg none x hx
    simp only [hai, false_or]
    constructor
    · intro hzero
      constructor <;> nlinarith
    · rintro ⟨hi, h₀⟩
      rw [hi, h₀, mul_zero, sub_zero]

/-- Every old actual vertex lies on an old nonbase facet that is strictly
inside at the apex.  This is proved from the existing extension, not
assumed in the construction of another realization. -/
theorem retention_facet (R : ConvexPolytope d) (a : E d)
    (hvertices : R.vertices = insert a Q.vertices) (ha : D.AdmissiblePoint a)
    (v : VertexType Q) :
    ∃ F : FacetType Q, F.val.val ≠ D.base ∧ v.val ∈ F.val.val ∧
      0 < chosenFacetForm Q F a := by
  have hR := extension_fullDim Q R D.fullDim a hvertices
  have hvR : v.val ∈ R.vertices := by rw [hvertices]; exact Finset.mem_insert_of_mem v.property
  have haR : a ∈ R.toSet := subset_convexHull ℝ _ (by rw [hvertices]; exact Finset.mem_insert_self _ _)
  have hav : a ≠ v.val := fun h => D.apex_not_mem_vertices a ha (h.symm ▸ v.property)
  obtain ⟨H, hH, hvH, haH⟩ := exists_facet_containing_not_mem R hR
    ({v.val} : Set (E d)) (vertex_isFace R hvR) a haR hav
  obtain ⟨i, hi⟩ := D.extension_facets R a hvertices ha H hH
  cases i with
  | inl F =>
    have hzv : chosenFacetForm Q F.val v.val = 0 := by
      have hmem := hvH (Set.mem_singleton _)
      rw [hi] at hmem
      exact hmem.2
    have hza : chosenFacetForm Q F.val a ≠ 0 := by
      intro hz
      apply haH
      rw [hi]
      exact ⟨haR, hz⟩
    exact ⟨F.val, F.property,
      ((chosenFacetForm_supports Q F.val).mem_iff _).mpr
        ⟨subset_convexHull ℝ _ v.property, hzv⟩,
      lt_of_le_of_ne (D.nonbase_facet_nonneg a ha F.val F.property) (Ne.symm hza)⟩
  | inr i =>
    apply False.elim
    apply haH
    rw [hi]
    exact ⟨haR, restorationConeForm_at_apex (D.form none)
      (fun i => D.form (some i)) a (ne_of_lt ha.1) i⟩

end SimplexFacetPresentation
end Papers.Polytopes

end
end
end BundlePart11

section BundlePart12
/- Source: Papers/EquivalentExtensions.lean -/





@[expose] public section

/-!
# The face lattice of an extension depends on the prescribed coplanar facets

The ordinary face isomorphism of the old polytopes transports the full
facet list.  The new point is specified by the base facet and the zero
pattern on its neighboring facets.  The proof includes retention of every
old vertex and constructs the ordinary face order of the enlarged hulls.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι]

def extensionLabelPoint {Q : ConvexPolytope d} (a : E d) : Option (VertexType Q) → E d :=
  fun u => u.elim a Subtype.val

namespace SimplexFacetPresentation

variable {Q Q' : ConvexPolytope d}

theorem aligned_base_eq_iff
    (D : SimplexFacetPresentation Q ι) (D₂ : SimplexFacetPresentation Q' ι)
    (φ : FaceType Q ≃o FaceType Q') (hDE : D.Aligned D₂ φ) (F : FacetType Q) :
    F.val.val = D.base ↔ (facetEquivOfFaceOrder φ F).val.val = D₂.base := by
  constructor
  · intro h
    have hF : F = D.facet none := Subtype.ext (Subtype.ext h)
    rw [hF, ← hDE.1 none]
    rfl
  · intro h
    have hF : facetEquivOfFaceOrder φ F = D₂.facet none := Subtype.ext (Subtype.ext h)
    rw [hDE.1 none] at hF
    exact congrArg (fun F : FacetType Q => F.val.val)
      ((facetEquivOfFaceOrder φ).injective hF)

def nonbaseFacetEquiv
    (D : SimplexFacetPresentation Q ι) (D₂ : SimplexFacetPresentation Q' ι)
    (φ : FaceType Q ≃o FaceType Q') (hDE : D.Aligned D₂ φ) :
    {F : FacetType Q // F.val.val ≠ D.base} ≃
      {F : FacetType Q' // F.val.val ≠ D₂.base} :=
  (facetEquivOfFaceOrder φ).subtypeEquiv
    (fun F => not_congr (D.aligned_base_eq_iff D₂ φ hDE F))

def extensionIndexEquiv
    (D : SimplexFacetPresentation Q ι) (D₂ : SimplexFacetPresentation Q' ι)
    (φ : FaceType Q ≃o FaceType Q') (hDE : D.Aligned D₂ φ) :
    ExtensionFacetIndex Q D.base ι ≃ ExtensionFacetIndex Q' D₂.base ι :=
  Equiv.sumCongr (D.nonbaseFacetEquiv D₂ φ hDE) (Equiv.refl ι)

theorem form_zero_at_old_vertex_preserved
    (D : SimplexFacetPresentation Q ι) (D₂ : SimplexFacetPresentation Q' ι)
    (φ : FaceType Q ≃o FaceType Q') (hDE : D.Aligned D₂ φ)
    (i : Option ι) (v : VertexType Q) :
    D.form i v.val = 0 ↔ D₂.form i (imageVertex φ v).val = 0 := by
  have hvQ : v.val ∈ Q.toSet := subset_convexHull ℝ _ v.property
  have hvQ' : (imageVertex φ v).val ∈ Q'.toSet :=
    subset_convexHull ℝ _ (imageVertex φ v).property
  have hleft := (D.supports i).mem_iff v.val
  have hright := (D₂.supports i).mem_iff (imageVertex φ v).val
  rw [and_iff_right hvQ] at hleft
  rw [and_iff_right hvQ'] at hright
  rw [← hleft, ← hright, hDE.1 i]
  exact (imageVertex_mem_iff φ v (D.facet i).val).symm

theorem extension_zero_incidence_preserved
    (D : SimplexFacetPresentation Q ι) (D₂ : SimplexFacetPresentation Q' ι)
    (φ : FaceType Q ≃o FaceType Q') (hDE : D.Aligned D₂ φ)
    (a a' : E d) (ha : D.AdmissiblePoint a) (ha' : D₂.AdmissiblePoint a')
    (hsame : D.SameCoplanar a D₂ a')
    (i : ExtensionFacetIndex Q D.base ι) (u : Option (VertexType Q)) :
    D.extensionForm a i (extensionLabelPoint a u) = 0 ↔
      D₂.extensionForm a' (D.extensionIndexEquiv D₂ φ hDE i)
        (extensionLabelPoint a' (Equiv.optionCongr (vertexEquivOfFaceOrder φ) u)) = 0 := by
  cases i with
  | inl F =>
    cases u with
    | none =>
      exact D.nonbase_zero_preserved D₂ φ hDE a a' ha ha' hsame F.val F.property
    | some v =>
      change chosenFacetForm Q F.val v.val = 0 ↔
        chosenFacetForm Q' (facetEquivOfFaceOrder φ F.val) (imageVertex φ v).val = 0
      have hleft := (chosenFacetForm_supports Q F.val).mem_iff v.val
      have hright := (chosenFacetForm_supports Q' (facetEquivOfFaceOrder φ F.val)).mem_iff
        (imageVertex φ v).val
      have hvQ : v.val ∈ Q.toSet := subset_convexHull ℝ _ v.property
      have hvQ' : (imageVertex φ v).val ∈ Q'.toSet :=
        subset_convexHull ℝ _ (imageVertex φ v).property
      rw [and_iff_right hvQ] at hleft
      rw [and_iff_right hvQ'] at hright
      rw [← hleft, ← hright]
      exact (imageVertex_mem_iff φ v F.val.val).symm
  | inr i =>
    cases u with
    | none =>
      have h := restorationConeForm_at_apex (D.form none) (fun i => D.form (some i))
        a (ne_of_lt ha.1) i
      have h' := restorationConeForm_at_apex (D₂.form none) (fun i => D₂.form (some i))
        a' (ne_of_lt ha'.1) i
      exact iff_of_true h h'
    | some v =>
      change D.extensionForm a (Sum.inr i) v.val = 0 ↔
        D₂.extensionForm a' (Sum.inr i) (imageVertex φ v).val = 0
      rw [D.cone_form_zero_iff a ha i v.val (subset_convexHull ℝ _ v.property),
        D₂.cone_form_zero_iff a' ha' i (imageVertex φ v).val
          (subset_convexHull ℝ _ (imageVertex φ v).property),
        D.form_zero_at_old_vertex_preserved D₂ φ hDE (some i) v,
        D.form_zero_at_old_vertex_preserved D₂ φ hDE none v,
        hsame i]

theorem transferred_retention
    (D : SimplexFacetPresentation Q ι) (D₂ : SimplexFacetPresentation Q' ι)
    (φ : FaceType Q ≃o FaceType Q') (hDE : D.Aligned D₂ φ)
    (R : ConvexPolytope d) (a a' : E d)
    (hvertices : R.vertices = insert a Q.vertices)
    (ha : D.AdmissiblePoint a) (ha' : D₂.AdmissiblePoint a')
    (hsame : D.SameCoplanar a D₂ a') :
    ∀ v' : VertexType Q', ∃ g : E d →ᵃ[ℝ] ℝ,
      (∀ x ∈ Q'.toSet, 0 ≤ g x) ∧ g v'.val = 0 ∧ 0 < g a' := by
  intro v'
  obtain ⟨v, rfl⟩ := (vertexEquivOfFaceOrder φ).surjective v'
  obtain ⟨F, hFT, hvF, hFa⟩ := D.retention_facet R a hvertices ha v
  let F' := facetEquivOfFaceOrder φ F
  have hF'T : F'.val.val ≠ D₂.base :=
    (not_congr (D.aligned_base_eq_iff D₂ φ hDE F)).mp hFT
  have hvF' : (imageVertex φ v).val ∈ F'.val.val :=
    (imageVertex_mem_iff φ v F.val).mpr hvF
  have hFa' : chosenFacetForm Q' F' a' ≠ 0 := by
    intro hz
    exact (ne_of_gt hFa) ((D.nonbase_zero_preserved D₂ φ hDE a a' ha ha' hsame F hFT).mpr hz)
  exact ⟨chosenFacetForm Q' F', (chosenFacetForm_supports Q' F').1,
    (chosenFacetForm_supports Q' F').eq_zero hvF',
    lt_of_le_of_ne (D₂.nonbase_facet_nonneg a' ha' F' hF'T) (Ne.symm hFa')⟩

def extensionVertexEquiv
    (D : SimplexFacetPresentation Q ι) (D₂ : SimplexFacetPresentation Q' ι)
    (φ : FaceType Q ≃o FaceType Q')
    (R R' : ConvexPolytope d) (a a' : E d)
    (hvertices : R.vertices = insert a Q.vertices)
    (hvertices' : R'.vertices = insert a' Q'.vertices)
    (ha : D.AdmissiblePoint a) (ha' : D₂.AdmissiblePoint a') :
    VertexType R ≃ VertexType R' :=
  (extensionVertexLabels Q R a hvertices (D.apex_not_mem_vertices a ha)).symm.trans
    ((Equiv.optionCongr (vertexEquivOfFaceOrder φ)).trans
      (extensionVertexLabels Q' R' a' hvertices' (D₂.apex_not_mem_vertices a' ha')))

def extensionFaceOrderIso
    (D : SimplexFacetPresentation Q ι) (D₂ : SimplexFacetPresentation Q' ι)
    (φ : FaceType Q ≃o FaceType Q') (hDE : D.Aligned D₂ φ)
    (R R' : ConvexPolytope d) (a a' : E d)
    (hvertices : R.vertices = insert a Q.vertices)
    (hvertices' : R'.vertices = insert a' Q'.vertices)
    (ha : D.AdmissiblePoint a) (ha' : D₂.AdmissiblePoint a')
    (hsame : D.SameCoplanar a D₂ a') : FaceType R ≃o FaceType R' := by
  let b := D.extensionVertexEquiv D₂ φ R R' a a' hvertices hvertices' ha ha'
  let e := D.extensionIndexEquiv D₂ φ hDE
  have hinc (i : ExtensionFacetIndex Q D.base ι) (v : VertexType R) :
      (b v).val ∈ affineZeroFace R' (D₂.extensionForm a' (e i)) ↔
        v.val ∈ affineZeroFace R (D.extensionForm a i) := by
    have hvR : v.val ∈ R.toSet := subset_convexHull ℝ _ v.property
    have hbvR' : (b v).val ∈ R'.toSet := subset_convexHull ℝ _ (b v).property
    obtain ⟨u, rfl⟩ :=
      (extensionVertexLabels Q R a hvertices (D.apex_not_mem_vertices a ha)).surjective v
    change ((b _).val ∈ R'.toSet ∧ D₂.extensionForm a' (e i) (b _).val = 0) ↔
      (_ ∈ R.toSet ∧ D.extensionForm a i _ = 0)
    rw [and_iff_right hbvR', and_iff_right hvR]
    have hlabel : (b (extensionVertexLabels Q R a hvertices
        (D.apex_not_mem_vertices a ha) u)).val =
        extensionLabelPoint a' (Equiv.optionCongr (vertexEquivOfFaceOrder φ) u) := by
      dsimp only [b, extensionVertexEquiv, Equiv.trans_apply]
      rw [Equiv.symm_apply_apply]
      cases (Equiv.optionCongr (vertexEquivOfFaceOrder φ) u) <;> rfl
    have hlabel' : (extensionVertexLabels Q R a hvertices
        (D.apex_not_mem_vertices a ha) u).val = extensionLabelPoint a u := by
      cases u <;> rfl
    rw [hlabel, hlabel']
    exact (D.extension_zero_incidence_preserved D₂ φ hDE a a' ha ha' hsame i u).symm
  apply faceOrderIsoOfFacetIncidence R (extension_fullDim Q R D.fullDim a hvertices)
    R' (extension_fullDim Q' R' D₂.fullDim a' hvertices') b
  · intro F hF
    obtain ⟨i, hi⟩ := D.extension_facets R a hvertices ha F.val hF
    refine ⟨⟨_, (D₂.extension_form_isFacet R' a' hvertices' ha' (e i)).1⟩,
      D₂.extension_form_isFacet R' a' hvertices' ha' (e i), ?_⟩
    intro v
    rw [hi]
    exact hinc i v
  · intro G hG
    obtain ⟨j, hj⟩ := D₂.extension_facets R' a' hvertices' ha' G.val hG
    obtain ⟨i, rfl⟩ := e.surjective j
    refine ⟨⟨_, (D.extension_form_isFacet R a hvertices ha i).1⟩,
      D.extension_form_isFacet R a hvertices ha i, ?_⟩
    intro v
    rw [hj]
    exact hinc i v

/-- Whenever a same-type core admits a point with the prescribed signs,
the resulting convex hull is an actual realization of the original
extension.  Existence of that point over each field is a separate,
constructive homogeneous-coordinate theorem. -/
theorem realize_extension_from_admissible_point
    (D : SimplexFacetPresentation Q ι) (D₂ : SimplexFacetPresentation Q' ι)
    (φ : FaceType Q ≃o FaceType Q') (hDE : D.Aligned D₂ φ)
    (R : ConvexPolytope d) (a a' : E d)
    (hvertices : R.vertices = insert a Q.vertices)
    (ha : D.AdmissiblePoint a) (ha' : D₂.AdmissiblePoint a')
    (hsame : D.SameCoplanar a D₂ a') :
    ∃ R' : ConvexPolytope d, R'.vertices = insert a' Q'.vertices ∧
      Nonempty (FaceType R ≃o FaceType R') := by
  let hr := D.transferred_retention D₂ φ hDE R a a' hvertices ha ha' hsame
  let R' := addExteriorVertex Q' a' (D₂.form none) (D₂.supports none).1 ha'.1 hr
  have hv : R'.vertices = insert a' Q'.vertices := rfl
  exact ⟨R', hv, ⟨D.extensionFaceOrderIso D₂ φ hDE R R' a a' hvertices hv ha ha' hsame⟩⟩

end SimplexFacetPresentation
end Papers.Polytopes

end
end
end BundlePart12

section BundlePart13
/- Source: Papers/ExtensionVertexLabels.lean -/



@[expose] public section

/-!
# The actual vertex labels in the extension face isomorphism

The face-order construction induces exactly the prescribed bijection on
vertices.  The new vertex and the old vertices therefore have their
intended coordinate correspondences in approximation statements.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d e : ℕ} {ι : Type*} [Fintype ι]

theorem faceOrderIsoOfVertexIncidence_vertex
    (P : ConvexPolytope d) (Q : ConvexPolytope e)
    (b : VertexType P ≃ VertexType Q)
    (hforward : ∀ F : FaceType P, ∃ G : FaceType Q,
      ∀ v : VertexType P, (b v).val ∈ G.val ↔ v.val ∈ F.val)
    (hbackward : ∀ G : FaceType Q, ∃ F : FaceType P,
      ∀ v : VertexType P, (b v).val ∈ G.val ↔ v.val ∈ F.val)
    (v : VertexType P) :
    imageVertex (faceOrderIsoOfVertexIncidence P Q b hforward hbackward) v = b v := by
  let φ := faceOrderIsoOfVertexIncidence P Q b hforward hbackward
  have hm : (b v).val ∈ (φ (vertexFace P v)).val :=
    (Classical.choose_spec (hforward (vertexFace P v)) v).mpr (Set.mem_singleton _)
  rw [← imageVertex_face φ v] at hm
  exact Subtype.ext (show (imageVertex φ v).val = (b v).val from hm.symm)

theorem faceOrderIsoOfFacetIncidence_vertex
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (Q : ConvexPolytope e) (hQ : Q.IsFullDim)
    (b : VertexType P ≃ VertexType Q)
    (hforward : ∀ F : FaceType P, IsFacet P F.val →
      ∃ G : FaceType Q, IsFacet Q G.val ∧
        ∀ v : VertexType P, (b v).val ∈ G.val ↔ v.val ∈ F.val)
    (hbackward : ∀ G : FaceType Q, IsFacet Q G.val →
      ∃ F : FaceType P, IsFacet P F.val ∧
        ∀ v : VertexType P, (b v).val ∈ G.val ↔ v.val ∈ F.val)
    (v : VertexType P) :
    imageVertex (faceOrderIsoOfFacetIncidence P hP Q hQ b hforward hbackward) v = b v := by
  unfold faceOrderIsoOfFacetIncidence
  exact faceOrderIsoOfVertexIncidence_vertex P Q b _ _ v

namespace SimplexFacetPresentation

variable {Q Q' : ConvexPolytope d}

theorem extensionFaceOrderIso_vertex
    (D : SimplexFacetPresentation Q ι) (D₂ : SimplexFacetPresentation Q' ι)
    (φ : FaceType Q ≃o FaceType Q') (hDE : D.Aligned D₂ φ)
    (R R' : ConvexPolytope d) (a a' : E d)
    (hvertices : R.vertices = insert a Q.vertices)
    (hvertices' : R'.vertices = insert a' Q'.vertices)
    (ha : D.AdmissiblePoint a) (ha' : D₂.AdmissiblePoint a')
    (hsame : D.SameCoplanar a D₂ a') (v : VertexType R) :
    imageVertex (D.extensionFaceOrderIso D₂ φ hDE R R' a a'
      hvertices hvertices' ha ha' hsame) v =
      D.extensionVertexEquiv D₂ φ R R' a a' hvertices hvertices' ha ha' v := by
  unfold extensionFaceOrderIso
  apply faceOrderIsoOfFacetIncidence_vertex

theorem extensionVertexEquiv_at_label
    (D : SimplexFacetPresentation Q ι) (D₂ : SimplexFacetPresentation Q' ι)
    (φ : FaceType Q ≃o FaceType Q')
    (R R' : ConvexPolytope d) (a a' : E d)
    (hvertices : R.vertices = insert a Q.vertices)
    (hvertices' : R'.vertices = insert a' Q'.vertices)
    (ha : D.AdmissiblePoint a) (ha' : D₂.AdmissiblePoint a')
    (u : Option (VertexType Q)) :
    D.extensionVertexEquiv D₂ φ R R' a a' hvertices hvertices' ha ha'
      (extensionVertexLabels Q R a hvertices (D.apex_not_mem_vertices a ha) u) =
      extensionVertexLabels Q' R' a' hvertices' (D₂.apex_not_mem_vertices a' ha')
        (Equiv.optionCongr (vertexEquivOfFaceOrder φ) u) := by
  dsimp only [extensionVertexEquiv, Equiv.trans_apply]
  rw [Equiv.symm_apply_apply]

theorem realize_extension_close
    (D : SimplexFacetPresentation Q ι) (D₂ : SimplexFacetPresentation Q' ι)
    (φ : FaceType Q ≃o FaceType Q') (hDE : D.Aligned D₂ φ)
    (R : ConvexPolytope d) (a a' : E d)
    (hvertices : R.vertices = insert a Q.vertices)
    (ha : D.AdmissiblePoint a) (ha' : D₂.AdmissiblePoint a')
    (hsame : D.SameCoplanar a D₂ a')
    (K : Subfield ℝ) (hQ'K : CoordinatesIn K Q') (ha'K : ∀ j, a' j ∈ K)
    (ε : ℝ) (hnew : dist a' a < ε)
    (hold : ∀ v : VertexType Q, dist (imageVertex φ v).val v.val < ε) :
    ∃ R' : ConvexPolytope d, ∃ ψ : FaceType R ≃o FaceType R', CoordinatesIn K R' ∧
      ∀ v : VertexType R, dist (imageVertex ψ v).val v.val < ε := by
  obtain ⟨R', hR', _⟩ := D.realize_extension_from_admissible_point D₂ φ hDE
    R a a' hvertices ha ha' hsame
  let ψ := D.extensionFaceOrderIso D₂ φ hDE R R' a a' hvertices hR' ha ha' hsame
  refine ⟨R', ψ, ?_, ?_⟩
  · intro x hx j
    rw [hR'] at hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha'K j
    · exact hQ'K x hx j
  · intro v
    obtain ⟨u, rfl⟩ :=
      (extensionVertexLabels Q R a hvertices (D.apex_not_mem_vertices a ha)).surjective v
    rw [D.extensionFaceOrderIso_vertex D₂ φ hDE R R' a a' hvertices hR' ha ha' hsame,
      D.extensionVertexEquiv_at_label D₂ φ R R' a a' hvertices hR' ha ha']
    cases u with
    | none => exact hnew
    | some v => exact hold v

end SimplexFacetPresentation
end Papers.Polytopes

end
end
end BundlePart13

section BundlePart14
/- Source: Papers/StrictFacetRealization.lean -/





@[expose] public section

/-! Strict incidences give actual vertices and actual facets of a three-polytope. -/

noncomputable section
namespace Papers.StrictFacetRealization
open Set Module Matrix
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.IncidenceCoreGeometry Papers.PolytopeIncidenceConfiguration
open Papers.ActualThreeVertexIndependence Papers.SupportedLabelStability

theorem exists_separating_facet_labels (P : ConvexPolytope 3) (hP : P.IsFullDim)
    (v w : VertexType P) (hne : v≠w) :
    ∃ F : FacetType P, v.val∈F.val.val ∧ w.val∉F.val.val := by
  obtain ⟨F,hF,hvF,hwF⟩ := exists_facet_containing_not_mem P hP
    {v.val} (vertex_isFace P v.property) w.val (vertex_mem_body P w.property)
    (by intro h; exact hne (Subtype.ext (Set.mem_singleton_iff.mp h).symm))
  exact ⟨⟨⟨F,hF.1⟩,hF⟩,hvF (Set.mem_singleton _),hwF⟩

structure Incidences (P : ConvexPolytope 3) (q : VertexType P → E 3)
    (g : FacetType P → E 3 →ᵃ[ℝ] ℝ) : Prop where
  zero : ∀ F v, v.val∈F.val.val → g F (q v)=0
  positive : ∀ F v, v.val∉F.val.val → 0<g F (q v)

variable (P : ConvexPolytope 3) (hP : P.IsFullDim)
  (q : VertexType P → E 3) (g : FacetType P → E 3 →ᵃ[ℝ] ℝ)
  (h : Incidences P q g)

include hP h

theorem incidences_injective : Function.Injective q := by
  intro v w heq
  by_contra hne
  obtain ⟨F,hv,hw⟩ := exists_separating_facet_labels P hP v w hne
  have hz := h.zero F v hv
  have hp := h.positive F w hw
  rw [heq] at hz
  linarith

theorem incidences_nonnegative (F : FacetType P) (v : VertexType P) :
    0≤g F (q v) := by
  by_cases hv : v.val∈F.val.val
  · exact le_of_eq (h.zero F v hv).symm
  · exact (h.positive F v hv).le

def polytope : ConvexPolytope 3 := by
  let S := Finset.univ.image q
  have hS : S.Nonempty := by
    obtain ⟨v,hv⟩ := P.vertices_nonempty
    exact ⟨q ⟨v,hv⟩,Finset.mem_image.mpr ⟨⟨v,hv⟩,Finset.mem_univ _,rfl⟩⟩
  apply polytopeOfStrictMinima S hS
  intro x hx
  obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hx
  let T : Finset (FacetType P) := Finset.univ.filter (fun F => v.val∈F.val.val)
  refine ⟨∑ F∈T,(g F).linear.toContinuousLinearMap,?_⟩
  intro y hy hyne
  obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hy
  have hne : v≠w := by intro hvw; subst w; exact hyne rfl
  obtain ⟨F,hvF,hwF⟩ := exists_separating_facet_labels P hP v w hne
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_lt_sum
  · intro G hG
    have hz := h.zero G v (Finset.mem_filter.mp hG).2
    have hp := incidences_nonnegative P hP q g h G w
    rw [affine_form_apply] at hz hp
    change (g G).linear (q v)≤(g G).linear (q w)
    linarith
  · refine ⟨F,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvF⟩,?_⟩
    have hz := h.zero F v hvF
    have hp := h.positive F w hwF
    rw [affine_form_apply] at hz hp
    change (g F).linear (q v)<(g F).linear (q w)
    linarith

@[simp] theorem polytope_vertices : (polytope P hP q g h).vertices=Finset.univ.image q := rfl

def vertexEquiv : VertexType P ≃ VertexType (polytope P hP q g h) :=
  Equiv.ofBijective
    (fun v => ⟨q v,Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩⟩)
    ⟨fun _ _ heq => incidences_injective P hP q g h (congrArg Subtype.val heq),
      by intro x; obtain ⟨v,_,hv⟩ := Finset.mem_image.mp x.property
         exact ⟨v,Subtype.ext hv⟩⟩

theorem body_nonnegative (F : FacetType P) :
    ∀ x∈(polytope P hP q g h).toSet,0≤g F x := by
  apply affine_nonneg_on_hull
  intro x hx
  obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hx
  exact incidences_nonnegative P hP q g h F v

theorem facet_zeroFace_data (F : FacetType P) :
    (polytope P hP q g h).IsFullDim ∧
    IsFacet (polytope P hP q g h) (affineZeroFace (polytope P hP q g h) (g F)) := by
  let Q := polytope P hP q g h
  let Z := affineZeroFace Q (g F)
  let V := VerticesOn P F.val.val
  have hFdim : faceDim F.val.val=2 := by have hh := F.property.2; rw [hP] at hh; omega
  have hVcard : 3≤Nat.card V := by
    let FF : Face P 2 := ⟨⟨F.val.val,F.property.1⟩,hFdim⟩
    have hh := Papers.PolytopeThreeIncidences.face_vertex_card_gt_dimension P 2 FF
    exact Nat.succ_le_iff.mpr hh
  let S : Finset (E 3) := Finset.univ.image (fun v : V => q v.val)
  have hmapinj : Function.Injective (fun v : V => q v.val) :=
    (incidences_injective P hP q g h).comp Subtype.val_injective
  have hScard : 3≤S.card := by
    rw [Finset.card_image_of_injective _ hmapinj,Finset.card_univ]
    simpa only [Nat.card_eq_fintype_card] using hVcard
  have hSQ : S⊆Q.vertices := by
    intro x hx
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨v.val,Finset.mem_univ _,rfl⟩
  have hSZ : (S : Set (E 3))⊆Z := by
    intro x hx
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hx
    exact ⟨vertex_mem_body Q (Finset.mem_image.mpr ⟨v.val,Finset.mem_univ _,rfl⟩),
      h.zero F v.val v.property⟩
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hZ : Q.IsFace Z := affineZeroFace_isFace Q (g F)
    (body_nonnegative P hP q g h F) (hSne.to_set.mono hSZ)
  have hproper : Z≠Q.toSet := by
    have houtside : ∃ v : VertexType P, v.val ∉ F.val.val := by
      by_contra hh
      push_neg at hh
      have hPF : P.toSet ⊆ F.val.val := convexHull_min
        (fun x hx => hh ⟨x, hx⟩)
        (F.property.1.1.convex (convex_convexHull ℝ _))
      exact F.property.ne_toSet
        (Set.Subset.antisymm (face_subset_toSet P F.property.1) hPF)
    obtain ⟨v, hv⟩ := houtside
    intro heq
    have hz : q v∈Z := heq.symm ▸ vertex_mem_body Q
      (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩)
    exact (ne_of_gt (h.positive F v hv)) hz.2
  have hlow : 2≤faceDim Z := three_vertices_dimension_of_subset Q S hSQ Z (fun _ hx => hSZ hx) hScard
  have hhigh := faceDim_lt_of_ssubset Q hZ (toSet_isFace Q)
    (Set.ssubset_iff_subset_ne.mpr ⟨face_subset_toSet Q hZ,hproper⟩)
  have hamb : Q.dim≤3 := by
    have hh := Submodule.finrank_le (vectorSpan ℝ Q.toSet)
    change finrank ℝ (vectorSpan ℝ Q.toSet)≤3
    simpa only [finrank_euclideanSpace_fin] using hh
  have hdQ : Q.dim=3 := by change faceDim Z<Q.dim at hhigh; omega
  refine ⟨hdQ,hZ,?_⟩
  change faceDim Z+1=Q.dim
  change faceDim Z<Q.dim at hhigh
  omega

theorem polytope_fullDim : (polytope P hP q g h).IsFullDim := by
  have hn := actual_vertices_card_gt_dim P
  rw [hP] at hn
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp (by omega : 1<P.vertices.card)
  obtain ⟨F,_,_⟩ := exists_separating_facet_labels P hP ⟨x,hx⟩ ⟨y,hy⟩
    (fun heq => hxy (congrArg Subtype.val heq))
  exact (facet_zeroFace_data P hP q g h F).1

theorem zeroFace_vertex_iff (F : FacetType P) (v : VertexType P) :
    q v ∈ affineZeroFace (polytope P hP q g h) (g F) ↔ v.val∈F.val.val := by
  constructor
  · intro hv
    by_contra hn
    exact (ne_of_gt (h.positive F v hn)) hv.2
  · intro hv
    exact ⟨vertex_mem_body _ (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩),h.zero F v hv⟩

end Papers.StrictFacetRealization

end
end
end BundlePart14

section BundlePart15
/- Source: Papers/StrictFacetFaceOrder.lean -/



@[expose] public section

/-! Exact reconstruction of the complete face order near a three-polytope. -/

noncomputable section
namespace Papers.StrictFacetRealization
open Set Module Matrix Filter Topology
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeIncidenceConfiguration Papers.PolytopeFaceCounting
open Papers.ActualThreeVertexIndependence Papers.SupportedLabelStability
open Papers.AffineCoordinates

theorem coefficientVector_formOfVector {d : ℕ} (a : Fin (d+1) → ℝ) :
    coefficientVector (formOfVector a)=a := by
  have h := affineCoefficients_fromCoefficients
    (fun i : Option (Fin d) => i.elim (a 0) (fun j => a j.succ))
  ext i
  cases i using Fin.cases with
  | zero => exact congrFun h none
  | succ j => exact congrFun h (some j)

theorem supported_labels_contained_in_facet
    (P : ConvexPolytope 3) (hP : P.IsFullDim) (S : Finset (VertexType P))
    (hne : S.Nonempty)
    (hs : SupportedLabels (fun v : VertexType P => homogeneousVertex v.val) S) :
    ∃ F : FacetType P, ∀ v∈S,v.val∈F.val.val := by
  obtain ⟨a,ha,hpos,hzero⟩ := hs
  let f := formOfVector a
  have hfne : f≠0 := by
    intro hf
    have ha0 : a=0 := by
      rw [← coefficientVector_formOfVector a]
      change coefficientVector f=0
      rw [hf]
      exact coefficientVectorLinear.map_zero
    simp [ha0] at ha
  have hnonneg : ∀ x∈P.toSet,0≤f x := by
    apply affine_nonneg_on_hull
    intro x hx
    simpa only [vector_dot_homogeneous] using hpos ⟨x,hx⟩
  have hZne : (affineZeroFace P f).Nonempty := by
    obtain ⟨v,hv⟩ := hne
    refine ⟨v.val,vertex_mem_body P v.property,?_⟩
    exact (vector_dot_homogeneous a v.val).symm.trans (hzero v hv)
  have hZ : P.IsFace (affineZeroFace P f) := affineZeroFace_isFace P f hnonneg hZne
  have hproper : affineZeroFace P f≠P.toSet := by
    intro heq
    apply hfne
    apply affine_eq_zero_of_body P hP f
    intro x hx
    exact (show x∈affineZeroFace P f from heq.symm ▸ hx).2
  have hnot : ¬P.toSet⊆affineZeroFace P f := by
    intro hsub
    exact hproper (Set.Subset.antisymm (face_subset_toSet P hZ) hsub)
  obtain ⟨x,hx,hxZ⟩ := Set.not_subset.mp hnot
  obtain ⟨F,hF,hZF,_⟩ := exists_facet_containing_not_mem P hP
    (affineZeroFace P f) hZ x hx hxZ
  refine ⟨⟨⟨F,hF.1⟩,hF⟩,?_⟩
  intro v hv
  exact hZF ⟨vertex_mem_body P v.property,
    (vector_dot_homogeneous a v.val).symm.trans (hzero v hv)⟩

theorem faceOrder_of_no_new_supports
    (P : ConvexPolytope 3) (hP : P.IsFullDim)
    (q : VertexType P → E 3) (g : FacetType P → E 3 →ᵃ[ℝ] ℝ)
    (h : Incidences P q g)
    (hnew : ∀ S : Finset (VertexType P),
      SupportedLabels (fun v => homogeneousVertex (q v)) S →
      SupportedLabels (fun v : VertexType P => homogeneousVertex v.val) S) :
    ∃ Q : ConvexPolytope 3, Q.IsFullDim ∧
      ∃ φ : FaceType P ≃o FaceType Q, ∀ v, (imageVertex φ v).val=q v := by
  let Q := polytope P hP q g h
  let b := vertexEquiv P hP q g h
  have hQ : Q.IsFullDim := polytope_fullDim P hP q g h
  have hforward : ∀ F : FaceType P, IsFacet P F.val →
      ∃ G : FaceType Q, IsFacet Q G.val ∧
        ∀ v : VertexType P,(b v).val∈G.val ↔ v.val∈F.val := by
    intro F hF
    let FF : FacetType P := ⟨F,hF⟩
    have hg := (facet_zeroFace_data P hP q g h FF).2
    exact ⟨⟨affineZeroFace Q (g FF),hg.1⟩,hg,zeroFace_vertex_iff P hP q g h FF⟩
  have hbackward : ∀ G : FaceType Q, IsFacet Q G.val →
      ∃ F : FaceType P, IsFacet P F.val ∧
        ∀ v : VertexType P,(b v).val∈G.val ↔ v.val∈F.val := by
    intro G hG
    let S : Finset (VertexType P) := Finset.univ.filter (fun v => q v∈G.val)
    have hS : S.Nonempty := by
      obtain ⟨x,hx,hxG⟩ := face_has_vertex Q G.property
      obtain ⟨v,_,hv⟩ := Finset.mem_image.mp hx
      exact ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [hv] using hxG⟩⟩
    obtain ⟨f,hf⟩ := exists_supportsFace Q G.property
    have ha : coefficientVector f≠0 := by
      intro ha
      apply hG.support_ne_zero hf
      apply coefficientVector_injective
      simpa only [show coefficientVector (0 : E 3 →ᵃ[ℝ] ℝ)=0 from coefficientVectorLinear.map_zero] using ha
    have hsup : SupportedLabels (fun v => homogeneousVertex (q v)) S := by
      apply supportedLabels_of_nonzero_normal _ S (coefficientVector f) ha
      · intro v
        rw [coefficient_dot_homogeneous]
        exact hf.1 (q v) (vertex_mem_body Q (b v).property)
      · intro v hv
        rw [coefficient_dot_homogeneous]
        exact hf.eq_zero (Finset.mem_filter.mp hv).2
    obtain ⟨F,hSF⟩ := supported_labels_contained_in_facet P hP S hS (hnew S hsup)
    have hFQ := (facet_zeroFace_data P hP q g h F).2
    have hsub : G.val⊆affineZeroFace Q (g F) := by
      apply (face_le_iff_vertex_incidence Q G ⟨affineZeroFace Q (g F),hFQ.1⟩).mpr
      intro w hw
      obtain ⟨v,rfl⟩ := b.surjective w
      apply (zeroFace_vertex_iff P hP q g h F v).mpr
      exact hSF v (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩)
    have heq : G.val=affineZeroFace Q (g F) :=
      hG.eq_of_subset hFQ.1 hFQ.ne_toSet hsub
    refine ⟨F.val,F.property,?_⟩
    intro v
    rw [heq]
    exact zeroFace_vertex_iff P hP q g h F v
  let φ := faceOrderIsoOfFacetIncidence P hP Q hQ b hforward hbackward
  refine ⟨Q,hQ,φ,?_⟩
  intro v
  rw [faceOrderIsoOfFacetIncidence_vertex]
  rfl

theorem eventually_faceOrder_of_strict_incidences
    (P : ConvexPolytope 3) (hP : P.IsFullDim) :
    ∀ᶠ q in 𝓝 (Subtype.val : VertexType P → E 3),
      ∀ g : FacetType P → E 3 →ᵃ[ℝ] ℝ, Incidences P q g →
        ∃ Q : ConvexPolytope 3, Q.IsFullDim ∧
          ∃ φ : FaceType P ≃o FaceType Q, ∀ v,(imageVertex φ v).val=q v := by
  have hc : Continuous (fun q : VertexType P → E 3 => fun v => homogeneousVertex (q v)) :=
    continuous_pi fun v => continuous_homogeneousVertex.comp (continuous_apply v)
  have he := hc.continuousAt.eventually
    (eventually_no_new_supportedLabels (fun v : VertexType P => homogeneousVertex v.val))
  filter_upwards [he] with q hq g hg
  exact faceOrder_of_no_new_supports P hP q g hg hq

end Papers.StrictFacetRealization

end
end
end BundlePart15

section BundlePart16
/- Source: Papers/ThreePolytopeRationalDensity.lean -/




@[expose] public section

/-! Rational realisations are dense for every genuine three-polytope. -/

noncomputable section
namespace Papers.ThreePolytopeRationalDensity
open Set Module Matrix Filter Topology
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting
open Papers.PolytopeIncidenceConfiguration Papers.ActualThreeVertexIndependence
open Papers.RationalKernelCharts Papers.RationalOrthogonalityPeeling
open Papers.StrictFacetRealization

def vectorToHomogeneous {d : ℕ} : (Fin (d+1) → ℝ) →ₗ[ℝ] (E d × ℝ) where
  toFun a := (WithLp.toLp 2 (fun j => a j.succ),a 0)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def dehomogeneousVector {d : ℕ} (a : Fin (d+1) → ℝ) : E d :=
  dehomogenizePoint (vectorToHomogeneous a)

theorem dehomogeneousVector_apply {d : ℕ} (a : Fin (d+1) → ℝ) (j : Fin d) :
    dehomogeneousVector a j=a j.succ/a 0 := by
  change (a 0)⁻¹*a j.succ=a j.succ/a 0
  rw [div_eq_mul_inv,mul_comm]

theorem dehomogeneousVector_homogeneousVertex {d : ℕ} (x : E d) :
    dehomogeneousVector (homogeneousVertex x)=x := by
  ext j
  simp [dehomogeneousVector_apply,homogeneousVertex]

theorem homogeneousVertex_dehomogeneousVector {d : ℕ}
    (a : Fin (d+1) → ℝ) (ha : a 0≠0) :
    homogeneousVertex (dehomogeneousVector a)=(a 0)⁻¹ • a := by
  ext i
  cases i using Fin.cases with
  | zero => simp [homogeneousVertex,ha]
  | succ j => simp [homogeneousVertex,dehomogeneousVector_apply,div_eq_mul_inv,mul_comm]

theorem continuousAt_dehomogeneousVector {d : ℕ}
    (a : Fin (d+1) → ℝ) (ha : a 0≠0) : ContinuousAt dehomogeneousVector a := by
  exact (continuousAt_dehomogenizePoint (vectorToHomogeneous a) ha).comp_of_eq
    vectorToHomogeneous.continuous_of_finiteDimensional.continuousAt rfl

theorem formOfVector_dehomogeneousVector {d : ℕ}
    (f a : Fin (d+1) → ℝ) (ha : a 0≠0) :
    formOfVector f (dehomogeneousVector a)=(a 0)⁻¹*(f ⬝ᵥ a) := by
  rw [← vector_dot_homogeneous,homogeneousVertex_dehomogeneousVector a ha]
  simp [dotProduct,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_left_comm,mul_assoc]

def twoFaceOfFacet (P : ConvexPolytope 3) (hP : P.IsFullDim) (F : FacetType P) :
    Face P 2 := ⟨⟨F.val.val,F.property.1⟩,by
    change faceDim F.val.val=2
    have hh := F.property.2
    rw [hP] at hh
    omega⟩

theorem facetOfTwoFace_twoFaceOfFacet
    (P : ConvexPolytope 3) (hP : P.IsFullDim) (F : FacetType P) :
    facetOfTwoFace P hP (twoFaceOfFacet P hP F)=F := by
  apply Subtype.ext
  rfl

theorem three_polytope_rationally_approximable
    (P : ConvexPolytope 3) (hP : P.IsFullDim) : RationallyApproximable P := by
  intro ε hε
  let z₀ := incidenceVectors P hP
  let Qmap : (P.vertices ⊕ Face P 2 → Fin 4 → ℝ) → (VertexType P → E 3) :=
    fun z v => dehomogeneousVector (z (.inl v))
  have hbase : Qmap z₀=(Subtype.val : VertexType P → E 3) := by
    funext v
    exact dehomogeneousVector_homogeneousVertex v.val
  have hQc : ContinuousAt Qmap z₀ := by
    apply continuousAt_pi.mpr
    intro v
    exact (continuousAt_dehomogeneousVector (z₀ (.inl v)) (by simp [z₀,incidenceVectors,homogeneousVertex])).comp_of_eq
      (continuous_apply (Sum.inl v : P.vertices ⊕ Face P 2)).continuousAt rfl
  have hfirst : ∀ᶠ z in 𝓝 z₀, ∀ v : VertexType P,0<z (.inl v) 0 := by
    apply eventually_all.mpr
    intro v
    have hc : Continuous (fun z : P.vertices ⊕ Face P 2 → Fin 4 → ℝ => z (.inl v) 0) :=
      (continuous_apply 0).comp (continuous_apply (Sum.inl v : P.vertices ⊕ Face P 2))
    exact hc.continuousAt.eventually (Ioi_mem_nhds (by simp [z₀,incidenceVectors,homogeneousVertex]))
  have hpositive : ∀ᶠ z in 𝓝 z₀, ∀ F : FacetType P, ∀ v : VertexType P,
      v.val∉F.val.val → 0<z (.inr (twoFaceOfFacet P hP F)) ⬝ᵥ z (.inl v) := by
    apply eventually_all.mpr
    intro F
    apply eventually_all.mpr
    intro v
    by_cases hv : v.val∈F.val.val
    · exact Filter.Eventually.of_forall fun _ h => False.elim (h hv)
    · have hp : 0<chosenFacetForm P F v.val := by
        have hn := (chosenFacetForm_supports P F).1 v.val (vertex_mem_body P v.property)
        have hz : chosenFacetForm P F v.val≠0 := by
          intro hz
          exact hv ((chosenFacetForm_supports P F).mem_iff v.val |>.mpr
            ⟨vertex_mem_body P v.property,hz⟩)
        exact lt_of_le_of_ne hn hz.symm
      have hc : Continuous (fun z : P.vertices ⊕ Face P 2 → Fin 4 → ℝ =>
          z (.inr (twoFaceOfFacet P hP F)) ⬝ᵥ z (.inl v)) :=
        (continuous_apply _).dotProduct (continuous_apply _)
      have hpb : 0<z₀ (.inr (twoFaceOfFacet P hP F)) ⬝ᵥ z₀ (.inl v) := by
        simpa only [z₀,incidenceVectors,Sum.elim_inl,Sum.elim_inr,
          facetOfTwoFace_twoFaceOfFacet,coefficient_dot_homogeneous] using hp
      exact (hc.continuousAt.eventually (Ioi_mem_nhds hpb)).mono fun _ hz _ => hz
  have hreal := hQc.eventually (by
    simpa only [hbase] using eventually_faceOrder_of_strict_incidences P hP)
  have hclose : ∀ᶠ z in 𝓝 z₀, ∀ v : VertexType P,dist (Qmap z v) v.val<ε := by
    apply eventually_all.mpr
    intro v
    have hc := (continuous_apply v : Continuous (fun u : VertexType P → E 3 => u v)).continuousAt.comp_of_eq hQc rfl
    have hh : ContinuousAt (fun z => dist (Qmap z v) v.val) z₀ :=
      hc.dist continuousAt_const
    apply hh.eventually (p := fun t : ℝ => t < ε)
    apply Iio_mem_nhds
    simpa only [hbase,dist_self] using hε
  have hdense := mem_closure_iff_frequently.mp (actual_incidence_rational_density P hP)
  obtain ⟨z,hz,hzfirst,hzpos,hzreal,hzclose⟩ :=
    (hdense.and_eventually (hfirst.and (hpositive.and (hreal.and hclose)))).exists
  let g : FacetType P → E 3 →ᵃ[ℝ] ℝ := fun F =>
    formOfVector (z (.inr (twoFaceOfFacet P hP F)))
  have hinc : Incidences P (Qmap z) g := by
    constructor
    · intro F v hv
      rw [show g F (Qmap z v) = _ from
        formOfVector_dehomogeneousVector _ _ (ne_of_gt (hzfirst v))]
      have hh := hz.2 v (twoFaceOfFacet P hP F) hv
      rw [dotProduct_comm] at hh
      rw [hh,mul_zero]
    · intro F v hv
      rw [show g F (Qmap z v) = _ from
        formOfVector_dehomogeneousVector _ _ (ne_of_gt (hzfirst v))]
      exact mul_pos (inv_pos.mpr (hzfirst v)) (hzpos F v hv)
  obtain ⟨Q,hQ,φ,hφ⟩ := hzreal g hinc
  refine ⟨Q,φ,?_,?_⟩
  · intro x hx j
    obtain ⟨v,hv⟩ := (vertexEquivOfFaceOrder φ).surjective ⟨x,hx⟩
    have hxq : x=Qmap z v := (congrArg Subtype.val hv).symm.trans (hφ v)
    rw [hxq]
    change RatScalar (dehomogeneousVector (z (.inl v)) j)
    rw [dehomogeneousVector_apply]
    exact (hz.1 (.inl v) j.succ).div (hz.1 (.inl v) 0)
  · intro v
    rw [hφ v]
    exact hzclose v

theorem rationallyDense_three_polytope (P : ConvexPolytope 3) (hP : P.IsFullDim) :
    RationallyDense P := by
  intro Q hPQ
  obtain ⟨φ⟩ := hPQ
  have hQ : Q.IsFullDim := (faceOrderIso_polytope_dim φ).trans hP
  exact three_polytope_rationally_approximable Q hQ

end Papers.ThreePolytopeRationalDensity

end
end
end BundlePart16

section BundlePart17
/- Source: Papers/ActualHomogeneousFaceRanks.lean -/





@[expose] public section
noncomputable section
open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.ActualThreeVertexIndependence Papers.HomogeneousSpanDimension
open Papers.FaceVertexCardinality Papers.ThreePolytopeRationalDensity

namespace Papers.RationalityTen.ChirotopeDensity

def coordinateHomogeneousEquiv (d : ℕ) : (Fin (d+1)→ℝ) ≃ₗ[ℝ] (E d×ℝ) where
  toFun := vectorToHomogeneous
  invFun z := Fin.cases z.2 (fun j => z.1 j)
  left_inv a := by ext i; cases i using Fin.cases <;> rfl
  right_inv z := by
    apply Prod.ext
    · ext j; rfl
    · rfl
  map_add' x y := vectorToHomogeneous.map_add x y
  map_smul' a x := vectorToHomogeneous.map_smul a x

theorem coordinateHomogeneousEquiv_vertex {d : ℕ} (x : E d) :
    coordinateHomogeneousEquiv d (homogeneousVertex x)=liftPoint x := by
  apply Prod.ext
  · ext j; rfl
  · rfl

def vertexCoordinates {d n : ℕ} (P : ConvexPolytope d) (e : Fin n≃P.vertices) :
    Fin n→Fin (d+1)→ℝ := fun i => homogeneousVertex (e i).val

def actualFaceLabels {d n : ℕ} (P : ConvexPolytope d) (e : Fin n≃P.vertices)
    (F : PolytopeFace P) : Finset (Fin n) :=
  Finset.univ.filter fun i => (e i).val∈F.carrier

@[simp] theorem mem_actualFaceLabels {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n≃P.vertices) (F : PolytopeFace P) (i : Fin n) :
    i∈actualFaceLabels P e F ↔ (e i).val∈F.carrier := by
  simp [actualFaceLabels]

def actualFaceLabelsEquiv {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n≃P.vertices) (F : PolytopeFace P) :
    actualFaceLabels P e F ≃ VerticesOn P F.carrier where
  toFun i := ⟨e i.val,(mem_actualFaceLabels P e F i.val).mp i.property⟩
  invFun v := ⟨e.symm v.val,by simpa using v.property⟩
  left_inv i := by apply Subtype.ext; exact e.symm_apply_apply i.val
  right_inv v := by apply Subtype.ext; exact e.apply_symm_apply v.val

theorem actualFaceLabels_card {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n≃P.vertices) (F : PolytopeFace P) :
    (actualFaceLabels P e F).card=Nat.card (VerticesOn P F.carrier) := by
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using
    Nat.card_congr (actualFaceLabelsEquiv P e F)

theorem actualFaceLabels_injective {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n≃P.vertices) : Function.Injective (actualFaceLabels P e) := by
  intro F G h
  have he : (⟨F.carrier,F.isFace⟩ : FaceType P)=⟨G.carrier,G.isFace⟩ := by
    apply face_eq_of_vertex_incidence P
    intro v
    obtain ⟨i,rfl⟩ := e.surjective v
    rw [←mem_actualFaceLabels P e F i,←mem_actualFaceLabels P e G i,h]
  exact PolytopeFace.ext (congrArg Subtype.val he)

theorem actualFaceLabels_mono {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n≃P.vertices) {F G : PolytopeFace P} (hFG : F.carrier⊆G.carrier) :
    actualFaceLabels P e F⊆actualFaceLabels P e G := by
  intro i hi
  exact (mem_actualFaceLabels P e G i).mpr (hFG ((mem_actualFaceLabels P e F i).mp hi))

theorem actualFaceLabels_subset_iff {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n≃P.vertices) (F G : PolytopeFace P) :
    actualFaceLabels P e F⊆actualFaceLabels P e G ↔ F.carrier⊆G.carrier := by
  constructor
  · intro h
    apply (face_le_iff_vertex_incidence P ⟨F.carrier,F.isFace⟩ ⟨G.carrier,G.isFace⟩).mpr
    intro v hv
    obtain ⟨i,rfl⟩ := e.surjective v
    exact (mem_actualFaceLabels P e G i).mp (h ((mem_actualFaceLabels P e F i).mpr hv))
  · exact actualFaceLabels_mono P e

theorem actualFaceLabels_rank {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n≃P.vertices) (F : PolytopeFace P) :
    subsetRank (vertexCoordinates P e) (actualFaceLabels P e F)=faceDim F.carrier+1 := by
  let U := Submodule.span ℝ
    (vertexCoordinates P e '' (↑(actualFaceLabels P e F) : Set (Fin n)))
  let V := P.vertices.filter (·∈F.carrier)
  have hmap : U.map (coordinateHomogeneousEquiv d).toLinearMap=liftSpan (V : Set (E d)) := by
    dsimp only [U]
    rw [Submodule.map_span]
    apply congrArg (Submodule.span ℝ)
    ext z
    constructor
    · rintro ⟨a,⟨i,hi,rfl⟩,rfl⟩
      refine ⟨(e i).val,?_,?_⟩
      · exact Finset.mem_filter.mpr ⟨(e i).property,(mem_actualFaceLabels P e F i).mp hi⟩
      · exact (coordinateHomogeneousEquiv_vertex (e i).val).symm
    · rintro ⟨x,hx,rfl⟩
      obtain ⟨hxP,hxF⟩ := Finset.mem_filter.mp hx
      let i := e.symm ⟨x,hxP⟩
      have hi : i∈actualFaceLabels P e F := by simpa [i] using hxF
      refine ⟨vertexCoordinates P e i,⟨i,hi,rfl⟩,?_⟩
      simpa [vertexCoordinates,i] using coordinateHomogeneousEquiv_vertex x
  calc
    subsetRank (vertexCoordinates P e) (actualFaceLabels P e F)=finrank ℝ U := rfl
    _ = finrank ℝ (U.map (coordinateHomogeneousEquiv d).toLinearMap) :=
      ((coordinateHomogeneousEquiv d).finrank_map_eq U).symm
    _ = finrank ℝ (liftSpan F.carrier) := by
      rw [hmap,←liftSpan_convexHull]
      exact congrArg (fun S : Set (E d) => finrank ℝ (liftSpan S))
        (face_eq_hull_vertices P F.isFace).symm
    _ = faceDim F.carrier+1 := finrank_liftSpan F.isFace.2

theorem actualFaceLabels_top {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n≃P.vertices) :
    actualFaceLabels P e ⟨P.toSet,toSet_isFace P⟩=Finset.univ := by
  ext i
  simp only [mem_actualFaceLabels,Finset.mem_univ,iff_true]
  exact subset_convexHull ℝ _ (e i).property

theorem vertexCoordinates_spans {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n≃P.vertices) (hP : P.IsFullDim) : Spans (vertexCoordinates P e) := by
  have h := actualFaceLabels_rank P e ⟨P.toSet,toSet_isFace P⟩
  rw [actualFaceLabels_top] at h
  change subsetRank (vertexCoordinates P e) Finset.univ=P.dim+1 at h
  rw [hP] at h
  apply (spans_iff_matrix_rank _).mpr
  rw [Matrix.rank_eq_finrank_span_row]
  change finrank ℝ (Submodule.span ℝ (Set.range (vertexCoordinates P e))) = d + 1
  unfold subsetRank at h
  have he : vertexCoordinates P e '' (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)) =
      Set.range (vertexCoordinates P e) := by
    ext x
    constructor
    · rintro ⟨i, _, hix⟩
      exact ⟨i, hix⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, Finset.mem_univ i, rfl⟩
  rw [he] at h
  exact h

theorem actualFacetLabels_strictSupport {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n≃P.vertices) (F : FacetType P) :
    StrictSupport (vertexCoordinates P e)
      (actualFaceLabels P e ⟨F.val.val,F.property.1⟩)
      (Papers.PolytopeIncidenceConfiguration.coefficientVector (chosenFacetForm P F)) := by
  constructor
  · intro i hi
    rw [vertexCoordinates,Papers.PolytopeIncidenceConfiguration.coefficient_dot_homogeneous]
    exact (chosenFacetForm_supports P F).eq_zero ((mem_actualFaceLabels P e _ i).mp hi)
  · intro i hi
    rw [vertexCoordinates,Papers.PolytopeIncidenceConfiguration.coefficient_dot_homogeneous]
    have hm : (e i).val∈P.toSet := subset_convexHull ℝ _ (e i).property
    have hn := (chosenFacetForm_supports P F).1 (e i).val hm
    have hz : chosenFacetForm P F (e i).val≠0 := by
      intro hz
      exact hi ((mem_actualFaceLabels P e _ i).mpr
        (((chosenFacetForm_supports P F).mem_iff _).mpr ⟨hm,hz⟩))
    exact lt_of_le_of_ne hn (Ne.symm hz)

theorem vertexCoordinates_small_independent {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n≃P.vertices) (hP : 3≤P.vertices.card)
    (S : Finset (Fin n)) (hS : S.card≤3) :
    LinearIndependent ℝ (fun i : S => vertexCoordinates P e i.val) := by
  exact small_homogeneous_vertex_family_independent P hP (fun i : S => e i.val)
    (e.injective.comp Subtype.val_injective) (by simpa only [Fintype.card_coe] using hS)

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart17

section BundlePart18
/- Source: Papers/ActualCoordinateRealizations.lean -/





@[expose] public section

/-!
# From labeled coordinate hulls to actual polytope realizations

Preserving the labeled exposed-face order preserves every singleton vertex
face. Consequently all approximating points are genuine extreme vertices.
The conclusions below use the paper's actual convex-polytope definitions and
control the vertex map induced by the complete face-order isomorphism.
-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix Filter Topology
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes

def euclideanCoordinateEquiv (d : ℕ) : E d ≃L[ℝ] (Fin d → ℝ) :=
  (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toContinuousLinearEquiv

theorem exposed_image_equiv
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (e : V ≃L[ℝ] W) {A B : Set V} (h : IsExposed ℝ A B) :
    IsExposed ℝ (e '' A) (e '' B) := by
  intro hne
  obtain ⟨_, x, hx, rfl⟩ := hne
  obtain ⟨l, hl⟩ := h ⟨x, hx⟩
  refine ⟨l.comp e.symm.toContinuousLinearMap, ?_⟩
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [hl] at hz
    refine ⟨⟨z, hz.1, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      e.symm_apply_apply] using hz.2 w hw
  · rintro ⟨⟨z, hz, rfl⟩, hmax⟩
    refine ⟨z, ?_, rfl⟩
    rw [hl]
    refine ⟨hz, ?_⟩
    intro w hw
    have hh := hmax (e w) ⟨w, hw, rfl⟩
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      e.symm_apply_apply] using hh

def exposedOrderIso
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (e : V ≃L[ℝ] W) (A : Set V) (B : Set W) (hB : e '' A = B) :
    {F : Set V // IsExposed ℝ A F ∧ F.Nonempty} ≃o
      {F : Set W // IsExposed ℝ B F ∧ F.Nonempty} where
  toFun F := ⟨e '' F.val, hB ▸ exposed_image_equiv e F.property.1,
    F.property.2.image e⟩
  invFun G := ⟨e.symm '' G.val, by
    have h := exposed_image_equiv e.symm G.property.1
    have hA : e.symm '' B = A := by
      rw [← hB, Set.image_image]
      simp only [Function.comp_def, e.symm_apply_apply, Set.image_id']
    exact hA ▸ h,
    G.property.2.image e.symm⟩
  left_inv F := by
    apply Subtype.ext
    change e.symm '' (e '' F.val) = F.val
    rw [Set.image_image]
    simp only [Function.comp_def, e.symm_apply_apply, Set.image_id']
  right_inv G := by
    apply Subtype.ext
    change e '' (e.symm '' G.val) = G.val
    rw [Set.image_image]
    simp only [Function.comp_def, e.apply_symm_apply, Set.image_id']
  map_rel_iff' := by
    intro F G
    change e '' F.val ⊆ e '' G.val ↔ F.val ⊆ G.val
    exact Set.image_subset_image_iff e.injective

def ordinaryVertexCoordinates {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) : Fin n → Fin d → ℝ :=
  fun i => euclideanCoordinateEquiv d (e i).val

theorem ordinaryVertexCoordinates_homogeneous {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) :
    homogeneousPoints (ordinaryVertexCoordinates P e) = vertexCoordinates P e := by
  ext i j
  cases j using Fin.cases <;> rfl

theorem coordinateHull_actual_polytope {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) :
    euclideanCoordinateEquiv d '' P.toSet =
      coordinateHull (ordinaryVertexCoordinates P e) := by
  change (euclideanCoordinateEquiv d).toLinearEquiv.toLinearMap ''
    convexHull ℝ (P.vertices : Set (E d)) = _
  rw [(euclideanCoordinateEquiv d).toLinearEquiv.toLinearMap.image_convexHull]
  apply congrArg (convexHull ℝ)
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
    exact ⟨i, congrArg (fun v : P.vertices => euclideanCoordinateEquiv d v.val) hi⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(e i).val, (e i).property, rfl⟩

def coordinateFaceOrderIso {d n : ℕ} (P : ConvexPolytope d)
    (p : Fin n → Fin d → ℝ)
    (hbody : euclideanCoordinateEquiv d '' P.toSet = coordinateHull p) :
    FaceType P ≃o ActualCoordinateFace p :=
  exposedOrderIso (euclideanCoordinateEquiv d) P.toSet (coordinateHull p) hbody

private theorem actual_vertex_coordinate_labels {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (i : Fin n) :
    faceLabels (ordinaryVertexCoordinates P e)
      (coordinateFaceOrderIso P _ (coordinateHull_actual_polytope P e)
        (vertexFace P (e i))).val = {i} := by
  ext j
  simp only [faceLabels, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  change euclideanCoordinateEquiv d (e j).val ∈
    euclideanCoordinateEquiv d '' {(e i).val} ↔ j = i
  rw [Set.image_singleton, Set.mem_singleton_iff]
  constructor
  · intro h
    exact e.injective (Subtype.ext ((euclideanCoordinateEquiv d).injective h))
  · rintro rfl
    rfl

private theorem exposed_face_singleton_of_labels {n d : ℕ}
    (q : Fin n → Fin d → ℝ) (F : ActualCoordinateFace q) (i : Fin n)
    (h : faceLabels q F.val = {i}) : F.val = {q i} := by
  rw [exposed_face_eq_labelledHull q F.property.1, h]
  simp only [labelledHull, Finset.coe_singleton, Set.image_singleton,
    convexHull_singleton]

theorem coordinate_image_hull {n d : ℕ} (q : Fin n → Fin d → ℝ) :
    (euclideanCoordinateEquiv d).symm '' coordinateHull q =
      convexHull ℝ
        ((Finset.univ.image (fun i => (euclideanCoordinateEquiv d).symm (q i)) :
          Finset (E d)) : Set (E d)) := by
  change (euclideanCoordinateEquiv d).symm.toLinearEquiv.toLinearMap ''
    convexHull ℝ (Set.range q) = _
  rw [(euclideanCoordinateEquiv d).symm.toLinearEquiv.toLinearMap.image_convexHull]
  apply congrArg (convexHull ℝ)
  ext x
  simp only [Set.mem_image, Set.mem_range, Finset.mem_coe, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨q i, ⟨i, rfl⟩, rfl⟩

/-- A coordinate realization with the exact original face labels is an
actual convex polytope, and the induced vertex map has exactly those coordinates. -/
theorem actual_polytope_of_labelled_coordinates {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices)
    (q : Fin n → Fin d → ℝ)
    (h : LabelledPolytopeEquivalent (ordinaryVertexCoordinates P e) q) :
    ∃ Q : ConvexPolytope d, ∃ φ : FaceType P ≃o FaceType Q,
      Q.vertices = Finset.univ.image (fun i => (euclideanCoordinateEquiv d).symm (q i)) ∧
      ∀ i, (imageVertex φ (e i)).val = (euclideanCoordinateEquiv d).symm (q i) := by
  obtain ⟨ψ, hψ⟩ := h
  let σ := coordinateFaceOrderIso P _ (coordinateHull_actual_polytope P e)
  have hsingle (i : Fin n) : (ψ (σ (vertexFace P (e i)))).val = {q i} := by
    apply exposed_face_singleton_of_labels
    rw [hψ]
    exact actual_vertex_coordinate_labels P e i
  let S := Finset.univ.image (fun i => (euclideanCoordinateEquiv d).symm (q i))
  have hSne : S.Nonempty := by
    obtain ⟨v, hv⟩ := P.vertices_nonempty
    exact ⟨_, Finset.mem_image.mpr ⟨e.symm ⟨v, hv⟩, Finset.mem_univ _, rfl⟩⟩
  have hQext : (S : Set (E d)) = (convexHull ℝ (S : Set (E d))).extremePoints ℝ := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      have hex : IsExposed ℝ (coordinateHull q) {q i} :=
        hsingle i ▸ (ψ (σ (vertexFace P (e i)))).property.1
      have hi := exposed_image_equiv (euclideanCoordinateEquiv d).symm hex
      rw [coordinate_image_hull, Set.image_singleton] at hi
      exact hi.isExtreme.mem_extremePoints
    · exact extremePoints_convexHull_subset
  let Q : ConvexPolytope d := ⟨S, hSne, hQext⟩
  have hbody : euclideanCoordinateEquiv d '' Q.toSet = coordinateHull q := by
    change euclideanCoordinateEquiv d '' convexHull ℝ (S : Set (E d)) = _
    rw [← coordinate_image_hull, Set.image_image]
    simp only [Function.comp_def, ContinuousLinearEquiv.apply_symm_apply, Set.image_id']
  let τ := coordinateFaceOrderIso Q q hbody
  let φ := σ.trans (ψ.trans τ.symm)
  refine ⟨Q, φ, rfl, ?_⟩
  intro i
  have hv := congrArg Subtype.val (imageVertex_face φ (e i))
  change {(imageVertex φ (e i)).val} =
    (euclideanCoordinateEquiv d).symm '' (ψ (σ (vertexFace P (e i)))).val at hv
  rw [hsingle i, Set.image_singleton] at hv
  exact Set.singleton_injective hv

/-- Coordinate-space density implies the paper's vertexwise approximation
predicate with genuine extreme vertices and the induced face-order labeling. -/
theorem rationallyApproximable_of_coordinate_density {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices)
    (hdense : ordinaryVertexCoordinates P e ∈ closure
      {q : Fin n → Fin d → ℝ |
        RationalCoordinates q ∧ LabelledPolytopeEquivalent (ordinaryVertexCoordinates P e) q}) :
    Papers.Polytopes.RationallyApproximable P := by
  intro ε hε
  let p := ordinaryVertexCoordinates P e
  have hclose : ∀ᶠ q in 𝓝 p, ∀ i : Fin n,
      dist ((euclideanCoordinateEquiv d).symm (q i)) (e i).val < ε := by
    apply eventually_all.mpr
    intro i
    have hc : Continuous (fun q : Fin n → Fin d → ℝ =>
        dist ((euclideanCoordinateEquiv d).symm (q i)) (e i).val) :=
      ((euclideanCoordinateEquiv d).symm.continuous.comp (continuous_apply i)).dist
        continuous_const
    apply hc.continuousAt.eventually (p := fun t : ℝ => t < ε)
    apply Iio_mem_nhds
    simpa only [p, ordinaryVertexCoordinates, ContinuousLinearEquiv.symm_apply_apply,
      dist_self] using hε
  obtain ⟨q, hq, hnear⟩ :=
    ((mem_closure_iff_frequently.mp hdense).and_eventually hclose).exists
  obtain ⟨Q, φ, hvertices, hφ⟩ := actual_polytope_of_labelled_coordinates P e q hq.2
  refine ⟨Q, φ, ?_, ?_⟩
  · intro x hx j
    rw [hvertices] at hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hq.1 i j
  · intro v
    obtain ⟨i, rfl⟩ := e.surjective v
    rw [hφ]
    exact hnear i

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart18
