module

public import wishart.verified.core04

/- Generated ordinary proof stage. See audit/staged_core/Core05/manifest.json. -/

@[expose] public section

section CanonicalSource100
/- Source: Wishart/PrincipalAssembly.lean -/



open scoped Classical
open MeasureTheory

/-!
# Exact principal target assembly and degenerate-factor cases

The final theorem in this file is deliberately conditional on the two remaining
analytic conclusions: full selected splits and strict active correlated pairs.
It is a proof of their implication to the exact `PrincipalTheorem` proposition,
not an unconditional verification of that proposition. Equality sufficiency,
moment finiteness, subproduct iteration, and zero-power cases are supplied by
actual proved Wishart-law statements rather than additional analytic premises.
-/

namespace WishartVerification

variable {p d : ℕ} {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}

theorem principalMomentIntegrand_erase_of_exponent_zero
    (P : PrincipalPartition p d) (ν : Fin d → ℝ) (J : Finset (Fin d))
    (j : Fin d) (hzero : ν j = 0) (X : SymmetricMatrix p) :
    principalMomentIntegrand P ν J X = principalMomentIntegrand P ν (J.erase j) X := by
  by_cases hj : j ∈ J
  · have h := Finset.mul_prod_erase J
      (fun i ↦ (principalMinor (P.block i) X) ^ ν i) hj
    simpa only [principalMomentIntegrand, hzero, Real.rpow_zero, one_mul] using h.symm
  · rw [Finset.erase_eq_of_notMem hj]

theorem principalMoment_erase_of_exponent_zero
    (P : PrincipalPartition p d) (ν : Fin d → ℝ) (J : Finset (Fin d))
    (j : Fin d) (hzero : ν j = 0) :
    principalMoment α Sigma P ν J = principalMoment α Sigma P ν (J.erase j) := by
  apply integral_congr_ae
  exact ae_of_all _ (principalMomentIntegrand_erase_of_exponent_zero P ν J j hzero)

theorem principal_split_eq_of_selected_exponent_zero
    (P : PrincipalPartition p d) (ν : Fin d → ℝ)
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (J : Finset (Fin d)) (j : Fin d) (hzero : ν j = 0) :
    principalMoment α Sigma P ν {j} * principalMoment α Sigma P ν (J.erase j) =
      principalMoment α Sigma P ν J := by
  rw [principalMoment_singleton_of_exponent_zero P ν hSigma hα j hzero, one_mul]
  exact (principalMoment_erase_of_exponent_zero P ν J j hzero).symm

theorem principalMoment_eq_one_of_zero_exponents
    (P : PrincipalPartition p d) (ν : Fin d → ℝ)
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (J : Finset (Fin d)) (hzero : ∀ i ∈ J, ν i = 0) :
    principalMoment α Sigma P ν J = 1 := by
  letI := TauCeti.Probability.isProbabilityMeasure_nonsingularWishartMeasure hSigma hα
  have hprod (X : SymmetricMatrix p) : principalMomentIntegrand P ν J X = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    rw [hzero i hi, Real.rpow_zero]
  simp only [principalMoment, hprod, integral_const, probReal_univ, one_smul]

theorem principal_split_eq_of_other_exponents_zero
    (P : PrincipalPartition p d) (ν : Fin d → ℝ)
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (J : Finset (Fin d)) (j : Fin d) (hj : j ∈ J)
    (hzero : ∀ i ∈ J, i ≠ j → ν i = 0) :
    principalMoment α Sigma P ν {j} * principalMoment α Sigma P ν (J.erase j) =
      principalMoment α Sigma P ν J := by
  have hrest : principalMoment α Sigma P ν (J.erase j) = 1 :=
    principalMoment_eq_one_of_zero_exponents P ν hSigma hα _
      (fun i hi ↦ hzero i (Finset.mem_of_mem_erase hi) (Finset.mem_erase.mp hi).1)
  have hjoint : principalMoment α Sigma P ν J = principalMoment α Sigma P ν {j} := by
    apply integral_congr_ae
    filter_upwards [] with X
    simp only [principalMomentIntegrand, Finset.prod_singleton]
    exact Finset.prod_eq_single j
      (fun i hi hij ↦ by rw [hzero i hi hij, Real.rpow_zero])
      (fun h ↦ (h hj).elim)
  rw [hrest, mul_one, hjoint]

theorem principal_split_eq_of_one_block
    (P : PrincipalPartition p 1) (ν : Fin 1 → ℝ)
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α) (j : Fin 1) :
    principalMoment α Sigma P ν {j} * principalMoment α Sigma P ν (Finset.univ.erase j) =
      principalMoment α Sigma P ν Finset.univ := by
  have hfull : (Finset.univ : Finset (Fin 1)) = {j} := by
    ext i
    constructor
    · intro hi
      exact Finset.mem_singleton.mpr (Subsingleton.elim i j)
    · intro hi
      exact Finset.mem_univ i
  rw [hfull, Finset.erase_singleton, principalMoment_empty P ν hSigma hα, mul_one]

/-- Explicit conditional assembly into the unchanged full principal target.
Both analytic inputs still need to be discharged. In particular, this theorem
is never to be substituted for an unconditional proof of `PrincipalTheorem`.
-/
theorem principalTheorem_of_selected_splits_and_strict_pairs
    (hselected : ∀ (p d : ℕ) (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
      (P : PrincipalPartition p d) (ν : Fin d → ℝ),
      0 < p → 0 < d → (p : ℝ) - 1 < α → Sigma.PosDef → (∀ i, 0 ≤ ν i) →
      ∀ j : Fin d,
        principalMoment α Sigma P ν {j} *
            principalMoment α Sigma P ν (Finset.univ.erase j) ≤
          principalMoment α Sigma P ν Finset.univ)
    (hstrictPair : ∀ (p d : ℕ) (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
      (P : PrincipalPartition p d) (ν : Fin d → ℝ),
      0 < p → 0 < d → (p : ℝ) - 1 < α → Sigma.PosDef → (∀ i, 0 ≤ ν i) →
      ∀ i j : Fin d, i ≠ j → 0 < ν i → 0 < ν j →
        Sigma.submatrix (fun a : P.block i ↦ (a : Fin p))
          (fun b : P.block j ↦ (b : Fin p)) ≠ 0 →
        principalMoment α Sigma P ν {i} * principalMoment α Sigma P ν {j} <
          principalMoment α Sigma P ν {i, j}) :
    PrincipalTheorem := by
  intro p d α Sigma P ν hp hd hα hSigma hν
  have hsplit := principal_subproduct_splits_of_full_splits P ν hν
    (fun η hη j ↦ hselected p d α Sigma P η hp hd hα hSigma hη j)
  exact principal_result_of_split_pair_factorization P ν hSigma hα hν hsplit
    (hstrictPair p d α Sigma P ν hp hd hα hSigma hν)
    (principalMoment_factorizes_of_activeScaleBlocks P ν hSigma hα hν)

end WishartVerification
end CanonicalSource100

section CanonicalSource101
/- Source: Wishart/PrincipalSelectedSplit.lean -/



open scoped Classical
open MeasureTheory

/-!
# Selected principal splits with the actual conditional monotonicity

All laws, moment identities, integrability, and order properties are supplied
by their proved constructions. For three or more partition blocks, the radial
rank condition follows from disjointness and nonemptiness of the partition.
The two-block endpoint uses the separate unrestricted determinant argument.
-/

namespace WishartVerification

noncomputable section

variable {p d : ℕ}

theorem remainingCompressionData_offset_posSemidef
    (P : PrincipalPartition p d) (ν : Fin d → ℝ)
    (J : Finset (Fin d)) (j : Fin d) (i : J.erase j) :
    ((remainingCompressionData P ν J j i).offset).PosSemidef :=
  Matrix.PosSemidef.zero

theorem remainingCompressionData_exponent_nonneg
    (P : PrincipalPartition p d) (ν : Fin d → ℝ) (hν : ∀ i, 0 ≤ ν i)
    (J : Finset (Fin d)) (j : Fin d) (i : J.erase j) :
    0 ≤ (remainingCompressionData P ν J j i).exponent := hν i

theorem remainingCompressionData_radial_rank_bound
    (P : PrincipalPartition p d) (hd : 3 ≤ d) {α : ℝ} (hα : (p : ℝ) - 1 < α)
    (ν : Fin d → ℝ) (J : Finset (Fin d)) (j : Fin d) (i : J.erase j) :
    ((remainingCompressionData P ν J j i).size : ℝ) + 1 ≤
      α - selectedRank P j + 1 := by
  have h := P.radial_rank_bound hd α hα j i
    (Ne.symm (Finset.mem_erase.mp i.property).1)
  simpa only [remainingCompressionData, selectedRank, Wishart.selectedDimension,
    Fintype.card_coe, add_comm] using h

theorem principalSpectralAverage_nonneg
    (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (P : PrincipalPartition p d) (ν : Fin d → ℝ)
    (J : Finset (Fin d)) (j : Fin d) (lam : Fin (selectedRank P j) → ℝ) :
    0 ≤ principalSpectralAverage α Sigma P ν J j lam :=
  Wishart.regressionSpectralAverage_compressionProduct_nonneg α
    (principalResidualScale P Sigma j) (principalCrossScale P Sigma j)
    (remainingCompressionData P ν J j)
    (remainingCompressionData_offset_posSemidef P ν J j) lam

theorem principalSpectralAverage_monotone_of_three_blocks
    (P : PrincipalPartition p d) (hd : 3 ≤ d)
    {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (ν : Fin d → ℝ) (hν : ∀ i, 0 ≤ ν i)
    (J : Finset (Fin d)) (j : Fin d) :
    MonotoneOn (principalSpectralAverage α Sigma P ν J j)
      (orderedChamber (Set.Ioi 0)) :=
  Wishart.monotoneOn_regressionSpectralAverage_compressionProduct
    (principal_regression_shape P hα j) (principalResidualScale_posDef P hSigma j)
    (principalCrossScale P Sigma j) (remainingCompressionData P ν J j)
    (remainingCompressionData_offset_posSemidef P ν J j)
    (remainingCompressionData_exponent_nonneg P ν hν J j)
    (remainingCompressionData_radial_rank_bound P hd hα ν J j)

/-- Every selected split, including arbitrary retained subproducts, for three
or more nonempty partition blocks in the full real nonsingular shape range. -/
theorem principal_selected_split_of_three_blocks
    (P : PrincipalPartition p d) (hd : 3 ≤ d)
    {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (ν : Fin d → ℝ) (hν : ∀ i, 0 ≤ ν i)
    (J : Finset (Fin d)) (j : Fin d) (hj : j ∈ J) :
    principalMoment α Sigma P ν {j} * principalMoment α Sigma P ν (J.erase j) ≤
      principalMoment α Sigma P ν J :=
  principal_split_of_actual_spectral_monotonicity P hSigma hα ν hν J j hj
    (principalSpectralAverage_nonneg α Sigma P ν J j)
    (principalSpectralAverage_monotone_of_three_blocks P hd hSigma hα ν hν J j)

end

end WishartVerification
end CanonicalSource101

section CanonicalSource102
/- Source: Wishart/HaarNull.lean -/



/-!
# Haar rotations avoid every fixed hyperplane

The argument uses an auxiliary standard Gaussian only to find one direction
whose orthogonal hyperplane has zero mass under an orbit law. Fubini gives that
direction, a reflection moves any prescribed nonzero direction to it, and Haar
invariance transfers the null statement. No sphere-density formula or
measurable choice of rotations is needed.
-/

open MeasureTheory ProbabilityTheory Function
open scoped RealInnerProductSpace Matrix

namespace Wishart

section Gaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A nonzero real linear observable of a standard Gaussian has no atom at zero. -/
theorem stdGaussian_inner_ne_zero {v : E} (hv : v ≠ 0) :
    ∀ᵐ z ∂stdGaussian E, ⟪v, z⟫ ≠ 0 := by
  have hvar : (‖v‖ ^ 2).toNNReal ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr hv)))
  letI := nullSingletonClass_gaussianReal (μ := (0 : ℝ)) hvar
  have hmap : (stdGaussian E).map (innerSL ℝ v) =
      gaussianReal 0 (‖v‖ ^ 2).toNNReal := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, innerSL_apply_norm]
  have ha : ∀ᵐ t ∂(stdGaussian E).map (innerSL ℝ v), t ≠ 0 := by
    rw [hmap]
    exact Measure.ae_ne _ 0
  simpa only [innerSL_apply_apply] using
    (ae_of_ae_map (innerSL ℝ v).continuous.measurable.aemeasurable ha)

/-- For a measurable action realizing every linear isometry, a nonzero vector's
Haar orbit avoids every fixed hyperplane. This also covers dimension one. -/
theorem ae_inner_orbit_ne_zero
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (ν : Measure G) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (hρsurj : Function.Surjective ρ)
    (hρ : Measurable (fun p : G × E => ρ p.1 p.2))
    {u v : E} (hu : u ≠ 0) (hv : v ≠ 0) :
    ∀ᵐ g ∂ν, ⟪u, ρ g v⟫ ≠ 0 := by
  have hprod : ∀ᵐ g ∂ν, ∀ᵐ z ∂stdGaussian E, ⟪z, ρ g v⟫ ≠ 0 := by
    apply Filter.Eventually.of_forall
    intro g
    have hgv : ρ g v ≠ 0 := fun h => hv ((ρ g).map_eq_zero_iff.mp h)
    simpa only [real_inner_comm] using stdGaussian_inner_ne_zero hgv
  have hm : Measurable (fun p : G × E => ⟪p.2, ρ p.1 v⟫) :=
    (continuous_fst.inner continuous_snd).measurable.comp
      (measurable_snd.prodMk (hρ.comp (measurable_fst.prodMk measurable_const)))
  have hswap : ∀ᵐ z ∂stdGaussian E, ∀ᵐ g ∂ν, ⟪z, ρ g v⟫ ≠ 0 :=
    (Measure.ae_ae_comm ((hm (measurableSet_singleton (0 : ℝ))).compl)).mp hprod
  obtain ⟨z, hz⟩ := hswap.exists
  have hz0 : z ≠ 0 := by
    intro hz0
    subst z
    obtain ⟨g, hg⟩ := hz.exists
    exact hg (inner_zero_left _)
  let c : ℝ := ‖z‖ / ‖u‖
  have hc : 0 < c := div_pos (norm_pos_iff.mpr hz0) (norm_pos_iff.mpr hu)
  have hnorm : ‖c • u‖ = ‖z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hu)
  let e : E ≃ₗᵢ[ℝ] E := (ℝ ∙ (c • u - z))ᗮ.reflection
  have he : e (c • u) = z := Submodule.reflection_sub hnorm
  obtain ⟨h, hh⟩ := hρsurj e
  have hshift := (measurePreserving_mul_left ν h).quasiMeasurePreserving.ae hz
  filter_upwards [hshift] with g hg
  have heq : ⟪z, ρ (h * g) v⟫ = c * ⟪u, ρ g v⟫ := by
    rw [ρ.map_mul, hh]
    change ⟪z, e (ρ g v)⟫ = _
    rw [← he, e.inner_map_map, real_inner_smul_left]
  rw [heq] at hg
  exact fun hzero => hg (by rw [hzero, mul_zero])

end Gaussian

namespace Spectral

abbrev Vec (p : ℕ) := EuclideanSpace ℝ (Fin p)

/-- The usual matrix action identifies the orthogonal matrix group with the
group of all real linear isometries of Euclidean space. -/
noncomputable def orthogonalIsometryEquiv (p : ℕ) :
    Orth p ≃* (Vec p ≃ₗᵢ[ℝ] Vec p) :=
  (Unitary.mapEquiv (StarMulEquiv.ofClass
    (Matrix.toEuclideanCLM (n := Fin p) (𝕜 := ℝ)))).toMulEquiv.trans
      Unitary.linearIsometryEquiv

@[simp] theorem orthogonalIsometryEquiv_apply {p : ℕ} (O : Orth p) (v : Vec p) :
    orthogonalIsometryEquiv p O v =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (O : Matrix (Fin p) (Fin p) ℝ) v := rfl

theorem measurable_orthogonalIsometryEquiv (p : ℕ) :
    Measurable (fun x : Orth p × Vec p => orthogonalIsometryEquiv p x.1 x.2) := by
  simp only [orthogonalIsometryEquiv_apply]
  have hc : Continuous (fun x : Orth p × Vec p =>
      ((x.1 : Matrix (Fin p) (Fin p) ℝ), x.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  exact ((Matrix.continuous_uncurry_toEuclideanCLM (n := Fin p) (𝕜 := ℝ)).comp hc).measurable

/-- A nonzero vector rotated by Haar measure has nonzero pairing with each
prescribed nonzero vector almost surely. -/
theorem haar_inner_ne_zero {p : ℕ} {u v : Vec p} (hu : u ≠ 0) (hv : v ≠ 0) :
    ∀ᵐ (O : Orth p) ∂TauCeti.haarProb (Orth p),
      ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (O : Matrix (Fin p) (Fin p) ℝ) v⟫ ≠ 0 := by
  simpa only [MulEquiv.coe_toMonoidHom, orthogonalIsometryEquiv_apply] using
    ae_inner_orbit_ne_zero (TauCeti.haarProb (Orth p))
      (orthogonalIsometryEquiv p).toMonoidHom (orthogonalIsometryEquiv p).surjective
      (measurable_orthogonalIsometryEquiv p) hu hv

/-- The same null-hyperplane statement for the inverse (transpose) Haar frame. -/
theorem haar_inner_transpose_ne_zero {p : ℕ} {u v : Vec p}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    ∀ᵐ (O : Orth p) ∂TauCeti.haarProb (Orth p),
      ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ)
        (O : Matrix (Fin p) (Fin p) ℝ)ᵀ v⟫ ≠ 0 := by
  have h := (Measure.measurePreserving_inv (TauCeti.haarProb (Orth p))).quasiMeasurePreserving.ae
    (haar_inner_ne_zero hu hv)
  simpa only [← Unitary.star_eq_inv, Unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using h

/-- Every specified row of a Haar-rotated nonzero rectangular matrix is nonzero
almost surely. In particular this applies to the last spectral direction. -/
theorem haar_transpose_row_mul_ne_zero {p m : ℕ}
    (K : Matrix (Fin p) (Fin m) ℝ) (hK : K ≠ 0) (i : Fin p) :
    ∀ᵐ (O : Orth p) ∂TauCeti.haarProb (Orth p),
      (fun j => ((O : Matrix (Fin p) (Fin p) ℝ)ᵀ * K) i j) ≠ 0 := by
  classical
  have hentry : ∃ a b, K a b ≠ 0 := by
    by_contra! h
    exact hK (Matrix.ext h)
  obtain ⟨a, b, hab⟩ := hentry
  let v : Vec p := WithLp.toLp 2 (fun r => K r b)
  let u : Vec p := EuclideanSpace.single i 1
  have hv : v ≠ 0 := by
    intro h
    have hz := congrArg (fun x : Vec p => x a) h
    exact hab (by simpa [v] using hz)
  have hu : u ≠ 0 := by
    simp [u, PiLp.single_eq_zero_iff]
  filter_upwards [haar_inner_transpose_ne_zero hu hv] with O hO
  intro hrow
  apply hO
  have hz := congrFun hrow b
  simpa [u, v, EuclideanSpace.inner_single_left, Matrix.toEuclideanCLM_toLp,
    Matrix.mulVec, dotProduct, Matrix.mul_apply] using hz

end Spectral
end Wishart
end CanonicalSource102

section CanonicalSource103
/- Source: Wishart/RegressionPrincipalStrict.lean -/



/-!
# Unrestricted strict comparison for a single trailing principal block

The trailing determinant may be a proper principal compression of the full
complement. Projecting the actual Gaussian rows and residual Wishart law to
those coordinates preserves the real residual degree. The one-determinant
strict theorem therefore applies throughout the entire nonsingular shape
range. Haar avoidance of hyperplanes turns a nonzero cross-scale block into
strictness of every spectral coordinate after averaging.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace Wishart

def projectGaussianCoordinates {m k : ℕ} (f : Fin k → Fin m)
    (z : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun i => z (f i))

@[fun_prop] theorem measurable_projectGaussianCoordinates {m k : ℕ}
    (f : Fin k → Fin m) : Measurable (projectGaussianCoordinates f) := by
  unfold projectGaussianCoordinates
  fun_prop

set_option backward.isDefEq.respectTransparency false in
theorem measurePreserving_projectGaussianCoordinates {m k : ℕ}
    (f : Fin k → Fin m) {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosSemidef) :
    MeasurePreserving (projectGaussianCoordinates f)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) C)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) (C.submatrix f f)) := by
  refine ⟨measurable_projectGaussianCoordinates f, ?_⟩
  have hz : WithLp.toLp 2 (fun _ : Fin k => (0 : ℝ)) =
      (0 : EuclideanSpace ℝ (Fin k)) := by
    apply PiLp.ext
    intro i
    rfl
  unfold projectGaussianCoordinates
  simpa only [PiLp.zero_apply, hz] using
    map_comp_multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) hC f

def regressionNoiseProjection {q m k : ℕ} (f : Fin k → Fin m)
    (x : RegressionNoise q m) : RegressionNoise q k :=
  (fun a => projectGaussianCoordinates f (x.1 a), principalSymmetricBlock f x.2)

@[fun_prop] theorem measurable_regressionNoiseProjection {q m k : ℕ}
    (f : Fin k → Fin m) : Measurable (regressionNoiseProjection (q := q) f) := by
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro a
    exact (measurable_projectGaussianCoordinates f).comp
      ((measurable_pi_apply a).comp measurable_fst)
  · exact (measurable_principalSymmetricBlock f).comp measurable_snd

theorem measurePreserving_regressionNoiseProjection {q m k : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (f : Fin k → Fin m) (hf : Function.Injective f) :
    MeasurePreserving (regressionNoiseProjection (q := q) f)
      (regressionNoiseMeasure n q m C)
      (regressionNoiseMeasure n q k (C.submatrix f f)) := by
  have hdegree : (m : ℝ) - 1 < n - q := by
    push_cast at hn
    linarith
  have hrows := measurePreserving_pi
    (fun _ : Fin q => multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) C)
    (fun _ : Fin q => multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) (C.submatrix f f))
    (fun _ => measurePreserving_projectGaussianCoordinates f hC.posSemidef)
  have hresidual : MeasurePreserving (principalSymmetricBlock f)
      (nonsingularWishartMeasure (n - q) C)
      (nonsingularWishartMeasure (n - q) (C.submatrix f f)) :=
    ⟨measurable_principalSymmetricBlock f,
      map_principalSymmetricBlock_nonsingularWishartMeasure f hf hC hdegree⟩
  exact hrows.prod hresidual

theorem principalSymmetricBlock_regressionGramWithMean {q m k : ℕ}
    (f : Fin k → Fin m) (M : Matrix (Fin m) (Fin q) ℝ) (x : RegressionNoise q m) :
    principalSymmetricBlock f (regressionGramWithMean M x) =
      regressionGramWithMean (M.submatrix f id) (regressionNoiseProjection f x) := by
  apply Subtype.ext
  ext i j
  simp only [principalSymmetricBlock, regressionGramWithMean, regressionNoiseProjection,
    projectGaussianCoordinates, gaussianRowMatrix, Matrix.submatrix_apply,
    Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    PiLp.toLp_apply, id_eq]

theorem spectralRegressionMean_submatrix {q m k : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ)
    (lam : Fin q → ℝ) (f : Fin k → Fin m) :
    (spectralRegressionMean K O lam).submatrix f id =
      spectralRegressionMean (K.submatrix id f) O lam := by
  ext i a
  simp only [Matrix.submatrix_apply, id_eq, spectralRegressionMean_apply,
    Matrix.mul_apply]

theorem spectralConditionalMoment_principal {q m k : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ)
    (lam : Fin q → ℝ) (f : Fin k → Fin m) (hf : Function.Injective f)
    {g : SymmetricMatrix k → ℝ} (hg : Measurable g) :
    spectralConditionalMoment n C K (fun T => g (principalSymmetricBlock f T)) lam O =
      spectralConditionalMoment n (C.submatrix f f) (K.submatrix id f) g lam O := by
  have hproj := measurePreserving_regressionNoiseProjection hn hC f hf
  unfold spectralConditionalMoment
  simp_rw [principalSymmetricBlock_regressionGramWithMean, spectralRegressionMean_submatrix]
  rw [← hproj.map_eq]
  exact (integral_map hproj.measurable.aemeasurable
    (show AEStronglyMeasurable
      (fun x : RegressionNoise q k =>
        g (regressionGramWithMean (spectralRegressionMean (K.submatrix id f) O lam) x))
      ((regressionNoiseMeasure n q m C).map (regressionNoiseProjection f)) from
      (hg.comp (measurable_regressionGramWithMean _)).aestronglyMeasurable)).symm

theorem strictMono_spectralConditionalMoment_principal_det
    {q m k : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ)
    (f : Fin k → Fin m) (hf : Function.Injective f)
    (lam : Fin q → ℝ) (a : Fin q)
    (hrow : (fun i => (Oᵀ * K.submatrix id f) a i) ≠ 0)
    {η : ℝ} (hη : 0 < η) :
    StrictMonoOn (fun t => spectralConditionalMoment n C K
      (fun T => (principalSymmetricBlock f T : Matrix (Fin k) (Fin k) ℝ).det ^ η)
        (Function.update lam a t) O) (Set.Ici 0) := by
  have hkm : k ≤ m := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf
  have hnk : ((q + k : ℕ) : ℝ) - 1 < n := by
    have hkmR : (k : ℝ) ≤ m := by exact_mod_cast hkm
    push_cast at hn ⊢
    linarith
  have hm : Measurable (fun T : SymmetricMatrix k =>
      (T : Matrix (Fin k) (Fin k) ℝ).det ^ η) :=
    continuous_subtype_val.matrix_det.measurable.pow_const _
  simp_rw [spectralConditionalMoment_principal hn hC K O _ f hf hm]
  exact strictMono_spectralRegression_determinant_moment hnk (hC.submatrix hf)
    (K.submatrix id f) O lam a hrow hη

theorem spectralRegressionMean_update_of_row_eq_zero {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ)
    (lam : Fin q → ℝ) (a : Fin q)
    (hrow : (fun i => (Oᵀ * K) a i) = 0) (t : ℝ) :
    spectralRegressionMean K O (Function.update lam a t) = spectralRegressionMean K O lam := by
  ext i b
  simp only [spectralRegressionMean_apply]
  by_cases hba : b = a
  · subst b
    have hzero : (Oᵀ * K) a i = 0 := congrFun hrow i
    simp only [hzero, mul_zero]
  · rw [Function.update_of_ne hba]

theorem monotoneOn_spectralConditionalMoment_principal_det
    {q m k : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ)
    (f : Fin k → Fin m) (hf : Function.Injective f)
    {η : ℝ} (hη : 0 ≤ η) :
    MonotoneOn (fun lam => spectralConditionalMoment n C K
      (fun T => (principalSymmetricBlock f T : Matrix (Fin k) (Fin k) ℝ).det ^ η) lam O)
      (Set.Ici (0 : Fin q → ℝ)) := by
  apply monotoneOn_nonnegative_pi_of_update
  intro lam a
  by_cases hη0 : η = 0
  · subst η
    intro s hs t ht hst
    simp only [spectralConditionalMoment, Real.rpow_zero]
    exact le_rfl
  have hηpos : 0 < η := lt_of_le_of_ne hη (Ne.symm hη0)
  by_cases hrow : (fun i => (Oᵀ * K.submatrix id f) a i) = 0
  · have hm : Measurable (fun T : SymmetricMatrix k =>
        (T : Matrix (Fin k) (Fin k) ℝ).det ^ η) :=
      continuous_subtype_val.matrix_det.measurable.pow_const _
    intro s hs t ht hst
    simp_rw [spectralConditionalMoment_principal hn hC K O _ f hf hm,
      spectralConditionalMoment,
      spectralRegressionMean_update_of_row_eq_zero _ _ _ _ hrow]
    exact le_rfl
  · exact (strictMono_spectralConditionalMoment_principal_det hn hC K O f hf lam a hrow hηpos).monotoneOn

def principalDetCompressionData {m k : ℕ} (f : Fin k → Fin m) (η : ℝ) :
    Unit → CompressionData m :=
  fun _ => ⟨k, 0, (1 : Matrix (Fin m) (Fin m) ℝ).submatrix id f, η⟩

set_option backward.isDefEq.respectTransparency false in
theorem compressionProduct_principalDet {m k : ℕ} (f : Fin k → Fin m) (η : ℝ)
    (T : SymmetricMatrix m) :
    compressionProduct (principalDetCompressionData f η) T =
      (principalSymmetricBlock f T : Matrix (Fin k) (Fin k) ℝ).det ^ η := by
  simp only [compressionProduct, Fintype.prod_unique, principalDetCompressionData,
    zero_add, Matrix.transpose_submatrix, Matrix.transpose_one,
    Matrix.submatrix_one_mul_mul_submatrix_one]
  rfl

theorem integrable_haar_spectralConditionalMoment_principal_det
    {q m k : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ) (f : Fin k → Fin m)
    {η : ℝ} (hη : 0 ≤ η) (lam : Fin q → ℝ) :
    Integrable (fun O : Spectral.Orth q => spectralConditionalMoment n C K
      (fun T => (principalSymmetricBlock f T : Matrix (Fin k) (Fin k) ℝ).det ^ η) lam ↑O)
      (haarProb (Spectral.Orth q)) := by
  have heq : compressionProduct (principalDetCompressionData f η) =
      (fun T => (principalSymmetricBlock f T : Matrix (Fin k) (Fin k) ℝ).det ^ η) :=
    funext (compressionProduct_principalDet f η)
  rw [← heq]
  exact integrable_haar_spectralConditionalMoment_compressionProduct hn hC K
    (principalDetCompressionData f η) (fun _ => hη) lam

theorem monotoneOn_regressionSpectralAverage_principal_det
    {q m k : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ) (f : Fin k → Fin m) (hf : Function.Injective f)
    {η : ℝ} (hη : 0 ≤ η) :
    MonotoneOn (regressionSpectralAverage n C K
      (fun T => (principalSymmetricBlock f T : Matrix (Fin k) (Fin k) ℝ).det ^ η))
      (Spectral.positiveChamber q) := by
  apply parameterAverageOn_monotoneOn
  · intro lam hlam
    exact integrable_haar_spectralConditionalMoment_principal_det hn hC K f hη lam
  · intro lam hlam lam' hlam' hle
    exact Filter.Eventually.of_forall fun O =>
      monotoneOn_spectralConditionalMoment_principal_det hn hC K ↑O f hf hη
        (fun i => (hlam.2 i).le) (fun i => (hlam'.2 i).le) hle

/-- A nonzero selected-to-trailing scale block gives a strict Haar-averaged
comparison in every spectral coordinate, with no extra degree bound. -/
theorem regressionSpectralAverage_principal_det_strict_update
    {q m k : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ) (f : Fin k → Fin m) (hf : Function.Injective f)
    (hK : K.submatrix id f ≠ 0) {η : ℝ} (hη : 0 < η)
    (lam : Fin q → ℝ) (a : Fin q) {s t : ℝ} (hst : s < t)
    (hs : Function.update lam a s ∈ Spectral.positiveChamber q)
    (ht : Function.update lam a t ∈ Spectral.positiveChamber q) :
    regressionSpectralAverage n C K
      (fun T => (principalSymmetricBlock f T : Matrix (Fin k) (Fin k) ℝ).det ^ η)
        (Function.update lam a s) <
      regressionSpectralAverage n C K
        (fun T => (principalSymmetricBlock f T : Matrix (Fin k) (Fin k) ℝ).det ^ η)
          (Function.update lam a t) := by
  apply parameterAverageOn_strict_compare _ _ _ hs ht
    (integrable_haar_spectralConditionalMoment_principal_det hn hC K f hη.le _)
    (integrable_haar_spectralConditionalMoment_principal_det hn hC K f hη.le _)
  filter_upwards [Spectral.haar_transpose_row_mul_ne_zero (K.submatrix id f) hK a] with O hO
  have hs0 : 0 ≤ s := by simpa only [Function.update_self] using (hs.2 a).le
  have ht0 : 0 ≤ t := by simpa only [Function.update_self] using (ht.2 a).le
  exact strictMono_spectralConditionalMoment_principal_det hn hC K ↑O f hf lam a hO hη
    hs0 ht0 hst

end Wishart
end
end CanonicalSource103

section CanonicalSource104
/- Source: Wishart/PrincipalPairSplit.lean -/



open scoped Classical
open MeasureTheory

/-!
# The unrestricted two-factor comparison and strictness

The remaining observable in a pair is literally one determinant of a
principal compression. Its conditional comparison has no determinant-generator
rank threshold. Whitening preserves nonvanishing of the selected cross block,
and Haar averaging supplies strictness in every selected spectral coordinate.
-/

namespace WishartVerification

noncomputable section

variable {p d : ℕ}

theorem remainingPrincipalTest_eq_principal_det
    (P : PrincipalPartition p d) (ν : Fin d → ℝ) (J : Finset (Fin d))
    (j i : Fin d) (hij : i ≠ j) (hJ : J.erase j = {i}) :
    remainingPrincipalTest P ν J j = fun T ↦
      (Wishart.principalSymmetricBlock (remainingBlockCoordinates P j i hij) T :
        Matrix (Fin (Fintype.card (P.block i))) (Fin (Fintype.card (P.block i))) ℝ).det ^ ν i := by
  funext T
  let k : J.erase j := ⟨i, by rw [hJ]; exact Finset.mem_singleton_self i⟩
  have huniq (a : J.erase j) : a = k := by
    apply Subtype.ext
    have ha := a.property
    have hmem : ((a : Fin d) ∈ J.erase j) = ((a : Fin d) ∈ ({i} : Finset (Fin d))) :=
      congrArg (fun S : Finset (Fin d) => (a : Fin d) ∈ S) hJ
    exact Finset.mem_singleton.mp (hmem.mp ha)
  unfold remainingPrincipalTest compressionProduct
  rw [Finset.prod_eq_single k]
  · change ((0 : Matrix (Fin (Fintype.card (P.block i))) (Fin (Fintype.card (P.block i))) ℝ) +
      ((1 : Matrix (Fin (remainingRank P j)) (Fin (remainingRank P j)) ℝ).submatrix id
        (remainingBlockCoordinates P j i hij)).transpose *
        (T : Matrix (Fin (remainingRank P j)) (Fin (remainingRank P j)) ℝ) *
        (1 : Matrix (Fin (remainingRank P j)) (Fin (remainingRank P j)) ℝ).submatrix id
          (remainingBlockCoordinates P j i hij)).det ^ ν i = _
    rw [zero_add, Matrix.transpose_submatrix, Matrix.transpose_one,
      Matrix.submatrix_one_mul_mul_submatrix_one]
    rfl
  · intro a ha hne
    exact (hne (huniq a)).elim
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

theorem principalCrossScale_submatrix_ne_zero
    (P : PrincipalPartition p d) {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (j i : Fin d) (hij : i ≠ j)
    (hcross : Sigma.submatrix (fun a : P.block j ↦ (a : Fin p))
      (fun b : P.block i ↦ (b : Fin p)) ≠ 0) :
    (principalCrossScale P Sigma j).submatrix id
      (remainingBlockCoordinates P j i hij) ≠ 0 := by
  intro hz
  have hraw := (Wishart.normalizedCrossScale_submatrix_eq_zero_iff
    (hSigma.submatrix (Wishart.selectedCoordinatesEquiv (P.block j)).injective)
    (remainingBlockCoordinates P j i hij)).mp hz
  apply hcross
  ext a b
  have hentry := congrFun (congrFun hraw ((Fintype.equivFin (P.block j)) a))
    ((Fintype.equivFin (P.block i)) b)
  simpa [Wishart.crossScale, Matrix.submatrix_apply, remainingBlockCoordinates,
    Wishart.complementCoordinates] using hentry

theorem principalSpectralAverage_monotone_of_single_remaining
    (P : PrincipalPartition p d)
    {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (ν : Fin d → ℝ) (hν : ∀ i, 0 ≤ ν i)
    (J : Finset (Fin d)) (j i : Fin d) (hij : i ≠ j)
    (hJ : J.erase j = {i}) :
    MonotoneOn (principalSpectralAverage α Sigma P ν J j)
      (orderedChamber (Set.Ioi 0)) := by
  unfold principalSpectralAverage
  rw [remainingPrincipalTest_eq_principal_det P ν J j i hij hJ]
  exact Wishart.monotoneOn_regressionSpectralAverage_principal_det
    (principal_regression_shape P hα j) (principalResidualScale_posDef P hSigma j)
    (principalCrossScale P Sigma j) (remainingBlockCoordinates P j i hij)
    (remainingBlockCoordinates_injective P j i hij) (hν i)

theorem principalSpectralAverage_strict_update_of_single_remaining
    (P : PrincipalPartition p d)
    {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (ν : Fin d → ℝ) (J : Finset (Fin d)) (j i : Fin d) (hij : i ≠ j)
    (hJ : J.erase j = {i}) (hνi : 0 < ν i)
    (hcross : Sigma.submatrix (fun a : P.block j ↦ (a : Fin p))
      (fun b : P.block i ↦ (b : Fin p)) ≠ 0)
    (x : Fin (selectedRank P j) → ℝ) (a : Fin (selectedRank P j))
    (s t : ℝ) (hst : s < t)
    (hs : Function.update x a s ∈ orderedChamber (Set.Ioi 0))
    (ht : Function.update x a t ∈ orderedChamber (Set.Ioi 0)) :
    principalSpectralAverage α Sigma P ν J j (Function.update x a s) <
      principalSpectralAverage α Sigma P ν J j (Function.update x a t) := by
  unfold principalSpectralAverage
  rw [remainingPrincipalTest_eq_principal_det P ν J j i hij hJ]
  exact Wishart.regressionSpectralAverage_principal_det_strict_update
    (principal_regression_shape P hα j) (principalResidualScale_posDef P hSigma j)
    (principalCrossScale P Sigma j) (remainingBlockCoordinates P j i hij)
    (remainingBlockCoordinates_injective P j i hij)
    (principalCrossScale_submatrix_ne_zero P hSigma j i hij hcross) hνi x a hst hs ht

/-- The two-factor inequality holds in any ambient principal partition and
throughout the original real nonsingular shape range. -/
theorem principal_pair_split
    (P : PrincipalPartition p d)
    {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (ν : Fin d → ℝ) (hν : ∀ i, 0 ≤ ν i) (j i : Fin d) (hij : i ≠ j) :
    principalMoment α Sigma P ν {j} * principalMoment α Sigma P ν {i} ≤
      principalMoment α Sigma P ν {j, i} := by
  have hJ : ({j, i} : Finset (Fin d)).erase j = {i} := by simp [hij, hij.symm]
  have h := principal_split_of_actual_spectral_monotonicity P hSigma hα ν hν
    {j, i} j (by simp)
    (principalSpectralAverage_nonneg α Sigma P ν {j, i} j)
    (principalSpectralAverage_monotone_of_single_remaining P hSigma hα ν hν
      {j, i} j i hij hJ)
  simpa only [hJ] using h

/-- Strict two-factor inequality for precisely an active nonzero cross-scale
block. No rank, exponent, integer-shape, or ambient-correlation restriction is
introduced. -/
theorem principal_pair_strict_split
    (P : PrincipalPartition p d)
    {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (ν : Fin d → ℝ) (hν : ∀ i, 0 ≤ ν i)
    (j i : Fin d) (hij : i ≠ j) (hνj : 0 < ν j) (hνi : 0 < ν i)
    (hcross : Sigma.submatrix (fun a : P.block j ↦ (a : Fin p))
      (fun b : P.block i ↦ (b : Fin p)) ≠ 0) :
    principalMoment α Sigma P ν {j} * principalMoment α Sigma P ν {i} <
      principalMoment α Sigma P ν {j, i} := by
  have hJ : ({j, i} : Finset (Fin d)).erase j = {i} := by simp [hij, hij.symm]
  have h := principal_strict_split_of_actual_spectral_updates P hSigma hα ν hν
    {j, i} j (by simp) hνj
    (principalSpectralAverage_nonneg α Sigma P ν {j, i} j)
    (principalSpectralAverage_monotone_of_single_remaining P hSigma hα ν hν
      {j, i} j i hij hJ)
    (principalSpectralAverage_strict_update_of_single_remaining P hSigma hα ν
      {j, i} j i hij hJ hνi hcross)
  simpa only [hJ] using h

end

end WishartVerification
end CanonicalSource104

section CanonicalSource105
/- Source: Wishart/PrincipalTheorem.lean -/



open scoped Classical
open MeasureTheory

/-!
# The complete principal target

This file assembles the exact original target, without analytic bridge
hypotheses. The selected-split proof separates the one-block identity, the
unrestricted two-block determinant comparison, and the many-block radial
comparison. Strict correlated pairs and actual block-diagonal factorization
give both directions of the equality characterization.

The file and its entire dependency closure must pass canonical compilation and
the axiom/statement audit before the project is represented as verified.
-/

namespace WishartVerification

variable {p d : ℕ}

/-- The selected split for every nonempty principal partition in the complete
admissible shape and exponent ranges. -/
theorem principal_selected_split
    (P : PrincipalPartition p d)
    {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (ν : Fin d → ℝ) (hν : ∀ i, 0 ≤ ν i) (j : Fin d) :
    principalMoment α Sigma P ν {j} *
        principalMoment α Sigma P ν (Finset.univ.erase j) ≤
      principalMoment α Sigma P ν Finset.univ := by
  by_cases hd : 3 ≤ d
  · exact principal_selected_split_of_three_blocks P hd hSigma hα ν hν
      Finset.univ j (Finset.mem_univ j)
  have hcases : d = 1 ∨ d = 2 := by
    have hj := j.isLt
    omega
  rcases hcases with rfl | hd2
  · exact (principal_split_eq_of_one_block P ν hSigma hα j).le
  · have hcard : (Finset.univ.erase j : Finset (Fin d)).card = 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
        Fintype.card_fin, hd2]
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
    have himem : i ∈ (Finset.univ.erase j : Finset (Fin d)) := by
      rw [hi]
      exact Finset.mem_singleton_self i
    have hij : i ≠ j := (Finset.mem_erase.mp himem).1
    have hfull : (Finset.univ : Finset (Fin d)) = {j, i} := by
      rw [← Finset.insert_erase (Finset.mem_univ j), hi]
    rw [hi, hfull]
    exact principal_pair_split P hSigma hα ν hν j i hij

/-- Theorem 1.1, with all original quantifiers and parameter ranges, joint
moment finiteness, every selected split, the product lower bound, and the exact
active-block equality characterization. -/
theorem theorem_1_1 : PrincipalTheorem := by
  apply principalTheorem_of_selected_splits_and_strict_pairs
  · intro p d α Sigma P ν hp hd hα hSigma hν j
    exact principal_selected_split P hSigma hα ν hν j
  · intro p d α Sigma P ν hp hd hα hSigma hν i j hij hνi hνj hcross
    exact principal_pair_strict_split P hSigma hα ν hν i j hij.symm hνi hνj hcross

end WishartVerification
end CanonicalSource105
