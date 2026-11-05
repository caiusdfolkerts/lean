module

public import Ellipsoid.StrictCoefficientBound
public import Ellipsoid.CoefficientInjectivity
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated

@[expose] public section

noncomputable section

open scoped ContDiff

open Set Filter Matrix
open scoped Topology BigOperators

namespace EllipsoidVerification

def closedCoefficientOrthant (m : ℕ) : Set (Fin m → ℝ) := {x | 0 ≤ x}

def restrictedCoefficientMap (m : ℕ) (e0 en : ℝ) : closedCoefficientOrthant m → (Fin m → ℝ) :=
  fun x => coefficientMap m e0 en x

theorem isClosed_closedCoefficientOrthant (m : ℕ) : IsClosed (closedCoefficientOrthant m) :=
  isClosed_le continuous_const continuous_id

theorem coefficientMap_smooth_neighborhood {m : ℕ} {e0 en : ℝ}
    (h0 : 0 < e0) (hn : 0 < en) :
    ∃ U : Set (Fin m → ℝ), IsOpen U ∧ closedCoefficientOrthant m ⊆ U ∧
      ContDiffOn ℝ ∞ (coefficientMap m e0 en) U := by
  let U := fixedEndpoints m e0 en ⁻¹' positiveCoefficientDomain (m + 1)
  have hPhi : ContDiff ℝ ∞ (fixedEndpoints m e0 en) := by
    apply contDiff_pi.mpr
    intro j
    unfold fixedEndpoints
    split_ifs <;> fun_prop
  refine ⟨U, (isOpen_positiveCoefficientDomain (m + 1)).preimage hPhi.continuous, ?_, ?_⟩
  · exact fun x hx => admissible_mem_positiveCoefficientDomain (fixedEndpoints_admissible h0 hn hx)
  · apply contDiffOn_pi.mpr
    intro k
    exact (contDiffOn_coefficientTransform (k := k.val + 1) (by omega) (by omega)).comp
      hPhi.contDiffOn (fun x hx => hx)

theorem coefficientMap_contDiffAt {m : ℕ} {e0 en : ℝ} {x : Fin m → ℝ}
    (h0 : 0 < e0) (hn : 0 < en) (hx : 0 ≤ x) :
    ContDiffAt ℝ ∞ (coefficientMap m e0 en) x := by
  obtain ⟨U, hU, hO, hF⟩ := coefficientMap_smooth_neighborhood h0 hn
  exact hF.contDiffAt (hU.mem_nhds (hO hx))

theorem continuousOn_coefficientMap_orthant {m : ℕ} {e0 en : ℝ}
    (h0 : 0 < e0) (hn : 0 < en) :
    ContinuousOn (coefficientMap m e0 en) (closedCoefficientOrthant m) :=
  fun x hx => (coefficientMap_contDiffAt h0 hn hx).continuousAt.continuousWithinAt

theorem continuous_restrictedCoefficientMap {m : ℕ} {e0 en : ℝ}
    (h0 : 0 < e0) (hn : 0 < en) : Continuous (restrictedCoefficientMap m e0 en) :=
  (continuousOn_coefficientMap_orthant h0 hn).restrict

theorem coefficientMap_coordinate_lt_sq {m : ℕ} {e0 en : ℝ} {x : Fin m → ℝ}
    (h0 : 0 < e0) (hn : 0 < en) (hx : 0 ≤ x) (i : Fin m) :
    x i < (coefficientMap m e0 en x i) ^ 2 := by
  have hi := i.isLt
  have h := coefficientTransform_coefficient_lt_sq (fixedEndpoints_admissible h0 hn hx)
    (⟨i.val + 1, by omega⟩ : Fin (m + 2))
    (by change 0 < i.val + 1; omega) (by change i.val + 1 < m + 1; omega)
  rw [fixedEndpoints_internal m e0 en x i] at h
  simpa only [coefficientMap, Fin.val_mk] using h

theorem isCompact_coefficientMap_preimage {m : ℕ} {e0 en : ℝ}
    (h0 : 0 < e0) (hn : 0 < en) {K : Set (Fin m → ℝ)} (hK : IsCompact K) :
    IsCompact (closedCoefficientOrthant m ∩ coefficientMap m e0 en ⁻¹' K) := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (continuous_id : Continuous (id : (Fin m → ℝ) → _)).continuousOn
  let M := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  have hclosed := (continuousOn_coefficientMap_orthant h0 hn).preimage_isClosed_of_isClosed
    (isClosed_closedCoefficientOrthant m) hK.isClosed
  apply (isCompact_Icc : IsCompact (Icc (0 : Fin m → ℝ) (fun _ => M ^ 2))).of_isClosed_subset hclosed
  intro x hx
  refine ⟨hx.1, fun i => ?_⟩
  have hbound : ‖coefficientMap m e0 en x‖ ≤ M := (hB _ hx.2).trans (le_max_left _ _)
  have hi : |coefficientMap m e0 en x i| ≤ M := by
    simpa only [Real.norm_eq_abs] using
      (norm_le_pi_norm (coefficientMap m e0 en x) i).trans hbound
  have hsq : (coefficientMap m e0 en x i) ^ 2 ≤ M ^ 2 := by
    have h := abs_le.mp hi
    nlinarith
  exact (coefficientMap_coordinate_lt_sq h0 hn hx.1 i).le.trans hsq

theorem restrictedCoefficientMap_isProperMap {m : ℕ} {e0 en : ℝ}
    (h0 : 0 < e0) (hn : 0 < en) : IsProperMap (restrictedCoefficientMap m e0 en) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨continuous_restrictedCoefficientMap h0 hn, ?_⟩
  intro K hK
  rw [Subtype.isCompact_iff]
  convert isCompact_coefficientMap_preimage h0 hn hK using 1
  ext x
  simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff, Subtype.exists,
    restrictedCoefficientMap, exists_prop]
  aesop

theorem restrictedCoefficientMap_isClosedEmbedding {m : ℕ} {e0 en : ℝ}
    (h0 : 0 < e0) (hn : 0 < en) :
    Topology.IsClosedEmbedding (restrictedCoefficientMap m e0 en) := by
  apply Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_restrictedCoefficientMap h0 hn)
  · intro x y hxy
    exact Subtype.ext (coefficientMap_injOn_nonnegative h0 hn x.property y.property hxy)
  · exact (restrictedCoefficientMap_isProperMap h0 hn).isClosedMap

theorem coefficientMap_has_smooth_localInverse {m : ℕ} {e0 en : ℝ} {x : Fin m → ℝ}
    (h0 : 0 < e0) (hn : 0 < en) (hx : 0 ≤ x) :
    ∃ G : (Fin m → ℝ) → (Fin m → ℝ),
      ContDiffAt ℝ ∞ G (coefficientMap m e0 en x) ∧
      (∀ᶠ y in 𝓝 x, G (coefficientMap m e0 en y) = y) ∧
      (∀ᶠ z in 𝓝 (coefficientMap m e0 en x), coefficientMap m e0 en (G z) = z) := by
  let J := fixedCoefficientJacobian m e0 en x
  have hJ := fixedCoefficientJacobian_diagonallyStable h0 hn hx
  have hinj : Function.Injective (matrixDerivative J) := by
    apply (injective_iff_map_eq_zero (matrixDerivative J)).mpr
    intro v hv
    by_contra hne
    obtain ⟨i, hi⟩ := hJ.exists_positive_coordinate hne
    have hvi := congrFun hv i
    change (J *ᵥ v) i = 0 at hvi
    rw [hvi, mul_zero] at hi
    exact (lt_irrefl 0) hi
  let A := (LinearEquiv.ofInjectiveEndo (matrixDerivative J).toLinearMap hinj).toContinuousLinearEquiv
  have hA : HasFDerivAt (coefficientMap m e0 en) (A : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) x :=
    hasFDerivAt_coefficientMap h0 hn hx
  have hs := coefficientMap_contDiffAt h0 hn hx
  have hstrict := hs.hasStrictFDerivAt' hA (by simp)
  refine ⟨hstrict.localInverse _ A x, ?_, hstrict.eventually_left_inverse,
    hstrict.eventually_right_inverse⟩
  exact hs.to_localInverse hA (by simp)

/-- All assertions of the coefficient-transform theorem are kept explicit,
including its boundary, actual derivative, properness, and local smooth inverse. -/
structure CoefficientTransformConclusion (m : ℕ) (e0 en : ℝ) : Prop where
  injective : Set.InjOn (coefficientMap m e0 en) (closedCoefficientOrthant m)
  smoothNeighborhood : ∃ U : Set (Fin m → ℝ), IsOpen U ∧ closedCoefficientOrthant m ⊆ U ∧
    ContDiffOn ℝ ∞ (coefficientMap m e0 en) U
  principalMinors : ∀ x, 0 ≤ x → principalJacobianPositive (fixedCoefficientJacobian m e0 en x)
  exactDerivative : ∀ x, 0 ≤ x → HasFDerivAt (coefficientMap m e0 en)
    (matrixDerivative (fixedCoefficientJacobian m e0 en x)) x
  strictBound : ∀ x, 0 ≤ x → ∀ i, Real.sqrt (x i) < coefficientMap m e0 en x i
  proper : IsProperMap (restrictedCoefficientMap m e0 en)
  embedding : Topology.IsClosedEmbedding (restrictedCoefficientMap m e0 en)
  closedImage : IsClosed (Set.range (restrictedCoefficientMap m e0 en))
  smoothLocalInverse : ∀ x, 0 ≤ x → ∃ G : (Fin m → ℝ) → (Fin m → ℝ),
    ContDiffAt ℝ ∞ G (coefficientMap m e0 en x) ∧
    (∀ᶠ y in 𝓝 x, G (coefficientMap m e0 en y) = y) ∧
    (∀ᶠ z in 𝓝 (coefficientMap m e0 en x), coefficientMap m e0 en (G z) = z)

theorem coefficient_transform_theorem {m : ℕ} {e0 en : ℝ}
    (h0 : 0 < e0) (hn : 0 < en) : CoefficientTransformConclusion m e0 en where
  injective := coefficientMap_injOn_nonnegative h0 hn
  smoothNeighborhood := coefficientMap_smooth_neighborhood h0 hn
  principalMinors := fun x hx => coefficientMap_principalJacobianPositive h0 hn hx
  exactDerivative := fun x hx => hasFDerivAt_coefficientMap h0 hn hx
  strictBound := by
    intro x hx i
    have hi := i.isLt
    have h := coefficientTransform_gt_sqrt (fixedEndpoints_admissible h0 hn hx)
      (⟨i.val + 1, by omega⟩ : Fin (m + 2))
      (by change 0 < i.val + 1; omega) (by change i.val + 1 < m + 1; omega)
    rw [fixedEndpoints_internal m e0 en x i] at h
    simpa only [coefficientMap, Fin.val_mk] using h
  proper := restrictedCoefficientMap_isProperMap h0 hn
  embedding := restrictedCoefficientMap_isClosedEmbedding h0 hn
  closedImage := (restrictedCoefficientMap_isProperMap h0 hn).isClosed_range
  smoothLocalInverse := fun x hx => coefficientMap_has_smooth_localInverse h0 hn hx

end EllipsoidVerification
