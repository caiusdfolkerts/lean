module

public import Continuation.Divisor.CoordinateCriterion
public import Continuation.Divisor.FullSupportCriterion
public import Continuation.Divisor.IntrinsicAmple
public import Continuation.Divisor.StrictProjectivity
public import Continuation.Divisor.ProjectiveOverField
public import Unimodular.Geometry

/-!
# Ordinary anticanonical ampleness from the positive-coordinate criterion

The numerical criterion has a strict integral gap away from the rays of a
maximal cone. This proves strict unit support on the original fan and then
ampleness of its actual dual canonical bundle. No projectivity hypothesis
is introduced in this implication of Proposition 6.3.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

namespace Unimodular.Thomsen
open PaperVerification.ToricGeometry CategoryTheory
open scoped BigOperators Classical

variable {n : ℕ} (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)

lemma integerPairing_unitCartier (s : F.fullCones) (u : Lattice n) :
    integerPairing u (F.cartierLatticePoint (fun _ => 1) s) =
      -∑ i, (F.fullConeBasis s).repr u i := by
  simp only [PaperVerification.ToricGeometry.SmoothCompleteFan.cartierLatticePoint, one_smul]
  change (∑ j, u j * (-(∑ i, integralDualBasis (F.fullConeBasis s) i)) j) = _
  simp only [Pi.neg_apply, Finset.sum_apply, mul_neg, Finset.mul_sum,
    Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simpa only [mul_comm] using integralDualBasis_pairing (F.fullConeBasis s) i u

/-- Every inactive ray has integral unit-support slack at least one. -/
theorem unitSupport_strict_of_positiveCriterion
    (h : ∀ s : F.fullCones, ∀ u ∈ F.rays,
      (∑ i, max ((F.fullConeBasis s).repr u i) 0) ≤ 1) :
    F.IsStrictSupport (fun _ => 1) := by
  apply F.strictSupport_of_full_cartier_inequalities F.isPure
  intro s u hu hus
  have hsum : (∑ i, (F.fullConeBasis s).repr u i) ≤ 0 := by
    apply Unimodular.sum_nonpos_of_positive_mass_le_one _ (h s u hu)
    intro i hi
    have he : F.fullConeBasis s i = u := by
      apply (F.fullConeBasis s).repr.injective
      ext j
      have hij := congrFun hi j
      simpa [Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply, eq_comm] using hij.symm
    apply hus
    rw [F.fullConeBasis_ray_set]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, he⟩
  have hpoint := F.embed_cartierLatticePoint (fun _ => (1 : ℤ)) s
  simp only [Int.cast_one] at hpoint
  rw [← hpoint,
    PaperVerification.ToricGeometry.SmoothCompleteFan.normalRay_pairing_lattice]
  change (-1 : ℝ) < ((integerPairing u (F.cartierLatticePoint (fun _ => 1) s) : ℤ) : ℝ)
  rw [integerPairing_unitCartier]
  have hsumR : ((∑ i, (F.fullConeBasis s).repr u i : ℤ) : ℝ) ≤ 0 := by
    exact_mod_cast hsum
  simp only [Int.cast_neg]
  linarith

/-- The Fano implication of Proposition 6.3 concerns the intrinsically
constructed dual of the top exterior power of Kähler differentials. -/
theorem anticanonical_isAmple_of_positiveCriterion
    (k : Type u) [Field k]
    (h : Unimodular.ConeBases.PositiveCriterion
      (Unimodular.FanInterfaces.dictionaryToricFan F)) :
    Unimodular.NefBig.IsAmpleModule
      (Unimodular.NefBig.anticanonicalLineBundle F k).obj :=
  Unimodular.NefBig.anticanonical_isAmple_of_strictSupport F k
    (unitSupport_strict_of_positiveCriterion F
      ((Unimodular.FanInterfaces.dictionaryPositiveCriterion_iff F).mp h))

/-- The full Fano implication includes an actual finite projective embedding
and ordinary properness, not only the support-function inequality. -/
theorem smooth_projective_fano_of_positiveCriterion
    (k : Type u) [Field k]
    (h : Unimodular.ConeBases.PositiveCriterion
      (Unimodular.FanInterfaces.dictionaryToricFan F)) :
    AlgebraicGeometry.Smooth (F.fanSchemeStructureMap k) ∧
    AlgebraicGeometry.IsProper (F.fanSchemeStructureMap k) ∧
    topologicalKrullDim (F.fanScheme k) = n ∧
    Unimodular.NefBig.IsAmpleModule (Unimodular.NefBig.anticanonicalLineBundle F k).obj ∧
    ∃ ha : F.IsStrictSupport (fun _ => ((1 : ℤ) : ℝ)),
      AlgebraicGeometry.IsClosedImmersion
        (Unimodular.Projectivity.strictSupportProjectiveEmbedding F (fun _ => 1) ha k) ∧
      Unimodular.Projectivity.strictSupportProjectiveEmbedding F (fun _ => 1) ha k ≫
        Unimodular.Projectivity.polynomialProjectiveToSpec k
          (Unimodular.Projectivity.WeightIndex.{u} (F := F)) = F.fanSchemeStructureMap k := by
  let ha : F.IsStrictSupport (fun _ => ((1 : ℤ) : ℝ)) := by
    simpa only [Int.cast_one] using unitSupport_strict_of_positiveCriterion F
      ((Unimodular.FanInterfaces.dictionaryPositiveCriterion_iff F).mp h)
  let D := Unimodular.Projectivity.strictSupportVertexData F (fun _ => 1) ha
  exact ⟨Unimodular.NefBig.fanScheme_smooth F k, D.fanScheme_isProper k,
    F.fanScheme_topologicalKrullDim k F.isPure,
    anticanonical_isAmple_of_positiveCriterion F k h,
    ha, inferInstance, D.fanProjectiveEmbedding_toSpec k⟩

/-- The actual anticanonical section polytope is, up to the integral
reflection `x ↦ -x`, a deeply monotone smooth reflexive presentation.
Its outward primitive normals are exactly the original fan rays. -/
theorem anticanonical_polytope_deeplyMonotone
    (h : Unimodular.ConeBases.PositiveCriterion
      (Unimodular.FanInterfaces.dictionaryToricFan F)) :
    ∃ P : Unimodular.SmoothReflexivePresentation n,
      P.normals = F.rays ∧ P.DeeplyMonotone ∧
      ∀ x : Unimodular.Ambient n,
        x ∈ P.carrier ↔ -x ∈ F.fanPolytope (fun _ => 1) := by
  obtain ⟨σ, hr, hc⟩ := Unimodular.FanBridge.exists_smoothCompleteFan
    (Unimodular.FanInterfaces.dictionaryToricFan F)
    (Unimodular.FanInterfaces.dictionaryToricFan_complete F)
    (Unimodular.FanInterfaces.dictionaryToricFan_regular F)
  let P := σ.polarPresentation (hc.mp h)
  have hnormals : P.normals = F.rays := by
    ext v
    change v ∈ σ.rayFinset ↔ v ∈ F.rays
    exact (σ.mem_rayFinset v).trans
      ((hr v).trans (Unimodular.FanInterfaces.dictionaryToricFan_ray_iff F v))
  refine ⟨P, hnormals, σ.polarPresentation_deeplyMonotone (hc.mp h), ?_⟩
  intro x
  rw [P.mem_carrier_iff, hnormals]
  change (∀ v ∈ F.rays, Unimodular.pairing x v ≤ 1) ↔
    ∀ v ∈ F.rays, -(1 : ℝ) ≤
      (dotProductEquiv ℝ (Fin n) (PaperVerification.ToricGeometry.embed n v)) (-x)
  have he (v : Lattice n) :
      (dotProductEquiv ℝ (Fin n) (PaperVerification.ToricGeometry.embed n v)) (-x) =
        -Unimodular.pairing x v := by
    simp [dotProductEquiv, dotProduct, PaperVerification.ToricGeometry.embed,
      Unimodular.pairing, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, mul_comm]
  constructor
  · intro hx v hv
    rw [he]
    exact neg_le_neg (hx v hv)
  · intro hx v hv
    have hh := hx v hv
    rw [he] at hh
    exact neg_le_neg_iff.mp hh

#print axioms anticanonical_polytope_deeplyMonotone

#print axioms smooth_projective_fano_of_positiveCriterion

#print axioms integerPairing_unitCartier
#print axioms unitSupport_strict_of_positiveCriterion
#print axioms anticanonical_isAmple_of_positiveCriterion
end Unimodular.Thomsen
