module

public import ellipsoid.verified.main

@[expose] public section

/-!
# Independent literal targets for the remaining ellipsoid claims

These declarations spell out the mathematical conclusions independently
of the four packaged recovery predicates and of
`CoefficientTransformConclusion`.  The intrinsic volumes remain those of
the actual parallel-body Steiner polynomial.  The full affine-ball
parameterization is checked separately in `EllipsoidAffineCheck.lean`.

The coefficient theorem uses `m` internal coordinates, hence ambient
ellipsoid dimension `m+1`; `m=0` is included.  Its corners conclusion is
expressed by an actual proper closed embedding of the closed orthant,
a smooth extension to an open neighborhood, and a smooth ambient local
inverse at every boundary point.  No definition of a manifold embedding
is substituted for those concrete assertions.

This file is an ordinary statement-check gate only.  It does not by itself
assert that the imported facade or the subsequent actual-body/kernel audit
has passed.
-/

noncomputable section

open EllipsoidVerification MeasureTheory Set Filter Matrix
open scoped Classical BigOperators Topology ContDiff

namespace EllipsoidAudit

/-- Theorem 1.2, with both maxima and the minimization over permutations
written out and with the uniform quantifiers in their printed order. -/
def UniformOneOverNStatement : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ a b : ℝ, 0 < a → a ≤ b →
    ∃ C : ℝ, 0 < C ∧ ∀ E F : FullEllipsoid n,
      (∀ i, a ≤ E.semiaxis i ∧ E.semiaxis i ≤ b) →
      (∀ i, a ≤ F.semiaxis i ∧ F.semiaxis i ≤ b) →
      (⨅ σ : Equiv.Perm (Fin n), ⨆ i : Fin n, |E.semiaxis i - F.semiaxis (σ i)|) ≤
        C * Real.rpow
          (⨆ k : Fin n, |intrinsicVolume E.body (k.val + 1) -
            intrinsicVolume F.body (k.val + 1)|) (1 / (n : ℝ))

theorem uniformOneOverN_statement : UniformOneOverNStatement := by
  intro n hn a b ha hab
  obtain ⟨C, hC, h⟩ := uniform_holder_recovery n hn a b ha hab
  exact ⟨C, hC, h⟩

/-- Every exponent larger than `1/n` fails in every positive semiaxis
neighborhood of every interior sphere, for every proposed positive constant. -/
def NoLargerExponentStatement : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ a b r : ℝ, 0 < a → a < r → r < b →
    ∀ γ : ℝ, 1 / (n : ℝ) < γ → ∀ δ C : ℝ, 0 < δ → 0 < C →
      ∃ E F : FullEllipsoid n,
        (∀ i, a ≤ E.semiaxis i ∧ E.semiaxis i ≤ b) ∧
        (∀ i, a ≤ F.semiaxis i ∧ F.semiaxis i ≤ b) ∧
        (∀ i, |E.semiaxis i - r| < δ) ∧
        (∀ i, |F.semiaxis i - r| < δ) ∧
        C * Real.rpow
          (⨆ k : Fin n, |intrinsicVolume E.body (k.val + 1) -
            intrinsicVolume F.body (k.val + 1)|) γ <
          (⨅ σ : Equiv.Perm (Fin n), ⨆ i : Fin n, |E.semiaxis i - F.semiaxis (σ i)|)

theorem noLargerExponent_statement : NoLargerExponentStatement :=
  sharp_holder_recovery

/-- The equal-volume clause retains its exact range `n ≥ 2` and the
literal top intrinsic-volume equality, in addition to all local quantifiers. -/
def NoLargerExponentEqualVolumeStatement : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ a b r : ℝ, 0 < a → a < r → r < b →
    ∀ γ : ℝ, 1 / (n : ℝ) < γ → ∀ δ C : ℝ, 0 < δ → 0 < C →
      ∃ E F : FullEllipsoid n,
        (∀ i, a ≤ E.semiaxis i ∧ E.semiaxis i ≤ b) ∧
        (∀ i, a ≤ F.semiaxis i ∧ F.semiaxis i ≤ b) ∧
        (∀ i, |E.semiaxis i - r| < δ) ∧
        (∀ i, |F.semiaxis i - r| < δ) ∧
        intrinsicVolume E.body n = intrinsicVolume F.body n ∧
        C * Real.rpow
          (⨆ k : Fin n, |intrinsicVolume E.body (k.val + 1) -
            intrinsicVolume F.body (k.val + 1)|) γ <
          (⨅ σ : Equiv.Perm (Fin n), ⨆ i : Fin n, |E.semiaxis i - F.semiaxis (σ i)|)

theorem noLargerExponentEqualVolume_statement : NoLargerExponentEqualVolumeStatement :=
  sharp_holder_recovery_at_fixed_volume

/-- The Jacobian in this audit is the actual Fréchet derivative evaluated
on the standard coordinate vectors, rather than a separately stipulated matrix. -/
def derivativeJacobian (m : ℕ) (e0 en : ℝ) (x : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of (fun k j => (fderiv ℝ
    (fun y : Fin m → ℝ => fun q : Fin m =>
      coefficientTransform (fixedEndpoints m e0 en y) (q.val + 1)) x)
        (Pi.single j 1) k)

theorem derivativeJacobian_eq {m : ℕ} {e0 en : ℝ} {x : Fin m → ℝ}
    (h0 : 0 < e0) (hn : 0 < en) (hx : ∀ i, 0 ≤ x i) :
    derivativeJacobian m e0 en x = fixedCoefficientJacobian m e0 en x := by
  ext k j
  change (fderiv ℝ (coefficientMap m e0 en) x) (Pi.single j 1) k = _
  rw [(hasFDerivAt_coefficientMap h0 hn hx).fderiv]
  change ((fixedCoefficientJacobian m e0 en x) *ᵥ (Pi.single j 1)) k = _
  exact congrFun (Matrix.mulVec_single_one (fixedCoefficientJacobian m e0 en x) j) k

/-- All clauses of Theorem 2.1.  Smoothness on a neighborhood of the entire
closed orthant implies the manuscript's compact-box neighborhood assertion.
The empty principal minor is also positive, since its determinant is one. -/
def CoefficientTransformFullStatement : Prop :=
  ∀ (m : ℕ) (e0 en : ℝ), 0 < e0 → 0 < en →
    let F : (Fin m → ℝ) → (Fin m → ℝ) := fun x k =>
      coefficientTransform (fixedEndpoints m e0 en x) (k.val + 1)
    let O : Set (Fin m → ℝ) := {x | ∀ i, 0 ≤ x i}
    let f : O → (Fin m → ℝ) := fun x => F x.val
    (∀ x y, x ∈ O → y ∈ O → F x = F y → x = y) ∧
    (∃ U : Set (Fin m → ℝ), IsOpen U ∧ O ⊆ U ∧ ContDiffOn ℝ ∞ F U) ∧
    (∀ x, x ∈ O → ∀ s : Finset (Fin m),
      0 < ((derivativeJacobian m e0 en x).submatrix
        (fun i : s => i.val) (fun i : s => i.val)).det) ∧
    (∀ x, x ∈ O → HasFDerivAt F
      (matrixDerivative (fixedCoefficientJacobian m e0 en x)) x) ∧
    (∀ x, x ∈ O → ∀ i, Real.sqrt (x i) < F x i) ∧
    IsProperMap f ∧ Topology.IsClosedEmbedding f ∧ IsClosed (Set.range f) ∧
    (∀ x, x ∈ O → ∃ G : (Fin m → ℝ) → (Fin m → ℝ),
      ContDiffAt ℝ ∞ G (F x) ∧
      (∀ᶠ y in 𝓝 x, G (F y) = y) ∧
      (∀ᶠ z in 𝓝 (F x), F (G z) = z))

theorem coefficientTransformFull_statement : CoefficientTransformFullStatement := by
  intro m e0 en h0 hn
  dsimp only
  have h := coefficient_transform_theorem (m := m) h0 hn
  refine ⟨?_, h.smoothNeighborhood, ?_, h.exactDerivative, h.strictBound,
    h.proper, h.embedding, h.closedImage, h.smoothLocalInverse⟩
  · intro x y hx hy hxy
    exact h.injective hx hy hxy
  · intro x hx s
    rw [derivativeJacobian_eq h0 hn hx]
    exact h.principalMinors x hx s

/-- The displayed strict estimate is also checked directly for every
admissible coefficient vector, without a real-root or positive-internal-coefficient assumption. -/
theorem coefficient_strict_bound_statement {n : ℕ} (e : Fin (n + 1) → ℝ)
    (he : ∀ j, 0 ≤ e j) (h0 : 0 < e 0) (hn : 0 < e (Fin.last n))
    (k : Fin (n + 1)) (hk : 0 < k.val) (hkn : k.val < n) :
    Real.sqrt (e k) < coefficientTransform e k.val :=
  coefficientTransform_gt_sqrt ⟨he, h0, hn⟩ k hk hkn

/-- Section 5.1's measured coefficient box, written with the actual sum of
products defining the elementary symmetric function of squared semiaxes.
The leading coefficient equality is retained separately, including `n=1`. -/
def MeasuredCoefficientBoxStatement : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ E : FullEllipsoid n,
    (∏ i : Fin n, E.semiaxis i ^ 2) =
      (intrinsicVolume E.body n / unitBallVolume n) ^ 2 ∧
    ∀ k : ℕ, 1 ≤ k → k < n →
      (n.choose k : ℝ) * Real.rpow
        (intrinsicVolume E.body n / unitBallVolume n) (2 * (k : ℝ) / n) ≤
        (∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          ∏ i ∈ s, E.semiaxis i ^ 2) ∧
      (∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        ∏ i ∈ s, E.semiaxis i ^ 2) <
          (intrinsicVolume E.body k / unitBallVolume k) ^ 2

theorem measuredCoefficientBox_statement : MeasuredCoefficientBoxStatement := by
  intro n hn E
  constructor
  · change (∏ i : Fin n, E.semiaxis i ^ 2) = (E.volume n / unitBallVolume n) ^ 2
    rw [Finset.prod_pow, E.volume_top hn]
    field_simp [(unitBallVolume_pos n).ne']
  · intro k hk hkn
    let k' : Fin (n + 1) := ⟨k, by omega⟩
    have hk' : 0 < k'.val := by
      change 0 < k
      omega
    have h := measured_coefficient_box hn E k' hk' hkn
    have he : axisCoefficients E.semiaxis k' =
        ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          ∏ i ∈ s, E.semiaxis i ^ 2 := by
      exact elementaryOn_eq_sum_products (fun i => E.semiaxis i ^ 2) hkn.le
    rw [he] at h
    exact ⟨h.1, h.2.1⟩

#print UniformOneOverNStatement
#print NoLargerExponentStatement
#print NoLargerExponentEqualVolumeStatement
#print CoefficientTransformFullStatement
#print MeasuredCoefficientBoxStatement
#print derivativeJacobian
#print EllipsoidVerification.coefficientTransform
#print EllipsoidVerification.fixedEndpoints
#print EllipsoidVerification.coefficientJacobian
#print EllipsoidVerification.matrixDerivative
#print EllipsoidVerification.FullEllipsoid.body
#print EllipsoidVerification.intrinsicVolume

#print axioms uniformOneOverN_statement
#print axioms noLargerExponent_statement
#print axioms noLargerExponentEqualVolume_statement
#print axioms coefficientTransformFull_statement
#print axioms coefficient_strict_bound_statement
#print axioms measuredCoefficientBox_statement

end EllipsoidAudit
