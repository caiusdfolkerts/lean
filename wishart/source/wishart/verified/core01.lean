module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Logic.Equiv.Basic
public import tau_ceti.probability.distributions.wishart.bartlett
public import tau_ceti.probability.distributions.gaussian.affine
public import tau_ceti.measure_theory.constructions.pi
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Measurable
public import tau_ceti.probability.distributions.wishart.congruence
public import tau_ceti.probability.distributions.wishart.marginal
public import tau_ceti.probability.distributions.wishart.moments
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import tau_ceti.analysis.calculus.f_deriv.det
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/- Generated ordinary proof stage. See audit/staged_core/Core01/manifest.json. -/

@[expose] public section

section CanonicalSource0
/- Source: Wishart/BartlettIndices.lean -/



/-!
# Block coordinates for a lower triangular matrix

The lower triangular positions of a `(q + m) × (q + m)` matrix split into the
lower triangle of the first block, the rectangular off-diagonal block, and the
lower triangle of the second block.  This finite equivalence supplies the exact
coordinate partition used in the Bartlett proof of Wishart block regression.
-/

namespace Wishart

/-- Positions on or below the diagonal, with the same convention as TauCeti's
`lowerTriangle`: the row index is first. -/
abbrev LowerIndex (p : ℕ) := {ij : Fin p × Fin p // ij.2 ≤ ij.1}

abbrev BlockLowerIndex (q m : ℕ) :=
  LowerIndex q ⊕ ((Fin m × Fin q) ⊕ LowerIndex m)

def blockLowerIndex (q m : ℕ) : BlockLowerIndex q m → LowerIndex (q + m)
  | .inl ij => ⟨(ij.1.1.castAdd m, ij.1.2.castAdd m), ij.2⟩
  | .inr (.inl ij) =>
      ⟨(Fin.natAdd q ij.1, ij.2.castAdd m), by
        change ij.2.val ≤ q + ij.1.val
        omega⟩
  | .inr (.inr ij) =>
      ⟨(Fin.natAdd q ij.1.1, Fin.natAdd q ij.1.2), by
        change q + ij.1.2.val ≤ q + ij.1.1.val
        exact Nat.add_le_add_left ij.2 q⟩

theorem blockLowerIndex_injective (q m : ℕ) : Function.Injective (blockLowerIndex q m) := by
  intro a b h
  have hrow := congrArg (fun ij : LowerIndex (q + m) => ij.1.1.val) h
  have hcol := congrArg (fun ij : LowerIndex (q + m) => ij.1.2.val) h
  rcases a with a | (a | a) <;> rcases b with b | (b | b)
  · apply congrArg Sum.inl
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · exact hrow
    · exact hcol
  · simp only [blockLowerIndex, Fin.val_castAdd, Fin.val_natAdd] at hrow
    omega
  · simp only [blockLowerIndex, Fin.val_castAdd, Fin.val_natAdd] at hrow
    omega
  · simp only [blockLowerIndex, Fin.val_castAdd, Fin.val_natAdd] at hrow
    omega
  · apply congrArg Sum.inr
    apply congrArg Sum.inl
    apply Prod.ext <;> apply Fin.ext
    · simpa only [blockLowerIndex, Fin.val_natAdd, Nat.add_left_cancel_iff] using hrow
    · exact hcol
  · simp only [blockLowerIndex, Fin.val_castAdd, Fin.val_natAdd] at hcol
    omega
  · simp only [blockLowerIndex, Fin.val_castAdd, Fin.val_natAdd] at hrow
    omega
  · simp only [blockLowerIndex, Fin.val_castAdd, Fin.val_natAdd] at hcol
    omega
  · apply congrArg Sum.inr
    apply congrArg Sum.inr
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · simpa only [blockLowerIndex, Fin.val_natAdd, Nat.add_left_cancel_iff] using hrow
    · simpa only [blockLowerIndex, Fin.val_natAdd, Nat.add_left_cancel_iff] using hcol

theorem blockLowerIndex_surjective (q m : ℕ) : Function.Surjective (blockLowerIndex q m) := by
  rintro ⟨⟨i, j⟩, hji⟩
  by_cases hi : i.val < q
  · let i₀ : Fin q := ⟨i.val, hi⟩
    let j₀ : Fin q := ⟨j.val, Nat.lt_of_le_of_lt hji hi⟩
    refine ⟨.inl ⟨(i₀, j₀), hji⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> rfl
  · have hiq : q ≤ i.val := Nat.le_of_not_gt hi
    let i₁ : Fin m := ⟨i.val - q, by omega⟩
    by_cases hj : j.val < q
    · let j₀ : Fin q := ⟨j.val, hj⟩
      refine ⟨.inr (.inl (i₁, j₀)), ?_⟩
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext
      · simp [blockLowerIndex, i₁, Nat.add_sub_of_le hiq]
      · rfl
    · have hjq : q ≤ j.val := Nat.le_of_not_gt hj
      let j₁ : Fin m := ⟨j.val - q, by omega⟩
      have hji₁ : j₁ ≤ i₁ := Nat.sub_le_sub_right hji q
      refine ⟨.inr (.inr ⟨(i₁, j₁), hji₁⟩), ?_⟩
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext
      · simp [blockLowerIndex, i₁, Nat.add_sub_of_le hiq]
      · simp [blockLowerIndex, j₁, Nat.add_sub_of_le hjq]

noncomputable def blockLowerEquiv (q m : ℕ) : BlockLowerIndex q m ≃ LowerIndex (q + m) :=
  Equiv.ofBijective (blockLowerIndex q m)
    ⟨blockLowerIndex_injective q m, blockLowerIndex_surjective q m⟩

@[simp] theorem blockLowerEquiv_apply (q m : ℕ) (ij : BlockLowerIndex q m) :
    blockLowerEquiv q m ij = blockLowerIndex q m ij := rfl

end Wishart
end CanonicalSource0

section CanonicalSource1
/- Source: Wishart/BartlettBlocks.lean -/



/-!
# Bartlett block regression

The Bartlett coordinates of a standard Wishart matrix split into three
independent groups: the selected block, a rectangular standard Gaussian block,
and a lower-dimensional Bartlett family with its degree reduced by the selected
rank.  This file proves that split as an equality of concrete product measures
and records the associated block Gram identity.
-/

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open scoped Matrix

noncomputable section

namespace Wishart

def blockBartlettCoordinateMeasure (n : ℝ) (q m : ℕ) :
    BlockLowerIndex q m → Measure ℝ
  | .inl ij => bartlettCoordinateMeasure n ij
  | .inr (.inl _) => gaussianReal 0 1
  | .inr (.inr ij) => bartlettCoordinateMeasure (n - q) ij

/-- Bartlett coordinate laws depend only on whether the position is diagonal
and on the degree minus its row index. -/
theorem bartlettCoordinateMeasure_congr {p r : ℕ} (n n' : ℝ)
    (ij : LowerIndex p) (kl : LowerIndex r)
    (hdiag : (ij.1.1 = ij.1.2) ↔ (kl.1.1 = kl.1.2))
    (hdegree : n - (ij.1.1 : ℝ) = n' - (kl.1.1 : ℝ)) :
    bartlettCoordinateMeasure n ij = bartlettCoordinateMeasure n' kl := by
  by_cases hi : ij.1.1 = ij.1.2
  · rw [bartlettCoordinateMeasure_of_eq n (ij := ij) hi,
      bartlettCoordinateMeasure_of_eq n' (ij := kl) (hdiag.mp hi), hdegree]
  · rw [bartlettCoordinateMeasure_of_ne n (ij := ij) hi,
      bartlettCoordinateMeasure_of_ne n' (ij := kl) (fun hk => hi (hdiag.mpr hk))]

theorem bartlettCoordinateMeasure_blockLowerIndex (n : ℝ) (q m : ℕ)
    (ij : BlockLowerIndex q m) :
    bartlettCoordinateMeasure n (blockLowerIndex q m ij) =
      blockBartlettCoordinateMeasure n q m ij := by
  rcases ij with ij | (ij | ij)
  · change bartlettCoordinateMeasure n (blockLowerIndex q m (.inl ij)) =
      bartlettCoordinateMeasure n ij
    apply bartlettCoordinateMeasure_congr
    · simp [blockLowerIndex]
    · simp [blockLowerIndex]
  · have hne : Fin.natAdd q ij.1 ≠ Fin.castAdd m ij.2 := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
      omega
    exact bartlettCoordinateMeasure_of_ne n
      (ij := blockLowerIndex q m (.inr (.inl ij))) hne
  · change bartlettCoordinateMeasure n (blockLowerIndex q m (.inr (.inr ij))) =
      bartlettCoordinateMeasure (n - q) ij
    apply bartlettCoordinateMeasure_congr
    · simp [blockLowerIndex]
    · simp only [blockLowerIndex, Fin.val_natAdd, Nat.cast_add]
      ring

def assembleBlockLowerCoordinates (q m : ℕ) (x : BlockLowerIndex q m → ℝ) :
    LowerIndex (q + m) → ℝ := x ∘ (blockLowerEquiv q m).symm

@[simp] theorem assembleBlockLowerCoordinates_apply (q m : ℕ)
    (x : BlockLowerIndex q m → ℝ) (ij : BlockLowerIndex q m) :
    assembleBlockLowerCoordinates q m x (blockLowerIndex q m ij) = x ij := by
  change x ((blockLowerEquiv q m).symm (blockLowerEquiv q m ij)) = x ij
  exact congrArg x ((blockLowerEquiv q m).symm_apply_apply ij)

@[fun_prop] theorem measurable_assembleBlockLowerCoordinates (q m : ℕ) :
    Measurable (assembleBlockLowerCoordinates q m) := by
  unfold assembleBlockLowerCoordinates
  fun_prop

instance (n : ℝ) (q m : ℕ) (ij : BlockLowerIndex q m) :
    SigmaFinite (blockBartlettCoordinateMeasure n q m ij) := by
  rcases ij with ij | (ij | ij) <;>
    simp only [blockBartlettCoordinateMeasure] <;> infer_instance

theorem map_assembleBlockLowerCoordinates (n : ℝ) (q m : ℕ) :
    (Measure.pi (blockBartlettCoordinateMeasure n q m)).map
        (assembleBlockLowerCoordinates q m) =
      Measure.pi (bartlettCoordinateMeasure (p := q + m) n) := by
  have h := (measurePreserving_piCongrLeft
    (bartlettCoordinateMeasure (p := q + m) n) (blockLowerEquiv q m)).map_eq
  have hfun :
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : LowerIndex (q + m) => ℝ)
        (blockLowerEquiv q m)) = assembleBlockLowerCoordinates q m := by
    funext x j
    obtain ⟨i, rfl⟩ := (blockLowerEquiv q m).surjective j
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
    simpa only [blockLowerEquiv_apply] using
      (assembleBlockLowerCoordinates_apply q m x i).symm
  rw [hfun] at h
  simpa only [blockLowerEquiv_apply, bartlettCoordinateMeasure_blockLowerIndex] using h

/-- Exact real-shape Wishart law in the three independent blocks of Bartlett
coordinates.  The right-hand side is a product measure before the explicit Gram
map; the reduced degree `n-q` is part of its definition. -/
theorem nonsingularWishartMeasure_one_eq_map_blockBartlett
    {n : ℝ} {q m : ℕ} (hn : ((q + m : ℕ) : ℝ) - 1 < n) :
    nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) =
      (Measure.pi (blockBartlettCoordinateMeasure n q m)).map
        (lowerTriangleGram (q + m) ∘ assembleBlockLowerCoordinates q m) := by
  rw [nonsingularWishartMeasure_one_eq_map_lowerTriangleGram hn,
    ← map_assembleBlockLowerCoordinates n q m,
    Measure.map_map (measurable_lowerTriangleGram (q + m))
      (measurable_assembleBlockLowerCoordinates q m)]

abbrev BartlettBlockData (q m : ℕ) :=
  (LowerIndex q → ℝ) × ((Fin m × Fin q → ℝ) × (LowerIndex m → ℝ))

def bartlettBlockDataMeasure (n : ℝ) (q m : ℕ) : Measure (BartlettBlockData q m) :=
  (Measure.pi (bartlettCoordinateMeasure (p := q) n)).prod
    ((Measure.pi (fun _ : Fin m × Fin q => gaussianReal 0 1)).prod
      (Measure.pi (bartlettCoordinateMeasure (p := m) (n - q))))

def packBartlettBlockData (q m : ℕ) (x : BartlettBlockData q m) :
    BlockLowerIndex q m → ℝ :=
  Sum.elim x.1 (Sum.elim x.2.1 x.2.2)

@[fun_prop] theorem measurable_packBartlettBlockData (q m : ℕ) :
    Measurable (packBartlettBlockData q m) := by
  apply measurable_pi_iff.mpr
  intro ij
  rcases ij with ij | (ij | ij) <;> dsimp [packBartlettBlockData] <;> fun_prop

/-- The three groups of coordinates have their literal iterated product law,
so independence here is proved by measure transport, rather than added as an
assumption about a purported Wishart representation. -/
theorem map_packBartlettBlockData (n : ℝ) (q m : ℕ) :
    (bartlettBlockDataMeasure n q m).map (packBartlettBlockData q m) =
      Measure.pi (blockBartlettCoordinateMeasure n q m) := by
  let μinner : ((Fin m × Fin q) ⊕ LowerIndex m) → Measure ℝ :=
    Sum.elim (fun _ => gaussianReal 0 1) (bartlettCoordinateMeasure (n - q))
  letI (ij : (Fin m × Fin q) ⊕ LowerIndex m) : SigmaFinite (μinner ij) := by
    rcases ij with ij | ij <;> dsimp [μinner] <;> infer_instance
  have hinner := measurePreserving_sumPiEquivProdPi_symm μinner
  have houter := measurePreserving_sumPiEquivProdPi_symm
    (blockBartlettCoordinateMeasure n q m)
  have hleft : (fun i => blockBartlettCoordinateMeasure n q m (.inl i)) =
      bartlettCoordinateMeasure (p := q) n := rfl
  have hright : (fun i => blockBartlettCoordinateMeasure n q m (.inr i)) = μinner := by
    funext i
    cases i <;> rfl
  rw [hleft, hright] at houter
  have hprod := (MeasurePreserving.id
    (Measure.pi (bartlettCoordinateMeasure (p := q) n))).prod hinner
  have h := (houter.comp hprod).map_eq
  change Measure.map
    (⇑(MeasurableEquiv.sumPiEquivProdPi
        (fun _ : BlockLowerIndex q m => ℝ)).symm ∘
      Prod.map id (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : (Fin m × Fin q) ⊕ LowerIndex m => ℝ)).symm)
    (bartlettBlockDataMeasure n q m) = _ at h
  have hfun :
      ⇑(MeasurableEquiv.sumPiEquivProdPi
        (fun _ : BlockLowerIndex q m => ℝ)).symm ∘
      Prod.map id (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : (Fin m × Fin q) ⊕ LowerIndex m => ℝ)).symm =
      packBartlettBlockData q m := by
    funext x ij
    rcases ij with ij | (ij | ij) <;> rfl
  rw [hfun] at h
  exact h

theorem nonsingularWishartMeasure_one_eq_map_bartlettBlockData
    {n : ℝ} {q m : ℕ} (hn : ((q + m : ℕ) : ℝ) - 1 < n) :
    nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) =
      (bartlettBlockDataMeasure n q m).map
        (lowerTriangleGram (q + m) ∘ assembleBlockLowerCoordinates q m ∘
          packBartlettBlockData q m) := by
  rw [nonsingularWishartMeasure_one_eq_map_blockBartlett hn,
    ← map_packBartlettBlockData n q m,
    Measure.map_map
      ((measurable_lowerTriangleGram (q + m)).comp
        (measurable_assembleBlockLowerCoordinates q m))
      (measurable_packBartlettBlockData q m)]
  rw [Function.comp_assoc]

/-- Independently mapping the selected and residual Bartlett groups to their
Gram matrices gives the product of Wishart( n, I_q ), rectangular standard
Gaussian, and Wishart( n-q, I_m ) laws. -/
theorem measurePreserving_bartlettBlockData_gram
    {n : ℝ} {q m : ℕ} (hn : ((q + m : ℕ) : ℝ) - 1 < n) :
    MeasurePreserving
      (fun x : BartlettBlockData q m =>
        (lowerTriangleGram q x.1, (x.2.1, lowerTriangleGram m x.2.2)))
      (bartlettBlockDataMeasure n q m)
      ((nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ)).prod
        ((Measure.pi (fun _ : Fin m × Fin q => gaussianReal 0 1)).prod
          (nonsingularWishartMeasure (n - q) (1 : Matrix (Fin m) (Fin m) ℝ)))) := by
  have hnq : (q : ℝ) - 1 < n := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hn
    linarith
  have hnm : (m : ℝ) - 1 < n - q := by
    push_cast at hn
    linarith
  have hleft : MeasurePreserving (lowerTriangleGram q)
      (Measure.pi (bartlettCoordinateMeasure (p := q) n))
      (nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ)) :=
    ⟨measurable_lowerTriangleGram q,
      (nonsingularWishartMeasure_one_eq_map_lowerTriangleGram hnq).symm⟩
  have hright : MeasurePreserving (lowerTriangleGram m)
      (Measure.pi (bartlettCoordinateMeasure (p := m) (n - q)))
      (nonsingularWishartMeasure (n - q) (1 : Matrix (Fin m) (Fin m) ℝ)) :=
    ⟨measurable_lowerTriangleGram m,
      (nonsingularWishartMeasure_one_eq_map_lowerTriangleGram hnm).symm⟩
  exact hleft.prod ((MeasurePreserving.id _).prod hright)

def selectedBartlettMatrix {q m : ℕ} (x : BlockLowerIndex q m → ℝ) :
    Matrix (Fin q) (Fin q) ℝ :=
  lowerTriangleMatrix q (fun ij => x (.inl ij))

def rectangularBartlettMatrix {q m : ℕ} (x : BlockLowerIndex q m → ℝ) :
    Matrix (Fin m) (Fin q) ℝ :=
  Matrix.of fun i j => x (.inr (.inl (i, j)))

def residualBartlettMatrix {q m : ℕ} (x : BlockLowerIndex q m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  lowerTriangleMatrix m (fun ij => x (.inr (.inr ij)))

theorem lowerTriangleMatrix_assemble_submatrix {q m : ℕ}
    (x : BlockLowerIndex q m → ℝ) :
    (lowerTriangleMatrix (q + m) (assembleBlockLowerCoordinates q m x)).submatrix
        finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (selectedBartlettMatrix x) 0
        (rectangularBartlettMatrix x) (residualBartlettMatrix x) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_left,
      Matrix.fromBlocks_apply₁₁, selectedBartlettMatrix]
    by_cases hij : j ≤ i
    · have hij' : Fin.castAdd m j ≤ Fin.castAdd m i := hij
      rw [lowerTriangleMatrix_apply_of_le _ hij',
        lowerTriangleMatrix_apply_of_le _ hij]
      exact assembleBlockLowerCoordinates_apply q m x (.inl ⟨(i, j), hij⟩)
    · have hij' : Fin.castAdd m i < Fin.castAdd m j := not_le.1 hij
      rw [lowerTriangleMatrix_apply_of_lt _ hij',
        lowerTriangleMatrix_apply_of_lt _ (not_le.1 hij)]
  · simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
    apply lowerTriangleMatrix_apply_of_lt
    change i.val < q + j.val
    omega
  · simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₂₁, rectangularBartlettMatrix,
      Matrix.of_apply]
    have hij : Fin.castAdd m j ≤ Fin.natAdd q i := by
      change j.val ≤ q + i.val
      omega
    rw [lowerTriangleMatrix_apply_of_le _ hij]
    exact assembleBlockLowerCoordinates_apply q m x (.inr (.inl (i, j)))
  · simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_right,
      Matrix.fromBlocks_apply₂₂, residualBartlettMatrix]
    by_cases hij : j ≤ i
    · have hij' : Fin.natAdd q j ≤ Fin.natAdd q i := Nat.add_le_add_left hij q
      rw [lowerTriangleMatrix_apply_of_le _ hij', lowerTriangleMatrix_apply_of_le _ hij]
      exact assembleBlockLowerCoordinates_apply q m x (.inr (.inr ⟨(i, j), hij⟩))
    · have hij' : Fin.natAdd q i < Fin.natAdd q j := Nat.add_lt_add_left (not_le.1 hij) q
      rw [lowerTriangleMatrix_apply_of_lt _ hij',
        lowerTriangleMatrix_apply_of_lt _ (not_le.1 hij)]

/-- The algebraic regression identity read from the Bartlett coordinates:
the Schur complement is the independent reduced-degree Wishart block. -/
theorem blockBartlett_gram_identity {q m : ℕ} (x : BlockLowerIndex q m → ℝ) :
    ((lowerTriangleGram (q + m) (assembleBlockLowerCoordinates q m x) :
        Matrix (Fin (q + m)) (Fin (q + m)) ℝ)).submatrix
        finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks
        (selectedBartlettMatrix x * (selectedBartlettMatrix x)ᵀ)
        (selectedBartlettMatrix x * (rectangularBartlettMatrix x)ᵀ)
        (rectangularBartlettMatrix x * (selectedBartlettMatrix x)ᵀ)
        (rectangularBartlettMatrix x * (rectangularBartlettMatrix x)ᵀ +
          residualBartlettMatrix x * (residualBartlettMatrix x)ᵀ) := by
  rw [coe_lowerTriangleGram,
    ← Matrix.submatrix_mul_equiv _ _ finSumFinEquiv finSumFinEquiv finSumFinEquiv,
    ← Matrix.transpose_submatrix, lowerTriangleMatrix_assemble_submatrix,
    Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  simp

end Wishart
end
end CanonicalSource1

section CanonicalSource2
/- Source: Wishart/GaussianRotations.lean -/



/-!
# Orthogonal rotations of the independent Gaussian block

These lemmas keep the selected Bartlett coordinates independent of the rotated
Gaussian noise.  The rotation may depend measurably on the selected block;
`MeasurePreserving.skew_product` handles precisely that dependence.
-/

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker

noncomputable section

namespace Wishart

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The positive functional-calculus square root of a real matrix is symmetric,
including the totalized value outside the positive cone. -/
@[simp] theorem matrix_sqrt_transpose (S : Matrix ι ι ℝ) :
    (CFC.sqrt S)ᵀ = CFC.sqrt S := by
  have hh := (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg S)).isHermitian.eq
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hh

/-- Orthogonal matrix multiplication preserves the concrete product of
independent real standard normal coordinate laws. -/
theorem map_piGaussian_mulVec (U : Matrix ι ι ℝ) (hU : U * Uᵀ = 1) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).map U.mulVec =
      Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  apply (MeasurableEquiv.toLp 2 (ι → ℝ)).map_measurableEquiv_injective
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have h := map_affine_multivariateGaussian (0 : EuclideanSpace ℝ ι)
    Matrix.PosSemidef.one U 0
  simp only [add_zero, map_zero, Matrix.mul_one, hU] at h
  simp only [multivariateGaussian_one_eq_map_pi, PiLp.zero_apply] at h
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at h
  exact h

def rectangularRotation {q m : ℕ} (U : Matrix (Fin q) (Fin q) ℝ)
    (g : Fin m × Fin q → ℝ) : Fin m × Fin q → ℝ :=
  fun ij => ∑ k : Fin q, U ij.2 k * g (ij.1, k)

@[fun_prop] theorem measurable_rectangularRotation {q m : ℕ} :
    Measurable (fun p : Matrix (Fin q) (Fin q) ℝ × (Fin m × Fin q → ℝ) =>
      rectangularRotation p.1 p.2) := by
  unfold rectangularRotation
  fun_prop

theorem rectangularRotation_eq_kronecker_mulVec {q m : ℕ}
    (U : Matrix (Fin q) (Fin q) ℝ) :
    rectangularRotation (m := m) U =
      ((1 : Matrix (Fin m) (Fin m) ℝ) ⊗ₖ U).mulVec := by
  funext g
  ext ij
  simp [rectangularRotation, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply]

theorem map_rectangularRotation_piGaussian {q m : ℕ}
    (U : Matrix (Fin q) (Fin q) ℝ) (hU : U * Uᵀ = 1) :
    (Measure.pi (fun _ : Fin m × Fin q => gaussianReal 0 1)).map
        (rectangularRotation U) =
      Measure.pi (fun _ : Fin m × Fin q => gaussianReal 0 1) := by
  rw [rectangularRotation_eq_kronecker_mulVec]
  apply map_piGaussian_mulVec
  rw [← Matrix.kroneckerMap_transpose, Matrix.transpose_one,
    ← Matrix.mul_kronecker_mul, Matrix.mul_one, hU, Matrix.one_kronecker_one]

/-- The rectangular action is right multiplication by the transpose. -/
theorem rectangularRotation_matrix {q m : ℕ}
    (U : Matrix (Fin q) (Fin q) ℝ) (g : Fin m × Fin q → ℝ) :
    Matrix.of (fun i j => rectangularRotation U g (i, j)) =
      Matrix.of (fun i j => g (i, j)) * Uᵀ := by
  ext i j
  simp only [rectangularRotation, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

/-- A measurable orthogonal rotation depending on an independent parameter
preserves their entire joint product law. -/
theorem measurePreserving_parameterizedGaussianRotation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    (U : Ω → Matrix ι ι ℝ) (hUmeas : Measurable U)
    (hU : ∀ᵐ s ∂μ, U s * (U s)ᵀ = 1) :
    MeasurePreserving (fun p : Ω × (ι → ℝ) => (p.1, (U p.1).mulVec p.2))
      (μ.prod (Measure.pi (fun _ : ι => gaussianReal 0 1)))
      (μ.prod (Measure.pi (fun _ : ι => gaussianReal 0 1))) := by
  refine (MeasurePreserving.id μ).skew_product
    (μc := Measure.pi (fun _ : ι => gaussianReal 0 1))
    (μd := Measure.pi (fun _ : ι => gaussianReal 0 1))
    (g := fun s z => (U s).mulVec z) ?_ ?_
  · fun_prop
  · filter_upwards [hU] with s hs
    exact map_piGaussian_mulVec (U s) hs

/-- The orthogonal factor in `L = sqrt(L Lᵀ) * O` on the invertible locus. -/
def leftPolarFactor (L : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (CFC.sqrt (L * Lᵀ))⁻¹ * L

@[fun_prop] theorem measurable_leftPolarFactor :
    Measurable (leftPolarFactor : Matrix ι ι ℝ → Matrix ι ι ℝ) := by
  unfold leftPolarFactor
  have hgram : Measurable (fun L : Matrix ι ι ℝ => L * Lᵀ) :=
    (continuous_id.matrix_mul continuous_id.matrix_transpose).measurable
  exact (measurable_matrix_inv.comp (CFC.measurable_sqrt.comp hgram)).mul measurable_id

theorem leftPolarFactor_properties (L : Matrix ι ι ℝ) (hL : L.det ≠ 0) :
    leftPolarFactor L * (leftPolarFactor L)ᵀ = 1 ∧
      CFC.sqrt (L * Lᵀ) * leftPolarFactor L = L := by
  let R := CFC.sqrt (L * Lᵀ)
  have hS : (L * Lᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose L
  have hsq : R * R = L * Lᵀ := CFC.sqrt_mul_sqrt_self _ hS.nonneg
  have hRtr : Rᵀ = R := by
    have hh := (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg (L * Lᵀ))).isHermitian.eq
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hh
  have hRdet : R.det ≠ 0 := by
    intro hzero
    have hh := congrArg Matrix.det hsq
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hzero, zero_mul] at hh
    exact hL (mul_self_eq_zero.mp hh.symm)
  have hRu : IsUnit R.det := isUnit_iff_ne_zero.mpr hRdet
  constructor
  · change (R⁻¹ * L) * (R⁻¹ * L)ᵀ = 1
    rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hRtr]
    calc
      R⁻¹ * L * (Lᵀ * R⁻¹) = R⁻¹ * (L * Lᵀ) * R⁻¹ := by
        simp only [Matrix.mul_assoc]
      _ = R⁻¹ * (R * R) * R⁻¹ := by rw [hsq]
      _ = 1 := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hRu,
          Matrix.one_mul, Matrix.mul_nonsing_inv _ hRu]
  · change R * (R⁻¹ * L) = L
    exact Matrix.mul_nonsing_inv_cancel_left R L hRu

/-- A full block Gram matrix with a fixed symmetric residual block.  This
unbundled algebraic form is used both before and after rotating the noise. -/
def regressionBlockMatrix {q m : ℕ}
    (R : Matrix (Fin q) (Fin q) ℝ) (G : Matrix (Fin m) (Fin q) ℝ)
    (W : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin q ⊕ Fin m) (Fin q ⊕ Fin m) ℝ :=
  Matrix.fromBlocks (R * Rᵀ) (R * Gᵀ) (G * Rᵀ) (G * Gᵀ + W)

theorem regressionBlockMatrix_isHermitian {q m : ℕ}
    (R : Matrix (Fin q) (Fin q) ℝ) (G : Matrix (Fin m) (Fin q) ℝ)
    {W : Matrix (Fin m) (Fin m) ℝ} (hW : W.IsHermitian) :
    (regressionBlockMatrix R G W).IsHermitian := by
  apply Matrix.IsHermitian.fromBlocks
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_mul_conjTranspose_self R
  · simp only [Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_mul, Matrix.transpose_transpose]
  · apply Matrix.IsHermitian.add _ hW
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_mul_conjTranspose_self G

@[fun_prop] theorem measurable_regressionBlockMatrix {q m : ℕ} :
    Measurable (fun p : Matrix (Fin q) (Fin q) ℝ ×
        (Matrix (Fin m) (Fin q) ℝ × Matrix (Fin m) (Fin m) ℝ) =>
      regressionBlockMatrix p.1 p.2.1 p.2.2) := by
  apply Matrix.measurable_iff.mpr
  intro i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [regressionBlockMatrix, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂] <;>
    fun_prop

/-- Rotating the selected factor and the independent Gaussian rows in opposite
directions leaves the entire regression matrix unchanged. -/
theorem regressionBlockMatrix_rotation {q m : ℕ}
    (R L U : Matrix (Fin q) (Fin q) ℝ)
    (G : Matrix (Fin m) (Fin q) ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (hU : U * Uᵀ = 1) (hL : R * U = L) :
    regressionBlockMatrix R (G * Uᵀ) W = regressionBlockMatrix L G W := by
  have hUU : Uᵀ * U = 1 := mul_eq_one_comm.mp hU
  have htop : R * Rᵀ = L * Lᵀ := by
    rw [← hL, Matrix.transpose_mul]
    calc
      R * Rᵀ = R * (U * Uᵀ) * Rᵀ := by rw [hU, Matrix.mul_one]
      _ = R * U * (Uᵀ * Rᵀ) := by simp only [Matrix.mul_assoc]
  have hcross : R * (G * Uᵀ)ᵀ = L * Gᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc, hL]
  have hcross' : (G * Uᵀ) * Rᵀ = G * Lᵀ := by
    rw [← hL, Matrix.transpose_mul, Matrix.mul_assoc]
  have hbottom : (G * Uᵀ) * (G * Uᵀ)ᵀ = G * Gᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      G * Uᵀ * (U * Gᵀ) = G * (Uᵀ * U) * Gᵀ := by
        simp only [Matrix.mul_assoc]
      _ = G * Gᵀ := by rw [hUU, Matrix.mul_one]
  simp only [regressionBlockMatrix, htop, hcross, hcross', hbottom]

/-- Invertible Bartlett factors may be replaced by their symmetric positive
square root while rotating only the Gaussian noise. -/
theorem regressionBlockMatrix_leftPolarFactor {q m : ℕ}
    (L : Matrix (Fin q) (Fin q) ℝ) (G : Matrix (Fin m) (Fin q) ℝ)
    (W : Matrix (Fin m) (Fin m) ℝ) (hL : L.det ≠ 0) :
    regressionBlockMatrix (CFC.sqrt (L * Lᵀ)) (G * (leftPolarFactor L)ᵀ) W =
      regressionBlockMatrix L G W :=
  regressionBlockMatrix_rotation _ _ _ _ _
    (leftPolarFactor_properties L hL).1 (leftPolarFactor_properties L hL).2

/-- Reading a rectangular array by its columns gives independent standard
Gaussian coordinate vectors. -/
theorem measurePreserving_rectangularGaussian_columns {q m : ℕ} :
    MeasurePreserving
      (fun g : Fin m × Fin q → ℝ => fun j : Fin q => fun i : Fin m => g (i, j))
      (Measure.pi (fun _ : Fin m × Fin q => gaussianReal 0 1))
      (Measure.pi (fun _ : Fin q =>
        Measure.pi (fun _ : Fin m => gaussianReal 0 1))) := by
  let e : (Fin m × Fin q) ≃ ((j : Fin q) × Fin m) :=
    { toFun := fun ij => ⟨ij.2, ij.1⟩
      invFun := fun ji => (ji.2, ji.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hperm := measurePreserving_piCongrLeft
    (fun _ : (j : Fin q) × Fin m => gaussianReal 0 1) e
  have hcurry := TauCeti.measurePreserving_piCurry
    (fun (_ : Fin q) (_ : Fin m) => gaussianReal 0 1)
  exact hcurry.comp hperm

def gaussianRowsWithFactor {q m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ)
    (g : Fin m × Fin q → ℝ) : Fin q → EuclideanSpace ℝ (Fin m) :=
  fun j => R.toEuclideanLin (WithLp.toLp 2 (fun i => g (i, j)))

theorem gaussianRowsWithFactor_matrix {q m : ℕ}
    (R : Matrix (Fin m) (Fin m) ℝ) (g : Fin m × Fin q → ℝ) :
    Matrix.of (fun i j => gaussianRowsWithFactor R g j i) =
      R * Matrix.of (fun i j => g (i, j)) := by
  ext i j
  simp [gaussianRowsWithFactor, Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- The transformed rectangular Gaussian coordinates have exactly the product
of q independent Gaussian laws with covariance R Rᵀ. -/
theorem measurePreserving_gaussianRowsWithFactor {q m : ℕ}
    (R : Matrix (Fin m) (Fin m) ℝ) :
    MeasurePreserving (gaussianRowsWithFactor (q := q) R)
      (Measure.pi (fun _ : Fin m × Fin q => gaussianReal 0 1))
      (Measure.pi (fun _ : Fin q =>
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (R * Rᵀ))) := by
  have hstd : MeasurePreserving (WithLp.toLp 2 : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m))
      (Measure.pi (fun _ : Fin m => gaussianReal 0 1))
      (multivariateGaussian 0 (1 : Matrix (Fin m) (Fin m) ℝ)) := by
    refine ⟨by fun_prop, ?_⟩
    simpa only [PiLp.zero_apply] using
      (multivariateGaussian_one_eq_map_pi (0 : EuclideanSpace ℝ (Fin m))).symm
  have hR : MeasurePreserving R.toEuclideanLin
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
        (1 : Matrix (Fin m) (Fin m) ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (R * Rᵀ)) := by
    refine ⟨by fun_prop, ?_⟩
    simpa only [add_zero, map_zero, Matrix.mul_one] using
      map_affine_multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
        Matrix.PosSemidef.one R 0
  have hrows := measurePreserving_pi
    (fun _ : Fin q => Measure.pi (fun _ : Fin m => gaussianReal 0 1))
    (fun _ : Fin q => multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (R * Rᵀ))
    (fun _ => hR.comp hstd)
  exact hrows.comp measurePreserving_rectangularGaussian_columns

end Wishart
end
end CanonicalSource2

section CanonicalSource3
/- Source: Wishart/BlockRegression.lean -/



/-!
# The standard real-shape Wishart block regression law

This is an equality of concrete probability measures, not a conditional-law
axiom.  Its proof starts from the verified Bartlett density formula, rotates the
independent rectangular Gaussian coordinates by a measurable orthogonal polar
factor, and pushes the independent Bartlett groups to their Wishart Gram laws.
-/

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Wishart

abbrev SymmetricMatrix (p : ℕ) :=
  selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)

abbrev StandardRegressionData (q m : ℕ) :=
  SymmetricMatrix q × ((Fin m × Fin q → ℝ) × SymmetricMatrix m)

def standardRegressionMeasure (n : ℝ) (q m : ℕ) :
    Measure (StandardRegressionData q m) :=
  (nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ)).prod
    ((Measure.pi (fun _ : Fin m × Fin q => gaussianReal 0 1)).prod
      (nonsingularWishartMeasure (n - q) (1 : Matrix (Fin m) (Fin m) ℝ)))

def standardRegressionGram {q m : ℕ} (x : StandardRegressionData q m) :
    SymmetricMatrix (q + m) :=
  ⟨(regressionBlockMatrix (CFC.sqrt (x.1 : Matrix (Fin q) (Fin q) ℝ))
      (Matrix.of fun i j => x.2.1 (i, j)) (x.2.2 : Matrix (Fin m) (Fin m) ℝ)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm,
    Matrix.isHermitian_iff_isSelfAdjoint.mp
      ((regressionBlockMatrix_isHermitian _ _
        (Matrix.isHermitian_iff_isSelfAdjoint.mpr x.2.2.property)).submatrix
          finSumFinEquiv.symm)⟩

@[simp] theorem standardRegressionGram_submatrix {q m : ℕ}
    (x : StandardRegressionData q m) :
    ((standardRegressionGram x : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)).submatrix
        finSumFinEquiv finSumFinEquiv =
      regressionBlockMatrix (CFC.sqrt (x.1 : Matrix (Fin q) (Fin q) ℝ))
        (Matrix.of fun i j => x.2.1 (i, j)) (x.2.2 : Matrix (Fin m) (Fin m) ℝ) := by
  ext i j
  simp [standardRegressionGram, Matrix.submatrix_apply]

@[fun_prop] theorem measurable_standardRegressionGram {q m : ℕ} :
    Measurable (standardRegressionGram (q := q) (m := m)) := by
  have hR : Measurable (fun x : StandardRegressionData q m =>
      CFC.sqrt (x.1 : Matrix (Fin q) (Fin q) ℝ)) := by
    fun_prop
  have hG : Measurable (fun x : StandardRegressionData q m =>
      Matrix.of (fun i j => x.2.1 (i, j))) := by
    apply Matrix.measurable_iff.mpr
    intro i j
    simp only [Matrix.of_apply]
    fun_prop
  have hW : Measurable (fun x : StandardRegressionData q m =>
      (x.2.2 : Matrix (Fin m) (Fin m) ℝ)) := by
    fun_prop
  have hM := measurable_regressionBlockMatrix.comp (hR.prodMk (hG.prodMk hW))
  apply Measurable.subtype_mk
  apply Matrix.measurable_iff.mpr
  intro i j
  exact hM.eval_matrix

def bartlettBlockDataGram {q m : ℕ} (x : BartlettBlockData q m) :
    StandardRegressionData q m :=
  (lowerTriangleGram q x.1, (x.2.1, lowerTriangleGram m x.2.2))

@[fun_prop] theorem measurable_bartlettBlockDataGram {q m : ℕ} :
    Measurable (bartlettBlockDataGram (q := q) (m := m)) := by
  unfold bartlettBlockDataGram
  fun_prop

def rotateBartlettBlockData {q m : ℕ} (x : BartlettBlockData q m) :
    BartlettBlockData q m :=
  (x.1,
    (rectangularRotation (leftPolarFactor (lowerTriangleMatrix q x.1)) x.2.1, x.2.2))

@[fun_prop] theorem measurable_rotateBartlettBlockData {q m : ℕ} :
    Measurable (rotateBartlettBlockData (q := q) (m := m)) := by
  unfold rotateBartlettBlockData
  have hL : Measurable (fun x : BartlettBlockData q m => lowerTriangleMatrix q x.1) :=
    (continuous_lowerTriangleMatrix.comp continuous_fst).measurable
  have hU := measurable_leftPolarFactor.comp hL
  have hrot := measurable_rectangularRotation.comp
    (hU.prodMk (measurable_fst.comp measurable_snd))
  exact measurable_fst.prodMk (hrot.prodMk (measurable_snd.comp measurable_snd))

theorem ae_det_lowerTriangleMatrix_ne_zero {n : ℝ} {q : ℕ}
    (hn : (q : ℝ) - 1 < n) :
    ∀ᵐ a ∂Measure.pi (bartlettCoordinateMeasure (p := q) n),
      (lowerTriangleMatrix q a).det ≠ 0 := by
  have hae : ∀ᵐ a ∂Measure.pi (bartlettCoordinateMeasure (p := q) n),
      a ∈ posDiagLowerRegion q := by
    rw [ae_iff]
    exact pi_bartlettCoordinateMeasure_compl_posDiagLowerRegion hn
  filter_upwards [hae] with a ha
  rw [det_lowerTriangleMatrix]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact ((mem_posDiagLowerRegion q).mp ha i).ne'

theorem measurePreserving_rotateBartlettBlockData
    {n : ℝ} {q m : ℕ} (hn : (q : ℝ) - 1 < n) :
    MeasurePreserving (rotateBartlettBlockData (q := q) (m := m))
      (bartlettBlockDataMeasure n q m) (bartlettBlockDataMeasure n q m) := by
  let μa := Measure.pi (bartlettCoordinateMeasure (p := q) n)
  let μg := Measure.pi (fun _ : Fin m × Fin q => gaussianReal 0 1)
  let μb := Measure.pi (bartlettCoordinateMeasure (p := m) (n - q))
  change MeasurePreserving
    (fun x : BartlettBlockData q m =>
      (id x.1, (rectangularRotation (leftPolarFactor (lowerTriangleMatrix q x.1))
        x.2.1, x.2.2))) (μa.prod (μg.prod μb)) (μa.prod (μg.prod μb))
  refine (MeasurePreserving.id μa).skew_product
    (μc := μg.prod μb) (μd := μg.prod μb)
    (g := fun a z =>
      (rectangularRotation (leftPolarFactor (lowerTriangleMatrix q a)) z.1, z.2)) ?_ ?_
  · exact measurable_snd.comp measurable_rotateBartlettBlockData
  · filter_upwards [ae_det_lowerTriangleMatrix_ne_zero hn] with a ha
    have horth := (leftPolarFactor_properties (lowerTriangleMatrix q a) ha).1
    have hrot : MeasurePreserving
        (rectangularRotation (m := m) (leftPolarFactor (lowerTriangleMatrix q a))) μg μg :=
      ⟨by fun_prop, map_rectangularRotation_piGaussian _ horth⟩
    exact (hrot.prod (MeasurePreserving.id μb)).map_eq

theorem standardRegressionGram_rotateBartlettBlockData
    {q m : ℕ} (x : BartlettBlockData q m)
    (hL : (lowerTriangleMatrix q x.1).det ≠ 0) :
    standardRegressionGram (bartlettBlockDataGram (rotateBartlettBlockData x)) =
      lowerTriangleGram (q + m)
        (assembleBlockLowerCoordinates q m (packBartlettBlockData q m x)) := by
  apply Subtype.ext
  have h₁ := standardRegressionGram_submatrix
    (bartlettBlockDataGram (rotateBartlettBlockData x))
  have h₂ := blockBartlett_gram_identity (packBartlettBlockData q m x)
  have hrot := regressionBlockMatrix_leftPolarFactor
    (lowerTriangleMatrix q x.1) (Matrix.of fun i j => x.2.1 (i, j))
    (lowerTriangleMatrix m x.2.2 * (lowerTriangleMatrix m x.2.2)ᵀ) hL
  have hmid :
      regressionBlockMatrix
        (CFC.sqrt ((lowerTriangleGram q x.1 : SymmetricMatrix q) :
          Matrix (Fin q) (Fin q) ℝ))
        (Matrix.of fun i j => rectangularRotation (leftPolarFactor (lowerTriangleMatrix q x.1))
          x.2.1 (i, j))
        (lowerTriangleGram m x.2.2 : Matrix (Fin m) (Fin m) ℝ) =
      regressionBlockMatrix (lowerTriangleMatrix q x.1)
        (Matrix.of fun i j => x.2.1 (i, j))
        (lowerTriangleMatrix m x.2.2 * (lowerTriangleMatrix m x.2.2)ᵀ) := by
    rw [rectangularRotation_matrix, coe_lowerTriangleGram, coe_lowerTriangleGram]
    exact hrot
  have hblocks :
      ((standardRegressionGram (bartlettBlockDataGram (rotateBartlettBlockData x)) :
          SymmetricMatrix (q + m)) : Matrix (Fin (q + m)) (Fin (q + m)) ℝ).submatrix
          finSumFinEquiv finSumFinEquiv =
        ((lowerTriangleGram (q + m)
          (assembleBlockLowerCoordinates q m (packBartlettBlockData q m x)) :
            SymmetricMatrix (q + m)) : Matrix (Fin (q + m)) (Fin (q + m)) ℝ).submatrix
              finSumFinEquiv finSumFinEquiv := by
    rw [h₁, h₂]
    exact hmid
  ext i j
  simpa only [Matrix.submatrix_apply, Equiv.apply_symm_apply] using congrArg
    (fun A : Matrix (Fin q ⊕ Fin m) (Fin q ⊕ Fin m) ℝ =>
      A (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) hblocks

/-- **Standard real-shape block regression.** Independently take
`S ~ W_q(n,I)`, a rectangular matrix of standard normals, and
`W ~ W_m(n-q,I)`.  Their symmetric-square-root regression reconstruction has
the full nonsingular `W_(q+m)(n,I)` law, for every real `n > q+m-1`. -/
theorem map_standardRegressionGram
    {n : ℝ} {q m : ℕ} (hn : ((q + m : ℕ) : ℝ) - 1 < n) :
    (standardRegressionMeasure n q m).map standardRegressionGram =
      nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) := by
  have hnq : (q : ℝ) - 1 < n := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hn
    linarith
  have hrot := measurePreserving_rotateBartlettBlockData (m := m) hnq
  have hgram := measurePreserving_bartlettBlockData_gram hn
  have hpush :
      (bartlettBlockDataMeasure n q m).map
        (bartlettBlockDataGram ∘ rotateBartlettBlockData) =
        standardRegressionMeasure n q m := (hgram.comp hrot).map_eq
  rw [← hpush,
    Measure.map_map measurable_standardRegressionGram
      (measurable_bartlettBlockDataGram.comp measurable_rotateBartlettBlockData)]
  rw [nonsingularWishartMeasure_one_eq_map_bartlettBlockData hn]
  apply Measure.map_congr
  have hae : ∀ᵐ x ∂bartlettBlockDataMeasure n q m,
      (lowerTriangleMatrix q x.1).det ≠ 0 :=
    (Measure.quasiMeasurePreserving_fst).ae (ae_det_lowerTriangleMatrix_ne_zero hnq)
  filter_upwards [hae] with x hx
  exact standardRegressionGram_rotateBartlettBlockData x hx

/-- The lower block-triangular factor which introduces the regression mean K
and residual covariance factor R. -/
def regressionCovarianceFactor {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (R : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin (q + m)) (Fin (q + m)) ℝ :=
  (Matrix.fromBlocks (1 : Matrix (Fin q) (Fin q) ℝ) 0 Kᵀ R).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm

/-- The covariance block matrix appearing in the paper's regression lemma. -/
def regressionScale {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (C : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin (q + m)) (Fin (q + m)) ℝ :=
  (Matrix.fromBlocks (1 : Matrix (Fin q) (Fin q) ℝ) K Kᵀ (Kᵀ * K + C)).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm

@[simp] theorem regressionCovarianceFactor_submatrix {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (R : Matrix (Fin m) (Fin m) ℝ) :
    (regressionCovarianceFactor K R).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (1 : Matrix (Fin q) (Fin q) ℝ) 0 Kᵀ R := by
  ext i j
  simp [regressionCovarianceFactor, Matrix.submatrix_apply]

@[simp] theorem det_regressionCovarianceFactor {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (R : Matrix (Fin m) (Fin m) ℝ) :
    (regressionCovarianceFactor K R).det = R.det := by
  simp [regressionCovarianceFactor]

theorem regressionCovarianceFactor_mul_transpose {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (R : Matrix (Fin m) (Fin m) ℝ) :
    regressionCovarianceFactor K R * (regressionCovarianceFactor K R)ᵀ =
      regressionScale K (R * Rᵀ) := by
  simp only [regressionCovarianceFactor, regressionScale, Matrix.transpose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_transpose,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul,
    zero_add, add_zero]

/-- The block covariance in the regression lemma is positive definite when its
Schur complement C is positive definite. -/
theorem regressionScale_posDef {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) {C : Matrix (Fin m) (Fin m) ℝ}
    (hC : C.PosDef) : (regressionScale K C).PosDef := by
  have hsquare : CFC.sqrt C * CFC.sqrt C = C :=
    CFC.sqrt_mul_sqrt_self _ hC.posSemidef.nonneg
  have hrootdet : (CFC.sqrt C).det ≠ 0 := by
    intro hz
    have hd := congrArg Matrix.det hsquare
    rw [Matrix.det_mul, hz, zero_mul] at hd
    exact hC.det_pos.ne' hd.symm
  let T := regressionCovarianceFactor K (CFC.sqrt C)
  have hT : T.det ≠ 0 := by simpa only [T, det_regressionCovarianceFactor] using hrootdet
  have hgram : (T * Tᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose T
  have hPD : (T * Tᵀ).PosDef := hgram.posDef_iff_det_ne_zero.mpr (by
    rw [Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero hT hT)
  simpa only [T, regressionCovarianceFactor_mul_transpose,
    matrix_sqrt_transpose, hsquare] using hPD

/-- The entire regression matrix, including all cross blocks, transforms by
the same fixed block congruence. -/
theorem regressionBlockMatrix_congruence {q m : ℕ}
    (A : Matrix (Fin q) (Fin q) ℝ) (G : Matrix (Fin m) (Fin q) ℝ)
    (W : Matrix (Fin m) (Fin m) ℝ)
    (K : Matrix (Fin q) (Fin m) ℝ) (R : Matrix (Fin m) (Fin m) ℝ) :
    Matrix.fromBlocks (1 : Matrix (Fin q) (Fin q) ℝ) 0 Kᵀ R *
        regressionBlockMatrix A G W *
        (Matrix.fromBlocks (1 : Matrix (Fin q) (Fin q) ℝ) 0 Kᵀ R)ᵀ =
      regressionBlockMatrix A (Kᵀ * A + R * G) (R * W * Rᵀ) := by
  simp only [regressionBlockMatrix, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.transpose_one, Matrix.transpose_zero,
    Matrix.transpose_transpose, Matrix.transpose_add, Matrix.transpose_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul,
    zero_add, add_zero, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_assoc]
  congr 1 <;> abel

/-- Regression with any invertible residual covariance factor, with all shapes
real.  The source variables remain the explicitly independent standard laws. -/
theorem map_congruence_standardRegressionGram
    {n : ℝ} {q m : ℕ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : R.det ≠ 0) :
    (standardRegressionMeasure n q m).map
        (Matrix.symmetricCongruenceLinearMap (regressionCovarianceFactor K R) ∘
          standardRegressionGram) =
      nonsingularWishartMeasure n (regressionScale K (R * Rᵀ)) := by
  rw [← Measure.map_map
    ((LinearMap.continuous_of_finiteDimensional _).measurable)
    measurable_standardRegressionGram,
    map_standardRegressionGram hn,
    map_symmetricCongruenceLinearMap_nonsingularWishartMeasure_of_det_ne_zero n 1
      (C := regressionCovarianceFactor K R) (by simpa using hR), Matrix.mul_one,
    regressionCovarianceFactor_mul_transpose]

/-- The covariance in the preceding construction is exactly
`[[I,K],[Kᵀ,KᵀK+C]]` when the residual factor is the positive square root of C. -/
theorem map_whitenedRegressionGram
    {n : ℝ} {q m : ℕ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ) {C : Matrix (Fin m) (Fin m) ℝ}
    (hC : C.PosDef) :
    (standardRegressionMeasure n q m).map
        (Matrix.symmetricCongruenceLinearMap
            (regressionCovarianceFactor K (CFC.sqrt C)) ∘ standardRegressionGram) =
      nonsingularWishartMeasure n (regressionScale K C) := by
  have hsquare : CFC.sqrt C * CFC.sqrt C = C :=
    CFC.sqrt_mul_sqrt_self _ hC.posSemidef.nonneg
  have htranspose : (CFC.sqrt C)ᵀ = CFC.sqrt C := by
    have hh := (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg C)).isHermitian.eq
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hh
  have hrootdet : (CFC.sqrt C).det ≠ 0 := by
    intro hz
    have hd := congrArg Matrix.det hsquare
    rw [Matrix.det_mul, hz, zero_mul] at hd
    exact hC.det_pos.ne' hd.symm
  simpa only [htranspose, hsquare] using
    map_congruence_standardRegressionGram hn K (CFC.sqrt C) hrootdet

end Wishart
end
end CanonicalSource3

section CanonicalSource4
/- Source: Wishart/RegressionLaw.lean -/



/-!
# The independent-variable form of the Wishart regression lemma

The source measure in the final theorem is the literal product of the selected
Wishart law, q independent Gaussian row laws with covariance C, and the
reduced-degree residual Wishart law with covariance C.  Thus the theorem records
both the joint law and the independence needed in the paper's Lemma 2.2.
-/

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Wishart

/-- The totalized nonsingular law is finite for every parameter: it is the
proved probability law on the admissible branch and the zero measure otherwise.
All principal theorems separately require the admissible branch. -/
instance isFiniteMeasure_nonsingularWishartMeasure {p : ℕ} (n : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) :
    IsFiniteMeasure (nonsingularWishartMeasure n S) := by
  classical
  by_cases hS : S.PosDef
  · by_cases hn : (p : ℝ) - 1 < n
    · letI := isProbabilityMeasure_nonsingularWishartMeasure hS hn
      infer_instance
    · rw [nonsingularWishartMeasure_of_le S (le_of_not_gt hn)]
      infer_instance
  · rw [nonsingularWishartMeasure_of_not_posDef n hS]
    infer_instance

abbrev RegressionData (q m : ℕ) :=
  SymmetricMatrix q × ((Fin q → EuclideanSpace ℝ (Fin m)) × SymmetricMatrix m)

def regressionDataMeasure (n : ℝ) (q m : ℕ)
    (C : Matrix (Fin m) (Fin m) ℝ) : Measure (RegressionData q m) :=
  (nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ)).prod
    ((Measure.pi (fun _ : Fin q =>
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) C)).prod
      (nonsingularWishartMeasure (n - q) C))

/-- At the stated regression parameters the source is a probability measure.
In particular, the main law identity does not rely on the zero-measure
totalization of an invalid Wishart parameter. -/
theorem isProbabilityMeasure_regressionDataMeasure
    {n : ℝ} {q m : ℕ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef) :
    IsProbabilityMeasure (regressionDataMeasure n q m C) := by
  have hnq : (q : ℝ) - 1 < n := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hn
    linarith
  have hnm : (m : ℝ) - 1 < n - q := by
    push_cast at hn
    linarith
  letI := isProbabilityMeasure_nonsingularWishartMeasure
    (S := (1 : Matrix (Fin q) (Fin q) ℝ)) Matrix.PosDef.one hnq
  letI := isProbabilityMeasure_nonsingularWishartMeasure hC hnm
  unfold regressionDataMeasure
  infer_instance

def regressionDataTransform {q m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ)
    (x : StandardRegressionData q m) : RegressionData q m :=
  (x.1, (gaussianRowsWithFactor R x.2.1,
    Matrix.symmetricCongruenceLinearMap R x.2.2))

@[fun_prop] theorem measurable_regressionDataTransform {q m : ℕ}
    (R : Matrix (Fin m) (Fin m) ℝ) :
    Measurable (regressionDataTransform (q := q) R) := by
  unfold regressionDataTransform gaussianRowsWithFactor
  fun_prop

/-- Change the covariance of both independent residual variables by the same
invertible factor.  The selected Wishart variable is preserved. -/
theorem measurePreserving_regressionDataTransform
    {n : ℝ} {q m : ℕ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.det ≠ 0) :
    MeasurePreserving (regressionDataTransform (q := q) R)
      (standardRegressionMeasure n q m)
      (regressionDataMeasure n q m (R * Rᵀ)) := by
  have hnq : (q : ℝ) - 1 < n := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hn
    linarith
  have hnm : (m : ℝ) - 1 < n - q := by
    push_cast at hn
    linarith
  letI := isProbabilityMeasure_nonsingularWishartMeasure
    (S := (1 : Matrix (Fin q) (Fin q) ℝ)) Matrix.PosDef.one hnq
  letI := isProbabilityMeasure_nonsingularWishartMeasure
    (S := (1 : Matrix (Fin m) (Fin m) ℝ)) Matrix.PosDef.one hnm
  have hW : MeasurePreserving (Matrix.symmetricCongruenceLinearMap R)
      (nonsingularWishartMeasure (n - q) (1 : Matrix (Fin m) (Fin m) ℝ))
      (nonsingularWishartMeasure (n - q) (R * Rᵀ)) := by
    refine ⟨(LinearMap.continuous_of_finiteDimensional _).measurable, ?_⟩
    simpa only [Matrix.mul_one] using
      map_symmetricCongruenceLinearMap_nonsingularWishartMeasure_of_det_ne_zero
        (n - q) 1 hR
  exact (MeasurePreserving.id _).prod
    ((measurePreserving_gaussianRowsWithFactor R).prod hW)

/-- Reconstruct the full block matrix from the selected block, Gaussian rows,
and the independent Schur-complement matrix.  The noise rows are indexed by the
selected rank q, and each row is an m-dimensional Gaussian vector. -/
def regressionReconstruction {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (x : RegressionData q m) :
    SymmetricMatrix (q + m) :=
  standardRegressionGram
    (x.1, ((fun ij =>
      (Kᵀ * CFC.sqrt (x.1 : Matrix (Fin q) (Fin q) ℝ)) ij.1 ij.2 +
        x.2.1 ij.2 ij.1), x.2.2))

@[fun_prop] theorem measurable_regressionReconstruction {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) :
    Measurable (regressionReconstruction K) := by
  unfold regressionReconstruction
  apply measurable_standardRegressionGram.comp
  fun_prop

theorem regressionReconstruction_submatrix {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (x : RegressionData q m) :
    ((regressionReconstruction K x : SymmetricMatrix (q + m)) :
        Matrix (Fin (q + m)) (Fin (q + m)) ℝ).submatrix
          finSumFinEquiv finSumFinEquiv =
      regressionBlockMatrix (CFC.sqrt (x.1 : Matrix (Fin q) (Fin q) ℝ))
        (Kᵀ * CFC.sqrt (x.1 : Matrix (Fin q) (Fin q) ℝ) +
          Matrix.of (fun i j => x.2.1 j i))
        (x.2.2 : Matrix (Fin m) (Fin m) ℝ) :=
  standardRegressionGram_submatrix _

/-- The selected principal block is exactly the independent selected Wishart
variable; no square-root reparameterization changes that variable. -/
theorem regressionReconstruction_selected {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (x : RegressionData q m)
    (hS : (x.1 : Matrix (Fin q) (Fin q) ℝ).PosSemidef) :
    ((regressionReconstruction K x : SymmetricMatrix (q + m)) :
        Matrix (Fin (q + m)) (Fin (q + m)) ℝ).submatrix
          (Fin.castAdd m) (Fin.castAdd m) =
      (x.1 : Matrix (Fin q) (Fin q) ℝ) := by
  have hsquare := CFC.sqrt_mul_sqrt_self
    (x.1 : Matrix (Fin q) (Fin q) ℝ) hS.nonneg
  ext i j
  have h := congrArg
    (fun A : Matrix (Fin q ⊕ Fin m) (Fin q ⊕ Fin m) ℝ =>
      A (.inl i) (.inl j)) (regressionReconstruction_submatrix K x)
  simpa only [Matrix.submatrix_apply, finSumFinEquiv_apply_left,
    regressionBlockMatrix, Matrix.fromBlocks_apply₁₁, matrix_sqrt_transpose,
    hsquare] using h

/-- The preceding selected-block identity holds almost surely under the exact
independent source law used in the regression theorem. -/
theorem ae_regressionReconstruction_selected
    (n : ℝ) {q m : ℕ} (K : Matrix (Fin q) (Fin m) ℝ)
    (C : Matrix (Fin m) (Fin m) ℝ) :
    ∀ᵐ x ∂regressionDataMeasure n q m C,
      ((regressionReconstruction K x : SymmetricMatrix (q + m)) :
          Matrix (Fin (q + m)) (Fin (q + m)) ℝ).submatrix
            (Fin.castAdd m) (Fin.castAdd m) =
        (x.1 : Matrix (Fin q) (Fin q) ℝ) := by
  have hae : ∀ᵐ x ∂regressionDataMeasure n q m C,
      (x.1 : Matrix (Fin q) (Fin q) ℝ).PosDef :=
    (Measure.quasiMeasurePreserving_fst).ae
      (ae_posDef_nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ))
  filter_upwards [hae] with x hx
  exact regressionReconstruction_selected K x hx.posSemidef

/-- The covariance change of the independent variables agrees pointwise with
the corresponding block congruence of the reconstructed full matrix. -/
theorem regressionReconstruction_transform {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (x : StandardRegressionData q m) :
    regressionReconstruction K (regressionDataTransform R x) =
      Matrix.symmetricCongruenceLinearMap (regressionCovarianceFactor K R)
        (standardRegressionGram x) := by
  apply Subtype.ext
  have hblocks :
      ((regressionReconstruction K (regressionDataTransform R x) :
          SymmetricMatrix (q + m)) : Matrix (Fin (q + m)) (Fin (q + m)) ℝ).submatrix
            finSumFinEquiv finSumFinEquiv =
        ((Matrix.symmetricCongruenceLinearMap (regressionCovarianceFactor K R)
          (standardRegressionGram x) : SymmetricMatrix (q + m)) :
            Matrix (Fin (q + m)) (Fin (q + m)) ℝ).submatrix
              finSumFinEquiv finSumFinEquiv := by
    rw [regressionReconstruction_submatrix,
      Matrix.coe_symmetricCongruenceLinearMap_apply,
      ← Matrix.submatrix_mul_equiv _ _ finSumFinEquiv finSumFinEquiv finSumFinEquiv,
      ← Matrix.submatrix_mul_equiv _ _ finSumFinEquiv finSumFinEquiv finSumFinEquiv,
      ← Matrix.transpose_submatrix, regressionCovarianceFactor_submatrix,
      standardRegressionGram_submatrix, regressionBlockMatrix_congruence]
    change regressionBlockMatrix _
      (_ + Matrix.of (fun i j => gaussianRowsWithFactor R x.2.1 j i))
      ((Matrix.symmetricCongruenceLinearMap R x.2.2 : SymmetricMatrix m) :
        Matrix (Fin m) (Fin m) ℝ) = _
    rw [gaussianRowsWithFactor_matrix, Matrix.coe_symmetricCongruenceLinearMap_apply]
    rfl
  ext i j
  simpa only [Matrix.submatrix_apply, Equiv.apply_symm_apply] using congrArg
    (fun A : Matrix (Fin q ⊕ Fin m) (Fin q ⊕ Fin m) ℝ =>
      A (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) hblocks

/-- **Wishart regression lemma, independent-variable form.** For every real
degree n > q+m-1, positive-definite residual covariance C, and arbitrary K,
independent S ~ W_q(n,I), q Gaussian rows N_m(0,C), and
W ~ W_m(n-q,C) reconstruct a matrix with law
W_(q+m)(n, [[I,K],[Kᵀ,KᵀK+C]]).

The theorem includes the entire joint matrix, not only its diagonal blocks or
Schur complement; the source is an explicit product measure. -/
theorem map_regressionReconstruction
    {n : ℝ} {q m : ℕ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ) {C : Matrix (Fin m) (Fin m) ℝ}
    (hC : C.PosDef) :
    (regressionDataMeasure n q m C).map (regressionReconstruction K) =
      nonsingularWishartMeasure n (regressionScale K C) := by
  have hsquare : CFC.sqrt C * CFC.sqrt C = C :=
    CFC.sqrt_mul_sqrt_self _ hC.posSemidef.nonneg
  have htranspose : (CFC.sqrt C)ᵀ = CFC.sqrt C := by
    have hh := (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg C)).isHermitian.eq
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hh
  have hrootdet : (CFC.sqrt C).det ≠ 0 := by
    intro hz
    have hd := congrArg Matrix.det hsquare
    rw [Matrix.det_mul, hz, zero_mul] at hd
    exact hC.det_pos.ne' hd.symm
  have hpush : (standardRegressionMeasure n q m).map
      (regressionDataTransform (q := q) (CFC.sqrt C)) =
        regressionDataMeasure n q m C := by
    simpa only [htranspose, hsquare] using
      (measurePreserving_regressionDataTransform hn (CFC.sqrt C) hrootdet).map_eq
  rw [← hpush, Measure.map_map (measurable_regressionReconstruction K)
    (measurable_regressionDataTransform (CFC.sqrt C))]
  have hfun : regressionReconstruction K ∘ regressionDataTransform (CFC.sqrt C) =
      Matrix.symmetricCongruenceLinearMap
        (regressionCovarianceFactor K (CFC.sqrt C)) ∘ standardRegressionGram := by
    funext x
    exact regressionReconstruction_transform K (CFC.sqrt C) x
  rw [hfun]
  exact map_whitenedRegressionGram hn K hC

end Wishart
end
end CanonicalSource4

section CanonicalSource5
/- Source: Wishart/RegressionCorrespondence.lean -/



/-!
# Joint-law and expectation forms of the regression representation

The selected matrix in the independent source is the selected principal block
of the reconstructed matrix, almost surely.  The joint pushforward identity
below expresses that identification directly, so the source-product theorem
can be used for the conditional representation in manuscript Lemma 2.2.
-/

noncomputable section

open MeasureTheory TauCeti TauCeti.Probability
open scoped Matrix

namespace Wishart

def regressionSelectedBlock {q m : ℕ} (X : SymmetricMatrix (q + m)) :
    SymmetricMatrix q :=
  ⟨(X : Matrix (Fin (q + m)) (Fin (q + m)) ℝ).submatrix
      (Fin.castAdd m) (Fin.castAdd m),
    Matrix.isHermitian_iff_isSelfAdjoint.mp
      ((Matrix.isHermitian_iff_isSelfAdjoint.mpr X.property).submatrix
        (Fin.castAdd m))⟩

@[fun_prop] theorem measurable_regressionSelectedBlock {q m : ℕ} :
    Measurable (regressionSelectedBlock (q := q) (m := m)) := by
  apply Measurable.subtype_mk
  apply Matrix.measurable_iff.mpr
  intro i j
  exact measurable_subtype_coe.eval_matrix

/-- The complete joint law of the selected block and the full matrix is the
one induced by the independent regression variables.  This is stronger than
the full-matrix marginal identity alone. -/
theorem map_regressionJointReconstruction
    {n : ℝ} {q m : ℕ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ) {C : Matrix (Fin m) (Fin m) ℝ}
    (hC : C.PosDef) :
    (regressionDataMeasure n q m C).map
        (fun x => (x.1, regressionReconstruction K x)) =
      (nonsingularWishartMeasure n (regressionScale K C)).map
        (fun X => (regressionSelectedBlock X, X)) := by
  rw [← map_regressionReconstruction hn K hC,
    Measure.map_map (by fun_prop) (measurable_regressionReconstruction K)]
  apply Measure.map_congr
  filter_upwards [ae_regressionReconstruction_selected n K C] with x hx
  apply Prod.ext
  · exact Subtype.ext hx.symm
  · rfl

/-- Integration against the concrete Wishart law can be transported to the
independent regression source without imposing any new shape or rank bound. -/
theorem integral_regressionReconstruction
    {n : ℝ} {q m : ℕ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ) {C : Matrix (Fin m) (Fin m) ℝ}
    (hC : C.PosDef) {f : SymmetricMatrix (q + m) → ℝ}
    (hf : AEStronglyMeasurable f
      (nonsingularWishartMeasure n (regressionScale K C))) :
    (∫ X, f X ∂nonsingularWishartMeasure n (regressionScale K C)) =
      ∫ x, f (regressionReconstruction K x) ∂regressionDataMeasure n q m C := by
  rw [← map_regressionReconstruction hn K hC] at hf ⊢
  exact integral_map (measurable_regressionReconstruction K).aemeasurable hf

/-- Integrability is preserved by the regression representation as well as
the value of the expectation. -/
theorem integrable_regressionReconstruction_iff
    {n : ℝ} {q m : ℕ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ) {C : Matrix (Fin m) (Fin m) ℝ}
    (hC : C.PosDef) {f : SymmetricMatrix (q + m) → ℝ}
    (hf : AEStronglyMeasurable f
      (nonsingularWishartMeasure n (regressionScale K C))) :
    Integrable f (nonsingularWishartMeasure n (regressionScale K C)) ↔
      Integrable (fun x => f (regressionReconstruction K x))
        (regressionDataMeasure n q m C) := by
  rw [← map_regressionReconstruction hn K hC] at hf ⊢
  exact integrable_map_measure hf (measurable_regressionReconstruction K).aemeasurable

end Wishart
end
end CanonicalSource5

section CanonicalSource6
/- Source: Wishart/BlockIndependence.lean -/



/-!
# Independence of Wishart principal blocks at block-diagonal scale

The diagonal blocks are not assumed independent. They are extracted from the
proved real-shape regression representation with K=0. The second block depends
only on the independent Gaussian and residual Wishart variables; its marginal
law is identified by the verified Wishart principal-submatrix theorem.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace Wishart

def principalSymmetricBlock {p q : ℕ} (f : Fin q → Fin p)
    (X : SymmetricMatrix p) : SymmetricMatrix q :=
  ⟨(X : Matrix (Fin p) (Fin p) ℝ).submatrix f f,
    Matrix.isHermitian_iff_isSelfAdjoint.mp
      ((Matrix.isHermitian_iff_isSelfAdjoint.mpr X.property).submatrix f)⟩

theorem principalSymmetricBlock_eq_congruence {p q : ℕ} (f : Fin q → Fin p) :
    principalSymmetricBlock f = Matrix.symmetricCongruenceLinearMap
      ((1 : Matrix (Fin p) (Fin p) ℝ).submatrix f id) := by
  funext X
  apply Subtype.ext
  rw [Matrix.coe_symmetricCongruenceLinearMap_apply,
    Matrix.transpose_submatrix, Matrix.transpose_one,
    Matrix.submatrix_one_mul_mul_submatrix_one]
  rfl

@[fun_prop] theorem measurable_principalSymmetricBlock {p q : ℕ}
    (f : Fin q → Fin p) : Measurable (principalSymmetricBlock f) := by
  rw [principalSymmetricBlock_eq_congruence]
  exact (LinearMap.continuous_of_finiteDimensional _).measurable

theorem map_principalSymmetricBlock_nonsingularWishartMeasure
    {n : ℝ} {p q : ℕ} (f : Fin q → Fin p) (hf : Function.Injective f)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (hn : (p : ℝ) - 1 < n) :
    (nonsingularWishartMeasure n S).map (principalSymmetricBlock f) =
      nonsingularWishartMeasure n (S.submatrix f f) := by
  rw [principalSymmetricBlock_eq_congruence]
  exact map_symmetricCongruenceLinearMap_submatrix_one_nonsingularWishartMeasure
    f hf hS hn

abbrev RegressionNoise (q m : ℕ) :=
  (Fin q → EuclideanSpace ℝ (Fin m)) × SymmetricMatrix m

def regressionNoiseMeasure (n : ℝ) (q m : ℕ) (C : Matrix (Fin m) (Fin m) ℝ) :
    Measure (RegressionNoise q m) :=
  (Measure.pi (fun _ : Fin q => multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) C)).prod
    (nonsingularWishartMeasure (n - q) C)

instance isFiniteMeasure_regressionNoiseMeasure (n : ℝ) (q m : ℕ)
    (C : Matrix (Fin m) (Fin m) ℝ) :
    IsFiniteMeasure (regressionNoiseMeasure n q m C) := by
  unfold regressionNoiseMeasure
  infer_instance

theorem isProbabilityMeasure_regressionNoiseMeasure {n : ℝ} {q m : ℕ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef) :
    IsProbabilityMeasure (regressionNoiseMeasure n q m C) := by
  have hdegree : (m : ℝ) - 1 < n - q := by
    push_cast at hn
    linarith
  letI := isProbabilityMeasure_nonsingularWishartMeasure hC hdegree
  unfold regressionNoiseMeasure
  infer_instance

def regressionNoiseGram {q m : ℕ} (x : RegressionNoise q m) : SymmetricMatrix m :=
  let G : Matrix (Fin m) (Fin q) ℝ := Matrix.of fun i j => x.1 j i
  ⟨G * Gᵀ + (x.2 : Matrix (Fin m) (Fin m) ℝ),
    Matrix.isHermitian_iff_isSelfAdjoint.mp
      ((show (G * Gᵀ).IsHermitian from by
        simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
          Matrix.isHermitian_mul_conjTranspose_self G).add
          (Matrix.isHermitian_iff_isSelfAdjoint.mpr x.2.property))⟩

@[fun_prop] theorem measurable_regressionNoiseGram {q m : ℕ} :
    Measurable (regressionNoiseGram (q := q) (m := m)) := by
  apply Measurable.subtype_mk
  apply Matrix.measurable_iff.mpr
  intro i j
  simp only [regressionNoiseGram, Matrix.add_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.of_apply]
  apply Measurable.add
  · apply Finset.measurable_sum
    intro a _
    exact
      ((measurable_pi_apply i).comp ((WithLp.measurable_ofLp 2 (Fin m → ℝ)).comp
        ((measurable_pi_apply a).comp measurable_fst))).mul
      ((measurable_pi_apply j).comp ((WithLp.measurable_ofLp 2 (Fin m → ℝ)).comp
        ((measurable_pi_apply a).comp measurable_fst)))
  · exact (measurable_subtype_coe.comp measurable_snd).eval_matrix

theorem regressionReconstruction_zero_trailing {q m : ℕ} (x : RegressionData q m) :
    principalSymmetricBlock (Fin.natAdd q)
        (regressionReconstruction (0 : Matrix (Fin q) (Fin m) ℝ) x) =
      regressionNoiseGram x.2 := by
  apply Subtype.ext
  ext i j
  have h := congrArg
    (fun A : Matrix (Fin q ⊕ Fin m) (Fin q ⊕ Fin m) ℝ => A (.inr i) (.inr j))
    (regressionReconstruction_submatrix (0 : Matrix (Fin q) (Fin m) ℝ) x)
  simpa only [principalSymmetricBlock, regressionNoiseGram, Matrix.submatrix_apply,
    finSumFinEquiv_apply_right, regressionBlockMatrix, Matrix.fromBlocks_apply₂₂,
    Matrix.transpose_zero, Matrix.zero_mul, zero_add] using h

theorem regressionScale_zero_trailing {q m : ℕ} (C : Matrix (Fin m) (Fin m) ℝ) :
    (regressionScale (0 : Matrix (Fin q) (Fin m) ℝ) C).submatrix
      (Fin.natAdd q) (Fin.natAdd q) = C := by
  ext i j
  simp [regressionScale, Matrix.submatrix_apply]

/-- The Gaussian Gram term plus the independent residual has the full marginal
degree n. This identification follows from regression and the principal
submatrix law, with no convolution identity assumed. -/
theorem map_regressionNoiseGram {n : ℝ} {q m : ℕ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef) :
    (regressionNoiseMeasure n q m C).map regressionNoiseGram =
      nonsingularWishartMeasure n C := by
  letI := isProbabilityMeasure_regressionNoiseMeasure hn hC
  have hnq : (q : ℝ) - 1 < n := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hn
    linarith
  letI := isProbabilityMeasure_nonsingularWishartMeasure
    (S := (1 : Matrix (Fin q) (Fin q) ℝ)) Matrix.PosDef.one hnq
  have hinj : Function.Injective (Fin.natAdd q : Fin m → Fin (q + m)) := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simpa only [Fin.val_natAdd, Nat.add_left_cancel_iff] using hv
  have htail := map_principalSymmetricBlock_nonsingularWishartMeasure
    (Fin.natAdd q) hinj (regressionScale_posDef 0 hC) hn
  rw [regressionScale_zero_trailing] at htail
  rw [← map_regressionReconstruction hn 0 hC,
    Measure.map_map (measurable_principalSymmetricBlock (Fin.natAdd q))
      (measurable_regressionReconstruction 0)] at htail
  have hfun : principalSymmetricBlock (Fin.natAdd q) ∘
      regressionReconstruction (0 : Matrix (Fin q) (Fin m) ℝ) =
      regressionNoiseGram ∘ Prod.snd :=
    funext regressionReconstruction_zero_trailing
  rw [hfun, ← Measure.map_map measurable_regressionNoiseGram measurable_snd] at htail
  change Measure.map regressionNoiseGram
    (Measure.map Prod.snd
      ((nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ)).prod
        (regressionNoiseMeasure n q m C))) = _ at htail
  rw [Measure.map_snd_prod, measure_univ, one_smul] at htail
  exact htail

/-- Exact joint law of the leading and trailing diagonal blocks when the
selected scale is whitened and the cross covariance vanishes. -/
theorem map_diagonalBlocks_regressionScale_zero {n : ℝ} {q m : ℕ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef) :
    (nonsingularWishartMeasure n
        (regressionScale (0 : Matrix (Fin q) (Fin m) ℝ) C)).map
      (fun X => (principalSymmetricBlock (Fin.castAdd m) X,
        principalSymmetricBlock (Fin.natAdd q) X)) =
      (nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ)).prod
        (nonsingularWishartMeasure n C) := by
  letI := isProbabilityMeasure_regressionNoiseMeasure hn hC
  rw [← map_regressionReconstruction hn 0 hC,
    Measure.map_map (by fun_prop) (measurable_regressionReconstruction 0)]
  have hae :
      (fun x : RegressionData q m =>
        (principalSymmetricBlock (Fin.castAdd m) (regressionReconstruction 0 x),
          principalSymmetricBlock (Fin.natAdd q) (regressionReconstruction 0 x))) =ᵐ[
            regressionDataMeasure n q m C]
        Prod.map id regressionNoiseGram := by
    filter_upwards [ae_regressionReconstruction_selected n
      (0 : Matrix (Fin q) (Fin m) ℝ) C] with x hx
    apply Prod.ext
    · exact Subtype.ext hx
    · exact regressionReconstruction_zero_trailing x
  rw [Measure.map_congr (show
    ((fun X => (principalSymmetricBlock (Fin.castAdd m) X,
      principalSymmetricBlock (Fin.natAdd q) X)) ∘
        regressionReconstruction (0 : Matrix (Fin q) (Fin m) ℝ)) =ᵐ[
          regressionDataMeasure n q m C] Prod.map id regressionNoiseGram from hae)]
  change Measure.map (Prod.map id regressionNoiseGram)
    ((nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ)).prod
      (regressionNoiseMeasure n q m C)) = _
  rw [← Measure.map_prod_map _ _ measurable_id measurable_regressionNoiseGram,
    Measure.map_id, map_regressionNoiseGram hn hC]

def blockDiagonalMatrix {q m : ℕ} (A : Matrix (Fin q) (Fin q) ℝ)
    (C : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin (q + m)) (Fin (q + m)) ℝ :=
  (Matrix.fromBlocks A 0 0 C).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem regressionScale_zero_eq_blockDiagonal {q m : ℕ}
    (C : Matrix (Fin m) (Fin m) ℝ) :
    regressionScale (0 : Matrix (Fin q) (Fin m) ℝ) C = blockDiagonalMatrix 1 C := by
  simp [regressionScale, blockDiagonalMatrix]

@[simp] theorem det_blockDiagonalMatrix {q m : ℕ} (A : Matrix (Fin q) (Fin q) ℝ)
    (C : Matrix (Fin m) (Fin m) ℝ) :
    (blockDiagonalMatrix A C).det = A.det * C.det := by
  simp [blockDiagonalMatrix]

theorem blockDiagonalMatrix_congruence_left {q m : ℕ}
    (R : Matrix (Fin q) (Fin q) ℝ) (C : Matrix (Fin m) (Fin m) ℝ) :
    blockDiagonalMatrix R (1 : Matrix (Fin m) (Fin m) ℝ) *
        regressionScale (0 : Matrix (Fin q) (Fin m) ℝ) C *
        (blockDiagonalMatrix R (1 : Matrix (Fin m) (Fin m) ℝ))ᵀ =
      blockDiagonalMatrix (R * Rᵀ) C := by
  rw [regressionScale_zero_eq_blockDiagonal]
  simp only [blockDiagonalMatrix, Matrix.transpose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.transpose_one, Matrix.transpose_zero, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero]

theorem castAdd_ne_natAdd {q m : ℕ} (i : Fin q) (j : Fin m) :
    Fin.castAdd m i ≠ Fin.natAdd q j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

theorem natAdd_ne_castAdd {q m : ℕ} (i : Fin m) (j : Fin q) :
    Fin.natAdd q i ≠ Fin.castAdd m j := (castAdd_ne_natAdd j i).symm

theorem leadingSelection_blockDiagonal {q m : ℕ}
    (R : Matrix (Fin q) (Fin q) ℝ) :
    (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ).submatrix (Fin.castAdd m) id *
        blockDiagonalMatrix R (1 : Matrix (Fin m) (Fin m) ℝ) =
      R * (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ).submatrix (Fin.castAdd m) id := by
  have hselection :
      (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ).submatrix (Fin.castAdd m) id *
          blockDiagonalMatrix R (1 : Matrix (Fin m) (Fin m) ℝ) =
        (blockDiagonalMatrix R (1 : Matrix (Fin m) (Fin m) ℝ)).submatrix
          (Fin.castAdd m) id := by
    simpa only [Equiv.coe_refl, Equiv.refl_symm, Function.id_comp] using
      Matrix.one_submatrix_mul (Fin.castAdd m) (Equiv.refl (Fin (q + m)))
        (blockDiagonalMatrix R (1 : Matrix (Fin m) (Fin m) ℝ))
  rw [hselection]
  ext i j
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin q ⊕ Fin m ≃ Fin (q + m)).surjective j
  rcases j with j | j <;>
    simp [blockDiagonalMatrix, Matrix.submatrix_apply, Matrix.mul_apply,
      Matrix.one_apply, castAdd_ne_natAdd]

theorem trailingSelection_blockDiagonal {q m : ℕ}
    (R : Matrix (Fin q) (Fin q) ℝ) :
    (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ).submatrix (Fin.natAdd q) id *
        blockDiagonalMatrix R (1 : Matrix (Fin m) (Fin m) ℝ) =
      (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ).submatrix (Fin.natAdd q) id := by
  have hselection :
      (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ).submatrix (Fin.natAdd q) id *
          blockDiagonalMatrix R (1 : Matrix (Fin m) (Fin m) ℝ) =
        (blockDiagonalMatrix R (1 : Matrix (Fin m) (Fin m) ℝ)).submatrix
          (Fin.natAdd q) id := by
    simpa only [Equiv.coe_refl, Equiv.refl_symm, Function.id_comp] using
      Matrix.one_submatrix_mul (Fin.natAdd q) (Equiv.refl (Fin (q + m)))
        (blockDiagonalMatrix R (1 : Matrix (Fin m) (Fin m) ℝ))
  rw [hselection]
  ext i j
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin q ⊕ Fin m ≃ Fin (q + m)).surjective j
  rcases j with j | j <;>
    simp [blockDiagonalMatrix, Matrix.submatrix_apply, Matrix.one_apply,
      natAdd_ne_castAdd]

theorem principalBlocks_blockDiagonal_congruence {q m : ℕ}
    (R : Matrix (Fin q) (Fin q) ℝ) (X : SymmetricMatrix (q + m)) :
    (principalSymmetricBlock (Fin.castAdd m)
        (Matrix.symmetricCongruenceLinearMap
          (blockDiagonalMatrix R (1 : Matrix (Fin m) (Fin m) ℝ)) X),
      principalSymmetricBlock (Fin.natAdd q)
        (Matrix.symmetricCongruenceLinearMap
          (blockDiagonalMatrix R (1 : Matrix (Fin m) (Fin m) ℝ)) X)) =
      (Matrix.symmetricCongruenceLinearMap R (principalSymmetricBlock (Fin.castAdd m) X),
        principalSymmetricBlock (Fin.natAdd q) X) := by
  apply Prod.ext
  · have h := congrArg (fun M : Matrix (Fin q) (Fin (q + m)) ℝ =>
        Matrix.symmetricCongruenceLinearMap M X) (leadingSelection_blockDiagonal (m := m) R)
    simpa only [principalSymmetricBlock_eq_congruence,
      Matrix.symmetricCongruenceLinearMap_mul, LinearMap.comp_apply] using h
  · have h := congrArg (fun M : Matrix (Fin m) (Fin (q + m)) ℝ =>
        Matrix.symmetricCongruenceLinearMap M X) (trailingSelection_blockDiagonal (m := m) R)
    simpa only [principalSymmetricBlock_eq_congruence,
      Matrix.symmetricCongruenceLinearMap_mul, LinearMap.comp_apply] using h

/-- **Independence of the two principal blocks at block-diagonal scale.**
Both marginal degrees are n, and n is any real number in the full nonsingular
range. The conclusion is an exact joint product law. -/
theorem map_diagonalBlocks_blockDiagonalScale {n : ℝ} {q m : ℕ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {A : Matrix (Fin q) (Fin q) ℝ} (hA : A.PosDef)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef) :
    (nonsingularWishartMeasure n (blockDiagonalMatrix A C)).map
      (fun X => (principalSymmetricBlock (Fin.castAdd m) X,
        principalSymmetricBlock (Fin.natAdd q) X)) =
      (nonsingularWishartMeasure n A).prod (nonsingularWishartMeasure n C) := by
  have hnm : (m : ℝ) - 1 < n := by
    push_cast at hn
    linarith [Nat.cast_nonneg (α := ℝ) q]
  letI := isProbabilityMeasure_nonsingularWishartMeasure hC hnm
  let R : Matrix (Fin q) (Fin q) ℝ := CFC.sqrt A
  have hRR : R * Rᵀ = A := by
    rw [show Rᵀ = R from matrix_sqrt_transpose A]
    exact CFC.sqrt_mul_sqrt_self _ hA.posSemidef.nonneg
  have hR : R.det ≠ 0 := by
    intro hz
    have hdet := congrArg Matrix.det hRR
    rw [Matrix.det_mul, hz, zero_mul] at hdet
    exact hA.det_pos.ne' hdet.symm
  have hD : (blockDiagonalMatrix R (1 : Matrix (Fin m) (Fin m) ℝ)).det ≠ 0 := by
    simpa only [det_blockDiagonalMatrix, Matrix.det_one, mul_one] using hR
  have hfull :
      (nonsingularWishartMeasure n (regressionScale (0 : Matrix (Fin q) (Fin m) ℝ) C)).map
        (Matrix.symmetricCongruenceLinearMap
          (blockDiagonalMatrix R (1 : Matrix (Fin m) (Fin m) ℝ))) =
        nonsingularWishartMeasure n (blockDiagonalMatrix A C) := by
    simpa only [blockDiagonalMatrix_congruence_left, hRR] using
      map_symmetricCongruenceLinearMap_nonsingularWishartMeasure_of_det_ne_zero
        n (regressionScale (0 : Matrix (Fin q) (Fin m) ℝ) C) hD
  have hselected : (nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ)).map
      (Matrix.symmetricCongruenceLinearMap R) = nonsingularWishartMeasure n A := by
    simpa only [Matrix.mul_one, hRR] using
      map_symmetricCongruenceLinearMap_nonsingularWishartMeasure_of_det_ne_zero n 1 hR
  have hfun :
      (fun X : SymmetricMatrix (q + m) =>
        (principalSymmetricBlock (Fin.castAdd m) X,
          principalSymmetricBlock (Fin.natAdd q) X)) ∘
        Matrix.symmetricCongruenceLinearMap
          (blockDiagonalMatrix R (1 : Matrix (Fin m) (Fin m) ℝ)) =
      Prod.map (Matrix.symmetricCongruenceLinearMap R) id ∘
        (fun X => (principalSymmetricBlock (Fin.castAdd m) X,
          principalSymmetricBlock (Fin.natAdd q) X)) :=
    funext (principalBlocks_blockDiagonal_congruence R)
  rw [← hfull, Measure.map_map (by fun_prop)
    (LinearMap.continuous_of_finiteDimensional _).measurable,
    hfun, ← Measure.map_map (by fun_prop) (by fun_prop),
    map_diagonalBlocks_regressionScale_zero hn hC,
    ← Measure.map_prod_map _ _ (LinearMap.continuous_of_finiteDimensional _).measurable
      measurable_id, hselected, Measure.map_id]

/-- Factorization of arbitrary measurable block observables. The applications
to determinant powers additionally prove integrability, so these Bochner
integrals are the finite moments used in the manuscript's equality case. -/
theorem integral_mul_diagonalBlocks_blockDiagonalScale {n : ℝ} {q m : ℕ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {A : Matrix (Fin q) (Fin q) ℝ} (hA : A.PosDef)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {f : SymmetricMatrix q → ℝ} {g : SymmetricMatrix m → ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    (∫ X, f (principalSymmetricBlock (Fin.castAdd m) X) *
      g (principalSymmetricBlock (Fin.natAdd q) X)
        ∂nonsingularWishartMeasure n (blockDiagonalMatrix A C)) =
      (∫ S, f S ∂nonsingularWishartMeasure n A) *
        ∫ T, g T ∂nonsingularWishartMeasure n C := by
  have hnq : (q : ℝ) - 1 < n := by
    push_cast at hn
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hnm : (m : ℝ) - 1 < n := by
    push_cast at hn
    linarith [Nat.cast_nonneg (α := ℝ) q]
  letI := isProbabilityMeasure_nonsingularWishartMeasure hA hnq
  letI := isProbabilityMeasure_nonsingularWishartMeasure hC hnm
  have hmap := map_diagonalBlocks_blockDiagonalScale hn hA hC
  have hi := integral_map
    (φ := fun X : SymmetricMatrix (q + m) =>
      (principalSymmetricBlock (Fin.castAdd m) X, principalSymmetricBlock (Fin.natAdd q) X))
    (f := fun x : SymmetricMatrix q × SymmetricMatrix m => f x.1 * g x.2)
    (μ := nonsingularWishartMeasure n (blockDiagonalMatrix A C))
    (by fun_prop) (by fun_prop)
  rw [hmap, integral_prod_mul] at hi
  exact hi.symm

end Wishart
end
end CanonicalSource6

section CanonicalSource7
/- Source: Wishart/ScaleNormalization.lean -/



/-!
# Whitening a selected principal block without changing the other blocks

An arbitrary positive-definite scale is reduced to the exact covariance in
the regression theorem. The selected block is conjugated by its inverse
positive square root. Every matrix entry in the complementary principal block
is unchanged, and the selected determinant changes by the fixed scale factor.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace Wishart

def twoBlockScale {q m : ℕ} (A : Matrix (Fin q) (Fin q) ℝ)
    (B : Matrix (Fin q) (Fin m) ℝ) (D : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin (q + m)) (Fin (q + m)) ℝ :=
  (Matrix.fromBlocks A B Bᵀ D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

def leadingScale (q m : ℕ) (S : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) :
    Matrix (Fin q) (Fin q) ℝ := S.submatrix (Fin.castAdd m) (Fin.castAdd m)

def crossScale (q m : ℕ) (S : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) :
    Matrix (Fin q) (Fin m) ℝ := S.submatrix (Fin.castAdd m) (Fin.natAdd q)

def trailingScale (q m : ℕ) (S : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) :
    Matrix (Fin m) (Fin m) ℝ := S.submatrix (Fin.natAdd q) (Fin.natAdd q)

def selectedInverseRoot (q m : ℕ)
    (S : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  (CFC.sqrt (leadingScale q m S))⁻¹

def selectedWhitening (q m : ℕ)
    (S : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) :
    Matrix (Fin (q + m)) (Fin (q + m)) ℝ :=
  blockDiagonalMatrix (selectedInverseRoot q m S) (1 : Matrix (Fin m) (Fin m) ℝ)

def normalizedCrossScale (q m : ℕ)
    (S : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) : Matrix (Fin q) (Fin m) ℝ :=
  selectedInverseRoot q m S * crossScale q m S

def selectedSchurScale (q m : ℕ)
    (S : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  trailingScale q m S - (crossScale q m S)ᵀ * (leadingScale q m S)⁻¹ * crossScale q m S

theorem leadingScale_posDef {q m : ℕ}
    {S : Matrix (Fin (q + m)) (Fin (q + m)) ℝ} (hS : S.PosDef) :
    (leadingScale q m S).PosDef := hS.submatrix (Fin.castAdd_injective q m)

theorem eq_twoBlockScale {q m : ℕ}
    {S : Matrix (Fin (q + m)) (Fin (q + m)) ℝ} (hS : S.IsHermitian) :
    S = twoBlockScale (leadingScale q m S) (crossScale q m S) (trailingScale q m S) := by
  apply Matrix.submatrix_injective finSumFinEquiv.surjective finSumFinEquiv.surjective
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [twoBlockScale, leadingScale, Matrix.submatrix_apply]
  · simp [twoBlockScale, crossScale, Matrix.submatrix_apply]
  · simpa [twoBlockScale, crossScale, Matrix.submatrix_apply] using
      (hS.apply (Fin.natAdd q i) (Fin.castAdd m j)).symm
  · simp [twoBlockScale, trailingScale, Matrix.submatrix_apply]

theorem twoBlockScale_congruence_left {q m : ℕ}
    (H A : Matrix (Fin q) (Fin q) ℝ) (B : Matrix (Fin q) (Fin m) ℝ)
    (D : Matrix (Fin m) (Fin m) ℝ) :
    blockDiagonalMatrix H (1 : Matrix (Fin m) (Fin m) ℝ) * twoBlockScale A B D *
        (blockDiagonalMatrix H (1 : Matrix (Fin m) (Fin m) ℝ))ᵀ =
      twoBlockScale (H * A * Hᵀ) (H * B) D := by
  simp only [blockDiagonalMatrix, twoBlockScale, Matrix.transpose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

theorem sqrt_det_ne_zero_of_posDef {q : ℕ} {A : Matrix (Fin q) (Fin q) ℝ}
    (hA : A.PosDef) : (CFC.sqrt A).det ≠ 0 := by
  intro hz
  have hdet := congrArg Matrix.det (CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg)
  rw [Matrix.det_mul, hz, zero_mul] at hdet
  exact hA.det_pos.ne' hdet.symm

theorem inverseSqrt_properties {q : ℕ} {A : Matrix (Fin q) (Fin q) ℝ}
    (hA : A.PosDef) :
    ((CFC.sqrt A)⁻¹)ᵀ = (CFC.sqrt A)⁻¹ ∧
      (CFC.sqrt A)⁻¹ * A * ((CFC.sqrt A)⁻¹)ᵀ = 1 ∧
      (CFC.sqrt A)⁻¹ * (CFC.sqrt A)⁻¹ = A⁻¹ := by
  let R : Matrix (Fin q) (Fin q) ℝ := CFC.sqrt A
  have hR : IsUnit R.det := isUnit_iff_ne_zero.mpr (sqrt_det_ne_zero_of_posDef hA)
  have hsquare : R * R = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have htranspose : Rᵀ = R := matrix_sqrt_transpose A
  have hHR : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hR
  have hRH : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hR
  have hHt : (R⁻¹)ᵀ = R⁻¹ := by rw [Matrix.transpose_nonsing_inv, htranspose]
  refine ⟨hHt, ?_, ?_⟩
  · change R⁻¹ * A * (R⁻¹)ᵀ = 1
    rw [hHt, ← hsquare, ← Matrix.mul_assoc R⁻¹ R R, hHR,
      Matrix.one_mul, hRH]
  · change R⁻¹ * R⁻¹ = A⁻¹
    apply (Matrix.inv_eq_left_inv ?_).symm
    rw [← hsquare, Matrix.mul_assoc R⁻¹ R⁻¹ (R * R),
      ← Matrix.mul_assoc R⁻¹ R R, hHR, Matrix.one_mul, hHR]

theorem inverseSqrt_mul_eq_zero_iff {q : ℕ} {A : Matrix (Fin q) (Fin q) ℝ}
    (hA : A.PosDef) {ι : Type*} (B : Matrix (Fin q) ι ℝ) :
    (CFC.sqrt A)⁻¹ * B = 0 ↔ B = 0 := by
  have hR : IsUnit (CFC.sqrt A).det :=
    isUnit_iff_ne_zero.mpr (sqrt_det_ne_zero_of_posDef hA)
  constructor
  · intro h
    have hh := congrArg (fun M : Matrix (Fin q) ι ℝ => CFC.sqrt A * M) h
    simpa only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hR,
      Matrix.one_mul, Matrix.mul_zero] using hh
  · rintro rfl
    exact Matrix.mul_zero _

/-- Whitening preserves whether any selected cross block vanishes, including
each individual complementary principal block used in the strictness case. -/
theorem normalizedCrossScale_submatrix_eq_zero_iff {q m : ℕ}
    {S : Matrix (Fin (q + m)) (Fin (q + m)) ℝ} (hS : S.PosDef)
    {ι : Type*} (f : ι → Fin m) :
    (normalizedCrossScale q m S).submatrix id f = 0 ↔
      (crossScale q m S).submatrix id f = 0 := by
  have hsub : (normalizedCrossScale q m S).submatrix id f =
      (CFC.sqrt (leadingScale q m S))⁻¹ * (crossScale q m S).submatrix id f := rfl
  rw [hsub]
  exact inverseSqrt_mul_eq_zero_iff (leadingScale_posDef hS) _

theorem normalizedCrossScale_gram {q m : ℕ}
    {S : Matrix (Fin (q + m)) (Fin (q + m)) ℝ} (hS : S.PosDef) :
    (normalizedCrossScale q m S)ᵀ * normalizedCrossScale q m S =
      (crossScale q m S)ᵀ * (leadingScale q m S)⁻¹ * crossScale q m S := by
  obtain ⟨htranspose, _, hsquare⟩ := inverseSqrt_properties (leadingScale_posDef hS)
  simp only [normalizedCrossScale, selectedInverseRoot, Matrix.transpose_mul]
  rw [htranspose]
  calc
    (crossScale q m S)ᵀ * (CFC.sqrt (leadingScale q m S))⁻¹ *
        ((CFC.sqrt (leadingScale q m S))⁻¹ * crossScale q m S) =
        (crossScale q m S)ᵀ *
          ((CFC.sqrt (leadingScale q m S))⁻¹ * (CFC.sqrt (leadingScale q m S))⁻¹) *
          crossScale q m S := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hsquare]

/-- Exact deterministic covariance normalization. -/
theorem selectedWhitening_scale {q m : ℕ}
    {S : Matrix (Fin (q + m)) (Fin (q + m)) ℝ} (hS : S.PosDef) :
    selectedWhitening q m S * S * (selectedWhitening q m S)ᵀ =
      regressionScale (normalizedCrossScale q m S) (selectedSchurScale q m S) := by
  have hH := (inverseSqrt_properties (leadingScale_posDef hS)).2.1
  have hsum : (normalizedCrossScale q m S)ᵀ * normalizedCrossScale q m S +
      selectedSchurScale q m S = trailingScale q m S := by
    rw [normalizedCrossScale_gram hS, selectedSchurScale]
    abel
  calc
    selectedWhitening q m S * S * (selectedWhitening q m S)ᵀ =
        selectedWhitening q m S *
          twoBlockScale (leadingScale q m S) (crossScale q m S) (trailingScale q m S) *
            (selectedWhitening q m S)ᵀ := by rw [← eq_twoBlockScale hS.isHermitian]
    _ = twoBlockScale 1 (normalizedCrossScale q m S) (trailingScale q m S) := by
      change blockDiagonalMatrix _ 1 * _ * (blockDiagonalMatrix _ 1)ᵀ = _
      rw [twoBlockScale_congruence_left]
      simpa only [selectedInverseRoot, hH, normalizedCrossScale]
    _ = _ := by simp only [twoBlockScale, regressionScale, hsum]

theorem regressionScale_shear {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (C : Matrix (Fin m) (Fin m) ℝ) :
    regressionCovarianceFactor (-K) 1 * regressionScale K C *
        (regressionCovarianceFactor (-K) 1)ᵀ = blockDiagonalMatrix 1 C := by
  simp only [regressionCovarianceFactor, regressionScale, blockDiagonalMatrix,
    Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.transpose_one,
    Matrix.transpose_zero, Matrix.transpose_neg, Matrix.transpose_transpose,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul,
    zero_add, add_zero, neg_mul, mul_neg]
  simp only [neg_add_cancel, Matrix.zero_mul, zero_add, Matrix.neg_mul, neg_add_cancel_left]

theorem regressionScale_posDef_iff {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (C : Matrix (Fin m) (Fin m) ℝ) :
    (regressionScale K C).PosDef ↔ C.PosDef := by
  constructor
  · intro h
    have hT : IsUnit (regressionCovarianceFactor (-K) (1 : Matrix (Fin m) (Fin m) ℝ)) := by
      apply (Matrix.isUnit_iff_isUnit_det _).mpr
      simp only [det_regressionCovarianceFactor, Matrix.det_one]
      exact isUnit_one
    have hdiag := h.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hT)
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, regressionScale_shear] at hdiag
    have hinj : Function.Injective (Fin.natAdd q : Fin m → Fin (q + m)) := by
      intro i j hij
      apply Fin.ext
      have hval := congrArg Fin.val hij
      simpa only [Fin.val_natAdd, Nat.add_left_cancel_iff] using hval
    have hc := hdiag.submatrix hinj
    have hblock : (blockDiagonalMatrix (1 : Matrix (Fin q) (Fin q) ℝ) C).submatrix
        (Fin.natAdd q) (Fin.natAdd q) = C := by
      ext i j
      simp [blockDiagonalMatrix, Matrix.submatrix_apply]
    rwa [hblock] at hc
  · exact regressionScale_posDef K

theorem selectedWhitening_det_ne_zero {q m : ℕ}
    {S : Matrix (Fin (q + m)) (Fin (q + m)) ℝ} (hS : S.PosDef) :
    (selectedWhitening q m S).det ≠ 0 := by
  simp only [selectedWhitening, det_blockDiagonalMatrix, Matrix.det_one, mul_one,
    selectedInverseRoot, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact inv_ne_zero (sqrt_det_ne_zero_of_posDef (leadingScale_posDef hS))

/-- The residual covariance is the usual Schur complement, and is genuinely
positive definite throughout the full nonsingular scale range. -/
theorem selectedSchurScale_posDef {q m : ℕ}
    {S : Matrix (Fin (q + m)) (Fin (q + m)) ℝ} (hS : S.PosDef) :
    (selectedSchurScale q m S).PosDef := by
  have hW : IsUnit (selectedWhitening q m S) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (selectedWhitening_det_ne_zero hS))
  have hnorm := hS.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hW)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, selectedWhitening_scale hS] at hnorm
  exact (regressionScale_posDef_iff _ _).mp hnorm

/-- Whitening transports the actual real-shape Wishart law to the exact scale
required by the regression theorem. -/
theorem map_selectedWhitening_nonsingularWishartMeasure {q m : ℕ} (n : ℝ)
    {S : Matrix (Fin (q + m)) (Fin (q + m)) ℝ} (hS : S.PosDef) :
    (nonsingularWishartMeasure n S).map
      (Matrix.symmetricCongruenceLinearMap (selectedWhitening q m S)) =
      nonsingularWishartMeasure n
        (regressionScale (normalizedCrossScale q m S) (selectedSchurScale q m S)) := by
  simpa only [selectedWhitening_scale hS] using
    map_symmetricCongruenceLinearMap_nonsingularWishartMeasure_of_det_ne_zero
      n S (selectedWhitening_det_ne_zero hS)

theorem selectedWhitening_blocks {q m : ℕ}
    (S : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) (X : SymmetricMatrix (q + m)) :
    (principalSymmetricBlock (Fin.castAdd m)
        (Matrix.symmetricCongruenceLinearMap (selectedWhitening q m S) X),
      principalSymmetricBlock (Fin.natAdd q)
        (Matrix.symmetricCongruenceLinearMap (selectedWhitening q m S) X)) =
      (Matrix.symmetricCongruenceLinearMap (selectedInverseRoot q m S)
        (principalSymmetricBlock (Fin.castAdd m) X),
        principalSymmetricBlock (Fin.natAdd q) X) :=
  principalBlocks_blockDiagonal_congruence (selectedInverseRoot q m S) X

/-- Every complementary principal submatrix is unchanged pointwise. The map
selecting its coordinates may use any order. -/
theorem selectedWhitening_remainingSubmatrix {q m : ℕ}
    (S : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) (X : SymmetricMatrix (q + m))
    {ι : Type*} (f : ι → Fin m) :
    ((Matrix.symmetricCongruenceLinearMap (selectedWhitening q m S) X :
        SymmetricMatrix (q + m)) : Matrix (Fin (q + m)) (Fin (q + m)) ℝ).submatrix
          (Fin.natAdd q ∘ f) (Fin.natAdd q ∘ f) =
      (X : Matrix (Fin (q + m)) (Fin (q + m)) ℝ).submatrix
        (Fin.natAdd q ∘ f) (Fin.natAdd q ∘ f) := by
  have htail := congrArg Prod.snd (selectedWhitening_blocks S X)
  have hm := congrArg
    (fun U : SymmetricMatrix m => (U : Matrix (Fin m) (Fin m) ℝ).submatrix f f) htail
  exact hm

/-- The selected determinant changes by exactly the inverse determinant of its
scale block. In particular, the whitening introduces no random factor. -/
theorem selectedWhitening_selectedDeterminant {q m : ℕ}
    {S : Matrix (Fin (q + m)) (Fin (q + m)) ℝ} (hS : S.PosDef)
    (X : SymmetricMatrix (q + m)) :
    ((principalSymmetricBlock (Fin.castAdd m)
      (Matrix.symmetricCongruenceLinearMap (selectedWhitening q m S) X) :
        SymmetricMatrix q) : Matrix (Fin q) (Fin q) ℝ).det =
      (leadingScale q m S).det⁻¹ *
        ((principalSymmetricBlock (Fin.castAdd m) X : SymmetricMatrix q) :
          Matrix (Fin q) (Fin q) ℝ).det := by
  have hlead := congrArg Prod.fst (selectedWhitening_blocks S X)
  simp only [Prod.fst] at hlead
  rw [hlead, Matrix.coe_symmetricCongruenceLinearMap_apply,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hdet : (selectedInverseRoot q m S).det * (selectedInverseRoot q m S).det =
      (leadingScale q m S).det⁻¹ := by
    rw [← Matrix.det_mul]
    change ((CFC.sqrt (leadingScale q m S))⁻¹ *
      (CFC.sqrt (leadingScale q m S))⁻¹).det = _
    rw [(inverseSqrt_properties (leadingScale_posDef hS)).2.2, Matrix.det_nonsing_inv,
      Ring.inverse_eq_inv]
  calc
    _ = ((selectedInverseRoot q m S).det * (selectedInverseRoot q m S).det) *
        ((principalSymmetricBlock (Fin.castAdd m) X : SymmetricMatrix q) :
          Matrix (Fin q) (Fin q) ℝ).det := by ring
    _ = _ := by rw [hdet]

end Wishart
end
end CanonicalSource7

section CanonicalSource8
/- Source: Wishart/Statements.lean -/



/-!
# Exact statement of the principal real Wishart theorem

`PrincipalTheorem` below is a proposition, not a proved theorem. Keeping the
target separate prevents a proof of a weakened statement or an auxiliary lemma
from being mistaken for verification of the manuscript.

The law is TauCeti's density-defined real-shape Wishart law on the vector space
of symmetric real matrices. No Gaussian-row restriction is imposed on `α`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Matrix

namespace WishartVerification

abbrev SymmetricMatrix (p : ℕ) :=
  selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)

/-- A partition into labelled nonempty principal blocks. -/
structure PrincipalPartition (p d : ℕ) where
  block : Fin d → Finset (Fin p)
  nonempty : ∀ i, (block i).Nonempty
  unique_block : ∀ x : Fin p, ∃! i : Fin d, x ∈ block i

def principalMinor {p : ℕ} (I : Finset (Fin p)) (X : SymmetricMatrix p) : ℝ :=
  ((X : Matrix (Fin p) (Fin p) ℝ).submatrix
    (fun i : I => (i : Fin p)) (fun i : I => (i : Fin p))).det

def principalMomentIntegrand {p d : ℕ} (P : PrincipalPartition p d)
    (ν : Fin d → ℝ) (J : Finset (Fin d)) (X : SymmetricMatrix p) : ℝ :=
  ∏ i ∈ J, (principalMinor (P.block i) X) ^ (ν i)

def principalMoment {p d : ℕ} (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (P : PrincipalPartition p d) (ν : Fin d → ℝ) (J : Finset (Fin d)) : ℝ :=
  ∫ X, principalMomentIntegrand P ν J X
    ∂TauCeti.Probability.nonsingularWishartMeasure α Sigma

def independentActiveScaleBlocks {p d : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (P : PrincipalPartition p d) (ν : Fin d → ℝ) : Prop :=
  ∀ i j : Fin d, i ≠ j → 0 < ν i → 0 < ν j →
    ∀ a ∈ P.block i, ∀ b ∈ P.block j, Sigma a b = 0

/-- The whole content of manuscript Theorem 1.1: arbitrary real shape in its
full nonsingular range, all nonnegative real exponents, all selected splits,
joint integrability, and the exact equality characterization. This is an
unproved target definition until an explicit theorem of this type is supplied.

Integrability is required for every subproduct, so all three real integrals in
every split are genuine expectations. Equality of the two endpoints is
equivalent to equality throughout the displayed chain once both inequalities
have been proved.
-/
def PrincipalTheorem : Prop :=
  ∀ (p d : ℕ) (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (P : PrincipalPartition p d) (ν : Fin d → ℝ),
    0 < p → 0 < d → (p : ℝ) - 1 < α → Sigma.PosDef → (∀ i, 0 ≤ ν i) →
    (∀ J : Finset (Fin d),
      Integrable (principalMomentIntegrand P ν J)
        (TauCeti.Probability.nonsingularWishartMeasure α Sigma)) ∧
    (∀ j : Fin d,
      principalMoment α Sigma P ν {j} *
          principalMoment α Sigma P ν (Finset.univ.erase j) ≤
        principalMoment α Sigma P ν Finset.univ ∧
      (∏ i : Fin d, principalMoment α Sigma P ν {i}) ≤
        principalMoment α Sigma P ν {j} *
          principalMoment α Sigma P ν (Finset.univ.erase j)) ∧
    ((principalMoment α Sigma P ν Finset.univ =
        ∏ i : Fin d, principalMoment α Sigma P ν {i}) ↔
      independentActiveScaleBlocks Sigma P ν)

end WishartVerification
end
end CanonicalSource8

section CanonicalSource9
/- Source: Wishart/StatementCorrespondence.lean -/



/-!
# Correspondence checks for the principal Wishart statement

These lemmas justify the finite-index and equality formulations in
`WishartVerification.PrincipalTheorem`. They do not prove that proposition or
assume it as an axiom. The equality comparison below assumes the two displayed
inequalities solely to prove the elementary equivalence of two formulations of
"equality throughout".
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Matrix

namespace WishartVerification

theorem PrincipalPartition.covers {p d : ℕ} (P : PrincipalPartition p d)
    (a : Fin p) : ∃ i : Fin d, a ∈ P.block i :=
  (P.unique_block a).exists

theorem PrincipalPartition.disjoint {p d : ℕ} (P : PrincipalPartition p d)
    {i j : Fin d} (hij : i ≠ j) : Disjoint (P.block i) (P.block j) := by
  apply Finset.disjoint_left.mpr
  intro a hai haj
  obtain ⟨k, _, hk⟩ := P.unique_block a
  exact hij ((hk i hai).trans (hk j haj).symm)

/-- The determinant indexed by the finite set agrees with the determinant
computed using any enumeration of that set. Thus the definition imposes no
extra ordering on the paper's principal blocks. -/
theorem principalMinor_eq_det_enumeration {p : ℕ} (I : Finset (Fin p))
    (X : SymmetricMatrix p) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ I) :
    principalMinor I X =
      ((X : Matrix (Fin p) (Fin p) ℝ).submatrix
        (fun i => (e i : Fin p)) (fun i => (e i : Fin p))).det := by
  exact (Matrix.det_submatrix_equiv_self e
    ((X : Matrix (Fin p) (Fin p) ℝ).submatrix
      (fun i : I => (i : Fin p)) (fun i : I => (i : Fin p)))).symm

theorem principalMinor_pos {p : ℕ} (I : Finset (Fin p)) (X : SymmetricMatrix p)
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    0 < principalMinor I X :=
  (hX.submatrix (Subtype.coe_injective : Function.Injective (fun i : I =>
    (i : Fin p)))).det_pos

/-- On the actual Wishart support, the real power in the target statement is
the usual positive-base exponential/logarithm power. -/
theorem principalMinor_rpow_eq_exp {p : ℕ} (I : Finset (Fin p))
    (X : SymmetricMatrix p) (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosDef) (ν : ℝ) :
    (principalMinor I X) ^ ν = Real.exp (Real.log (principalMinor I X) * ν) :=
  Real.rpow_def_of_pos (principalMinor_pos I X hX) ν

theorem ae_principalMinor_pos {p : ℕ} (α : ℝ)
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (I : Finset (Fin p)) :
    ∀ᵐ X ∂TauCeti.Probability.nonsingularWishartMeasure α Sigma,
      0 < principalMinor I X := by
  filter_upwards [TauCeti.Probability.ae_posDef_nonsingularWishartMeasure α Sigma]
    with X hX
  exact principalMinor_pos I X hX

theorem principalMomentIntegrand_pos {p d : ℕ} (P : PrincipalPartition p d)
    (ν : Fin d → ℝ) (J : Finset (Fin d)) (X : SymmetricMatrix p)
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    0 < principalMomentIntegrand P ν J X := by
  apply Finset.prod_pos
  intro i _
  exact Real.rpow_pos_of_pos (principalMinor_pos (P.block i) X hX) _

theorem ae_principalMomentIntegrand_pos {p d : ℕ} (α : ℝ)
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (P : PrincipalPartition p d)
    (ν : Fin d → ℝ) (J : Finset (Fin d)) :
    ∀ᵐ X ∂TauCeti.Probability.nonsingularWishartMeasure α Sigma,
      0 < principalMomentIntegrand P ν J X := by
  filter_upwards [TauCeti.Probability.ae_posDef_nonsingularWishartMeasure α Sigma]
    with X hX
  exact principalMomentIntegrand_pos P ν J X hX

/-- The entrywise condition in the target is exactly vanishing of every active
off-diagonal covariance block as a matrix. -/
theorem independentActiveScaleBlocks_iff {p d : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (P : PrincipalPartition p d)
    (ν : Fin d → ℝ) :
    independentActiveScaleBlocks Sigma P ν ↔
      ∀ i j : Fin d, i ≠ j → 0 < ν i → 0 < ν j →
        Sigma.submatrix (fun a : P.block i => (a : Fin p))
          (fun b : P.block j => (b : Fin p)) = 0 := by
  constructor
  · intro h i j hij hi hj
    ext a b
    exact h i j hij hi hj a a.property b b.property
  · intro h i j hij hi hj a ha b hb
    have hm := congrArg
      (fun M : Matrix (P.block i) (P.block j) ℝ => M ⟨a, ha⟩ ⟨b, hb⟩)
      (h i j hij hi hj)
    exact hm

theorem eq_endpoints_iff_eq_throughout {a b c : ℝ} (hcb : c ≤ b) (hba : b ≤ a) :
    a = c ↔ a = b ∧ b = c := by
  constructor
  · intro hac
    have hbc : b = c := le_antisymm (hac ▸ hba) hcb
    exact ⟨hac.trans hbc.symm, hbc⟩
  · rintro ⟨hab, hbc⟩
    exact hab.trans hbc

/-- Under the inequalities in the target, endpoint equality is equivalent to
equality in both inequalities for every selected block. This is precisely the
paper's "equality throughout" formulation. -/
theorem principalEndpointEquality_iff_throughout {p d : ℕ} (hd : 0 < d)
    (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (P : PrincipalPartition p d) (ν : Fin d → ℝ)
    (hchain : ∀ j : Fin d,
      principalMoment α Sigma P ν {j} *
          principalMoment α Sigma P ν (Finset.univ.erase j) ≤
        principalMoment α Sigma P ν Finset.univ ∧
      (∏ i : Fin d, principalMoment α Sigma P ν {i}) ≤
        principalMoment α Sigma P ν {j} *
          principalMoment α Sigma P ν (Finset.univ.erase j)) :
    (principalMoment α Sigma P ν Finset.univ =
        ∏ i : Fin d, principalMoment α Sigma P ν {i}) ↔
      ∀ j : Fin d,
        principalMoment α Sigma P ν Finset.univ =
            principalMoment α Sigma P ν {j} *
              principalMoment α Sigma P ν (Finset.univ.erase j) ∧
        principalMoment α Sigma P ν {j} *
            principalMoment α Sigma P ν (Finset.univ.erase j) =
          ∏ i : Fin d, principalMoment α Sigma P ν {i} := by
  constructor
  · intro h j
    exact (eq_endpoints_iff_eq_throughout (hchain j).2 (hchain j).1).mp h
  · intro h
    exact (h ⟨0, hd⟩).1.trans (h ⟨0, hd⟩).2

end WishartVerification
end
end CanonicalSource9

section CanonicalSource10
/- Source: Wishart/SelectedReindexing.lean -/



/-!
# Arbitrary selected principal blocks in regression coordinates

The finite equivalence puts precisely the chosen index set first and its
complement second. Reindexing preserves all principal determinants, while
subsequent whitening changes only the chosen determinant by its scale factor.
The final measure identity applies to every admissible real Wishart degree.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace Wishart

abbrev selectedDimension {p : ℕ} (I : Finset (Fin p)) : ℕ := Fintype.card I

abbrev complementDimension {p : ℕ} (I : Finset (Fin p)) : ℕ :=
  Fintype.card {a : Fin p // a ∉ I}

def selectedCoordinatesEquiv {p : ℕ} (I : Finset (Fin p)) :
    Fin (selectedDimension I + complementDimension I) ≃ Fin p :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr (Fintype.equivFin I).symm
      (Fintype.equivFin {a : Fin p // a ∉ I}).symm).trans
        (Equiv.sumCompl (fun a : Fin p => a ∈ I)))

theorem selectedDimension_add_complementDimension {p : ℕ} (I : Finset (Fin p)) :
    selectedDimension I + complementDimension I = p := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (selectedCoordinatesEquiv I)

@[simp] theorem selectedCoordinatesEquiv_castAdd {p : ℕ} (I : Finset (Fin p))
    (i : Fin (selectedDimension I)) :
    selectedCoordinatesEquiv I (Fin.castAdd (complementDimension I) i) =
      ((Fintype.equivFin I).symm i : Fin p) := by
  simp [selectedCoordinatesEquiv]

@[simp] theorem selectedCoordinatesEquiv_natAdd {p : ℕ} (I : Finset (Fin p))
    (i : Fin (complementDimension I)) :
    selectedCoordinatesEquiv I (Fin.natAdd (selectedDimension I) i) =
      ((Fintype.equivFin {a : Fin p // a ∉ I}).symm i : Fin p) := by
  simp [selectedCoordinatesEquiv]

theorem selectedCoordinatesEquiv_castAdd_mem {p : ℕ} (I : Finset (Fin p))
    (i : Fin (selectedDimension I)) :
    selectedCoordinatesEquiv I (Fin.castAdd (complementDimension I) i) ∈ I := by
  rw [selectedCoordinatesEquiv_castAdd]
  exact ((Fintype.equivFin I).symm i).property

theorem selectedCoordinatesEquiv_natAdd_notMem {p : ℕ} (I : Finset (Fin p))
    (i : Fin (complementDimension I)) :
    selectedCoordinatesEquiv I (Fin.natAdd (selectedDimension I) i) ∉ I := by
  rw [selectedCoordinatesEquiv_natAdd]
  exact ((Fintype.equivFin {a : Fin p // a ∉ I}).symm i).property

/-- Reindexing a finite principal index set leaves its determinant unchanged. -/
theorem principalMinor_map_equiv {p k : ℕ} (e : Fin k ≃ Fin p)
    (J : Finset (Fin k)) (X : SymmetricMatrix p) :
    WishartVerification.principalMinor (J.map e.toEmbedding) X =
      WishartVerification.principalMinor J (principalSymmetricBlock e X) := by
  have h := WishartVerification.principalMinor_eq_det_enumeration
    (J.map e.toEmbedding) X (Finset.equivMap e.toEmbedding J)
  simpa only [WishartVerification.principalMinor, principalSymmetricBlock,
    Matrix.submatrix_submatrix, Function.comp_def, Finset.equivMap, Equiv.ofBijective_apply,
    Equiv.toEmbedding_apply] using h

theorem selectedCoordinates_leadingDeterminant {p : ℕ} (I : Finset (Fin p))
    (X : SymmetricMatrix p) :
    ((principalSymmetricBlock (Fin.castAdd (complementDimension I))
        (principalSymmetricBlock (selectedCoordinatesEquiv I) X) :
          SymmetricMatrix (selectedDimension I)) :
            Matrix (Fin (selectedDimension I)) (Fin (selectedDimension I)) ℝ).det =
      WishartVerification.principalMinor I X := by
  have h := WishartVerification.principalMinor_eq_det_enumeration I X
    (Fintype.equivFin I).symm
  simpa only [principalSymmetricBlock, Matrix.submatrix_submatrix, Function.comp_def,
    selectedCoordinatesEquiv_castAdd] using h.symm

theorem selectedCoordinates_leadingScaleDeterminant {p : ℕ} (I : Finset (Fin p))
    (S : Matrix (Fin p) (Fin p) ℝ) :
    (leadingScale (selectedDimension I) (complementDimension I)
      (S.submatrix (selectedCoordinatesEquiv I) (selectedCoordinatesEquiv I))).det =
      (S.submatrix (fun i : I => (i : Fin p)) (fun i : I => (i : Fin p))).det := by
  have h := Matrix.det_submatrix_equiv_self (Fintype.equivFin I).symm
    (S.submatrix (fun i : I => (i : Fin p)) (fun i : I => (i : Fin p)))
  simpa only [leadingScale, Matrix.submatrix_submatrix, Function.comp_def,
    selectedCoordinatesEquiv_castAdd] using h

def normalizedSelectedMatrix {p : ℕ} (I : Finset (Fin p))
    (S : Matrix (Fin p) (Fin p) ℝ) (X : SymmetricMatrix p) :
    SymmetricMatrix (selectedDimension I + complementDimension I) :=
  Matrix.symmetricCongruenceLinearMap
    (selectedWhitening (selectedDimension I) (complementDimension I)
      (S.submatrix (selectedCoordinatesEquiv I) (selectedCoordinatesEquiv I)))
    (principalSymmetricBlock (selectedCoordinatesEquiv I) X)

@[fun_prop] theorem measurable_normalizedSelectedMatrix {p : ℕ}
    (I : Finset (Fin p)) (S : Matrix (Fin p) (Fin p) ℝ) :
    Measurable (normalizedSelectedMatrix I S) := by
  unfold normalizedSelectedMatrix
  exact (LinearMap.continuous_of_finiteDimensional _).measurable.comp
    (measurable_principalSymmetricBlock _)

/-- Exact regression-scale law after selecting any principal block and
whitening it. The shape is the original real shape, without a restriction to
integer Gaussian Gram models. -/
theorem map_normalizedSelectedMatrix_nonsingularWishartMeasure
    {p : ℕ} {n : ℝ} (I : Finset (Fin p))
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (hn : (p : ℝ) - 1 < n) :
    (nonsingularWishartMeasure n S).map (normalizedSelectedMatrix I S) =
      nonsingularWishartMeasure n
        (regressionScale
          (normalizedCrossScale (selectedDimension I) (complementDimension I)
            (S.submatrix (selectedCoordinatesEquiv I) (selectedCoordinatesEquiv I)))
          (selectedSchurScale (selectedDimension I) (complementDimension I)
            (S.submatrix (selectedCoordinatesEquiv I) (selectedCoordinatesEquiv I)))) := by
  change Measure.map
    (Matrix.symmetricCongruenceLinearMap
      (selectedWhitening (selectedDimension I) (complementDimension I)
        (S.submatrix (selectedCoordinatesEquiv I) (selectedCoordinatesEquiv I))) ∘
      principalSymmetricBlock (selectedCoordinatesEquiv I))
    (nonsingularWishartMeasure n S) = _
  rw [← Measure.map_map (LinearMap.continuous_of_finiteDimensional _).measurable
    (measurable_principalSymmetricBlock _),
    map_principalSymmetricBlock_nonsingularWishartMeasure
      (selectedCoordinatesEquiv I) (selectedCoordinatesEquiv I).injective hS hn,
    map_selectedWhitening_nonsingularWishartMeasure n
      (hS.submatrix (selectedCoordinatesEquiv I).injective)]

/-- The selected determinant has precisely its original covariance minor as
the fixed normalization factor. -/
theorem normalizedSelectedMatrix_selectedDeterminant
    {p : ℕ} (I : Finset (Fin p))
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (X : SymmetricMatrix p) :
    ((principalSymmetricBlock (Fin.castAdd (complementDimension I))
      (normalizedSelectedMatrix I S X) : SymmetricMatrix (selectedDimension I)) :
        Matrix (Fin (selectedDimension I)) (Fin (selectedDimension I)) ℝ).det =
      (S.submatrix (fun i : I => (i : Fin p)) (fun i : I => (i : Fin p))).det⁻¹ *
        WishartVerification.principalMinor I X := by
  have h := selectedWhitening_selectedDeterminant
    (hS.submatrix (selectedCoordinatesEquiv I).injective)
    (principalSymmetricBlock (selectedCoordinatesEquiv I) X)
  rw [selectedCoordinates_leadingScaleDeterminant, selectedCoordinates_leadingDeterminant] at h
  exact h

def complementCoordinates {p : ℕ} (I : Finset (Fin p)) {ι : Type*}
    (f : ι → Fin p) (hf : ∀ i, f i ∉ I) : ι → Fin (complementDimension I) :=
  fun i => Fintype.equivFin {a : Fin p // a ∉ I} ⟨f i, hf i⟩

@[simp] theorem selectedCoordinates_complementCoordinates {p : ℕ}
    (I : Finset (Fin p)) {ι : Type*} (f : ι → Fin p) (hf : ∀ i, f i ∉ I) (i : ι) :
    selectedCoordinatesEquiv I
      (Fin.natAdd (selectedDimension I) (complementCoordinates I f hf i)) = f i := by
  simp [complementCoordinates]

/-- Every principal submatrix whose coordinates lie outside the selected set
is unchanged after reindexing and whitening, when its indices are transported
by the displayed finite coordinate map. This covers every other block of the
original principal partition. -/
theorem normalizedSelectedMatrix_complementarySubmatrix {p : ℕ}
    (I : Finset (Fin p)) (S : Matrix (Fin p) (Fin p) ℝ) (X : SymmetricMatrix p)
    {ι : Type*} (f : ι → Fin p) (hf : ∀ i, f i ∉ I) :
    ((normalizedSelectedMatrix I S X :
        SymmetricMatrix (selectedDimension I + complementDimension I)) :
          Matrix (Fin (selectedDimension I + complementDimension I))
            (Fin (selectedDimension I + complementDimension I)) ℝ).submatrix
              (Fin.natAdd (selectedDimension I) ∘ complementCoordinates I f hf)
              (Fin.natAdd (selectedDimension I) ∘ complementCoordinates I f hf) =
      (X : Matrix (Fin p) (Fin p) ℝ).submatrix f f := by
  have h := selectedWhitening_remainingSubmatrix
    (S.submatrix (selectedCoordinatesEquiv I) (selectedCoordinatesEquiv I))
    (principalSymmetricBlock (selectedCoordinatesEquiv I) X) (complementCoordinates I f hf)
  simpa only [normalizedSelectedMatrix, principalSymmetricBlock,
    Matrix.submatrix_submatrix, Function.comp_def,
    selectedCoordinates_complementCoordinates] using h

end Wishart
end
end CanonicalSource10

section CanonicalSource11
/- Source: Wishart/AllMoments.lean -/



/-!
# Closure of finite moments under determinant products

This file proves a distribution-independent integrability result used for the
finiteness assertion of the Wishart paper. It does not assert any correlation
inequality. In particular, `HasAllFiniteMoments` is only a convenient name for
membership in every finite Lp space; it carries no positivity or independence
assumption.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace WishartVerification

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def HasAllFiniteMoments (f : Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp f p μ

namespace HasAllFiniteMoments

variable {f g : Ω → ℝ}

theorem comp_measurePreserving {Ξ : Type*} [MeasurableSpace Ξ]
    {ν : Measure Ξ} {h : Ξ → ℝ} (hh : HasAllFiniteMoments h ν)
    {T : Ω → Ξ} (hT : MeasurePreserving T μ ν) :
    HasAllFiniteMoments (h ∘ T) μ := by
  intro p hp
  exact (hh p hp).comp_measurePreserving hT

theorem integrable (hf : HasAllFiniteMoments f μ) : Integrable f μ :=
  memLp_one_iff_integrable.mp (hf 1 (by simp))

theorem const [IsFiniteMeasure μ] (c : ℝ) :
    HasAllFiniteMoments (fun _ : Ω => c) μ := by
  intro p hp
  exact memLp_const c

theorem add (hf : HasAllFiniteMoments f μ) (hg : HasAllFiniteMoments g μ) :
    HasAllFiniteMoments (fun x => f x + g x) μ := by
  intro p hp
  exact (hf p hp).add (hg p hp)

theorem const_mul (hf : HasAllFiniteMoments f μ) (c : ℝ) :
    HasAllFiniteMoments (fun x => c * f x) μ := by
  intro p hp
  exact (hf p hp).const_mul c

theorem mul (hf : HasAllFiniteMoments f μ) (hg : HasAllFiniteMoments g μ) :
    HasAllFiniteMoments (fun x => f x * g x) μ := by
  intro p hp
  letI : ENNReal.HolderTriple (2 * p) (2 * p) p := by
    constructor
    rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by simp)),
      ← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
  exact (hf (2 * p) (by finiteness)).mul (hg (2 * p) (by finiteness))

theorem finset_prod [IsFiniteMeasure μ] {ι : Type*} (s : Finset ι)
    (f : ι → Ω → ℝ) (hf : ∀ i ∈ s, HasAllFiniteMoments (f i) μ) :
    HasAllFiniteMoments (fun x => ∏ i ∈ s, f i x) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (μ := μ) 1
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).mul
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → Ω → ℝ) (hf : ∀ i ∈ s, HasAllFiniteMoments (f i) μ) :
    HasAllFiniteMoments (fun x => ∑ i ∈ s, f i x) μ := by
  intro p hp
  exact memLp_finsetSum s (fun i hi => hf i hi p hp)

theorem matrix_left_mul_entry {m n k : Type*} [Fintype n]
    (A : Ω → Matrix n k ℝ) (M : Matrix m n ℝ)
    (hA : ∀ i j, HasAllFiniteMoments (fun x => A x i j) μ) (i : m) (j : k) :
    HasAllFiniteMoments (fun x => (M * A x) i j) μ := by
  simp only [Matrix.mul_apply]
  exact finset_sum Finset.univ _ fun a _ => (hA a j).const_mul (M i a)

theorem matrix_right_mul_entry {m n k : Type*} [Fintype n]
    (A : Ω → Matrix m n ℝ) (M : Matrix n k ℝ)
    (hA : ∀ i j, HasAllFiniteMoments (fun x => A x i j) μ) (i : m) (j : k) :
    HasAllFiniteMoments (fun x => (A x * M) i j) μ := by
  have h := finset_sum Finset.univ (fun a x => M a j * A x i a)
    (fun a _ => (hA i a).const_mul (M a j))
  simpa only [Matrix.mul_apply, mul_comm] using h

theorem abs_rpow [IsFiniteMeasure μ] (hf : HasAllFiniteMoments f μ)
    {a : ℝ} (ha : 0 ≤ a) :
    HasAllFiniteMoments (fun x => |f x| ^ a) μ := by
  rcases ha.eq_or_lt with rfl | ha
  · simpa using const (μ := μ) 1
  intro p hp
  let q : ℝ≥0∞ := ENNReal.ofReal a
  have hq0 : q ≠ 0 := by simpa [q] using ha
  have hqtop : q ≠ ∞ := by simp [q]
  have hmem := hf (p * q) (ENNReal.mul_ne_top hp hqtop)
  have hrpow := hmem.norm_rpow_div q
  convert hrpow using 1
  · ext x
    simp [q, ENNReal.toReal_ofReal ha.le, Real.norm_eq_abs]
  · exact (ENNReal.mul_div_cancel_right hq0 hqtop).symm

theorem rpow [IsFiniteMeasure μ] (hf : HasAllFiniteMoments f μ)
    {a : ℝ} (ha : 0 ≤ a) :
    HasAllFiniteMoments (fun x => f x ^ a) μ := by
  intro p hp
  apply (hf.abs_rpow ha p hp).mono'
  · exact ((hf p hp).aestronglyMeasurable.aemeasurable.pow
      aemeasurable_const).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using Real.abs_rpow_le_abs_rpow (f x) a

theorem det [IsFiniteMeasure μ] {n : Type*} [Fintype n] [DecidableEq n]
    (A : Ω → Matrix n n ℝ)
    (hA : ∀ i j, HasAllFiniteMoments (fun x => A x i j) μ) :
    HasAllFiniteMoments (fun x => (A x).det) μ := by
  simp only [Matrix.det_apply']
  exact finset_sum Finset.univ _ (fun σ _ =>
    (finset_prod Finset.univ _ (fun i _ => hA (σ i) i)).const_mul _)

end HasAllFiniteMoments

end WishartVerification
end
end CanonicalSource11

section CanonicalSource12
/- Source: Wishart/MomentTransport.lean -/



open scoped Classical
open MeasureTheory

/-!
# Transporting moments through a proved law identity and a nonzero scale

These lemmas retain the actual source and target measures. The equality of
observables is allowed almost everywhere, which is needed when determinant
powers are identified on the positive-definite Wishart support.
-/

namespace WishartVerification

variable {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]

theorem HasAllFiniteMoments.congr_ae {μ : Measure Ω} {f g : Ω → ℝ}
    (hf : HasAllFiniteMoments f μ) (hfg : f =ᵐ[μ] g) : HasAllFiniteMoments g μ :=
  fun p hp ↦ (memLp_congr_ae hfg).mp (hf p hp)

theorem HasAllFiniteMoments.of_comp_measurePreserving
    {μ : Measure Ω} {ν : Measure Ψ} {T : Ω → Ψ} (hT : MeasurePreserving T μ ν)
    {g : Ψ → ℝ} (hgm : Measurable g) (hg : HasAllFiniteMoments (g ∘ T) μ) :
    HasAllFiniteMoments g ν := by
  intro p hp
  rw [← hT.map_eq]
  exact (memLp_map_measure_iff hgm.aestronglyMeasurable hT.measurable.aemeasurable).mpr (hg p hp)

theorem allFiniteMoments_of_scaled_pullback
    {μ : Measure Ω} {ν : Measure Ψ} {T : Ω → Ψ} (hT : MeasurePreserving T μ ν)
    (f : Ω → ℝ) (g : Ψ → ℝ) (c : ℝ) (hc : c ≠ 0) (hgm : Measurable g)
    (hf : HasAllFiniteMoments f μ)
    (heq : f =ᵐ[μ] fun x ↦ c * g (T x)) : HasAllFiniteMoments g ν := by
  apply HasAllFiniteMoments.of_comp_measurePreserving hT hgm
  apply (hf.const_mul c⁻¹).congr_ae
  filter_upwards [heq] with x hx
  simp only [Function.comp_apply]
  rw [hx, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem integral_eq_scaled_of_pullback
    {μ : Measure Ω} {ν : Measure Ψ} {T : Ω → Ψ} (hT : MeasurePreserving T μ ν)
    (f : Ω → ℝ) (g : Ψ → ℝ) (c : ℝ) (hgm : Measurable g)
    (heq : f =ᵐ[μ] fun x ↦ c * g (T x)) :
    (∫ x, f x ∂μ) = c * ∫ y, g y ∂ν := by
  have hmap : (∫ x, g (T x) ∂μ) = ∫ y, g y ∂ν := by
    rw [← hT.map_eq]
    exact (integral_map_of_stronglyMeasurable hT.measurable hgm.stronglyMeasurable).symm
  rw [integral_congr_ae heq, integral_const_mul, hmap]

end WishartVerification
end CanonicalSource12

section CanonicalSource13
/- Source: Wishart/MomentFiniteness.lean -/



/-!
# Finiteness of arbitrary nonnegative determinant moments

The measure in these results is the density-defined real Wishart measure on the
space of self-adjoint real matrices. The hypotheses explicitly put it in the
nondegenerate probability range: the scale is positive definite and the real
shape is greater than the dimension minus one. Thus none of the assertions
uses the zero-measure default outside the classical parameter range.

The result allows overlapping rectangular compressions, arbitrary real
nonnegative powers, and any finite number of factors. It proves the finiteness
part of the paper's main theorem; it does not assert the product inequality.
-/

noncomputable section

open MeasureTheory Matrix
open TauCeti.Probability
open scoped ENNReal

namespace WishartVerification

variable {p : ℕ} {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}

theorem allFiniteMoments_wishart_entry (i j : Fin p) :
    HasAllFiniteMoments (fun X : SymmetricMatrix p =>
      (X : Matrix (Fin p) (Fin p) ℝ) i j) (nonsingularWishartMeasure α Sigma) := by
  intro q hq
  have h := memLp_coe_apply_nonsingularWishartMeasure Sigma α i j q.toNNReal
  simpa only [ENNReal.coe_toNNReal hq] using h

theorem allFiniteMoments_wishart_compression_entry
    {k : Type*} [Fintype k] (M : Matrix (Fin p) k ℝ) (i j : k) :
    HasAllFiniteMoments (fun X : SymmetricMatrix p =>
      (M.transpose * (X : Matrix (Fin p) (Fin p) ℝ) * M) i j)
      (nonsingularWishartMeasure α Sigma) := by
  exact HasAllFiniteMoments.matrix_right_mul_entry _ M
    (fun a b => HasAllFiniteMoments.matrix_left_mul_entry _ M.transpose
      (fun i j => allFiniteMoments_wishart_entry i j) a b) i j

theorem allFiniteMoments_wishart_compression_det
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    {k : Type*} [Fintype k] [DecidableEq k] (M : Matrix (Fin p) k ℝ) :
    HasAllFiniteMoments (fun X : SymmetricMatrix p =>
      (M.transpose * (X : Matrix (Fin p) (Fin p) ℝ) * M).det)
      (nonsingularWishartMeasure α Sigma) := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure hSigma hα
  exact HasAllFiniteMoments.det _ fun i j =>
    allFiniteMoments_wishart_compression_entry M i j

theorem allFiniteMoments_wishart_affine_compression_det
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    {k : Type*} [Fintype k] [DecidableEq k]
    (B : Matrix k k ℝ) (M : Matrix (Fin p) k ℝ) :
    HasAllFiniteMoments (fun X : SymmetricMatrix p =>
      (B + M.transpose * (X : Matrix (Fin p) (Fin p) ℝ) * M).det)
      (nonsingularWishartMeasure α Sigma) := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure hSigma hα
  apply HasAllFiniteMoments.det
  intro i j
  exact (HasAllFiniteMoments.const (B i j)).add
    (allFiniteMoments_wishart_compression_entry M i j)

theorem allFiniteMoments_wishart_principalMinor
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α) (I : Finset (Fin p)) :
    HasAllFiniteMoments (principalMinor I) (nonsingularWishartMeasure α Sigma) := by
  classical
  letI := isProbabilityMeasure_nonsingularWishartMeasure hSigma hα
  exact HasAllFiniteMoments.det _ fun i j =>
    allFiniteMoments_wishart_entry (α := α) (Sigma := Sigma) (i : Fin p) (j : Fin p)

theorem integrable_principalMomentIntegrand
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    {d : ℕ} (P : PrincipalPartition p d) (ν : Fin d → ℝ)
    (hν : ∀ i, 0 ≤ ν i) (J : Finset (Fin d)) :
    Integrable (principalMomentIntegrand P ν J)
      (nonsingularWishartMeasure α Sigma) := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure hSigma hα
  apply HasAllFiniteMoments.integrable
  apply HasAllFiniteMoments.finset_prod J
  intro i hi
  exact (allFiniteMoments_wishart_principalMinor hSigma hα (P.block i)).rpow (hν i)

theorem integrable_compression_determinant_product
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    {ι : Type*} (J : Finset ι) (k : ι → Type*)
    [∀ i, Fintype (k i)] [∀ i, DecidableEq (k i)]
    (M : ∀ i, Matrix (Fin p) (k i) ℝ) (ν : ι → ℝ)
    (hν : ∀ i ∈ J, 0 ≤ ν i) :
    Integrable (fun X : SymmetricMatrix p =>
      ∏ i ∈ J, ( (M i).transpose *
        (X : Matrix (Fin p) (Fin p) ℝ) * M i ).det ^ ν i)
      (nonsingularWishartMeasure α Sigma) := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure hSigma hα
  exact (HasAllFiniteMoments.finset_prod J _ fun i hi =>
    (allFiniteMoments_wishart_compression_det hSigma hα (M i)).rpow (hν i hi)).integrable

end WishartVerification
end
end CanonicalSource13

section CanonicalSource14
/- Source: Wishart/SmoothPositivePowers.lean -/



/-!
# Smooth polynomial-growth extensions of positive real powers

For every positive threshold `a` and every real exponent, the extension below
equals the ordinary real power on `[a,∞)`.  It is smooth on the whole real line
and all its derivatives have polynomial growth.  This lets the radial argument
use the actual regularized determinant power on the positive cone while using
globally smooth tests in its integration identities.

The estimate for powers on `(1/2,∞)` generalizes the argument in Mathlib's
`hasTemperateGrowth_one_add_norm_sq_rpow` (Apache-2.0, Moritz Doll, Anatole
Dedecker, Sébastien Gouëzel).
-/

noncomputable section

open Filter Topology Function
open scoped ContDiff

namespace WishartVerification

theorem hasCompactSupport_fderiv_smoothTransition :
    HasCompactSupport (fderiv ℝ Real.smoothTransition) := by
  apply HasCompactSupport.intro (K := Set.Icc (0 : ℝ) 1) isCompact_Icc
  intro x hx
  have hx' : x < 0 ∨ 1 < x := by
    by_cases hx0 : x < 0
    · exact Or.inl hx0
    · apply Or.inr
      by_contra hx1
      exact hx ⟨le_of_not_gt hx0, le_of_not_gt hx1⟩
  rcases hx' with hleft | hright
  · have he : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [Iio_mem_nhds hleft] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    simpa using he.fderiv_eq (𝕜 := ℝ)
  · have he : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      filter_upwards [Ioi_mem_nhds hright] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    simpa using he.fderiv_eq (𝕜 := ℝ)

theorem hasTemperateGrowth_smoothTransition : Real.smoothTransition.HasTemperateGrowth := by
  have hsmooth : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  apply Function.HasTemperateGrowth.of_fderiv
    (hasCompactSupport_fderiv_smoothTransition.hasTemperateGrowth
      ((contDiff_infty_iff_fderiv.mp hsmooth).2))
    (hsmooth.differentiable (by simp)) (k := 0) (C := 1)
  intro x
  simpa [Real.norm_of_nonneg (Real.smoothTransition.nonneg x)] using Real.smoothTransition.le_one x

def smoothPositiveClamp (x : ℝ) : ℝ :=
  1 + (x - 1) * Real.smoothTransition (x - 1)

theorem one_le_smoothPositiveClamp (x : ℝ) : 1 ≤ smoothPositiveClamp x := by
  by_cases hx : x ≤ 1
  · simp [smoothPositiveClamp, Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hx)]
  · dsimp [smoothPositiveClamp]
    exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr (not_le.mp hx).le)
      (Real.smoothTransition.nonneg _))

theorem smoothPositiveClamp_eq {x : ℝ} (hx : 2 ≤ x) : smoothPositiveClamp x = x := by
  rw [smoothPositiveClamp, Real.smoothTransition.one_of_one_le (by linarith)]
  ring

theorem hasTemperateGrowth_smoothPositiveClamp : smoothPositiveClamp.HasTemperateGrowth := by
  have hid : (fun x : ℝ => x - 1).HasTemperateGrowth := by fun_prop
  exact (Function.HasTemperateGrowth.const 1).add
    (hid.mul (hasTemperateGrowth_smoothTransition.comp hid))

theorem hasTemperateGrowth_rpow_of_half_lt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : f.HasTemperateGrowth)
    (hpos : ∀ x, (1 : ℝ) / 2 < f x) (r : ℝ) :
    (fun x => f x ^ r).HasTemperateGrowth := by
  let t : Set ℝ := Set.Ioi (1 / 2)
  have ht : Set.range f ⊆ t := by rintro _ ⟨x, rfl⟩; exact hpos x
  have hunique : UniqueDiffOn ℝ t := isOpen_Ioi.uniqueDiffOn
  have hdiff : ContDiffOn ℝ ∞ (fun x : ℝ => x ^ r) t :=
    contDiffOn_fun_id.rpow_const_of_ne fun x hx => (lt_trans (by norm_num) hx).ne'
  apply Function.HasTemperateGrowth.comp' ht hunique hdiff _ hf
  intro N
  obtain ⟨k, hk⟩ := exists_nat_ge (max r ((N - r) * Real.log 2 / Real.log (3 / 2)))
  have hk₁ : r ≤ k := le_max_left _ _ |>.trans hk
  have hk₂ : Real.log 2 * (N - r) ≤ Real.log (3 / 2) * k := by
    have hlog : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
    have h := (le_max_right r ((N - r) * Real.log 2 / Real.log (3 / 2))).trans hk
    have h' := (div_le_iff₀ hlog).mp h
    nlinarith
  refine ⟨k, ∑ j ∈ Finset.range (N + 1), ‖Polynomial.eval r (descPochhammer ℝ j)‖,
    by positivity, ?_⟩
  intro n hn x hx
  have hx' : 1 / 2 < x := hx
  have hxpos : 0 < x := lt_trans (by norm_num) hx'
  have hdiffx : ContDiffAt ℝ n (fun x : ℝ => x ^ r) x :=
    Real.contDiffAt_rpow_const (Or.inl hxpos.ne')
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedDerivWithin_eq_iteratedDeriv hunique hdiffx hx, iteratedDeriv_eq_iterate,
    Real.iter_deriv_rpow_const, norm_mul]
  gcongr 1
  · apply Finset.single_le_sum
      (fun j _ => norm_nonneg (Polynomial.eval r (descPochhammer ℝ j)))
      (show n ∈ Finset.range (N + 1) by simp; omega)
  · simp only [Real.norm_eq_abs]
    apply (Real.abs_rpow_le_abs_rpow _ _).trans
    by_cases h : 0 ≤ r - n
    · have hnk : r - n ≤ k := by nlinarith
      rw [← Real.rpow_natCast]
      exact (Real.rpow_le_rpow (abs_nonneg x) (by simp) h).trans
        (Real.rpow_le_rpow_of_exponent_le (by simp) hnk)
    · have hnr : 0 < n - r := by linarith
      calc
        |x| ^ (r - n) = x ^ (-(n - r)) := by rw [abs_of_pos hxpos]; congr 1 <;> ring
        _ ≤ (2 : ℝ) ^ (n - r) := by
          rw [Real.rpow_neg_eq_inv_rpow]
          gcongr
          exact ((inv_lt_comm₀ hxpos (by norm_num)).mpr
            (by simpa only [one_div] using hx')).le
        _ = Real.exp (Real.log 2 * (n - r)) := by rw [Real.rpow_def_of_pos (by norm_num)]
        _ ≤ Real.exp (Real.log (3 / 2) * k) := by
          apply Real.exp_le_exp.mpr
          have hn' : (n : ℝ) ≤ N := by exact_mod_cast hn
          have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
          nlinarith [hk₂]
        _ = (3 / 2 : ℝ) ^ k := by rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
        _ ≤ (1 + |x|) ^ k := by gcongr; rw [abs_of_pos hxpos]; linarith

def smoothPositivePower (a r x : ℝ) : ℝ :=
  (a / 2) ^ r * smoothPositiveClamp (2 * x / a) ^ r

theorem hasTemperateGrowth_smoothPositivePower {a : ℝ} (ha : 0 < a) (r : ℝ) :
    (smoothPositivePower a r).HasTemperateGrowth := by
  have hscale : (fun x : ℝ => 2 * x / a).HasTemperateGrowth := by
    simpa only [div_eq_mul_inv, Pi.mul_def, id_eq] using
      ((Function.HasTemperateGrowth.const (2 : ℝ)).mul
        Function.HasTemperateGrowth.id).mul (Function.HasTemperateGrowth.const a⁻¹)
  have hc : (fun x : ℝ => smoothPositiveClamp (2 * x / a)).HasTemperateGrowth :=
    hasTemperateGrowth_smoothPositiveClamp.comp hscale
  exact (Function.HasTemperateGrowth.const _).mul
    (hasTemperateGrowth_rpow_of_half_lt hc (fun x => by
      have := one_le_smoothPositiveClamp (2 * x / a); linarith) r)

theorem smoothPositivePower_eq {a x : ℝ} (ha : 0 < a) (hx : a ≤ x) (r : ℝ) :
    smoothPositivePower a r x = x ^ r := by
  have hx0 : 0 < x := ha.trans_le hx
  have hx2 : 2 ≤ 2 * x / a := (le_div_iff₀ ha).mpr (by linarith)
  rw [smoothPositivePower, smoothPositiveClamp_eq hx2,
    ← Real.mul_rpow (by positivity : 0 ≤ a / 2) (by positivity : 0 ≤ 2 * x / a)]
  congr 1
  field_simp

end WishartVerification
end
end CanonicalSource14

section CanonicalSource15
/- Source: Wishart/GeneratorAlgebra.lean -/



/-!
# The algebra of the Wishart diffusion operator

These are finite-dimensional identities in arbitrary dimension. The two inputs
to `driftDiffusion` are explicitly the first and second differential forms.
The connection with actual Fréchet derivatives of logarithmic determinants is
made in the calculus modules; this file contains only their matrix algebra.
-/

noncomputable section

open Matrix Finset
open scoped BigOperators Matrix

namespace WishartVerification

variable {n : Type*} [Fintype n] [DecidableEq n]

def symRankOne (v w : n → ℝ) : Matrix n n ℝ :=
  Matrix.vecMulVec v w + Matrix.vecMulVec w v

def driftDiffusion (N : ℝ) (v : n → ℝ) (V : Matrix n n ℝ)
    (D : Matrix n n ℝ → ℝ) (D₂ : Matrix n n ℝ → Matrix n n ℝ → ℝ) : ℝ :=
  2 * N * D (Matrix.vecMulVec v v) +
    ∑ i, ∑ j, V i j * D₂ (symRankOne v (Pi.single i 1))
      (symRankOne v (Pi.single j 1))

theorem trace_mul_rankOne (A : Matrix n n ℝ) (v w : n → ℝ) :
    Matrix.trace (A * Matrix.vecMulVec v w) = w ⬝ᵥ (A *ᵥ v) := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

theorem trace_mul_symRankOne {A : Matrix n n ℝ} (hA : A.IsSymm)
    (v w : n → ℝ) :
    Matrix.trace (A * symRankOne v w) = 2 * (w ⬝ᵥ (A *ᵥ v)) := by
  rw [symRankOne, Matrix.mul_add, Matrix.trace_add,
    trace_mul_rankOne, trace_mul_rankOne,
    hA.dotProduct_mulVec_comm (x := v) (y := w)]
  ring

theorem trace_mul_symRankOne_mul_symRankOne {A : Matrix n n ℝ}
    (hA : A.IsSymm) (v u w : n → ℝ) :
    Matrix.trace (A * symRankOne v u * A * symRankOne v w) =
      2 * ((v ⬝ᵥ (A *ᵥ v)) * (u ⬝ᵥ (A *ᵥ w)) +
        (u ⬝ᵥ (A *ᵥ v)) * (w ⬝ᵥ (A *ᵥ v))) := by
  rw [Matrix.mul_assoc (A * symRankOne v u) A (symRankOne v w)]
  simp only [symRankOne, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.add_mulVec, Matrix.vecMulVec_mulVec, add_dotProduct, smul_dotProduct,
    Matrix.trace_add, Matrix.trace_smul, Matrix.trace_vecMulVec,
    smul_eq_mul]
  try simp only [dotProduct_comm (A *ᵥ v) w, dotProduct_comm (A *ᵥ v) v,
    dotProduct_comm (A *ᵥ u) w, dotProduct_comm (A *ᵥ u) v]
  rw [hA.dotProduct_mulVec_comm (x := w) (y := u),
    hA.dotProduct_mulVec_comm (x := v) (y := u),
    hA.dotProduct_mulVec_comm (x := v) (y := w)]
  simp only [op_smul_eq_smul, smul_eq_mul]
  ring

theorem trace_mul_eq_sum_entries {A : Matrix n n ℝ} (hA : A.IsSymm)
    (V : Matrix n n ℝ) :
    Matrix.trace (A * V) = ∑ i, ∑ j, V i j * A i j := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hA.apply j i, mul_comm]

theorem driftDiffusion_logdet_forms {A : Matrix n n ℝ}
    (hA : A.IsSymm) (N : ℝ) (v : n → ℝ) (V : Matrix n n ℝ) :
    driftDiffusion N v V
      (fun H => Matrix.trace (A * H))
      (fun H K => -Matrix.trace (A * H * A * K)) =
        2 * (N - Matrix.trace (A * V)) * (v ⬝ᵥ (A *ᵥ v)) -
          2 * ((A *ᵥ v) ⬝ᵥ (V *ᵥ (A *ᵥ v))) := by
  simp only [driftDiffusion, trace_mul_rankOne,
    trace_mul_symRankOne_mul_symRankOne hA,
    single_dotProduct, one_mul, Matrix.mulVec_single, MulOpposite.op_one, one_smul,
    Matrix.col_apply, Pi.smul_apply, smul_eq_mul]
  rw [trace_mul_eq_sum_entries hA]
  simp only [mul_neg, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have hfirst : (∑ i, ∑ j, V i j *
      (2 * ((v ⬝ᵥ (A *ᵥ v)) * A i j))) =
      2 * (v ⬝ᵥ (A *ᵥ v)) * (∑ i, ∑ j, V i j * A i j) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hsecond (a : n → ℝ) : (∑ i, ∑ j, V i j *
      (2 * (a i * a j))) = 2 * (a ⬝ᵥ (V *ᵥ a)) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hfirst, hsecond]
  ring

end WishartVerification
end
end CanonicalSource15

section CanonicalSource16
/- Source: Wishart/ContractionBounds.lean -/



/-!
# Bounds for compressed logarithmic determinants

For `Q > 0` and `Q - Mᵀ V M ≥ 0`, the matrix `A = M Q⁻¹ Mᵀ`
satisfies `tr(A V) ≤ dim(Q)` and `A V A ≤ A`. These are the two
estimates used in the paper's radial generator calculation. No matrix-order
assumption is encoded as entrywise inequalities: all order hypotheses below
are genuine positive semidefiniteness assertions.
-/

noncomputable section

open Matrix
open scoped Matrix MatrixOrder

namespace WishartVerification

variable {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]

theorem trace_mul_nonneg_of_posSemidef {A B : Matrix k k ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ Matrix.trace (A * B) := by
  have hroot : (CFC.sqrt A).PosSemidef := Matrix.LE.le.posSemidef (CFC.sqrt_nonneg A)
  have h := (hB.conjTranspose_mul_mul_same (CFC.sqrt A)).trace_nonneg
  rw [hroot.isHermitian.eq, hA.trace_sqrt_mul_mul_sqrt, Matrix.trace_mul_comm] at h
  exact h

theorem trace_inverse_mul_le_card {Q T : Matrix k k ℝ}
    (hQ : Q.PosDef) (hQT : (Q - T).PosSemidef) :
    Matrix.trace (Q⁻¹ * T) ≤ Fintype.card k := by
  have h := trace_mul_nonneg_of_posSemidef hQ.inv.posSemidef hQT
  have hdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ.isUnit
  rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.nonsing_inv_mul Q hdet,
    Matrix.trace_one] at h
  linarith

theorem compressed_inverse_posSemidef {Q : Matrix k k ℝ}
    (hQ : Q.PosDef) (M : Matrix n k ℝ) :
    (M * Q⁻¹ * M.transpose).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hQ.inv.posSemidef.mul_mul_conjTranspose_same M

theorem compressed_inverse_contraction {Q : Matrix k k ℝ}
    (hQ : Q.PosDef) (M : Matrix n k ℝ) (V : Matrix n n ℝ)
    (hQT : (Q - M.transpose * V * M).PosSemidef) :
    let A := M * Q⁻¹ * M.transpose
    (A - A * V * A).PosSemidef := by
  have hdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ.isUnit
  have h := hQT.mul_mul_conjTranspose_same (M * Q⁻¹)
  have hadj : (M * Q⁻¹).conjTranspose = Q⁻¹ * M.transpose := by
    rw [Matrix.conjTranspose_mul, hQ.inv.isHermitian.eq]
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [hadj, Matrix.mul_sub, Matrix.sub_mul] at h
  convert h using 1 <;>
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left Q _ hdet,
      Matrix.one_mul]

theorem compressed_trace_le_card {Q : Matrix k k ℝ}
    (hQ : Q.PosDef) (M : Matrix n k ℝ) (V : Matrix n n ℝ)
    (hQT : (Q - M.transpose * V * M).PosSemidef) :
    Matrix.trace ((M * Q⁻¹ * M.transpose) * V) ≤ Fintype.card k := by
  have h := trace_inverse_mul_le_card hQ hQT
  convert h using 1
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm M]
  simp only [Matrix.mul_assoc]

theorem quadratic_contraction_bound {A V : Matrix n n ℝ}
    (hA : A.IsSymm) (hC : (A - A * V * A).PosSemidef) (v : n → ℝ) :
    (A *ᵥ v) ⬝ᵥ (V *ᵥ (A *ᵥ v)) ≤ v ⬝ᵥ (A *ᵥ v) := by
  have h := hC.dotProduct_mulVec_nonneg v
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at h
  have hid : v ⬝ᵥ ((A * V * A) *ᵥ v) =
      (A *ᵥ v) ⬝ᵥ (V *ᵥ (A *ᵥ v)) := by
    simp only [← Matrix.mulVec_mulVec]
    rw [hA.dotProduct_mulVec_comm, dotProduct_comm]
  rw [hid] at h
  linarith

theorem logarithmic_generator_lower_bound {A V : Matrix n n ℝ}
    (hA : A.PosSemidef) (hC : (A - A * V * A).PosSemidef)
    {r : ℝ} (htr : Matrix.trace (A * V) ≤ r) (N : ℝ) (v : n → ℝ) :
    2 * (N - r - 1) * (v ⬝ᵥ (A *ᵥ v)) ≤
      2 * (N - Matrix.trace (A * V)) * (v ⬝ᵥ (A *ᵥ v)) -
        2 * ((A *ᵥ v) ⬝ᵥ (V *ᵥ (A *ᵥ v))) := by
  have hb : 0 ≤ v ⬝ᵥ (A *ᵥ v) := by
    simpa only [star_trivial] using hA.dotProduct_mulVec_nonneg v
  have hs : A.IsSymm := by
    simpa only [Matrix.IsHermitian, Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hA.isHermitian
  have hquad := quadratic_contraction_bound hs hC v
  have hprod := mul_nonneg (sub_nonneg.mpr htr) hb
  nlinarith

end WishartVerification
end
end CanonicalSource16

section CanonicalSource17
/- Source: Wishart/LogDetCalculus.lean -/



/-!
# Differential identities for the logarithmic determinant

The formulas here are statements about Mathlib's actual Fréchet derivative,
not definitions of a formal differential operator. They supply the calculus
part of the determinant computation in Section 3 of the Wishart manuscript.
-/

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.Operator

namespace WishartVerification

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev traceCLM : Matrix n n ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap n ℝ ℝ)

def traceLeftCLM (A : Matrix n n ℝ) : Matrix n n ℝ →L[ℝ] ℝ :=
  (traceCLM (n := n)).comp
    (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ A))

@[simp] theorem traceLeftCLM_apply (A H : Matrix n n ℝ) :
    traceLeftCLM A H = Matrix.trace (A * H) := rfl

theorem hasFDerivAt_logdet {A : Matrix n n ℝ} (hA : IsUnit A.det) :
    HasFDerivAt (fun B : Matrix n n ℝ => Real.log B.det)
      (traceLeftCLM A⁻¹) A := by
  have h := (Matrix.hasFDerivAt_det hA).log hA.ne_zero
  have h' : HasFDerivAt (fun B : Matrix n n ℝ => Real.log B.det)
      (A.det⁻¹ • A.det • traceLeftCLM A⁻¹) A := h
  simpa only [smul_smul, inv_mul_cancel₀ hA.ne_zero, one_smul] using h'

theorem fderiv_logdet_apply {A : Matrix n n ℝ} (hA : IsUnit A.det)
    (H : Matrix n n ℝ) :
    fderiv ℝ (fun B : Matrix n n ℝ => Real.log B.det) A H =
      Matrix.trace (A⁻¹ * H) := by
  rw [(hasFDerivAt_logdet hA).fderiv]
  rfl

theorem hasFDerivAt_matrix_inv {A : Matrix n n ℝ} (hA : IsUnit A.det) :
    HasFDerivAt (fun B : Matrix n n ℝ => B⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℝ) A⁻¹ A⁻¹) A := by
  obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det A).mpr hA
  simpa only [Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit] using
    (hasFDerivAt_ringInverse (𝕜 := ℝ) u)

def logdetSecondCLM (A H : Matrix n n ℝ) : Matrix n n ℝ →L[ℝ] ℝ :=
  ((traceCLM (n := n)).comp
    (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ H))).comp
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℝ) A⁻¹ A⁻¹)

@[simp] theorem logdetSecondCLM_apply (A H K : Matrix n n ℝ) :
    logdetSecondCLM A H K = -Matrix.trace (A⁻¹ * K * A⁻¹ * H) := by
  change Matrix.trace ((-(A⁻¹ * K * A⁻¹)) * H) = _
  simp only [Matrix.neg_mul, Matrix.trace_neg]

theorem hasFDerivAt_trace_inverse_mul {A : Matrix n n ℝ}
    (hA : IsUnit A.det) (H : Matrix n n ℝ) :
    HasFDerivAt (fun B : Matrix n n ℝ => Matrix.trace (B⁻¹ * H))
      (logdetSecondCLM A H) A := by
  exact ((traceCLM (n := n)).hasFDerivAt.comp _
    (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ H)).hasFDerivAt).comp _
      (hasFDerivAt_matrix_inv hA)

theorem fderiv_trace_inverse_mul_apply {A : Matrix n n ℝ}
    (hA : IsUnit A.det) (H K : Matrix n n ℝ) :
    fderiv ℝ (fun B : Matrix n n ℝ => Matrix.trace (B⁻¹ * H)) A K =
      -Matrix.trace (A⁻¹ * K * A⁻¹ * H) := by
  rw [(hasFDerivAt_trace_inverse_mul hA H).fderiv]
  exact logdetSecondCLM_apply A H K

theorem hasFDerivAt_logdet_direction {A : Matrix n n ℝ}
    (hA : IsUnit A.det) (H : Matrix n n ℝ) :
    HasFDerivAt
      (fun B : Matrix n n ℝ =>
        fderiv ℝ (fun C : Matrix n n ℝ => Real.log C.det) B H)
      (logdetSecondCLM A H) A := by
  apply (hasFDerivAt_trace_inverse_mul hA H).congr_of_eventuallyEq
  have hnear := Matrix.differentiable_det.continuous.continuousAt.eventually_ne hA.ne_zero
  filter_upwards [hnear] with B hB
  exact fderiv_logdet_apply (isUnit_iff_ne_zero.mpr hB) H

theorem second_fderiv_logdet_apply {A : Matrix n n ℝ}
    (hA : IsUnit A.det) (H K : Matrix n n ℝ) :
    fderiv ℝ
      (fun B : Matrix n n ℝ =>
        fderiv ℝ (fun C : Matrix n n ℝ => Real.log C.det) B H) A K =
      -Matrix.trace (A⁻¹ * K * A⁻¹ * H) := by
  rw [(hasFDerivAt_logdet_direction hA H).fderiv]
  exact logdetSecondCLM_apply A H K

end WishartVerification
end
end CanonicalSource17

section CanonicalSource18
/- Source: Wishart/RegularizedDeterminants.lean -/



/-!
# Smooth extensions of regularized determinant products

The smooth extension equals the ordinary determinant power on the entire
positive semidefinite cone.  Its global polynomial derivative bounds permit
application of the fully justified Gaussian and Wishart Stein identities.
-/

noncomputable section

open Matrix Filter Topology
open scoped Matrix.Norms.Operator

namespace WishartVerification

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasTemperateGrowth_finset_prod {ι : Type*} (s : Finset ι)
    (f : ι → E → ℝ) (hf : ∀ i ∈ s, (f i).HasTemperateGrowth) :
    (fun x => ∏ i ∈ s, f i x).HasTemperateGrowth := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Function.HasTemperateGrowth.const (1 : ℝ)
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).mul
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem hasTemperateGrowth_matrix_det {k : Type*} [Fintype k] [DecidableEq k]
    (A : E → Matrix k k ℝ) (hA : ∀ i j, (fun x => A x i j).HasTemperateGrowth) :
    (fun x => (A x).det).HasTemperateGrowth := by
  simp only [Matrix.det_apply']
  exact Function.HasTemperateGrowth.sum (fun σ _ =>
    (Function.HasTemperateGrowth.const _).mul
      (hasTemperateGrowth_finset_prod Finset.univ _ (fun i _ => hA (σ i) i)))

theorem det_add_epsilon_identity_lower {k : Type*} [Fintype k] [DecidableEq k]
    {B : Matrix k k ℝ} (hB : B.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    ε ^ Fintype.card k ≤ (B + ε • (1 : Matrix k k ℝ)).det := by
  let Q : ℝ → Matrix k k ℝ := fun t => ε • (1 : Matrix k k ℝ) + t • B
  have hQ (t : ℝ) (ht : 0 ≤ t) : (Q t).PosDef :=
    (Matrix.PosDef.one.smul hε).add_posSemidef (hB.smul ht)
  have hd (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt (fun s => (Q s).det) ((Q t).det * Matrix.trace ((Q t)⁻¹ * B)) t := by
    have h := (Matrix.hasFDerivAt_det (isUnit_iff_ne_zero.mpr (hQ t ht).det_pos.ne')).comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const B).const_add (ε • (1 : Matrix k k ℝ)))
    simp only [id_eq, one_smul] at h
    have h' : HasDerivAt (fun s => (Q s).det)
        (((Q t).det • traceLeftCLM (Q t)⁻¹) B) t := h
    simpa only [ContinuousLinearMap.smul_apply, traceLeftCLM_apply, smul_eq_mul] using h'
  have hm : MonotoneOn (fun t => (Q t).det) (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (show ContinuousOn (fun t => (Q t).det) (Set.Ici 0) by unfold Q; fun_prop)
    · intro t ht
      have ht' : 0 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
      exact (hd t ht'.le).hasDerivWithinAt
    · intro t ht
      have ht' : 0 ≤ t := le_of_lt (by simpa only [interior_Ici, Set.mem_Ioi] using ht)
      exact mul_nonneg (hQ t ht').det_pos.le
        (trace_mul_nonneg_of_posSemidef (hQ t ht').inv.posSemidef hB)
  have h := hm (show (0 : ℝ) ∈ Set.Ici 0 by simp)
    (show (1 : ℝ) ∈ Set.Ici 0 by simp) (by norm_num)
  simpa [Q, Matrix.det_smul, add_comm] using h

variable {p : ℕ} {k : Type*} [Fintype k] [DecidableEq k]

def compressionCLM (M : Matrix (Fin p) k ℝ) :
    SymmetricMatrix p →L[ℝ] Matrix k k ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun X => Mᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * M
    map_add' := by intros; simp [Matrix.mul_add, Matrix.add_mul]
    map_smul' := by intros; simp [Matrix.mul_smul, Matrix.smul_mul] }

@[simp] theorem compressionCLM_apply (M : Matrix (Fin p) k ℝ) (X : SymmetricMatrix p) :
    compressionCLM M X = Mᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * M := rfl

def regularizedCompression (ε : ℝ) (B : Matrix k k ℝ) (M : Matrix (Fin p) k ℝ)
    (X : SymmetricMatrix p) : Matrix k k ℝ := B + compressionCLM M X + ε • 1

theorem regularizedCompression_posDef {ε : ℝ} (hε : 0 < ε)
    {B : Matrix k k ℝ} (hB : B.PosSemidef) (M : Matrix (Fin p) k ℝ)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    (regularizedCompression ε B M X).PosDef := by
  have hc : (compressionCLM M X).PosSemidef := by
    simpa [compressionCLM_apply, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hX.conjTranspose_mul_mul_same M
  exact Matrix.PosDef.posSemidef_add (hB.add hc) (Matrix.PosDef.one.smul hε)

theorem regularizedCompression_det_lower {ε : ℝ} (hε : 0 < ε)
    {B : Matrix k k ℝ} (hB : B.PosSemidef) (M : Matrix (Fin p) k ℝ)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    ε ^ Fintype.card k ≤ (regularizedCompression ε B M X).det := by
  have hc : (compressionCLM M X).PosSemidef := by
    simpa [compressionCLM_apply, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hX.conjTranspose_mul_mul_same M
  exact det_add_epsilon_identity_lower (hB.add hc) hε

theorem hasTemperateGrowth_regularizedCompression_det (ε : ℝ) (B : Matrix k k ℝ)
    (M : Matrix (Fin p) k ℝ) :
    (fun X => (regularizedCompression ε B M X).det).HasTemperateGrowth := by
  apply hasTemperateGrowth_matrix_det
  intro i j
  let L : SymmetricMatrix p →L[ℝ] ℝ :=
    (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℝ i j)).comp (compressionCLM M)
  exact ((Function.HasTemperateGrowth.const (B i j)).add L.hasTemperateGrowth).add
    (Function.HasTemperateGrowth.const ((ε • (1 : Matrix k k ℝ)) i j))

def smoothRegularizedDetPower (ε η : ℝ) (B : Matrix k k ℝ)
    (M : Matrix (Fin p) k ℝ) (X : SymmetricMatrix p) : ℝ :=
  smoothPositivePower (ε ^ Fintype.card k / 2) η (regularizedCompression ε B M X).det

theorem hasTemperateGrowth_smoothRegularizedDetPower {ε : ℝ} (hε : 0 < ε)
    (η : ℝ) (B : Matrix k k ℝ) (M : Matrix (Fin p) k ℝ) :
    (smoothRegularizedDetPower ε η B M).HasTemperateGrowth :=
  (hasTemperateGrowth_smoothPositivePower (by positivity) η).comp
    (hasTemperateGrowth_regularizedCompression_det ε B M)

theorem smoothRegularizedDetPower_eq {ε : ℝ} (hε : 0 < ε)
    (η : ℝ) {B : Matrix k k ℝ} (hB : B.PosSemidef) (M : Matrix (Fin p) k ℝ)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    smoothRegularizedDetPower ε η B M X = (regularizedCompression ε B M X).det ^ η := by
  exact smoothPositivePower_eq (by positivity)
    ((half_le_self (by positivity)).trans (regularizedCompression_det_lower hε hB M hX)) η

theorem smoothRegularizedDetPower_eventuallyEq {ε : ℝ} (hε : 0 < ε)
    (η : ℝ) {B : Matrix k k ℝ} (hB : B.PosSemidef) (M : Matrix (Fin p) k ℝ)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    smoothRegularizedDetPower ε η B M =ᶠ[𝓝 X]
      (fun Y => (regularizedCompression ε B M Y).det ^ η) := by
  have hx : ε ^ Fintype.card k / 2 < (regularizedCompression ε B M X).det :=
    (half_lt_self (by positivity)).trans_le (regularizedCompression_det_lower hε hB M hX)
  have hc : Continuous (fun Y => (regularizedCompression ε B M Y).det) :=
    (hasTemperateGrowth_regularizedCompression_det ε B M).1.continuous
  filter_upwards [hc.continuousAt.eventually_const_lt hx] with Y hY
  exact smoothPositivePower_eq (by positivity) hY.le η

end WishartVerification
end
end CanonicalSource18

section CanonicalSource19
/- Source: Wishart/TransportDifferentiation.lean -/



/-!
# Differentiating a transported probability law

This is a general analytic lemma.  Its hypotheses explicitly include the
domination needed for each differentiation under the integral.  The Gaussian
and Wishart applications must construct these witnesses; this file does not
postulate an integration-by-parts identity for either distribution.
-/

noncomputable section

open MeasureTheory Filter Topology TauCeti.Probability

namespace WishartVerification

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Concrete witnesses for dominated differentiation at one real parameter.
Every field is an ordinary mathematical obligation; no derivative of an
expectation is included among the assumptions. -/
structure IntegralDerivativeData (μ : Measure Ω)
    (F F' : ℝ → Ω → ℝ) (t : ℝ) where
  neighborhood : Set ℝ
  neighborhood_mem : neighborhood ∈ 𝓝 t
  bound : Ω → ℝ
  measurable_near : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) μ
  integrable_at : Integrable (F t) μ
  derivative_measurable : AEStronglyMeasurable (F' t) μ
  derivative_bound : ∀ᵐ x ∂μ, ∀ s ∈ neighborhood, ‖F' s x‖ ≤ bound x
  integrable_bound : Integrable bound μ
  has_derivative : ∀ᵐ x ∂μ, ∀ s ∈ neighborhood,
    HasDerivAt (fun r => F r x) (F' s x) s

namespace IntegralDerivativeData

variable {μ : Measure Ω} {F F' : ℝ → Ω → ℝ} {t : ℝ}

theorem integrable_derivative_and_hasDerivAt (d : IntegralDerivativeData μ F F' t) :
    Integrable (F' t) μ ∧
      HasDerivAt (fun s => ∫ x, F s x ∂μ) (∫ x, F' t x ∂μ) t :=
  hasDerivAt_integral_of_dominated_loc_of_deriv_le d.neighborhood_mem
    d.measurable_near d.integrable_at d.derivative_measurable d.derivative_bound
    d.integrable_bound d.has_derivative

theorem integrable_derivative (d : IntegralDerivativeData μ F F' t) :
    Integrable (F' t) μ := d.integrable_derivative_and_hasDerivAt.1

theorem hasDerivAt (d : IntegralDerivativeData μ F F' t) :
    HasDerivAt (fun s => ∫ x, F s x ∂μ) (∫ x, F' t x ∂μ) t :=
  d.integrable_derivative_and_hasDerivAt.2

end IntegralDerivativeData

/-- A common compact support for a continuous derivative gives a constant
integrable bound under any finite measure.  This is the compact-test route to
the Gaussian and Wishart integration-by-parts identities. -/
theorem integralDerivativeData_of_compact_derivative_support
    [TopologicalSpace Ω] [BorelSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {F F' : ℝ → Ω → ℝ} {t ε : ℝ} (hε : 0 < ε)
    {K : Set Ω} (hK : IsCompact K)
    (hFmeas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) μ)
    (hFint : Integrable (F t) μ)
    (hF'meas : AEStronglyMeasurable (F' t) μ)
    (hF'cont : ContinuousOn (Function.uncurry F') (Set.Icc (t - ε) (t + ε) ×ˢ K))
    (hsupp : ∀ s ∈ Set.Icc (t - ε) (t + ε), ∀ x ∉ K, F' s x = 0)
    (hderiv : ∀ x, ∀ s ∈ Set.Icc (t - ε) (t + ε),
      HasDerivAt (fun r => F r x) (F' s x) s) :
    Nonempty (IntegralDerivativeData μ F F' t) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod hK).bddAbove_image hF'cont.norm
  refine ⟨{
    neighborhood := Set.Icc (t - ε) (t + ε)
    neighborhood_mem := Icc_mem_nhds (by linarith) (by linarith)
    bound := fun _ => max M 0
    measurable_near := hFmeas
    integrable_at := hFint
    derivative_measurable := hF'meas
    derivative_bound := ?_
    integrable_bound := integrable_const _
    has_derivative := Filter.Eventually.of_forall hderiv }⟩
  filter_upwards with x
  intro s hs
  by_cases hx : x ∈ K
  · exact (hM ⟨(s, x), ⟨hs, hx⟩, rfl⟩).trans (le_max_left _ _)
  · simp only [hsupp s hs x hx, norm_zero]
    exact le_max_right _ _

theorem integral_transport_eq_weighted_integral {μ : Measure Ω}
    {T : Ω → Ω} {ρ g : Ω → ℝ}
    (hT : Measurable T) (hρ : AEMeasurable ρ μ) (hρ0 : 0 ≤ᵐ[μ] ρ)
    (hg : Measurable g)
    (hlaw : μ.map T = μ.withDensity (fun x => ENNReal.ofReal (ρ x))) :
    (∫ x, g (T x) ∂μ) = ∫ x, ρ x * g x ∂μ := by
  rw [← integral_map hT.aemeasurable hg.aestronglyMeasurable, hlaw,
    TauCeti.Probability.integral_withDensity_ofReal hρ hρ0]
  rfl

/-- Equality of a transported law and its density gives the score identity
after both sides are differentiated with fully supplied domination witnesses. -/
theorem transport_derivative_identity {μ : Measure Ω}
    {T : ℝ → Ω → Ω} {ρ : ℝ → Ω → ℝ} {g : Ω → ℝ}
    {DTransport DDensity : ℝ → Ω → ℝ} {t : ℝ}
    (hg : Measurable g)
    (hlaw : ∀ᶠ s in 𝓝 t,
      Measurable (T s) ∧ AEMeasurable (ρ s) μ ∧
      (0 ≤ᵐ[μ] ρ s) ∧
      μ.map (T s) = μ.withDensity (fun x => ENNReal.ofReal (ρ s x)))
    (dT : IntegralDerivativeData μ (fun s x => g (T s x)) DTransport t)
    (dρ : IntegralDerivativeData μ (fun s x => ρ s x * g x) DDensity t) :
    (∫ x, DTransport t x ∂μ) = ∫ x, DDensity t x ∂μ := by
  have heq : (fun s => ∫ x, g (T s x) ∂μ) =ᶠ[𝓝 t]
      (fun s => ∫ x, ρ s x * g x ∂μ) := by
    filter_upwards [hlaw] with s hs
    exact integral_transport_eq_weighted_integral hs.1 hs.2.1 hs.2.2.1 hg hs.2.2.2
  exact (dT.hasDerivAt.congr_of_eventuallyEq heq.symm).unique dρ.hasDerivAt

end WishartVerification
end
end CanonicalSource19

section CanonicalSource20
/- Source: Wishart/QuadraticTransport.lean -/



/-!
# Domination for a quadratic linear transport

The map `x ↦ x + t • V x + t² • Q x` includes congruence by `I + t A`.
For a compactly supported C¹ test, its derivative is bounded by a constant
times `‖x‖`.  This supplies the actual differentiation witness under every
finite measure with a finite first moment.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace WishartVerification

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def quadraticLinearTransport (V Q : E →L[ℝ] E) (t : ℝ) (x : E) : E :=
  x + t • V x + t ^ 2 • Q x

@[simp] theorem quadraticLinearTransport_zero (V Q : E →L[ℝ] E) (x : E) :
    quadraticLinearTransport V Q 0 x = x := by
  simp [quadraticLinearTransport]

theorem hasDerivAt_quadraticLinearTransport (V Q : E →L[ℝ] E) (x : E) (t : ℝ) :
    HasDerivAt (fun s => quadraticLinearTransport V Q s x)
      (V x + (2 * t) • Q x) t := by
  simpa [quadraticLinearTransport, Pi.add_def] using
    (((hasDerivAt_id t).smul_const (V x)).const_add x).add
      ((hasDerivAt_pow 2 t).smul_const (Q x))

theorem quadraticLinearTransport_derivative_bound (V Q : E →L[ℝ] E)
    (x : E) {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    ‖V x + (2 * t) • Q x‖ ≤ (‖V‖ + 2 * ‖Q‖) * ‖x‖ := by
  have ht' : |t| ≤ 1 := abs_le.mpr ht
  calc
    ‖V x + (2 * t) • Q x‖ ≤ ‖V x‖ + ‖(2 * t) • Q x‖ := norm_add_le _ _
    _ = ‖V x‖ + (2 * |t|) * ‖Q x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ ‖V‖ * ‖x‖ + 2 * (‖Q‖ * ‖x‖) := by
      apply add_le_add (V.le_opNorm x)
      calc
        (2 * |t|) * ‖Q x‖ ≤ 2 * ‖Q x‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg (Q x))
          linarith
        _ ≤ 2 * (‖Q‖ * ‖x‖) := mul_le_mul_of_nonneg_left (Q.le_opNorm x) (by norm_num)
    _ = (‖V‖ + 2 * ‖Q‖) * ‖x‖ := by ring

theorem integralDerivativeData_quadraticLinearTransport
    {μ : Measure E} [IsFiniteMeasure μ]
    (hμ : Integrable (fun x : E => x) μ)
    {g : E → ℝ} (hg : ContDiff ℝ 1 g) (hcpt : HasCompactSupport g)
    (V Q : E →L[ℝ] E) :
    Nonempty (IntegralDerivativeData μ
      (fun t x => g (quadraticLinearTransport V Q t x))
      (fun t x => fderiv ℝ g (quadraticLinearTransport V Q t x)
        (V x + (2 * t) • Q x)) 0) := by
  have hgdiff : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hgD : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  obtain ⟨M, hM⟩ := hgD.norm.bddAbove_range_of_hasCompactSupport (hcpt.fderiv ℝ).norm
  refine ⟨{
    neighborhood := Set.Icc (-1 : ℝ) 1
    neighborhood_mem := Icc_mem_nhds (by norm_num) (by norm_num)
    bound := fun x => (max M 0 * (‖V‖ + 2 * ‖Q‖)) * ‖x‖
    measurable_near := Filter.Eventually.of_forall fun t => ?_
    integrable_at := ?_
    derivative_measurable := ?_
    derivative_bound := Filter.Eventually.of_forall fun x t ht => ?_
    integrable_bound := hμ.norm.const_mul _
    has_derivative := Filter.Eventually.of_forall fun x t _ => ?_ }⟩
  · exact (hg.continuous.comp (by unfold quadraticLinearTransport; fun_prop)).aestronglyMeasurable
  · simpa using hg.continuous.integrable_of_hasCompactSupport hcpt
  · apply Continuous.aestronglyMeasurable
    exact (hgD.comp (by unfold quadraticLinearTransport; fun_prop)).clm_apply (by fun_prop)
  · calc
      ‖fderiv ℝ g (quadraticLinearTransport V Q t x) (V x + (2 * t) • Q x)‖
          ≤ ‖fderiv ℝ g (quadraticLinearTransport V Q t x)‖ * ‖V x + (2 * t) • Q x‖ :=
        (fderiv ℝ g _).le_opNorm _
      _ ≤ max M 0 * ((‖V‖ + 2 * ‖Q‖) * ‖x‖) :=
        mul_le_mul ((hM ⟨_, rfl⟩).trans (le_max_left _ _))
          (quadraticLinearTransport_derivative_bound V Q x ht) (norm_nonneg _)
          (le_max_right _ _)
      _ = _ := by ring
  · exact (hgdiff _).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_quadraticLinearTransport V Q x t)

end WishartVerification
end
end CanonicalSource20

section CanonicalSource21
/- Source: Wishart/CongruenceFlow.lean -/



/-!
# The infinitesimal congruence flow on symmetric matrices

Every tangent vector below belongs to the genuine vector space of symmetric
matrices.  The flow is exactly congruence by `I + t A`.
-/

noncomputable section

open Matrix MeasureTheory Filter Topology

namespace WishartVerification

variable {p : ℕ}

def congruenceCLM (A : Matrix (Fin p) (Fin p) ℝ) :
    SymmetricMatrix p →L[ℝ] SymmetricMatrix p :=
  LinearMap.toContinuousLinearMap (Matrix.symmetricCongruenceLinearMap A)

def congruenceVelocity (A : Matrix (Fin p) (Fin p) ℝ) :
    SymmetricMatrix p →L[ℝ] SymmetricMatrix p :=
  congruenceCLM (A + 1) - congruenceCLM A - ContinuousLinearMap.id ℝ _

@[simp] theorem coe_congruenceCLM (A : Matrix (Fin p) (Fin p) ℝ)
    (X : SymmetricMatrix p) :
    (congruenceCLM A X : Matrix (Fin p) (Fin p) ℝ) =
      A * (X : Matrix (Fin p) (Fin p) ℝ) * Aᵀ := by
  simpa only [congruenceCLM, LinearMap.coe_toContinuousLinearMap'] using
    Matrix.coe_symmetricCongruenceLinearMap_apply A X

@[simp] theorem coe_congruenceVelocity (A : Matrix (Fin p) (Fin p) ℝ)
    (X : SymmetricMatrix p) :
    (congruenceVelocity A X : Matrix (Fin p) (Fin p) ℝ) =
      A * (X : Matrix (Fin p) (Fin p) ℝ) + (X : Matrix (Fin p) (Fin p) ℝ) * Aᵀ := by
  simp only [congruenceVelocity, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, Submodule.coe_sub, coe_congruenceCLM]
  rw [Matrix.transpose_add, Matrix.transpose_one]
  noncomm_ring

theorem quadraticLinearTransport_eq_congruence (A : Matrix (Fin p) (Fin p) ℝ)
    (t : ℝ) (X : SymmetricMatrix p) :
    quadraticLinearTransport (congruenceVelocity A) (congruenceCLM A) t X =
      Matrix.symmetricCongruenceLinearMap (1 + t • A) X := by
  apply Subtype.ext
  change (X : Matrix (Fin p) (Fin p) ℝ) +
      t • (congruenceVelocity A X : Matrix (Fin p) (Fin p) ℝ) +
      t ^ 2 • (congruenceCLM A X : Matrix (Fin p) (Fin p) ℝ) = _
  rw [coe_congruenceVelocity, coe_congruenceCLM,
    Matrix.coe_symmetricCongruenceLinearMap_apply]
  simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul,
    add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, smul_smul,
    smul_add, pow_two]
  abel

theorem hasDerivAt_congruenceFlow (A : Matrix (Fin p) (Fin p) ℝ)
    (X : SymmetricMatrix p) (t : ℝ) :
    HasDerivAt (fun s => Matrix.symmetricCongruenceLinearMap (1 + s • A) X)
      (congruenceVelocity A X + (2 * t) • congruenceCLM A X) t := by
  simpa only [quadraticLinearTransport_eq_congruence] using
    hasDerivAt_quadraticLinearTransport (congruenceVelocity A) (congruenceCLM A) X t

theorem congruenceFlow_det_eventually_ne_zero (A : Matrix (Fin p) (Fin p) ℝ) :
    ∀ᶠ t in 𝓝 (0 : ℝ), (1 + t • A).det ≠ 0 := by
  have hc : Continuous (fun t : ℝ => (1 + t • A).det) := by fun_prop
  exact hc.continuousAt.eventually_ne (by simp)

end WishartVerification
end
end CanonicalSource21

section CanonicalSource22
/- Source: Wishart/TemperateMoments.lean -/



/-!
# Polynomial growth and genuine integrability

`Function.HasTemperateGrowth` uses actual iterated Fréchet derivatives and
uniform polynomial bounds on their norms.  The lemmas here connect it to all
finite moments of the Gaussian and full real-shape Wishart laws.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti.Probability
open scoped ENNReal

namespace WishartVerification

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [SecondCountableTopology F]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology F] in
theorem hasTemperateGrowth_fderiv {f : E → F} (hf : f.HasTemperateGrowth) :
    (fderiv ℝ f).HasTemperateGrowth := by
  refine ⟨(contDiff_infty_iff_fderiv.mp hf.1).2, fun n => ?_⟩
  obtain ⟨k, C, hC⟩ := hf.2 (n + 1)
  exact ⟨k, C, fun x => by simpa only [norm_iteratedFDeriv_fderiv] using hC x⟩

theorem memLp_temperate_of_allNormMoments {μ : Measure E} [IsFiniteMeasure μ]
    (hμ : HasAllFiniteMoments (fun x : E => ‖x‖) μ)
    {f : E → F} (hf : f.HasTemperateGrowth) {q : ℝ≥0∞} (hq : q ≠ ∞) :
    MemLp f q μ := by
  obtain ⟨k, C, hC⟩ := hf.2 0
  have hb : HasAllFiniteMoments (fun x : E => C * (1 + ‖x‖) ^ k) μ := by
    have h := ((HasAllFiniteMoments.const (μ := μ) 1).add hμ).rpow
      (show 0 ≤ (k : ℝ) by positivity)
    simpa only [Real.rpow_natCast] using h.const_mul C
  apply (hb q hq).mono' hf.1.continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by simpa using hC x

theorem integrable_temperate_of_allNormMoments {μ : Measure E} [IsFiniteMeasure μ]
    (hμ : HasAllFiniteMoments (fun x : E => ‖x‖) μ)
    {f : E → F} (hf : f.HasTemperateGrowth) : Integrable f μ :=
  memLp_one_iff_integrable.mp (memLp_temperate_of_allNormMoments hμ hf (by simp))

theorem allFiniteMoments_temperate_norm {μ : Measure E} [IsFiniteMeasure μ]
    (hμ : HasAllFiniteMoments (fun x : E => ‖x‖) μ)
    {f : E → F} (hf : f.HasTemperateGrowth) :
    HasAllFiniteMoments (fun x => ‖f x‖) μ := by
  intro q hq
  exact (memLp_temperate_of_allNormMoments hμ hf hq).norm

theorem integrable_fderiv_apply_temperate [FiniteDimensional ℝ E]
    {μ : Measure E} [IsFiniteMeasure μ]
    (hμ : HasAllFiniteMoments (fun x : E => ‖x‖) μ)
    {g : E → ℝ} {b : E → E} (hg : g.HasTemperateGrowth) (hb : b.HasTemperateGrowth) :
    Integrable (fun x => fderiv ℝ g x (b x)) μ := by
  have hD := allFiniteMoments_temperate_norm hμ (hasTemperateGrowth_fderiv hg)
  have hB := allFiniteMoments_temperate_norm hμ hb
  apply (hD.mul hB).integrable.mono'
  · exact ((hg.1.continuous_fderiv (by simp)).clm_apply hb.1.continuous).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => (fderiv ℝ g x).le_opNorm (b x)

theorem allFiniteMoments_gaussian_norm [CompleteSpace E] [SecondCountableTopology E]
    {μ : Measure E} [IsGaussian μ] :
    HasAllFiniteMoments (fun x : E => ‖x‖) μ := by
  intro q hq
  exact (IsGaussian.memLp_id μ q hq).norm

theorem allFiniteMoments_wishart_norm {p : ℕ} (ν : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) :
    HasAllFiniteMoments (fun X : SymmetricMatrix p => ‖X‖)
      (nonsingularWishartMeasure ν S) := by
  intro q hq
  have h := (memLp_id_nonsingularWishartMeasure S ν q.toNNReal).norm
  simpa only [ENNReal.coe_toNNReal hq] using h

end WishartVerification
end
end CanonicalSource22

section CanonicalSource23
/- Source: Wishart/RankOneCalculus.lean -/



/-!
# Rank-one perturbations as maps into the symmetric matrix space

The derivative of `w ↦ wwᵀ` is the symmetric rank-one direction
`h ↦ whᵀ + hwᵀ`.  The formulas here concern the actual Fréchet derivative.
-/

noncomputable section

open Matrix MeasureTheory
open scoped RealInnerProductSpace

namespace WishartVerification

variable {p : ℕ}

def symmetricOuter (u v : EuclideanSpace ℝ (Fin p)) : SymmetricMatrix p :=
  ⟨(1 / 2 : ℝ) • (Matrix.vecMulVec (fun i => u i) (fun i => v i) +
    Matrix.vecMulVec (fun i => v i) (fun i => u i)), by
    apply Matrix.isHermitian_iff_isSelfAdjoint.mp
    rw [Matrix.isHermitian_iff_isSymm]
    simp [Matrix.IsSymm, Matrix.transpose_smul, Matrix.transpose_add,
      Matrix.transpose_vecMulVec, add_comm]⟩

@[simp] theorem coe_symmetricOuter (u v : EuclideanSpace ℝ (Fin p)) :
    (symmetricOuter u v : Matrix (Fin p) (Fin p) ℝ) =
      (1 / 2 : ℝ) • (Matrix.vecMulVec (fun i => u i) (fun i => v i) +
        Matrix.vecMulVec (fun i => v i) (fun i => u i)) := rfl

theorem symmetricOuter_comm (u v : EuclideanSpace ℝ (Fin p)) :
    symmetricOuter u v = symmetricOuter v u := by
  apply Subtype.ext
  simp only [coe_symmetricOuter, add_comm]

def symmetricOuterBilin : EuclideanSpace ℝ (Fin p) →ₗ[ℝ]
    EuclideanSpace ℝ (Fin p) →ₗ[ℝ] SymmetricMatrix p :=
  LinearMap.mk₂ ℝ symmetricOuter
    (fun u v w => by
      apply Subtype.ext
      ext i j
      simp [symmetricOuter, Matrix.vecMulVec_apply]
      ring)
    (fun c u v => by
      apply Subtype.ext
      ext i j
      simp [symmetricOuter, Matrix.vecMulVec_apply]
      ring)
    (fun u v w => by
      apply Subtype.ext
      ext i j
      simp [symmetricOuter, Matrix.vecMulVec_apply]
      ring)
    (fun c u v => by
      apply Subtype.ext
      ext i j
      simp [symmetricOuter, Matrix.vecMulVec_apply]
      ring)

def symmetricOuterCLM : EuclideanSpace ℝ (Fin p) →L[ℝ]
    EuclideanSpace ℝ (Fin p) →L[ℝ] SymmetricMatrix p :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      (EuclideanSpace ℝ (Fin p) →ₗ[ℝ] SymmetricMatrix p) ≃ₗ[ℝ]
        (EuclideanSpace ℝ (Fin p) →L[ℝ] SymmetricMatrix p)).toLinearMap.comp symmetricOuterBilin)

@[simp] theorem symmetricOuterCLM_apply (u v : EuclideanSpace ℝ (Fin p)) :
    symmetricOuterCLM u v = symmetricOuter u v := rfl

def rankOneSymmetric (u : EuclideanSpace ℝ (Fin p)) : SymmetricMatrix p :=
  symmetricOuter u u

def symmetricRankDirection (u : EuclideanSpace ℝ (Fin p)) :
    EuclideanSpace ℝ (Fin p) →L[ℝ] SymmetricMatrix p :=
  2 • symmetricOuterCLM u

@[simp] theorem coe_rankOneSymmetric (u : EuclideanSpace ℝ (Fin p)) :
    (rankOneSymmetric u : Matrix (Fin p) (Fin p) ℝ) =
      Matrix.vecMulVec (fun i => u i) (fun i => u i) := by
  ext i j
  simp [rankOneSymmetric, symmetricOuter, Matrix.vecMulVec_apply]
  ring

@[simp] theorem coe_symmetricRankDirection (u v : EuclideanSpace ℝ (Fin p)) :
    (symmetricRankDirection u v : Matrix (Fin p) (Fin p) ℝ) =
      Matrix.vecMulVec (fun i => u i) (fun i => v i) +
        Matrix.vecMulVec (fun i => v i) (fun i => u i) := by
  ext i j
  simp [symmetricRankDirection, two_smul, symmetricOuter, Matrix.vecMulVec_apply]
  ring

theorem symmetricRankDirection_comm (u v : EuclideanSpace ℝ (Fin p)) :
    symmetricRankDirection u v = symmetricRankDirection v u := by
  apply Subtype.ext
  simp [add_comm]

theorem symmetricRankDirection_self (u : EuclideanSpace ℝ (Fin p)) :
    symmetricRankDirection u u = 2 • rankOneSymmetric u := rfl

set_option backward.isDefEq.respectTransparency false in
theorem hasFDerivAt_rankOneSymmetric (u : EuclideanSpace ℝ (Fin p)) :
    HasFDerivAt rankOneSymmetric (symmetricRankDirection u) u := by
  have h := symmetricOuterCLM.hasFDerivAt_of_bilinear (hasFDerivAt_id u) (hasFDerivAt_id u)
  have hlin :
      symmetricOuterCLM.precompR (EuclideanSpace ℝ (Fin p)) u
          (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin p))) +
        symmetricOuterCLM.precompL (EuclideanSpace ℝ (Fin p))
          (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin p))) u =
        symmetricRankDirection u := by
    ext v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.precompR_apply,
      ContinuousLinearMap.precompL_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      symmetricRankDirection, two_smul, ContinuousLinearMap.add_apply,
      symmetricOuterCLM_apply]
    rw [symmetricOuter_comm v u]
  change HasFDerivAt (fun y => symmetricOuterCLM y y) (symmetricRankDirection u) u
  exact h.congr_fderiv hlin

theorem hasTemperateGrowth_rankOneSymmetric :
    (rankOneSymmetric (p := p)).HasTemperateGrowth :=
  symmetricOuterCLM.bilinear_hasTemperateGrowth
    Function.HasTemperateGrowth.id Function.HasTemperateGrowth.id

theorem hasDerivAt_rankOne_shift (z v : EuclideanSpace ℝ (Fin p)) (r : ℝ) :
    HasDerivAt (fun s => rankOneSymmetric (z + s • v))
      (symmetricRankDirection (z + r • v) v) r := by
  have hz : HasDerivAt (fun s : ℝ => z + s • v) v r := by
    simpa only [id_eq, one_smul] using
      (((hasDerivAt_id r).smul_const v).const_add z)
  exact (hasFDerivAt_rankOneSymmetric _).comp_hasDerivAt r hz

theorem congruenceVelocity_rankOne (A : Matrix (Fin p) (Fin p) ℝ)
    (u : EuclideanSpace ℝ (Fin p)) :
    congruenceVelocity A (rankOneSymmetric u) =
      symmetricRankDirection u (A.toEuclideanLin u) := by
  apply Subtype.ext
  rw [coe_congruenceVelocity, coe_rankOneSymmetric, coe_symmetricRankDirection]
  simp only [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.toLpLin_apply]
  ext i j
  simp [Matrix.vecMulVec_apply, Matrix.vecMul, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, mul_comm, add_comm]

end WishartVerification
end
end CanonicalSource23

section CanonicalSource24
/- Source: Wishart/SymmetricSteinAlgebra.lean -/



/-! # Matrix identities connecting the two Stein formulas -/

noncomputable section

open Matrix
open scoped RealInnerProductSpace

namespace WishartVerification

variable {p : ℕ}

def symmetricMatrixAction : SymmetricMatrix p →L[ℝ]
    EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p) :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      (EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) ≃ₗ[ℝ]
        (EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p))).toLinearMap.comp
      ((Matrix.toEuclideanLin : Matrix (Fin p) (Fin p) ℝ ≃ₗ[ℝ]
        EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)).toLinearMap.comp
          (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)).subtype))

@[simp] theorem symmetricMatrixAction_apply (W : SymmetricMatrix p)
    (u : EuclideanSpace ℝ (Fin p)) :
    symmetricMatrixAction W u = (W : Matrix (Fin p) (Fin p) ℝ).toEuclideanLin u := rfl

def outerMatrix (u v : EuclideanSpace ℝ (Fin p)) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.vecMulVec (fun i => u i) (fun i => v i)

theorem trace_outerMatrix (u v : EuclideanSpace ℝ (Fin p)) :
    Matrix.trace (outerMatrix u v) = ⟪v, u⟫ := by
  simp [outerMatrix, Matrix.trace_vecMulVec, EuclideanSpace.inner_eq_star_dotProduct]

theorem trace_mul_outerMatrix_mul (C : Matrix (Fin p) (Fin p) ℝ)
    (W : SymmetricMatrix p) (w u : EuclideanSpace ℝ (Fin p)) :
    Matrix.trace (C * outerMatrix w u * (W : Matrix (Fin p) (Fin p) ℝ)) =
      ⟪u, symmetricMatrixAction W (C.toEuclideanLin w)⟫ := by
  rw [Matrix.trace_mul_cycle, outerMatrix, trace_mul_rankOne]
  simp [symmetricMatrixAction_apply, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.toLpLin_apply, ← Matrix.mulVec_mulVec, dotProduct_comm]

theorem congruenceVelocity_outerMatrix (W : SymmetricMatrix p)
    (w u : EuclideanSpace ℝ (Fin p)) :
    congruenceVelocity (outerMatrix w u) W =
      symmetricRankDirection w (symmetricMatrixAction W u) := by
  apply Subtype.ext
  rw [coe_congruenceVelocity, coe_symmetricRankDirection]
  have hW := (selfAdjoint.isHermitian_coe W).isSymm
  simp only [outerMatrix, Matrix.vecMulVec_mul, Matrix.transpose_vecMulVec,
    Matrix.mul_vecMulVec, symmetricMatrixAction_apply, Matrix.toLpLin_apply]
  rw [← hW.eq, Matrix.vecMul_transpose]
  simp only [hW.eq]

theorem inner_symmetricMatrixAction (W : SymmetricMatrix p)
    (u z : EuclideanSpace ℝ (Fin p)) :
    ⟪symmetricMatrixAction W u, z⟫ = ⟪u, symmetricMatrixAction W z⟫ :=
  (Matrix.isSymmetric_toEuclideanLin_iff.mpr (selfAdjoint.isHermitian_coe W)) u z

end WishartVerification
end
end CanonicalSource24
