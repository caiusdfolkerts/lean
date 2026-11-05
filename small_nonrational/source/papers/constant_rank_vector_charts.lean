module
public import Papers.ConstantRankKernels
public import Papers.GaleConfigurationRanks
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.ChirotopeDensity

open PlaneRationalization

theorem transpose_spans_of_rowIndependent {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ A.row) :
    Spans A.transpose := by
  apply (spans_iff_matrix_rank A.transpose).mpr
  change A.transpose.rank = m
  rw [Matrix.rank_transpose]
  simpa using hA.rank_matrix

def rowKernelVector {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (w : Fin n → ℝ) : Fin n → ℝ :=
  galeChart A.transpose (fun _ : Fin 1 => w) 0

theorem rowKernelVector_mem {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ A.row)
    (w : Fin n → ℝ) : A.mulVec (rowKernelVector A w) = 0 := by
  have h := galeChart_mul (transpose_spans_of_rowIndependent hA) (fun _ : Fin 1 => w)
  ext i
  have hi := congrFun (congrFun h 0) i
  simpa [rowKernelVector,Matrix.mul_apply,Matrix.mulVec,dotProduct,mul_comm] using hi

theorem rowKernelVector_self {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (w : Fin n → ℝ)
    (hw : A.mulVec w=0) : rowKernelVector A w=w := by
  have hWA : Matrix.of (fun _ : Fin 1 => w) * A.transpose = 0 := by
    ext i j
    have h := congrFun hw j
    simpa [Matrix.mul_apply,Matrix.mulVec,dotProduct,mul_comm] using h
  exact congrFun (galeChart_self A.transpose (fun _ : Fin 1 => w) hWA) 0

theorem rowKernelVector_rational {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} {w : Fin n → ℝ}
    (hA : RationalCoordinates A) (hw : ∀ i, RatScalar (w i)) :
    ∀ i, RatScalar (rowKernelVector A w i) :=
  fun i => galeChart_rational (rationalCoordinates_transpose hA)
    (fun (_ : Fin 1) j => hw j) 0 i

theorem rowKernelVector_continuousAt {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ A.row)
    (w : Fin n → ℝ) :
    ContinuousAt (fun z : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ) =>
      rowKernelVector z.1 z.2) (A,w) := by
  have hparam : Continuous
      (fun z : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ) =>
        (z.1.transpose,(fun _ : Fin 1 => z.2))) :=
    continuous_fst.matrix_transpose.prodMk (continuous_pi fun _ => continuous_snd)
  have hchart := (galeChart_continuousAt (transpose_spans_of_rowIndependent hA)
    (fun _ : Fin 1 => w)).comp_of_eq (hparam.continuousAt (x := (A,w))) rfl
  exact (continuous_apply 0).continuousAt.comp hchart


/-- Fixed original row labels provide one local chart on each
constant-rank matrix stratum. -/
structure RowKernelChart {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) where
  rank : ℕ
  rows : Fin rank → Fin m
  independent : LinearIndependent ℝ (fun i => A (rows i))
  rank_eq : A.rank=rank

theorem exists_rowKernelChart {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) : Nonempty (RowKernelChart A) := by
  classical
  obtain ⟨B⟩ := exists_matrixRowBasis A
  let k := B.support.card
  let e : Fin k ≃ B.support := Fintype.equivOfCardEq (by simp [k])
  refine ⟨⟨k,(fun i => (e i).1),?_,B.card_eq_rank.symm⟩⟩
  exact B.independent.comp e e.injective

def RowKernelChart.eval {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (C : RowKernelChart A) (A' : Matrix (Fin m) (Fin n) ℝ)
    (w : Fin n → ℝ) : Fin n → ℝ :=
  rowKernelVector (A'.submatrix C.rows id) w

theorem RowKernelChart.self {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (C : RowKernelChart A) (w : Fin n → ℝ) (hw : A.mulVec w=0) :
    C.eval A w=w := by
  apply rowKernelVector_self
  ext i
  exact congrFun hw (C.rows i)

theorem RowKernelChart.mem {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (C : RowKernelChart A) (A' : Matrix (Fin m) (Fin n) ℝ)
    (hA' : A'.rank=A.rank)
    (hrows : LinearIndependent ℝ (fun i => A' (C.rows i)))
    (w : Fin n → ℝ) : A'.mulVec (C.eval A' w)=0 := by
  have hk := kernel_row_restriction_eq_of_independent A' C.rows hrows
    (by simpa using hA'.trans C.rank_eq)
  have hm : C.eval A' w ∈ (A'.submatrix C.rows id).mulVecLin.ker :=
    rowKernelVector_mem hrows w
  rw [← hk] at hm
  exact hm

theorem RowKernelChart.rational {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (C : RowKernelChart A) {A' : Matrix (Fin m) (Fin n) ℝ}
    {w : Fin n → ℝ} (hA' : RationalCoordinates A')
    (hw : ∀ i, RatScalar (w i)) :
    ∀ i, RatScalar (C.eval A' w i) :=
  rowKernelVector_rational (fun i j => hA' (C.rows i) j) hw

theorem RowKernelChart.continuousAt {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (C : RowKernelChart A) (w : Fin n → ℝ) :
    ContinuousAt (fun z : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ) =>
      C.eval z.1 z.2) (A,w) := by
  have hsub : Continuous
      (fun z : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ) =>
        (z.1.submatrix C.rows id,z.2)) :=
    (continuous_pi fun i => continuous_pi fun j =>
      (continuous_apply j).comp ((continuous_apply (C.rows i)).comp continuous_fst)).prodMk
        continuous_snd
  exact (rowKernelVector_continuousAt C.independent w).comp_of_eq
    (hsub.continuousAt (x := (A, w))) rfl

theorem RowKernelChart.eventually_independent {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} (C : RowKernelChart A) :
    ∀ᶠ A' in 𝓝 A, LinearIndependent ℝ (fun i => A' (C.rows i)) := by
  have h : Continuous (fun A' : Matrix (Fin m) (Fin n) ℝ => fun i => A' (C.rows i)) :=
    continuous_pi fun i => continuous_apply (C.rows i)
  exact h.continuousAt.tendsto.eventually C.independent.eventually

end Papers.RationalityTen.ChirotopeDensity
