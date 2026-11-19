module
public import Consolidated.MatrixNormalization
public import Papers.AlgebraicChartDensity

@[expose] public section
noncomputable section

namespace Papers.RationalityTen.MatroidChecked.ExactDensity

open Matrix Set Filter Topology
open Papers.MatrixGaugeNormalization (ZeroRationalRealizations)
open Papers.RationalKernelCharts (RationalCoordinates)
open AlgebraicChartDensity (restrict_closure_to_open)

/-- Every ordered maximal minor vanishes exactly when it did originally.
In particular this retains the full rank and the complete basis family. -/
def ExactRationalRealizations {n r : ℕ} (p : Matrix (Fin n) (Fin r) ℝ) :
    Set (Matrix (Fin n) (Fin r) ℝ) :=
  {q | RationalCoordinates q ∧ ∀ s : Fin r → Fin n,
    (p.submatrix s id).det = 0 ↔ (q.submatrix s id).det = 0}

def NonzeroMinorNeighbourhood {n r : ℕ} (p : Matrix (Fin n) (Fin r) ℝ) :
    Set (Matrix (Fin n) (Fin r) ℝ) :=
  {q | ∀ s : Fin r → Fin n,
    (p.submatrix s id).det ≠ 0 → (q.submatrix s id).det ≠ 0}

theorem continuous_minor {n r : ℕ} (s : Fin r → Fin n) :
    Continuous (fun q : Matrix (Fin n) (Fin r) ℝ => (q.submatrix s id).det) := by
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_apply j).comp (continuous_apply (s i))

theorem isOpen_nonzeroMinorNeighbourhood {n r : ℕ}
    (p : Matrix (Fin n) (Fin r) ℝ) : IsOpen (NonzeroMinorNeighbourhood p) := by
  have hset : NonzeroMinorNeighbourhood p =
      ⋂ s : Fin r → Fin n, {q | (p.submatrix s id).det ≠ 0 →
        (q.submatrix s id).det ≠ 0} := by
    ext q
    simp only [NonzeroMinorNeighbourhood,Set.mem_setOf_eq,Set.mem_iInter]
  rw [hset]
  apply isOpen_iInter_of_finite
  intro s
  by_cases hs : (p.submatrix s id).det ≠ 0
  · have heq : {q : Matrix (Fin n) (Fin r) ℝ |
        (p.submatrix s id).det ≠ 0 → (q.submatrix s id).det ≠ 0} =
        {q : Matrix (Fin n) (Fin r) ℝ | (q.submatrix s id).det ≠ 0} := by
      ext q
      exact ⟨fun h => h hs,fun h _ => h⟩
    rw [heq]
    exact (isOpen_ne (x := (0 : ℝ))).preimage (continuous_minor s)
  · simp only [hs,false_implies,Set.setOf_true,isOpen_univ]

/-- Keeping the nonzero minors is an open restriction of the proved
zero-minor density statement; no generic-position hypothesis is introduced. -/
theorem exact_density_of_zero_density {n r : ℕ}
    (p : Matrix (Fin n) (Fin r) ℝ)
    (hp : p ∈ closure (ZeroRationalRealizations p)) :
    p ∈ closure (ExactRationalRealizations p) := by
  have hnear := restrict_closure_to_open hp
    (isOpen_nonzeroMinorNeighbourhood p) (fun _ h => h)
  apply closure_mono ?_ hnear
  rintro q ⟨hz,hn⟩
  refine ⟨hz.1,?_⟩
  intro s
  constructor
  · exact hz.2 s
  · intro hq
    by_contra hp
    exact hn s hp hq

end Papers.RationalityTen.MatroidChecked.ExactDensity
