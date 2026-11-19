module
public import Papers.RankFourCoordinates
public import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section
open Matrix Set Filter Topology

namespace Papers.MatrixGaugeNormalization

open Papers.RationalKernelCharts

/-- Nodes 0,...,3 are basis-coordinate rows of the displayed block D;
nodes 4,...,7 are nonbasis-point columns. This is the orientation used by
the finite chart certificates. The actual point matrix stores vectors as
rows, so its lower block is D transposed. -/
def certificateWeights (q : Matrix (Fin 8) (Fin 4) ℝ) : Fin 8 → Fin 8 → ℝ :=
  fun u v => Fin.addCases
    (fun i : Fin 4 => Fin.addCases (fun _ : Fin 4 => 0)
      (fun j : Fin 4 => lowerBlock q j i) v)
    (fun j : Fin 4 => Fin.addCases (fun i : Fin 4 => lowerBlock q j i)
      (fun _ : Fin 4 => 0) v) u

@[simp] theorem certificateWeights_left_right (q : Matrix (Fin 8) (Fin 4) ℝ)
    (i j : Fin 4) :
    certificateWeights q (firstFour i) (lastFour j) = lowerBlock q j i := by
  simp only [certificateWeights,firstFour,lastFour,Fin.addCases_left,Fin.addCases_right]

@[simp] theorem certificateWeights_right_left (q : Matrix (Fin 8) (Fin 4) ℝ)
    (i j : Fin 4) :
    certificateWeights q (lastFour j) (firstFour i) = lowerBlock q j i := by
  simp only [certificateWeights,firstFour,lastFour,Fin.addCases_left,Fin.addCases_right]

/-- A chart obtained by an explicitly checked ordered forest schedule.
The basis and all scalings remain actual data of the given representation. -/
structure ScheduledRankFourChart (p : Matrix (Fin 8) (Fin 4) ℝ)
    (e : Equiv.Perm (Fin 8)) (edges : List (Fin 8 × Fin 8)) where
  basis_nonsingular : (basisMatrix (p.submatrix e id) firstFour).det ≠ 0
  rowScale : Fin 8 → ℝ
  columnScale : Fin 4 → ℝ
  rowScale_nonzero : ∀ i, rowScale i ≠ 0
  columnScale_nonzero : ∀ i, columnScale i ≠ 0
  basis_identity : (normalizedMatrix p e rowScale columnScale).submatrix firstFour id = 1
  entries_one : ∀ i j,
    (firstFour i,lastFour j) ∈ edges ∨ (lastFour j,firstFour i) ∈ edges →
    lowerBlock (normalizedMatrix p e rowScale columnScale) j i = 1

/-- A verified finite schedule normalizes every represented matrix whose
scheduled entries are nonzero. These nonzero entries are basis-exchange
minors, as identified by `coordinate_eq_exchange_minor`. -/
theorem exists_scheduled_rankFourChart (p : Matrix (Fin 8) (Fin 4) ℝ)
    (e : Equiv.Perm (Fin 8))
    (hdet : (basisMatrix (p.submatrix e id) firstFour).det ≠ 0)
    (roots : Finset (Fin 8)) (edges : List (Fin 8 × Fin 8))
    (hcheck : checkSchedule roots edges = true)
    (hweight : ∀ f ∈ edges,
      certificateWeights (normalizeBasis (p.submatrix e id) firstFour) f.1 f.2 ≠ 0) :
    Nonempty (ScheduledRankFourChart p e edges) := by
  classical
  let q := normalizeBasis (p.submatrix e id) firstFour
  obtain ⟨g,hg,_,hunit⟩ := exists_forest_normalization (certificateWeights q)
    (validSteps_of_check (certificateWeights q) hcheck hweight)
  let c : Fin 4 → ℝ := fun i => g (firstFour i)
  let a : Fin 8 → ℝ := fun k => Fin.addCases (fun i : Fin 4 => (c i)⁻¹)
    (fun j : Fin 4 => g (lastFour j)) k
  have hc : ∀ i, c i ≠ 0 := fun i => hg (firstFour i)
  have ha : ∀ i, a i ≠ 0 := by
    intro i
    refine Fin.addCases (m := 4) (n := 4) (fun j => ?_) (fun j => ?_) i
    · simpa only [a,Fin.addCases_left] using inv_ne_zero (hc j)
    · simpa only [a,Fin.addCases_right] using hg (lastFour j)
  have he (i j : Fin 4)
      (h : (firstFour i,lastFour j) ∈ edges ∨ (lastFour j,firstFour i) ∈ edges) :
      g (lastFour j) * lowerBlock q j i * g (firstFour i) = 1 := by
    rcases h with h | h
    · have hh := hunit (firstFour i,lastFour j) h
      simp only [certificateWeights_left_right] at hh
      calc
        _ = g (firstFour i) * lowerBlock q j i * g (lastFour j) := by ring
        _ = 1 := hh
    · simpa only [certificateWeights_right_left] using hunit (lastFour j,firstFour i) h
  refine ⟨{
    basis_nonsingular := hdet
    rowScale := a
    columnScale := c
    rowScale_nonzero := ha
    columnScale_nonzero := hc
    basis_identity := ?_
    entries_one := ?_ }⟩
  · apply scale_normalizeBasis_basis _ _ hdet
    intro i
    simpa only [a,firstFour,Fin.addCases_left] using inv_mul_cancel₀ (hc i)
  · intro i j h
    change a (lastFour j) * q (lastFour j) i * c i = 1
    simpa only [a,lastFour,Fin.addCases_right,lowerBlock,c] using he i j h

def ScheduledRankFourChart.matrix {p : Matrix (Fin 8) (Fin 4) ℝ}
    {e : Equiv.Perm (Fin 8)} {edges : List (Fin 8 × Fin 8)}
    (D : ScheduledRankFourChart p e edges) : Matrix (Fin 8) (Fin 4) ℝ :=
  normalizedMatrix p e D.rowScale D.columnScale

/-- The 4-by-4 block in the certificates' [I | D] convention. -/
def ScheduledRankFourChart.displayBlock {p : Matrix (Fin 8) (Fin 4) ℝ}
    {e : Equiv.Perm (Fin 8)} {edges : List (Fin 8 × Fin 8)}
    (D : ScheduledRankFourChart p e edges) : Matrix (Fin 4) (Fin 4) ℝ :=
  (lowerBlock D.matrix).transpose

theorem ScheduledRankFourChart.zero_minor_iff {p : Matrix (Fin 8) (Fin 4) ℝ}
    {e : Equiv.Perm (Fin 8)} {edges : List (Fin 8 × Fin 8)}
    (D : ScheduledRankFourChart p e edges) (s : Fin 4 → Fin 8) :
    (D.matrix.submatrix s id).det = 0 ↔
      ((p.submatrix e id).submatrix s id).det = 0 := by
  rw [ScheduledRankFourChart.matrix,normalizedMatrix,
    scaleRowsColumns_zero_minor_iff _ _ _ D.rowScale_nonzero D.columnScale_nonzero,
    normalizeBasis_zero_minor_iff _ _ D.basis_nonsingular]

/-- The support of the certificate block is the basis-exchange support of
the original representation, with the matrix orientation made explicit. -/
theorem ScheduledRankFourChart.coordinate_zero_iff_exchange
    {p : Matrix (Fin 8) (Fin 4) ℝ} {e : Equiv.Perm (Fin 8)}
    {edges : List (Fin 8 × Fin 8)} (D : ScheduledRankFourChart p e edges) (i j : Fin 4) :
    D.displayBlock i j = 0 ↔
      ((p.submatrix e id).submatrix (Function.update firstFour i (lastFour j)) id).det = 0 := by
  change D.matrix (lastFour j) i = 0 ↔ _
  rw [← coordinate_eq_exchange_minor D.matrix firstFour D.basis_identity (lastFour j) i]
  exact D.zero_minor_iff _

/-- Rational density at the certificate chart transfers to the actual
representation by simultaneous rational approximation of the real gauges
and the original real basis, followed by undoing the label permutation. -/
theorem ScheduledRankFourChart.density {p : Matrix (Fin 8) (Fin 4) ℝ}
    {e : Equiv.Perm (Fin 8)} {edges : List (Fin 8 × Fin 8)}
    (D : ScheduledRankFourChart p e edges)
    (h : D.matrix ∈ closure (ZeroRationalRealizations D.matrix)) :
    p ∈ closure (ZeroRationalRealizations p) := by
  apply density_of_permuted_rows p e
  exact density_of_normalized_chart _ _ D.basis_nonsingular _ _
    D.rowScale_nonzero D.columnScale_nonzero h

end Papers.MatrixGaugeNormalization
