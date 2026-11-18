module

public import Papers.GraphicalZonotopes.PathSlacks
public import Papers.GraphicalZonotopes.Directions

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace Path
open Finset
open scoped BigOperators Pointwise

/-- The paper's actual lower base polytope. -/
def polytope (n : ℕ) : Set (Fin n → ℝ) := basePolytope (setFunction n)

/-- The actual complement at dilation two, with integral lower-support data. -/
def complement (n : ℕ) : Set (Fin n → ℝ) :=
  basePolytope ((2 : ℝ) • graphFunction (graph n) - setFunction n)

/-- The defining affine hyperplane is exactly the paper's total n−2. -/
theorem setFunction_univ (n : ℕ) :
    setFunction n Finset.univ = ((n-2 : ℕ) : ℝ) := by
  rw [setFunction_expansion]
  simp [setMonomial]

/-- Exact set equality with the displayed definition (3.1), using zero-based
labels for the n standard coordinates. -/
theorem polytope_defining_equations (n : ℕ) :
    polytope n = {x : Fin n → ℝ | subsetSum x Finset.univ = ((n-2 : ℕ) : ℝ) ∧
      ∀ S, setFunction n S ≤ subsetSum x S} := by
  unfold polytope basePolytope
  rw [setFunction_univ]

theorem setFunction_ne_zero {n : ℕ} (hn : 4 ≤ n) : setFunction n ≠ 0 := by
  intro he
  have hz : coefficients n = 0 := (zeta_eq_zero_iff _).mp he
  have hc := congrFun (congrArg Coordinates.tri012 (coordinates_coefficients n))
    (⟨0, by omega⟩ : Fin (n-2))
  change coefficients n _ = 1 at hc
  rw [hz] at hc
  norm_num at hc

theorem setFunction_extreme {n : ℕ} (hn : 4 ≤ n) :
    ExtremeSupermodular (setFunction n) :=
  extremeSupermodular_of_tightEquations (setFunction_normalized n)
    (setFunction_supermodular n) (setFunction_ne_zero hn) (complete_tight_kernel hn)

theorem polytope_indecomposable {n : ℕ} (hn : 4 ≤ n) :
    MinkowskiIndecomposable (polytope n) :=
  (setFunction_extreme hn).minkowskiIndecomposable

theorem setFunction_integerValued (n : ℕ) : IntegerValued (setFunction n) := by
  rw [setFunction_expansion]
  apply IntegerValued.sub
  · apply IntegerValued.add
    · exact IntegerValued.finset_sum _ _ (fun _ _ => setMonomial_integerValued _)
    · exact IntegerValued.finset_sum _ _ (fun _ _ => setMonomial_integerValued _)
  · exact IntegerValued.finset_sum _ _ (fun _ _ => setMonomial_integerValued _)

theorem polytope_lattice (n : ℕ) : LatticePolytope (polytope n) :=
  (setFunction_integerValued n).basePolytope (setFunction_normalized n).1
    (setFunction_supermodular n)

theorem complement_normalized (n : ℕ) :
    Normalized ((2 : ℝ) • graphFunction (graph n) - setFunction n) := by
  change 2 * graphFunction (graph n) ∅ - setFunction n ∅ = 0
  rw [graphFunction_normalized, (setFunction_normalized n).1]
  ring

theorem complement_supermodular (n : ℕ) :
    Supermodular ((2 : ℝ) • graphFunction (graph n) - setFunction n) :=
  graphical_complement_supermodular (setFunction_graphical n) (by norm_num)
    (fun u v huv _ S hu hv => (slack_bounds huv hu hv).2)

theorem complement_lattice (n : ℕ) : LatticePolytope (complement n) := by
  have hZ := (graphFunction_integerValued (graph n)).int_smul 2
  have hz : IntegerValued ((2 : ℝ) • graphFunction (graph n)-setFunction n) := by
    simpa using hZ.sub (setFunction_integerValued n)
  exact hz.basePolytope (complement_normalized n) (complement_supermodular n)

/-- The claimed dilation is an equality of genuine sets under Minkowski
addition; it is stronger than membership in a formally defined deformation cone. -/
theorem polytope_add_complement (n : ℕ) :
    polytope n + complement n = (2 : ℝ) • graphicalZonotope (graph n) :=
  basePolytope_add_graphical_complement (setFunction_normalized n).1
    (setFunction_supermodular n) (setFunction_graphical n) (by norm_num)
    (fun u v huv _ S hu hv => (slack_bounds huv hu hv).2)

theorem polytope_compact (n : ℕ) : IsCompact (polytope n) :=
  basePolytope_compact (setFunction_normalized n).1 (setFunction_supermodular n)

theorem polytope_nonempty (n : ℕ) : (polytope n).Nonempty :=
  basePolytope_nonempty (setFunction_normalized n).1 (setFunction_supermodular n)

theorem complement_compact (n : ℕ) : IsCompact (complement n) :=
  basePolytope_compact (complement_normalized n) (complement_supermodular n)

end Path
end GraphicalZonotopes
