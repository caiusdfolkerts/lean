module

public import Papers.GraphicalZonotopes.FiniteMonomialCoordinates
public import Papers.GraphicalZonotopes.DiamondGenerated
public import Papers.GraphicalZonotopes.ConnectedDimension
public import Papers.GraphicalZonotopes.GraphDefinitions
public import Papers.GraphicalZonotopes.BoundaryContexts

@[expose] public section
namespace GraphicalZonotopes.DiamondGeometry
open Finset
open scoped BigOperators Pointwise
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

def edges : Finset (Finset (Fin 10)) :=
  {{0,1}, {0,2}, {1,2}, {0,3}, {1,3}, {0,4}, {1,4}, {0,5}, {1,5}, {0,6}, {1,6}, {0,7}, {1,7}, {0,8}, {1,8}, {0,9}, {1,9}, {3,4}, {3,5}, {2,6}, {2,7}, {2,8}, {3,8}, {2,9}, {3,9}}

def graph : SimpleGraph (Fin 10) where
  Adj u v := u≠v ∧ {u,v}∈edges
  symm := ⟨by intro u v h; exact ⟨Ne.symm h.1,by simpa only [pair_comm] using h.2⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

instance graphDecidable : DecidableRel graph.Adj :=
  fun u v => inferInstanceAs (Decidable (u≠v ∧ ({u,v} : Finset (Fin 10))∈edges))

def cliques : Fin 57 → Finset (Fin 10) :=
  ![{0,1}, {0,2}, {1,2}, {0,1,2}, {0,3}, {1,3}, {0,1,3}, {0,4}, {1,4}, {0,1,4}, {3,4}, {0,3,4}, {1,3,4}, {0,1,3,4}, {0,5}, {1,5}, {0,1,5}, {3,5}, {0,3,5}, {1,3,5}, {0,1,3,5}, {0,6}, {1,6}, {0,1,6}, {2,6}, {0,2,6}, {1,2,6}, {0,1,2,6}, {0,7}, {1,7}, {0,1,7}, {2,7}, {0,2,7}, {1,2,7}, {0,1,2,7}, {0,8}, {1,8}, {0,1,8}, {2,8}, {0,2,8}, {1,2,8}, {0,1,2,8}, {3,8}, {0,3,8}, {1,3,8}, {0,1,3,8}, {0,9}, {1,9}, {0,1,9}, {2,9}, {0,2,9}, {1,2,9}, {0,1,2,9}, {3,9}, {0,3,9}, {1,3,9}, {0,1,3,9}]

def coefficientsZ : Fin 57 → ℤ :=
  ![1, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, -1, 0, 0, 2, 0, 0, 2, -2, 0, 0, 1, 0, 1, 0, -1, 0, 1, 0, 0, 1, 0, -1, 0, 1, 0, 1, 0, -1, 1, 0, 1, 0, -1, 1, 1, -1, 1, 0, -1, 1, 1, -1, 0, 1]

theorem cliques_injective : Function.Injective cliques := by decide +kernel

theorem cliques_valid : ∀ i,2≤(cliques i).card ∧ graph.IsClique (cliques i) := by
  decide +kernel

theorem cliques_complete : ∀ C : Finset (Fin 10),
    IsCliqueCoordinate graph C → ∃ i,cliques i=C := by
  change ∀ C : Finset (Fin 10),(2≤C.card ∧ ∀ u∈C,∀ v∈C,u≠v → graph.Adj u v) → ∃ i,cliques i=C
  decide +kernel

noncomputable def function : SetFunction (Fin 10) :=
  FiniteMonomial.polynomial cliques DiamondGenerated.coefficients

theorem coefficients_cast : ∀ i,(coefficientsZ i : ℝ)=DiamondGenerated.coefficients i := by
  intro i
  fin_cases i <;> norm_num [coefficientsZ,DiamondGenerated.coefficients]

theorem normalized : TranslationNormalized function :=
  FiniteMonomial.polynomial_normalized cliques (fun i => (cliques_valid i).1) _

theorem graphical : Graphical graph function :=
  FiniteMonomial.polynomial_graphical cliques (fun i => (cliques_valid i).2) _

def slackZ (u v : Fin 10) (S : Finset (Fin 10)) : ℤ :=
  ∑ i : Fin 57,if u∈cliques i ∧ v∈cliques i ∧
    cliques i⊆insert u (insert v S) then coefficientsZ i else 0

theorem delta_eq_slackZ {u v : Fin 10} (huv : u≠v) {S : Finset (Fin 10)}
    (hu : u∉S) (hv : v∉S) : delta function u v S=(slackZ u v S : ℝ) := by
  change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) u v S=_
  rw [FiniteMonomial.delta_polynomial cliques DiamondGenerated.coefficients huv hu hv]
  simp only [slackZ,Int.cast_sum,apply_ite,Int.cast_zero,coefficients_cast]

def neighbors (u v : Fin 10) : Finset (Fin 10) :=
  univ.filter (fun w => graph.Adj u w ∧ graph.Adj v w)

theorem neighbors_eq (u v : Fin 10) : neighbors u v=commonNeighbors graph u v := by
  ext w
  simp [neighbors]

theorem neighbors_literal_0 : neighbors 0 1={2,3,4,5,6,7,8,9} := by decide +kernel

theorem bounded_edge_0 (S : Finset (Fin 10)) (hS : S∈({2,3,4,5,6,7,8,9} : Finset (Fin 10)).powerset) :
    0≤slackZ 0 1 S ∧ slackZ 0 1 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h2 : (2 : Fin 10) ∈ S <;>
    by_cases h3 : (3 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_1 : neighbors 0 2={1,6,7,8,9} := by decide +kernel

theorem bounded_edge_1 (S : Finset (Fin 10)) (hS : S∈({1,6,7,8,9} : Finset (Fin 10)).powerset) :
    0≤slackZ 0 2 S ∧ slackZ 0 2 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_2 : neighbors 1 2={0,6,7,8,9} := by decide +kernel

theorem bounded_edge_2 (S : Finset (Fin 10)) (hS : S∈({0,6,7,8,9} : Finset (Fin 10)).powerset) :
    0≤slackZ 1 2 S ∧ slackZ 1 2 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_3 : neighbors 0 3={1,4,5,8,9} := by decide +kernel

theorem bounded_edge_3 (S : Finset (Fin 10)) (hS : S∈({1,4,5,8,9} : Finset (Fin 10)).powerset) :
    0≤slackZ 0 3 S ∧ slackZ 0 3 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_4 : neighbors 1 3={0,4,5,8,9} := by decide +kernel

theorem bounded_edge_4 (S : Finset (Fin 10)) (hS : S∈({0,4,5,8,9} : Finset (Fin 10)).powerset) :
    0≤slackZ 1 3 S ∧ slackZ 1 3 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_5 : neighbors 0 4={1,3} := by decide +kernel

theorem bounded_edge_5 (S : Finset (Fin 10)) (hS : S∈({1,3} : Finset (Fin 10)).powerset) :
    0≤slackZ 0 4 S ∧ slackZ 0 4 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    by_cases h3 : (3 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_6 : neighbors 1 4={0,3} := by decide +kernel

theorem bounded_edge_6 (S : Finset (Fin 10)) (hS : S∈({0,3} : Finset (Fin 10)).powerset) :
    0≤slackZ 1 4 S ∧ slackZ 1 4 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    by_cases h3 : (3 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_7 : neighbors 0 5={1,3} := by decide +kernel

theorem bounded_edge_7 (S : Finset (Fin 10)) (hS : S∈({1,3} : Finset (Fin 10)).powerset) :
    0≤slackZ 0 5 S ∧ slackZ 0 5 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    by_cases h3 : (3 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_8 : neighbors 1 5={0,3} := by decide +kernel

theorem bounded_edge_8 (S : Finset (Fin 10)) (hS : S∈({0,3} : Finset (Fin 10)).powerset) :
    0≤slackZ 1 5 S ∧ slackZ 1 5 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    by_cases h3 : (3 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_9 : neighbors 0 6={1,2} := by decide +kernel

theorem bounded_edge_9 (S : Finset (Fin 10)) (hS : S∈({1,2} : Finset (Fin 10)).powerset) :
    0≤slackZ 0 6 S ∧ slackZ 0 6 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    by_cases h2 : (2 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_10 : neighbors 1 6={0,2} := by decide +kernel

theorem bounded_edge_10 (S : Finset (Fin 10)) (hS : S∈({0,2} : Finset (Fin 10)).powerset) :
    0≤slackZ 1 6 S ∧ slackZ 1 6 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    by_cases h2 : (2 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_11 : neighbors 0 7={1,2} := by decide +kernel

theorem bounded_edge_11 (S : Finset (Fin 10)) (hS : S∈({1,2} : Finset (Fin 10)).powerset) :
    0≤slackZ 0 7 S ∧ slackZ 0 7 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    by_cases h2 : (2 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_12 : neighbors 1 7={0,2} := by decide +kernel

theorem bounded_edge_12 (S : Finset (Fin 10)) (hS : S∈({0,2} : Finset (Fin 10)).powerset) :
    0≤slackZ 1 7 S ∧ slackZ 1 7 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    by_cases h2 : (2 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_13 : neighbors 0 8={1,2,3} := by decide +kernel

theorem bounded_edge_13 (S : Finset (Fin 10)) (hS : S∈({1,2,3} : Finset (Fin 10)).powerset) :
    0≤slackZ 0 8 S ∧ slackZ 0 8 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    by_cases h2 : (2 : Fin 10) ∈ S <;>
    by_cases h3 : (3 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_14 : neighbors 1 8={0,2,3} := by decide +kernel

theorem bounded_edge_14 (S : Finset (Fin 10)) (hS : S∈({0,2,3} : Finset (Fin 10)).powerset) :
    0≤slackZ 1 8 S ∧ slackZ 1 8 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    by_cases h2 : (2 : Fin 10) ∈ S <;>
    by_cases h3 : (3 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_15 : neighbors 0 9={1,2,3} := by decide +kernel

theorem bounded_edge_15 (S : Finset (Fin 10)) (hS : S∈({1,2,3} : Finset (Fin 10)).powerset) :
    0≤slackZ 0 9 S ∧ slackZ 0 9 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    by_cases h2 : (2 : Fin 10) ∈ S <;>
    by_cases h3 : (3 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_16 : neighbors 1 9={0,2,3} := by decide +kernel

theorem bounded_edge_16 (S : Finset (Fin 10)) (hS : S∈({0,2,3} : Finset (Fin 10)).powerset) :
    0≤slackZ 1 9 S ∧ slackZ 1 9 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    by_cases h2 : (2 : Fin 10) ∈ S <;>
    by_cases h3 : (3 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_17 : neighbors 3 4={0,1} := by decide +kernel

theorem bounded_edge_17 (S : Finset (Fin 10)) (hS : S∈({0,1} : Finset (Fin 10)).powerset) :
    0≤slackZ 3 4 S ∧ slackZ 3 4 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_18 : neighbors 3 5={0,1} := by decide +kernel

theorem bounded_edge_18 (S : Finset (Fin 10)) (hS : S∈({0,1} : Finset (Fin 10)).powerset) :
    0≤slackZ 3 5 S ∧ slackZ 3 5 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_19 : neighbors 2 6={0,1} := by decide +kernel

theorem bounded_edge_19 (S : Finset (Fin 10)) (hS : S∈({0,1} : Finset (Fin 10)).powerset) :
    0≤slackZ 2 6 S ∧ slackZ 2 6 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_20 : neighbors 2 7={0,1} := by decide +kernel

theorem bounded_edge_20 (S : Finset (Fin 10)) (hS : S∈({0,1} : Finset (Fin 10)).powerset) :
    0≤slackZ 2 7 S ∧ slackZ 2 7 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_21 : neighbors 2 8={0,1} := by decide +kernel

theorem bounded_edge_21 (S : Finset (Fin 10)) (hS : S∈({0,1} : Finset (Fin 10)).powerset) :
    0≤slackZ 2 8 S ∧ slackZ 2 8 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_22 : neighbors 3 8={0,1} := by decide +kernel

theorem bounded_edge_22 (S : Finset (Fin 10)) (hS : S∈({0,1} : Finset (Fin 10)).powerset) :
    0≤slackZ 3 8 S ∧ slackZ 3 8 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_23 : neighbors 2 9={0,1} := by decide +kernel

theorem bounded_edge_23 (S : Finset (Fin 10)) (hS : S∈({0,1} : Finset (Fin 10)).powerset) :
    0≤slackZ 2 9 S ∧ slackZ 2 9 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_24 : neighbors 3 9={0,1} := by decide +kernel

theorem bounded_edge_24 (S : Finset (Fin 10)) (hS : S∈({0,1} : Finset (Fin 10)).powerset) :
    0≤slackZ 3 9 S ∧ slackZ 3 9 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem edge_orientation_certificate : ∀ u v : Fin 10,u<v → graph.Adj u v →
  (u=0 ∧ v=1) ∨ (u=0 ∧ v=2) ∨ (u=1 ∧ v=2) ∨ (u=0 ∧ v=3) ∨ (u=1 ∧ v=3) ∨ (u=0 ∧ v=4) ∨ (u=1 ∧ v=4) ∨ (u=0 ∧ v=5) ∨ (u=1 ∧ v=5) ∨ (u=0 ∧ v=6) ∨ (u=1 ∧ v=6) ∨ (u=0 ∧ v=7) ∨ (u=1 ∧ v=7) ∨ (u=0 ∧ v=8) ∨ (u=1 ∧ v=8) ∨ (u=0 ∧ v=9) ∨ (u=1 ∧ v=9) ∨ (u=3 ∧ v=4) ∨ (u=3 ∧ v=5) ∨ (u=2 ∧ v=6) ∨ (u=2 ∧ v=7) ∨ (u=2 ∧ v=8) ∨ (u=3 ∧ v=8) ∨ (u=2 ∧ v=9) ∨ (u=3 ∧ v=9) := by decide +kernel

theorem bounded_slack_certificate : ∀ u v : Fin 10,u<v → graph.Adj u v →
    ∀ S : Finset (Fin 10),S∈(neighbors u v).powerset →
      0≤slackZ u v S ∧ slackZ u v S≤4 := by
  intro u v hlt he S hS
  rcases edge_orientation_certificate u v hlt he with
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rw [neighbors_literal_0] at hS
    exact bounded_edge_0 S hS
  · rw [neighbors_literal_1] at hS
    exact bounded_edge_1 S hS
  · rw [neighbors_literal_2] at hS
    exact bounded_edge_2 S hS
  · rw [neighbors_literal_3] at hS
    exact bounded_edge_3 S hS
  · rw [neighbors_literal_4] at hS
    exact bounded_edge_4 S hS
  · rw [neighbors_literal_5] at hS
    exact bounded_edge_5 S hS
  · rw [neighbors_literal_6] at hS
    exact bounded_edge_6 S hS
  · rw [neighbors_literal_7] at hS
    exact bounded_edge_7 S hS
  · rw [neighbors_literal_8] at hS
    exact bounded_edge_8 S hS
  · rw [neighbors_literal_9] at hS
    exact bounded_edge_9 S hS
  · rw [neighbors_literal_10] at hS
    exact bounded_edge_10 S hS
  · rw [neighbors_literal_11] at hS
    exact bounded_edge_11 S hS
  · rw [neighbors_literal_12] at hS
    exact bounded_edge_12 S hS
  · rw [neighbors_literal_13] at hS
    exact bounded_edge_13 S hS
  · rw [neighbors_literal_14] at hS
    exact bounded_edge_14 S hS
  · rw [neighbors_literal_15] at hS
    exact bounded_edge_15 S hS
  · rw [neighbors_literal_16] at hS
    exact bounded_edge_16 S hS
  · rw [neighbors_literal_17] at hS
    exact bounded_edge_17 S hS
  · rw [neighbors_literal_18] at hS
    exact bounded_edge_18 S hS
  · rw [neighbors_literal_19] at hS
    exact bounded_edge_19 S hS
  · rw [neighbors_literal_20] at hS
    exact bounded_edge_20 S hS
  · rw [neighbors_literal_21] at hS
    exact bounded_edge_21 S hS
  · rw [neighbors_literal_22] at hS
    exact bounded_edge_22 S hS
  · rw [neighbors_literal_23] at hS
    exact bounded_edge_23 S hS
  · rw [neighbors_literal_24] at hS
    exact bounded_edge_24 S hS

end GraphicalZonotopes.DiamondGeometry
