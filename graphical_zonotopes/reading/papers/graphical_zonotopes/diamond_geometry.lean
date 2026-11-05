module
public import Papers.GraphicalZonotopes.DiamondData
public import Papers.GraphicalZonotopes.ConnectedDimension
public import Papers.GraphicalZonotopes.SummandEdges

@[expose] public section
noncomputable section
namespace GraphicalZonotopes.DiamondGeometry
open Finset
open scoped BigOperators Pointwise
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

theorem elemental_bounds {u v : Fin 10} (huv : u≠v)
    {S : Finset (Fin 10)} (hu : u∉S) (hv : v∉S) :
    0≤delta function u v S ∧ delta function u v S≤4 := by
  have ordered : ∀ u v : Fin 10,u<v → ∀ S : Finset (Fin 10),u∉S → v∉S →
      0≤delta function u v S ∧ delta function u v S≤4 := by
    intro a b hab T ha hb
    by_cases he : graph.Adj a b
    · let U:=T∩commonNeighbors graph a b
      have hU : U∈(neighbors a b).powerset := by
        rw [neighbors_eq,mem_powerset]
        exact inter_subset_right
      have hUa : a∉U:=fun h => ha (mem_inter.mp h).1
      have hUb : b∉U:=fun h => hb (mem_inter.mp h).1
      rw [delta_commonNeighbors normalized graphical (ne_of_lt hab) ha hb,
        delta_eq_slackZ (ne_of_lt hab) hUa hUb]
      exact_mod_cast bounded_slack_certificate a b hab he U hU
    · rw [graphical a b (ne_of_lt hab) he T ha hb]
      norm_num
  rcases lt_or_gt_of_ne huv with hlt | hgt
  · exact ordered u v hlt S hu hv
  · rw [delta_comm u v]
    exact ordered v u hgt S hv hu

theorem supermodular : Supermodular function :=
  ElementallyNonnegative.supermodular (fun _ _ huv _ hu hv => (elemental_bounds huv hu hv).1)

theorem actual_summand : IsMinkowskiSummand (basePolytope function)
    ((4 : ℝ) • graphicalZonotope graph) := by
  apply (isMinkowskiSummand_graphical_iff normalized.1 supermodular (by norm_num : (0 : ℝ)≤4)).mpr
  exact ⟨graphical,fun _ _ huv _ _ hu hv => (elemental_bounds huv hu hv).2⟩

theorem integerValued : IntegerValued function := by
  change IntegerValued (∑ i : Fin 57,DiamondGenerated.coefficients i • setMonomial (cliques i))
  apply IntegerValued.finset_sum
  intro i hi
  rw [← coefficients_cast i]
  exact (setMonomial_integerValued (cliques i)).int_smul (coefficientsZ i)

theorem tight_row_0 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 1 {2,7} = x 0 + x 3 + x 30 + x 34 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (1 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 1 ({2,7} : Finset (Fin 10)))) = {0,3,30,34} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_1 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 1 {2,4,7} = x 0 + x 3 + x 9 + x 30 + x 34 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (1 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 1 ({2,4,7} : Finset (Fin 10)))) = {0,3,9,30,34} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_2 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 1 {2,3,4,7} = x 0 + x 3 + x 6 + x 9 + x 13 + x 30 + x 34 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (1 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 1 ({2,3,4,7} : Finset (Fin 10)))) = {0,3,6,9,13,30,34} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_3 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 1 {2,3,4,5,7} = x 0 + x 3 + x 6 + x 9 + x 13 + x 16 + x 20 + x 30 + x 34 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (1 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 1 ({2,3,4,5,7} : Finset (Fin 10)))) = {0,3,6,9,13,16,20,30,34} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_4 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 1 {2,6,7} = x 0 + x 3 + x 23 + x 27 + x 30 + x 34 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (1 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 1 ({2,6,7} : Finset (Fin 10)))) = {0,3,23,27,30,34} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_5 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 1 {3,4,8} = x 0 + x 6 + x 9 + x 13 + x 37 + x 45 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (1 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 1 ({3,4,8} : Finset (Fin 10)))) = {0,6,9,13,37,45} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_6 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 1 {3,4,7,8} = x 0 + x 6 + x 9 + x 13 + x 30 + x 37 + x 45 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (1 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 1 ({3,4,7,8} : Finset (Fin 10)))) = {0,6,9,13,30,37,45} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_7 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 1 {2,3,4,7,8} = x 0 + x 3 + x 6 + x 9 + x 13 + x 30 + x 34 + x 37 + x 41 + x 45 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (1 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 1 ({2,3,4,7,8} : Finset (Fin 10)))) = {0,3,6,9,13,30,34,37,41,45} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_8 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 1 {9} = x 0 + x 48 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (1 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 1 ({9} : Finset (Fin 10)))) = {0,48} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_9 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 1 {2,7,9} = x 0 + x 3 + x 30 + x 34 + x 48 + x 52 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (1 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 1 ({2,7,9} : Finset (Fin 10)))) = {0,3,30,34,48,52} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_10 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 1 {8,9} = x 0 + x 37 + x 48 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (1 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 1 ({8,9} : Finset (Fin 10)))) = {0,37,48} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_11 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 1 {3,4,8,9} = x 0 + x 6 + x 9 + x 13 + x 37 + x 45 + x 48 + x 56 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (1 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 1 ({3,4,8,9} : Finset (Fin 10)))) = {0,6,9,13,37,45,48,56} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_12 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 2 ∅ = x 1 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (2 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 2 (∅ : Finset (Fin 10)))) = {1} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_13 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 2 {1} = x 1 + x 3 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (2 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 2 ({1} : Finset (Fin 10)))) = {1,3} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_14 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 2 {1,6} = x 1 + x 3 + x 25 + x 27 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (2 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 2 ({1,6} : Finset (Fin 10)))) = {1,3,25,27} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_15 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 2 {1,7} = x 1 + x 3 + x 32 + x 34 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (2 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 2 ({1,7} : Finset (Fin 10)))) = {1,3,32,34} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_16 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 2 {8} = x 1 + x 39 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (2 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 2 ({8} : Finset (Fin 10)))) = {1,39} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_17 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 2 {9} = x 1 + x 50 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (2 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 2 ({9} : Finset (Fin 10)))) = {1,50} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_18 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 2 {0,6,7} = x 2 + x 3 + x 26 + x 27 + x 33 + x 34 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (2 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 2 ({0,6,7} : Finset (Fin 10)))) = {2,3,26,27,33,34} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_19 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 2 {0,6,7,8} = x 2 + x 3 + x 26 + x 27 + x 33 + x 34 + x 40 + x 41 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (2 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 2 ({0,6,7,8} : Finset (Fin 10)))) = {2,3,26,27,33,34,40,41} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_20 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 2 {0,6,7,9} = x 2 + x 3 + x 26 + x 27 + x 33 + x 34 + x 51 + x 52 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (2 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 2 ({0,6,7,9} : Finset (Fin 10)))) = {2,3,26,27,33,34,51,52} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_21 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 2 {8,9} = x 2 + x 40 + x 51 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (2 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 2 ({8,9} : Finset (Fin 10)))) = {2,40,51} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_22 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 2 {6,8,9} = x 2 + x 26 + x 40 + x 51 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (2 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 2 ({6,8,9} : Finset (Fin 10)))) = {2,26,40,51} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_23 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 2 {7,8,9} = x 2 + x 33 + x 40 + x 51 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (2 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 2 ({7,8,9} : Finset (Fin 10)))) = {2,33,40,51} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_24 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 3 {1,5} = x 4 + x 6 + x 18 + x 20 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (3 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 3 ({1,5} : Finset (Fin 10)))) = {4,6,18,20} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_25 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 3 {1,4,5} = x 4 + x 6 + x 11 + x 13 + x 18 + x 20 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (3 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 3 ({1,4,5} : Finset (Fin 10)))) = {4,6,11,13,18,20} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_26 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 3 {1,5,8} = x 4 + x 6 + x 18 + x 20 + x 43 + x 45 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (3 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 3 ({1,5,8} : Finset (Fin 10)))) = {4,6,18,20,43,45} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_27 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 3 {9} = x 4 + x 54 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (3 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 3 ({9} : Finset (Fin 10)))) = {4,54} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_28 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 3 {5,9} = x 4 + x 18 + x 54 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (3 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 3 ({5,9} : Finset (Fin 10)))) = {4,18,54} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_29 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 3 {1,5,9} = x 4 + x 6 + x 18 + x 20 + x 54 + x 56 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (3 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 3 ({1,5,9} : Finset (Fin 10)))) = {4,6,18,20,54,56} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_30 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 3 ∅ = x 5 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (3 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 3 (∅ : Finset (Fin 10)))) = {5} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_31 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 3 {8} = x 5 + x 44 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (3 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 3 ({8} : Finset (Fin 10)))) = {5,44} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_32 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 3 {0,8} = x 5 + x 6 + x 44 + x 45 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (3 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 3 ({0,8} : Finset (Fin 10)))) = {5,6,44,45} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_33 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 3 {0,4,8} = x 5 + x 6 + x 12 + x 13 + x 44 + x 45 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (3 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 3 ({0,4,8} : Finset (Fin 10)))) = {5,6,12,13,44,45} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_34 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 3 {0,5,8} = x 5 + x 6 + x 19 + x 20 + x 44 + x 45 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (3 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 3 ({0,5,8} : Finset (Fin 10)))) = {5,6,19,20,44,45} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_35 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 3 {9} = x 5 + x 55 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (3 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 3 ({9} : Finset (Fin 10)))) = {5,55} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_36 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 4 ∅ = x 7 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (4 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 4 (∅ : Finset (Fin 10)))) = {7} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_37 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 4 ∅ = x 8 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (4 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 4 (∅ : Finset (Fin 10)))) = {8} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_38 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 5 ∅ = x 14 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (5 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 5 (∅ : Finset (Fin 10)))) = {14} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_39 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 5 ∅ = x 15 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (5 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 5 (∅ : Finset (Fin 10)))) = {15} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_40 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 6 ∅ = x 21 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (6 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 6 (∅ : Finset (Fin 10)))) = {21} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_41 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 6 ∅ = x 22 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (6 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 6 (∅ : Finset (Fin 10)))) = {22} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_42 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 7 ∅ = x 28 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (7 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 7 (∅ : Finset (Fin 10)))) = {28} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_43 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 7 {0,2} = x 29 + x 30 + x 33 + x 34 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (7 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 7 ({0,2} : Finset (Fin 10)))) = {29,30,33,34} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_44 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 8 ∅ = x 35 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (8 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 8 (∅ : Finset (Fin 10)))) = {35} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_45 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 8 {2} = x 36 + x 40 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (8 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 8 ({2} : Finset (Fin 10)))) = {36,40} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_46 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 9 {1} = x 46 + x 48 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (9 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 9 ({1} : Finset (Fin 10)))) = {46,48} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_47 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 9 {0} = x 47 + x 48 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (9 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 9 ({0} : Finset (Fin 10)))) = {47,48} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_48 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 3 4 ∅ = x 10 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (3 : Fin 10) ∈ cliques i ∧ (4 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 3 (insert 4 (∅ : Finset (Fin 10)))) = {10} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_49 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 3 5 ∅ = x 17 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (3 : Fin 10) ∈ cliques i ∧ (5 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 3 (insert 5 (∅ : Finset (Fin 10)))) = {17} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_50 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 2 6 ∅ = x 24 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (2 : Fin 10) ∈ cliques i ∧ (6 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 2 (insert 6 (∅ : Finset (Fin 10)))) = {24} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_51 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 2 7 ∅ = x 31 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (2 : Fin 10) ∈ cliques i ∧ (7 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 2 (insert 7 (∅ : Finset (Fin 10)))) = {31} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_52 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 2 8 {1} = x 38 + x 40 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (2 : Fin 10) ∈ cliques i ∧ (8 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 2 (insert 8 ({1} : Finset (Fin 10)))) = {38,40} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_53 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 3 8 ∅ = x 42 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (3 : Fin 10) ∈ cliques i ∧ (8 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 3 (insert 8 (∅ : Finset (Fin 10)))) = {42} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_54 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 2 9 {1} = x 49 + x 51 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (2 : Fin 10) ∈ cliques i ∧ (9 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 2 (insert 9 ({1} : Finset (Fin 10)))) = {49,51} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_55 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 3 9 {0} = x 53 + x 54 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (3 : Fin 10) ∈ cliques i ∧ (9 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 3 (insert 9 ({0} : Finset (Fin 10)))) = {53,54} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem actual_tight_kernel (f : SetFunction (Fin 10)) (hn : TranslationNormalized f)
    (hz : ∀ u v,u≠v → ∀ S : Finset (Fin 10),u∉S → v∉S →
      delta function u v S=0 → delta f u v S=0) :
    ∃ a : ℝ,f=a • function := by
  have hG : Graphical graph f := fun u v huv hnon S hu hv =>
    hz u v huv S hu hv (graphical u v huv hnon S hu hv)
  let x : Fin 57 → ℝ := fun i => mobius f (cliques i)
  have he : f=FiniteMonomial.polynomial cliques x :=
    FiniteMonomial.graphical_eq_polynomial cliques cliques_injective cliques_complete hn hG
  have h0 : x 0 + x 3 + x 30 + x 34=0 := by
    have h := hz 0 1 (by decide) {2,7} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 1 {2,7}=0
      rw [tight_row_0]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_0] at h
    exact h
  have h1 : x 0 + x 3 + x 9 + x 30 + x 34=0 := by
    have h := hz 0 1 (by decide) {2,4,7} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 1 {2,4,7}=0
      rw [tight_row_1]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_1] at h
    exact h
  have h2 : x 0 + x 3 + x 6 + x 9 + x 13 + x 30 + x 34=0 := by
    have h := hz 0 1 (by decide) {2,3,4,7} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 1 {2,3,4,7}=0
      rw [tight_row_2]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_2] at h
    exact h
  have h3 : x 0 + x 3 + x 6 + x 9 + x 13 + x 16 + x 20 + x 30 + x 34=0 := by
    have h := hz 0 1 (by decide) {2,3,4,5,7} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 1 {2,3,4,5,7}=0
      rw [tight_row_3]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_3] at h
    exact h
  have h4 : x 0 + x 3 + x 23 + x 27 + x 30 + x 34=0 := by
    have h := hz 0 1 (by decide) {2,6,7} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 1 {2,6,7}=0
      rw [tight_row_4]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_4] at h
    exact h
  have h5 : x 0 + x 6 + x 9 + x 13 + x 37 + x 45=0 := by
    have h := hz 0 1 (by decide) {3,4,8} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 1 {3,4,8}=0
      rw [tight_row_5]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_5] at h
    exact h
  have h6 : x 0 + x 6 + x 9 + x 13 + x 30 + x 37 + x 45=0 := by
    have h := hz 0 1 (by decide) {3,4,7,8} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 1 {3,4,7,8}=0
      rw [tight_row_6]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_6] at h
    exact h
  have h7 : x 0 + x 3 + x 6 + x 9 + x 13 + x 30 + x 34 + x 37 + x 41 + x 45=0 := by
    have h := hz 0 1 (by decide) {2,3,4,7,8} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 1 {2,3,4,7,8}=0
      rw [tight_row_7]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_7] at h
    exact h
  have h8 : x 0 + x 48=0 := by
    have h := hz 0 1 (by decide) {9} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 1 {9}=0
      rw [tight_row_8]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_8] at h
    exact h
  have h9 : x 0 + x 3 + x 30 + x 34 + x 48 + x 52=0 := by
    have h := hz 0 1 (by decide) {2,7,9} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 1 {2,7,9}=0
      rw [tight_row_9]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_9] at h
    exact h
  have h10 : x 0 + x 37 + x 48=0 := by
    have h := hz 0 1 (by decide) {8,9} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 1 {8,9}=0
      rw [tight_row_10]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_10] at h
    exact h
  have h11 : x 0 + x 6 + x 9 + x 13 + x 37 + x 45 + x 48 + x 56=0 := by
    have h := hz 0 1 (by decide) {3,4,8,9} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 1 {3,4,8,9}=0
      rw [tight_row_11]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_11] at h
    exact h
  have h12 : x 1=0 := by
    have h := hz 0 2 (by decide) ∅ (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 2 ∅=0
      rw [tight_row_12]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_12] at h
    exact h
  have h13 : x 1 + x 3=0 := by
    have h := hz 0 2 (by decide) {1} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 2 {1}=0
      rw [tight_row_13]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_13] at h
    exact h
  have h14 : x 1 + x 3 + x 25 + x 27=0 := by
    have h := hz 0 2 (by decide) {1,6} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 2 {1,6}=0
      rw [tight_row_14]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_14] at h
    exact h
  have h15 : x 1 + x 3 + x 32 + x 34=0 := by
    have h := hz 0 2 (by decide) {1,7} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 2 {1,7}=0
      rw [tight_row_15]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_15] at h
    exact h
  have h16 : x 1 + x 39=0 := by
    have h := hz 0 2 (by decide) {8} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 2 {8}=0
      rw [tight_row_16]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_16] at h
    exact h
  have h17 : x 1 + x 50=0 := by
    have h := hz 0 2 (by decide) {9} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 2 {9}=0
      rw [tight_row_17]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_17] at h
    exact h
  have h18 : x 2 + x 3 + x 26 + x 27 + x 33 + x 34=0 := by
    have h := hz 1 2 (by decide) {0,6,7} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 2 {0,6,7}=0
      rw [tight_row_18]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_18] at h
    exact h
  have h19 : x 2 + x 3 + x 26 + x 27 + x 33 + x 34 + x 40 + x 41=0 := by
    have h := hz 1 2 (by decide) {0,6,7,8} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 2 {0,6,7,8}=0
      rw [tight_row_19]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_19] at h
    exact h
  have h20 : x 2 + x 3 + x 26 + x 27 + x 33 + x 34 + x 51 + x 52=0 := by
    have h := hz 1 2 (by decide) {0,6,7,9} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 2 {0,6,7,9}=0
      rw [tight_row_20]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_20] at h
    exact h
  have h21 : x 2 + x 40 + x 51=0 := by
    have h := hz 1 2 (by decide) {8,9} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 2 {8,9}=0
      rw [tight_row_21]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_21] at h
    exact h
  have h22 : x 2 + x 26 + x 40 + x 51=0 := by
    have h := hz 1 2 (by decide) {6,8,9} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 2 {6,8,9}=0
      rw [tight_row_22]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_22] at h
    exact h
  have h23 : x 2 + x 33 + x 40 + x 51=0 := by
    have h := hz 1 2 (by decide) {7,8,9} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 2 {7,8,9}=0
      rw [tight_row_23]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_23] at h
    exact h
  have h24 : x 4 + x 6 + x 18 + x 20=0 := by
    have h := hz 0 3 (by decide) {1,5} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 3 {1,5}=0
      rw [tight_row_24]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_24] at h
    exact h
  have h25 : x 4 + x 6 + x 11 + x 13 + x 18 + x 20=0 := by
    have h := hz 0 3 (by decide) {1,4,5} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 3 {1,4,5}=0
      rw [tight_row_25]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_25] at h
    exact h
  have h26 : x 4 + x 6 + x 18 + x 20 + x 43 + x 45=0 := by
    have h := hz 0 3 (by decide) {1,5,8} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 3 {1,5,8}=0
      rw [tight_row_26]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_26] at h
    exact h
  have h27 : x 4 + x 54=0 := by
    have h := hz 0 3 (by decide) {9} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 3 {9}=0
      rw [tight_row_27]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_27] at h
    exact h
  have h28 : x 4 + x 18 + x 54=0 := by
    have h := hz 0 3 (by decide) {5,9} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 3 {5,9}=0
      rw [tight_row_28]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_28] at h
    exact h
  have h29 : x 4 + x 6 + x 18 + x 20 + x 54 + x 56=0 := by
    have h := hz 0 3 (by decide) {1,5,9} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 3 {1,5,9}=0
      rw [tight_row_29]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_29] at h
    exact h
  have h30 : x 5=0 := by
    have h := hz 1 3 (by decide) ∅ (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 3 ∅=0
      rw [tight_row_30]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_30] at h
    exact h
  have h31 : x 5 + x 44=0 := by
    have h := hz 1 3 (by decide) {8} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 3 {8}=0
      rw [tight_row_31]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_31] at h
    exact h
  have h32 : x 5 + x 6 + x 44 + x 45=0 := by
    have h := hz 1 3 (by decide) {0,8} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 3 {0,8}=0
      rw [tight_row_32]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_32] at h
    exact h
  have h33 : x 5 + x 6 + x 12 + x 13 + x 44 + x 45=0 := by
    have h := hz 1 3 (by decide) {0,4,8} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 3 {0,4,8}=0
      rw [tight_row_33]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_33] at h
    exact h
  have h34 : x 5 + x 6 + x 19 + x 20 + x 44 + x 45=0 := by
    have h := hz 1 3 (by decide) {0,5,8} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 3 {0,5,8}=0
      rw [tight_row_34]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_34] at h
    exact h
  have h35 : x 5 + x 55=0 := by
    have h := hz 1 3 (by decide) {9} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 3 {9}=0
      rw [tight_row_35]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_35] at h
    exact h
  have h36 : x 7=0 := by
    have h := hz 0 4 (by decide) ∅ (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 4 ∅=0
      rw [tight_row_36]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_36] at h
    exact h
  have h37 : x 8=0 := by
    have h := hz 1 4 (by decide) ∅ (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 4 ∅=0
      rw [tight_row_37]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_37] at h
    exact h
  have h38 : x 14=0 := by
    have h := hz 0 5 (by decide) ∅ (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 5 ∅=0
      rw [tight_row_38]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_38] at h
    exact h
  have h39 : x 15=0 := by
    have h := hz 1 5 (by decide) ∅ (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 5 ∅=0
      rw [tight_row_39]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_39] at h
    exact h
  have h40 : x 21=0 := by
    have h := hz 0 6 (by decide) ∅ (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 6 ∅=0
      rw [tight_row_40]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_40] at h
    exact h
  have h41 : x 22=0 := by
    have h := hz 1 6 (by decide) ∅ (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 6 ∅=0
      rw [tight_row_41]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_41] at h
    exact h
  have h42 : x 28=0 := by
    have h := hz 0 7 (by decide) ∅ (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 7 ∅=0
      rw [tight_row_42]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_42] at h
    exact h
  have h43 : x 29 + x 30 + x 33 + x 34=0 := by
    have h := hz 1 7 (by decide) {0,2} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 7 {0,2}=0
      rw [tight_row_43]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_43] at h
    exact h
  have h44 : x 35=0 := by
    have h := hz 0 8 (by decide) ∅ (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 8 ∅=0
      rw [tight_row_44]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_44] at h
    exact h
  have h45 : x 36 + x 40=0 := by
    have h := hz 1 8 (by decide) {2} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 8 {2}=0
      rw [tight_row_45]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_45] at h
    exact h
  have h46 : x 46 + x 48=0 := by
    have h := hz 0 9 (by decide) {1} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 9 {1}=0
      rw [tight_row_46]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_46] at h
    exact h
  have h47 : x 47 + x 48=0 := by
    have h := hz 1 9 (by decide) {0} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 9 {0}=0
      rw [tight_row_47]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_47] at h
    exact h
  have h48 : x 10=0 := by
    have h := hz 3 4 (by decide) ∅ (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 3 4 ∅=0
      rw [tight_row_48]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_48] at h
    exact h
  have h49 : x 17=0 := by
    have h := hz 3 5 (by decide) ∅ (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 3 5 ∅=0
      rw [tight_row_49]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_49] at h
    exact h
  have h50 : x 24=0 := by
    have h := hz 2 6 (by decide) ∅ (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 2 6 ∅=0
      rw [tight_row_50]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_50] at h
    exact h
  have h51 : x 31=0 := by
    have h := hz 2 7 (by decide) ∅ (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 2 7 ∅=0
      rw [tight_row_51]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_51] at h
    exact h
  have h52 : x 38 + x 40=0 := by
    have h := hz 2 8 (by decide) {1} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 2 8 {1}=0
      rw [tight_row_52]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_52] at h
    exact h
  have h53 : x 42=0 := by
    have h := hz 3 8 (by decide) ∅ (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 3 8 ∅=0
      rw [tight_row_53]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_53] at h
    exact h
  have h54 : x 49 + x 51=0 := by
    have h := hz 2 9 (by decide) {1} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 2 9 {1}=0
      rw [tight_row_54]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_54] at h
    exact h
  have h55 : x 53 + x 54=0 := by
    have h := hz 3 9 (by decide) {0} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 3 9 {0}=0
      rw [tight_row_55]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_55] at h
    exact h
  have hx := DiamondGenerated.kernel_line x h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41 h42 h43 h44 h45 h46 h47 h48 h49 h50 h51 h52 h53 h54 h55
  refine ⟨x 0,?_⟩
  have hs : x=(x 0) • DiamondGenerated.coefficients := by
    funext i
    simpa only [Pi.smul_apply,smul_eq_mul,mul_comm] using hx i
  calc
    f=FiniteMonomial.polynomial cliques x := he
    _=FiniteMonomial.polynomial cliques ((x 0) • DiamondGenerated.coefficients) :=
      congrArg (FiniteMonomial.polynomial cliques) hs
    _=(x 0) • function :=
      FiniteMonomial.polynomial_smul cliques DiamondGenerated.coefficients (x 0)

theorem function_ne_zero : function≠0 := by
  intro h
  have he:=congrFun h ({0,1} : Finset (Fin 10))
  norm_num [function,FiniteMonomial.polynomial,cliques,DiamondGenerated.coefficients,
    Fin.sum_univ_succ,setMonomial,Finset.subset_iff] at he

theorem extreme : ExtremeSupermodular function :=
  extremeSupermodular_of_tightEquations normalized supermodular function_ne_zero actual_tight_kernel

theorem lattice : LatticePolytope (basePolytope function) :=
  integerValued.basePolytope normalized.1 supermodular

theorem indecomposable : MinkowskiIndecomposable (basePolytope function) :=
  extreme.minkowskiIndecomposable


def orientedEdges : Fin 25 → Fin 10 × Fin 10 :=
  ![(0,1), (0,2), (1,2), (0,3), (1,3), (0,4), (1,4), (0,5), (1,5), (0,6), (1,6), (0,7), (1,7), (0,8), (1,8), (0,9), (1,9), (3,4), (3,5), (2,6), (2,7), (2,8), (3,8), (2,9), (3,9)]

def positiveContexts : Fin 25 → Finset (Fin 10) :=
  ![∅, {6}, ∅, ∅, {0}, {3}, {3}, {1}, {0}, {1}, {0}, {2}, ∅, {1,2}, ∅, ∅, ∅, {0}, {1}, {0}, {0}, ∅, {0}, ∅, ∅]

theorem oriented_edges_complete : ∀ u v : Fin 10,u<v → graph.Adj u v →
    ∃ i,orientedEdges i=(u,v) := by decide +kernel

theorem positive_contexts_certificate : ∀ i : Fin 25,
    (orientedEdges i).1∉positiveContexts i ∧
    (orientedEdges i).2∉positiveContexts i ∧
    0<slackZ (orientedEdges i).1 (orientedEdges i).2 (positiveContexts i) := by decide +kernel

theorem positive_slack {u v : Fin 10} (he : graph.Adj u v) :
    ∃ S : Finset (Fin 10),u∉S ∧ v∉S ∧ 0<delta function u v S := by
  have ordered : ∀ u v : Fin 10,u<v → graph.Adj u v →
      ∃ S : Finset (Fin 10),u∉S ∧ v∉S ∧ 0<delta function u v S := by
    intro a b hab he
    obtain ⟨i,hi⟩:=oriented_edges_complete a b hab he
    have hc:=positive_contexts_certificate i
    rw [hi] at hc
    refine ⟨positiveContexts i,hc.1,hc.2.1,?_⟩
    rw [delta_eq_slackZ (ne_of_lt hab) hc.1 hc.2.1]
    exact_mod_cast hc.2.2
  rcases lt_or_gt_of_ne (graph.ne_of_adj he) with hlt | hgt
  · exact ordered u v hlt he
  · obtain ⟨S,hv,hu,hs⟩:=ordered v u hgt (graph.adj_symm he)
    exact ⟨S,hu,hv,by rw [delta_comm u v]; exact hs⟩

theorem graph_connected : graph.Connected := by
  apply graph.connected_iff_exists_forall_reachable.mpr
  refine ⟨0,fun v => ?_⟩
  by_cases hv : v=0
  · subst v
    exact SimpleGraph.Reachable.refl _
  · have ha : ∀ w : Fin 10,w≠0 → graph.Adj 0 w := by decide +kernel
    exact (ha v hv).reachable

theorem full_dimension : FullDimension (basePolytope function) := by
  exact finrank_vectorSpan_eq_of_connected_slacks normalized.1 supermodular graph_connected
    (fun _ _ he => by
      obtain ⟨S,hu,hv,hd⟩:=positive_slack he
      exact ⟨S,hu,hv,ne_of_gt hd⟩)

theorem actual_direction_graph : actualDirectionGraph (basePolytope function)=graph := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  constructor
  · intro h
    obtain ⟨R,hR,hRc,hnR,hsum⟩:=actual_summand
    exact basePolytope_summand_actualRootEdge normalized.1 supermodular graph
      (by norm_num : (0 : ℝ)≤4) R hsum h
  · intro he
    obtain ⟨S,hu,hv,hd⟩:=positive_slack he
    exact exposedSegment_of_positive_delta normalized.1 supermodular (graph.ne_of_adj he) hu hv hd

theorem edge_family_eq : edgeFamily graph=edges := by
  ext C
  by_cases hc : C.card=2
  · obtain ⟨u,v,huv,rfl⟩:=card_eq_two.mp hc
    rw [pair_mem_edgeFamily graph huv]
    change (u≠v ∧ ({u,v} : Finset (Fin 10))∈edges) ↔ _
    exact ⟨fun h => h.2,fun h => ⟨huv,h⟩⟩
  · have hnot : C∉edgeFamily graph := fun h => hc ((mem_edgeFamily graph C).mp h).1
    have hcard : ∀ D∈edges,D.card=2 := by decide +kernel
    have hnot' : C∉edges := fun h => hc (hcard C h)
    simp only [hnot,hnot']

theorem direction_count : directionCount (basePolytope function)=25 := by
  rw [directionCount,actual_direction_graph,edge_family_eq]
  decide

/-- The actual ten-vertex diamond polytope, with its full real tight kernel,
integer lattice, genuine Minkowski complement, full dimension, and exactly
25 actual exposed-edge directions. This is the finite witness used in8.1;
the unbounded classification is a separate theorem. -/
theorem diamond_polytope : LatticePolytope (basePolytope function) ∧
    MinkowskiIndecomposable (basePolytope function) ∧
    FullDimension (basePolytope function) ∧
    IsMinkowskiSummand (basePolytope function) ((4 : ℝ) • graphicalZonotope graph) ∧
    directionCount (basePolytope function)=25 :=
  ⟨lattice,indecomposable,full_dimension,actual_summand,direction_count⟩

end GraphicalZonotopes.DiamondGeometry
