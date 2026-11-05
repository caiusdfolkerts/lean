module
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A uniform triangle bound for graphs on ten vertices

The tables enumerate all pairs and triples of ten labels. Their enumeration
properties are checked by kernel reduction. The algebraic identity is
Goodman's counting identity, proved by polynomial normalization. No graph
is enumerated: the theorem quantifies over every edge set.
-/
namespace Papers.RationalityTen.MatroidChecked.GoodmanTen
open Finset
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def pair : Fin 45 → Finset (Fin 10) := ![{0, 1}, {0, 2}, {0, 3}, {0, 4}, {0, 5}, {0, 6}, {0, 7}, {0, 8}, {0, 9}, {1, 2}, {1, 3}, {1, 4}, {1, 5}, {1, 6}, {1, 7}, {1, 8}, {1, 9}, {2, 3}, {2, 4}, {2, 5}, {2, 6}, {2, 7}, {2, 8}, {2, 9}, {3, 4}, {3, 5}, {3, 6}, {3, 7}, {3, 8}, {3, 9}, {4, 5}, {4, 6}, {4, 7}, {4, 8}, {4, 9}, {5, 6}, {5, 7}, {5, 8}, {5, 9}, {6, 7}, {6, 8}, {6, 9}, {7, 8}, {7, 9}, {8, 9}]

def triple : Fin 120 → Finset (Fin 10) := ![{0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 1, 5}, {0, 1, 6}, {0, 1, 7}, {0, 1, 8}, {0, 1, 9}, {0, 2, 3}, {0, 2, 4}, {0, 2, 5}, {0, 2, 6}, {0, 2, 7}, {0, 2, 8}, {0, 2, 9}, {0, 3, 4}, {0, 3, 5}, {0, 3, 6}, {0, 3, 7}, {0, 3, 8}, {0, 3, 9}, {0, 4, 5}, {0, 4, 6}, {0, 4, 7}, {0, 4, 8}, {0, 4, 9}, {0, 5, 6}, {0, 5, 7}, {0, 5, 8}, {0, 5, 9}, {0, 6, 7}, {0, 6, 8}, {0, 6, 9}, {0, 7, 8}, {0, 7, 9}, {0, 8, 9}, {1, 2, 3}, {1, 2, 4}, {1, 2, 5}, {1, 2, 6}, {1, 2, 7}, {1, 2, 8}, {1, 2, 9}, {1, 3, 4}, {1, 3, 5}, {1, 3, 6}, {1, 3, 7}, {1, 3, 8}, {1, 3, 9}, {1, 4, 5}, {1, 4, 6}, {1, 4, 7}, {1, 4, 8}, {1, 4, 9}, {1, 5, 6}, {1, 5, 7}, {1, 5, 8}, {1, 5, 9}, {1, 6, 7}, {1, 6, 8}, {1, 6, 9}, {1, 7, 8}, {1, 7, 9}, {1, 8, 9}, {2, 3, 4}, {2, 3, 5}, {2, 3, 6}, {2, 3, 7}, {2, 3, 8}, {2, 3, 9}, {2, 4, 5}, {2, 4, 6}, {2, 4, 7}, {2, 4, 8}, {2, 4, 9}, {2, 5, 6}, {2, 5, 7}, {2, 5, 8}, {2, 5, 9}, {2, 6, 7}, {2, 6, 8}, {2, 6, 9}, {2, 7, 8}, {2, 7, 9}, {2, 8, 9}, {3, 4, 5}, {3, 4, 6}, {3, 4, 7}, {3, 4, 8}, {3, 4, 9}, {3, 5, 6}, {3, 5, 7}, {3, 5, 8}, {3, 5, 9}, {3, 6, 7}, {3, 6, 8}, {3, 6, 9}, {3, 7, 8}, {3, 7, 9}, {3, 8, 9}, {4, 5, 6}, {4, 5, 7}, {4, 5, 8}, {4, 5, 9}, {4, 6, 7}, {4, 6, 8}, {4, 6, 9}, {4, 7, 8}, {4, 7, 9}, {4, 8, 9}, {5, 6, 7}, {5, 6, 8}, {5, 6, 9}, {5, 7, 8}, {5, 7, 9}, {5, 8, 9}, {6, 7, 8}, {6, 7, 9}, {6, 8, 9}, {7, 8, 9}]

def triangleEdges : Fin 120 → Fin 3 → Fin 45 := ![![0, 1, 9], ![0, 2, 10], ![0, 3, 11], ![0, 4, 12], ![0, 5, 13], ![0, 6, 14], ![0, 7, 15], ![0, 8, 16], ![1, 2, 17], ![1, 3, 18], ![1, 4, 19], ![1, 5, 20], ![1, 6, 21], ![1, 7, 22], ![1, 8, 23], ![2, 3, 24], ![2, 4, 25], ![2, 5, 26], ![2, 6, 27], ![2, 7, 28], ![2, 8, 29], ![3, 4, 30], ![3, 5, 31], ![3, 6, 32], ![3, 7, 33], ![3, 8, 34], ![4, 5, 35], ![4, 6, 36], ![4, 7, 37], ![4, 8, 38], ![5, 6, 39], ![5, 7, 40], ![5, 8, 41], ![6, 7, 42], ![6, 8, 43], ![7, 8, 44], ![9, 10, 17], ![9, 11, 18], ![9, 12, 19], ![9, 13, 20], ![9, 14, 21], ![9, 15, 22], ![9, 16, 23], ![10, 11, 24], ![10, 12, 25], ![10, 13, 26], ![10, 14, 27], ![10, 15, 28], ![10, 16, 29], ![11, 12, 30], ![11, 13, 31], ![11, 14, 32], ![11, 15, 33], ![11, 16, 34], ![12, 13, 35], ![12, 14, 36], ![12, 15, 37], ![12, 16, 38], ![13, 14, 39], ![13, 15, 40], ![13, 16, 41], ![14, 15, 42], ![14, 16, 43], ![15, 16, 44], ![17, 18, 24], ![17, 19, 25], ![17, 20, 26], ![17, 21, 27], ![17, 22, 28], ![17, 23, 29], ![18, 19, 30], ![18, 20, 31], ![18, 21, 32], ![18, 22, 33], ![18, 23, 34], ![19, 20, 35], ![19, 21, 36], ![19, 22, 37], ![19, 23, 38], ![20, 21, 39], ![20, 22, 40], ![20, 23, 41], ![21, 22, 42], ![21, 23, 43], ![22, 23, 44], ![24, 25, 30], ![24, 26, 31], ![24, 27, 32], ![24, 28, 33], ![24, 29, 34], ![25, 26, 35], ![25, 27, 36], ![25, 28, 37], ![25, 29, 38], ![26, 27, 39], ![26, 28, 40], ![26, 29, 41], ![27, 28, 42], ![27, 29, 43], ![28, 29, 44], ![30, 31, 35], ![30, 32, 36], ![30, 33, 37], ![30, 34, 38], ![31, 32, 39], ![31, 33, 40], ![31, 34, 41], ![32, 33, 42], ![32, 34, 43], ![33, 34, 44], ![35, 36, 39], ![35, 37, 40], ![35, 38, 41], ![36, 37, 42], ![36, 38, 43], ![37, 38, 44], ![39, 40, 42], ![39, 41, 43], ![40, 41, 44], ![42, 43, 44]]

def incidentEdges : Fin 10 → Fin 9 → Fin 45 := ![![0, 1, 2, 3, 4, 5, 6, 7, 8], ![0, 9, 10, 11, 12, 13, 14, 15, 16], ![1, 9, 17, 18, 19, 20, 21, 22, 23], ![2, 10, 17, 24, 25, 26, 27, 28, 29], ![3, 11, 18, 24, 30, 31, 32, 33, 34], ![4, 12, 19, 25, 30, 35, 36, 37, 38], ![5, 13, 20, 26, 31, 35, 39, 40, 41], ![6, 14, 21, 27, 32, 36, 39, 42, 43], ![7, 15, 22, 28, 33, 37, 40, 42, 44], ![8, 16, 23, 29, 34, 38, 41, 43, 44]]

theorem pair_injective : Function.Injective pair := by decide +kernel

theorem triple_injective : Function.Injective triple := by decide +kernel

theorem pairs_exact : univ.image pair = (univ : Finset (Fin 10)).powersetCard 2 := by
  decide +kernel

theorem triples_exact : univ.image triple = (univ : Finset (Fin 10)).powersetCard 3 := by
  decide +kernel

theorem triangle_edges_exact (t : Fin 120) :
    (triple t).powersetCard 2 = univ.image (fun j => pair (triangleEdges t j)) := by
  revert t
  decide +kernel

theorem incident_edges_injective (v : Fin 10) : Function.Injective (incidentEdges v) := by
  revert v
  decide +kernel

theorem incident_edges_exact (v : Fin 10) :
    univ.image (fun j => pair (incidentEdges v j)) =
      ((univ : Finset (Fin 10)).powersetCard 2).filter (fun e => v ∈ e) := by
  revert v
  decide +kernel

def degreePolynomial (x : Fin 45 → ℚ) (v : Fin 10) : ℚ :=
  ∑ j : Fin 9, x (incidentEdges v j)

def trianglePolynomial (x : Fin 45 → ℚ) : ℚ :=
  ∑ t : Fin 120, ∏ j : Fin 3, x (triangleEdges t j)

def complementTrianglePolynomial (x : Fin 45 → ℚ) : ℚ :=
  ∑ t : Fin 120, ∏ j : Fin 3, (1 - x (triangleEdges t j))

/-- Goodman's identity, including the idempotence remainder for arbitrary
rational weights. Specializing to zero-one weights removes the remainder. -/
theorem goodman_identity (x : Fin 45 → ℚ) :
    2 * trianglePolynomial x + 2 * complementTrianglePolynomial x +
      (∑ v : Fin 10, degreePolynomial x v * (9 - degreePolynomial x v)) +
      2 * (∑ i : Fin 45, (x i * x i - x i)) = 240 := by
  norm_num [trianglePolynomial, complementTrianglePolynomial, degreePolynomial,
    triangleEdges, incidentEdges, Fin.sum_univ_succ, Fin.prod_univ_succ]
  ring

theorem weighted_triangle_bound (x : Fin 45 → ℚ)
    (hx : ∀ i, x i = 0 ∨ x i = 1)
    (hdegree : ∀ v, 3 ≤ degreePolynomial x v ∧ degreePolynomial x v ≤ 6) :
    trianglePolynomial x ≤ 30 := by
  have hrem : (∑ i : Fin 45, (x i * x i - x i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rcases hx i with h | h <;> rw [h] <;> norm_num
  have hc : 0 ≤ complementTrianglePolynomial x := by
    apply Finset.sum_nonneg
    intro t _
    apply Finset.prod_nonneg
    intro j _
    rcases hx (triangleEdges t j) with h | h <;> rw [h] <;> norm_num
  have hd (v : Fin 10) : 18 ≤ degreePolynomial x v * (9 - degreePolynomial x v) := by
    have h := mul_nonneg (sub_nonneg.mpr (hdegree v).1)
      (sub_nonneg.mpr (hdegree v).2)
    nlinarith
  have hs := Finset.sum_le_sum (s := (univ : Finset (Fin 10))) (fun v _ => hd v)
  norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat] at hs
  have hi := goodman_identity x
  rw [hrem] at hi
  linarith

def edgeWeight (E : Finset (Finset (Fin 10))) (i : Fin 45) : ℚ :=
  if pair i ∈ E then 1 else 0

def graphTriangles (E : Finset (Finset (Fin 10))) : Finset (Finset (Fin 10)) :=
  ((univ : Finset (Fin 10)).powersetCard 3).filter fun T => T.powersetCard 2 ⊆ E

private theorem weighted_card_image {a : ℕ} (f : Fin a → Finset (Fin 10))
    (hf : Function.Injective f) (E : Finset (Finset (Fin 10))) :
    (∑ i : Fin a, if f i ∈ E then (1 : ℚ) else 0) =
      (((univ.image f).filter (fun T => T ∈ E)).card : ℚ) := by
  rw [Finset.filter_image, Finset.card_image_of_injective _ hf]
  simp

theorem degreePolynomial_edgeWeight (E : Finset (Finset (Fin 10)))
    (hE : ∀ e ∈ E, e.card = 2) (v : Fin 10) :
    degreePolynomial (edgeWeight E) v = ((E.filter fun e => v ∈ e).card : ℚ) := by
  unfold degreePolynomial edgeWeight
  have hw := weighted_card_image (fun j => pair (incidentEdges v j))
    (pair_injective.comp (incident_edges_injective v)) E
  rw [hw, incident_edges_exact]
  congr 2
  ext e
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hE e h.1, h.2⟩, h.1⟩⟩

private theorem triangle_product (E : Finset (Finset (Fin 10))) (t : Fin 120) :
    (∏ j : Fin 3, edgeWeight E (triangleEdges t j)) =
      if (triple t).powersetCard 2 ⊆ E then (1 : ℚ) else 0 := by
  simp only [triangle_edges_exact, Finset.image_subset_iff, Finset.mem_univ, true_implies]
  by_cases h : ∀ j : Fin 3, pair (triangleEdges t j) ∈ E
  · rw [if_pos h]
    simp only [edgeWeight, h, if_true, Finset.prod_const_one]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨j, hj⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp only [edgeWeight, if_neg hj]

theorem trianglePolynomial_edgeWeight (E : Finset (Finset (Fin 10))) :
    trianglePolynomial (edgeWeight E) = ((graphTriangles E).card : ℚ) := by
  unfold trianglePolynomial
  simp_rw [triangle_product]
  calc
    (∑ t : Fin 120, if (triple t).powersetCard 2 ⊆ E then (1 : ℚ) else 0) =
        ∑ T ∈ univ.image triple, if T.powersetCard 2 ⊆ E then (1 : ℚ) else 0 := by
      rw [Finset.sum_image]
      intro a _ b _ h
      exact triple_injective h
    _ = ((graphTriangles E).card : ℚ) := by
      rw [triples_exact]
      simp [graphTriangles]

/-- Every graph on ten vertices with all degrees between three and six
has at most thirty triangles. The graph is an arbitrary edge set. -/
theorem triangle_card_le_thirty (E : Finset (Finset (Fin 10)))
    (hE : ∀ e ∈ E, e.card = 2)
    (hdegree : ∀ v : Fin 10, 3 ≤ (E.filter (fun e => v ∈ e)).card ∧
      (E.filter (fun e => v ∈ e)).card ≤ 6) :
    (graphTriangles E).card ≤ 30 := by
  have h := weighted_triangle_bound (edgeWeight E)
    (fun i => by unfold edgeWeight; split_ifs <;> simp)
    (fun v => by rw [degreePolynomial_edgeWeight E hE]; exact_mod_cast hdegree v)
  rw [trianglePolynomial_edgeWeight] at h
  exact_mod_cast h

end Papers.RationalityTen.MatroidChecked.GoodmanTen
