module

public import Papers.GraphicalZonotopes.GraphicalCone
public import Papers.GraphicalZonotopes.GraphModels

@[expose] public section

/-! Graphical zonotopes as genuine Minkowski sums of standard-basis segments. -/
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

def basisVector (v : V) : V → ℝ := Pi.single v 1

@[simp] theorem subsetSum_basisVector (v : V) (S : Finset V) :
    subsetSum (basisVector v) S = if v ∈ S then 1 else 0 := by
  simp [subsetSum, basisVector, Pi.single_apply, eq_comm]

theorem setMonomial_supermodular (C : Finset V) : Supermodular (setMonomial C) := by
  apply ElementallyNonnegative.supermodular
  intro u v huv S hu hv
  rw [delta_setMonomial huv hu hv]
  split <;> norm_num

theorem setMonomial_normalized {C : Finset V} (hC : C.Nonempty) :
    Normalized (setMonomial C) := by
  simp [Normalized, setMonomial, hC.ne_empty]

theorem basisVector_mem_basePair {u v : V} (huv : u ≠ v) :
    basisVector u ∈ basePolytope (setMonomial ({u, v} : Finset V)) := by
  refine ⟨by simp [setMonomial], ?_⟩
  intro S
  rw [subsetSum_basisVector]
  unfold setMonomial
  by_cases h : ({u, v} : Finset V) ⊆ S
  · have hu : u ∈ S := h (by simp)
    simp [h, hu]
  · simp only [if_neg h]
    split_ifs <;> norm_num

theorem basePair_eq_segment {u v : V} (huv : u ≠ v) :
    basePolytope (setMonomial ({u, v} : Finset V)) =
      segment ℝ (basisVector u) (basisVector v) := by
  apply Set.Subset.antisymm
  · intro x hx
    have htotal : subsetSum x univ = 1 := by simpa [setMonomial] using hx.1
    have hnonneg : ∀ j, 0 ≤ x j := by
      intro j
      have hpair : ¬({u, v} : Finset V) ⊆ {j} := by
        simp only [insert_subset_iff, singleton_subset_iff, mem_singleton]
        rintro ⟨rfl, rfl⟩
        exact huv rfl
      simpa [setMonomial, hpair, subsetSum] using hx.2 {j}
    have hzero : ∀ j, j ≠ u → j ≠ v → x j = 0 := by
      intro j hju hjv
      have hpair : ({u, v} : Finset V) ⊆ univ.erase j := by
        simp [insert_subset_iff, singleton_subset_iff, Ne.symm hju, Ne.symm hjv]
      have hmin : 1 ≤ subsetSum x (univ.erase j) := by
        simpa [setMonomial, hpair] using hx.2 (univ.erase j)
      have hsum : subsetSum x (univ.erase j) + x j = 1 := by
        rw [subsetSum, sum_erase_add _ _ (mem_univ j)]
        exact htotal
      linarith [hnonneg j]
    have hsupport : subsetSum x ({u, v} : Finset V) = subsetSum x univ := by
      apply sum_subset (subset_univ _)
      intro j hj hnot
      exact hzero j (fun h => hnot (by simp [h])) (fun h => hnot (by simp [h]))
    have hsum : x u + x v = 1 := by
      simpa [subsetSum, huv] using hsupport.trans htotal
    refine ⟨x u, x v, hnonneg u, hnonneg v, hsum, ?_⟩
    funext j
    by_cases hju : j = u
    · subst j
      simp [basisVector, Ne.symm huv]
    · by_cases hjv : j = v
      · subst j
        simp [basisVector, huv]
      · simp [basisVector, Pi.single_apply, hju, hjv, hzero j hju hjv,
          Ne.symm hju, Ne.symm hjv]
  · apply (basePolytope_convex _).segment_subset (basisVector_mem_basePair huv)
    simpa [pair_comm u v] using basisVector_mem_basePair (Ne.symm huv)

/-- Convex hull of the standard basis vectors indexed by a finite set. On a
two-element set this is precisely the standard-basis segment. -/
def coordinateSimplex (C : Finset V) : Set (V → ℝ) :=
  convexHull ℝ (basisVector '' (C : Set V))

theorem coordinateSimplex_pair (u v : V) :
    coordinateSimplex ({u, v} : Finset V) = segment ℝ (basisVector u) (basisVector v) := by
  simp [coordinateSimplex, convexHull_pair]

theorem baseMonomial_eq_coordinateSimplex {C : Finset V} (hC : C.card = 2) :
    basePolytope (setMonomial C) = coordinateSimplex C := by
  obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp hC
  rw [coordinateSimplex_pair, basePair_eq_segment huv]

@[simp] theorem basePolytope_zero : basePolytope (0 : SetFunction V) = {0} := by
  have hn : Normalized (0 : SetFunction V) := rfl
  have hs : Supermodular (0 : SetFunction V) := by intro A B; simp
  rw [basePolytope_eq_convexHull hn hs]
  have he : greedyPoints (0 : SetFunction V) = {0} := by
    ext x
    constructor
    · rintro ⟨e, rfl⟩
      change greedyPoint (0 : SetFunction V) e = 0
      funext v
      simp [greedyPoint]
    · rintro rfl
      exact ⟨(Fintype.equivFin V).symm, by ext v; simp [greedyPoint]⟩
  rw [he, convexHull_singleton]

theorem Supermodular.finset_sum {I : Type*} (s : Finset I) (f : I → SetFunction V)
    (hs : ∀ i ∈ s, Supermodular (f i)) : Supermodular (∑ i ∈ s, f i) := by
  intro A B
  simp only [Finset.sum_apply]
  have h := sum_le_sum (fun i hi => hs i hi A B)
  simpa [sum_add_distrib] using h

theorem basePolytope_sum {I : Type*} (s : Finset I) (f : I → SetFunction V)
    (hn : ∀ i ∈ s, Normalized (f i)) (hs : ∀ i ∈ s, Supermodular (f i)) :
    basePolytope (∑ i ∈ s, f i) = ∑ i ∈ s, basePolytope (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty,basePolytope_zero]; rfl
  | @insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi]
    have hn' : Normalized (∑ j ∈ s, f j) := by
      simp only [Normalized, Finset.sum_apply]
      exact sum_eq_zero (fun j hj => hn j (mem_insert_of_mem hj))
    rw [basePolytope_add (hn i (mem_insert_self _ _)) hn'
      (hs i (mem_insert_self _ _)) (Supermodular.finset_sum s f (fun j hj => hs j (mem_insert_of_mem hj))),
      ih (fun j hj => hn j (mem_insert_of_mem hj)) (fun j hj => hs j (mem_insert_of_mem hj))]

/-- The lower set function counts edges in the induced subgraph. -/
def graphFunction (G : SimpleGraph V) : SetFunction V :=
  ∑ C ∈ edgeFamily G, setMonomial C

/-- The actual graphical zonotope, built by Minkowski summation of edge segments. -/
def graphicalZonotope (G : SimpleGraph V) : Set (V → ℝ) :=
  ∑ C ∈ edgeFamily G, coordinateSimplex C

theorem graphFunction_normalized (G : SimpleGraph V) : Normalized (graphFunction G) := by
  simp only [Normalized, graphFunction, Finset.sum_apply]
  apply sum_eq_zero
  intro C hC
  have hc := (mem_edgeFamily G C).mp hC
  exact setMonomial_normalized (card_pos.mp (by omega))

theorem graphFunction_supermodular (G : SimpleGraph V) : Supermodular (graphFunction G) :=
  Supermodular.finset_sum _ _ (fun C hC => setMonomial_supermodular C)

theorem baseGraphFunction_eq_graphicalZonotope (G : SimpleGraph V) :
    basePolytope (graphFunction G) = graphicalZonotope G := by
  rw [graphFunction, basePolytope_sum]
  · apply sum_congr rfl
    intro C hC
    exact baseMonomial_eq_coordinateSimplex ((mem_edgeFamily G C).mp hC).1
  · intro C hC
    have hc := ((mem_edgeFamily G C).mp hC).1
    exact setMonomial_normalized (card_pos.mp (by omega))
  · exact fun C hC => setMonomial_supermodular C

/-- The graphical zonotope has unit elemental slack on each graph edge, and
zero elemental slack on every nonedge, in every conditioning context. -/
theorem graphFunction_delta (G : SimpleGraph V) {u v : V} (huv : u ≠ v)
    {S : Finset V} (hu : u ∉ S) (hv : v ∉ S) :
    delta (graphFunction G) u v S = if G.Adj u v then 1 else 0 := by
  classical
  rw [graphFunction, delta_sum]
  have hrow : ∀ C ∈ edgeFamily G,
      delta (setMonomial C) u v S = if C = {u,v} then 1 else 0 := by
    intro C hC
    rw [delta_setMonomial huv hu hv]
    by_cases he : C = {u,v}
    · subst C
      simp
    · have hpair : ¬(u ∈ C ∧ v ∈ C) := by
        rintro ⟨huC,hvC⟩
        apply he
        apply Eq.symm
        apply Finset.eq_of_subset_of_card_le
        · intro w hw
          simp only [mem_insert, mem_singleton] at hw
          rcases hw with rfl | rfl <;> assumption
        · rw [(mem_edgeFamily G C).mp hC |>.1, card_pair huv]
      have hzero : ¬(u∈C ∧ v∈C ∧ C⊆insert u (insert v S)) := by tauto
      simp only [if_neg he,if_neg hzero]
  rw [sum_congr rfl hrow]
  simp [pair_mem_edgeFamily G huv]

theorem graphFunction_translationNormalized (G : SimpleGraph V) :
    TranslationNormalized (graphFunction G) := by
  refine ⟨graphFunction_normalized G, ?_⟩
  intro v
  simp only [graphFunction, Finset.sum_apply]
  apply sum_eq_zero
  intro C hC
  have hc := (mem_edgeFamily G C).mp hC |>.1
  have hnot : ¬C ⊆ {v} := by
    intro h
    have hcard := card_le_card h
    simp [hc] at hcard
  simp [setMonomial, hnot]

/-- Bounded genuine elemental slacks give an actual complementary base
polytope in the indicated dilation of the graphical zonotope. -/
theorem graphical_complement_supermodular {G : SimpleGraph V} {z : SetFunction V}
    (hG : Graphical G z) {a : ℝ} (ha : 0 ≤ a)
    (hub : ∀ u v, u ≠ v → G.Adj u v → ∀ S, u ∉ S → v ∉ S →
      delta z u v S ≤ a) : Supermodular (a • graphFunction G - z) := by
  apply ElementallyNonnegative.supermodular
  intro u v huv S hu hv
  rw [delta_sub, delta_smul, graphFunction_delta G huv hu hv]
  by_cases hedge : G.Adj u v
  · simp only [if_pos hedge, mul_one]
    exact sub_nonneg.mpr (hub u v huv hedge S hu hv)
  · rw [if_neg hedge, hG u v huv hedge S hu hv]
    simp

theorem basePolytope_add_graphical_complement {G : SimpleGraph V} {z : SetFunction V}
    (hn : Normalized z) (hs : Supermodular z) (hG : Graphical G z)
    {a : ℝ} (ha : 0 ≤ a)
    (hub : ∀ u v, u ≠ v → G.Adj u v → ∀ S, u ∉ S → v ∉ S →
      delta z u v S ≤ a) :
    basePolytope z + basePolytope (a • graphFunction G - z) = a • graphicalZonotope G := by
  have hcn : Normalized (a • graphFunction G - z) := by
    change a*graphFunction G ∅-z ∅=0
    rw [graphFunction_normalized G,hn]
    ring
  have hcs := graphical_complement_supermodular hG ha hub
  rw [← basePolytope_add hn hcn hs hcs]
  have he : z + (a • graphFunction G - z) = a • graphFunction G := by module
  rw [he, basePolytope_smul (graphFunction_normalized G) (graphFunction_supermodular G) ha,
    baseGraphFunction_eq_graphicalZonotope]

end GraphicalZonotopes
