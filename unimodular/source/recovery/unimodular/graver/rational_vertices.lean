module

public import Recovery.Unimodular.WeakFano.WeightedPolytope
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators Topology Matrix
open Set

namespace Unimodular.RationalVertices

variable {n r : ℕ}

/-- The ordinary real polyhedron given by the supplied integer inequalities. -/
def carrier (a : Fin r → Lattice n) (b : Fin r → ℤ) : Set (Ambient n) :=
  {x | ∀ i, pairing x (a i) ≤ (b i : ℝ)}

def rowMatrix (a : Fin r → Lattice n) (s : Fin n → Fin r) :
    Matrix (Fin n) (Fin n) ℤ := fun i j => a (s i) j

/-- Cramer's formula uses only exact integer determinants and rational division. -/
def corner (a : Fin r → Lattice n) (b : Fin r → ℤ) (s : Fin n → Fin r) :
    Fin n → ℚ := fun j =>
  (Matrix.cramer (rowMatrix a s) (b ∘ s) j : ℚ) / ((rowMatrix a s).det : ℚ)

def satisfies (a : Fin r → Lattice n) (b : Fin r → ℤ) (x : Fin n → ℚ) : Prop :=
  ∀ i, (∑ j, x j * (a i j : ℚ)) ≤ (b i : ℚ)

instance (a : Fin r → Lattice n) (b : Fin r → ℤ) (x : Fin n → ℚ) :
    Decidable (satisfies a b x) := by unfold satisfies; infer_instance

/-- A completely executable finite list of all feasible nonsingular corners. -/
def vertices (a : Fin r → Lattice n) (b : Fin r → ℤ) : Finset (Fin n → ℚ) :=
  ((Finset.univ : Finset (Fin n → Fin r)).filter (fun s =>
    (rowMatrix a s).det ≠ 0 ∧ satisfies a b (corner a b s))).image (corner a b)

/-- The standard rational-to-real embedding. -/
def ratEmbed (x : Fin n → ℚ) : Ambient n := fun j => (x j : ℝ)

noncomputable section

@[simp] theorem satisfies_iff (a : Fin r → Lattice n) (b : Fin r → ℤ)
    (x : Fin n → ℚ) : satisfies a b x ↔ ratEmbed x ∈ carrier a b := by
  change (∀ i, (∑ j, x j * (a i j : ℚ)) ≤ (b i : ℚ)) ↔
    ∀ i, (∑ j, (x j : ℝ) * (a i j : ℝ)) ≤ (b i : ℝ)
  constructor
  · intro h i
    have hi := (Rat.cast_le (K := ℝ)).2 (h i)
    simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast] using hi
  · intro h i
    apply (Rat.cast_le (K := ℝ)).1
    simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast] using h i

theorem carrier_convex (a : Fin r → Lattice n) (b : Fin r → ℤ) :
    Convex ℝ (carrier a b) := by
  intro x hx y hy c d hc hd hcd i
  rw [pairing_add_left, pairing_smul_left, pairing_smul_left]
  calc
    c * pairing x (a i) + d * pairing y (a i) ≤
        c * (b i : ℝ) + d * (b i : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left (hx i) hc)
        (mul_le_mul_of_nonneg_left (hy i) hd)
    _ = (b i : ℝ) := by rw [← add_mul, hcd, one_mul]

theorem carrier_isClosed (a : Fin r → Lattice n) (b : Fin r → ℤ) :
    IsClosed (carrier a b) := by
  simp only [carrier, Set.setOf_forall]
  exact isClosed_iInter fun i =>
    isClosed_le (WeightedPolytopes.pairing_continuous (a i)) continuous_const

/-- At a genuine extreme point the active integral normals span the real space.
No simplicity, full dimension, or unimodularity is assumed. -/
theorem active_span (a : Fin r → Lattice n) (b : Fin r → ℤ)
    {x : Ambient n} (hx : x ∈ (carrier a b).extremePoints ℝ) :
    Submodule.span ℝ (Set.range (fun i : {i // pairing x (a i) = (b i : ℝ)} =>
      embed (a i.val))) = ⊤ := by
  classical
  by_contra hspan
  obtain ⟨f, hf, hker⟩ :=
    (Submodule.span ℝ (Set.range (fun i : {i // pairing x (a i) = (b i : ℝ)} =>
      embed (a i.val)))).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hspan)
  let d : Ambient n := fun j => f (Pi.single j 1)
  have hd : d ≠ 0 := by
    intro hd0
    apply hf
    apply LinearMap.ext
    intro z
    change f z = 0
    rw [linearMap_eq_realPairing f z]
    change realPairing z d = 0
    rw [hd0]
    simp [realPairing]
  have ha (i : Fin r) (hi : pairing x (a i) = (b i : ℝ)) :
      pairing d (a i) = 0 := by
    have hh : f (embed (a i)) = 0 :=
      hker (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
    rw [linearMap_eq_realPairing f] at hh
    change realPairing d (embed (a i)) = 0
    change realPairing (embed (a i)) d = 0 at hh
    rwa [realPairing_comm] at hh
  obtain ⟨t, ht, hstep⟩ := exists_pos_feasible_step (Finset.univ : Finset (Fin r))
    (fun i => (b i : ℝ) - pairing x (a i)) (fun i => |pairing d (a i)|)
    (fun i _ => sub_nonneg.mpr (hx.1 i)) (by
      intro i hi he
      simp only [ha i (by linarith), abs_zero, le_refl])
  have hp : x + t • d ∈ carrier a b := by
    intro i
    rw [pairing_add_left, pairing_smul_left]
    have hh := (mul_le_mul_of_nonneg_left (le_abs_self (pairing d (a i))) ht.le).trans
      (hstep i (Finset.mem_univ _))
    linarith
  have hm : x + t • (-d) ∈ carrier a b := by
    intro i
    rw [pairing_add_left, pairing_smul_left]
    have he : pairing (-d) (a i) = -pairing d (a i) := by
      simp [pairing, Finset.sum_neg_distrib]
    rw [he]
    have hh := (mul_le_mul_of_nonneg_left (neg_le_abs (pairing d (a i))) ht.le).trans
      (hstep i (Finset.mem_univ _))
    linarith
  have he : x + t • d = x := hx.2 hp hm
    ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, by module⟩
  have hz : t • d = 0 := add_left_cancel (he.trans (add_zero x).symm)
  exact hd ((smul_eq_zero.1 hz).resolve_left ht.ne')

/-- Select an active real basis, without assuming an integral basis. -/
theorem active_tuple (a : Fin r → Lattice n) (b : Fin r → ℤ)
    {x : Ambient n} (hx : x ∈ (carrier a b).extremePoints ℝ) :
    ∃ s : Fin n → Fin r, LinearIndependent ℝ (fun j => embed (a (s j))) ∧
      ∀ j, pairing x (a (s j)) = (b (s j) : ℝ) := by
  classical
  let S := Set.range (fun i : {i // pairing x (a i) = (b i : ℝ)} => embed (a i.val))
  let v : Empty → Ambient n := fun i => i.elim
  have hv : LinearIndependent ℝ v := linearIndependent_empty_type
  have hsub : Set.range v ⊆ S := by
    rintro _ ⟨i, _⟩
    exact i.elim
  have hspan : ⊤ ≤ Submodule.span ℝ S := (active_span a b hx).ge
  let B := Module.Basis.extendLe hv.linearIndepOn_id hsub hspan
  let e := B.indexEquiv (Pi.basisFun ℝ (Fin n))
  let B' := B.reindex e
  have hB : Set.range B' ⊆ S := by
    rw [show Set.range B' = Set.range B from B.range_reindex e]
    exact Module.Basis.extendLe_subset hv.linearIndepOn_id hsub hspan
  have hh : ∀ j : Fin n, ∃ i : Fin r,
      pairing x (a i) = (b i : ℝ) ∧ embed (a i) = B' j := by
    intro j
    obtain ⟨i, hi⟩ := hB ⟨j, rfl⟩
    exact ⟨i.val, i.property, hi⟩
  choose s hs he using hh
  refine ⟨s, ?_, hs⟩
  have heq : (fun j => embed (a (s j))) = B' := funext he
  rw [heq]
  exact B'.linearIndependent

/-- Exact compatibility of Cramer's integer numerators with real casting. -/
theorem cramer_cast (A : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) (j : Fin n) :
    (Matrix.cramer A b j : ℝ) =
      Matrix.cramer (A.map (fun z => (z : ℝ))) (fun i => (b i : ℝ)) j := by
  simp only [Matrix.cramer_apply, Int.cast_det]
  congr 1
  ext i k
  by_cases hk : k = j <;> simp [Matrix.updateCol_apply, Matrix.map_apply, hk]

/-- Every genuine extreme point equals one of the explicitly enumerated corners. -/
theorem extreme_mem_vertices (a : Fin r → Lattice n) (b : Fin r → ℤ)
    {x : Ambient n} (hx : x ∈ (carrier a b).extremePoints ℝ) :
    x ∈ ratEmbed '' (vertices a b : Set (Fin n → ℚ)) := by
  classical
  obtain ⟨s, hli, hs⟩ := active_tuple a b hx
  let A := rowMatrix a s
  let AR : Matrix (Fin n) (Fin n) ℝ := A.map (fun z => (z : ℝ))
  have hliR : LinearIndependent ℝ AR.row := hli
  have hdR : AR.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det AR).1 (Matrix.linearIndependent_row_iff_isUnit.1 hliR)).ne_zero
  have hd : A.det ≠ 0 := by
    intro h
    apply hdR
    change (A.map (fun z => (z : ℝ))).det = 0
    rw [← Int.cast_det, h, Int.cast_zero]
  have hAx : AR *ᵥ x = fun i => (b (s i) : ℝ) := by
    ext i
    change (∑ j, (a (s i) j : ℝ) * x j) = _
    simpa only [pairing, mul_comm] using hs i
  have hcr : Matrix.cramer AR (fun i => (b (s i) : ℝ)) = AR.det • x := by
    rw [Matrix.cramer_eq_adjugate_mulVec, ← hAx, Matrix.mulVec_mulVec,
      Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have he : ratEmbed (corner a b s) = x := by
    ext j
    change (((Matrix.cramer A (b ∘ s) j : ℚ) / (A.det : ℚ) : ℚ) : ℝ) = x j
    rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast, cramer_cast]
    change Matrix.cramer AR (fun i => (b (s i) : ℝ)) j / (A.det : ℝ) = x j
    rw [hcr]
    change AR.det * x j / (A.det : ℝ) = x j
    rw [Int.cast_det]
    exact mul_div_cancel_left₀ (x j) hdR
  refine ⟨corner a b s, ?_, he⟩
  apply Finset.mem_image.2
  refine ⟨s, Finset.mem_filter.2 ⟨Finset.mem_univ _, hd, ?_⟩, rfl⟩
  rw [satisfies_iff, he]
  exact hx.1

theorem vertices_subset (a : Fin r → Lattice n) (b : Fin r → ℤ) :
    ratEmbed '' (vertices a b : Set (Fin n → ℚ)) ⊆ carrier a b := by
  rintro x ⟨q, hq, rfl⟩
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hq
  exact (satisfies_iff _ _ _).1 (Finset.mem_filter.1 hs).2.2

/-- An actual compact integer-halfspace polytope is exactly the convex hull of
its computably listed rational corners, including empty and lower-dimensional cases. -/
theorem carrier_eq_convexHull_vertices (a : Fin r → Lattice n) (b : Fin r → ℤ)
    (hc : IsCompact (carrier a b)) :
    carrier a b = convexHull ℝ (ratEmbed '' (vertices a b : Set (Fin n → ℚ))) := by
  apply Set.Subset.antisymm
  · rw [← closure_convexHull_extremePoints hc (carrier_convex a b)]
    apply closure_minimal
    · exact convexHull_min (fun x hx => subset_convexHull ℝ _ (extreme_mem_vertices a b hx))
        (convex_convexHull ℝ _)
    · exact ((vertices a b).finite_toSet.image ratEmbed).isClosed_convexHull ℝ
  · exact convexHull_min (vertices_subset a b) (carrier_convex a b)

end
end Unimodular.RationalVertices

#print axioms Unimodular.RationalVertices.active_span
#print axioms Unimodular.RationalVertices.extreme_mem_vertices
#print axioms Unimodular.RationalVertices.carrier_eq_convexHull_vertices
#check Unimodular.RationalVertices.carrier_eq_convexHull_vertices
