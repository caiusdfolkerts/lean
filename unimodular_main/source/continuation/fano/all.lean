module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Option
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.RingTheory.Noetherian.Orzech
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Unimodular
public import Unimodular.Extensions
public import Unimodular.Geometry

@[expose] public section

section FanoSource0


/-!
# A finite vertex description for bundles of simplices

Over a polytope `P`, attach one simplex whose size is the slack of each
defining inequality. The resulting set is again a polytope. Its vertices
are obtained by taking a vertex of `P` and a vertex of each fibre simplex.
The proof uses supporting linear forms, so it includes zero-dimensional
fibres and vanishing slacks without separate genericity assumptions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Unimodular.SimplexBundle

open Set
open scoped BigOperators

variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
variable (J : E → Type*) [∀ e, Fintype (J e)] [∀ e, DecidableEq (J e)]

noncomputable section

abbrev Extra := Sigma J
abbrev IntegralSpace := Lattice n × (Extra J → ℤ)
abbrev RealSpace := Ambient n × (Extra J → ℝ)
abbrev Choice := (e : E) → Option (J e)

def embed (z : IntegralSpace (n := n) J) : RealSpace (n := n) J :=
  (Unimodular.embed z.1, fun s => (z.2 s : ℝ))

def slack (A : E → Lattice n) (h : E → ℤ) (x : Ambient n) (e : E) : ℝ :=
  (h e : ℝ) - pairing x (A e)

def carrier (A : E → Lattice n) (h : E → ℤ) : Set (RealSpace (n := n) J) :=
  {z | ∀ e, (∀ j, 0 ≤ z.2 ⟨e, j⟩) ∧ (∑ j, z.2 ⟨e, j⟩) ≤ slack A h z.1 e}

def base (A : E → Lattice n) (h : E → ℤ) : Set (Ambient n) :=
  {x | ∀ e, pairing x (A e) ≤ (h e : ℝ)}

def corner (A : E → Lattice n) (h : E → ℤ) (v : Lattice n) (c : Choice J) :
    IntegralSpace (n := n) J :=
  (v, fun s => if c s.1 = some s.2 then h s.1 - integerPairing v (A s.1) else 0)

def vertices (A : E → Lattice n) (h : E → ℤ) (S : Finset (Lattice n)) :
    Finset (IntegralSpace (n := n) J) :=
  S.biUnion (fun v => Finset.univ.image (corner J A h v))

theorem projection_mem_base (A : E → Lattice n) (h : E → ℤ)
    {z : RealSpace (n := n) J} (hz : z ∈ carrier J A h) : z.1 ∈ base A h := by
  intro e
  have hn : 0 ≤ ∑ j, z.2 ⟨e, j⟩ := Finset.sum_nonneg fun j _ => (hz e).1 j
  have hh := (hz e).2
  dsimp [slack] at hh
  linarith

theorem corner_extra (A : E → Lattice n) (h : E → ℤ) (v : Lattice n)
    (c : Choice J) (e : E) (j : J e) :
    (embed J (corner J A h v c)).2 ⟨e, j⟩ =
      if c e = some j then slack A h (Unimodular.embed v) e else 0 := by
  simp only [embed, corner]
  split_ifs <;> simp [slack, pairing_embed]

theorem corner_mem (A : E → Lattice n) (h : E → ℤ) (v : Lattice n)
    (hv : Unimodular.embed v ∈ base A h) (c : Choice J) :
    embed J (corner J A h v c) ∈ carrier J A h := by
  intro e
  have hs : 0 ≤ slack A h (Unimodular.embed v) e := sub_nonneg.mpr (hv e)
  constructor
  · intro j
    rw [corner_extra]
    split_ifs <;> positivity
  · change (∑ j, (embed J (corner J A h v c)).2 ⟨e, j⟩) ≤
      slack A h (Unimodular.embed v) e
    simp_rw [corner_extra]
    cases hc : c e with
    | none => simpa [hc] using hs
    | some j => simp [hc]

theorem carrier_convex (A : E → Lattice n) (h : E → ℤ) :
    Convex ℝ (carrier J A h) := by
  intro x hx y hy a b ha hb hab e
  constructor
  · intro j
    exact add_nonneg (mul_nonneg ha ((hx e).1 j))
      (mul_nonneg hb ((hy e).1 j))
  · have hh := add_le_add (mul_le_mul_of_nonneg_left ((hx e).2) ha)
      (mul_le_mul_of_nonneg_left ((hy e).2) hb)
    change (∑ j, (a * x.2 ⟨e,j⟩ + b * y.2 ⟨e,j⟩)) ≤ _
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    refine hh.trans_eq ?_
    change a * slack A h x.1 e + b * slack A h y.1 e =
      slack A h (a • x.1 + b • y.1) e
    simp only [slack, pairing_add_left, pairing_smul_left]
    calc
      _ = (a + b) * (h e : ℝ) - (a * pairing x.1 (A e) + b * pairing y.1 (A e)) := by ring
      _ = _ := by rw [hab, one_mul]

def coefficient (f : Module.Dual ℝ (RealSpace (n := n) J)) (s : Extra J) : ℝ :=
  f (0, Pi.single s 1)

def choiceValue (f : Module.Dual ℝ (RealSpace (n := n) J)) (e : E)
    (c : Option (J e)) : ℝ := c.elim 0 (fun j => coefficient J f ⟨e,j⟩)

theorem linear_decomposition (f : Module.Dual ℝ (RealSpace (n := n) J))
    (z : RealSpace (n := n) J) :
    f z = f (z.1, 0) + ∑ e, ∑ j, z.2 ⟨e,j⟩ * coefficient J f ⟨e,j⟩ := by
  have hz : z = (z.1, 0) + ∑ s : Extra J, z.2 s • (0, Pi.single s (1 : ℝ)) := by
    apply Prod.ext
    · simp [Prod.fst_sum]
    · ext s
      simp [Prod.snd_sum, Pi.single_apply]
  calc
    f z = f ((z.1, 0) + ∑ s : Extra J, z.2 s • (0, Pi.single s (1 : ℝ))) :=
      congrArg f hz
    _ = f (z.1, 0) + ∑ s : Extra J, z.2 s * coefficient J f s := by
      rw [map_add, map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro s _
      exact f.map_smul (z.2 s) (0, Pi.single s 1)
    _ = _ := by rw [Fintype.sum_sigma]

theorem corner_evaluation (A : E → Lattice n) (h : E → ℤ)
    (f : Module.Dual ℝ (RealSpace (n := n) J)) (v : Lattice n) (c : Choice J) :
    f (embed J (corner J A h v c)) = f (Unimodular.embed v, 0) +
      ∑ e, choiceValue J f e (c e) * slack A h (Unimodular.embed v) e := by
  rw [linear_decomposition]
  change f (Unimodular.embed v, 0) + _ = _
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  simp_rw [corner_extra]
  cases hc : c e with
  | none => simp [hc, choiceValue]
  | some j => simp [hc, choiceValue, mul_comm]

theorem exists_max_corner (A : E → Lattice n) (h : E → ℤ)
    (S : Finset (Lattice n)) (hS : S.Nonempty)
    (hbase : base A h = convexHull ℝ (Unimodular.embed '' (S : Set (Lattice n))))
    (f : Module.Dual ℝ (RealSpace (n := n) J)) :
    ∃ v ∈ S, ∃ c : Choice J, ∀ z ∈ carrier J A h,
      f z ≤ f (embed J (corner J A h v c)) := by
  classical
  have hm (e : E) : ∃ c : Option (J e), ∀ d : Option (J e),
      choiceValue J f e d ≤ choiceValue J f e c := by
    obtain ⟨c, _, hc⟩ := (Finset.univ : Finset (Option (J e))).exists_max_image
      (choiceValue J f e) ⟨none, Finset.mem_univ _⟩
    exact ⟨c, fun d => hc d (Finset.mem_univ _)⟩
  choose c hc using hm
  let m : E → ℝ := fun e => choiceValue J f e (c e)
  have hm0 (e : E) : 0 ≤ m e := hc e none
  have hmj (e : E) (j : J e) : coefficient J f ⟨e,j⟩ ≤ m e := hc e (some j)
  let g : Module.Dual ℝ (Ambient n) :=
    { toFun := fun x => f (x,0) - ∑ e, m e * pairing x (A e)
      map_add' := by
        intro x y
        have hf : f (x+y,0) = f (x,0) + f (y,0) := by simpa using f.map_add (x,0) (y,0)
        simp only [hf, pairing_add_left, mul_add, Finset.sum_add_distrib]
        ring
      map_smul' := by
        intro a x
        have hf : f (a • x,0) = a * f (x,0) := by simpa using f.map_smul a (x,0)
        simp only [hf, pairing_smul_left, RingHom.id_apply, smul_eq_mul]
        rw [mul_sub, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro e he
        ring }
  obtain ⟨v, hv, hvmax⟩ := S.exists_max_image (fun v => g (Unimodular.embed v)) hS
  have hgmax : ∀ x ∈ base A h, g x ≤ g (Unimodular.embed v) := by
    rw [hbase]
    change convexHull ℝ (Unimodular.embed '' (S : Set (Lattice n))) ⊆
      {x | g x ≤ g (Unimodular.embed v)}
    apply convexHull_min
    · rintro _ ⟨w, hw, rfl⟩
      exact hvmax w hw
    · exact convex_halfSpace_le g.isLinear _
  refine ⟨v, hv, c, ?_⟩
  intro z hz
  have hsum (e : E) :
      (∑ j, z.2 ⟨e,j⟩ * coefficient J f ⟨e,j⟩) ≤ m e * slack A h z.1 e := by
    calc
      (∑ j, z.2 ⟨e,j⟩ * coefficient J f ⟨e,j⟩) ≤ ∑ j, z.2 ⟨e,j⟩ * m e :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hmj e j) ((hz e).1 j)
      _ = m e * ∑ j, z.2 ⟨e,j⟩ := by rw [Finset.mul_sum]; simp only [mul_comm]
      _ ≤ m e * slack A h z.1 e := mul_le_mul_of_nonneg_left ((hz e).2) (hm0 e)
  calc
    f z = f (z.1,0) + ∑ e, ∑ j, z.2 ⟨e,j⟩ * coefficient J f ⟨e,j⟩ :=
      linear_decomposition J f z
    _ ≤ f (z.1,0) + ∑ e, m e * slack A h z.1 e :=
      add_le_add le_rfl (Finset.sum_le_sum fun e _ => hsum e)
    _ = g z.1 + ∑ e, m e * (h e : ℝ) := by
      simp only [g, LinearMap.coe_mk, AddHom.coe_mk, slack, mul_sub,
        Finset.sum_sub_distrib]
      ring
    _ ≤ g (Unimodular.embed v) + ∑ e, m e * (h e : ℝ) :=
      add_le_add (hgmax z.1 (projection_mem_base J A h hz)) le_rfl
    _ = f (embed J (corner J A h v c)) := by
      rw [corner_evaluation]
      change f (Unimodular.embed v,0) - _ + _ = _
      simp only [slack, mul_sub, Finset.sum_sub_distrib]
      ring

/-- An exact finite lattice-polytope presentation of the whole simplex bundle. -/
theorem carrier_eq_convexHull_vertices (A : E → Lattice n) (h : E → ℤ)
    (S : Finset (Lattice n)) (hS : S.Nonempty)
    (hbase : base A h = convexHull ℝ (Unimodular.embed '' (S : Set (Lattice n)))) :
    carrier J A h = convexHull ℝ (embed J '' (vertices J A h S : Set (IntegralSpace (n := n) J))) := by
  classical
  apply Set.Subset.antisymm
  · intro z hz
    by_contra hnot
    obtain ⟨f, a, hfa, haz⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ _)
      (((vertices J A h S).finite_toSet.image (embed J)).isClosed_convexHull ℝ) hnot
    obtain ⟨v, hv, c, hmax⟩ := exists_max_corner J A h S hS hbase f.toLinearMap
    have hvc : corner J A h v c ∈ vertices J A h S :=
      Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩⟩
    have hlt := hfa _ (subset_convexHull ℝ _ ⟨corner J A h v c, hvc, rfl⟩)
    have hle := hmax z hz
    exact (not_lt_of_ge hle) (hlt.trans haz)
  · apply convexHull_min _ (carrier_convex J A h)
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨v, hv, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hz
    apply corner_mem
    rw [hbase]
    exact subset_convexHull ℝ _ ⟨v, hv, rfl⟩

end
end Unimodular.SimplexBundle

#print axioms Unimodular.SimplexBundle.carrier_eq_convexHull_vertices

end FanoSource0

section FanoSource1


/-!
# The integer matrix of a Fano multiwedge

Each new coordinate belongs to one old column. The old column receives a
minus one in all of its new coordinates, and every new coordinate contributes
its positive coordinate vector. The proof applies to arbitrary finite blocks;
in particular, their sizes need not agree.
-/

namespace Unimodular.Multiwedge

open Matrix

variable {I E S : Type*} [DecidableEq I] [DecidableEq E] [DecidableEq S]

/-- The rows added below the original matrix. -/
def privateRows (owner : S → E) : Matrix S E ℤ :=
  fun s e => if owner s = e then -1 else 0

/-- The positive unit columns in the new coordinates. -/
def privateColumns : Matrix (I ⊕ S) S ℤ :=
  fun i s => if i = Sum.inr s then 1 else 0

/-- The complete matrix of lifted old rays and pure extra rays. -/
def matrix (A : Matrix I E ℤ) (owner : S → E) : Matrix (I ⊕ S) (E ⊕ S) ℤ :=
  Matrix.fromCols (Matrix.fromRows A (privateRows owner)) privateColumns

@[simp] theorem matrix_inl_inl (A : Matrix I E ℤ) (owner : S → E) (i : I) (e : E) :
    matrix A owner (Sum.inl i) (Sum.inl e) = A i e := rfl

@[simp] theorem matrix_inr_inl (A : Matrix I E ℤ) (owner : S → E) (s : S) (e : E) :
    matrix A owner (Sum.inr s) (Sum.inl e) = if owner s = e then -1 else 0 := rfl

@[simp] theorem matrix_inl_inr (A : Matrix I E ℤ) (owner : S → E) (i : I) (s : S) :
    matrix A owner (Sum.inl i) (Sum.inr s) = 0 := by
  simp [matrix, privateColumns]

@[simp] theorem matrix_inr_inr (A : Matrix I E ℤ) (owner : S → E) (s t : S) :
    matrix A owner (Sum.inr s) (Sum.inr t) = if s = t then 1 else 0 := by
  simp [matrix, privateColumns]

/-- The multiwedge preserves every square minor bound, in all dimensions. -/
theorem totallyUnimodular (A : Matrix I E ℤ) (owner : S → E)
    (hA : A.IsTotallyUnimodular) : (matrix A owner).IsTotallyUnimodular := by
  have hrows : (Matrix.fromRows A (privateRows owner)).IsTotallyUnimodular := by
    apply hA.fromRows_unitlike
    intro _ s
    refine ⟨owner s, -1, ?_⟩
    ext e
    simp [privateRows, Pi.single_apply, eq_comm]
  have hcols : (Matrix.fromRows (Matrix.fromRows A (privateRows owner)).transpose
      (privateColumns (I := I) (S := S)).transpose).IsTotallyUnimodular := by
    apply hrows.transpose.fromRows_unitlike
    intro _ s
    refine ⟨Sum.inr s, 1, ?_⟩
    ext i
    simp [privateColumns, Pi.single_apply, eq_comm]
  simpa only [matrix, Matrix.transpose_fromRows, Matrix.transpose_fromCols, Matrix.transpose_transpose] using
    hcols.transpose

/-- Every lifted ray with at least one private coordinate is nonzero,
including a lift of an original loop. -/
theorem lifted_ne_zero (A : Matrix I E ℤ) (owner : S → E) (e : E)
    (he : ∃ s, owner s = e) : (fun i => matrix A owner i (Sum.inl e)) ≠ 0 := by
  obtain ⟨s, hs⟩ := he
  intro hz
  have h := congrFun hz (Sum.inr s)
  simp [hs] at h

theorem pure_ne_zero (A : Matrix I E ℤ) (owner : S → E) (s : S) :
    (fun i => matrix A owner i (Sum.inr s)) ≠ 0 := by
  intro hz
  have h := congrFun hz (Sum.inr s)
  simp at h

/-- Integral divisibility of a lifted column is detected by its private
coordinate. This is the ordinary primitive-vector property. -/
theorem lifted_primitive (A : Matrix I E ℤ) (owner : S → E) (e : E)
    (he : ∃ s, owner s = e) (k : ℤ) (v : I ⊕ S → ℤ)
    (hv : k • v = fun i => matrix A owner i (Sum.inl e)) : IsUnit k := by
  obtain ⟨s, hs⟩ := he
  have h := congrFun hv (Sum.inr s)
  have hk : k * v (Sum.inr s) = -1 := by simpa [hs] using h
  exact IsUnit.of_mul_eq_one (-v (Sum.inr s)) (by rw [mul_neg, hk]; norm_num)

theorem pure_primitive (A : Matrix I E ℤ) (owner : S → E) (s : S)
    (k : ℤ) (v : I ⊕ S → ℤ)
    (hv : k • v = fun i => matrix A owner i (Sum.inr s)) : IsUnit k := by
  have h := congrFun hv (Sum.inr s)
  have hk : k * v (Sum.inr s) = 1 := by simpa using h
  exact IsUnit.of_mul_eq_one (v (Sum.inr s)) hk

end Unimodular.Multiwedge

#print axioms Unimodular.Multiwedge.totallyUnimodular
#print axioms Unimodular.Multiwedge.lifted_primitive

end FanoSource1

section FanoSource2


/-!
# Integral bases at vertices of a multiwedge

The old active facet normals form an integral basis. In every inactive block,
one may replace at most one private unit vector by its lifted old normal.
The resulting family is again an integral basis. The proof constructs its
integral span explicitly, including all private coordinates.
-/

namespace Unimodular.MultiwedgeBasis

open scoped BigOperators
open Submodule

attribute [local simp] Prod.fst_sum Prod.snd_sum

variable {I E S V : Type*} [Fintype I] [Fintype S]
  [DecidableEq I] [DecidableEq E] [DecidableEq S]
  [AddCommGroup V]

variable (A : E → V) (owner : S → E)

def lift (e : E) : V × (S → ℤ) :=
  (A e, fun s => if owner s = e then -1 else 0)

def pure (s : S) : V × (S → ℤ) := (0, Pi.single s 1)

def selected (choose : E → Option S) (s : S) : Prop :=
  choose (owner s) = some s

instance (choose : E → Option S) (s : S) : Decidable (selected owner choose s) :=
  inferInstanceAs (Decidable (choose (owner s) = some s))

def columns (active : I → E) (choose : E → Option S) : I ⊕ S → V × (S → ℤ)
  | .inl i => lift A owner (active i)
  | .inr s => if selected owner choose s then lift A owner (owner s) else pure s

@[simp] theorem filtered_single_sum (e : E) (t : S) :
    (∑ s : S, if owner s = e then (if t = s then (1 : ℤ) else 0) else 0) =
      if owner t = e then 1 else 0 := by
  calc
    _ = ∑ s : S, if t = s then (if owner s = e then (1 : ℤ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      by_cases hs : owner s = e <;> by_cases ht : t = s <;> simp [hs, ht]
    _ = _ := by simp

variable (b : Module.Basis I ℤ V) (active : I → E) (choose : E → Option S)
  (ha : ∀ i, A (active i) = b i)
  (hc : ∀ i, choose (active i) = none)

/-- All private vectors which were not replaced belong to the generated lattice. -/
theorem pure_mem_of_not_selected (s : S) (hs : ¬selected owner choose s) :
    pure (V := V) s ∈ span ℤ (Set.range (columns A owner active choose)) := by
  apply subset_span
  exact ⟨Sum.inr s, by simp [columns, hs]⟩

include ha hc

/-- The original active basis is recovered by adding its private unit vectors. -/
theorem base_basis_mem (i : I) :
    (b i, (0 : S → ℤ)) ∈ span ℤ (Set.range (columns A owner active choose)) := by
  classical
  let P := span ℤ (Set.range (columns A owner active choose))
  have hl : lift A owner (active i) ∈ P := subset_span ⟨Sum.inl i, rfl⟩
  have hp (s : S) : (if owner s = active i then pure (V := V) s else 0) ∈ P := by
    split_ifs with hs
    · apply pure_mem_of_not_selected
      simp [selected, hs, hc i]
    · exact P.zero_mem
  have he : (b i, (0 : S → ℤ)) = lift A owner (active i) +
      ∑ s : S, if owner s = active i then pure (V := V) s else 0 := by
    apply Prod.ext
    · simp [lift, pure, ha i, apply_ite]
    · ext t
      by_cases ht : owner t = active i <;>
        simp [lift, pure, Pi.single_apply, ht, apply_ite, ite_apply]
  rw [he]
  exact P.add_mem hl (P.sum_mem fun s _ => hp s)

/-- Every vector of the old lattice embeds in the new generated lattice. -/
theorem base_mem (v : V) :
    (v, (0 : S → ℤ)) ∈ span ℤ (Set.range (columns A owner active choose)) := by
  let P := span ℤ (Set.range (columns A owner active choose))
  have he : (v, (0 : S → ℤ)) = ∑ i, b.repr v i • (b i, (0 : S → ℤ)) := by
    apply Prod.ext
    · simpa only [Prod.fst_sum, Prod.smul_fst] using (b.sum_repr v).symm
    · simp
  rw [he]
  exact P.sum_mem fun i _ => P.smul_mem _ (base_basis_mem A owner b active choose ha hc i)

/-- A replaced private vector is recovered from its lifted column and the
remaining private vectors in the same block. -/
theorem pure_mem (s : S) :
    pure (V := V) s ∈ span ℤ (Set.range (columns A owner active choose)) := by
  classical
  let P := span ℤ (Set.range (columns A owner active choose))
  by_cases hs : selected owner choose s
  · have hl : lift A owner (owner s) ∈ P :=
      subset_span ⟨Sum.inr s, by simp [columns, hs]⟩
    have hp (t : S) (ht : t ∈ Finset.univ.erase s) :
        (if owner t = owner s then pure (V := V) t else 0) ∈ P := by
      split_ifs with howner
      · apply pure_mem_of_not_selected
        intro hsel
        have hst : some t = some s := hsel.symm.trans ((congrArg choose howner).trans hs)
        exact (Finset.mem_erase.mp ht).1 (Option.some.inj hst)
      · exact P.zero_mem
    have he : pure (V := V) s = (A (owner s), (0 : S → ℤ)) - lift A owner (owner s) -
        ∑ t ∈ Finset.univ.erase s, if owner t = owner s then pure (V := V) t else 0 := by
      apply Prod.ext
      · simp [lift, pure, apply_ite]
      · ext t
        by_cases hts : t = s
        · subst t
          simp [lift, pure, Pi.single_apply, apply_ite, ite_apply]
        · by_cases howner : owner t = owner s <;>
            simp [lift, pure, Pi.single_apply, hts, howner, apply_ite, ite_apply]
    rw [he]
    exact P.sub_mem (P.sub_mem (base_mem A owner b active choose ha hc _) hl)
      (P.sum_mem fun t ht => hp t ht)
  · exact pure_mem_of_not_selected A owner active choose s hs

/-- The new columns span the original product lattice, not merely its real span. -/
theorem top_le_span :
    ⊤ ≤ span ℤ (Set.range (columns A owner active choose)) := by
  rw [← (b.prod (Pi.basisFun ℤ S)).span_eq]
  apply span_le.mpr
  rintro _ ⟨i, rfl⟩
  cases i with
  | inl i =>
    simpa using base_basis_mem A owner b active choose ha hc i
  | inr s =>
    simpa [pure, Pi.basisFun_apply] using pure_mem A owner b active choose ha hc s

/-- The exact integral active-normal basis used in the smooth Fano multiwedge. -/
noncomputable def basis : Module.Basis (I ⊕ S) ℤ (V × (S → ℤ)) :=
  basisOfTopLeSpanOfCardEqFinrank (columns A owner active choose)
    (top_le_span A owner b active choose ha hc)
    (Module.finrank_eq_card_basis (b.prod (Pi.basisFun ℤ S))).symm

@[simp] theorem basis_apply (i : I ⊕ S) :
    basis A owner b active choose ha hc i = columns A owner active choose i := by
  simp [basis]

end Unimodular.MultiwedgeBasis

#print axioms Unimodular.MultiwedgeBasis.basis

end FanoSource2

section FanoSource3


/-!
# Coordinates on an enlarged integral lattice

These are ordinary coordinate permutations between a product lattice and
`ℤ^(n + |S|)`. They preserve the integral-to-real embedding and the actual
dual pairing, so the polytope constructions can be stated in the same lattice
coordinates as the rest of the verification.
-/

namespace Unimodular.ProductCoordinates

open Set
open scoped BigOperators

noncomputable section
variable {n : ℕ} (S : Type*) [Fintype S]

abbrev dimension := n + Fintype.card S

def indexEquiv : Fin n ⊕ S ≃ Fin (dimension (n := n) S) :=
  (Equiv.sumCongr (Equiv.refl (Fin n)) (Fintype.equivFin S)).trans finSumFinEquiv

def pack (R : Type*) [Semiring R] :
    ((Fin n → R) × (S → R)) ≃ₗ[R] (Fin (dimension (n := n) S) → R) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin n) S R R).symm.trans
    (LinearEquiv.piCongrLeft R (fun _ : Fin (dimension (n := n) S) => R) (indexEquiv S))

@[simp] theorem pack_apply (R : Type*) [Semiring R]
    (z : (Fin n → R) × (S → R)) (i : Fin n ⊕ S) :
    pack S R z (indexEquiv S i) = Sum.elim z.1 z.2 i := by
  simp [pack, LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft']
  cases i <;> rfl

def embedProduct (z : Lattice n × (S → ℤ)) : Ambient n × (S → ℝ) :=
  (embed z.1, fun s => (z.2 s : ℝ))

/-- The integral coordinate change is exactly the restriction of its real counterpart. -/
theorem embed_pack (z : Lattice n × (S → ℤ)) :
    embed (pack S ℤ z) = pack S ℝ (embedProduct S z) := by
  ext i
  obtain ⟨j, rfl⟩ := (indexEquiv (n := n) S).surjective i
  change (pack S ℤ z (indexEquiv S j) : ℝ) = _
  rw [pack_apply, pack_apply]
  cases j <;> rfl

def productPairing (x : Ambient n × (S → ℝ)) (u : Lattice n × (S → ℤ)) : ℝ :=
  pairing x.1 u.1 + ∑ s, x.2 s * (u.2 s : ℝ)

/-- Pairing preservation involves both point and normal coordinates. -/
theorem pairing_pack (x : Ambient n × (S → ℝ)) (u : Lattice n × (S → ℤ)) :
    pairing (pack S ℝ x) (pack S ℤ u) = productPairing S x u := by
  unfold pairing
  rw [← Equiv.sum_comp (indexEquiv S)]
  simp only [pack_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  rfl

/-- The coordinate change transports the complete real convex hull. -/
theorem convexHull_pack (T : Set (Ambient n × (S → ℝ))) :
    convexHull ℝ (pack S ℝ '' T) = pack S ℝ '' convexHull ℝ T :=
  ((pack S ℝ).toLinearMap.image_convexHull T).symm

end
end Unimodular.ProductCoordinates

#print axioms Unimodular.ProductCoordinates.embed_pack
#print axioms Unimodular.ProductCoordinates.pairing_pack

end FanoSource3

section FanoSource4


/-!
# The actual multiwedge polytope

The affine change `s = 1 - y` identifies its unit-distance halfspaces with
products of slack simplices. All statements concern the complete convex
sets and their integral vertices.
-/

namespace Unimodular.MultiwedgeGeometry

open Set
open scoped BigOperators

noncomputable section
variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
variable (J : E → Type*) [∀ e, Fintype (J e)] [∀ e, DecidableEq (J e)]

abbrev Extra := Sigma J
abbrev IntegralSpace := Lattice n × (Extra J → ℤ)
abbrev RealSpace := Ambient n × (Extra J → ℝ)

variable (A : E → Lattice n) (h : E → ℤ)

def normal : E ⊕ Extra J → IntegralSpace (n := n) J
  | .inl e => MultiwedgeBasis.lift A Sigma.fst e
  | .inr s => MultiwedgeBasis.pure s

def normals : Finset (IntegralSpace (n := n) J) := Finset.univ.image (normal J A)

def carrier : Set (RealSpace (n := n) J) :=
  {z | ∀ e, pairing z.1 (A e) - ∑ j, z.2 ⟨e,j⟩ ≤ 1 ∧ ∀ j, z.2 ⟨e,j⟩ ≤ 1}

def reflectIntegral (z : IntegralSpace (n := n) J) : IntegralSpace (n := n) J :=
  (z.1, fun s => 1 - z.2 s)

def reflectReal (z : RealSpace (n := n) J) : RealSpace (n := n) J :=
  (z.1, fun s => 1 - z.2 s)

@[simp] theorem reflectReal_involutive (z : RealSpace (n := n) J) :
    reflectReal J (reflectReal J z) = z := by
  ext <;> simp [reflectReal]

@[simp] theorem reflectIntegral_involutive (z : IntegralSpace (n := n) J) :
    reflectIntegral J (reflectIntegral J z) = z := by
  ext <;> simp [reflectIntegral]

@[simp] theorem embed_reflect (z : IntegralSpace (n := n) J) :
    SimplexBundle.embed J (reflectIntegral J z) =
      reflectReal J (SimplexBundle.embed J z) := by
  ext <;> simp [SimplexBundle.embed, reflectIntegral, reflectReal]

def reflectAffine : RealSpace (n := n) J →ᵃ[ℝ] RealSpace (n := n) J where
  toFun := reflectReal J
  linear :=
    { toFun := fun z => (z.1, -z.2)
      map_add' := by intros; ext <;> simp [add_comm]
      map_smul' := by intros; ext <;> simp }
  map_vadd' := by
    intro x y
    ext <;> simp [reflectReal] <;> ring

/-- The unit-distance halfspaces are exactly the affine image of the slack simplices. -/
theorem reflect_mem_iff (hcard : ∀ e, (Fintype.card (J e) : ℤ) + 1 = h e)
    (z : RealSpace (n := n) J) :
    reflectReal J z ∈ carrier J A ↔ z ∈ SimplexBundle.carrier J A h := by
  constructor
  · intro hz e
    constructor
    · intro j
      have hh := (hz e).2 j
      change 1 - z.2 ⟨e,j⟩ ≤ 1 at hh
      linarith
    · have hh := (hz e).1
      change pairing z.1 (A e) - ∑ j, (1 - z.2 ⟨e,j⟩) ≤ 1 at hh
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_one] at hh
      have hc : (Fintype.card (J e) : ℝ) + 1 = h e := by exact_mod_cast hcard e
      dsimp [SimplexBundle.slack]
      linarith
  · intro hz e
    constructor
    · have hh := (hz e).2
      change pairing z.1 (A e) - ∑ j, (1 - z.2 ⟨e,j⟩) ≤ 1
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_one]
      have hc : (Fintype.card (J e) : ℝ) + 1 = h e := by exact_mod_cast hcard e
      dsimp [SimplexBundle.slack] at hh
      linarith
    · intro j
      change 1 - z.2 ⟨e,j⟩ ≤ 1
      linarith [(hz e).1 j]

theorem carrier_eq_image (hcard : ∀ e, (Fintype.card (J e) : ℤ) + 1 = h e) :
    carrier J A = reflectReal J '' SimplexBundle.carrier J A h := by
  ext z
  constructor
  · intro hz
    refine ⟨reflectReal J z, ?_, reflectReal_involutive J z⟩
    exact (reflect_mem_iff J A h hcard _).1 (by simpa using hz)
  · rintro ⟨w, hw, rfl⟩
    exact (reflect_mem_iff J A h hcard _).2 hw

def vertices (S : Finset (Lattice n)) : Finset (IntegralSpace (n := n) J) :=
  (SimplexBundle.vertices J A h S).image (reflectIntegral J)

/-- A complete finite lattice convex-hull description of the multiwedge. -/
theorem carrier_eq_convexHull_vertices
    (hcard : ∀ e, (Fintype.card (J e) : ℤ) + 1 = h e) (S : Finset (Lattice n)) (hS : S.Nonempty)
    (hbase : SimplexBundle.base A h =
      convexHull ℝ (Unimodular.embed '' (S : Set (Lattice n)))) :
    carrier J A = convexHull ℝ
      (SimplexBundle.embed J '' (vertices J A h S : Set (IntegralSpace (n := n) J))) := by
  rw [carrier_eq_image J A h hcard,
    SimplexBundle.carrier_eq_convexHull_vertices J A h S hS hbase]
  change reflectAffine J '' convexHull ℝ _ = _
  rw [(reflectAffine J).image_convexHull]
  congr 1
  ext z
  simp only [Set.mem_image, Finset.mem_coe, vertices, Finset.mem_image]
  constructor
  · rintro ⟨x, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨reflectIntegral J v, ⟨v, hv, rfl⟩, embed_reflect J v⟩
  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨SimplexBundle.embed J v, ⟨v, hv, rfl⟩, (embed_reflect J v).symm⟩

/-- Direct evaluation on a pure coordinate normal. -/
theorem pairing_pure (z : RealSpace (n := n) J) (s : Extra J) :
    ProductCoordinates.productPairing (Extra J) z (normal J A (.inr s)) = z.2 s := by
  simp [ProductCoordinates.productPairing, normal, MultiwedgeBasis.pure,
    pairing, Pi.single_apply]

/-- Direct evaluation on a lifted old normal. -/
theorem pairing_lift (z : RealSpace (n := n) J) (e : E) :
    ProductCoordinates.productPairing (Extra J) z (normal J A (.inl e)) =
      pairing z.1 (A e) - ∑ j, z.2 ⟨e,j⟩ := by
  change pairing z.1 (A e) +
    (∑ s : Extra J, z.2 s * ((if s.1 = e then -1 else 0 : ℤ) : ℝ)) = _
  have hinner (a : E) :
      (∑ j : J a, z.2 ⟨a,j⟩ * ((if a = e then -1 else 0 : ℤ) : ℝ)) =
        if a = e then -(∑ j : J a, z.2 ⟨a,j⟩) else 0 := by
    by_cases ha : a = e <;> simp [ha, Finset.sum_neg_distrib]
  rw [Fintype.sum_sigma]
  simp_rw [hinner]
  simp [sub_eq_add_neg]

/-- The displayed inequalities use exactly the listed primitive-normal candidates. -/
theorem mem_carrier_iff (z : RealSpace (n := n) J) :
    z ∈ carrier J A ↔ ∀ u ∈ normals J A,
      ProductCoordinates.productPairing (Extra J) z u ≤ 1 := by
  constructor
  · intro hz u hu
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
    cases i with
    | inl e => simpa only [pairing_lift] using (hz e).1
    | inr s => simpa only [pairing_pure] using (hz s.1).2 s.2
  · intro hz e
    constructor
    · simpa only [pairing_lift] using hz (normal J A (.inl e))
        (Finset.mem_image.mpr ⟨.inl e, Finset.mem_univ _, rfl⟩)
    · intro j
      simpa only [pairing_pure] using hz (normal J A (.inr ⟨e,j⟩))
        (Finset.mem_image.mpr ⟨.inr ⟨e,j⟩, Finset.mem_univ _, rfl⟩)

end
end Unimodular.MultiwedgeGeometry

#print axioms Unimodular.MultiwedgeGeometry.carrier_eq_convexHull_vertices

end FanoSource4

section FanoSource5


/-!
# Smooth reflexive multiwedges

The input is an ordinary finite integral halfspace presentation of a smooth
polytope, with the active facets at each vertex explicitly labelled. We prove
that the unit-distance multiwedge has exactly an integral basis of active
normals at every vertex. No smoothness or completeness of the output is assumed.
-/

namespace Unimodular.MultiwedgeSmooth

open Set
open scoped BigOperators
noncomputable section

variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
variable (J : E → Type*) [∀ e, Fintype (J e)] [∀ e, DecidableEq (J e)]
variable (A : E → Lattice n) (h : E → ℤ)

abbrev Extra := Sigma J
abbrev Choice := SimplexBundle.Choice J
abbrev Space := MultiwedgeGeometry.IntegralSpace (n := n) J
abbrev dimension := ProductCoordinates.dimension (n := n) (Extra J)

def slack (v : Lattice n) (e : E) : ℤ := h e - integerPairing v (A e)

def point (v : Lattice n) (c : Choice J) : Space (n := n) J :=
  MultiwedgeGeometry.reflectIntegral J (SimplexBundle.corner J A h v c)

def choose (v : Lattice n) (c : Choice J) (e : E) : Option (Extra J) :=
  if slack A h v e = 0 then none else (c e).map (fun j => ⟨e,j⟩)

@[simp] theorem choose_eq_none_of_zero (v : Lattice n) (c : Choice J) (e : E)
    (he : slack A h v e = 0) : choose J A h v c e = none := by simp [choose, he]

@[simp] theorem selected_iff (v : Lattice n) (c : Choice J) (s : Extra J) :
    MultiwedgeBasis.selected Sigma.fst (choose J A h v c) s ↔
      slack A h v s.1 ≠ 0 ∧ c s.1 = some s.2 := by
  rcases s with ⟨e,j⟩
  by_cases he : slack A h v e = 0
  · simp [MultiwedgeBasis.selected, choose, he]
  · cases hc : c e <;> simp [MultiwedgeBasis.selected, choose, he, hc]

theorem pure_evaluation (v : Lattice n) (c : Choice J) (s : Extra J) :
    ProductCoordinates.productPairing (Extra J)
      (SimplexBundle.embed J (point J A h v c))
      (MultiwedgeBasis.pure (V := Lattice n) s) =
      (1 - if c s.1 = some s.2 then slack A h v s.1 else 0 : ℤ) := by
  simpa [MultiwedgeGeometry.normal, point, MultiwedgeGeometry.reflectIntegral,
    SimplexBundle.embed, SimplexBundle.corner, slack] using
    MultiwedgeGeometry.pairing_pure J A
      (SimplexBundle.embed J (point J A h v c)) s

theorem pure_active_iff (v : Lattice n) (c : Choice J) (s : Extra J) :
    ProductCoordinates.productPairing (Extra J)
      (SimplexBundle.embed J (point J A h v c))
      (MultiwedgeBasis.pure (V := Lattice n) s) = 1 ↔
      ¬ MultiwedgeBasis.selected Sigma.fst (choose J A h v c) s := by
  rw [pure_evaluation, selected_iff]
  by_cases hc : c s.1 = some s.2 <;> simp [hc]

theorem lift_evaluation (hcard : ∀ e, (Fintype.card (J e) : ℤ) + 1 = h e)
    (v : Lattice n) (c : Choice J) (e : E) :
    ProductCoordinates.productPairing (Extra J)
      (SimplexBundle.embed J (point J A h v c))
      (MultiwedgeBasis.lift A Sigma.fst e) =
      if c e = none then 1 - (slack A h v e : ℝ) else 1 := by
  have he := MultiwedgeGeometry.pairing_lift J A
    (SimplexBundle.embed J (point J A h v c)) e
  change _ = pairing (Unimodular.embed v) (A e) -
    ∑ j, ((1 - if c e = some j then slack A h v e else 0 : ℤ) : ℝ) at he
  change ProductCoordinates.productPairing (Extra J)
    (SimplexBundle.embed J (point J A h v c)) (MultiwedgeBasis.lift A Sigma.fst e) = _ at he
  rw [he]
  have hh : (Fintype.card (J e) : ℝ) + 1 = h e := by exact_mod_cast hcard e
  cases hc : c e with
  | none =>
    simp only [hc, reduceCtorEq, ↓reduceIte, sub_zero, Int.cast_one,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    simp only [slack, Int.cast_sub, ← pairing_embed]
    linarith
  | some j =>
    simp only [hc, Option.some.injEq, Int.cast_sub, Int.cast_one, Int.cast_ite,
      Int.cast_zero, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      reduceCtorEq]
    simp only [slack, Int.cast_sub, ← pairing_embed]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    linarith

theorem lift_active_iff (hcard : ∀ e, (Fintype.card (J e) : ℤ) + 1 = h e)
    (v : Lattice n) (c : Choice J) (e : E) :
    ProductCoordinates.productPairing (Extra J)
      (SimplexBundle.embed J (point J A h v c))
      (MultiwedgeBasis.lift A Sigma.fst e) = 1 ↔
      slack A h v e = 0 ∨ c e ≠ none := by
  rw [lift_evaluation J A h hcard]
  by_cases hc : c e = none <;> simp [hc]

variable (S : Finset (Lattice n))
variable (B : {v // v ∈ S} → Module.Basis (Fin n) ℤ (Lattice n))
variable (active : {v // v ∈ S} → Fin n → E)
variable (hb : ∀ v i, A (active v i) = B v i)
variable (ha : ∀ v i, slack A h v.val (active v i) = 0)
variable (hs : ∀ v e, slack A h v.val e = 0 → ∃ i, active v i = e)

/-- The full integral active-normal basis at each displayed corner. -/
def cornerBasis (v : {v // v ∈ S}) (c : Choice J) :
    Module.Basis (Fin n ⊕ Extra J) ℤ (Space (n := n) J) :=
  MultiwedgeBasis.basis A Sigma.fst (B v) (active v) (choose J A h v.val c)
    (hb v) (fun i => choose_eq_none_of_zero J A h v.val c _ (ha v i))

@[simp] theorem cornerBasis_apply (v : {v // v ∈ S}) (c : Choice J)
    (i : Fin n ⊕ Extra J) :
    cornerBasis J A h S B active hb ha v c i =
      MultiwedgeBasis.columns A Sigma.fst (active v) (choose J A h v.val c) i := by
  simp [cornerBasis]

theorem basis_mem (v : {v // v ∈ S}) (c : Choice J) (i : Fin n ⊕ Extra J) :
    cornerBasis J A h S B active hb ha v c i ∈ MultiwedgeGeometry.normals J A := by
  rw [cornerBasis_apply]
  cases i with
  | inl i => exact Finset.mem_image.mpr ⟨.inl (active v i), Finset.mem_univ _, rfl⟩
  | inr s =>
    simp only [MultiwedgeBasis.columns]
    split_ifs
    · exact Finset.mem_image.mpr ⟨.inl s.1, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.inr s, Finset.mem_univ _, rfl⟩

theorem basis_active (hcard : ∀ e, (Fintype.card (J e) : ℤ) + 1 = h e)
    (v : {v // v ∈ S}) (c : Choice J) (i : Fin n ⊕ Extra J) :
    ProductCoordinates.productPairing (Extra J)
      (SimplexBundle.embed J (point J A h v.val c))
      (cornerBasis J A h S B active hb ha v c i) = 1 := by
  rw [cornerBasis_apply]
  cases i with
  | inl i =>
    apply (lift_active_iff J A h hcard v.val c _).2
    exact Or.inl (ha v i)
  | inr s =>
    simp only [MultiwedgeBasis.columns]
    split_ifs with hsel
    · apply (lift_active_iff J A h hcard v.val c _).2
      right
      have hh := ((selected_iff J A h v.val c s).1 hsel).2
      rw [hh]
      exact Option.some_ne_none _
    · exact (pure_active_iff J A h v.val c s).2 hsel

include hs in
theorem active_subset (hcard : ∀ e, (Fintype.card (J e) : ℤ) + 1 = h e)
    (v : {v // v ∈ S}) (c : Choice J) (u : Space (n := n) J)
    (hu : u ∈ MultiwedgeGeometry.normals J A)
    (huact : ProductCoordinates.productPairing (Extra J)
      (SimplexBundle.embed J (point J A h v.val c)) u = 1) :
    ∃ i, cornerBasis J A h S B active hb ha v c i = u := by
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hu
  cases a with
  | inl e =>
    have hh := (lift_active_iff J A h hcard v.val c e).1 huact
    by_cases he : slack A h v.val e = 0
    · obtain ⟨i, hi⟩ := hs v e he
      exact ⟨.inl i, by simp [hi, MultiwedgeBasis.columns, MultiwedgeGeometry.normal]⟩
    · obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp (hh.resolve_left he)
      refine ⟨.inr ⟨e,j⟩, ?_⟩
      have hsel := (selected_iff J A h v.val c (⟨e,j⟩ : Extra J)).2 ⟨he, hj⟩
      simp [MultiwedgeBasis.columns, hsel, MultiwedgeGeometry.normal]
  | inr s =>
    have hh := (pure_active_iff J A h v.val c s).1 huact
    exact ⟨.inr s, by simp [MultiwedgeBasis.columns, hh, MultiwedgeGeometry.normal]⟩


def packedVertices : Finset (Lattice (dimension (n := n) J)) :=
  (MultiwedgeGeometry.vertices J A h S).image (ProductCoordinates.pack (Extra J) ℤ)

def packedNormals : Finset (Lattice (dimension (n := n) J)) :=
  (MultiwedgeGeometry.normals J A).image (ProductCoordinates.pack (Extra J) ℤ)

theorem packedPoint_mem (v : {v // v ∈ S}) (c : Choice J) :
    ProductCoordinates.pack (Extra J) ℤ (point J A h v.val c) ∈
      packedVertices J A h S := by
  apply Finset.mem_image.mpr
  refine ⟨point J A h v.val c, ?_, rfl⟩
  apply Finset.mem_image.mpr
  refine ⟨SimplexBundle.corner J A h v.val c, ?_, rfl⟩
  exact Finset.mem_biUnion.mpr ⟨v.val, v.property,
    Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩⟩

theorem exists_point (w : {w // w ∈ packedVertices J A h S}) :
    ∃ p : {v // v ∈ S} × Choice J,
      ProductCoordinates.pack (Extra J) ℤ (point J A h p.1.val p.2) = w.val := by
  obtain ⟨q, hq, he⟩ := Finset.mem_image.mp w.property
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨v, hv, hz⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hz
  exact ⟨(⟨v,hv⟩,c), he⟩

def representative (w : {w // w ∈ packedVertices J A h S}) :
    {v // v ∈ S} × Choice J := Classical.choose (exists_point J A h S w)

theorem representative_eq (w : {w // w ∈ packedVertices J A h S}) :
    ProductCoordinates.pack (Extra J) ℤ
      (point J A h (representative J A h S w).1.val (representative J A h S w).2) = w.val :=
  Classical.choose_spec (exists_point J A h S w)

def packedBasis (v : {v // v ∈ S}) (c : Choice J) :
    Module.Basis (Fin (dimension (n := n) J)) ℤ (Lattice (dimension (n := n) J)) :=
  ((cornerBasis J A h S B active hb ha v c).map (ProductCoordinates.pack (Extra J) ℤ)).reindex
    (ProductCoordinates.indexEquiv (n := n) (Extra J))

@[simp] theorem packedBasis_apply (v : {v // v ∈ S}) (c : Choice J)
    (i : Fin n ⊕ Extra J) :
    packedBasis J A h S B active hb ha v c (ProductCoordinates.indexEquiv (Extra J) i) =
      ProductCoordinates.pack (Extra J) ℤ (cornerBasis J A h S B active hb ha v c i) := by
  simp [packedBasis]

def vertexBasis (w : {w // w ∈ packedVertices J A h S}) :
    Module.Basis (Fin (dimension (n := n) J)) ℤ (Lattice (dimension (n := n) J)) :=
  packedBasis J A h S B active hb ha (representative J A h S w).1
    (representative J A h S w).2

theorem vertexBasis_mem (w : {w // w ∈ packedVertices J A h S})
    (i : Fin (dimension (n := n) J)) :
    vertexBasis J A h S B active hb ha w i ∈ packedNormals J A := by
  obtain ⟨j, rfl⟩ := (ProductCoordinates.indexEquiv (n := n) (Extra J)).surjective i
  dsimp [vertexBasis]
  rw [packedBasis_apply]
  exact Finset.mem_image.mpr ⟨_, basis_mem J A h S B active hb ha _ _ _, rfl⟩

theorem pairing_packedPoint (v : Lattice n) (c : Choice J) (u : Space (n := n) J) :
    pairing (Unimodular.embed (ProductCoordinates.pack (Extra J) ℤ (point J A h v c)))
      (ProductCoordinates.pack (Extra J) ℤ u) =
      ProductCoordinates.productPairing (Extra J) (SimplexBundle.embed J (point J A h v c)) u := by
  rw [ProductCoordinates.embed_pack, ProductCoordinates.pairing_pack]
  rfl

theorem vertexBasis_active (hcard : ∀ e, (Fintype.card (J e) : ℤ) + 1 = h e)
    (w : {w // w ∈ packedVertices J A h S}) (i : Fin (dimension (n := n) J)) :
    pairing (Unimodular.embed w.val) (vertexBasis J A h S B active hb ha w i) = 1 := by
  obtain ⟨j, rfl⟩ := (ProductCoordinates.indexEquiv (n := n) (Extra J)).surjective i
  dsimp only [vertexBasis]
  rw [packedBasis_apply, ← representative_eq J A h S w, pairing_packedPoint]
  exact basis_active J A h S B active hb ha hcard _ _ j

include hs in
theorem vertexBasis_active_subset (hcard : ∀ e, (Fintype.card (J e) : ℤ) + 1 = h e)
    (w : {w // w ∈ packedVertices J A h S}) (u : Lattice (dimension (n := n) J))
    (hu : u ∈ packedNormals J A) (huact : pairing (Unimodular.embed w.val) u = 1) :
    ∃ i, vertexBasis J A h S B active hb ha w i = u := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hu
  rw [← representative_eq J A h S w, pairing_packedPoint] at huact
  obtain ⟨j, hj⟩ := active_subset J A h S B active hb ha hs hcard
    (representative J A h S w).1 (representative J A h S w).2 q hq huact
  refine ⟨ProductCoordinates.indexEquiv (Extra J) j, ?_⟩
  dsimp only [vertexBasis]
  rw [packedBasis_apply, hj]

theorem packedVertices_nonempty (hS : S.Nonempty) : (packedVertices J A h S).Nonempty := by
  obtain ⟨v,hv⟩ := hS
  exact ⟨_, packedPoint_mem J A h S ⟨v,hv⟩ (fun _ => none)⟩

include hs in
theorem normals_occur (hcard : ∀ e, (Fintype.card (J e) : ℤ) + 1 = h e)
    (hS : S.Nonempty) (hJ : ∀ e, Nonempty (J e)) (u : Lattice (dimension (n := n) J))
    (hu : u ∈ packedNormals J A) :
    ∃ w i, vertexBasis J A h S B active hb ha w i = u := by
  obtain ⟨v,hv⟩ := hS
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
  have hnorm : ProductCoordinates.pack (Extra J) ℤ (MultiwedgeGeometry.normal J A i) ∈
      packedNormals J A := Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr
        ⟨i,Finset.mem_univ _,rfl⟩,rfl⟩
  cases i with
  | inl e =>
    let c : Choice J := fun e => some (Classical.choice (hJ e))
    let w : {w // w ∈ packedVertices J A h S} :=
      ⟨_, packedPoint_mem J A h S ⟨v,hv⟩ c⟩
    refine ⟨w, vertexBasis_active_subset J A h S B active hb ha hs hcard w _ hnorm ?_⟩
    change pairing (Unimodular.embed (ProductCoordinates.pack (Extra J) ℤ
      (point J A h v c))) _ = 1
    rw [pairing_packedPoint]
    exact (lift_active_iff J A h hcard v c e).2 (Or.inr (Option.some_ne_none _))
  | inr s =>
    let c : Choice J := fun _ => none
    let w : {w // w ∈ packedVertices J A h S} :=
      ⟨_, packedPoint_mem J A h S ⟨v,hv⟩ c⟩
    refine ⟨w, vertexBasis_active_subset J A h S B active hb ha hs hcard w _ hnorm ?_⟩
    change pairing (Unimodular.embed (ProductCoordinates.pack (Extra J) ℤ
      (point J A h v c))) _ = 1
    rw [pairing_packedPoint]
    apply (pure_active_iff J A h v c s).2
    simp [selected_iff, c]

theorem packed_hull_eq (hcard : ∀ e, (Fintype.card (J e) : ℤ) + 1 = h e)
    (hS : S.Nonempty)
    (hbase : SimplexBundle.base A h = convexHull ℝ (Unimodular.embed '' (S : Set (Lattice n)))) :
    convexHull ℝ (Unimodular.embed '' (packedVertices J A h S : Set _)) =
      {x | ∀ u ∈ packedNormals J A, pairing x u ≤ 1} := by
  have himage : Unimodular.embed '' (packedVertices J A h S : Set _) =
      ProductCoordinates.pack (Extra J) ℝ ''
        (SimplexBundle.embed J '' (↑(MultiwedgeGeometry.vertices J A h S) :
          Set (MultiwedgeGeometry.IntegralSpace (n := n) J))) := by
    ext x
    simp only [packedVertices, Finset.coe_image, Set.mem_image]
    constructor
    · rintro ⟨w, ⟨z,hz,rfl⟩,rfl⟩
      exact ⟨SimplexBundle.embed J z, ⟨z,hz,rfl⟩, (ProductCoordinates.embed_pack _ z).symm⟩
    · rintro ⟨w,⟨z,hz,rfl⟩,rfl⟩
      exact ⟨ProductCoordinates.pack (Extra J) ℤ z, ⟨z,hz,rfl⟩,
        ProductCoordinates.embed_pack _ z⟩
  rw [himage, ProductCoordinates.convexHull_pack,
    ← MultiwedgeGeometry.carrier_eq_convexHull_vertices J A h hcard S hS hbase]
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩ u hu
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
    rw [ProductCoordinates.pairing_pack]
    exact (MultiwedgeGeometry.mem_carrier_iff J A z).1 hz v hv
  · intro hx
    refine ⟨(ProductCoordinates.pack (Extra J) ℝ).symm x, ?_,
      (ProductCoordinates.pack (Extra J) ℝ).apply_symm_apply x⟩
    apply (MultiwedgeGeometry.mem_carrier_iff J A _).2
    intro u hu
    have hh := hx (ProductCoordinates.pack (Extra J) ℤ u)
      (Finset.mem_image.mpr ⟨u,hu,rfl⟩)
    rw [← (ProductCoordinates.pack (Extra J) ℝ).apply_symm_apply x,
      ProductCoordinates.pairing_pack] at hh
    exact hh

/-- The actual smooth reflexive lattice polytope produced by the multiwedge. -/
def presentation (hcard : ∀ e, (Fintype.card (J e) : ℤ) + 1 = h e)
    (hS : S.Nonempty) (hJ : ∀ e, Nonempty (J e))
    (hbase : SimplexBundle.base A h = convexHull ℝ (Unimodular.embed '' (S : Set (Lattice n)))) :
    SmoothReflexivePresentation (dimension (n := n) J) where
  vertices := packedVertices J A h S
  normals := packedNormals J A
  vertices_nonempty := packedVertices_nonempty J A h S hS
  basis := vertexBasis J A h S B active hb ha
  basis_mem := vertexBasis_mem J A h S B active hb ha
  basis_active := vertexBasis_active J A h S B active hb ha hcard
  active_subset := vertexBasis_active_subset J A h S B active hb ha hs hcard
  normals_occur := normals_occur J A h S B active hb ha hs hcard hS hJ
  hull_eq := packed_hull_eq J A h S hcard hS hbase

end
end Unimodular.MultiwedgeSmooth

#print axioms Unimodular.MultiwedgeSmooth.presentation

end FanoSource5

section FanoSource6


set_option backward.isDefEq.respectTransparency false

/-!
# A cube with arbitrary redundant integral inequalities

Every prescribed integer vector is retained as a separately labelled inequality,
including zero vectors and repeated vectors. Its height makes it strictly
inactive throughout the cube. Thus the active facets remain the ordinary signed
coordinate basis, while the subsequent multiwedge turns every label into a
primitive facet normal.
-/

namespace Unimodular.CubeInput

open Set
open scoped BigOperators
noncomputable section

variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

abbrev Label (n : ℕ) (E : Type*) := E ⊕ (Fin n ⊕ Fin n)

variable (u : E → Lattice n) (d : ℤ)

def normal : Label n E → Lattice n
  | .inl e => u e
  | .inr (.inl i) => Pi.single i 1
  | .inr (.inr i) => -Pi.single i 1

def mass (e : E) : ℤ := ∑ i, |u e i|

def height : Label n E → ℤ
  | .inl e => d * (1 + mass u e)
  | .inr _ => d

def vertices : Finset (Lattice n) := Fintype.piFinset (fun _ => { -d, d })

def cube : Set (Ambient n) := {x | ∀ i, -(d : ℝ) ≤ x i ∧ x i ≤ d}

@[simp] theorem mem_vertices (v : Lattice n) :
    v ∈ vertices (n := n) d ↔ ∀ i, v i = -d ∨ v i = d := by
  simp [vertices, Fintype.mem_piFinset]

theorem vertices_nonempty : (vertices (n := n) d).Nonempty := by
  exact ⟨fun _ => d, (mem_vertices d _).2 (fun _ => Or.inr rfl)⟩

theorem embed_vertices (hd : 0 ≤ d) :
    embed '' (vertices (n := n) d : Set (Lattice n)) =
      Set.univ.pi (fun _ : Fin n => ({-(d : ℝ), (d : ℝ)} : Set ℝ)) := by
  ext x
  constructor
  · rintro ⟨v,hv,rfl⟩
    intro i _
    rcases (mem_vertices d v).1 hv i with he | he <;> simp [embed, he]
  · intro hx
    let v : Lattice n := fun i => if x i = -(d : ℝ) then -d else d
    refine ⟨v, (mem_vertices d v).2 ?_, ?_⟩
    · intro i
      dsimp [v]
      split_ifs <;> simp
    · ext i
      have hi := hx i (Set.mem_univ _)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
      by_cases he : x i = -(d : ℝ)
      · simp only [embed, v, if_pos he, Int.cast_neg]
        exact he.symm
      · simp only [embed, v, if_neg he]
        exact (hi.resolve_left he).symm

theorem cube_eq_convexHull (hd : 0 ≤ d) :
    cube (n := n) d = convexHull ℝ (embed '' (vertices (n := n) d : Set (Lattice n))) := by
  rw [embed_vertices d hd, convexHull_pi]
  have horder : -(d : ℝ) ≤ d := by exact_mod_cast (neg_le_self hd)
  simp only [convexHull_pair, segment_eq_Icc horder]
  ext x
  simp [cube, Set.mem_pi, Pi.le_def, forall_and]

theorem vertex_mem_cube (hd : 0 ≤ d) (v : {v // v ∈ vertices (n := n) d}) :
    embed v.val ∈ cube d := by
  intro i
  rcases (mem_vertices d v.val).1 v.property i with hi | hi <;>
    simp [embed, hi] <;> exact_mod_cast hd

theorem pairing_bound (hd : 0 ≤ d) {x : Ambient n} (hx : x ∈ cube d) (e : E) :
    pairing x (u e) ≤ (d : ℝ) * (mass u e : ℝ) := by
  have hdR : (0 : ℝ) ≤ d := by exact_mod_cast hd
  calc
    pairing x (u e) ≤ ∑ i, (d : ℝ) * |(u e i : ℝ)| := by
      apply Finset.sum_le_sum
      intro i _
      calc
        x i * (u e i : ℝ) ≤ |x i * (u e i : ℝ)| := le_abs_self _
        _ = |x i| * |(u e i : ℝ)| := abs_mul _ _
        _ ≤ (d : ℝ) * |(u e i : ℝ)| :=
          mul_le_mul_of_nonneg_right (abs_le.2 (hx i)) (abs_nonneg _)
    _ = (d : ℝ) * (mass u e : ℝ) := by
      rw [← Finset.mul_sum]
      simp [mass]

theorem raw_strict (hd : 0 < d) {x : Ambient n} (hx : x ∈ cube d) (e : E) :
    pairing x (u e) < (height u d (.inl e) : ℝ) := by
  have hb := pairing_bound u d hd.le hx e
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  simp only [height, Int.cast_mul, Int.cast_add, Int.cast_one]
  nlinarith

@[simp] theorem pairing_positive (x : Ambient n) (i : Fin n) :
    pairing x (normal u (.inr (.inl i))) = x i := by
  simp [normal, pairing, Pi.single_apply]

@[simp] theorem pairing_negative (x : Ambient n) (i : Fin n) :
    pairing x (normal u (.inr (.inr i))) = -x i := by
  simp [normal, pairing, Pi.single_apply, Finset.sum_neg_distrib]

theorem base_eq_cube (hd : 0 < d) :
    SimplexBundle.base (normal u) (height u d) = cube (n := n) d := by
  ext x
  constructor
  · intro hx i
    have hp := hx (.inr (.inl i))
    have hn := hx (.inr (.inr i))
    simp only [pairing_positive, pairing_negative, height] at hp hn
    exact ⟨by linarith, hp⟩
  · intro hx a
    cases a with
    | inl e => exact (raw_strict u d hd hx e).le
    | inr a =>
      cases a with
      | inl i => simpa only [pairing_positive, height] using (hx i).2
      | inr i =>
        simp only [pairing_negative, height]
        linarith [(hx i).1]

def signUnit (v : Lattice n) (i : Fin n) : ℤˣ := if v i = d then 1 else -1

def basis (v : {v // v ∈ vertices (n := n) d}) : Module.Basis (Fin n) ℤ (Lattice n) :=
  (Pi.basisFun ℤ (Fin n)).unitsSMul (signUnit d v.val)

def active (v : {v // v ∈ vertices (n := n) d}) (i : Fin n) : Label n E :=
  if v.val i = d then .inr (.inl i) else .inr (.inr i)

theorem normal_active_eq_basis (v : {v // v ∈ vertices (n := n) d}) (i : Fin n) :
    normal u (active d v i) = basis d v i := by
  by_cases hi : v.val i = d <;>
    simp [normal, active, basis, signUnit, hi, Module.Basis.unitsSMul_apply,
      Pi.basisFun_apply, Units.smul_def]

theorem active_slack_zero (v : {v // v ∈ vertices (n := n) d}) (i : Fin n) :
    MultiwedgeSmooth.slack (normal u) (height u d) v.val (active d v i) = 0 := by
  have hv := (mem_vertices d v.val).1 v.property i
  by_cases hi : v.val i = d
  · rw [active, if_pos hi]
    simp [MultiwedgeSmooth.slack, hi, height, normal, integerPairing, Pi.single_apply]
  · have hi' : v.val i = -d := hv.resolve_right hi
    rw [active, if_neg hi]
    simp [MultiwedgeSmooth.slack, hi', height, normal,
      integerPairing, Pi.single_apply, Finset.sum_neg_distrib]

theorem zero_slack_active (hd : 0 < d) (v : {v // v ∈ vertices (n := n) d})
    (a : Label n E)
    (hz : MultiwedgeSmooth.slack (normal u) (height u d) v.val a = 0) :
    ∃ i, active d v i = a := by
  cases a with
  | inl e =>
    have hstrict := raw_strict u d hd (vertex_mem_cube d hd.le v) e
    have he : (height u d (.inl e) : ℝ) - pairing (embed v.val) (u e) = 0 := by
      change height u d (.inl e) - integerPairing v.val (u e) = 0 at hz
      rw [pairing_embed]
      exact_mod_cast hz
    linarith
  | inr a =>
    cases a with
    | inl i =>
      have hi : v.val i = d := by
        have he : d - v.val i = 0 := by
          simpa [MultiwedgeSmooth.slack, height, normal, integerPairing,
            Pi.single_apply] using hz
        exact (sub_eq_zero.mp he).symm
      exact ⟨i, by simp [active, hi]⟩
    | inr i =>
      have hi : v.val i ≠ d := by
        intro he
        simp [MultiwedgeSmooth.slack, height, normal, integerPairing, Pi.single_apply,
          Finset.sum_neg_distrib, he] at hz
        omega
      exact ⟨i, by simp [active, hi]⟩

theorem height_ge (hd : 0 ≤ d) (a : Label n E) : d ≤ height u d a := by
  cases a with
  | inl e =>
    have hm : 0 ≤ mass u e := Finset.sum_nonneg fun i _ => abs_nonneg _
    dsimp [height]
    nlinarith
  | inr a => exact le_rfl

/-- Every input height is a multiple of the prescribed index. -/
theorem height_dvd (a : Label n E) : d ∣ height u d a := by
  cases a <;> simp [height]

/-- Every input vertex is zero modulo the prescribed index. -/
theorem vertex_dvd (v : Lattice n) (hv : v ∈ vertices (n := n) d) (i : Fin n) : d ∣ v i := by
  rcases (mem_vertices d v).1 hv i with hi | hi <;> simp [hi]

/-- The number of new coordinates is dictated by each actual integer height. -/
def Block (a : Label n E) := Fin ((height u d a).toNat - 1)

instance (a : Label n E) : Fintype (Block u d a) := inferInstanceAs (Fintype (Fin _))
instance (a : Label n E) : DecidableEq (Block u d a) := inferInstanceAs (DecidableEq (Fin _))

theorem block_card (hd : 2 ≤ d) (a : Label n E) :
    (Fintype.card (Block u d a) : ℤ) + 1 = height u d a := by
  have hh := height_ge u d (by omega) a
  have hc : Fintype.card (Block u d a) = (height u d a).toNat - 1 := Fintype.card_fin _
  rw [hc]
  omega

theorem block_nonempty (hd : 2 ≤ d) (a : Label n E) : Nonempty (Block u d a) := by
  have hh := height_ge u d (by omega) a
  exact ⟨⟨0, by omega⟩⟩

/-- A smooth reflexive polytope for every integer column family and index `d ≥ 2`.
All original labels, including loops and repetitions, survive among its lifted facets. -/
def presentation (hd : 2 ≤ d) :
    SmoothReflexivePresentation
      (MultiwedgeSmooth.dimension (n := n) (Block u d)) :=
  MultiwedgeSmooth.presentation (Block u d) (normal u) (height u d) (vertices d)
    (basis d) (active d) (normal_active_eq_basis u d) (active_slack_zero u d)
    (zero_slack_active u d (by omega)) (block_card u d hd) (vertices_nonempty d)
    (block_nonempty u d hd)
    ((base_eq_cube u d (by omega)).trans (cube_eq_convexHull d (by omega)))

end
end Unimodular.CubeInput

#print axioms Unimodular.CubeInput.presentation

end FanoSource6

section FanoSource7


set_option backward.isDefEq.respectTransparency false

/-!
# The integral character witnessing divisibility of the boundary class

The character is zero in the old coordinates and one in each private coordinate.
Its value on a pure facet is one, and its value on the lift of the label `e` is
`1 - h e`. Hence heights divisible by `d` make the all-ones divisor differ from
a multiple of an integral invariant divisor by this actual principal character.
-/

namespace Unimodular.MultiwedgeSmooth

open scoped BigOperators
noncomputable section
variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
variable (J : E → Type*) [∀ e, Fintype (J e)] [∀ e, DecidableEq (J e)]
variable (A : E → Lattice n) (h : E → ℤ)

def indexCharacter : Lattice (dimension (n := n) J) :=
  ProductCoordinates.pack (Extra J) ℤ (0, fun _ => 1)

theorem indexCharacter_pure (s : Extra J) :
    integerPairing (indexCharacter (n := n) J)
      (ProductCoordinates.pack (Extra J) ℤ (MultiwedgeGeometry.normal J A (.inr s))) = 1 := by
  apply Int.cast_injective (α := ℝ)
  rw [← pairing_embed, indexCharacter, ProductCoordinates.embed_pack,
    ProductCoordinates.pairing_pack]
  simpa [ProductCoordinates.embedProduct] using MultiwedgeGeometry.pairing_pure J A
    (ProductCoordinates.embedProduct (Extra J) (0, fun _ => 1)) s

theorem indexCharacter_lift
    (hcard : ∀ e, (Fintype.card (J e) : ℤ) + 1 = h e) (e : E) :
    integerPairing (indexCharacter (n := n) J)
      (ProductCoordinates.pack (Extra J) ℤ (MultiwedgeGeometry.normal J A (.inl e))) =
      1 - h e := by
  apply Int.cast_injective (α := ℝ)
  rw [← pairing_embed, indexCharacter, ProductCoordinates.embed_pack,
    ProductCoordinates.pairing_pack]
  have he := MultiwedgeGeometry.pairing_lift J A
    (ProductCoordinates.embedProduct (Extra J) (0, fun _ => 1)) e
  simp only [ProductCoordinates.embedProduct, embed, Pi.zero_apply, Int.cast_zero,
    Int.cast_one, pairing, zero_mul, Finset.sum_const_zero, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, zero_sub] at he
  simpa only [ProductCoordinates.embedProduct, embed, Int.cast_one] using he.trans (by
    have hh : -(Fintype.card (J e) : ℤ) = 1 - h e := by linarith [hcard e]
    exact_mod_cast hh)

/-- Literal equality of integral divisor coefficients, including the principal
character term; no class-group equality is assumed. -/
theorem boundary_coefficient_relation
    (hcard : ∀ e, (Fintype.card (J e) : ℤ) + 1 = h e)
    (d : ℤ) (hh : ∀ e, d ∣ h e) :
    ∃ D : Lattice (dimension (n := n) J) → ℤ,
      ∀ u ∈ packedNormals J A,
        1 = d * D u + integerPairing (indexCharacter (n := n) J) u := by
  let D : Lattice (dimension (n := n) J) → ℤ :=
    fun u => (1 - integerPairing (indexCharacter (n := n) J) u) / d
  refine ⟨D, ?_⟩
  intro u hu
  have hdiv : d ∣ 1 - integerPairing (indexCharacter (n := n) J) u := by
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hq
    cases a with
    | inl e => simpa only [indexCharacter_lift J A h hcard, sub_sub_cancel] using hh e
    | inr s => simp only [indexCharacter_pure, sub_self, dvd_zero]
  have he := Int.mul_ediv_cancel_of_dvd hdiv
  dsimp [D]
  linarith

end
end Unimodular.MultiwedgeSmooth

#print axioms Unimodular.MultiwedgeSmooth.boundary_coefficient_relation

end FanoSource7

section FanoSource8


set_option backward.isDefEq.respectTransparency false

/-! # Uniform unimodularity of the complete Fano construction

The argument bounds every square minor of the actual labelled ray matrix.
It therefore applies to every independent full-rank selection in the facet set,
not merely the bases appearing as maximal cones of its normal fan.
-/

namespace Unimodular.MultiwedgeSmooth

noncomputable section
variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
variable (J : E → Type*) [∀ e, Fintype (J e)] [∀ e, DecidableEq (J e)]
variable (A : E → Lattice n)

def packedFamily : E ⊕ Extra J → Lattice (dimension (n := n) J) :=
  fun e => ProductCoordinates.pack (Extra J) ℤ (MultiwedgeGeometry.normal J A e)

def packedMatrix : Matrix (Fin (dimension (n := n) J)) (E ⊕ Extra J) ℤ :=
  fun i e => packedFamily J A e i

theorem packedMatrix_eq : packedMatrix J A =
    (Multiwedge.matrix (fun i e => A e i) Sigma.fst).submatrix
      (ProductCoordinates.indexEquiv (n := n) (Extra J)).symm id := by
  ext i e
  obtain ⟨j,rfl⟩ := (ProductCoordinates.indexEquiv (n := n) (Extra J)).surjective i
  simp only [packedMatrix, packedFamily, ProductCoordinates.pack_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply, id_eq]
  cases j <;> cases e <;>
    simp [MultiwedgeGeometry.normal, MultiwedgeBasis.lift, MultiwedgeBasis.pure,
      Multiwedge.matrix, Multiwedge.privateRows, Multiwedge.privateColumns,
      Pi.single_apply, eq_comm]

theorem packedMatrix_tu (hA : Matrix.IsTotallyUnimodular (fun i e => A e i)) :
    (packedMatrix J A).IsTotallyUnimodular := by
  rw [packedMatrix_eq]
  exact (Multiwedge.totallyUnimodular _ Sigma.fst hA).submatrix _ _

theorem packedFamily_uniform (hA : Matrix.IsTotallyUnimodular (fun i e => A e i)) :
    IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin (dimension (n := n) J))) (packedFamily J A) := by
  intro a
  rw [Pi.basisFun_det_apply]
  have he : Matrix.of (packedFamily J A ∘ a) =
      ((packedMatrix J A).submatrix id a).transpose := rfl
  rw [he, Matrix.det_transpose]
  obtain ⟨s,hs⟩ := (Matrix.isTotallyUnimodular_iff _).1 (packedMatrix_tu J A hA)
    (dimension (n := n) J) id a
  rw [← hs]
  cases s <;> norm_num

theorem mem_packedNormals_iff (u : Lattice (dimension (n := n) J)) :
    u ∈ packedNormals J A ↔ ∃ e, packedFamily J A e = u := by
  simp only [packedNormals, MultiwedgeGeometry.normals, Finset.image_image,
    Finset.mem_image, Finset.mem_univ, true_and, packedFamily, Function.comp_def]

theorem packedNormals_uniform (hA : Matrix.IsTotallyUnimodular (fun i e => A e i)) :
    IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin (dimension (n := n) J)))
      (fun u : {u // u ∈ packedNormals J A} => u.val) := by
  intro a
  choose f hf using fun i => (mem_packedNormals_iff J A (a i).val).1 (a i).property
  have he : (fun u : {u // u ∈ packedNormals J A} => u.val) ∘ a = packedFamily J A ∘ f := by
    funext i
    exact (hf i).symm
  rw [he]
  exact packedFamily_uniform J A hA f

end
end Unimodular.MultiwedgeSmooth

namespace Unimodular.CubeInput

noncomputable section
variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
variable (u : E → Lattice n)

/-- Appending both signs of every coordinate vector preserves all square minor bounds. -/
theorem normal_tu (hu : Matrix.IsTotallyUnimodular (fun i e => u e i)) :
    Matrix.IsTotallyUnimodular (fun i e => normal u e i) := by
  let B : Matrix (Fin n ⊕ Fin n) (Fin n) ℤ := fun a i => normal u (.inr a) i
  have hB : (Matrix.fromRows (fun e i => u e i) B).IsTotallyUnimodular := by
    apply hu.transpose.fromRows_unitlike
    intro _ a
    cases a with
    | inl i => exact ⟨i, 1, by ext j; simp [B, normal]⟩
    | inr i =>
      refine ⟨i, -1, ?_⟩
      ext j
      simp [B, normal, Pi.single_apply, apply_ite]
  have he : (Matrix.fromRows (fun e i => u e i) B).transpose =
      (fun i e => normal u e i) := by
    ext i e
    cases e <;> rfl
  exact he ▸ hB.transpose

/-- The Fano polytope is uniformly unimodular whenever the prescribed matrix is TU. -/
theorem presentation_uniform (d : ℤ) (hd : 2 ≤ d)
    (hu : Matrix.IsTotallyUnimodular (fun i e => u e i)) :
    IntegralRigidity.Uniform
      (Pi.basisFun ℤ (Fin (MultiwedgeSmooth.dimension (n := n) (Block u d))))
      (fun v : {v // v ∈ (presentation u d hd).normals} => v.val) :=
  MultiwedgeSmooth.packedNormals_uniform (Block u d) (normal u) (normal_tu u hu)

end
end Unimodular.CubeInput

#print axioms Unimodular.MultiwedgeSmooth.packedNormals_uniform
#print axioms Unimodular.CubeInput.presentation_uniform

end FanoSource8

section FanoSource9


/-! # The actual facet labels

Each lifted label has its own nonempty block of negative private coordinates;
each pure label is a positive unit vector. Consequently the complete family is
injective, even when the original input has zero or repeated columns. This gives
literal embeddings into the finite set of geometric primitive facet normals.
-/

namespace Unimodular.MultiwedgeSmooth

noncomputable section
variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
variable (J : E → Type*) [∀ e, Fintype (J e)] [∀ e, DecidableEq (J e)]
variable (A : E → Lattice n)

theorem normal_injective (hJ : ∀ e, Nonempty (J e)) :
    Function.Injective (MultiwedgeGeometry.normal J A) := by
  intro a b he
  cases a with
  | inl e =>
    cases b with
    | inl f =>
      apply congrArg Sum.inl
      by_contra hef
      let j := Classical.choice (hJ e)
      have hh := congrArg (fun z => z.2 (⟨e,j⟩ : Extra J)) he
      simp [MultiwedgeGeometry.normal, MultiwedgeBasis.lift, hef] at hh
    | inr s =>
      have hh := congrArg (fun z => z.2 s) he
      simp only [MultiwedgeGeometry.normal, MultiwedgeBasis.lift,
        MultiwedgeBasis.pure, Pi.single_eq_same] at hh
      split_ifs at hh <;> norm_num at hh
  | inr s =>
    cases b with
    | inl e =>
      have hh := congrArg (fun z => z.2 s) he
      simp only [MultiwedgeGeometry.normal, MultiwedgeBasis.lift,
        MultiwedgeBasis.pure, Pi.single_eq_same] at hh
      split_ifs at hh <;> norm_num at hh
    | inr t =>
      apply congrArg Sum.inr
      by_contra hst
      have hh := congrArg (fun z => z.2 s) he
      simp [MultiwedgeGeometry.normal, MultiwedgeBasis.pure, Pi.single_apply,
        hst, Ne.symm hst] at hh

theorem packedFamily_injective (hJ : ∀ e, Nonempty (J e)) :
    Function.Injective (packedFamily J A) := by
  intro a b he
  apply normal_injective J A hJ
  exact (ProductCoordinates.pack (Extra J) ℤ).injective he

/-- Every original label and every private label gives a distinct actual facet. -/
def facetEmbedding (hJ : ∀ e, Nonempty (J e)) :
    (E ⊕ Extra J) ↪ {u // u ∈ packedNormals J A} where
  toFun e := ⟨packedFamily J A e, (mem_packedNormals_iff J A _).2 ⟨e,rfl⟩⟩
  inj' := by
    intro e f he
    exact packedFamily_injective J A hJ (congrArg Subtype.val he)

@[simp] theorem facetEmbedding_val (hJ : ∀ e, Nonempty (J e)) (e : E ⊕ Extra J) :
    (facetEmbedding J A hJ e).val = packedFamily J A e := rfl

end
end Unimodular.MultiwedgeSmooth

#print axioms Unimodular.MultiwedgeSmooth.facetEmbedding

end FanoSource9

section FanoSource10


set_option backward.isDefEq.respectTransparency false

/-!
# Divisibility and absence of unimodular triangular faces

Congruence of all vertices modulo a nonunit forces every vertex difference
to be nonprimitive. This excludes genuine unimodular triangles in every face,
using the full saturated lattice of their plane. For a multiwedge the common
residue is zero in the old coordinates and one in every new coordinate.
-/

namespace Unimodular.LatticeCongruence

open Set
open scoped BigOperators
noncomputable section

/-- A geometric face cannot be a unimodular triangle when every difference
of ambient vertices is divisible by a fixed nonunit integer. -/
theorem no_unimodular_triangle {n : ℕ} (P : SmoothReflexivePresentation n)
    (d : ℤ) (hd : ¬ IsUnit d)
    (hdiv : ∀ a ∈ P.vertices, ∀ b ∈ P.vertices, ∃ z : Lattice n, b - a = d • z)
    (F : Set (Ambient n)) (hF : IsExtreme ℝ P.carrier F) :
    ¬ SegmentSimplex.IsUnimodularTriangle F := by
  intro htri
  obtain ⟨a,b,ha,hb,hprim⟩ := SegmentSimplex.unimodular_triangle_has_primitive_edge htri
  have haP := hF.extremePoints_subset_extremePoints ha
  have hbP := hF.extremePoints_subset_extremePoints hb
  have hsub : P.carrier.extremePoints ℝ ⊆ embed '' (P.vertices : Set (Lattice n)) :=
    extremePoints_convexHull_subset
  obtain ⟨a',ha',hea⟩ := hsub haP
  obtain ⟨b',hb',heb⟩ := hsub hbP
  have ea : a' = a := by
    funext i
    apply Int.cast_injective (α := ℝ)
    exact congrFun hea i
  have eb : b' = b := by
    funext i
    apply Int.cast_injective (α := ℝ)
    exact congrFun heb i
  subst a'
  subst b'
  obtain ⟨z,hz⟩ := hdiv a ha' b hb'
  exact hd (hprim d z hz)

theorem integerPairing_dvd {n : ℕ} (d : ℤ) (v u : Lattice n)
    (hv : ∀ i, d ∣ v i) : d ∣ integerPairing v u := by
  exact Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_left (hv i) (u i))

end
end Unimodular.LatticeCongruence

namespace Unimodular.MultiwedgeSmooth

open Set
open scoped BigOperators
noncomputable section

variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
variable (J : E → Type*) [∀ e, Fintype (J e)] [∀ e, DecidableEq (J e)]
variable (A : E → Lattice n) (h : E → ℤ) (d : ℤ)

include d in
theorem slack_dvd (v : Lattice n) (hv : ∀ i, d ∣ v i) (hh : ∀ e, d ∣ h e)
    (e : E) : d ∣ slack A h v e :=
  dvd_sub (hh e) (LatticeCongruence.integerPairing_dvd d v (A e) hv)

theorem point_extra_residue (v : Lattice n) (hv : ∀ i, d ∣ v i)
    (hh : ∀ e, d ∣ h e) (c : Choice J) (s : Extra J) :
    d ∣ (point J A h v c).2 s - 1 := by
  change d ∣ (1 - (if c s.1 = some s.2 then slack A h v s.1 else 0)) - 1
  by_cases hc : c s.1 = some s.2
  · simpa [hc] using dvd_neg.mpr (slack_dvd A h d v hv hh s.1)
  · simp [hc]

theorem point_difference (v w : Lattice n) (hv : ∀ i, d ∣ v i)
    (hw : ∀ i, d ∣ w i) (hh : ∀ e, d ∣ h e) (c t : Choice J) :
    ∃ z : Lattice (dimension (n := n) J),
      ProductCoordinates.pack (Extra J) ℤ (point J A h w t) -
        ProductCoordinates.pack (Extra J) ℤ (point J A h v c) = d • z := by
  have hcoord (i : Fin (dimension (n := n) J)) :
      d ∣ (ProductCoordinates.pack (Extra J) ℤ (point J A h w t) -
        ProductCoordinates.pack (Extra J) ℤ (point J A h v c)) i := by
    obtain ⟨j,rfl⟩ := (ProductCoordinates.indexEquiv (n := n) (Extra J)).surjective i
    simp only [Pi.sub_apply, ProductCoordinates.pack_apply]
    cases j with
    | inl i => exact dvd_sub (hw i) (hv i)
    | inr s =>
      have hb := point_extra_residue J A h d w hw hh t s
      have ha := point_extra_residue J A h d v hv hh c s
      simpa using dvd_sub hb ha
  choose z hz using hcoord
  exact ⟨z, funext hz⟩

theorem packed_vertices_difference (S : Finset (Lattice n))
    (hS : ∀ v ∈ S, ∀ i, d ∣ v i) (hh : ∀ e, d ∣ h e)
    (a b : Lattice (dimension (n := n) J))
    (ha : a ∈ packedVertices J A h S) (hb : b ∈ packedVertices J A h S) :
    ∃ z : Lattice (dimension (n := n) J), b - a = d • z := by
  obtain ⟨p,hp⟩ := exists_point J A h S ⟨a,ha⟩
  obtain ⟨q,hq⟩ := exists_point J A h S ⟨b,hb⟩
  change ProductCoordinates.pack (Extra J) ℤ (point J A h p.1.val p.2) = a at hp
  change ProductCoordinates.pack (Extra J) ℤ (point J A h q.1.val q.2) = b at hq
  rw [← hp, ← hq]
  exact point_difference J A h d p.1.val q.1.val
    (hS p.1.val p.1.property) (hS q.1.val q.1.property) hh p.2 q.2

variable (S : Finset (Lattice n))
variable (B : {v // v ∈ S} → Module.Basis (Fin n) ℤ (Lattice n))
variable (active : {v // v ∈ S} → Fin n → E)
variable (hb : ∀ v i, A (active v i) = B v i)
variable (ha : ∀ v i, slack A h v.val (active v i) = 0)
variable (hs : ∀ v e, slack A h v.val e = 0 → ∃ i, active v i = e)

/-- The divisible multiwedge has no unimodular triangular face in any dimension. -/
theorem presentation_UT_free
    (hcard : ∀ e, (Fintype.card (J e) : ℤ) + 1 = h e)
    (hSne : S.Nonempty) (hJ : ∀ e, Nonempty (J e))
    (hbase : SimplexBundle.base A h = convexHull ℝ (embed '' (S : Set (Lattice n))))
    (hd : ¬ IsUnit d) (hS : ∀ v ∈ S, ∀ i, d ∣ v i) (hh : ∀ e, d ∣ h e)
    (F : Set (Ambient (dimension (n := n) J)))
    (hF : IsExtreme ℝ
      (presentation J A h S B active hb ha hs hcard hSne hJ hbase).carrier F) :
    ¬ SegmentSimplex.IsUnimodularTriangle F := by
  apply LatticeCongruence.no_unimodular_triangle
    (presentation J A h S B active hb ha hs hcard hSne hJ hbase) d hd _ F hF
  intro a ha b hb
  exact packed_vertices_difference J A h d S hS hh a b ha hb

end
end Unimodular.MultiwedgeSmooth

#print axioms Unimodular.LatticeCongruence.no_unimodular_triangle
#print axioms Unimodular.MultiwedgeSmooth.presentation_UT_free


namespace Unimodular.CubeInput

noncomputable section
variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

/-- Every face of the constructed polytope avoids genuine unimodular triangles. -/
theorem presentation_UT_free (u : E → Lattice n) (d : ℤ) (hd : 2 ≤ d)
    (F : Set (Ambient (MultiwedgeSmooth.dimension (n := n) (Block u d))))
    (hF : IsExtreme ℝ (presentation u d hd).carrier F) :
    ¬ SegmentSimplex.IsUnimodularTriangle F := by
  apply LatticeCongruence.no_unimodular_triangle (presentation u d hd) d ?_ ?_ F hF
  · simp only [Int.isUnit_iff]
    omega
  · intro a ha b hb
    exact MultiwedgeSmooth.packed_vertices_difference (Block u d) (normal u) (height u d)
      d (vertices d) (vertex_dvd d) (height_dvd u d) a b ha hb

end
end Unimodular.CubeInput

#print axioms Unimodular.CubeInput.presentation_UT_free

end FanoSource10
