module
public import PaperVerification.ToricNormalFan
public import Mathlib.Data.Set.Finite.Lemmas
@[expose] public section
/-!
# Nonnegative edge degrees give globally feasible Cartier points

This is the elementary polytope form of the nef Cartier criterion. It is proved
on an actual finite reference polytope using a descending edge for every
nonminimal linear functional. The argument checks genuine vertex assignments
and their edge differences, with no global feasibility assumption.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open PaperVerification.ToricVertexCone

/-- Vanishing of all but one genuine basis coordinate characterizes the
corresponding real edge direction. -/
theorem eq_basis_smul_of_offdiagonal_zero {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (Ambient n)) (x : Ambient n) (i : Fin n)
    (h : ∀ j, j ≠ i → b.repr x j = 0) :
    x = b.repr x i • b i := by
  apply b.ext_elem
  intro j
  by_cases hji : j = i
  · subst j
    simp [LinearEquiv.map_smul]
  · simp [LinearEquiv.map_smul, h j hji, Module.Basis.repr_self,
      Finsupp.single_apply, hji, Ne.symm hji]

/-- Agreement on the active hyperplanes containing a reference edge forces
Cartier point differences to be parallel to that actual edge. -/
theorem cartier_difference_parallel {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (Ambient n)) (v w c d : Ambient n)
    (i : Fin n) (l : ℝ) (hl : l ≠ 0) (hedge : w - v = l • b i)
    (hactive : ∀ j, b.repr w j = b.repr v j → b.repr d j = b.repr c j) :
    d - c = (b.repr (d - c) i / l) • (w - v) := by
  have hoff (j : Fin n) (hji : j ≠ i) : b.repr (d - c) j = 0 := by
    have hcoord := congrArg (fun x => b.repr x j) hedge
    simp only [map_sub, Finsupp.sub_apply, LinearEquiv.map_smul,
      Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self,
      Finsupp.single_apply, if_neg (Ne.symm hji), mul_zero] at hcoord
    have hdc := hactive j (sub_eq_zero.mp hcoord)
    simp only [map_sub, Finsupp.sub_apply, hdc, sub_self]
  rw [hedge, smul_smul, div_mul_cancel₀ _ hl]
  exact eq_basis_smul_of_offdiagonal_zero b (d - c) i hoff

/-- Nonnegative coordinate edge degree gives a nonnegative parallel factor
for Cartier point differences. -/
theorem cartier_difference_nonnegative_multiple {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (Ambient n)) (v w c d : Ambient n)
    (i : Fin n) (l : ℝ) (hl : 0 < l) (hedge : w - v = l • b i)
    (hactive : ∀ j, b.repr w j = b.repr v j → b.repr d j = b.repr c j)
    (hdegree : 0 ≤ b.repr (d - c) i) :
    ∃ t : ℝ, 0 ≤ t ∧ d - c = t • (w - v) :=
  ⟨b.repr (d - c) i / l, div_nonneg hdegree hl.le,
    cartier_difference_parallel b v w c d i l hl.ne' hedge hactive⟩

namespace LatticePolytope

/-- At any vertex that does not minimize a linear functional, an actual
incident edge decreases that functional. This follows from the proved tangent
cone theorem for finite convex hulls. -/
theorem exists_descending_edge {n : ℕ} (P : LatticePolytope n)
    (v : Ambient n) (hv : v ∈ P.carrier.extremePoints ℝ)
    (f : Ambient n →ₗ[ℝ] ℝ) (hnotmin : ∃ x ∈ P.carrier, f x < f v) :
    ∃ w : Ambient n, P.IsEdge v w ∧ f w < f v := by
  classical
  by_contra h
  have hnonneg : ∀ w, P.IsEdge v w → 0 ≤ f (w - v) := by
    intro w hw
    have hle : f v ≤ f w := le_of_not_gt (fun hlt => h ⟨w, hw, hlt⟩)
    simpa only [map_sub, sub_nonneg] using hle
  let s := P.generators.image (embed n)
  have hcarrier : convexHull ℝ (s : Set (Ambient n)) = P.carrier := by
    simp [s, carrier, Finset.coe_image]
  have hv' : v ∈ (convexHull ℝ (s : Set (Ambient n))).extremePoints ℝ := by
    simpa only [hcarrier] using hv
  have hglobal := linear_nonneg_of_incident_edges s v hv' f
    (fun w hvw hface => hnonneg w ⟨hvw, by simpa only [hcarrier] using hface⟩)
  obtain ⟨x, hx, hlt⟩ := hnotmin
  have hx' : x ∈ convexHull ℝ (s : Set (Ambient n)) := by
    simpa only [hcarrier] using hx
  have hle := hglobal x hx'
  simp only [map_sub, sub_nonneg] at hle
  exact (not_lt_of_ge hle) hlt

/-- Assign a Cartier point to each actual reference vertex. If every
oriented edge difference is a nonnegative multiple of its original direction,
then all assigned points satisfy every target supporting halfspace.
The proof is finite descent in the original support height. -/
theorem cartier_feasible_of_nonnegative_edges {n : ℕ} (P : LatticePolytope n)
    {I : Type*} (u : I → Ambient n →ₗ[ℝ] ℝ) (a d : I → ℝ)
    (c : P.carrier.extremePoints ℝ → Ambient n)
    (hsupport : ∀ i x, x ∈ P.carrier → a i ≤ u i x)
    (hattain : ∀ i, ∃ x ∈ P.carrier, u i x = a i)
    (hactive : ∀ (j : P.carrier.extremePoints ℝ) i,
      u i (j : Ambient n) = a i → u i (c j) = d i)
    (hedge : ∀ v w : P.carrier.extremePoints ℝ, P.IsEdge v w →
      ∃ t : ℝ, 0 ≤ t ∧ c w - c v = t • ((w : Ambient n) - v)) :
    ∀ j, c j ∈ normalHalfspaces u d := by
  classical
  let J := P.carrier.extremePoints ℝ
  letI : Fintype J := P.finite_vertices.fintype
  intro j0 i
  by_contra hbad
  have hj0 : u i (c j0) < d i := lt_of_not_ge hbad
  let B : Set J := {j | u i (c j) < d i}
  obtain ⟨j, hj, hmin⟩ := Set.exists_min_image B (fun j : J => u i (j : Ambient n))
    B.toFinite ⟨j0, hj0⟩
  have hnotactive : u i (j : Ambient n) ≠ a i := by
    intro he
    have h := hactive j i he
    exact (ne_of_lt hj) h
  have hheight : a i < u i (j : Ambient n) :=
    lt_of_le_of_ne (hsupport i j j.property.1) hnotactive.symm
  obtain ⟨x, hx, hxi⟩ := hattain i
  obtain ⟨w, hjw, hdec⟩ := P.exists_descending_edge j j.property (u i)
    ⟨x, hx, by simpa only [hxi] using hheight⟩
  let wJ : J := ⟨w, (P.edge_endpoints_extreme hjw).2⟩
  obtain ⟨t, ht, he⟩ := hedge j wJ hjw
  have he' := congrArg (u i) he
  simp only [map_sub, map_smul, smul_eq_mul] at he'
  have hdecle : u i (wJ : Ambient n) - u i (j : Ambient n) ≤ 0 := by
    exact sub_nonpos.mpr hdec.le
  have htargetle : u i (c wJ) ≤ u i (c j) := by
    have h := mul_nonpos_of_nonneg_of_nonpos ht hdecle
    rw [← he'] at h
    exact sub_nonpos.mp h
  have hwbad : wJ ∈ B := htargetle.trans_lt hj
  exact (not_lt_of_ge (hmin wJ hwbad)) hdec

/-- The complete convex-hull form of the nef Cartier criterion, using actual
reference-vertex basis cones and the proven global feasibility above. -/
theorem cartier_halfspaces_eq_hull_of_nonnegative_edges {n : ℕ} (P : LatticePolytope n)
    {I : Type*} (u : I → Ambient n →ₗ[ℝ] ℝ) (a d : I → ℝ)
    (b : P.carrier.extremePoints ℝ → Module.Basis (Fin n) ℝ (Ambient n))
    (active : P.carrier.extremePoints ℝ → Fin n → I)
    (c : P.carrier.extremePoints ℝ → Ambient n)
    (hsupport : ∀ i x, x ∈ P.carrier → a i ≤ u i x)
    (hattain : ∀ i, ∃ x ∈ P.carrier, u i x = a i)
    (hactive_original : ∀ j k, u (active j k) (j : Ambient n) = a (active j k))
    (hactive : ∀ (j : P.carrier.extremePoints ℝ) i,
      u i (j : Ambient n) = a i → u i (c j) = d i)
    (hdual : ∀ j k x, u (active j k) x = (b j).repr x k)
    (hcomplete : ∀ f : Ambient n →ₗ[ℝ] ℝ, ∃ j, ∀ k, 0 ≤ f (b j k))
    (hedge : ∀ v w : P.carrier.extremePoints ℝ, P.IsEdge v w →
      ∃ t : ℝ, 0 ≤ t ∧ c w - c v = t • ((w : Ambient n) - v)) :
    normalHalfspaces u d = convexHull ℝ (Set.range c) := by
  classical
  letI : Fintype (P.carrier.extremePoints ℝ) := P.finite_vertices.fintype
  apply shifted_halfspaces_eq_convexHull u d b active c hdual hcomplete
  · intro j k
    exact hactive j (active j k) (hactive_original j k)
  · exact P.cartier_feasible_of_nonnegative_edges u a d c hsupport hattain hactive hedge

end LatticePolytope

end PaperVerification.ToricGeometry
