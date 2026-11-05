module

public import dirichlet
import harmonic_adjacent
import Lean.Data.Json.Basic
import Lean.Data.Json.FromToJson.Basic
import Lean.Data.Json.Printer
import Lean.Elab.Command
import Lean.Meta.Basic
import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.IntermediateValue
public import planar_geometry
public import triangle_sides
public import triangular_disk

-- Generated verification output directories.
run_cmd Lean.Elab.Command.liftIO do
  IO.FS.createDirAll ".lake/reports/audit/final"


/-! # Planar prerequisites for the three-dimensional construction

This module combines the convex-cap data, the proved adjacent-face interface,
and the elementary Euler count. The editable inputs and exact retained lines
are recorded in the generated source map. All mathematical bodies are unchanged.
-/

@[expose] public section
noncomputable section

/- Source component: Cor2Candidate/ConvexCap.lean -/
section


/-!
# Genuine strictly convex caps over the fixed triangle

The roof functions are actual affine supporting functions for the lifted
vertices. The strict inequalities record exactly which labelled vertices lie
on each roof face. No stress, PN relation, or connectedness conclusion is built
into this definition.
-/



namespace NormalProjective.Planar

open Set Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

structure StrictConvexCap (V : Type*) [Fintype V] [DecidableEq V] where
  disk : TriangularDisk V
  interior_nonempty : ∃ v, v ∉ disk.boundary
  height : V → ℝ
  boundary_zero : ∀ j, height (disk.corner j) = 0
  interior_positive : ∀ v, v ∉ disk.boundary → 0 < height v
  roof : disk.toTriangulation.Face → (ℂ →ᵃ[ℝ] ℝ)
  roof_equal : ∀ s v, v ∈ s.val → roof s (disk.point v) = height v
  roof_strict : ∀ s v, v ∉ s.val → height v < roof s (disk.point v)

namespace StrictConvexCap

variable (C : StrictConvexCap V)

def lifted (v : V) : Fin 3 → ℝ := ![(C.disk.point v).re,(C.disk.point v).im,C.height v]

def carrier : Set (Fin 3 → ℝ) := convexHull ℝ (Set.range C.lifted)

def SameCombinatorics (C D : StrictConvexCap V) : Prop :=
  C.disk.faces = D.disk.faces ∧ C.disk.corner = D.disk.corner

instance : TopologicalSpace (StrictConvexCap V) :=
  TopologicalSpace.induced (fun C => (C.disk.point,C.height)) inferInstance

theorem lifted_injective : Function.Injective C.lifted := by
  intro v w h
  apply C.disk.point_injective
  apply Complex.ext
  · exact congrFun h 0
  · exact congrFun h 1

theorem height_nonnegative (v : V) : 0 ≤ C.height v := by
  by_cases hv : v ∈ C.disk.boundary
  · obtain ⟨j,rfl⟩ := hv
    rw [C.boundary_zero]
  · exact (C.interior_positive v hv).le

theorem carrier_compact : IsCompact C.carrier :=
  (Set.finite_range C.lifted).isCompact_convexHull ℝ

end StrictConvexCap

end NormalProjective.Planar
end

/- Source component: Cor2Candidate/HarmonicAdjacencyAPI.lean -/
section



/-!
# The proved adjacent-face statements behind a small public interface

The public types below use the original geometric triangular disk and the
actual weighted harmonic equation. The implementation imports the previously
developed adjacent-face proofs privately, so downstream modules do not need
their cycle-construction and Jordan-separation implementation interfaces.

Each theorem is an exact application of its corresponding theorem in
`harmonic_adjacent`, with all quantifiers and hypotheses retained. These are
ordinary proof terms, not declarations of axioms or new assumptions.
The ordinary compiler and axiom-audit records identify the checked source bytes.
-/

namespace NormalProjective.Planar

/-- Exact public counterpart of `boundary_height_coordinate`. -/
public theorem boundary_height_coordinate_exact (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ σ : ℝ, σ ≠ 0 ∧ ∀ z : ℂ,
      edgeHeight (basePoint i) (basePoint j) z = σ * triangleCoordinate k z := by
  exact boundary_height_coordinate i j k hij hik hjk

namespace TriangularDisk

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact public counterpart of
`TriangularDisk.coordinate_pos_of_ne_other_corners`. -/
public theorem coordinate_positive_away_two_corners
    (D : TriangularDisk V) (i j k : Fin 3)
    (hcover : ∀ l : Fin 3, l = i ∨ l = j ∨ l = k)
    (v : V) (hvi : v ≠ D.corner i) (hvj : v ≠ D.corner j) :
    0 < triangleCoordinate k (D.point v) := by
  exact D.coordinate_pos_of_ne_other_corners i j k hcover v hvi hvj

/-- Exact public counterpart of
`TriangularDisk.interior_endpoint_of_two_faces`. -/
public theorem adjacent_faces_have_interior_endpoint
    (D : TriangularDisk V) {a b x y : V}
    (hs : ({a,b,x} : Finset V) ∈ D.faces)
    (ht : ({a,b,y} : Finset V) ∈ D.faces)
    (hab : a ≠ b) (hxy : x ≠ y)
    (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b) :
    a ∉ D.boundary ∨ b ∉ D.boundary := by
  exact D.interior_endpoint_of_two_faces hs ht hab hxy hxa hxb hya hyb

/-- Exact public counterpart of
`TriangularDisk.harmonic_height_negative_at_adjacent_face`. -/
public theorem harmonic_height_negative_across_edge
    (D : TriangularDisk V)
    (w : V → V → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (he : ∀ i j, D.toTriangulation.graph.Adj i j → 0 < w i j)
    (hoff : ∀ i j, ¬ D.toTriangulation.graph.Adj i j → w i j = 0)
    (h : V → ℝ) (hh : ∀ i, i ∉ D.boundary → Dirichlet.Harmonic w h i)
    {a b x y : V}
    (hs : ({a,b,x} : Finset V) ∈ D.faces)
    (ht : ({a,b,y} : Finset V) ∈ D.faces)
    (hab : a ≠ b) (hxy : x ≠ y)
    (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b)
    (ha : h a = 0) (hb : h b = 0) (hx : 0 < h x) : h y < 0 := by
  exact D.harmonic_height_negative_at_adjacent_face w hw he hoff h hh
    hs ht hab hxy hxa hxb hya hyb ha hb hx

end TriangularDisk
end NormalProjective.Planar

#print axioms NormalProjective.Planar.boundary_height_coordinate_exact
#print axioms NormalProjective.Planar.TriangularDisk.coordinate_positive_away_two_corners
#print axioms NormalProjective.Planar.TriangularDisk.adjacent_faces_have_interior_endpoint
#print axioms NormalProjective.Planar.TriangularDisk.harmonic_height_negative_across_edge

end

/- Source component: Cor2Candidate/EulerElementary.lean -/
section



/-! # The elementary face count for a finite triangular disk

A generic linear height counts each triangular face at its unique middle
vertex. Interior vertices contribute two transverse rays and the unique
middle boundary corner contributes one. No harmonic embedding is assumed.
-/


/-! ## EulerHeight -/


/-!
# A generic height for a finite planar drawing

The height `re z + a * im z`, with `0 < a < 1`, has pairwise distinct
values on any prescribed finite set of distinct vertices after avoiding
finitely many slopes. The corresponding level direction is `a - I`.
This elementary choice is used in the planar Euler count.
-/



namespace NormalProjective.Planar

open Set Finset Complex

def eulerHeight (a : ℝ) (z : ℂ) : ℝ := z.re + a * z.im

def eulerDirection (a : ℝ) : ℂ := (a : ℂ) - Complex.I

@[simp] theorem eulerHeight_zero (a : ℝ) : eulerHeight a 0 = 0 := by
  simp [eulerHeight]

@[simp] theorem eulerHeight_one (a : ℝ) : eulerHeight a 1 = 1 := by
  simp [eulerHeight]

@[simp] theorem eulerHeight_I (a : ℝ) : eulerHeight a Complex.I = a := by
  simp [eulerHeight]

@[simp] theorem eulerHeight_direction (a : ℝ) : eulerHeight a (eulerDirection a) = 0 := by
  simp [eulerHeight,eulerDirection]

theorem eulerDirection_ne_zero (a : ℝ) : eulerDirection a ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp [eulerDirection] at this

theorem eulerHeight_add (a : ℝ) (z w : ℂ) :
    eulerHeight a (z+w) = eulerHeight a z + eulerHeight a w := by
  simp only [eulerHeight,Complex.add_re,Complex.add_im]
  ring

theorem eulerHeight_smul (a t : ℝ) (z : ℂ) :
    eulerHeight a (t • z) = t * eulerHeight a z := by
  simp only [eulerHeight,Complex.smul_re,Complex.smul_im,smul_eq_mul]
  ring

def eulerHeightLinear (a : ℝ) : ℂ →ₗ[ℝ] ℝ where
  toFun := eulerHeight a
  map_add' := eulerHeight_add a
  map_smul' t z := eulerHeight_smul a t z

@[simp] theorem eulerHeightLinear_apply (a : ℝ) (z : ℂ) :
    eulerHeightLinear a z = eulerHeight a z := rfl

theorem eulerHeight_ray (a t : ℝ) (z : ℂ) :
    eulerHeight a (z+t • eulerDirection a) = eulerHeight a z := by
  rw [eulerHeight_add,eulerHeight_smul,eulerHeight_direction,mul_zero,add_zero]

theorem eq_ray_of_eulerHeight_eq (a : ℝ) {z w : ℂ}
    (h : eulerHeight a z = eulerHeight a w) :
    z = w + (w.im-z.im) • eulerDirection a := by
  apply Complex.ext
  · dsimp [eulerHeight] at h
    simp only [Complex.add_re,Complex.smul_re,smul_eq_mul,eulerDirection,
      Complex.sub_re,Complex.ofReal_re,Complex.I_re,sub_zero]
    linarith
  · simp only [Complex.add_im,Complex.smul_im,smul_eq_mul,eulerDirection,
      Complex.sub_im,Complex.ofReal_im,Complex.I_im,zero_sub,mul_neg,mul_one]
    ring

theorem exists_injective_eulerHeight {V : Type*} [Fintype V]
    (p : V → ℂ) (hp : Function.Injective p) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ Function.Injective (fun v => eulerHeight a (p v)) := by
  classical
  let bad : Finset ℝ := Finset.univ.image (fun vw : V × V =>
    -((p vw.1).re-(p vw.2).re) / ((p vw.1).im-(p vw.2).im))
  obtain ⟨a,ha,hbad⟩ := (Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num)).exists_notMem_finset bad
  refine ⟨a,ha.1,ha.2,?_⟩
  intro v w hvw
  by_cases him : (p v).im = (p w).im
  · apply hp
    apply Complex.ext _ him
    dsimp [eulerHeight] at hvw
    rw [him] at hvw
    linarith
  · have hd : (p v).im-(p w).im ≠ 0 := sub_ne_zero.mpr him
    have heq : a = -((p v).re-(p w).re) / ((p v).im-(p w).im) := by
      apply (eq_div_iff hd).mpr
      dsimp [eulerHeight] at hvw
      nlinarith
    exact False.elim (hbad (Finset.mem_image.mpr ⟨(v,w),Finset.mem_univ _,heq.symm⟩))

end NormalProjective.Planar


/-! ## EulerElementary -/


/-!
# The elementary Euler count for a triangulated triangle

Choose a linear height with distinct values at all vertices. A triangle is
counted at its unique middle-height vertex. The two level rays at an interior
vertex each enter exactly one incident triangle. Only the middle corner of
the outer triangle has an inward level ray. Consequently `F = 2 I + 1`.

The proof uses the geometric triangulation's exact simplex intersections
and finite closed cover, rather than importing a homology theory.
-/



namespace NormalProjective.Planar

open Set Finset Complex Filter
open scoped Topology

theorem eulerHeight_continuous (a : ℝ) : Continuous (eulerHeight a) := by
  unfold eulerHeight
  fun_prop

theorem convex_interior_level_nonempty {S : Set ℂ}
    (hconv : Convex ℝ S) (hint : (interior S).Nonempty)
    (a : ℝ) {x y : ℂ} (hx : x ∈ S) (hy : y ∈ S) {c : ℝ}
    (hxc : eulerHeight a x < c) (hcy : c < eulerHeight a y) :
    ∃ z ∈ interior S, eulerHeight a z = c := by
  have hc := hconv.closure_interior_eq_closure_of_nonempty_interior hint
  have hx' : x ∈ closure (interior S) := by rw [hc]; exact subset_closure hx
  have hy' : y ∈ closure (interior S) := by rw [hc]; exact subset_closure hy
  obtain ⟨x',hx'c,hx'S⟩ := mem_closure_iff_nhds.mp hx' {z | eulerHeight a z < c}
    ((isOpen_lt (eulerHeight_continuous a) continuous_const).mem_nhds hxc)
  obtain ⟨y',hy'c,hy'S⟩ := mem_closure_iff_nhds.mp hy' {z | c < eulerHeight a z}
    ((isOpen_lt continuous_const (eulerHeight_continuous a)).mem_nhds hcy)
  let f : ℝ → ℂ := fun t => (1-t) • x' + t • y'
  have hf : Continuous (fun t => eulerHeight a (f t)) := by
    exact (eulerHeight_continuous a).comp (by dsimp [f]; fun_prop)
  have hc' : c ∈ Icc (eulerHeight a (f 0)) (eulerHeight a (f 1)) := by
    simpa [f] using And.intro hx'c.le hy'c.le
  obtain ⟨t,ht,htc⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
    hf.continuousOn hc'
  exact ⟨f t,hconv.interior.segment_subset hx'S hy'S
    ⟨1-t,t,by linarith [ht.2],ht.1,by ring,rfl⟩,htc⟩

namespace Triangle

variable (T : Triangle)

theorem eulerHeight_reconstruct (a : ℝ) (z : ℂ) :
    eulerHeight a z = ∑ i, T.coord i z * eulerHeight a (T.point i) := by
  have h := congrArg (eulerHeightLinear a) (T.reconstruct z)
  simp only [map_sum,map_smul,smul_eq_mul] at h
  exact h.symm

theorem point_not_interior (i : Fin 3) : T.point i ∉ interior T.carrier := by
  intro h
  have h' := (T.mem_interior_iff _).mp h
  fin_cases i
  · simpa using h' 1
  · simpa using h' 0
  · simpa using h' 0

/-- A point on a generic level through a vertex is interior whenever it is
in the triangle, is different from that vertex, and has positive coefficient
at that vertex. The last condition is automatic in a sufficiently small
neighborhood of the vertex. -/
theorem interior_of_generic_level (a : ℝ)
    (hg : Function.Injective (fun i => eulerHeight a (T.point i)))
    (i : Fin 3) {z : ℂ} (hz : z ∈ T.carrier)
    (hle : eulerHeight a z = eulerHeight a (T.point i))
    (hne : z ≠ T.point i) (hci : 0 < T.coord i z) :
    z ∈ interior T.carrier := by
  rw [T.mem_interior_iff]
  intro j
  by_cases hji : j = i
  · simpa [hji] using hci
  · have hex : ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by
      fin_cases i <;> fin_cases j <;> simp_all
      all_goals first | exact ⟨0,by decide,by decide⟩ |
        exact ⟨1,by decide,by decide⟩ | exact ⟨2,by decide,by decide⟩
    obtain ⟨k,hik,hjk⟩ := hex
    have hc := (T.mem_carrier_iff z).mp hz
    apply lt_of_le_of_ne (hc j)
    intro hj0
    have hj : T.coord j z = 0 := hj0.symm
    have hs := T.sum_coord z
    rw [Triangle.sum_three (fun l => T.coord l z) i j k (Ne.symm hji) hik hjk,hj] at hs
    have hh := T.eulerHeight_reconstruct a z
    rw [Triangle.sum_three (fun l => T.coord l z * eulerHeight a (T.point l))
      i j k (Ne.symm hji) hik hjk,hj,hle] at hh
    have he : T.coord k z *
        (eulerHeight a (T.point k)-eulerHeight a (T.point i)) = 0 := by
      linear_combination -hh - eulerHeight a (T.point i) * hs
    have hd : eulerHeight a (T.point k)-eulerHeight a (T.point i) ≠ 0 :=
      sub_ne_zero.mpr (hg.ne hik.symm)
    have hk : T.coord k z = 0 := (mul_eq_zero.mp he).resolve_right hd
    have hi : T.coord i z = 1 := by rw [hk] at hs; linarith
    have hr := T.reconstruct_three z i j k (Ne.symm hji) hik hjk
    apply hne
    simpa [hi,hj,hk] using hr.symm

def IsMiddle (a : ℝ) (i : Fin 3) : Prop :=
  (∃ j, eulerHeight a (T.point j) < eulerHeight a (T.point i)) ∧
  (∃ k, eulerHeight a (T.point i) < eulerHeight a (T.point k))

theorem middle_of_level_interior (a : ℝ)
    (hg : Function.Injective (fun i => eulerHeight a (T.point i)))
    (i : Fin 3) {z : ℂ} (hz : z ∈ interior T.carrier)
    (hle : eulerHeight a z = eulerHeight a (T.point i)) : T.IsMiddle a i := by
  have hc := (T.mem_interior_iff z).mp hz
  have hh := T.eulerHeight_reconstruct a z
  have hs := T.sum_coord z
  have hsum : ∑ j, T.coord j z *
      (eulerHeight a (T.point j)-eulerHeight a (T.point i)) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,← Finset.sum_mul,hs,one_mul,← hh,hle,sub_self]
  have he : ∃ j : Fin 3, j ≠ i := by fin_cases i <;> decide
  obtain ⟨j,hji⟩ := he
  constructor
  · by_contra! h
    have hj : eulerHeight a (T.point i) < eulerHeight a (T.point j) :=
      lt_of_le_of_ne (h j) (hg.ne hji).symm
    have hpos : 0 < ∑ k, T.coord k z *
        (eulerHeight a (T.point k)-eulerHeight a (T.point i)) := by
      apply Finset.sum_pos'
      · intro k _
        exact mul_nonneg (hc k).le (sub_nonneg.mpr (h k))
      · exact ⟨j,Finset.mem_univ _,mul_pos (hc j) (sub_pos.mpr hj)⟩
    linarith
  · by_contra! h
    have hj : eulerHeight a (T.point j) < eulerHeight a (T.point i) :=
      lt_of_le_of_ne (h j) (hg.ne hji)
    have hsum' : ∑ k, T.coord k z *
        (eulerHeight a (T.point i)-eulerHeight a (T.point k)) = 0 := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib,← Finset.sum_mul,hs,one_mul,← hh,hle,sub_self]
    have hpos : 0 < ∑ k, T.coord k z *
        (eulerHeight a (T.point i)-eulerHeight a (T.point k)) := by
      apply Finset.sum_pos'
      · intro k _
        exact mul_nonneg (hc k).le (sub_nonneg.mpr (h k))
      · exact ⟨j,Finset.mem_univ _,mul_pos (hc j) (sub_pos.mpr hj)⟩
    linarith

theorem level_interior_of_middle (a : ℝ) {i : Fin 3} (hi : T.IsMiddle a i) :
    ∃ z ∈ interior T.carrier, eulerHeight a z = eulerHeight a (T.point i) := by
  obtain ⟨⟨j,hj⟩,⟨k,hk⟩⟩ := hi
  exact convex_interior_level_nonempty (convex_convexHull ℝ _) T.interior_nonempty a
    (subset_convexHull ℝ _ (Set.mem_range_self j))
    (subset_convexHull ℝ _ (Set.mem_range_self k)) hj hk

theorem exists_unique_middle (a : ℝ)
    (hg : Function.Injective (fun i => eulerHeight a (T.point i))) :
    ∃! i, T.IsMiddle a i := by
  let f : Fin 3 → ℝ := fun i => eulerHeight a (T.point i)
  have h01 : f 0 ≠ f 1 := hg.ne (by decide)
  have h02 : f 0 ≠ f 2 := hg.ne (by decide)
  have h12 : f 1 ≠ f 2 := hg.ne (by decide)
  have hord : ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ f i < f j ∧ f j < f k := by
    rcases lt_or_gt_of_ne h01 with h01 | h10 <;>
      rcases lt_or_gt_of_ne h02 with h02 | h20 <;>
      rcases lt_or_gt_of_ne h12 with h12 | h21
    all_goals first
      | exact ⟨0,1,2,by decide,by decide,by decide,by assumption,by assumption⟩
      | exact ⟨0,2,1,by decide,by decide,by decide,by assumption,by assumption⟩
      | exact ⟨1,0,2,by decide,by decide,by decide,by assumption,by assumption⟩
      | exact ⟨1,2,0,by decide,by decide,by decide,by assumption,by assumption⟩
      | exact ⟨2,0,1,by decide,by decide,by decide,by assumption,by assumption⟩
      | exact ⟨2,1,0,by decide,by decide,by decide,by assumption,by assumption⟩
      | exfalso; linarith
  obtain ⟨i,j,k,hij,hik,hjk,hij',hjk'⟩ := hord
  have hcover (l : Fin 3) : l = i ∨ l = j ∨ l = k := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp_all
  refine ⟨j,⟨⟨i,hij'⟩,⟨k,hjk'⟩⟩,?_⟩
  intro l hl
  rcases hcover l with rfl | rfl | rfl
  · obtain ⟨x,hx⟩ := hl.1
    rcases hcover x with rfl | rfl | rfl <;> change f _ < f _ at hx <;> linarith
  · rfl
  · obtain ⟨x,hx⟩ := hl.2
    rcases hcover x with rfl | rfl | rfl <;> change f _ < f _ at hx <;> linarith

end Triangle

def eulerRay (a : ℝ) (p : ℂ) (b : Bool) (t : ℝ) : ℂ :=
  p + (if b then t else -t) • eulerDirection a

@[simp] theorem eulerHeight_eulerRay (a : ℝ) (p : ℂ) (b : Bool) (t : ℝ) :
    eulerHeight a (eulerRay a p b t) = eulerHeight a p := by
  exact eulerHeight_ray a _ p

theorem eulerRay_ne (a : ℝ) (p : ℂ) (b : Bool) {t : ℝ} (ht : 0 < t) :
    eulerRay a p b t ≠ p := by
  intro h
  have h' : (if b then t else -t) • eulerDirection a = 0 := by
    exact add_left_cancel (show p + (if b then t else -t) • eulerDirection a = p+0 by
      simpa only [eulerRay,add_zero] using h)
  have hn : (if b then t else -t) ≠ 0 := by cases b <;> simp [ne_of_gt ht]
  exact (smul_eq_zero.mp h').elim hn (eulerDirection_ne_zero a)

namespace Triangle

variable (T : Triangle)

def RayAt (a : ℝ) (i : Fin 3) (b : Bool) : Prop :=
  ∃ t : ℝ, 0 < t ∧ eulerRay a (T.point i) b t ∈ interior T.carrier

theorem coord_eulerRay (a : ℝ) (i j : Fin 3) (b : Bool) (t : ℝ) :
    T.coord j (eulerRay a (T.point i) b t) =
      (if b then t else -t) * (T.coord j).linear (eulerDirection a) +
        if j = i then 1 else 0 := by
  rw [eulerRay,add_comm,← vadd_eq_add,AffineMap.map_vadd]
  simp only [map_smul,vadd_eq_add,smul_eq_mul,T.coord_point]

theorem middle_of_ray (a : ℝ)
    (hg : Function.Injective (fun i => eulerHeight a (T.point i)))
    {i : Fin 3} {b : Bool} (h : T.RayAt a i b) : T.IsMiddle a i := by
  obtain ⟨t,ht,htint⟩ := h
  exact T.middle_of_level_interior a hg i htint (eulerHeight_eulerRay a _ b t)

theorem ray_of_middle (a : ℝ) {i : Fin 3} (hi : T.IsMiddle a i) :
    ∃ b : Bool, T.RayAt a i b := by
  obtain ⟨z,hz,hle⟩ := T.level_interior_of_middle a hi
  have hne : z ≠ T.point i := by
    intro h
    exact T.point_not_interior i (h ▸ hz)
  let t := (T.point i).im-z.im
  have heq : z = T.point i+t • eulerDirection a := eq_ray_of_eulerHeight_eq a hle
  have ht : t ≠ 0 := by intro h; exact hne (by simpa [h] using heq)
  rcases lt_or_gt_of_ne ht with ht | ht
  · refine ⟨false,-t,neg_pos.mpr ht,?_⟩
    simpa only [eulerRay,Bool.false_eq_true,↓reduceIte,neg_neg,← heq] using hz
  · refine ⟨true,t,ht,?_⟩
    simpa only [eulerRay,↓reduceIte,← heq] using hz

theorem ray_unique (a : ℝ) (i : Fin 3) {b c : Bool}
    (hb : T.RayAt a i b) (hc : T.RayAt a i c) : b = c := by
  obtain ⟨t,ht,hbt⟩ := hb
  obtain ⟨s,hs,hcs⟩ := hc
  have hex : ∃ j : Fin 3, j ≠ i := by fin_cases i <;> decide
  obtain ⟨j,hji⟩ := hex
  have hp := (T.mem_interior_iff _).mp hbt j
  have hq := (T.mem_interior_iff _).mp hcs j
  simp only [T.coord_eulerRay] at hp hq
  simp only [hji,ite_false,add_zero] at hp hq
  cases b <;> cases c
  · rfl
  · simp only [Bool.false_eq_true,↓reduceIte] at hp hq
    have hL : 0 < (T.coord j).linear (eulerDirection a) := (mul_pos_iff_of_pos_left hs).mp hq
    have : 0 < t * (T.coord j).linear (eulerDirection a) := mul_pos ht hL
    nlinarith
  · simp only [Bool.false_eq_true,↓reduceIte] at hp hq
    have hL : 0 < (T.coord j).linear (eulerDirection a) := (mul_pos_iff_of_pos_left ht).mp hp
    have : 0 < s * (T.coord j).linear (eulerDirection a) := mul_pos hs hL
    nlinarith
  · rfl

end Triangle

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Triangulation

variable (T : Triangulation V)

def eulerTriangle (s : T.Face) : Triangle :=
  T.drawingTriangle T.point (fun s => T.face_independent s.val s.property) s

theorem eulerTriangle_carrier (s : T.Face) : (T.eulerTriangle s).carrier = T.cell s :=
  T.drawingTriangle_carrier T.point (fun s => T.face_independent s.val s.property) s

def eulerCoord (s : T.Face) (v : s.val) : ℂ →ᵃ[ℝ] ℝ :=
  (T.eulerTriangle s).coord ((T.faceEnumeration s).symm v)

theorem eulerTriangle_point (s : T.Face) (v : s.val) :
    (T.eulerTriangle s).point ((T.faceEnumeration s).symm v) = T.point v.val := by
  change T.point ((T.faceEnumeration s) ((T.faceEnumeration s).symm v)).val = _
  rw [Equiv.apply_symm_apply]

@[simp] theorem eulerCoord_point (s : T.Face) (v w : s.val) :
    T.eulerCoord s v (T.point w.val) = if v = w then 1 else 0 := by
  rw [← T.eulerTriangle_point s w]
  simp [eulerCoord,Triangle.coord_point]

theorem eulerCoord_continuous (s : T.Face) (v : s.val) :
    Continuous (T.eulerCoord s v) := (T.eulerTriangle s).coord_continuous _

theorem eulerCoord_pos_of_interior (s : T.Face) (v : s.val) {z : ℂ}
    (hz : z ∈ interior (T.cell s)) : 0 < T.eulerCoord s v z := by
  rw [← T.eulerTriangle_carrier s] at hz
  exact ((T.eulerTriangle s).mem_interior_iff z).mp hz _

theorem cell_interior_disjoint (s t : T.Face) (hst : s ≠ t) :
    Disjoint (interior (T.cell s)) (T.cell t) := by
  have hsub : ¬ s.val ⊆ t.val := by
    intro h
    apply hst
    exact Subtype.ext (Finset.eq_of_subset_of_card_le h (by
      rw [T.face_card s.val s.property,T.face_card t.val t.property]))
  obtain ⟨v,hvs,hvt⟩ := Finset.not_subset.mp hsub
  let v' : s.val := ⟨v,hvs⟩
  have hzsub : simplex T.point (s.val ∩ t.val) ⊆ {z | T.eulerCoord s v' z = 0} := by
    apply convexHull_min
    · rintro z ⟨w,hw,rfl⟩
      have hws : w ∈ s.val := (Finset.mem_inter.mp hw).1
      have hwt : w ∈ t.val := (Finset.mem_inter.mp hw).2
      have hvw : v' ≠ (⟨w,hws⟩ : s.val) := by
        intro h
        have he : v = w := congrArg Subtype.val h
        apply hvt
        simpa [he] using hwt
      simpa [T.eulerCoord_point s v' ⟨w,hws⟩,hvw]
    · exact (convex_singleton (0 : ℝ)).affine_preimage (T.eulerCoord s v')
  rw [Set.disjoint_left]
  intro z hzs hzt
  have hzi : z ∈ simplex T.point (s.val ∩ t.val) := by
    rw [← T.cell_intersection]
    exact ⟨interior_subset hzs,hzt⟩
  have hp := T.eulerCoord_pos_of_interior s v' hzs
  have hz0 : T.eulerCoord s v' z = 0 := hzsub hzi
  exact (ne_of_gt hp) hz0

theorem eventually_incident_coord (v : V) :
    ∀ᶠ z in 𝓝 (T.point v), ∀ s : T.Face, z ∈ T.cell s →
      ∃ hv : v ∈ s.val, 0 < T.eulerCoord s ⟨v,hv⟩ z := by
  rw [Filter.eventually_all]
  intro s
  by_cases hv : v ∈ s.val
  · have hp : 0 < T.eulerCoord s ⟨v,hv⟩ (T.point v) := by
      rw [T.eulerCoord_point s ⟨v,hv⟩ ⟨v,hv⟩,if_pos rfl]
      norm_num
    have he : ∀ᶠ z in 𝓝 (T.point v), 0 < T.eulerCoord s ⟨v,hv⟩ z :=
      (isOpen_lt continuous_const (T.eulerCoord_continuous s ⟨v,hv⟩)).mem_nhds hp
    filter_upwards [he] with z hz _
    exact ⟨hv,hz⟩
  · have hn : T.point v ∉ T.cell s := by
      exact fun h => hv ((T.point_mem_simplex_iff s.property (Finset.Subset.refl _) v).mp h)
    have he : ∀ᶠ z in 𝓝 (T.point v), z ∉ T.cell s :=
      (T.cell_isCompact s).isClosed.isOpen_compl.mem_nhds hn
    filter_upwards [he] with z hz hzs
    exact False.elim (hz hzs)

theorem eventually_level_interior (a : ℝ)
    (hg : Function.Injective (fun v => eulerHeight a (T.point v))) (v : V) :
    ∀ᶠ z in 𝓝 (T.point v), z ≠ T.point v →
      eulerHeight a z = eulerHeight a (T.point v) →
      ∀ s : T.Face, z ∈ T.cell s → v ∈ s.val ∧ z ∈ interior (T.cell s) := by
  filter_upwards [T.eventually_incident_coord v] with z hz hne hlevel s hzs
  obtain ⟨hvs,hcoord⟩ := hz s hzs
  refine ⟨hvs,?_⟩
  let i := (T.faceEnumeration s).symm ⟨v,hvs⟩
  have hi : (T.eulerTriangle s).point i = T.point v := T.eulerTriangle_point s ⟨v,hvs⟩
  have hg' : Function.Injective (fun j => eulerHeight a ((T.eulerTriangle s).point j)) :=
    hg.comp ((Subtype.val_injective).comp (T.faceEnumeration s).injective)
  rw [← T.eulerTriangle_carrier s]
  apply (T.eulerTriangle s).interior_of_generic_level a hg' i
  · rwa [T.eulerTriangle_carrier]
  · rwa [hi]
  · rwa [hi]
  · exact hcoord

def EulerRayFace (a : ℝ) (v : V) (b : Bool) (s : T.Face) : Prop :=
  v ∈ s.val ∧ ∃ t : ℝ, 0 < t ∧ eulerRay a (T.point v) b t ∈ interior (T.cell s)

theorem eulerRayFace_unique (a : ℝ) (v : V) (b : Bool) {s t : T.Face}
    (hs : T.EulerRayFace a v b s) (ht : T.EulerRayFace a v b t) : s = t := by
  by_contra hst
  obtain ⟨hvs,r,hr,hrs⟩ := hs
  obtain ⟨hvt,u,hu,hut⟩ := ht
  let e := min r u / 2
  have he : 0 < e := half_pos (lt_min hr hu)
  have her : e < r := (half_lt_self (lt_min hr hu)).trans_le (min_le_left _ _)
  have heu : e < u := (half_lt_self (lt_min hr hu)).trans_le (min_le_right _ _)
  have hseg (R : ℝ) (hR : 0 < R) (heR : e < R) :
      eulerRay a (T.point v) b e ∈
        openSegment ℝ (T.point v) (eulerRay a (T.point v) b R) := by
    refine ⟨1-e/R,e/R,sub_pos.mpr ((div_lt_one hR).mpr heR),
      div_pos he hR,by ring,?_⟩
    unfold eulerRay
    cases b <;> simp only [Bool.false_eq_true,↓reduceIte]
    all_goals
      simp only [smul_add,smul_smul,mul_neg,div_mul_cancel₀ _ hR.ne']
      rw [← add_assoc,← add_smul]
      simp
  have hes : eulerRay a (T.point v) b e ∈ interior (T.cell s) :=
    (convex_convexHull ℝ _).openSegment_self_interior_subset_interior
      (T.point_mem_cell s hvs) hrs (hseg r hr her)
  have het : eulerRay a (T.point v) b e ∈ interior (T.cell t) :=
    (convex_convexHull ℝ _).openSegment_self_interior_subset_interior
      (T.point_mem_cell t hvt) hut (hseg u hu heu)
  exact (Set.disjoint_left.mp (T.cell_interior_disjoint s t hst)) hes (interior_subset het)

theorem exists_unique_face_ray (a : ℝ)
    (hg : Function.Injective (fun v => eulerHeight a (T.point v))) (s : T.Face) :
    ∃! p : V × Bool, T.EulerRayFace a p.1 p.2 s := by
  let A := T.eulerTriangle s
  have hcarrier : A.carrier = T.cell s := T.eulerTriangle_carrier s
  have hg' : Function.Injective (fun i => eulerHeight a (A.point i)) :=
    hg.comp ((Subtype.val_injective).comp (T.faceEnumeration s).injective)
  obtain ⟨i,hi,hiunique⟩ := A.exists_unique_middle a hg'
  obtain ⟨b,hb⟩ := A.ray_of_middle a hi
  let v := (T.faceEnumeration s i).val
  have hvi : A.point i = T.point v := rfl
  have hface : T.EulerRayFace a v b s := by
    refine ⟨(T.faceEnumeration s i).property,?_⟩
    obtain ⟨t,ht,hint⟩ := hb
    exact ⟨t,ht,by simpa only [hvi,hcarrier] using hint⟩
  refine ⟨(v,b),hface,?_⟩
  intro p hp
  let j := (T.faceEnumeration s).symm ⟨p.1,hp.1⟩
  have hjp : A.point j = T.point p.1 := T.eulerTriangle_point s ⟨p.1,hp.1⟩
  have hjray : A.RayAt a j p.2 := by
    obtain ⟨t,ht,hint⟩ := hp.2
    exact ⟨t,ht,by simpa only [hjp,hcarrier] using hint⟩
  have hji : j = i := hiunique j (A.middle_of_ray a hg' hjray)
  have hpv : p.1 = v := by
    have he : (T.faceEnumeration s j).val = p.1 := by simp [j]
    rw [hji] at he
    exact he.symm
  have hpb : p.2 = b := A.ray_unique a i (hji ▸ hjray) hb
  exact Prod.ext hpv hpb

end Triangulation

namespace TriangularDisk

variable (D : TriangularDisk V)

/-- The two inward level rays at an interior vertex and the single inward
ray at the middle boundary corner. -/
def EulerPermitted (v : V) (b : Bool) : Prop :=
  v ∉ D.boundary ∨ (v = D.corner 2 ∧ b = true)

theorem eulerRay_tendsto (a : ℝ) (v : V) (b : Bool) :
    Tendsto (fun t : ℝ => eulerRay a (D.point v) b t) (𝓝[>] 0) (𝓝 (D.point v)) := by
  have hc : Continuous (fun t : ℝ => eulerRay a (D.point v) b t) := by
    cases b <;> dsimp [eulerRay] <;> fun_prop
  have hf : Tendsto (fun t : ℝ => eulerRay a (D.point v) b t) (𝓝 (0 : ℝ))
      (𝓝 (eulerRay a (D.point v) b 0)) := hc.continuousAt
  simpa [eulerRay] using hf.mono_left nhdsWithin_le_nhds

theorem permitted_ray_eventually_base (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (v : V) (b : Bool) (hp : D.EulerPermitted v b) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, eulerRay a (D.point v) b t ∈ baseTriangle := by
  rcases hp with hv | ⟨rfl,rfl⟩
  · have hvint : D.point v ∈ interior baseTriangle :=
      mem_interior_baseTriangle_of_coordinates (D.interior_vertex v hv)
    exact (D.eulerRay_tendsto a v b).eventually (mem_interior_iff_mem_nhds.mp hvint)
  · have ht : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
    have ht1all : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), t < 1 :=
      isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) ∈ Set.Iio (1 : ℝ))
    have ht1 : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds ht1all
    filter_upwards [ht,ht1] with t ht ht1
    intro j
    rw [D.corner_point]
    fin_cases j <;> simp [eulerRay,eulerDirection,basePoint,triangleCoordinate]
    · nlinarith [mul_pos ht (sub_pos.mpr ha1)]
    · exact (mul_pos ht ha).le
    · linarith

theorem permitted_of_rayFace (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (v : V) (b : Bool) (s : D.toTriangulation.Face)
    (hs : D.toTriangulation.EulerRayFace a v b s) : D.EulerPermitted v b := by
  by_cases hv : v ∈ D.boundary
  · obtain ⟨j,rfl⟩ := hv
    obtain ⟨_,t,ht,hint⟩ := hs
    have hbase : eulerRay a (D.point (D.corner j)) b t ∈ baseTriangle := by
      rw [← D.domain_eq]
      exact mem_iUnion.mpr ⟨s,interior_subset hint⟩
    rw [D.corner_point] at hbase
    have h0 := hbase 0
    have h1 := hbase 1
    have h2 := hbase 2
    fin_cases j <;> cases b
    all_goals simp [eulerRay,eulerDirection,basePoint,triangleCoordinate] at h0 h1 h2
    · exfalso; nlinarith [mul_pos ht ha]
    · exfalso; linarith
    · exfalso; nlinarith [mul_pos ht (sub_pos.mpr ha1)]
    · exfalso; linarith
    · exfalso; nlinarith [mul_pos ht ha]
    · exact Or.inr ⟨rfl,rfl⟩
  · exact Or.inl hv

theorem exists_unique_rayFace (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hg : Function.Injective (fun v => eulerHeight a (D.point v)))
    (v : V) (b : Bool) (hp : D.EulerPermitted v b) :
    ∃! s : D.toTriangulation.Face, D.toTriangulation.EulerRayFace a v b s := by
  have hbase := D.permitted_ray_eventually_base a ha ha1 v b hp
  have hstar := (D.eulerRay_tendsto a v b).eventually
    (D.toTriangulation.eventually_level_interior a hg v)
  have ht : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t,ht,hbase,hstar⟩ := (ht.and (hbase.and hstar)).exists
  rw [← D.domain_eq] at hbase
  obtain ⟨s,hs⟩ := mem_iUnion.mp hbase
  have hsi := hstar (eulerRay_ne a (D.point v) b ht) (eulerHeight_eulerRay a _ b t) s hs
  refine ⟨s,⟨hsi.1,t,ht,hsi.2⟩,?_⟩
  intro u hu
  exact D.toTriangulation.eulerRayFace_unique a v b hu ⟨hsi.1,t,ht,hsi.2⟩

abbrev EulerSlot := {p : V × Bool // D.EulerPermitted p.1 p.2}

def faceEulerSlotEquiv (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hg : Function.Injective (fun v => eulerHeight a (D.point v))) :
    D.toTriangulation.Face ≃ D.EulerSlot := by
  classical
  let chooseRay (s : D.toTriangulation.Face) : V × Bool :=
    Classical.choose (D.toTriangulation.exists_unique_face_ray a hg s)
  have hchoose (s : D.toTriangulation.Face) :
      D.toTriangulation.EulerRayFace a (chooseRay s).1 (chooseRay s).2 s :=
    (Classical.choose_spec (D.toTriangulation.exists_unique_face_ray a hg s)).1
  let f : D.toTriangulation.Face → D.EulerSlot := fun s =>
    ⟨chooseRay s,D.permitted_of_rayFace a ha ha1 _ _ s (hchoose s)⟩
  apply Equiv.ofBijective f
  constructor
  · intro s t hst
    have he : chooseRay s = chooseRay t := congrArg Subtype.val hst
    apply D.toTriangulation.eulerRayFace_unique a (chooseRay s).1 (chooseRay s).2
      (hchoose s)
    simpa only [he] using hchoose t
  · intro p
    obtain ⟨s,hs,_⟩ := D.exists_unique_rayFace a ha ha1 hg p.val.1 p.val.2 p.property
    refine ⟨s,Subtype.ext ?_⟩
    have hu := (Classical.choose_spec
      (D.toTriangulation.exists_unique_face_ray a hg s)).2 p.val hs
    exact hu.symm

def eulerSlotEquiv : D.EulerSlot ≃ ({v : V // v ∉ D.boundary} × Bool) ⊕ Unit := by
  classical
  refine
    { toFun := fun p => if h : p.val.1 ∉ D.boundary then
        Sum.inl (⟨p.val.1,h⟩,p.val.2) else Sum.inr ()
      invFun := fun q => match q with
        | Sum.inl p => ⟨(p.1.val,p.2),Or.inl p.1.property⟩
        | Sum.inr _ => ⟨(D.corner 2,true),Or.inr ⟨rfl,rfl⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro p
    by_cases hp : p.val.1 ∉ D.boundary
    · simp only [dif_pos hp]
    · simp only [dif_neg hp]
      apply Subtype.ext
      obtain ⟨hv,hb⟩ := p.property.resolve_left hp
      exact Prod.ext hv.symm hb.symm
  · intro q
    rcases q with ⟨v,b⟩ | ⟨⟩
    · simp [v.property]
    · have hc : D.corner 2 ∈ D.boundary := ⟨2,rfl⟩
      simp [hc]

attribute [local instance] Classical.propDecidable

/-- The exact face count for an arbitrary genuine finite triangulation of a
triangle whose only boundary vertices are its three corners. -/
theorem elementary_face_count :
    Fintype.card D.toTriangulation.Face =
      2 * Fintype.card {v : V // v ∉ D.boundary} + 1 := by
  classical
  obtain ⟨a,ha,ha1,hg⟩ := exists_injective_eulerHeight D.point D.point_injective
  calc
    Fintype.card D.toTriangulation.Face = Fintype.card D.EulerSlot :=
      Fintype.card_congr (D.faceEulerSlotEquiv a ha ha1 hg)
    _ = Fintype.card (({v : V // v ∉ D.boundary} × Bool) ⊕ Unit) :=
      Fintype.card_congr D.eulerSlotEquiv
    _ = 2 * Fintype.card {v : V // v ∉ D.boundary} + 1 := by
      simp [Nat.mul_comm]

#print axioms elementary_face_count

end TriangularDisk

end NormalProjective.Planar


end

/-! Read-only actual-body audit; generated from Verify.lean. -/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let localModules : Array Name := #[`planar_tools]
  let moduleOf (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => env.mainModule
  let isLocal (n : Name) : Bool := localModules.contains (moduleOf n)
  let names := env.checked.get.constants.foldStage2
    (fun ns n _ => ns.push n) (#[] : Array Name)
  let names := names.qsort Name.lt
  let mut records : Array Json := #[]
  let mut boundaries : NameSet := {}
  for n in names do
    let some ci := env.find? n | throwError "Missing imported declaration {n}"
    match ci with
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        unless (ci.value? true).isSome do
          throwError "Local proof or definition body unavailable: {n}"
    | .axiomInfo _ => throwError "Local axiom declaration is forbidden: {n}"
    | _ => pure ()
    let axs ← collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved transitive axiom {ax} in {n}"
    let typeDeps := ci.type.getUsedConstants
    let valueDeps := (ci.value? true).map Expr.getUsedConstants |>.getD #[]
    let ctorDeps := match ci with
      | .inductInfo v => v.ctors.toArray
      | _ => #[]
    let deps := (typeDeps ++ valueDeps ++ ctorDeps).foldl (fun s x => s.insert x) ({} : NameSet)
    for d in deps.toArray do
      unless isLocal d do boundaries := boundaries.insert d
    let typeString ← liftTermElabM <| return (← Meta.ppExpr ci.type).pretty
    records := records.push <| Json.mkObj [
      ("name", toJson n.toString), ("module", toJson (moduleOf n).toString),
      ("type", toJson typeString),
      ("proof_or_definition_body_available", toJson (ci.value? true).isSome),
      ("direct_dependencies", toJson (deps.toArray.qsort Name.lt |>.map Name.toString)),
      ("transitive_axioms", toJson (axs.map Name.toString))]
  let mut boundaryRecords : Array Json := #[]
  for n in boundaries.toArray.qsort Name.lt do
    let axs ← collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved library-boundary axiom {ax} in {n}"
    boundaryRecords := boundaryRecords.push <| Json.mkObj [
      ("name", toJson n.toString), ("module", toJson (moduleOf n).toString),
      ("transitive_axioms", toJson (axs.map Name.toString))]
  let result := Json.mkObj [
    ("lean_version", toJson "4.35.0"),
    ("mathlib_commit", toJson "56a005855ea17e0b0958f73ec801ae140b0a1679"),
    ("local_modules", toJson (localModules.map Name.toString)),
    ("local_declarations", Json.arr records),
    ("pinned_library_boundary", Json.arr boundaryRecords),
    ("unapproved_axioms", Json.arr #[])]
  IO.FS.createDirAll ".lake/reports/audit/final"
  IO.FS.writeFile ".lake/reports/audit/final/PlanarTools_dependencies.json" result.pretty
  logInfo m!"Audited {records.size} local declarations and {boundaryRecords.size} pinned-library boundaries."
