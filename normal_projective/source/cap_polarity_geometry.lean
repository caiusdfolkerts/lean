module

public import planar_tools
public import normal_projective.complete
import subfaces
import Mathlib.LinearAlgebra.AffineSpace.Midpoint
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Lean.Elab.Command
import Lean.Meta.Basic
import Lean.Util.CollectAxioms
import Lean.Data.Json.Basic
import Lean.Data.Json.FromToJson.Basic
import Lean.Data.Json.Printer

-- Generated verification output directories.
run_cmd Lean.Elab.Command.liftIO do
  IO.FS.createDirAll ".lake/reports/audit/final"


/-!
# Finite caps, polarity, and the path-to-PN bridge

Generated from exact fragment bodies by `tools/assemble_cap_modules.py`.
Retained-line provenance is recorded in `audit/current/CapPolarityGeometry_source_map.json`.
Only imports, file-wide section headers, and diagnostic commands are consolidated.
The ordinary compiler and axiom-audit records identify the checked source bytes.
-/

@[expose] public section
noncomputable section

/- Source: Cor2Candidate/PolarFinite.lean -/
section
/-!
# Finite polar hulls and their actual supporting faces

The polar is the usual set of pairing inequalities. The bipolar statement is
proved by separation, and a supporting face is identified with the convex hull
of precisely those labelled generators on its supporting hyperplane.
-/

open Set
open scoped BigOperators

namespace NormalProjective.PolarFinite

open CanonicalModel UnitNormalization NormalHull FiniteHullGeometry

variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem hull_iff_polar (v : ι → CanonicalModel.Space d)
    (hz : (0 : CanonicalModel.Space d) ∈ hull v) (y : CanonicalModel.Space d) :
    y ∈ hull v ↔ ∀ x ∈ primal v, dot y x ≤ 1 := by
  constructor
  · intro hy x hx
    exact (primal_iff_hull v x).mp hx y hy
  · intro hy
    by_contra hno
    obtain ⟨u, a, hsep, hay⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ (Set.range v))
      ((Set.finite_range v).isClosed_convexHull ℝ) hno
    have ha : 0 < a := by simpa only [map_zero] using hsep 0 hz
    let x : CanonicalModel.Space d := a⁻¹ • coefficients u
    have hx : x ∈ primal v := by
      intro i
      change rowForm (v i) (a⁻¹ • coefficients u) ≤ 1
      rw [map_smul, smul_eq_mul, rowForm_apply, coefficients_pairing]
      apply (inv_mul_le_iff₀ ha).mpr
      simpa only [mul_one] using
        (hsep (v i) (subset_convexHull ℝ _ ⟨i,rfl⟩)).le
    have hcontra := hy x hx
    change dot y (a⁻¹ • coefficients u) ≤ 1 at hcontra
    have hpair : dot y (a⁻¹ • coefficients u) = a⁻¹ * u y := by
      rw [← rowForm_apply,map_smul,smul_eq_mul,rowForm_apply,coefficients_pairing]
    rw [hpair] at hcontra
    have hu : u y ≤ a := by
      simpa only [mul_one] using (inv_mul_le_iff₀ ha).mp hcontra
    exact (not_le_of_gt hay) hu

/-- It suffices to test the actual extreme points of the compact primal. -/
theorem hull_iff_extreme_pairings (v : ι → CanonicalModel.Space d)
    (hz : (0 : CanonicalModel.Space d) ∈ interior (hull v)) (y : CanonicalModel.Space d) :
    y ∈ hull v ↔ ∀ x ∈ (primal v).extremePoints ℝ, dot y x ≤ 1 := by
  rw [hull_iff_polar v (interior_subset hz)]
  constructor
  · intro hy x hx
    exact hy x hx.1
  · intro hy x hx
    have hc := primal_compact_of_zero_interior v hz
    have heq : primal v = convexHull ℝ ((primal v).extremePoints ℝ) :=
      compact_halfspace_eq_convexHull_extremePoints
        (fun i => (rowForm (v i)).toLinearMap) (fun _ => 1) hc
    have hsub : convexHull ℝ ((primal v).extremePoints ℝ) ⊆
        {z | rowForm y z ≤ 1} := by
      apply convexHull_min
      · intro z hz
        change rowForm y z ≤ 1
        simpa only [rowForm_apply] using hy z hz
      · exact convex_halfSpace_le (rowForm y).toLinearMap.isLinear 1
    have hbound := hsub (heq ▸ hx)
    change rowForm y x ≤ 1 at hbound
    simpa only [rowForm_apply] using hbound

section Faces

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A supporting face of a finite hull is the hull of its tight generators.
In particular, no extra vertices or combinatorial faces enter the definition. -/
theorem supporting_face_eq (v : ι → E) (l : E →ₗ[ℝ] ℝ) (h : ℝ)
    (hle : ∀ i, l (v i) ≤ h) :
    {x ∈ convexHull ℝ (Set.range v) | l x = h} =
      convexHull ℝ (v '' {i | l (v i) = h}) := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨hx, he⟩
    obtain ⟨w, hw, hsum, hcomb⟩ := (mem_hull_iff_weights v x).mp hx
    have htotal : (∑ i, w i * (h - l (v i))) = 0 := by
      calc
        (∑ i, w i * (h - l (v i))) =
            (∑ i, w i) * h - l (∑ i, w i • v i) := by
              simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul,
                map_sum, map_smul, smul_eq_mul]
        _ = 0 := by rw [hsum,hcomb,he]; ring
    have hzero : ∀ i, w i * (h - l (v i)) = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => mul_nonneg (hw j) (sub_nonneg.mpr (hle j)))).mp htotal i
        (Finset.mem_univ i)
    let I : Finset ι := Finset.univ.filter (fun i => l (v i) = h)
    have hwzero : ∀ i, i ∉ I → w i = 0 := by
      intro i hi
      have hne : l (v i) ≠ h := by simpa only [I,Finset.mem_filter,Finset.mem_univ,
        true_and] using hi
      exact (mul_eq_zero.mp (hzero i)).resolve_right (sub_ne_zero.mpr hne.symm)
    have hsumI : (∑ i ∈ I, w i) = 1 := by
      calc
        (∑ i ∈ I, w i) = ∑ i, w i :=
          Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => hwzero i hi)
        _ = 1 := hsum
    have hcombI : (∑ i ∈ I, w i • v i) = x := by
      calc
        (∑ i ∈ I, w i • v i) = ∑ i, w i • v i :=
          Finset.sum_subset (Finset.subset_univ I)
            (fun i _ hi => by rw [hwzero i hi,zero_smul])
        _ = x := hcomb
    rw [← hcombI]
    apply (convex_convexHull ℝ (v '' {i | l (v i) = h})).sum_mem
      (fun i _ => hw i) hsumI
    intro i hi
    exact subset_convexHull ℝ _ ⟨i,(Finset.mem_filter.mp hi).2,rfl⟩
  · apply convexHull_min
    · rintro _ ⟨i,hi,rfl⟩
      exact ⟨subset_convexHull ℝ _ ⟨i,rfl⟩,hi⟩
    · exact (convex_convexHull ℝ (Set.range v)).inter
        (convex_hyperplane l.isLinear h)

/-- The labelled normal generators of a polar face are exactly the primal
facets containing its exposing vertex. -/
theorem normal_hull_face (v : ι → CanonicalModel.Space d) {x : CanonicalModel.Space d} (hx : x ∈ primal v) :
    {y ∈ hull v | dot y x = 1} =
      convexHull ℝ (v '' {i | dot (v i) x = 1}) := by
  have hh := supporting_face_eq v (rowForm x).toLinearMap 1
    (fun i => by
      have hi := hx i
      change rowForm (v i) x ≤ 1 at hi
      change rowForm x (v i) ≤ 1
      rw [rowForm_apply,NormalHull.dot_comm]
      simpa only [rowForm_apply] using hi)
  change {y ∈ hull v | rowForm x y = 1} =
    convexHull ℝ (v '' {i | rowForm x (v i) = 1}) at hh
  simpa only [hull,rowForm_apply,NormalHull.dot_comm] using hh

end Faces
end NormalProjective.PolarFinite
end

/- Source: Cor2Candidate/CapPolytope.lean -/
section
/-!
# The actual convex body below a strictly convex cap

This file supplies the geometric bridge from the cap coordinates to an ordinary
finite convex hull.  In particular, no assertion that the hull is simplicial is
included among the cap assumptions.
-/


open Set Finset
open scoped BigOperators Topology

namespace NormalProjective.Planar

section FiniteFaceCover

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {I : Type*} [Fintype I]

/-- Finitely many individually strict supporting inequalities can be made
simultaneously strict at one point of any nonempty convex set. -/
theorem exists_joint_strict (S : Set E) (hS : Convex ℝ S) (hne : S.Nonempty)
    (l : I → E →ₗ[ℝ] ℝ) (h : I → ℝ)
    (hle : ∀ i x, x ∈ S → l i x ≤ h i)
    (hstrict : ∀ i, ∃ x ∈ S, l i x < h i) :
    ∃ x ∈ S, ∀ i, l i x < h i := by
  classical
  have aux : ∀ t : Finset I, ∃ x ∈ S, ∀ i ∈ t, l i x < h i := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        obtain ⟨x,hx⟩ := hne
        exact ⟨x,hx,by simp⟩
    | @insert i t hit ih =>
        obtain ⟨x,hx,hxt⟩ := ih
        obtain ⟨y,hy,hyi⟩ := hstrict i
        refine ⟨(1/2 : ℝ) • x + (1/2 : ℝ) • y,
          hS hx hy (by norm_num) (by norm_num) (by norm_num), ?_⟩
        intro j hj
        simp only [map_add,map_smul,smul_eq_mul]
        rcases Finset.mem_insert.mp hj with rfl | hj
        · have hxj := hle j x hx
          linarith
        · have hxj := hxt j hj
          have hyj := hle j y hy
          linarith
  obtain ⟨x,hx,hall⟩ := aux Finset.univ
  exact ⟨x,hx,fun i => hall i (Finset.mem_univ i)⟩

/-- If a convex set is covered by finitely many supporting hyperplanes, one
of those hyperplanes contains the whole set.  The proof uses midpoint witnesses
and does not assume a dimension or a face classification. -/
theorem finite_supporting_cover (S : Set E) (hS : Convex ℝ S) (hne : S.Nonempty)
    (l : I → E →ₗ[ℝ] ℝ) (h : I → ℝ)
    (hle : ∀ i x, x ∈ S → l i x ≤ h i)
    (hcover : ∀ x ∈ S, ∃ i, l i x = h i) :
    ∃ i, ∀ x ∈ S, l i x = h i := by
  by_contra! hnot
  have hs : ∀ i, ∃ x ∈ S, l i x < h i := by
    intro i
    obtain ⟨x,hx,hne⟩ := hnot i
    exact ⟨x,hx,lt_of_le_of_ne (hle i x hx) hne⟩
  obtain ⟨x,hx,hstrict⟩ := exists_joint_strict S hS hne l h hle hs
  obtain ⟨i,hi⟩ := hcover x hx
  exact (ne_of_lt (hstrict i)) hi

end FiniteFaceCover

namespace CapCoordinates

abbrev Space := Fin 3 → ℝ

def horizontal : Space →ₗ[ℝ] ℂ where
  toFun x := ⟨x 0,x 1⟩
  map_add' x y := by apply Complex.ext <;> rfl
  map_smul' r x := by apply Complex.ext <;> simp

def lift (p : ℂ) (z : ℝ) : Space := ![p.re,p.im,z]

@[simp] theorem horizontal_lift (p : ℂ) (z : ℝ) : horizontal (lift p z) = p := by
  apply Complex.ext <;> rfl

@[simp] theorem height_lift (p : ℂ) (z : ℝ) : lift p z 2 = z := rfl

theorem lift_horizontal (x : Space) : lift (horizontal x) (x 2) = x := by
  funext j
  fin_cases j <;> rfl

def graphLift (L : ℂ →ᵃ[ℝ] ℝ) : ℂ →ᵃ[ℝ] Space where
  toFun p := lift p (L p)
  linear :=
    { toFun p := lift p (L.linear p)
      map_add' p q := by
        funext j
        fin_cases j <;> simp [lift]
      map_smul' r p := by
        funext j
        fin_cases j
        · simp [lift]
        · simp [lift]
        · change L.linear (r • p) = r • L.linear p
          exact L.linear.map_smul r p }
  map_vadd' p q := by
    funext j
    fin_cases j
    · simp [lift, vadd_eq_add]
    · simp [lift, vadd_eq_add]
    · change L (q +ᵥ p) = L.linear q +ᵥ L p
      exact L.map_vadd p q

def baseLift : ℂ →ᵃ[ℝ] Space := graphLift (AffineMap.const ℝ ℂ (0 : ℝ))

def roofLinear (L : ℂ →ᵃ[ℝ] ℝ) : Space →ₗ[ℝ] ℝ :=
  LinearMap.proj 2 - L.linear.comp horizontal

theorem roofLinear_iff (L : ℂ →ᵃ[ℝ] ℝ) (x : Space) :
    roofLinear L x ≤ L 0 ↔ x 2 ≤ L (horizontal x) := by
  have hL : L (horizontal x) = L.linear (horizontal x) + L 0 := by
    simpa only [vadd_eq_add,add_zero] using L.map_vadd 0 (horizontal x)
  simp only [roofLinear,LinearMap.sub_apply,LinearMap.proj_apply,
    LinearMap.comp_apply]
  constructor <;> intro h <;> linarith

theorem roofLinear_eq_iff (L : ℂ →ᵃ[ℝ] ℝ) (x : Space) :
    roofLinear L x = L 0 ↔ x 2 = L (horizontal x) := by
  have hL : L (horizontal x) = L.linear (horizontal x) + L 0 := by
    simpa only [vadd_eq_add,add_zero] using L.map_vadd 0 (horizontal x)
  simp only [roofLinear,LinearMap.sub_apply,LinearMap.proj_apply,
    LinearMap.comp_apply]
  constructor <;> intro h <;> linarith

end CapCoordinates

namespace StrictConvexCap

open CapCoordinates

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (C : StrictConvexCap V)

@[simp] theorem horizontal_lifted (v : V) : horizontal (C.lifted v) = C.disk.point v := by
  apply Complex.ext <;> rfl

@[simp] theorem height_lifted (v : V) : C.lifted v 2 = C.height v := rfl

theorem lifted_eq (v : V) : C.lifted v = lift (C.disk.point v) (C.height v) := rfl

theorem lifted_mem_carrier (v : V) : C.lifted v ∈ C.carrier :=
  subset_convexHull ℝ _ ⟨v,rfl⟩

theorem carrier_convex : Convex ℝ C.carrier := convex_convexHull ℝ _

theorem horizontal_mem_baseTriangle {x : Space} (hx : x ∈ C.carrier) :
    horizontal x ∈ baseTriangle := by
  apply (convexHull_min ?_ (baseTriangle_convex.linear_preimage horizontal)) hx
  rintro _ ⟨v,rfl⟩
  change horizontal (C.lifted v) ∈ baseTriangle
  rw [horizontal_lifted,← C.disk.domain_eq]
  exact C.disk.toTriangulation.point_mem_domain v

theorem carrier_height_nonnegative {x : Space} (hx : x ∈ C.carrier) : 0 ≤ x 2 := by
  have hsub : C.carrier ⊆ {x : Space | 0 ≤ (LinearMap.proj 2 : Space →ₗ[ℝ] ℝ) x} := by
    apply convexHull_min
    · rintro _ ⟨v,rfl⟩
      exact C.height_nonnegative v
    · exact convex_halfSpace_ge (LinearMap.proj 2 : Space →ₗ[ℝ] ℝ).isLinear 0
  exact hsub hx

theorem carrier_below_roof (s : C.disk.toTriangulation.Face)
    {x : Space} (hx : x ∈ C.carrier) : x 2 ≤ C.roof s (horizontal x) := by
  apply (roofLinear_iff (C.roof s) x).mp
  apply (convexHull_min ?_
    (convex_halfSpace_le (roofLinear (C.roof s)).isLinear (C.roof s 0))) hx
  rintro _ ⟨v,rfl⟩
  change roofLinear (C.roof s) (C.lifted v) ≤ C.roof s 0
  rw [roofLinear_iff,horizontal_lifted,height_lifted]
  by_cases hv : v ∈ s.val
  · exact (C.roof_equal s v hv).symm.le
  · exact (C.roof_strict s v hv).le

theorem roof_point_mem_carrier (s : C.disk.toTriangulation.Face)
    {p : ℂ} (hp : p ∈ C.disk.toTriangulation.cell s) :
    lift p (C.roof s p) ∈ C.carrier := by
  apply (convexHull_min ?_ (C.carrier_convex.affine_preimage (graphLift (C.roof s)))) hp
  rintro _ ⟨v,hv,rfl⟩
  change lift (C.disk.point v) (C.roof s (C.disk.point v)) ∈ C.carrier
  rw [C.roof_equal s v hv]
  exact C.lifted_mem_carrier v

theorem base_point_mem_carrier {p : ℂ} (hp : p ∈ baseTriangle) :
    lift p 0 ∈ C.carrier := by
  rw [baseTriangle_eq_convexHull] at hp
  apply (convexHull_min ?_ (C.carrier_convex.affine_preimage baseLift)) hp
  rintro _ ⟨j,rfl⟩
  change lift (basePoint j) 0 ∈ C.carrier
  rw [← C.disk.corner_point j,← C.boundary_zero j]
  exact C.lifted_mem_carrier (C.disk.corner j)

/-- The finite hull is exactly the region between the triangular base and all
of its supporting roof planes.  This is a set equality in the ambient space. -/
theorem mem_carrier_iff (x : Space) :
    x ∈ C.carrier ↔ horizontal x ∈ baseTriangle ∧ 0 ≤ x 2 ∧
      ∀ s : C.disk.toTriangulation.Face, x 2 ≤ C.roof s (horizontal x) := by
  constructor
  · intro hx
    exact ⟨C.horizontal_mem_baseTriangle hx,C.carrier_height_nonnegative hx,
      fun s => C.carrier_below_roof s hx⟩
  · rintro ⟨hp,hz,hroof⟩
    obtain ⟨s,hs⟩ := Set.mem_iUnion.mp (C.disk.domain_eq.symm ▸ hp)
    have htop := C.roof_point_mem_carrier s hs
    have hbase := C.base_point_mem_carrier hp
    let H := C.roof s (horizontal x)
    have hH : 0 ≤ H := hz.trans (hroof s)
    by_cases hHz : H = 0
    · have hzero : x 2 = 0 := le_antisymm (hHz ▸ hroof s) hz
      simpa only [← hzero,lift_horizontal] using hbase
    · have hHp : 0 < H := lt_of_le_of_ne hH (Ne.symm hHz)
      have hratio0 : 0 ≤ x 2 / H := div_nonneg hz hH
      have hratio1 : x 2 / H ≤ 1 := (div_le_one hHp).mpr (hroof s)
      have hconv := C.carrier_convex hbase htop
        (sub_nonneg.mpr hratio1) hratio0 (by ring : (1-x 2/H)+x 2/H=1)
      have heq : (1-x 2/H) • lift (horizontal x) 0 +
          (x 2/H) • lift (horizontal x) (C.roof s (horizontal x)) = x := by
        funext j
        fin_cases j
        · simp [lift,horizontal] <;> ring
        · simp [lift,horizontal] <;> ring
        · change (1 - x 2 / H) * 0 + (x 2 / H) * H = x 2
          simpa only [mul_zero,zero_add] using div_mul_cancel₀ (x 2) hHz
      exact heq ▸ hconv

theorem interior_of_strict {x : Space}
    (hp : ∀ j, 0 < triangleCoordinate j (horizontal x))
    (hz : 0 < x 2)
    (hr : ∀ s : C.disk.toTriangulation.Face, x 2 < C.roof s (horizontal x)) :
    x ∈ interior C.carrier := by
  have hcH : Continuous (horizontal : Space → ℂ) := horizontal.continuous_of_finiteDimensional
  have hnz : {y : Space | 0 < y 2} ∈ 𝓝 x :=
    (isOpen_lt continuous_const (continuous_apply 2)).mem_nhds hz
  have hnp : {y : Space | ∀ j, 0 < triangleCoordinate j (horizontal y)} ∈ 𝓝 x := by
    apply Filter.eventually_all.mpr
    intro j
    exact (isOpen_lt continuous_const ((coordinate_continuous j).comp hcH)).mem_nhds (hp j)
  have hnr : {y : Space | ∀ s : C.disk.toTriangulation.Face,
      y 2 < C.roof s (horizontal y)} ∈ 𝓝 x := by
    apply Filter.eventually_all.mpr
    intro s
    exact (isOpen_lt (continuous_apply 2)
      ((C.roof s).continuous_of_finiteDimensional.comp hcH)).mem_nhds (hr s)
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hnz,hnp,hnr] with y hyz hyp hyr
  exact (C.mem_carrier_iff y).mpr ⟨fun j => (hyp j).le,hyz.le,fun s => (hyr s).le⟩

/-- With a fixed interior vertex label this center depends continuously on
the cap's point and height coordinates. -/
def centerAt (v : V) : Space := lift (C.disk.point v) (C.height v / 2)

theorem centerAt_interior (v : V) (hv : v ∉ C.disk.boundary) :
    C.centerAt v ∈ interior C.carrier := by
  apply C.interior_of_strict
  · simpa only [centerAt,horizontal_lift] using C.disk.interior_vertex v hv
  · exact half_pos (C.interior_positive v hv)
  · intro s
    have hpos := C.interior_positive v hv
    have hle := C.carrier_below_roof s (C.lifted_mem_carrier v)
    simp only [height_lifted,horizontal_lifted] at hle
    change C.height v / 2 < C.roof s (C.disk.point v)
    linarith

theorem carrier_interior_nonempty : (interior C.carrier).Nonempty := by
  obtain ⟨v,hv⟩ := C.interior_nonempty
  exact ⟨C.centerAt v,C.centerAt_interior v hv⟩

theorem triangleCoordinate_sum (j : Fin 3) (w : V → ℝ) (p : V → ℂ)
    (hw : (∑ v, w v) = 1) :
    triangleCoordinate j (∑ v, w v • p v) =
      ∑ v, w v * triangleCoordinate j (p v) := by
  simp only [coordinate_eq_linear,map_sum,map_smul,smul_eq_mul,mul_sub,
    Finset.sum_sub_distrib,← Finset.sum_mul,hw,one_mul]

/-- Above an edge of the base triangle the cap has height zero.  This is
deduced from its convex-hull coordinates, including the strict positivity of
every interior vertex's three barycentric coordinates. -/
theorem height_zero_of_coordinate_zero {x : Space} (hx : x ∈ C.carrier)
    (j : Fin 3) (hj : triangleCoordinate j (horizontal x) = 0) : x 2 = 0 := by
  obtain ⟨w,hw,hsum,hcomb⟩ :=
    (FiniteHullGeometry.mem_hull_iff_weights C.lifted x).mp hx
  have hhorizontal : (∑ v, w v • C.disk.point v) = horizontal x := by
    simpa only [map_sum,map_smul,horizontal_lifted] using congrArg horizontal hcomb
  have hheight : (∑ v, w v * C.height v) = x 2 := by
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,height_lifted]
      using congrFun hcomb 2
  have hcoord : (∑ v, w v * triangleCoordinate j (C.disk.point v)) = 0 := by
    rw [← triangleCoordinate_sum j w C.disk.point hsum,hhorizontal,hj]
  have hnonneg (v : V) : 0 ≤ triangleCoordinate j (C.disk.point v) := by
    have hv : C.disk.point v ∈ baseTriangle := by
      rw [← C.disk.domain_eq]
      exact C.disk.toTriangulation.point_mem_domain v
    exact hv j
  have hzero (v : V) : w v * triangleCoordinate j (C.disk.point v) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun u _ => mul_nonneg (hw u) (hnonneg u))).mp hcoord v (Finset.mem_univ v)
  have hprod (v : V) : w v * C.height v = 0 := by
    by_cases hv : v ∈ C.disk.boundary
    · obtain ⟨k,rfl⟩ := hv
      simp [C.boundary_zero]
    · have hcv := C.disk.interior_vertex v hv j
      have hwv : w v = 0 := (mul_eq_zero.mp (hzero v)).resolve_right (ne_of_gt hcv)
      rw [hwv,zero_mul]
  rw [← hheight]
  exact Finset.sum_eq_zero (fun v _ => hprod v)

theorem positive_height_horizontal_interior {x : Space} (hx : x ∈ C.carrier)
    (hz : 0 < x 2) : ∀ j, 0 < triangleCoordinate j (horizontal x) := by
  intro j
  apply lt_of_le_of_ne (C.horizontal_mem_baseTriangle hx j)
  intro he
  exact hz.ne' (C.height_zero_of_coordinate_zero hx j he.symm)

/-- Every boundary point belongs to the base plane or a genuine roof plane. -/
theorem frontier_roof_cover {x : Space} (hx : x ∈ frontier C.carrier) :
    x 2 = 0 ∨ ∃ s : C.disk.toTriangulation.Face,
      x 2 = C.roof s (horizontal x) := by
  have hxK : x ∈ C.carrier := C.carrier_compact.isClosed.frontier_subset hx
  by_cases hz : x 2 = 0
  · exact Or.inl hz
  · right
    by_contra! hnot
    have hzp : 0 < x 2 := lt_of_le_of_ne (C.carrier_height_nonnegative hxK) (Ne.symm hz)
    have hp := C.positive_height_horizontal_interior hxK hzp
    have hr (s : C.disk.toTriangulation.Face) :
        x 2 < C.roof s (horizontal x) :=
      lt_of_le_of_ne (C.carrier_below_roof s hxK) (hnot s)
    have hcH : Continuous (horizontal : Space → ℂ) := horizontal.continuous_of_finiteDimensional
    have hnz : {y : Space | 0 < y 2} ∈ 𝓝 x :=
      (isOpen_lt continuous_const (continuous_apply 2)).mem_nhds hzp
    have hnp : {y : Space | ∀ j, 0 < triangleCoordinate j (horizontal y)} ∈ 𝓝 x := by
      apply Filter.eventually_all.mpr
      intro j
      exact (isOpen_lt continuous_const ((coordinate_continuous j).comp hcH)).mem_nhds (hp j)
    have hnr : {y : Space | ∀ s : C.disk.toTriangulation.Face,
        y 2 < C.roof s (horizontal y)} ∈ 𝓝 x := by
      apply Filter.eventually_all.mpr
      intro s
      exact (isOpen_lt (continuous_apply 2)
        ((C.roof s).continuous_of_finiteDimensional.comp hcH)).mem_nhds (hr s)
    have hinter : x ∈ interior C.carrier := by
      apply mem_interior_iff_mem_nhds.mpr
      filter_upwards [hnz,hnp,hnr] with y hyz hyp hyr
      exact (C.mem_carrier_iff y).mpr ⟨fun j => (hyp j).le,hyz.le,fun s => (hyr s).le⟩
    exact hx.2 hinter

def FacetLabel := Option C.disk.toTriangulation.Face

instance : Fintype C.FacetLabel := inferInstanceAs (Fintype (Option C.disk.toTriangulation.Face))

def facetLinear : C.FacetLabel → Space →ₗ[ℝ] ℝ
  | none => -(LinearMap.proj 2)
  | some s => roofLinear (C.roof s)

def facetSupport : C.FacetLabel → ℝ
  | none => 0
  | some s => C.roof s 0

def facetVertices : C.FacetLabel → Finset V
  | none => Finset.univ.image C.disk.corner
  | some s => s.val

theorem facetVertices_card (i : C.FacetLabel) : (C.facetVertices i).card = 3 := by
  cases i with
  | none =>
      rw [facetVertices,Finset.card_image_of_injective _ C.disk.corner.injective] <;> simp
  | some s => exact C.disk.face_card s.val s.property

theorem facet_bound (i : C.FacetLabel) {x : Space} (hx : x ∈ C.carrier) :
    C.facetLinear i x ≤ C.facetSupport i := by
  cases i with
  | none =>
      change -x 2 ≤ 0
      exact neg_nonpos.mpr (C.carrier_height_nonnegative hx)
  | some s =>
      exact (roofLinear_iff (C.roof s) x).mpr (C.carrier_below_roof s hx)

theorem facet_tight_lifted_iff (i : C.FacetLabel) (v : V) :
    C.facetLinear i (C.lifted v) = C.facetSupport i ↔ v ∈ C.facetVertices i := by
  cases i with
  | none =>
      change -C.height v = 0 ↔ v ∈ Finset.univ.image C.disk.corner
      constructor
      · intro h
        have hv : v ∈ C.disk.boundary := by
          by_contra hnot
          have hp := C.interior_positive v hnot
          linarith
        obtain ⟨j,rfl⟩ := hv
        exact Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩
      · intro hv
        obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
        simp [C.boundary_zero]
  | some s =>
      change roofLinear (C.roof s) (C.lifted v) = C.roof s 0 ↔ v ∈ s.val
      rw [roofLinear_eq_iff,horizontal_lifted,height_lifted]
      constructor
      · intro h
        by_contra hv
        exact (ne_of_lt (C.roof_strict s v hv)) h
      · intro hv
        exact (C.roof_equal s v hv).symm

/-- Each displayed roof and the base cuts out exactly the convex hull of its
three labelled vertices. -/
theorem facet_face_eq (i : C.FacetLabel) :
    {x ∈ C.carrier | C.facetLinear i x = C.facetSupport i} =
      convexHull ℝ (C.lifted '' (C.facetVertices i : Set V)) := by
  have hh := PolarFinite.supporting_face_eq C.lifted (C.facetLinear i)
    (C.facetSupport i) (fun v => C.facet_bound i (C.lifted_mem_carrier v))
  have ht : {v | C.facetLinear i (C.lifted v) = C.facetSupport i} =
      (C.facetVertices i : Set V) := by
    ext v
    exact C.facet_tight_lifted_iff i v
  simpa only [ht,carrier] using hh

/-- Any nonempty convex part of the boundary is contained in one of the
displayed triangular faces.  This is the finite-hull face-classification bridge. -/
theorem convex_boundary_subset_facet (S : Set Space) (hS : Convex ℝ S)
    (hne : S.Nonempty) (hboundary : S ⊆ frontier C.carrier) :
    ∃ i : C.FacetLabel,
      S ⊆ convexHull ℝ (C.lifted '' (C.facetVertices i : Set V)) := by
  have hSK : S ⊆ C.carrier :=
    hboundary.trans C.carrier_compact.isClosed.frontier_subset
  obtain ⟨i,hi⟩ := finite_supporting_cover S hS hne C.facetLinear C.facetSupport
    (fun i x hx => C.facet_bound i (hSK hx)) (by
      intro x hx
      rcases C.frontier_roof_cover (hboundary hx) with hz | ⟨s,hs⟩
      · exact ⟨none,by change -x 2 = 0; simpa only [hz,neg_zero]⟩
      · exact ⟨some s,(roofLinear_eq_iff (C.roof s) x).mpr hs⟩)
  refine ⟨i,?_⟩
  rw [← C.facet_face_eq i]
  exact fun x hx => ⟨hSK hx,hi x hx⟩

end StrictConvexCap
end NormalProjective.Planar
end

/- Source: Cor2Candidate/CapPolarity.lean -/
section
/-!
# Polarity of an actual strictly convex cap

The displayed normal vectors are the actual cap vertices translated by an
explicit interior point.  Compactness, irredundancy, and simplicity of the
polar are conclusions, not assumptions on the resulting presentation.
-/


open Set Finset
open scoped BigOperators Topology

namespace NormalProjective.Planar.StrictConvexCap

open CapCoordinates UnitNormalization CanonicalModel NormalHull

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (C : StrictConvexCap V)

def centeredNormal (v₀ v : V) : CapCoordinates.Space := C.lifted v - C.centerAt v₀

theorem centered_hull (v₀ : V) :
    hull (C.centeredNormal v₀) = (fun x : CapCoordinates.Space => x - C.centerAt v₀) '' C.carrier := by
  let a := AffineEquiv.constVAdd ℝ CapCoordinates.Space (-(C.centerAt v₀))
  have hh := a.toAffineMap.image_convexHull (Set.range C.lifted)
  have hr : a.toAffineMap '' Set.range C.lifted = Set.range (C.centeredNormal v₀) := by
    rw [← Set.range_comp']
    congr 1
    funext v
    simp [a,centeredNormal,sub_eq_add_neg,add_comm]
  rw [hr] at hh
  change convexHull ℝ (Set.range (C.centeredNormal v₀)) =
    (fun x : CapCoordinates.Space => x - C.centerAt v₀) '' convexHull ℝ (Set.range C.lifted)
  rw [← hh]
  congr 1
  funext x
  simp [a,sub_eq_add_neg,add_comm]

theorem centered_hull_zero_interior (v₀ : V) (hv₀ : v₀ ∉ C.disk.boundary) :
    (0 : CapCoordinates.Space) ∈ interior (hull (C.centeredNormal v₀)) := by
  rw [C.centered_hull]
  let a := AffineEquiv.constVAdd ℝ CapCoordinates.Space (-(C.centerAt v₀))
  have ha := a.toHomeomorphOfFiniteDimensional.image_interior C.carrier
  have hh : a.toHomeomorphOfFiniteDimensional (C.centerAt v₀) ∈
      a.toHomeomorphOfFiniteDimensional '' interior C.carrier :=
    ⟨C.centerAt v₀,C.centerAt_interior v₀ hv₀,rfl⟩
  rw [ha] at hh
  have he : (a : CapCoordinates.Space → CapCoordinates.Space) =
      fun y => y - C.centerAt v₀ := by
    funext y
    simp [a,sub_eq_add_neg,add_comm]
  simpa only [AffineEquiv.coe_toHomeomorphOfFiniteDimensional,he,sub_self] using hh

/-- Every lifted vertex is absent from the hull of all the other lifted
vertices.  The proof uses a roof face through that vertex and the already
proved exact intersections of subfaces of a genuine planar triangulation. -/
theorem lifted_not_mem_others (v : V) :
    C.lifted v ∉ convexHull ℝ (Set.range (fun w : {w : V // w ≠ v} => C.lifted w.val)) := by
  intro hv
  obtain ⟨s,hs,hvs⟩ := C.disk.vertex_covered v
  let f : C.disk.toTriangulation.Face := ⟨s,hs⟩
  let a : {w : V // w ≠ v} → CapCoordinates.Space := fun w => C.lifted w.val
  have hface := PolarFinite.supporting_face_eq a (C.facetLinear (some f))
    (C.facetSupport (some f)) (fun w => C.facet_bound (some f) (C.lifted_mem_carrier w.val))
  have hvface : C.lifted v ∈
      convexHull ℝ (a '' {w | C.facetLinear (some f) (a w) = C.facetSupport (some f)}) := by
    rw [← hface]
    exact ⟨hv,(C.facet_tight_lifted_iff (some f) v).mpr hvs⟩
  have hsmall : horizontal (C.lifted v) ∈ simplex C.disk.point (s.erase v) := by
    apply (convexHull_min ?_
      ((convex_convexHull ℝ _).linear_preimage horizontal)) hvface
    rintro _ ⟨w,hw,rfl⟩
    change C.disk.point w.val ∈ simplex C.disk.point (s.erase v)
    apply point_mem_simplex
    exact Finset.mem_erase.mpr ⟨w.property,
      (C.facet_tight_lifted_iff (some f) w.val).mp hw⟩
  rw [horizontal_lifted] at hsmall
  have hmem := (C.disk.toTriangulation.point_mem_simplex_iff hs (Finset.erase_subset _ _) v).mp hsmall
  exact (Finset.notMem_erase v s) hmem

include C in
theorem exists_other_vertex (v : V) : ∃ w : V, w ≠ v := by
  by_cases h : C.disk.corner 0 = v
  · refine ⟨C.disk.corner 1,?_⟩
    intro hh
    have he := C.disk.corner.injective (hh.trans h.symm)
    exact (by decide : (1 : Fin 3) ≠ 0) he
  · exact ⟨C.disk.corner 0,h⟩

/-- A genuine strictly exposing functional for each cap vertex. -/
theorem exposing_functional (v : V) :
    ∃ u : CapCoordinates.Space →L[ℝ] ℝ,
      u ≠ 0 ∧ ∀ w, w ≠ v → u (C.lifted w) < u (C.lifted v) := by
  let a : {w : V // w ≠ v} → CapCoordinates.Space := fun w => C.lifted w.val
  obtain ⟨u,b,hbelow,hbv⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (Set.range a))
    ((Set.finite_range a).isClosed_convexHull ℝ) (C.lifted_not_mem_others v)
  have hstrict (w : V) (hw : w ≠ v) : u (C.lifted w) < u (C.lifted v) :=
    (hbelow (a ⟨w,hw⟩) (subset_convexHull ℝ _ ⟨⟨w,hw⟩,rfl⟩)).trans hbv
  refine ⟨u,?_,hstrict⟩
  intro hu
  obtain ⟨w,hw⟩ := C.exists_other_vertex v
  have hh := hstrict w hw
  simpa [hu] using hh

theorem polar_strict_facet_point (v₀ : V) (hv₀ : v₀ ∉ C.disk.boundary) (v : V) :
    ∃ x ∈ primal (C.centeredNormal v₀),
      rowForm (C.centeredNormal v₀ v) x = 1 ∧
        ∀ w, w ≠ v → rowForm (C.centeredNormal v₀ w) x < 1 := by
  obtain ⟨u,hu,hstrict⟩ := C.exposing_functional v
  have hubound : ∀ y ∈ C.carrier, u y ≤ u (C.lifted v) := by
    intro y hy
    apply (convexHull_min ?_ (convex_halfSpace_le u.toLinearMap.isLinear (u (C.lifted v)))) hy
    rintro _ ⟨w,rfl⟩
    by_cases hw : w = v
    · simp [hw]
    · exact (hstrict w hw).le
  have huc : u (C.centerAt v₀) < u (C.lifted v) :=
    interior_lt_support C.carrier u hu _ hubound (C.centerAt_interior v₀ hv₀)
  let r := u (C.lifted v) - u (C.centerAt v₀)
  have hr : 0 < r := sub_pos.mpr huc
  let x : CapCoordinates.Space := r⁻¹ • coefficients u
  have heval (w : V) : rowForm (C.centeredNormal v₀ w) x =
      r⁻¹ * (u (C.lifted w) - u (C.centerAt v₀)) := by
    rw [show x = r⁻¹ • coefficients u from rfl,map_smul,smul_eq_mul,rowForm_apply,
      coefficients_pairing]
    simp only [centeredNormal,map_sub]
  have he : rowForm (C.centeredNormal v₀ v) x = 1 := by
    rw [heval]
    exact inv_mul_cancel₀ hr.ne'
  have hs (w : V) (hw : w ≠ v) : rowForm (C.centeredNormal v₀ w) x < 1 := by
    rw [heval]
    apply (inv_mul_lt_iff₀ hr).mpr
    simpa only [mul_one,r] using sub_lt_sub_right (hstrict w hw) (u (C.centerAt v₀))
  refine ⟨x,?_,he,hs⟩
  intro w
  by_cases hw : w = v
  · subst w
    exact he.le
  · exact (hs w hw).le

def polarRegular (v₀ : V) (hv₀ : v₀ ∉ C.disk.boundary) : RegularData 3 V where
  data := (fun v => rowForm (C.centeredNormal v₀ v),fun _ => 1)
  normal_ne_zero := by
    intro v hn
    change rowForm (C.centeredNormal v₀ v) = 0 at hn
    obtain ⟨x,_,hx,_⟩ := C.polar_strict_facet_point v₀ hv₀ v
    simp only [hn,ContinuousLinearMap.zero_apply] at hx
    exact zero_ne_one hx
  compact := primal_compact_of_zero_interior _ (C.centered_hull_zero_interior v₀ hv₀)
  full_dimensional := ⟨0,primal_zero_interior (C.centeredNormal v₀)⟩
  strict_facet_point := C.polar_strict_facet_point v₀ hv₀

@[simp] theorem polarRegular_data (v₀ : V) (hv₀ : v₀ ∉ C.disk.boundary) :
    (C.polarRegular v₀ hv₀).data =
      (fun v => rowForm (C.centeredNormal v₀ v),fun _ => 1) := rfl

theorem centered_pairing (v₀ v : V) (x : CapCoordinates.Space) :
    rowForm (C.centeredNormal v₀ v) x =
      rowForm x (C.lifted v) - rowForm x (C.centerAt v₀) := by
  calc
    rowForm (C.centeredNormal v₀ v) x = rowForm x (C.centeredNormal v₀ v) := by
      simp only [rowForm_apply,NormalHull.dot_comm]
    _ = rowForm x (C.lifted v) - rowForm x (C.centerAt v₀) := map_sub _ _ _

/-- The active facets at an arbitrary polar vertex are exactly one of the
original cap triangles or the base triangle. -/
theorem polar_vertex_pattern (v₀ : V) (hv₀ : v₀ ∉ C.disk.boundary)
    {x : CapCoordinates.Space} (hx : x ∈ (primal (C.centeredNormal v₀)).extremePoints ℝ) :
    ∃ i : C.FacetLabel, ∀ v,
      rowForm (C.centeredNormal v₀ v) x = 1 ↔ v ∈ C.facetVertices i := by
  classical
  let f := fun v => (rowForm (C.centeredNormal v₀ v)).toLinearMap
  obtain ⟨I,hI,_⟩ := extremePoint_has_active_basis f (fun _ => 1) hx
  have hxne : x ≠ 0 := by
    intro hh
    have hi := hI 0
    simp only [hh,map_zero] at hi
    exact zero_ne_one hi
  have hrow : rowForm x ≠ 0 := by
    intro hh
    have hc := congrArg coefficients hh
    exact hxne (by simpa only [coefficients_rowForm,coefficients_zero] using hc)
  let b := 1 + rowForm x (C.centerAt v₀)
  have hbound : ∀ y ∈ C.carrier, rowForm x y ≤ b := by
    intro y hy
    apply (convexHull_min ?_ (convex_halfSpace_le (rowForm x).toLinearMap.isLinear b)) hy
    rintro _ ⟨v,rfl⟩
    have hh := hx.1 v
    change rowForm (C.centeredNormal v₀ v) x ≤ 1 at hh
    rw [C.centered_pairing] at hh
    change rowForm x (C.lifted v) ≤ b
    dsimp [b]
    linarith
  let F : Set CapCoordinates.Space := {y ∈ C.carrier | rowForm x y = b}
  have hFconv : Convex ℝ F := C.carrier_convex.inter
    (convex_hyperplane (rowForm x).toLinearMap.isLinear b)
  have hFne : F.Nonempty := by
    refine ⟨C.lifted (I 0),C.lifted_mem_carrier _,?_⟩
    have hh := hI 0
    change rowForm (C.centeredNormal v₀ (I 0)) x = 1 at hh
    rw [C.centered_pairing] at hh
    dsimp [b]
    linarith
  have hFboundary : F ⊆ frontier C.carrier := by
    intro y hy
    refine ⟨subset_closure hy.1,?_⟩
    intro hyint
    have hh := interior_lt_support C.carrier (rowForm x) hrow b hbound hyint
    exact (ne_of_lt hh) hy.2
  obtain ⟨i,hi⟩ := C.convex_boundary_subset_facet F hFconv hFne hFboundary
  have hsub (v : V) (hv : rowForm (C.centeredNormal v₀ v) x = 1) :
      v ∈ C.facetVertices i := by
    have hvF : C.lifted v ∈ F := by
      refine ⟨C.lifted_mem_carrier v,?_⟩
      rw [C.centered_pairing] at hv
      dsimp [b]
      linarith
    have hm := hi hvF
    rw [← C.facet_face_eq i] at hm
    exact (C.facet_tight_lifted_iff i v).mp hm.2
  let A : Finset V := Finset.univ.filter (fun v => rowForm (C.centeredNormal v₀ v) x = 1)
  have hAF : A ⊆ C.facetVertices i := by
    intro v hv
    exact hsub v (Finset.mem_filter.mp hv).2
  have hIA : Finset.univ.image I ⊆ A := by
    intro v hv
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hI j⟩
  have hcard : 3 ≤ A.card := by
    have hh := Finset.card_le_card hIA
    simpa only [Finset.card_image_of_injective _ I.injective,Finset.card_univ,Fintype.card_fin] using hh
  have hEq : A = C.facetVertices i := Finset.eq_of_subset_of_card_le hAF (by
    rw [C.facetVertices_card]
    exact hcard)
  refine ⟨i,fun v => ?_⟩
  change rowForm (C.centeredNormal v₀ v) x = 1 ↔ v ∈ C.facetVertices i
  rw [← hEq]
  simp only [A,Finset.mem_filter,Finset.mem_univ,true_and]

/-- The polar of every strictly convex triangulated cap is simple. -/
theorem polar_simple (v₀ : V) (hv₀ : v₀ ∉ C.disk.boundary) :
    IsSimpleHalfspace
      (fun v => (rowForm (C.centeredNormal v₀ v)).toLinearMap) (fun _ => 1) := by
  intro x hx
  obtain ⟨i,hi⟩ := C.polar_vertex_pattern v₀ hv₀ hx
  have he : ActiveFacet (fun v => (rowForm (C.centeredNormal v₀ v)).toLinearMap)
      (fun _ => 1) x ≃ {v : V // v ∈ C.facetVertices i} :=
    Equiv.subtypeEquivRight hi
  rw [Nat.card_congr he]
  simp only [Nat.card_eq_fintype_card,Fintype.card_coe,C.facetVertices_card]

theorem facetLinear_nonzero (i : C.FacetLabel) : C.facetLinear i ≠ 0 := by
  intro hh
  have he := congrArg (fun l : CapCoordinates.Space →ₗ[ℝ] ℝ => l (Pi.single 2 1)) hh
  cases i with
  | none => simpa [facetLinear] using he
  | some s =>
      have hz : horizontal (Pi.single (2 : Fin 3) (1 : ℝ)) = 0 := by
        apply Complex.ext <;> simp [horizontal,Pi.single_apply]
      simp only [facetLinear,roofLinear,LinearMap.sub_apply,LinearMap.proj_apply,
        Pi.single_eq_same,LinearMap.comp_apply,hz,map_zero,sub_zero,
        LinearMap.zero_apply] at he
      exact one_ne_zero he

/-- Each actual triangular cap facet produces a polar vertex, with exactly
the intended three incidences. -/
theorem exists_polar_vertex_for_facet (v₀ : V) (hv₀ : v₀ ∉ C.disk.boundary)
    (i : C.FacetLabel) :
    ∃ x : CapCoordinates.Space,
      x ∈ (primal (C.centeredNormal v₀)).extremePoints ℝ ∧
        ∀ v, rowForm (C.centeredNormal v₀ v) x = 1 ↔ v ∈ C.facetVertices i := by
  classical
  let u := (C.facetLinear i).toContinuousLinearMap
  have hu : u ≠ 0 := by
    intro hh
    apply C.facetLinear_nonzero i
    exact congrArg ContinuousLinearMap.toLinearMap hh
  have huc : u (C.centerAt v₀) < C.facetSupport i :=
    interior_lt_support C.carrier u hu _
      (fun y hy => C.facet_bound i hy) (C.centerAt_interior v₀ hv₀)
  let r := C.facetSupport i - u (C.centerAt v₀)
  have hr : 0 < r := sub_pos.mpr huc
  let x : CapCoordinates.Space := r⁻¹ • coefficients u
  have heval (v : V) : rowForm (C.centeredNormal v₀ v) x =
      r⁻¹ * (u (C.lifted v) - u (C.centerAt v₀)) := by
    rw [show x = r⁻¹ • coefficients u from rfl,map_smul,smul_eq_mul,rowForm_apply,
      coefficients_pairing]
    simp only [centeredNormal,map_sub]
  have hx : x ∈ primal (C.centeredNormal v₀) := by
    intro v
    change rowForm (C.centeredNormal v₀ v) x ≤ 1
    rw [heval]
    apply (inv_mul_le_iff₀ hr).mpr
    have hh := C.facet_bound i (C.lifted_mem_carrier v)
    change u (C.lifted v) ≤ C.facetSupport i at hh
    dsimp [r]
    linarith
  have hactive (v : V) : rowForm (C.centeredNormal v₀ v) x = 1 ↔ v ∈ C.facetVertices i := by
    rw [heval,inv_mul_eq_iff_eq_mul₀ hr.ne']
    have heq : u (C.lifted v) - u (C.centerAt v₀) = r * 1 ↔
        C.facetLinear i (C.lifted v) = C.facetSupport i := by
      dsimp [r,u]
      constructor <;> intro h <;> linarith
    rw [heq,C.facet_tight_lifted_iff]
  have hcard : Fintype.card {v : V // v ∈ C.facetVertices i} = 3 := by
    simpa only [Fintype.card_coe] using C.facetVertices_card i
  let e : {v : V // v ∈ C.facetVertices i} ≃ Fin 3 :=
    (Fintype.equivFin _).trans (finCongr hcard)
  let I : Fin 3 ↪ V := ⟨fun j => (e.symm j).val,
    fun a b hab => e.symm.injective (Subtype.ext hab)⟩
  have hI : ∀ j, rowForm (C.centeredNormal v₀ (I j)) x = 1 := by
    intro j
    exact (hactive (I j)).mpr (e.symm j).property
  have hver := simple_feasible_minor
    (fun v => (rowForm (C.centeredNormal v₀ v)).toLinearMap) (fun _ => 1)
    (C.polarRegular v₀ hv₀).compact (C.polar_simple v₀ hv₀) I hx hI
  exact ⟨x,hver.1,hactive⟩

end NormalProjective.Planar.StrictConvexCap
end

/- Source: Cor2Candidate/CapPathBridge.lean -/
section
/-!
# From paths of genuine caps to normal--projective equivalence

The affine quotient and PN words here are the canonical geometric definitions
used for the paper's component theorem.  No statement of connectedness is an
assumption on the polytope type.
-/


open Set Filter
open scoped Topology

namespace NormalProjective

open UnitNormalization CanonicalModel

section Incidence

variable {d : ℕ} {V : Type*} [Fintype V]

/-- Two ordinary finite halfspace presentations have the same labelled face
lattice when each actual vertex incidence pattern occurs in both of them. -/
theorem sameLabelledType_of_mutual_vertex_patterns (p q : RegularData d V)
    (hpq : ∀ x : HalfspaceVertices (fun v => (p.data.1 v).toLinearMap) p.data.2,
      ∃ y : HalfspaceVertices (fun v => (q.data.1 v).toLinearMap) q.data.2,
        ∀ v, p.data.1 v x.val = p.data.2 v ↔ q.data.1 v y.val = q.data.2 v)
    (hqp : ∀ y : HalfspaceVertices (fun v => (q.data.1 v).toLinearMap) q.data.2,
      ∃ x : HalfspaceVertices (fun v => (p.data.1 v).toLinearMap) p.data.2,
        ∀ v, q.data.1 v y.val = q.data.2 v ↔ p.data.1 v x.val = p.data.2 v) :
    (presentation p).SameLabelledType (presentation q) := by
  classical
  let f := fun v => (p.data.1 v).toLinearMap
  let g := fun v => (q.data.1 v).toLinearMap
  let φ : HalfspaceVertices f p.data.2 → HalfspaceVertices g q.data.2 :=
    fun x => (hpq x).choose
  have hφ (x : HalfspaceVertices f p.data.2) (v : V) :
      f v x.val = p.data.2 v ↔ g v (φ x).val = q.data.2 v := (hpq x).choose_spec v
  have hinj : Function.Injective φ := by
    intro x y hxy
    apply extreme_activeFacetSet_injective f p.data.2
    ext v
    change f v x.val = p.data.2 v ↔ f v y.val = p.data.2 v
    exact (hφ x v).trans (by simpa only [hxy] using (hφ y v).symm)
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x,hx⟩ := hqp y
    refine ⟨x,?_⟩
    apply extreme_activeFacetSet_injective g q.data.2
    ext v
    change g v (φ x).val = q.data.2 v ↔ g v y.val = q.data.2 v
    exact (hφ x v).symm.trans (hx v).symm
  let e := Equiv.ofBijective φ ⟨hinj,hsurj⟩
  have he (x : HalfspaceVertices f p.data.2) (v : V) :
      f v x.val = p.data.2 v ↔ g v (e x).val = q.data.2 v := hφ x v
  apply sameLabelledType_of_faceOrderIso p q
    (halfspaceFaceOrderIso f g p.data.2 q.data.2 p.compact q.compact e he)
  exact fun v => halfspaceFaceOrderIso_facet _ _ _ _ _ _ _ _ v

end Incidence

namespace Planar.StrictConvexCap

open CapCoordinates CanonicalModel.Realization

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {C D : StrictConvexCap V}

theorem SameCombinatorics.symm (h : C.SameCombinatorics D) : D.SameCombinatorics C :=
  ⟨h.1.symm,h.2.symm⟩

theorem SameCombinatorics.trans {E : StrictConvexCap V}
    (hCD : C.SameCombinatorics D) (hDE : D.SameCombinatorics E) : C.SameCombinatorics E :=
  ⟨hCD.1.trans hDE.1,hCD.2.trans hDE.2⟩

theorem SameCombinatorics.boundary_eq (h : C.SameCombinatorics D) :
    C.disk.boundary = D.disk.boundary := by
  change Set.range C.disk.corner = Set.range D.disk.corner
  rw [h.2]

theorem SameCombinatorics.facet_pattern (h : C.SameCombinatorics D) (i : C.FacetLabel) :
    ∃ j : D.FacetLabel, C.facetVertices i = D.facetVertices j := by
  cases i with
  | none =>
      refine ⟨none,?_⟩
      change Finset.univ.image C.disk.corner = Finset.univ.image D.disk.corner
      rw [h.2]
  | some s =>
      have hs : s.val ∈ D.disk.faces := h.1 ▸ s.property
      exact ⟨some ⟨s.val,hs⟩,rfl⟩

theorem SameCombinatorics.polar_vertex_patterns (h : C.SameCombinatorics D)
    (v₀ : V) (hvC : v₀ ∉ C.disk.boundary) (hvD : v₀ ∉ D.disk.boundary)
    (x : HalfspaceVertices
      (fun v => (rowForm (C.centeredNormal v₀ v)).toLinearMap) (fun _ => 1)) :
    ∃ y : HalfspaceVertices
        (fun v => (rowForm (D.centeredNormal v₀ v)).toLinearMap) (fun _ => 1),
      ∀ v, rowForm (C.centeredNormal v₀ v) x.val = 1 ↔
        rowForm (D.centeredNormal v₀ v) y.val = 1 := by
  obtain ⟨i,hi⟩ := C.polar_vertex_pattern v₀ hvC x.property
  obtain ⟨j,hij⟩ := h.facet_pattern i
  obtain ⟨y,hy,hinc⟩ := D.exists_polar_vertex_for_facet v₀ hvD j
  refine ⟨⟨y,hy⟩,fun v => ?_⟩
  rw [hi,hinc,hij]

/-- Polarity translates cap combinatorics into the actual labelled face
lattice of the original simple polytope. -/
theorem SameCombinatorics.polar_sameLabelledType (h : C.SameCombinatorics D)
    (v₀ : V) (hvC : v₀ ∉ C.disk.boundary) (hvD : v₀ ∉ D.disk.boundary) :
    (presentation (C.polarRegular v₀ hvC)).SameLabelledType
      (presentation (D.polarRegular v₀ hvD)) := by
  apply sameLabelledType_of_mutual_vertex_patterns (C.polarRegular v₀ hvC) (D.polarRegular v₀ hvD)
  · exact h.polar_vertex_patterns v₀ hvC hvD
  · exact h.symm.polar_vertex_patterns v₀ hvD hvC

theorem polar_presentation_simple (C : StrictConvexCap V)
    (v₀ : V) (hv₀ : v₀ ∉ C.disk.boundary) :
    (presentation (C.polarRegular v₀ hv₀)).Simple :=
  (simple_iff_raw (C.polarRegular v₀ hv₀)).mpr (C.polar_simple v₀ hv₀)

theorem continuous_coordinates :
    Continuous (fun C : StrictConvexCap V => (C.disk.point,C.height)) :=
  continuous_induced_dom

theorem continuous_lifted (v : V) :
    Continuous (fun C : StrictConvexCap V => C.lifted v) := by
  have hp : Continuous (fun C : StrictConvexCap V => C.disk.point v) :=
    (continuous_apply v).comp continuous_coordinates.fst
  have hh : Continuous (fun C : StrictConvexCap V => C.height v) :=
    (continuous_apply v).comp continuous_coordinates.snd
  apply continuous_pi
  intro j
  fin_cases j
  · exact Complex.continuous_re.comp hp
  · exact Complex.continuous_im.comp hp
  · exact hh

theorem continuous_centerAt (v : V) :
    Continuous (fun C : StrictConvexCap V => C.centerAt v) := by
  have hp : Continuous (fun C : StrictConvexCap V => C.disk.point v) :=
    (continuous_apply v).comp continuous_coordinates.fst
  have hh : Continuous (fun C : StrictConvexCap V => C.height v) :=
    (continuous_apply v).comp continuous_coordinates.snd
  apply continuous_pi
  intro j
  fin_cases j
  · exact Complex.continuous_re.comp hp
  · exact Complex.continuous_im.comp hp
  · exact hh.div_const 2

theorem continuous_centeredNormal (v₀ v : V) :
    Continuous (fun C : StrictConvexCap V => C.centeredNormal v₀ v) :=
  (continuous_lifted v).sub (continuous_centerAt v₀)

abbrev FixedCombinatorics (C : StrictConvexCap V) :=
  {D : StrictConvexCap V // C.SameCombinatorics D}

def fixedPolarRegular (C : StrictConvexCap V) (v₀ : V)
    (hv₀ : v₀ ∉ C.disk.boundary) (D : FixedCombinatorics C) : RegularData 3 V :=
  D.val.polarRegular v₀ (by rw [← D.property.boundary_eq]; exact hv₀)

theorem continuous_fixedPolarRegular (C : StrictConvexCap V) (v₀ : V)
    (hv₀ : v₀ ∉ C.disk.boundary) : Continuous (fixedPolarRegular C v₀ hv₀) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun D : FixedCombinatorics C =>
    (fun v => rowForm (D.val.centeredNormal v₀ v),fun _ : V => (1 : ℝ)))
  apply Continuous.prodMk _ continuous_const
  apply continuous_pi
  intro v
  exact continuous_rowForm.comp
    ((continuous_centeredNormal v₀ v).comp continuous_subtype_val)

def fixedPolarRealization (C : StrictConvexCap V) (v₀ : V)
    (hv₀ : v₀ ∉ C.disk.boundary) (D : FixedCombinatorics C) :
    Realization (presentation (C.polarRegular v₀ hv₀)) :=
  ⟨presentation (fixedPolarRegular C v₀ hv₀ D),
    D.property.polar_sameLabelledType v₀ hv₀
      (by rw [← D.property.boundary_eq]; exact hv₀)⟩

theorem continuous_fixedPolarRealization (C : StrictConvexCap V) (v₀ : V)
    (hv₀ : v₀ ∉ C.disk.boundary) : Continuous (fixedPolarRealization C v₀ hv₀) := by
  apply Continuous.subtype_mk
  exact continuous_presentation.comp (continuous_fixedPolarRegular C v₀ hv₀)

/-- A path of actual caps with unchanged labelled triangulation gives a path
of actual simple polar realizations.  The already verified component theorem
then supplies a finite word of genuine normal/projective transformations. -/
theorem pnRelated_of_cap_path (C D : StrictConvexCap V) (v₀ : V)
    (hv₀ : v₀ ∉ C.disk.boundary) (hCD : C.SameCombinatorics D)
    (γ : Path C D) (hγ : ∀ t, C.SameCombinatorics (γ t)) :
    PNRelated
      (fixedPolarRealization C v₀ hv₀ ⟨C,⟨rfl,rfl⟩⟩)
      (fixedPolarRealization C v₀ hv₀ ⟨D,hCD⟩) := by
  let P := fixedPolarRealization C v₀ hv₀
  let q : unitInterval → FixedCombinatorics C := fun t => ⟨γ t,hγ t⟩
  have hq : Continuous q := γ.continuous.subtype_mk _
  let δ : Path (P ⟨C,⟨rfl,rfl⟩⟩) (P ⟨D,hCD⟩) :=
    { toFun := fun t => P (q t)
      continuous_toFun := (continuous_fixedPolarRealization C v₀ hv₀).comp hq
      source' := by
        have h : q 0 = ⟨C,⟨rfl,rfl⟩⟩ := Subtype.ext γ.source
        exact congrArg P h
      target' := by
        have h : q 1 = ⟨D,hCD⟩ := Subtype.ext γ.target
        exact congrArg P h }
  apply (pnRelated_iff_same_component (C.polar_presentation_simple v₀ hv₀) _ _).mpr
  exact pathComponent_subset_component _
    ((show Joined _ _ from ⟨δ⟩).map continuous_affineClass)

end Planar.StrictConvexCap
end NormalProjective
end

/- Source: Cor2Candidate/CapSourceDual.lean -/
section
/-!
# The finite polar of an arbitrary simple input polytope

This construction starts from the manuscript's normalized facet presentation.
The polar's supporting planes are indexed by the actual vertices of the input.
Their irredundancy and their triangular vertex sets are proved directly.
-/

open Set Finset
open scoped BigOperators Topology

namespace NormalProjective.CapSource

open CanonicalModel UnitNormalization NormalHull

abbrev Space := Fin 3 → ℝ

variable {V : Type*} [Fintype V]

def normals (p : RegularData 3 V) : V → Space := fun v => coefficients (p.data.1 v)

abbrev Vertices (p : RegularData 3 V) :=
  HalfspaceVertices (fun v => (p.data.1 v).toLinearMap) p.data.2

instance verticesFinite (p : RegularData 3 V) : Finite (Vertices p) :=
  (halfspace_extremePoints_finite (fun v => (p.data.1 v).toLinearMap) p.data.2).to_subtype

instance verticesFintype (p : RegularData 3 V) : Fintype (Vertices p) := Fintype.ofFinite _

theorem vertices_nonempty (p : RegularData 3 V) : Nonempty (Vertices p) := by
  obtain ⟨x,hx⟩ := p.compact.extremePoints_nonempty (p.full_dimensional.mono interior_subset)
  exact ⟨⟨x,hx⟩⟩

theorem labels_nonempty (p : RegularData 3 V) : Nonempty V := by
  obtain ⟨x⟩ := vertices_nonempty p
  obtain ⟨I,_,_⟩ := extremePoint_has_active_basis
    (fun v => (p.data.1 v).toLinearMap) p.data.2 x.property
  exact ⟨I 0⟩

theorem rowForm_coefficients (u : Space →L[ℝ] ℝ) : rowForm (coefficients u) = u := by
  ext x
  rw [rowForm_apply]
  exact coefficient_expansion u x

theorem primal_normals (p : RegularData 3 V) (hp : ∀ v, p.data.2 v = 1) :
    primal (normals p) = dataRegion p.data := by
  ext x
  change (∀ v, rowForm (normals p v) x ≤ 1) ↔ ∀ v, p.data.1 v x ≤ p.data.2 v
  simp only [normals,rowForm_coefficients,hp]

theorem normals_zero_interior (p : RegularData 3 V) (hp : ∀ v, p.data.2 v = 1) :
    (0 : Space) ∈ interior (hull (normals p)) := by
  letI : Nonempty V := labels_nonempty p
  apply zero_interior_of_primal_bounded (by decide)
  rw [primal_normals p hp]
  exact p.compact.isBounded

theorem vertex_ne_zero (p : RegularData 3 V) (hp : ∀ v, p.data.2 v = 1) (x : Vertices p) :
    x.val ≠ 0 := by
  obtain ⟨I,hI,_⟩ := extremePoint_has_active_basis
    (fun v => (p.data.1 v).toLinearMap) p.data.2 x.property
  intro hx
  have hh := hI 0
  simp only [hx,map_zero,hp] at hh
  exact zero_ne_one hh

def dualData (p : RegularData 3 V) : HalfspaceData (Vertices p) Space :=
  (fun x => rowForm x.val,fun _ => 1)

theorem dual_region (p : RegularData 3 V) (hp : ∀ v, p.data.2 v = 1) :
    dataRegion (dualData p) = hull (normals p) := by
  ext y
  rw [PolarFinite.hull_iff_extreme_pairings (normals p) (normals_zero_interior p hp),
    primal_normals p hp]
  change (∀ x : Vertices p, rowForm x.val y ≤ 1) ↔
    ∀ x ∈ (dataRegion p.data).extremePoints ℝ, dot y x ≤ 1
  constructor
  · intro h x hx
    simpa only [rowForm_apply,NormalHull.dot_comm] using h ⟨x,hx⟩
  · intro h x
    simpa only [rowForm_apply,NormalHull.dot_comm] using h x.val x.property

theorem dual_strict_facet_point (p : RegularData 3 V)
    (hp : ∀ v, p.data.2 v = 1) (x : Vertices p) :
    ∃ y ∈ dataRegion (dualData p), rowForm x.val y = 1 ∧
      ∀ z : Vertices p, z ≠ x → rowForm z.val y < 1 := by
  classical
  let f := fun v => (p.data.1 v).toLinearMap
  obtain ⟨I,hI,hind⟩ := extremePoint_has_active_basis f p.data.2 x.property
  have hdet := facetCoefficientMatrix_det_ne_zero (fun j => f (I j)) hind
  let y : Space := (1/3 : ℝ) • ∑ j : Fin 3, normals p (I j)
  have heval (z : Vertices p) : rowForm z.val y =
      (1/3 : ℝ) * ∑ j : Fin 3, p.data.1 (I j) z.val := by
    simp only [y,map_smul,map_sum,smul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [rowForm_apply,NormalHull.dot_comm,← rowForm_apply]
    exact congrArg (fun u : Space →L[ℝ] ℝ => u z.val) (rowForm_coefficients (p.data.1 (I j)))
  have hle (z : Vertices p) (j : Fin 3) : p.data.1 (I j) z.val ≤ 1 := by
    have hz := z.property.1 (I j)
    change p.data.1 (I j) z.val ≤ p.data.2 (I j) at hz
    exact hz.trans_eq (hp (I j))
  have he : rowForm x.val y = 1 := by
    rw [heval]
    have hh (j : Fin 3) : p.data.1 (I j) x.val = 1 := by
      have hj := hI j
      change p.data.1 (I j) x.val = p.data.2 (I j) at hj
      exact hj.trans (hp (I j))
    simp only [hh,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    norm_num
  have hstrict (z : Vertices p) (hz : z ≠ x) : rowForm z.val y < 1 := by
    have hex : ∃ j : Fin 3, p.data.1 (I j) z.val < 1 := by
      by_contra! hall
      apply hz
      apply Subtype.ext
      apply tight_minor_unique f p.data.2 I hdet
      · intro j
        exact (le_antisymm (hle z j) (hall j)).trans (hp (I j)).symm
      · exact hI
    obtain ⟨j,hj⟩ := hex
    have hsum : (∑ k : Fin 3, p.data.1 (I k) z.val) < ∑ _ : Fin 3, (1 : ℝ) :=
      Finset.sum_lt_sum (fun k _ => hle z k) ⟨j,Finset.mem_univ j,hj⟩
    rw [heval]
    norm_num at hsum ⊢
    linarith
  refine ⟨y,?_,he,hstrict⟩
  intro z
  by_cases hz : z = x
  · subst z
    exact he.le
  · exact (hstrict z hz).le

def dualRegular (p : RegularData 3 V) (hp : ∀ v, p.data.2 v = 1) :
    RegularData 3 (Vertices p) where
  data := dualData p
  normal_ne_zero := by
    intro x hx
    change rowForm x.val = 0 at hx
    have hh := congrArg coefficients hx
    have hn : x.val = 0 := by simpa only [coefficients_rowForm,coefficients_zero] using hh
    exact vertex_ne_zero p hp x hn
  compact := by
    rw [dual_region p hp]
    exact (Set.finite_range (normals p)).isCompact_convexHull ℝ
  full_dimensional := by
    rw [dual_region p hp]
    exact ⟨0,normals_zero_interior p hp⟩
  strict_facet_point := dual_strict_facet_point p hp

theorem normals_injective (p : RegularData 3 V) (hp : ∀ v, p.data.2 v = 1) :
    Function.Injective (normals p) := by
  intro v w hvw
  by_contra hne
  obtain ⟨x,hx,hv,hs⟩ := p.strict_facet_point v
  have he : p.data.1 v = p.data.1 w := by
    rw [← rowForm_coefficients (p.data.1 v),← rowForm_coefficients (p.data.1 w)]
    exact congrArg rowForm hvw
  have hw := hs w (Ne.symm hne)
  rw [← he,hv,hp,hp] at hw
  exact lt_irrefl 1 hw

def triangleLabels (p : RegularData 3 V) (x : Vertices p) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => p.data.1 v x.val = p.data.2 v)

@[simp] theorem mem_triangleLabels (p : RegularData 3 V) (x : Vertices p) (v : V) :
    v ∈ triangleLabels p x ↔ p.data.1 v x.val = p.data.2 v := by
  classical
  simp [triangleLabels]

theorem triangleLabels_card (p : RegularData 3 V)
    (hs : IsSimpleHalfspace (fun v => (p.data.1 v).toLinearMap) p.data.2) (x : Vertices p) :
    (triangleLabels p x).card = 3 := by
  have he : {v : V // v ∈ triangleLabels p x} ≃
      ActiveFacet (fun v => (p.data.1 v).toLinearMap) p.data.2 x.val :=
    Equiv.subtypeEquivRight (mem_triangleLabels p x)
  have hh := Nat.card_congr he
  rw [hs x.val x.property] at hh
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using hh

theorem triangleLabels_injective (p : RegularData 3 V) :
    Function.Injective (triangleLabels p) := by
  intro x y hxy
  apply extreme_activeFacetSet_injective (fun v => (p.data.1 v).toLinearMap) p.data.2
  ext v
  change (p.data.1 v x.val = p.data.2 v) ↔ p.data.1 v y.val = p.data.2 v
  rw [← mem_triangleLabels,← mem_triangleLabels,hxy]

/-- Every facet label of the original polytope occurs at a vertex other than
any fixed root.  Thus every vertex of the polar belongs to a non-base face. -/
theorem facet_has_nonroot_vertex (p : RegularData 3 V) (root : Vertices p) (v : V) :
    ∃ x : Vertices p, x ≠ root ∧ p.data.1 v x.val = p.data.2 v := by
  classical
  let f := fun i => (p.data.1 i).toLinearMap
  obtain ⟨w,hw,hwv,hwstrict⟩ := p.strict_facet_point v
  have hwr : w ≠ root.val := by
    intro hwr
    obtain ⟨I,hI,_⟩ := extremePoint_has_active_basis f p.data.2 root.property
    have hex : ∃ j : Fin 3, I j ≠ v := by
      by_cases h : I 0 = v
      · refine ⟨1,?_⟩
        intro h1
        have hh := I.injective (h1.trans h.symm)
        exact (by decide : (1 : Fin 3) ≠ 0) hh
      · exact ⟨0,h⟩
    obtain ⟨j,hj⟩ := hex
    have hh := hwstrict (I j) hj
    have hactive := hI j
    change p.data.1 (I j) root.val = p.data.2 (I j) at hactive
    rw [hwr,hactive] at hh
    exact lt_irrefl _ hh
  let F := tightFace f p.data.2 {v}
  have hF := tightFace_isExposed f p.data.2 {v}
  have hwF : w ∈ F := ⟨hw,fun i hi => by
    have hiv : i = v := Set.mem_singleton_iff.mp hi
    change p.data.1 i w = p.data.2 i
    simpa only [hiv] using hwv⟩
  have hhull := exposedFace_eq_convexHull_vertices f p.data.2 p.compact hF
  by_contra! hnot
  have hsub : F ⊆ {root.val} := by
    change tightFace f p.data.2 {v} ⊆ {root.val}
    rw [hhull]
    apply convexHull_min ?_ (convex_singleton _)
    rintro x ⟨hxF,hx⟩
    have hxeq : (⟨x,hx⟩ : Vertices p) = root := by
      by_contra hne
      exact (hnot ⟨x,hx⟩ hne) (hxF.2 v (Set.mem_singleton v))
    exact congrArg Subtype.val hxeq
  exact hwr (hsub hwF)

end NormalProjective.CapSource
end

#print axioms NormalProjective.PolarFinite.hull_iff_polar
#print axioms NormalProjective.Planar.StrictConvexCap.polar_simple
#print axioms NormalProjective.Planar.StrictConvexCap.pnRelated_of_cap_path
#print axioms NormalProjective.CapSource.dualRegular

/-! Read-only actual-body audit; generated from the canonical project root. -/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let localModules : Array Name := #[`cap_polarity_geometry]
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
  IO.FS.writeFile ".lake/reports/audit/final/CapPolarityGeometry_dependencies.json" result.pretty
  logInfo m!"Audited {records.size} local declarations and {boundaryRecords.size} pinned-library boundaries."
