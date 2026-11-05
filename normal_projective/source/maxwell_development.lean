module

public import maxwell_core
public import planar_tools
public import Mathlib.Topology.Path

import boundary_corners
import Mathlib.Data.Finset.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
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
# Exact Maxwell lifting and continuous convex-cap paths

This is the second of the two authoritative Maxwell modules. It uses the
linear and local-fold results of `maxwell_core`, proves the necessary edge
count and global supporting-roof inequalities, and constructs the continuous
path between any two genuine strictly convex caps with the same labelled
combinatorics. The final path theorem assumes no lifting or connectivity
result. Exact source ranges and body hashes are recorded in
`development/maxwell-split-provenance.json`.
-/

@[expose] public section
noncomputable section
open scoped Classical

/- Source section MaxwellCap -/
section
namespace NormalProjective.Planar.StrictConvexCap

open Set Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (C : StrictConvexCap V)

def interiorHeight : C.disk.InteriorVertex → ℝ := fun v => C.height v.val

theorem extend_interiorHeight : C.disk.extendInterior C.interiorHeight = C.height := by
  funext v
  by_cases hv : v ∈ C.disk.boundary
  · obtain ⟨j,rfl⟩ := hv
    rw [C.disk.extendInterior_corner,C.boundary_zero]
  · exact C.disk.extendInterior_at C.interiorHeight ⟨v,hv⟩

theorem facePlane_eq_roof (s : C.disk.toTriangulation.Face) :
    C.disk.facePlane C.height s = C.roof s := by
  apply AffineMap.ext_on
    (C.disk.toTriangulation.faceBasis C.disk.point
      (fun f => C.disk.face_independent f.val f.property) s).tot
  rintro z ⟨v,rfl⟩
  change (C.disk.toTriangulation.facePlaneMap C.disk.point
    (fun f => C.disk.face_independent f.val f.property) s C.height)
      (C.disk.point v.val) = C.roof s (C.disk.point v.val)
  rw [C.disk.toTriangulation.facePlaneMap_vertex C.disk.point _ s C.height v.val v.property]
  exact (C.roof_equal s v.val v.property).symm

theorem stressAt_pos {a b : V}
    (hab : C.disk.toTriangulation.graph.Adj a b)
    (hi : a ∉ C.disk.boundary ∨ b ∉ C.disk.boundary) :
    0 < C.disk.stressAt C.height a b := by
  classical
  let f := C.disk.toTriangulation.incidentSide hab.1
  have hf : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr
      ⟨C.disk.toTriangulation.incidentSide_injective hab.1,
        by simpa using C.disk.incidentFace_card_eq_two hab hi⟩
  obtain ⟨t,ht⟩ := hf.2 true
  obtain ⟨s,hs⟩ := hf.2 false
  have hst : s.val ≠ t.val := by
    intro heq
    have heq' : s = t := Subtype.ext heq
    have hbad := congrArg f heq'
    rw [hs,ht] at hbad
    cases hbad
  let v := C.disk.toTriangulation.edgeThird hab.1 t
  have hv := C.disk.toTriangulation.edgeThird_spec hab.1 t
  have hvnot : v ∉ s.val.val := by
    intro hvs
    have hsub : t.val.val ⊆ s.val.val := by
      rw [hv.2.2]
      simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
      exact ⟨s.property.1,s.property.2,hvs⟩
    have heq : t.val.val = s.val.val :=
      Finset.eq_of_subset_of_card_le hsub (by
        rw [C.disk.face_card t.val.val t.val.property,
          C.disk.face_card s.val.val s.val.property])
    exact hst (Subtype.ext heq.symm)
  have hheight : 0 < edgeHeight (C.disk.point a) (C.disk.point b) (C.disk.point v) := by
    simpa [f,Triangulation.incidentSide,v] using ht
  have hnorm : 0 < Complex.normSq (C.disk.point b-C.disk.point a) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr (C.disk.point_injective.ne hab.1.symm))
  have harea : 0 < signedArea (C.disk.point a) (C.disk.point b) (C.disk.point v) := by
    rw [edgeHeight_eq_area_div] at hheight
    exact (div_pos_iff_of_pos_right hnorm).mp hheight
  have hgap : 0 < C.disk.facePlane C.height s.val (C.disk.point v)-C.height v := by
    rw [C.facePlane_eq_roof]
    exact sub_pos.mpr (C.roof_strict s.val v hvnot)
  rw [C.disk.roof_gap_on_positive_side C.height hab.1 hv.1 hv.2.1
    s.val t.val hst s.property hv.2.2 harea] at hgap
  exact (mul_pos_iff_of_pos_right harea).mp hgap

def maxwellWeights : C.disk.InteriorEdge → ℝ :=
  C.disk.stressLinear C.interiorHeight

theorem maxwellWeights_pos (e : C.disk.InteriorEdge) : 0 < C.maxwellWeights e := by
  rw [maxwellWeights,C.disk.stressLinear_apply,C.extend_interiorHeight]
  exact C.stressAt_pos (C.disk.interiorEdge_adj e) (C.disk.interiorEdge_interior e)

theorem maxwellWeights_equilibrium : C.disk.equilibriumLinear C.maxwellWeights = 0 :=
  C.disk.equilibrium_stress C.interiorHeight

end NormalProjective.Planar.StrictConvexCap
end

/- Source section MaxwellEdgeCount -/
section
namespace NormalProjective.Planar.TriangularDisk

open Set Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (D : TriangularDisk V)

abbrev CountedEdge := {e : Finset V // e.card = 2 ∧ ∃ s ∈ D.faces, e ⊆ s}

instance countedEdgeFintype : Fintype D.CountedEdge := by
  classical
  unfold CountedEdge
  infer_instance

def edgeIsInterior (e : D.CountedEdge) : Prop := ∃ v ∈ e.val, v ∉ D.boundary

def countedInteriorEquiv : {e : D.CountedEdge // D.edgeIsInterior e} ≃ D.InteriorEdge where
  toFun e := ⟨e.val.val,e.val.property.1,e.val.property.2,e.property⟩
  invFun e := ⟨⟨e.val,e.property.1,e.property.2.1⟩,e.property.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def boundaryFinset : Finset V := Finset.univ.map D.corner

@[simp] theorem mem_boundaryFinset (v : V) : v ∈ D.boundaryFinset ↔ v ∈ D.boundary := by
  simp [boundaryFinset,TriangularDisk.boundary,Set.mem_range]

@[simp] theorem card_boundaryFinset : D.boundaryFinset.card = 3 := by
  simp [boundaryFinset]

theorem boundary_pair_is_edge (e : Finset V) (hc : e.card = 2)
    (he : e ⊆ D.boundaryFinset) : ∃ s ∈ D.faces, e ⊆ s := by
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hc
  obtain ⟨i,rfl⟩ := (D.mem_boundaryFinset a).mp (he (by simp))
  obtain ⟨j,rfl⟩ := (D.mem_boundaryFinset b).mp (he (by simp))
  have hij : i ≠ j := fun hh => hab (congrArg D.corner hh)
  obtain ⟨_,s,hs,ha,hb⟩ := D.boundary_edge i j hij
  exact ⟨s,hs,by simp [Finset.insert_subset_iff,ha,hb]⟩

def countedBoundaryEquiv : {e : D.CountedEdge // ¬D.edgeIsInterior e} ≃
    {e : Finset V // e ∈ D.boundaryFinset.powersetCard 2} where
  toFun e := ⟨e.val.val,Finset.mem_powersetCard.mpr ⟨by
    intro v hv
    apply (D.mem_boundaryFinset v).mpr
    by_contra hn
    exact e.property ⟨v,hv,hn⟩,e.val.property.1⟩⟩
  invFun e := ⟨⟨e.val,(Finset.mem_powersetCard.mp e.property).2,
    D.boundary_pair_is_edge e.val (Finset.mem_powersetCard.mp e.property).2
      (Finset.mem_powersetCard.mp e.property).1⟩,by
    rintro ⟨v,hv,hn⟩
    exact hn ((D.mem_boundaryFinset v).mp
      ((Finset.mem_powersetCard.mp e.property).1 hv))⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem counted_boundary_card : Fintype.card {e : D.CountedEdge // ¬D.edgeIsInterior e} = 3 := by
  classical
  rw [Fintype.card_congr D.countedBoundaryEquiv]
  change Fintype.card (D.boundaryFinset.powersetCard 2) = 3
  rw [Fintype.card_coe,Finset.card_powersetCard,D.card_boundaryFinset]
  norm_num

abbrev EdgeFaces (e : D.CountedEdge) := {s : D.toTriangulation.Face // e.val ⊆ s.val}

instance edgeFacesFintype (e : D.CountedEdge) : Fintype (D.EdgeFaces e) := by
  classical
  unfold EdgeFaces
  infer_instance

def edgeFacesEquivIncident (e : D.CountedEdge) {a b : V} (he : e.val = {a,b}) :
    D.EdgeFaces e ≃ D.toTriangulation.IncidentFace a b where
  toFun s := ⟨s.val,by simpa [he,Finset.insert_subset_iff] using s.property⟩
  invFun s := ⟨s.val,by simpa [he,Finset.insert_subset_iff] using s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem edgeFaces_card (e : D.CountedEdge) :
    Fintype.card (D.EdgeFaces e) = if D.edgeIsInterior e then 2 else 1 := by
  classical
  obtain ⟨a,b,hab,he⟩ := Finset.card_eq_two.mp e.property.1
  have habG : D.toTriangulation.graph.Adj a b := by
    obtain ⟨s,hs,hes⟩ := e.property.2
    refine ⟨hab,s,hs,hes ?_,hes ?_⟩ <;> simp [he]
  rw [Fintype.card_congr (D.edgeFacesEquivIncident e he)]
  by_cases hi : D.edgeIsInterior e
  · rw [if_pos hi]
    apply D.incidentFace_card_eq_two habG
    obtain ⟨v,hv,hvi⟩ := hi
    rw [he] at hv
    rcases edge_mem_pair_iff.mp hv with rfl | rfl
    · exact Or.inl hvi
    · exact Or.inr hvi
  · rw [if_neg hi]
    apply D.incidentFace_card_eq_one habG
    · by_contra ha
      exact hi ⟨a,by simp [he],ha⟩
    · by_contra hb
      exact hi ⟨b,by simp [he],hb⟩

def faceEdgeIncidenceEquiv :
    (Σ s : D.toTriangulation.Face, {e : Finset V // e ∈ s.val.powersetCard 2}) ≃
      (Σ e : D.CountedEdge, D.EdgeFaces e) where
  toFun x := ⟨⟨x.2.val,(Finset.mem_powersetCard.mp x.2.property).2,
    x.1.val,x.1.property,(Finset.mem_powersetCard.mp x.2.property).1⟩,
    x.1,(Finset.mem_powersetCard.mp x.2.property).1⟩
  invFun x := ⟨x.2.val,⟨x.1.val,
    Finset.mem_powersetCard.mpr ⟨x.2.property,x.1.property.1⟩⟩⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

theorem edge_face_incidence_count :
    3 * Fintype.card D.toTriangulation.Face = 2 * Fintype.card D.InteriorEdge + 3 := by
  classical
  have hface (s : D.toTriangulation.Face) :
      Fintype.card {e : Finset V // e ∈ s.val.powersetCard 2} = 3 := by
    change Fintype.card (s.val.powersetCard 2) = 3
    rw [Fintype.card_coe,Finset.card_powersetCard,D.face_card s.val s.property]
    norm_num
  have hsplit := Fintype.sum_subtype_add_sum_subtype (D.edgeIsInterior)
    (fun e => Fintype.card (D.EdgeFaces e))
  have hsum : (∑ e : D.CountedEdge, Fintype.card (D.EdgeFaces e)) =
      2 * Fintype.card D.InteriorEdge + 3 := by
    rw [← hsplit]
    have hin : ∀ e : {e : D.CountedEdge // D.edgeIsInterior e},
        Fintype.card (D.EdgeFaces e.val) = 2 :=
      fun e => by rw [D.edgeFaces_card,if_pos e.property]
    have hout : ∀ e : {e : D.CountedEdge // ¬D.edgeIsInterior e},
        Fintype.card (D.EdgeFaces e.val) = 1 :=
      fun e => by rw [D.edgeFaces_card,if_neg e.property]
    simp_rw [hin,hout]
    simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one]
    rw [Fintype.card_congr D.countedInteriorEquiv,D.counted_boundary_card]
    omega
  calc
    3 * Fintype.card D.toTriangulation.Face =
        Fintype.card (Σ s : D.toTriangulation.Face,
          {e : Finset V // e ∈ s.val.powersetCard 2}) := by
      rw [Fintype.card_sigma]
      simp_rw [hface]
      simp [Nat.mul_comm]
    _ = Fintype.card (Σ e : D.CountedEdge, D.EdgeFaces e) :=
      Fintype.card_congr D.faceEdgeIncidenceEquiv
    _ = ∑ e : D.CountedEdge, Fintype.card (D.EdgeFaces e) := Fintype.card_sigma
    _ = 2 * Fintype.card D.InteriorEdge + 3 := hsum

theorem interior_edge_count_of_face_count
    (hfaces : Fintype.card D.toTriangulation.Face =
      2 * Fintype.card D.InteriorVertex + 1) :
    Fintype.card D.InteriorEdge = 3 * Fintype.card D.InteriorVertex := by
  have h := D.edge_face_incidence_count
  omega

end NormalProjective.Planar.TriangularDisk
end

/- Source section MaxwellContinuity -/
section
namespace NormalProjective.Planar

open Set Finset Filter Matrix
open scoped Topology

theorem affineGradient_coordinates (L : ℂ →ᵃ[ℝ] ℝ) {a b c : ℂ}
    (harea : signedArea a b c ≠ 0) :
    (affineGradient L).re =
      ((L b-L a)*(c-a).im-(L c-L a)*(b-a).im) / signedArea a b c ∧
    (affineGradient L).im =
      ((b-a).re*(L c-L a)-(c-a).re*(L b-L a)) / signedArea a b c := by
  have hb := affineGradient_dot_difference L a b
  have hc := affineGradient_dot_difference L a c
  constructor
  · apply (eq_div_iff harea).mpr
    unfold signedArea
    linear_combination (c-a).im * hb - (b-a).im * hc
  · apply (eq_div_iff harea).mpr
    unfold signedArea
    linear_combination (b-a).re * hc - (c-a).re * hb

theorem continuous_signedArea {X : Type*} [TopologicalSpace X]
    {a b c : X → ℂ} (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
    Continuous (fun x => signedArea (a x) (b x) (c x)) := by
  unfold signedArea
  exact ((Complex.continuous_re.comp (hb.sub ha)).mul
      (Complex.continuous_im.comp (hc.sub ha))).sub
    ((Complex.continuous_im.comp (hb.sub ha)).mul
      (Complex.continuous_re.comp (hc.sub ha)))

theorem continuous_numericSign_of_nonzero {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} (hf : Continuous f) (hne : ∀ x, f x ≠ 0) :
    Continuous (fun x => numericSign (f x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rcases lt_or_gt_of_ne (hne x) with hn | hp
  · have hN : ∀ᶠ y in 𝓝 x, f y < 0 :=
      (isOpen_lt hf continuous_const).mem_nhds hn
    apply (continuousAt_const : ContinuousAt (fun _ : X => (-1 : ℝ)) x).congr
    filter_upwards [hN] with y hy
    exact (numericSign_of_neg hy).symm
  · have hN : ∀ᶠ y in 𝓝 x, 0 < f y :=
      (isOpen_lt continuous_const hf).mem_nhds hp
    apply (continuousAt_const : ContinuousAt (fun _ : X => (1 : ℝ)) x).congr
    filter_upwards [hN] with y hy
    exact (numericSign_of_pos hy).symm

namespace Triangulation

variable {V : Type*} [Fintype V] [DecidableEq V] (T : Triangulation V)
variable {X : Type*} [TopologicalSpace X]
variable (q : X → V → ℂ)
  (hind : ∀ x, ∀ s : T.Face, AffineIndependent ℝ (fun v : s.val => q x v.val))

theorem continuous_faceGradient (h : X → V → ℝ)
    (hq : Continuous q) (hh : Continuous h) (s : T.Face) :
    Continuous (fun x => affineGradient (T.facePlaneMap (q x) (hind x) s (h x))) := by
  let a := (T.faceEnumeration s 0).val
  let b := (T.faceEnumeration s 1).val
  let c := (T.faceEnumeration s 2).val
  have hinj : Function.Injective (fun i => (T.faceEnumeration s i).val) :=
    Subtype.val_injective.comp (T.faceEnumeration s).injective
  have hab : a ≠ b := hinj.ne (by decide : (0 : Fin 3) ≠ 1)
  have hca : c ≠ a := hinj.ne (by decide : (2 : Fin 3) ≠ 0)
  have hcb : c ≠ b := hinj.ne (by decide : (2 : Fin 3) ≠ 1)
  have harea : ∀ x, signedArea (q x a) (q x b) (q x c) ≠ 0 := by
    intro x
    exact signedArea_ne_zero_of_height_ne_zero
      (height_ne_zero_of_face_independent (q x) (hind x s)
        (T.faceEnumeration s 0).property (T.faceEnumeration s 1).property
        (T.faceEnumeration s 2).property hab hca hcb)
  have hqv (v : V) : Continuous (fun x => q x v) := (continuous_apply v).comp hq
  have hhv (v : V) : Continuous (fun x => h x v) := (continuous_apply v).comp hh
  have hden : Continuous (fun x => signedArea (q x a) (q x b) (q x c)) :=
    continuous_signedArea (hqv a) (hqv b) (hqv c)
  let R : X → ℝ := fun x =>
    ((h x b-h x a)*(q x c-q x a).im-(h x c-h x a)*(q x b-q x a).im) /
      signedArea (q x a) (q x b) (q x c)
  let S : X → ℝ := fun x =>
    ((q x b-q x a).re*(h x c-h x a)-(q x c-q x a).re*(h x b-h x a)) /
      signedArea (q x a) (q x b) (q x c)
  have hR : Continuous R :=
    ((((hhv b).sub (hhv a)).mul (Complex.continuous_im.comp ((hqv c).sub (hqv a)))).sub
      (((hhv c).sub (hhv a)).mul (Complex.continuous_im.comp ((hqv b).sub (hqv a))))).div
        hden harea
  have hS : Continuous S :=
    (((Complex.continuous_re.comp ((hqv b).sub (hqv a))).mul ((hhv c).sub (hhv a))).sub
      ((Complex.continuous_re.comp ((hqv c).sub (hqv a))).mul ((hhv b).sub (hhv a)))).div
        hden harea
  have heq : (fun x => affineGradient (T.facePlaneMap (q x) (hind x) s (h x))) =
      fun x => (R x : ℂ)+(S x : ℂ)*Complex.I := by
    funext x
    have hc' := affineGradient_coordinates
      (T.facePlaneMap (q x) (hind x) s (h x)) (harea x)
    rw [T.facePlaneMap_vertex (q x) (hind x) s (h x) a (T.faceEnumeration s 0).property,
      T.facePlaneMap_vertex (q x) (hind x) s (h x) b (T.faceEnumeration s 1).property,
      T.facePlaneMap_vertex (q x) (hind x) s (h x) c (T.faceEnumeration s 2).property] at hc'
    apply Complex.ext
    · simpa [R] using hc'.1
    · simpa [S] using hc'.2
  rw [heq]
  exact (Complex.continuous_ofReal.comp hR).add
    ((Complex.continuous_ofReal.comp hS).mul continuous_const)

include hind in
theorem continuous_faceIncidence (hq : Continuous q) (s : T.Face) (a b : V) :
    Continuous (fun x => faceIncidence (q x) s.val a b) := by
  classical
  by_cases hs : a ∈ s.val ∧ b ∈ s.val
  · simp only [faceIncidence,if_pos hs]
    apply continuous_finsetSum
    intro v hv
    by_cases hab : a = b
    · subst b
      simp only [signedArea_repeat_base,numericSign_zero]
      exact continuous_const
    by_cases hva : v = a
    · subst v
      simp only [signedArea_repeat_left,numericSign_zero]
      exact continuous_const
    by_cases hvb : v = b
    · subst v
      simp only [signedArea_repeat_right,numericSign_zero]
      exact continuous_const
    apply continuous_numericSign_of_nonzero
    · exact continuous_signedArea ((continuous_apply a).comp hq)
        ((continuous_apply b).comp hq) ((continuous_apply v).comp hq)
    · intro x
      exact signedArea_ne_zero_of_height_ne_zero
        (height_ne_zero_of_face_independent (q x) (hind x s) hs.1 hs.2 hv hab hva hvb)
  · simp only [faceIncidence,if_neg hs]
    exact continuous_const

theorem continuous_edgeGradientDifference (h : X → V → ℝ)
    (hq : Continuous q) (hh : Continuous h) (a b : V) :
    Continuous (fun x => T.edgeGradientDifference (q x) (hind x) (h x) a b) := by
  unfold edgeGradientDifference
  apply Continuous.neg
  apply continuous_finsetSum
  intro s hs
  exact (T.continuous_faceIncidence q hind hq s a b).smul
    (T.continuous_faceGradient q hind h hq hh s)

end Triangulation

namespace Maxwell

theorem continuous_perpendicularCoefficient {X : Type*} [TopologicalSpace X]
    {d g : X → ℂ} (hd : Continuous d) (hg : Continuous g) (hne : ∀ x, d x ≠ 0) :
    Continuous (fun x => perpendicularCoefficient (d x) (g x)) := by
  have hdr := Complex.continuous_re.comp hd
  have hdi := Complex.continuous_im.comp hd
  have hgr := Complex.continuous_re.comp hg
  have hgi := Complex.continuous_im.comp hg
  unfold perpendicularCoefficient
  apply ((hgi.mul hdr).sub (hgr.mul hdi)).div
  · simpa only [Complex.normSq_apply,Pi.add_def,Pi.mul_def,Function.comp_def]
      using (hdr.mul hdr).add (hdi.mul hdi)
  · intro x
    exact mt Complex.normSq_eq_zero.mp (hne x)

end Maxwell

namespace TriangularDisk

open Maxwell

variable {V : Type*} [Fintype V] [DecidableEq V] (D : TriangularDisk V)

/-- The Maxwell matrix on fixed combinatorial index sets, evaluated at a
possibly varying nondegenerate drawing. -/
def drawingStressMatrix (q : V → ℂ)
    (hind : ∀ s : D.toTriangulation.Face,
      AffineIndependent ℝ (fun v : s.val => q v.val)) :
    Matrix D.InteriorEdge D.InteriorVertex ℝ := fun e i =>
  perpendicularCoefficient (q (D.interiorEdgeRight e)-q (D.interiorEdgeLeft e))
    (D.toTriangulation.edgeGradientDifference q hind
      (D.extendInterior (Pi.single i 1)) (D.interiorEdgeLeft e) (D.interiorEdgeRight e))

def stressMatrix : Matrix D.InteriorEdge D.InteriorVertex ℝ :=
  LinearMap.toMatrix' D.stressLinear

theorem stressMatrix_mulVec (h : D.InteriorVertex → ℝ) :
    D.stressMatrix *ᵥ h = D.stressLinear h := LinearMap.toMatrix'_mulVec _ _

theorem drawingStressMatrix_self :
    D.drawingStressMatrix D.point (fun s => D.face_independent s.val s.property) =
      D.stressMatrix := by
  ext e i
  rw [stressMatrix,LinearMap.toMatrix'_apply,D.stressLinear_apply] <;> rfl

theorem drawing_edge_ne (q : V → ℂ)
    (hind : ∀ s : D.toTriangulation.Face,
      AffineIndependent ℝ (fun v : s.val => q v.val)) (e : D.InteriorEdge) :
    q (D.interiorEdgeRight e)-q (D.interiorEdgeLeft e) ≠ 0 := by
  apply sub_ne_zero.mpr
  intro heq
  obtain ⟨_,s,hs,ha,hb⟩ := D.interiorEdge_adj e
  have hv := (hind ⟨s,hs⟩).injective
    (a₁ := ⟨D.interiorEdgeRight e,hb⟩) (a₂ := ⟨D.interiorEdgeLeft e,ha⟩) heq
  exact (D.interiorEdge_endpoints e).1 (congrArg Subtype.val hv).symm

theorem continuous_drawingStressMatrix {X : Type*} [TopologicalSpace X]
    (q : X → V → ℂ)
    (hind : ∀ x, ∀ s : D.toTriangulation.Face,
      AffineIndependent ℝ (fun v : s.val => q x v.val))
    (hq : Continuous q) : Continuous (fun x => D.drawingStressMatrix (q x) (hind x)) := by
  apply continuous_pi
  intro e
  apply continuous_pi
  intro i
  apply continuous_perpendicularCoefficient
  · exact ((continuous_apply (D.interiorEdgeRight e)).comp hq).sub
      ((continuous_apply (D.interiorEdgeLeft e)).comp hq)
  · exact D.toTriangulation.continuous_edgeGradientDifference q hind
      (fun _ => D.extendInterior (Pi.single i 1)) hq continuous_const
      (D.interiorEdgeLeft e) (D.interiorEdgeRight e)
  · exact fun x => D.drawing_edge_ne (q x) (hind x) e

theorem harmonic_drawingStressMatrix_eq (w : V → V → ℝ)
    (hw : ∀ i j, 0 ≤ w i j)
    (he : ∀ i j, D.toTriangulation.graph.Adj i j → 0 < w i j)
    (hoff : ∀ i j, ¬D.toTriangulation.graph.Adj i j → w i j = 0)
    (q : V → ℂ) (hq : D.IsHarmonicDrawing w q) :
    D.drawingStressMatrix q (fun s => D.harmonic_face_independent w hw he hoff q hq s.val s.property) =
      (D.harmonicTriangularDisk w hw he hoff q hq).stressMatrix := by
  exact (D.harmonicTriangularDisk w hw he hoff q hq).drawingStressMatrix_self

end TriangularDisk

end NormalProjective.Planar
end

/- Source section MaxwellRoof -/
section
/- Source section FaceCoordinates -/
section
namespace NormalProjective.Planar.Triangulation

open Set Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (T : Triangulation V)

theorem faceEnumeration_label_injective (s : T.Face) :
    Function.Injective (fun i => (T.faceEnumeration s i).val) :=
  Subtype.val_injective.comp (T.faceEnumeration s).injective

theorem faceEnumeration_triple (s : T.Face) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    s.val = {(T.faceEnumeration s i).val,(T.faceEnumeration s j).val,
      (T.faceEnumeration s k).val} := by
  ext v
  constructor
  · intro hv
    obtain ⟨l,hl⟩ := (T.faceEnumeration s).surjective ⟨v,hv⟩
    have hcover : l = i ∨ l = j ∨ l = k := by
      fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp_all
    simp only [Finset.mem_insert,Finset.mem_singleton]
    have heq : (T.faceEnumeration s l).val = v := congrArg Subtype.val hl
    rcases hcover with rfl | rfl | rfl
    · exact Or.inl heq.symm
    · exact Or.inr (Or.inl heq.symm)
    · exact Or.inr (Or.inr heq.symm)
  · intro hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    all_goals exact (T.faceEnumeration s _).property

theorem outside_face_edge {s : T.Face} {v : V} (hv : v ∉ s.val) :
    ∃ a b x : V, a ≠ b ∧ x ≠ a ∧ x ≠ b ∧ s.val = {a,b,x} ∧
      edgeHeight (T.point a) (T.point b) (T.point x) *
        edgeHeight (T.point a) (T.point b) (T.point v) < 0 := by
  let hind : ∀ f : T.Face, AffineIndependent ℝ (fun v : f.val => T.point v.val) :=
    fun f => T.face_independent f.val f.property
  let Δ := T.drawingTriangle T.point hind s
  have hnot : T.point v ∉ Δ.carrier := by
    change T.point v ∉ (T.drawingTriangle T.point hind s).carrier
    rw [T.drawingTriangle_carrier]
    exact fun h => hv ((T.point_mem_simplex_iff s.property (Finset.Subset.refl _) v).mp h)
  have hcoords : ¬ ∀ i, 0 ≤ Δ.coord i (T.point v) := by
    simpa only [← Δ.mem_carrier_iff] using hnot
  push_neg at hcoords
  obtain ⟨k,hk⟩ := hcoords
  have hex : ∃ i j : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
    fin_cases k
    · exact ⟨1,2,by decide,by decide,by decide⟩
    · exact ⟨0,2,by decide,by decide,by decide⟩
    · exact ⟨0,1,by decide,by decide,by decide⟩
  obtain ⟨i,j,hij,hik,hjk⟩ := hex
  let a := (T.faceEnumeration s i).val
  let b := (T.faceEnumeration s j).val
  let x := (T.faceEnumeration s k).val
  have hab : a ≠ b := (T.faceEnumeration_label_injective s).ne hij
  have hxa : x ≠ a := (T.faceEnumeration_label_injective s).ne hik.symm
  have hxb : x ≠ b := (T.faceEnumeration_label_injective s).ne hjk.symm
  have hs := T.faceEnumeration_triple s i j k hij hik hjk
  have hxne : edgeHeight (T.point a) (T.point b) (T.point x) ≠ 0 :=
    T.face_third_height_ne_zero s.property (T.faceEnumeration s i).property
      (T.faceEnumeration s j).property (T.faceEnumeration s k).property hab hxa hxb
  refine ⟨a,b,x,hab,hxa,hxb,hs,?_⟩
  have heq := Δ.coord_mul_height i j k hij hik hjk (T.point v)
  change Δ.coord k (T.point v) * edgeHeight (T.point a) (T.point b) (T.point x) =
    edgeHeight (T.point a) (T.point b) (T.point v) at heq
  rw [← heq]
  have hsquare : 0 < (edgeHeight (T.point a) (T.point b) (T.point x))^2 :=
    sq_pos_of_ne_zero hxne
  nlinarith [mul_neg_of_neg_of_pos hk hsquare]

end NormalProjective.Planar.Triangulation
end


/- Source section PlaneDescent -/
section
namespace NormalProjective.Planar

open Set Finset

theorem affine_eq_height_multiple {a b y : ℂ} (hy : edgeHeight a b y ≠ 0)
    (L : ℂ →ᵃ[ℝ] ℝ) (ha : L a = 0) (hb : L b = 0) (z : ℂ) :
    L z * edgeHeight a b y = L y * edgeHeight a b z := by
  let T : Triangle := ⟨![a,b,y],affineIndependent_triple_of_height_ne_zero hy⟩
  let H : ℂ →ᵃ[ℝ] ℝ := Complex.imCLM.toLinearMap.toAffineMap.comp (edgeNormalize a b)
  have heq : edgeHeight a b y • L = L y • H := by
    apply AffineMap.ext_on T.basis.tot
    rintro x ⟨i,rfl⟩
    change edgeHeight a b y * L (T.point i) = L y * edgeHeight a b (T.point i)
    fin_cases i
    · simp [T,ha,edgeHeight,edgeNormalize]
    · have hab : a ≠ b := by intro h; apply hy; simp [h,edgeHeight,edgeNormalize]
      simp [T,hb,edgeHeight,edgeNormalize_right hab]
    · simp [T,mul_comm]
  have h := congrArg (fun f : ℂ →ᵃ[ℝ] ℝ => f z) heq
  change edgeHeight a b y * L z = L y * edgeHeight a b z at h
  simpa only [mul_comm] using h

theorem affine_positive_on_same_edge_side {a b y z : ℂ}
    (L : ℂ →ᵃ[ℝ] ℝ) (ha : L a = 0) (hb : L b = 0) (hy : 0 < L y)
    (hside : 0 < edgeHeight a b y * edgeHeight a b z) : 0 < L z := by
  have hyne : edgeHeight a b y ≠ 0 := by intro h; simp [h] at hside
  have heq := affine_eq_height_multiple hyne L ha hb z
  have hprod : 0 < L z * (edgeHeight a b y)^2 := by
    have hh : L z * (edgeHeight a b y)^2 = L y *
        (edgeHeight a b y * edgeHeight a b z) := by
      linear_combination edgeHeight a b y * heq
    rw [hh]
    exact mul_pos hy hside
  exact (mul_pos_iff.mp hprod).elim (fun h => h.1)
    (fun h => False.elim ((sq_nonneg (edgeHeight a b y)).not_gt h.2))

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Triangulation

variable (T : Triangulation V)

/-- The finite minimum argument. Its descent premise will be proved from the
literal adjacent-face inequalities, not included in the final cap definition. -/
theorem strict_roofs_of_descent (h : V → ℝ) (L : T.Face → ℂ →ᵃ[ℝ] ℝ)
    (hvertex : ∀ s v, v ∈ s.val → L s (T.point v) = h v)
    (hdescent : ∀ s v, v ∉ s.val → ∃ t : T.Face, L t (T.point v) < L s (T.point v)) :
    ∀ s v, v ∉ s.val → h v < L s (T.point v) := by
  classical
  intro s v hvs
  obtain ⟨t,htv⟩ := hdescent s v hvs
  letI : Nonempty T.Face := ⟨s⟩
  obtain ⟨m,hm,hmin⟩ := Finset.exists_min_image (Finset.univ : Finset T.Face)
    (fun f => L f (T.point v)) (Finset.univ_nonempty)
  have hvm : v ∈ m.val := by
    by_contra hvm
    obtain ⟨n,hn⟩ := hdescent m v hvm
    exact hn.not_ge (hmin n (Finset.mem_univ n))
  rw [← hvertex m v hvm]
  exact (hmin t (Finset.mem_univ t)).trans_lt htv

end Triangulation

namespace TriangularDisk

variable (D : TriangularDisk V)

theorem opposite_vertex_forces_interior_edge {a b x v : V}
    (hab : a ≠ b) (hxa : x ≠ a) (hxb : x ≠ b)
    (hopp : edgeHeight (D.point a) (D.point b) (D.point x) *
      edgeHeight (D.point a) (D.point b) (D.point v) < 0) :
    a ∉ D.boundary ∨ b ∉ D.boundary := by
  by_contra! h
  obtain ⟨i,rfl⟩ := h.1
  obtain ⟨j,rfl⟩ := h.2
  have hij : i ≠ j := fun h => hab (congrArg D.corner h)
  have hex : ∃ k : Fin 3, i ≠ k ∧ j ≠ k ∧
      ∀ l : Fin 3, l = i ∨ l = j ∨ l = k := by
    fin_cases i <;> fin_cases j <;> simp_all
    all_goals decide
  obtain ⟨k,hik,hjk,hcover⟩ := hex
  obtain ⟨σ,hσ,hheight⟩ := boundary_height_coordinate_exact i j k hij hik hjk
  rw [D.corner_point,D.corner_point,hheight,hheight] at hopp
  have hx := D.coordinate_positive_away_two_corners i j k hcover x hxa hxb
  have hv := D.source_coordinates_nonnegative v k
  have hnonneg : 0 ≤ (σ * triangleCoordinate k (D.point x)) *
      (σ * triangleCoordinate k (D.point v)) := by
    calc
      0 ≤ (σ * σ) *
          (triangleCoordinate k (D.point x) * triangleCoordinate k (D.point v)) :=
        mul_nonneg (mul_self_nonneg σ) (mul_nonneg hx.le hv)
      _ = (σ * triangleCoordinate k (D.point x)) *
          (σ * triangleCoordinate k (D.point v)) := by ring
  exact hopp.not_ge hnonneg

end TriangularDisk

end NormalProjective.Planar
end


/- Source section LocalRoofs -/
section
namespace NormalProjective.Planar.TriangularDisk

open Set Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (D : TriangularDisk V)

def LocalStrictRoofs (h : V → ℝ) (L : D.toTriangulation.Face → ℂ →ᵃ[ℝ] ℝ) : Prop :=
  ∀ s t : D.toTriangulation.Face, D.toTriangulation.faceGraph.Adj s t →
    ∀ v ∈ t.val, v ∉ s.val → h v < L s (D.point v)

theorem roof_descent (h : V → ℝ) (L : D.toTriangulation.Face → ℂ →ᵃ[ℝ] ℝ)
    (hvertex : ∀ s v, v ∈ s.val → L s (D.point v) = h v)
    (hlocal : D.LocalStrictRoofs h L)
    (s : D.toTriangulation.Face) (v : V) (hvs : v ∉ s.val) :
    ∃ t : D.toTriangulation.Face, L t (D.point v) < L s (D.point v) := by
  obtain ⟨a,b,x,hab,hxa,hxb,hs,hopp⟩ := D.toTriangulation.outside_face_edge hvs
  have hsf : ({a,b,x} : Finset V) ∈ D.faces := hs ▸ s.property
  have hi := D.opposite_vertex_forces_interior_edge hab hxa hxb hopp
  have hxne : edgeHeight (D.point a) (D.point b) (D.point x) ≠ 0 := by
    intro hzero
    simp [hzero] at hopp
  have hex : ∃ y, y ≠ a ∧ y ≠ b ∧ y ≠ x ∧ ({a,b,y} : Finset V) ∈ D.faces ∧
      0 < edgeHeight (D.point a) (D.point b) (D.point y) *
        edgeHeight (D.point a) (D.point b) (D.point v) := by
    rcases lt_or_gt_of_ne hxne with hxneg | hxpos
    · have hsf' : ({b,a,x} : Finset V) ∈ D.faces := by
        simpa only [Finset.insert_comm] using hsf
      have hxpos' : 0 < edgeHeight (D.point b) (D.point a) (D.point x) := by
        rw [edgeHeight_swap (D.point_injective.ne hab)]
        exact neg_pos.mpr hxneg
      obtain ⟨y,hyb,hya,hyx,hyf,hyneg⟩ := D.exists_opposite_face hsf' hab.symm hxb hxa hi.symm hxpos'
      have hypos : 0 < edgeHeight (D.point a) (D.point b) (D.point y) := by
        rw [edgeHeight_swap (D.point_injective.ne hab)] at hyneg
        linarith
      have hvpos : 0 < edgeHeight (D.point a) (D.point b) (D.point v) := by nlinarith
      exact ⟨y,hya,hyb,hyx,by simpa only [Finset.insert_comm] using hyf,mul_pos hypos hvpos⟩
    · obtain ⟨y,hya,hyb,hyx,hyf,hyneg⟩ := D.exists_opposite_face hsf hab hxa hxb hi hxpos
      have hvneg : edgeHeight (D.point a) (D.point b) (D.point v) < 0 := by nlinarith
      exact ⟨y,hya,hyb,hyx,hyf,mul_pos_of_neg_of_neg hyneg hvneg⟩
  obtain ⟨y,hya,hyb,hyx,hyf,hside⟩ := hex
  let t : D.toTriangulation.Face := ⟨{a,b,y},hyf⟩
  have hyout : y ∉ s.val := by
    rw [hs]
    simp [hya,hyb,hyx]
  have hst : s ≠ t := by
    intro h
    apply hyout
    rw [h]
    simp [t]
  have hadj : D.toTriangulation.faceGraph.Adj s t := by
    refine ⟨hst,?_⟩
    have hsub : ({a,b} : Finset V) ⊆ s.val ∩ t.val := by
      rw [hs]
      simp [t,Finset.insert_subset_iff]
    have hc := Finset.card_le_card hsub
    simpa [hab] using hc
  let A : ℂ →ᵃ[ℝ] ℝ := L s - L t
  have hAa : A (D.point a) = 0 := by
    change L s (D.point a)-L t (D.point a) = 0
    rw [hvertex s a (by simp [hs]),hvertex t a (by simp [t]),sub_self]
  have hAb : A (D.point b) = 0 := by
    change L s (D.point b)-L t (D.point b) = 0
    rw [hvertex s b (by simp [hs]),hvertex t b (by simp [t]),sub_self]
  have hAy : 0 < A (D.point y) := by
    change 0 < L s (D.point y)-L t (D.point y)
    rw [hvertex t y (by simp [t])]
    exact sub_pos.mpr (hlocal s t hadj y (by simp [t]) hyout)
  have hAv := affine_positive_on_same_edge_side A hAa hAb hAy hside
  exact ⟨t,sub_pos.mp hAv⟩

/-- Global supporting inequalities for every face and every vertex follow
from the actual local folds. This is the full convexity implication needed in
the lifting stage, not a weakened sufficient condition for Corollary 2. -/
theorem global_strict_roofs_of_local (h : V → ℝ)
    (L : D.toTriangulation.Face → ℂ →ᵃ[ℝ] ℝ)
    (hvertex : ∀ s v, v ∈ s.val → L s (D.point v) = h v)
    (hlocal : D.LocalStrictRoofs h L) :
    ∀ s v, v ∉ s.val → h v < L s (D.point v) :=
  D.toTriangulation.strict_roofs_of_descent h L hvertex (D.roof_descent h L hvertex hlocal)

end NormalProjective.Planar.TriangularDisk
end


/- Source section CapHeight -/
section
namespace NormalProjective.Planar

open Set Finset

theorem affine_base_coordinate_formula (L : ℂ →ᵃ[ℝ] ℝ) (z : ℂ) :
    L z = ∑ j : Fin 3, triangleCoordinate j z * L (basePoint j) := by
  have h := (Finset.univ : Finset (Fin 3)).map_affineCombination basePoint
    (fun j => triangleCoordinate j z) (coordinate_sum z) L
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (coordinate_sum z),
    Finset.affineCombination_eq_linear_combination _ _ _ (coordinate_sum z),
    coordinate_reconstruct] at h
  simpa only [Function.comp_apply,smul_eq_mul] using h

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace TriangularDisk

variable (D : TriangularDisk V)

theorem face_missing_corner (hi : ∃ v, v ∉ D.boundary) (s : D.toTriangulation.Face) :
    ∃ j, D.corner j ∉ s.val := by
  classical
  by_contra! hall
  let B : Finset V := Finset.univ.image D.corner
  have hBcard : B.card = 3 := by
    rw [Finset.card_image_of_injective _ D.corner.injective]
    simp
  have hBs : B ⊆ s.val := by
    intro v hv
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
    exact hall j
  have hBeq : B = s.val := Finset.eq_of_subset_of_card_le hBs (by
    rw [D.face_card s.val s.property,hBcard])
  obtain ⟨v,hv⟩ := hi
  have hsub : baseTriangle ⊆ D.toTriangulation.cell s := by
    rw [baseTriangle_eq_convexHull]
    apply convexHull_min
    · rintro z ⟨j,rfl⟩
      rw [← D.corner_point]
      exact D.toTriangulation.point_mem_cell s (hall j)
    · exact convex_convexHull ℝ _
  have hvdom : D.point v ∈ baseTriangle := by
    rw [← D.domain_eq]
    exact D.toTriangulation.point_mem_domain v
  have hvs : v ∈ s.val :=
    (D.toTriangulation.point_mem_simplex_iff s.property (Finset.Subset.refl _) v).mp (hsub hvdom)
  rw [← hBeq] at hvs
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hvs
  exact hv ⟨j,hj⟩

theorem height_positive_of_strict_roofs
    (hi : ∃ v, v ∉ D.boundary) (h : V → ℝ)
    (L : D.toTriangulation.Face → ℂ →ᵃ[ℝ] ℝ)
    (hzero : ∀ j, h (D.corner j) = 0)
    (hvertex : ∀ s v, v ∈ s.val → L s (D.point v) = h v)
    (hstrict : ∀ s v, v ∉ s.val → h v < L s (D.point v))
    (v : V) (hv : v ∉ D.boundary) : 0 < h v := by
  classical
  obtain ⟨s,hs,hvs⟩ := D.vertex_covered v
  let f : D.toTriangulation.Face := ⟨s,hs⟩
  obtain ⟨j,hjf⟩ := D.face_missing_corner hi f
  have hnonneg : ∀ k, 0 ≤ L f (basePoint k) := by
    intro k
    rw [← D.corner_point]
    by_cases hk : D.corner k ∈ f.val
    · rw [hvertex f _ hk,hzero]
    · exact (hzero k ▸ hstrict f _ hk).le
  have hpos : 0 < L f (basePoint j) := by
    rw [← D.corner_point]
    exact hzero j ▸ hstrict f _ hjf
  rw [← hvertex f v hvs,affine_base_coordinate_formula]
  apply Finset.sum_pos'
  · intro k hk
    exact mul_nonneg (D.interior_vertex v hv k).le (hnonneg k)
  · exact ⟨j,Finset.mem_univ j,mul_pos (D.interior_vertex v hv j) hpos⟩

/-- The actual cap obtained from a lifting whose strict local folds have been
proved. All cap fields, including positivity and every remote roof inequality,
are derived here. -/
def strictConvexCapOfLocal
    (hi : ∃ v, v ∉ D.boundary) (h : V → ℝ)
    (L : D.toTriangulation.Face → ℂ →ᵃ[ℝ] ℝ)
    (hzero : ∀ j, h (D.corner j) = 0)
    (hvertex : ∀ s v, v ∈ s.val → L s (D.point v) = h v)
    (hlocal : D.LocalStrictRoofs h L) : StrictConvexCap V where
  disk := D
  interior_nonempty := hi
  height := h
  boundary_zero := hzero
  interior_positive := D.height_positive_of_strict_roofs hi h L hzero hvertex
    (D.global_strict_roofs_of_local h L hvertex hlocal)
  roof := L
  roof_equal := hvertex
  roof_strict := D.global_strict_roofs_of_local h L hvertex hlocal

end TriangularDisk

end NormalProjective.Planar
end
end

/- Source section MaxwellLifting -/
section
namespace NormalProjective.Planar.TriangularDisk

open Set Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] (D : TriangularDisk V)

theorem interior_edge_count :
    Fintype.card D.InteriorEdge = 3 * Fintype.card D.InteriorVertex :=
  D.interior_edge_count_of_face_count D.elementary_face_count

theorem maxwell_dimension_identity
    (hcount : Fintype.card D.InteriorEdge = 3 * Fintype.card D.InteriorVertex) :
    Module.finrank ℝ (D.InteriorEdge → ℝ) =
      Module.finrank ℝ (D.InteriorVertex → ℝ) +
        Module.finrank ℝ (D.InteriorVertex → ℂ) := by
  simp only [Module.finrank_pi,Module.finrank_pi_fintype,Complex.finrank_real_complex,
    Finset.sum_const,Finset.card_univ,smul_eq_mul]
  omega

theorem maxwell_exact_of_count
    (hcount : Fintype.card D.InteriorEdge = 3 * Fintype.card D.InteriorVertex) :
    LinearMap.range D.stressLinear = LinearMap.ker D.equilibriumLinear :=
  range_eq_kernel_of_dimensions D.stressLinear D.equilibriumLinear
    D.stressLinear_injective D.equilibriumLinear_surjective D.equilibrium_comp_stress
    (D.maxwell_dimension_identity hcount)

theorem maxwell_exact : LinearMap.range D.stressLinear = LinearMap.ker D.equilibriumLinear :=
  D.maxwell_exact_of_count D.interior_edge_count

theorem existsUnique_height_of_count
    (hcount : Fintype.card D.InteriorEdge = 3 * Fintype.card D.InteriorVertex)
    (w : D.InteriorEdge → ℝ) (hw : D.equilibriumLinear w = 0) :
    ∃! h : D.InteriorVertex → ℝ, D.stressLinear h = w :=
  existsUnique_lifting_of_dimensions D.stressLinear D.equilibriumLinear
    D.stressLinear_injective D.equilibriumLinear_surjective D.equilibrium_comp_stress
    (D.maxwell_dimension_identity hcount) w hw

theorem stressMatrix_injective : Function.Injective D.stressMatrix.mulVec := by
  intro h k heq
  apply D.stressLinear_injective
  simpa only [D.stressMatrix_mulVec] using heq

def canonicalHeight (w : D.InteriorEdge → ℝ) : D.InteriorVertex → ℝ :=
  liftingLeftInverse D.stressMatrix w

/-- Equality of disks transports the whole lifting function, including its
edge-index type. This avoids an ill-typed rewrite of a disk while keeping a
weight vector whose type depends on that disk fixed. -/
theorem canonicalLift_heq {E : TriangularDisk V} (hDE : D = E) :
    HEq (fun w : D.InteriorEdge → ℝ => D.extendInterior (D.canonicalHeight w))
      (fun w : E.InteriorEdge → ℝ => E.extendInterior (E.canonicalHeight w)) := by
  cases hDE
  rfl

/-- Transport an actual lifting value across equality of disks and of its
possibly dependent weight-vector type. -/
theorem canonicalLift_apply_eq {E : TriangularDisk V} (hDE : D = E)
    (w : D.InteriorEdge → ℝ) (w' : E.InteriorEdge → ℝ) (hw : HEq w w') :
    D.extendInterior (D.canonicalHeight w) = E.extendInterior (E.canonicalHeight w') := by
  cases hDE
  cases hw
  rfl

theorem canonicalHeight_stressLinear (h : D.InteriorVertex → ℝ) :
    D.canonicalHeight (D.stressLinear h) = h := by
  rw [← D.stressMatrix_mulVec,canonicalHeight]
  exact liftingLeftInverse_apply D.stressMatrix D.stressMatrix_injective h

theorem canonicalHeight_solution_of_count
    (hcount : Fintype.card D.InteriorEdge = 3 * Fintype.card D.InteriorVertex)
    (w : D.InteriorEdge → ℝ) (hw : D.equilibriumLinear w = 0) :
    D.stressLinear (D.canonicalHeight w) = w := by
  obtain ⟨h,hh,_⟩ := D.existsUnique_height_of_count hcount w hw
  rw [← hh,D.canonicalHeight_stressLinear]

theorem canonicalHeight_solution (w : D.InteriorEdge → ℝ)
    (hw : D.equilibriumLinear w = 0) : D.stressLinear (D.canonicalHeight w) = w :=
  D.canonicalHeight_solution_of_count D.interior_edge_count w hw

def capOfPositiveEquilibrium
    (hi : ∃ v, v ∉ D.boundary)
    (w : D.InteriorEdge → ℝ) (hpos : ∀ e, 0 < w e)
    (heq : D.equilibriumLinear w = 0) : StrictConvexCap V :=
  D.strictConvexCapOfLocal hi (D.extendInterior (D.canonicalHeight w))
    (D.facePlane (D.extendInterior (D.canonicalHeight w)))
    (D.extendInterior_corner _)
    (fun s v hv => D.toTriangulation.facePlaneMap_vertex D.point _ s _ v hv)
    (D.stress_positive_local_folds _ (fun e => by
      rw [D.canonicalHeight_solution w heq]
      exact hpos e))

@[simp] theorem capOfPositiveEquilibrium_disk
    (hi : ∃ v, v ∉ D.boundary)
    (w : D.InteriorEdge → ℝ) (hpos : ∀ e, 0 < w e)
    (heq : D.equilibriumLinear w = 0) :
    (D.capOfPositiveEquilibrium hi w hpos heq).disk = D := rfl

@[simp] theorem capOfPositiveEquilibrium_height
    (hi : ∃ v, v ∉ D.boundary)
    (w : D.InteriorEdge → ℝ) (hpos : ∀ e, 0 < w e)
    (heq : D.equilibriumLinear w = 0) :
    (D.capOfPositiveEquilibrium hi w hpos heq).height =
      D.extendInterior (D.canonicalHeight w) := rfl

end NormalProjective.Planar.TriangularDisk
end

/- Source section MaxwellHarmonic -/
section
namespace NormalProjective.Planar.TriangularDisk

open Set Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (D : TriangularDisk V)

def completedWeights (w : D.InteriorEdge → ℝ) (a b : V) : ℝ := by
  classical
  exact if hab : D.toTriangulation.graph.Adj a b then
    if hi : a ∉ D.boundary ∨ b ∉ D.boundary then w (D.edgeOfAdjacent hab hi) else 1
  else 0

theorem completedWeights_off_graph (w : D.InteriorEdge → ℝ) (a b : V)
    (hab : ¬D.toTriangulation.graph.Adj a b) : D.completedWeights w a b = 0 := by
  simp [completedWeights,hab]

theorem completedWeights_positive (w : D.InteriorEdge → ℝ) (hw : ∀ e, 0 < w e)
    (a b : V) (hab : D.toTriangulation.graph.Adj a b) :
    0 < D.completedWeights w a b := by
  simp only [completedWeights,dif_pos hab]
  split_ifs
  · exact hw _
  · norm_num

theorem completedWeights_nonnegative (w : D.InteriorEdge → ℝ) (hw : ∀ e, 0 < w e) :
    ∀ a b, 0 ≤ D.completedWeights w a b := by
  intro a b
  by_cases hab : D.toTriangulation.graph.Adj a b
  · exact (D.completedWeights_positive w hw a b hab).le
  · simp [D.completedWeights_off_graph w a b hab]

theorem completedWeights_at_interior (w : D.InteriorEdge → ℝ) (a b : V)
    (ha : a ∉ D.boundary) : D.completedWeights w a b = D.edgeWeight w a b := by
  classical
  by_cases hab : D.toTriangulation.graph.Adj a b
  · simp [completedWeights,edgeWeight,hab,ha]
  · simp [completedWeights,edgeWeight,hab]

theorem continuous_completedWeights {X : Type*} [TopologicalSpace X]
    (w : X → D.InteriorEdge → ℝ) (hw : Continuous w) :
    Continuous (fun x => D.completedWeights (w x)) := by
  classical
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  simp only [completedWeights]
  split_ifs
  · exact (continuous_apply _).comp hw
  · exact continuous_const
  · exact continuous_const

theorem equilibrium_iff_point_harmonic (w : D.InteriorEdge → ℝ) :
    D.equilibriumLinear w = 0 ↔ D.IsHarmonicDrawing (D.completedWeights w) D.point := by
  have hre (a : D.InteriorVertex) :
      Dirichlet.Harmonic (D.completedWeights w) (fun v => (D.point v).re) a.val ↔
        (D.equilibriumLinear w a).re = 0 := by
    rw [D.equilibriumLinear_apply]
    simp only [Complex.re_sum,Complex.smul_re,Complex.sub_re,smul_eq_mul]
    unfold Dirichlet.Harmonic
    have hneg (b : V) : (D.point a.val).re - (D.point b).re =
        -((D.point b).re - (D.point a.val).re) := by ring
    simp_rw [D.completedWeights_at_interior w a.val _ a.property,
      hneg,mul_neg,Finset.sum_neg_distrib,neg_eq_zero]
  have him (a : D.InteriorVertex) :
      Dirichlet.Harmonic (D.completedWeights w) (fun v => (D.point v).im) a.val ↔
        (D.equilibriumLinear w a).im = 0 := by
    rw [D.equilibriumLinear_apply]
    simp only [Complex.im_sum,Complex.smul_im,Complex.sub_im,smul_eq_mul]
    unfold Dirichlet.Harmonic
    have hneg (b : V) : (D.point a.val).im - (D.point b).im =
        -((D.point b).im - (D.point a.val).im) := by ring
    simp_rw [D.completedWeights_at_interior w a.val _ a.property,
      hneg,mul_neg,Finset.sum_neg_distrib,neg_eq_zero]
  constructor
  · intro hw
    refine ⟨D.corner_point,?_⟩
    intro v hv
    have hh := congrFun hw ⟨v,hv⟩
    exact ⟨(hre ⟨v,hv⟩).mpr (by simp [hh]),(him ⟨v,hv⟩).mpr (by simp [hh])⟩
  · intro hq
    funext a
    apply Complex.ext
    · exact (hre a).mp (hq.2 a.val a.property).1
    · exact (him a).mp (hq.2 a.val a.property).2

def harmonicSolution (w : D.InteriorEdge → ℝ) : V → ℂ := fun v =>
  (Dirichlet.solution D.boundary (D.completedWeights w) (fun v => (D.point v).re) v : ℂ) +
  (Dirichlet.solution D.boundary (D.completedWeights w) (fun v => (D.point v).im) v : ℂ) * Complex.I

theorem harmonicSolution_drawing (w : D.InteriorEdge → ℝ) (hw : ∀ e, 0 < w e) :
    D.IsHarmonicDrawing (D.completedWeights w) (D.harmonicSolution w) := by
  have hB : D.boundary.Nonempty := ⟨D.corner 0,0,rfl⟩
  have hr := Dirichlet.solution_spec D.toTriangulation.graph D.graph_connected
    D.boundary hB (D.completedWeights w) (D.completedWeights_nonnegative w hw)
    (D.completedWeights_positive w hw) (fun v => (D.point v).re)
  have hi := Dirichlet.solution_spec D.toTriangulation.graph D.graph_connected
    D.boundary hB (D.completedWeights w) (D.completedWeights_nonnegative w hw)
    (D.completedWeights_positive w hw) (fun v => (D.point v).im)
  constructor
  · intro j
    apply Complex.ext
    · simpa [harmonicSolution,D.corner_point] using hr.1 (D.corner j) ⟨j,rfl⟩
    · simpa [harmonicSolution,D.corner_point] using hi.1 (D.corner j) ⟨j,rfl⟩
  · intro v hv
    constructor
    · simpa [harmonicSolution] using hr.2 v hv
    · simpa [harmonicSolution] using hi.2 v hv

theorem harmonicSolution_eq (w : D.InteriorEdge → ℝ) (hw : ∀ e, 0 < w e)
    (q : V → ℂ) (hq : D.IsHarmonicDrawing (D.completedWeights w) q) :
    D.harmonicSolution w = q := by
  have hB : D.boundary.Nonempty := ⟨D.corner 0,0,rfl⟩
  have hboundary : ∀ v ∈ D.boundary, q v = D.point v := by
    rintro v ⟨j,rfl⟩
    rw [hq.1,D.corner_point]
  have hsol (b x : V → ℝ) (hb : ∀ v ∈ D.boundary, x v = b v)
      (hx : ∀ v, v ∉ D.boundary → Dirichlet.Harmonic (D.completedWeights w) x v) :
      Dirichlet.solution D.boundary (D.completedWeights w) b = x := by
    obtain ⟨y,_,hy⟩ := Dirichlet.existsUnique_extension
      D.toTriangulation.graph D.graph_connected D.boundary hB (D.completedWeights w)
      (D.completedWeights_nonnegative w hw) (D.completedWeights_positive w hw) b
    exact (hy _ (Dirichlet.solution_spec D.toTriangulation.graph D.graph_connected
      D.boundary hB (D.completedWeights w) (D.completedWeights_nonnegative w hw)
      (D.completedWeights_positive w hw) b)).trans (hy x ⟨hb,hx⟩).symm
  have hr := hsol
    (fun v => (D.point v).re) (fun v => (q v).re)
    (fun v hv => congrArg Complex.re (hboundary v hv))
    (fun v hv => (hq.2 v hv).1)
  have hi := hsol
    (fun v => (D.point v).im) (fun v => (q v).im)
    (fun v hv => congrArg Complex.im (hboundary v hv))
    (fun v hv => (hq.2 v hv).2)
  funext v
  apply Complex.ext <;> simp [harmonicSolution,hr,hi]

theorem continuous_harmonicSolution {X : Type*} [TopologicalSpace X]
    (w : X → D.InteriorEdge → ℝ) (hw : Continuous w) (hpos : ∀ x e, 0 < w x e) :
    Continuous (fun x => D.harmonicSolution (w x)) := by
  have hB : D.boundary.Nonempty := ⟨D.corner 0,0,rfl⟩
  have hr := Dirichlet.continuous_solution D.toTriangulation.graph D.graph_connected
    D.boundary hB (fun x => D.completedWeights (w x)) (D.continuous_completedWeights w hw)
    (fun x => D.completedWeights_nonnegative (w x) (hpos x))
    (fun x => D.completedWeights_positive (w x) (hpos x)) (fun v => (D.point v).re)
  have hi := Dirichlet.continuous_solution D.toTriangulation.graph D.graph_connected
    D.boundary hB (fun x => D.completedWeights (w x)) (D.continuous_completedWeights w hw)
    (fun x => D.completedWeights_nonnegative (w x) (hpos x))
    (fun x => D.completedWeights_positive (w x) (hpos x)) (fun v => (D.point v).im)
  apply continuous_pi
  intro v
  exact (Complex.continuous_ofReal.comp ((continuous_apply v).comp hr)).add
    ((Complex.continuous_ofReal.comp ((continuous_apply v).comp hi)).mul continuous_const)

end NormalProjective.Planar.TriangularDisk
end

/- Source section MaxwellRebase -/
section
namespace NormalProjective.Planar

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem Triangulation.ext_point_faces {T U : Triangulation V}
    (hp : T.point = U.point) (hf : T.faces = U.faces) : T = U := by
  rcases T with ⟨p,hp',f,hfc,hfi,hint,hcov⟩
  rcases U with ⟨q,hq',g,hgc,hgi,hint',hcov'⟩
  change p = q at hp
  change f = g at hf
  subst q
  subst g
  rfl

theorem TriangularDisk.ext_point_faces_corner {D E : TriangularDisk V}
    (hp : D.point = E.point) (hf : D.faces = E.faces) (hc : D.corner = E.corner) : D = E := by
  rcases D with ⟨T,c,hcp,hdom,hint⟩
  rcases E with ⟨U,d,hdp,hdom',hint'⟩
  have hTU : T = U := Triangulation.ext_point_faces hp hf
  subst U
  change c = d at hc
  subst d
  rfl

namespace TriangularDisk

/-- Replace equal face and corner fields by the prescribed fields. Its point
configuration and its actual geometry are exactly those of `E`. -/
def rebase (D E : TriangularDisk V) (hf : D.faces = E.faces) (hc : D.corner = E.corner) :
    TriangularDisk V where
  point := E.point
  point_injective := E.point_injective
  faces := D.faces
  face_card s hs := E.face_card s (by simpa only [hf] using hs)
  face_independent s hs := E.face_independent s (by simpa only [hf] using hs)
  intersection s hs t ht := E.intersection s (by simpa only [hf] using hs)
    t (by simpa only [hf] using ht)
  vertex_covered v := by simpa only [hf] using E.vertex_covered v
  corner := D.corner
  corner_point j := by simpa only [hc] using E.corner_point j
  domain_eq := by
    change (⋃ s : {s : Finset V // s ∈ D.faces}, simplex E.point s.val) = baseTriangle
    rw [hf]
    simpa only [Triangulation.domain,Triangulation.cell] using E.domain_eq
  interior_vertex v hv := E.interior_vertex v (by simpa only [hc] using hv)

theorem rebase_eq (D E : TriangularDisk V) (hf : D.faces = E.faces) (hc : D.corner = E.corner) :
    D.rebase E hf hc = E :=
  ext_point_faces_corner rfl hf hc

end TriangularDisk

namespace StrictConvexCap

theorem ext_geometric_data {C E : StrictConvexCap V}
    (hp : C.disk.point = E.disk.point) (hf : C.disk.faces = E.disk.faces)
    (hc : C.disk.corner = E.disk.corner) (hh : C.height = E.height) : C = E := by
  rcases C with ⟨D,hi,h,hzero,hpos,L,hLe,hLs⟩
  rcases E with ⟨D',hi',h',hzero',hpos',L',hLe',hLs'⟩
  have hD : D = D' := TriangularDisk.ext_point_faces_corner hp hf hc
  subst D'
  change h = h' at hh
  subst h'
  have hL : L = L' := by
    funext s
    apply AffineMap.ext_on
      (D.toTriangulation.faceBasis D.point
        (fun f => D.face_independent f.val f.property) s).tot
    rintro z ⟨v,rfl⟩
    exact (hLe s v.val v.property).trans (hLe' s v.val v.property).symm
  subst L'
  rfl

/-- Normalize the representations of equal combinatorial fields. The result
equals the given cap, not merely an isomorphic or affinely equivalent cap. -/
def rebase (C : StrictConvexCap V) (D : TriangularDisk V)
    (hf : D.faces = C.disk.faces) (hc : D.corner = C.disk.corner) : StrictConvexCap V where
  disk := D.rebase C.disk hf hc
  interior_nonempty := by
    simpa only [TriangularDisk.boundary,TriangularDisk.rebase,hc] using C.interior_nonempty
  height := C.height
  boundary_zero j := by
    simpa only [TriangularDisk.rebase,hc] using C.boundary_zero j
  interior_positive v hv := C.interior_positive v (by
    simpa only [TriangularDisk.boundary,TriangularDisk.rebase,hc] using hv)
  roof s := C.roof ⟨s.val,by simpa only [TriangularDisk.rebase,hf] using s.property⟩
  roof_equal s v hv := C.roof_equal
    ⟨s.val,by simpa only [TriangularDisk.rebase,hf] using s.property⟩ v hv
  roof_strict s v hv := C.roof_strict
    ⟨s.val,by simpa only [TriangularDisk.rebase,hf] using s.property⟩ v hv

theorem rebase_eq (C : StrictConvexCap V) (D : TriangularDisk V)
    (hf : D.faces = C.disk.faces) (hc : D.corner = C.disk.corner) : C.rebase D hf hc = C :=
  ext_geometric_data rfl hf hc rfl

end StrictConvexCap

end NormalProjective.Planar
end

/- Source section MaxwellCapPath -/
section
namespace NormalProjective.Planar

open Set Finset
open scoped Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace TriangularDisk

variable (D : TriangularDisk V)

def stressDisk (w : D.InteriorEdge → ℝ) (hw : ∀ e, 0 < w e) : TriangularDisk V :=
  D.harmonicTriangularDisk (D.completedWeights w)
    (D.completedWeights_nonnegative w hw) (D.completedWeights_positive w hw)
    (D.completedWeights_off_graph w) (D.harmonicSolution w) (D.harmonicSolution_drawing w hw)

theorem stressDisk_equilibrium (w : D.InteriorEdge → ℝ) (hw : ∀ e, 0 < w e) :
    (D.stressDisk w hw).equilibriumLinear w = 0 := by
  apply ((D.stressDisk w hw).equilibrium_iff_point_harmonic w).mpr
  exact D.harmonicSolution_drawing w hw

def capFromWeights (hi : ∃ v, v ∉ D.boundary)
    (w : D.InteriorEdge → ℝ) (hw : ∀ e, 0 < w e) : StrictConvexCap V :=
  (D.stressDisk w hw).capOfPositiveEquilibrium hi w hw (D.stressDisk_equilibrium w hw)

@[simp] theorem capFromWeights_point (hi : ∃ v, v ∉ D.boundary)
    (w : D.InteriorEdge → ℝ) (hw : ∀ e, 0 < w e) :
    (D.capFromWeights hi w hw).disk.point = D.harmonicSolution w := rfl

@[simp] theorem capFromWeights_faces (hi : ∃ v, v ∉ D.boundary)
    (w : D.InteriorEdge → ℝ) (hw : ∀ e, 0 < w e) :
    (D.capFromWeights hi w hw).disk.faces = D.faces := rfl

@[simp] theorem capFromWeights_corner (hi : ∃ v, v ∉ D.boundary)
    (w : D.InteriorEdge → ℝ) (hw : ∀ e, 0 < w e) :
    (D.capFromWeights hi w hw).disk.corner = D.corner := rfl

theorem continuous_extendInterior {X : Type*} [TopologicalSpace X]
    (h : X → D.InteriorVertex → ℝ) (hh : Continuous h) :
    Continuous (fun x => D.extendInterior (h x)) := by
  classical
  apply continuous_pi
  intro v
  by_cases hv : v ∉ D.boundary
  · simp only [extendInterior,dif_pos hv]
    exact (continuous_apply ⟨v,hv⟩).comp hh
  · simp only [extendInterior,dif_neg hv]
    exact continuous_const

theorem continuous_stressDisk_matrix {X : Type*} [TopologicalSpace X]
    (w : X → D.InteriorEdge → ℝ) (hw : Continuous w) (hpos : ∀ x e, 0 < w x e) :
    Continuous (X := X) (Y := Matrix D.InteriorEdge D.InteriorVertex ℝ)
      (fun x => (D.stressDisk (w x) (hpos x)).stressMatrix) := by
  let q := fun x => D.harmonicSolution (w x)
  let hind := fun x (s : D.toTriangulation.Face) =>
    D.harmonic_face_independent (D.completedWeights (w x))
      (D.completedWeights_nonnegative (w x) (hpos x))
      (D.completedWeights_positive (w x) (hpos x))
      (D.completedWeights_off_graph (w x)) (q x)
      (D.harmonicSolution_drawing (w x) (hpos x)) s.val s.property
  have heq : (fun x => D.drawingStressMatrix (q x) (hind x)) =
      fun x => (D.stressDisk (w x) (hpos x)).stressMatrix := by
    funext x
    exact D.harmonic_drawingStressMatrix_eq (D.completedWeights (w x))
      (D.completedWeights_nonnegative (w x) (hpos x))
      (D.completedWeights_positive (w x) (hpos x))
      (D.completedWeights_off_graph (w x)) (q x)
      (D.harmonicSolution_drawing (w x) (hpos x))
  rw [← heq]
  exact D.continuous_drawingStressMatrix q hind (D.continuous_harmonicSolution w hw hpos)

theorem continuous_capFromWeights {X : Type*} [TopologicalSpace X]
    (hi : ∃ v, v ∉ D.boundary) (w : X → D.InteriorEdge → ℝ)
    (hw : Continuous w) (hpos : ∀ x e, 0 < w x e) :
    Continuous (fun x => D.capFromWeights hi (w x) (hpos x)) := by
  let M : X → Matrix D.InteriorEdge D.InteriorVertex ℝ :=
    fun x => (D.stressDisk (w x) (hpos x)).stressMatrix
  have hM : Continuous M := D.continuous_stressDisk_matrix w hw hpos
  have hinj (x : X) : Function.Injective (M x).mulVec :=
    (D.stressDisk (w x) (hpos x)).stressMatrix_injective
  have hH : Continuous (X := X) (Y := D.InteriorVertex → ℝ)
      (fun x => (D.stressDisk (w x) (hpos x)).canonicalHeight (w x)) := by
    change Continuous (X := X) (Y := D.InteriorVertex → ℝ)
      (fun x => liftingLeftInverse (M x) (w x))
    exact continuous_liftingLeftInverse (X := X)
      (I := D.InteriorVertex) (J := D.InteriorEdge) M w hM hw hinj
  apply continuous_induced_rng.mpr
  change Continuous (fun x => (D.harmonicSolution (w x),
    D.extendInterior ((D.stressDisk (w x) (hpos x)).canonicalHeight (w x))))
  exact (D.continuous_harmonicSolution w hw hpos).prodMk
    (D.continuous_extendInterior _ hH)

theorem capFromWeights_eq_rebase (hi : ∃ v, v ∉ D.boundary)
    (C : StrictConvexCap V) (hf : D.faces = C.disk.faces) (hc : D.corner = C.disk.corner) :
    D.capFromWeights hi (C.rebase D hf hc).maxwellWeights
      (C.rebase D hf hc).maxwellWeights_pos = C := by
  let E := C.rebase D hf hc
  have hq : D.harmonicSolution E.maxwellWeights = E.disk.point := by
    apply D.harmonicSolution_eq E.maxwellWeights E.maxwellWeights_pos E.disk.point
    exact (E.disk.equilibrium_iff_point_harmonic E.maxwellWeights).mp E.maxwellWeights_equilibrium
  have hd : D.stressDisk E.maxwellWeights E.maxwellWeights_pos = E.disk :=
    ext_point_faces_corner hq rfl rfl
  have heq : D.capFromWeights hi E.maxwellWeights E.maxwellWeights_pos = E := by
    apply StrictConvexCap.ext_geometric_data
      (C := D.capFromWeights hi E.maxwellWeights E.maxwellWeights_pos) (E := E)
      hq rfl rfl
    change (D.stressDisk E.maxwellWeights E.maxwellWeights_pos).extendInterior
      ((D.stressDisk E.maxwellWeights E.maxwellWeights_pos).canonicalHeight E.maxwellWeights) =
        E.height
    have htransport :
        (D.stressDisk E.maxwellWeights E.maxwellWeights_pos).extendInterior
          ((D.stressDisk E.maxwellWeights E.maxwellWeights_pos).canonicalHeight E.maxwellWeights) =
        E.disk.extendInterior (E.disk.canonicalHeight E.maxwellWeights) :=
      (D.stressDisk E.maxwellWeights E.maxwellWeights_pos).canonicalLift_apply_eq
        (E := E.disk) hd E.maxwellWeights E.maxwellWeights (HEq.refl _)
    rw [htransport]
    change E.disk.extendInterior (E.disk.canonicalHeight (E.disk.stressLinear E.interiorHeight)) = _
    rw [E.disk.canonicalHeight_stressLinear,E.extend_interiorHeight]
  exact heq.trans (C.rebase_eq D hf hc)

end TriangularDisk

namespace StrictConvexCap

/-- The full fixed-combinatorics cap space is path connected. The path consists
of genuine caps, with exact geometric triangulations and all strict supporting
inequalities retained at every parameter value. -/
theorem exists_path_sameCombinatorics (C E : StrictConvexCap V)
    (hCE : C.SameCombinatorics E) :
    ∃ γ : Path C E, ∀ t, C.SameCombinatorics (γ t) := by
  let D := C.disk
  let C₀ := C.rebase D rfl rfl
  let C₁ := E.rebase D hCE.1 hCE.2
  let w : unitInterval → D.InteriorEdge → ℝ := fun t e =>
    (1-(t : ℝ))*C₀.maxwellWeights e+(t : ℝ)*C₁.maxwellWeights e
  have hw : Continuous w := by
    apply continuous_pi
    intro e
    exact ((continuous_const.sub continuous_subtype_val).mul continuous_const).add
      (continuous_subtype_val.mul continuous_const)
  have hpos : ∀ t e, 0 < w t e := by
    intro t e
    have h₀ := C₀.maxwellWeights_pos e
    have h₁ := C₁.maxwellWeights_pos e
    by_cases ht : (t : ℝ) = 0
    · simpa [w,ht] using h₀
    · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr t.property.2) h₀.le) (mul_pos htpos h₁)
  let F : unitInterval → StrictConvexCap V :=
    fun t => D.capFromWeights C.interior_nonempty (w t) (hpos t)
  have hF : Continuous F := D.continuous_capFromWeights C.interior_nonempty w hw hpos
  have hF₀ : F 0 = C := by
    simpa [F,w,C₀] using D.capFromWeights_eq_rebase C.interior_nonempty C rfl rfl
  have hF₁ : F 1 = E := by
    simpa [F,w,C₁] using D.capFromWeights_eq_rebase C.interior_nonempty E hCE.1 hCE.2
  let γ : Path C E :=
    { toFun := F
      continuous_toFun := hF
      source' := hF₀
      target' := hF₁ }
  refine ⟨γ,?_⟩
  intro t
  exact ⟨rfl,rfl⟩

end StrictConvexCap

end NormalProjective.Planar
end

/-! Read-only actual-body audit; generated from Verify.lean. -/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let localModules : Array Name := #[`maxwell_development]
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
  IO.FS.writeFile ".lake/reports/audit/final/MaxwellDevelopment_dependencies.json" result.pretty
  logInfo m!"Audited {records.size} local declarations and {boundaryRecords.size} pinned-library boundaries."
