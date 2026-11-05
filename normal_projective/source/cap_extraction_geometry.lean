module

public import cap_polarity_geometry
import Mathlib.Data.Finset.Max
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
# Extracting corresponding genuine caps from arbitrary simple inputs

Generated from exact fragment bodies by `tools/assemble_cap_modules.py`.
Retained-line provenance is recorded in `audit/current/CapExtractionGeometry_source_map.json`.
Only imports, file-wide section headers, and diagnostic commands are consolidated.
The ordinary compiler and axiom-audit records identify the checked source bytes.
-/

@[expose] public section
noncomputable section

/- Source: Cor2Candidate/CapSourceShrink.lean -/
section
/-!
# Moving the polar into cap position

For a normalized input polytope and one of its actual vertices `r`, expand the
primal by the affine map `x ↦ r + t⁻¹ • (x-r)`.  The three polar vertices of the
distinguished facet stay fixed, while every other polar vertex tends to zero
as `t` tends to zero through positive values.  A single affine coordinate map
then puts the distinguished facet at the standard horizontal triangle.
-/

open Set Finset Filter
open scoped BigOperators Topology

namespace NormalProjective.CapSource

open CanonicalModel UnitNormalization NormalHull
open Planar Planar.CapCoordinates

variable {V : Type*} [Fintype V]

def scalarEquiv (t : ℝ) (ht : t ≠ 0) : Space ≃ₗ[ℝ] Space where
  toFun x := t • x
  invFun x := t⁻¹ • x
  map_add' x y := smul_add t x y
  map_smul' c x := by simp only [smul_smul, RingHom.id_apply]; rw [mul_comm]
  left_inv x := by
    change t⁻¹ • (t • x) = x
    rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
  right_inv x := by
    change t • (t⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ ht, one_smul]

def rootExpansion (r : Space) (t : ℝ) (ht : t ≠ 0) : Space ≃ᵃ[ℝ] Space where
  toFun x := r + t⁻¹ • (x-r)
  invFun x := r + t • (x-r)
  linear := (scalarEquiv t ht).symm
  left_inv x := by
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp [ht]
    ring
  right_inv x := by
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp [ht]
    ring
  map_vadd' x y := by
    change r + t⁻¹ • ((y + x) - r) =
      t⁻¹ • y + (r + t⁻¹ • (x - r))
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring

@[simp] theorem rootExpansion_root (r : Space) (t : ℝ) (ht : t ≠ 0) :
    rootExpansion r t ht r = r := by simp [rootExpansion]

def rootDenominator (p : RegularData 3 V) (r : Space) (t : ℝ) (v : V) : ℝ :=
  1-(1-t)*p.data.1 v r

theorem rootDenominator_pos (p : RegularData 3 V) (hp : ∀ v, p.data.2 v = 1)
    {r : Space} (hr : r ∈ dataRegion p.data) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (v : V) : 0 < rootDenominator p r t v := by
  have hv := hr v
  change p.data.1 v r ≤ p.data.2 v at hv
  rw [hp v] at hv
  have hh := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hv)
  dsimp [rootDenominator]
  nlinarith

theorem expanded_data (p : RegularData 3 V) (hp : ∀ v, p.data.2 v = 1)
    (r : Space) (t : ℝ) (ht : t ≠ 0) :
    (affineRegular (rootExpansion r t ht) p).data =
      (fun v => t • p.data.1 v, rootDenominator p r t) := by
  apply Prod.ext
  · funext v
    apply ContinuousLinearMap.ext
    intro x
    change p.data.1 v (t • x) = (t • p.data.1 v) x
    simp
  · funext v
    change p.data.2 v - p.data.1 v (r + t • (0-r)) = _
    rw [hp]
    simp only [map_add, map_smul, map_sub, map_zero, smul_eq_mul]
    dsimp [rootDenominator]
    ring

def shrinkRegular (p : RegularData 3 V) (hp : ∀ v, p.data.2 v = 1)
    (r : Space) (hr : r ∈ dataRegion p.data) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    RegularData 3 V :=
  scaleRegular (affineRegular (rootExpansion r t ht.ne') p)
    (fun v => (rootDenominator p r t v)⁻¹)
    (fun v => inv_pos.mpr (rootDenominator_pos p hp hr ht ht1 v))

def shrinkingNormal (p : RegularData 3 V) (r : Space) (t : ℝ) (v : V) : Space :=
  (t / rootDenominator p r t v) • normals p v

theorem shrinkRegular_support (p : RegularData 3 V) (hp : ∀ v, p.data.2 v = 1)
    (r : Space) (hr : r ∈ dataRegion p.data) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (v : V) : (shrinkRegular p hp r hr t ht ht1).data.2 v = 1 := by
  change (rootDenominator p r t v)⁻¹ *
    (affineRegular (rootExpansion r t ht.ne') p).data.2 v = 1
  rw [expanded_data p hp]
  exact inv_mul_cancel₀ (rootDenominator_pos p hp hr ht ht1 v).ne'

theorem shrinkRegular_normals (p : RegularData 3 V) (hp : ∀ v, p.data.2 v = 1)
    (r : Space) (hr : r ∈ dataRegion p.data) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    normals (shrinkRegular p hp r hr t ht ht1) = shrinkingNormal p r t := by
  funext v j
  change ((rootDenominator p r t v)⁻¹ •
    (affineRegular (rootExpansion r t ht.ne') p).data.1 v) (Pi.single j 1) = _
  rw [expanded_data p hp]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, shrinkingNormal,
    Pi.smul_apply, normals, coefficients, div_eq_mul_inv]
  ring

theorem shrinkRegular_presentation (p : RegularData 3 V)
    (hp : ∀ v, p.data.2 v = 1) (r : Space) (hr : r ∈ dataRegion p.data)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    presentation (shrinkRegular p hp r hr t ht ht1) =
      affinePresentation (rootExpansion r t ht.ne') (presentation p) := by
  rw [shrinkRegular,presentation_scaleRegular,affineRegular_presentation]

theorem shrinkingNormal_tight (p : RegularData 3 V) (r : Space) (t : ℝ)
    (ht : t ≠ 0) (v : V) (hv : p.data.1 v r = 1) :
    shrinkingNormal p r t v = normals p v := by
  simp only [shrinkingNormal,rootDenominator,hv,mul_one]
  have hh : 1-(1-t)=t := by ring
  rw [hh,div_self ht,one_smul]

theorem shrinkingNormal_continuousAt (p : RegularData 3 V) (r : Space) (v : V)
    (hv : p.data.1 v r < 1) :
    ContinuousAt (fun t : ℝ => shrinkingNormal p r t v) 0 := by
  let f : ℝ → ℝ := fun t => t / rootDenominator p r t v
  let g : ℝ → Space := fun _ => normals p v
  have hden : Continuous (fun t : ℝ => rootDenominator p r t v) := by
    unfold rootDenominator
    fun_prop
  have hne : rootDenominator p r 0 v ≠ 0 := by
    dsimp [rootDenominator]
    linarith
  have hf : ContinuousAt f 0 := continuousAt_id.div hden.continuousAt hne
  have hg : ContinuousAt g 0 := continuousAt_const
  change ContinuousAt (f • g) 0
  exact hf.smul hg

@[simp] theorem shrinkingNormal_zero (p : RegularData 3 V) (r : Space) (v : V) :
    shrinkingNormal p r 0 v = 0 := by simp [shrinkingNormal]

/-- A nonsingular matrix acting on column vectors, with its explicit inverse. -/
def columnEquiv (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.det ≠ 0) :
    Space ≃ₗ[ℝ] Space where
  __ := Matrix.mulVecLin M
  toFun := M.mulVec
  invFun := M⁻¹.mulVec
  left_inv x := by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM),
      Matrix.one_mulVec]
  right_inv x := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM),
      Matrix.one_mulVec]

def standardCapMap : Space →ᵃ[ℝ] Space where
  toFun x := ![x 1+(1-(x 0+x 1+x 2))/3,
    x 2+(1-(x 0+x 1+x 2))/3,1-(x 0+x 1+x 2)]
  linear :=
    { toFun x := ![x 1-(x 0+x 1+x 2)/3,
        x 2-(x 0+x 1+x 2)/3,-(x 0+x 1+x 2)]
      map_add' x y := by ext i; fin_cases i <;> simp <;> ring
      map_smul' c x := by ext i; fin_cases i <;> simp <;> ring }
  map_vadd' x y := by
    ext i
    fin_cases i <;> simp [vadd_eq_add] <;> ring

def standardCapInverse (x : Space) : Space :=
  ![1-x 0-x 1-x 2/3,x 0-x 2/3,x 1-x 2/3]

theorem standardCapMap_left_inv : Function.LeftInverse standardCapInverse standardCapMap := by
  intro x
  ext i
  fin_cases i <;> simp [standardCapMap,standardCapInverse] <;> ring

theorem standardCapMap_right_inv : Function.RightInverse standardCapInverse standardCapMap := by
  intro x
  ext i
  fin_cases i <;> simp [standardCapMap,standardCapInverse] <;> ring

def standardCapEquiv : Space ≃ᵃ[ℝ] Space :=
  AffineEquiv.ofBijective ⟨standardCapMap_left_inv.injective,
    standardCapMap_right_inv.surjective⟩

@[simp] theorem standardCapEquiv_apply (x : Space) :
    standardCapEquiv x = standardCapMap x := rfl

theorem standardCapEquiv_single (j : Fin 3) :
    standardCapEquiv (Pi.single j 1) = lift (basePoint j) 0 := by
  ext i
  fin_cases i <;> fin_cases j <;>
    norm_num [standardCapEquiv_apply,standardCapMap,Pi.single_apply,lift,basePoint]

@[simp] theorem standardCapEquiv_zero :
    standardCapEquiv 0 = lift (⟨1/3,1/3⟩ : ℂ) 1 := by
  ext i
  fin_cases i <;> norm_num [standardCapEquiv_apply,standardCapMap,lift]

def rootMatrix (p : RegularData 3 V) (I : Fin 3 ↪ V) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun j => normals p (I j)

theorem rootMatrix_det (p : RegularData 3 V) (I : Fin 3 ↪ V)
    (hi : LinearIndependent ℝ (fun j => (p.data.1 (I j)).toLinearMap)) :
    (rootMatrix p I).det ≠ 0 := by
  exact facetCoefficientMatrix_det_ne_zero _ hi

def rootFrame (p : RegularData 3 V) (I : Fin 3 ↪ V)
    (hI : (rootMatrix p I).det ≠ 0) : Space ≃ᵃ[ℝ] Space :=
  ((columnEquiv (rootMatrix p I).transpose
    (by rwa [Matrix.det_transpose])).symm.toAffineEquiv).trans standardCapEquiv

theorem rootMatrix_column (p : RegularData 3 V) (I : Fin 3 ↪ V)
    (hI : (rootMatrix p I).det ≠ 0) (j : Fin 3) :
    columnEquiv (rootMatrix p I).transpose (by rwa [Matrix.det_transpose])
      (Pi.single j 1) = normals p (I j) := by
  ext k
  change ((rootMatrix p I).transpose.mulVec (Pi.single j 1)) k = normals p (I j) k
  simp [Matrix.mulVec,dotProduct,rootMatrix,Pi.single_apply]

theorem rootFrame_normal (p : RegularData 3 V) (I : Fin 3 ↪ V)
    (hI : (rootMatrix p I).det ≠ 0) (j : Fin 3) :
    rootFrame p I hI (normals p (I j)) = lift (basePoint j) 0 := by
  change standardCapEquiv ((columnEquiv (rootMatrix p I).transpose
    (by rwa [Matrix.det_transpose])).symm (normals p (I j))) = _
  rw [← rootMatrix_column p I hI j,LinearEquiv.symm_apply_apply,
    standardCapEquiv_single]

@[simp] theorem rootFrame_zero (p : RegularData 3 V) (I : Fin 3 ↪ V)
    (hI : (rootMatrix p I).det ≠ 0) :
    rootFrame p I hI 0 = lift (⟨1/3,1/3⟩ : ℂ) 1 := by
  change standardCapEquiv ((columnEquiv (rootMatrix p I).transpose
    (by rwa [Matrix.det_transpose])).symm 0) = _
  rw [map_zero,standardCapEquiv_zero]

theorem rootFrame_height (p : RegularData 3 V) (r : Space) (I : Fin 3 ↪ V)
    (hI : (rootMatrix p I).det ≠ 0) (htight : ∀ j, p.data.1 (I j) r = 1)
    (x : Space) : rootFrame p I hI x 2 = 1-rowForm r x := by
  let e := columnEquiv (rootMatrix p I).transpose
    (by rwa [Matrix.det_transpose] : (rootMatrix p I).transpose.det ≠ 0)
  let f := (rowForm r).comp e.toContinuousLinearMap
  have hf (j : Fin 3) : coefficients f j = 1 := by
    change rowForm r (e (Pi.single j 1)) = 1
    rw [rootMatrix_column p I hI j,rowForm_apply,NormalHull.dot_comm,
      ← rowForm_apply]
    simpa only [normals,rowForm_coefficients] using htight j
  have he : rowForm r x = ∑ j, (e.symm x) j := by
    calc
      rowForm r x = f (e.symm x) := by
        change rowForm r x = rowForm r (e (e.symm x))
        rw [e.apply_symm_apply]
      _ = ∑ j, (e.symm x) j := by
        rw [← coefficient_expansion f (e.symm x)]
        simp only [hf,one_mul]
  change 1-((e.symm x) 0+(e.symm x) 1+(e.symm x) 2) = _
  rw [he]
  simp [Fin.sum_univ_succ]
  <;> ring

theorem rootFrame_shrinking_eventually (p : RegularData 3 V) (r : Space)
    (I : Fin 3 ↪ V) (hI : (rootMatrix p I).det ≠ 0)
    (hstrict : ∀ v, v ∉ Set.range I → p.data.1 v r < 1) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ v, v ∉ Set.range I → ∀ j,
      0 < triangleCoordinate j (horizontal (rootFrame p I hI (shrinkingNormal p r t v))) := by
  apply Filter.eventually_all.mpr
  intro v
  by_cases hv : v ∈ Set.range I
  · exact Filter.Eventually.of_forall (fun _ h => (h hv).elim)
  have hc := (rootFrame p I hI).continuous_of_finiteDimensional.continuousAt.comp
    (shrinkingNormal_continuousAt p r v (hstrict v hv))
  have hj (j : Fin 3) : ∀ᶠ t : ℝ in 𝓝 0,
      0 < triangleCoordinate j (horizontal (rootFrame p I hI (shrinkingNormal p r t v))) := by
    have hct := (coordinate_continuous j).continuousAt.comp
      (horizontal.continuous_of_finiteDimensional.continuousAt.comp hc)
    apply hct.eventually
    apply isOpen_Ioi.mem_nhds
    change 0 < triangleCoordinate j
      (horizontal (rootFrame p I hI (shrinkingNormal p r 0 v)))
    rw [shrinkingNormal_zero,rootFrame_zero,horizontal_lift]
    fin_cases j <;> norm_num [triangleCoordinate]
  filter_upwards [Filter.eventually_all.mpr hj] with t ht _
  exact ht

end NormalProjective.CapSource
end

/- Source: Cor2Candidate/RoofTriangulation.lean -/
section
/-!
# Projecting the roof of a finite convex polytope

The input records actual supporting affine roof planes and an exact halfspace
description of a finite convex hull.  Geometric triangulation laws for the
horizontal projections are conclusions: in particular, no planar injectivity,
intersection, or coverage assumption is made here.
-/


namespace NormalProjective.Planar

open Set Finset CapCoordinates

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A face lying on an affine roof retains affine independence under
horizontal projection, because the roof graph lifts it back exactly. -/
theorem affineIndependent_horizontal_of_roof {ι : Type*} (v : ι → Space)
    (L : ℂ →ᵃ[ℝ] ℝ) (hroof : ∀ i, v i 2 = L (horizontal (v i)))
    (hv : AffineIndependent ℝ v) :
    AffineIndependent ℝ (horizontal ∘ v) := by
  apply AffineIndependent.of_comp (graphLift L)
  have heq : graphLift L ∘ (horizontal ∘ v) = v := by
    funext i
    change lift (horizontal (v i)) (L (horizontal (v i))) = v i
    rw [← hroof i, lift_horizontal]
  rwa [heq]

structure RoofHullData (V : Type*) [Fintype V] [DecidableEq V] where
  point : V → ℂ
  height : V → ℝ
  lifted_injective : Function.Injective (fun v => lift (point v) (height v))
  corner : Fin 3 ↪ V
  corner_point : ∀ j, point (corner j) = basePoint j
  boundary_zero : ∀ j, height (corner j) = 0
  interior_nonempty : ∃ v, v ∉ Set.range corner
  interior_positive : ∀ v, v ∉ Set.range corner → 0 < height v
  interior_coordinates : ∀ v, v ∉ Set.range corner →
    ∀ j, 0 < triangleCoordinate j (point v)
  faces : Finset (Finset V)
  face_card : ∀ s ∈ faces, s.card = 3
  face_independent : ∀ s ∈ faces, AffineIndependent ℝ (fun v : s => point v)
  vertex_covered : ∀ v, ∃ s ∈ faces, v ∈ s
  roof : {s : Finset V // s ∈ faces} → (ℂ →ᵃ[ℝ] ℝ)
  roof_equal : ∀ s v, v ∈ s.val → roof s (point v) = height v
  roof_strict : ∀ s v, v ∉ s.val → height v < roof s (point v)
  hull_eq : convexHull ℝ (Set.range (fun v => lift (point v) (height v))) =
    {x : Space | horizontal x ∈ baseTriangle ∧ 0 ≤ x 2 ∧
      ∀ s, x 2 ≤ roof s (horizontal x)}

namespace RoofHullData

variable (R : RoofHullData V)

abbrev Face := {s : Finset V // s ∈ R.faces}

def lifted (v : V) : Space := lift (R.point v) (R.height v)

def carrier : Set Space := convexHull ℝ (Set.range R.lifted)

def faceHull (s : R.Face) : Set Space :=
  convexHull ℝ (R.lifted '' (s.val : Set V))

theorem roof_bound (s : R.Face) (v : V) : R.height v ≤ R.roof s (R.point v) := by
  by_cases hv : v ∈ s.val
  · exact (R.roof_equal s v hv).symm.le
  · exact (R.roof_strict s v hv).le

theorem roof_tight_iff (s : R.Face) (v : V) :
    R.height v = R.roof s (R.point v) ↔ v ∈ s.val := by
  constructor
  · intro h
    by_contra hv
    exact (R.roof_strict s v hv).ne h
  · intro hv
    exact (R.roof_equal s v hv).symm

theorem linear_roof_bound (s : R.Face) (v : V) :
    roofLinear (R.roof s) (R.lifted v) ≤ R.roof s 0 := by
  rw [roofLinear_iff]
  simpa only [lifted, horizontal_lift, height_lift] using R.roof_bound s v

theorem linear_roof_tight_iff (s : R.Face) (v : V) :
    roofLinear (R.roof s) (R.lifted v) = R.roof s 0 ↔ v ∈ s.val := by
  rw [roofLinear_eq_iff]
  simpa only [lifted, horizontal_lift, height_lift] using R.roof_tight_iff s v

theorem faceHull_eq (s : R.Face) :
    R.faceHull s = {x ∈ R.carrier | roofLinear (R.roof s) x = R.roof s 0} := by
  have h := PolarFinite.supporting_face_eq R.lifted (roofLinear (R.roof s))
    (R.roof s 0) (R.linear_roof_bound s)
  have ht : {v | roofLinear (R.roof s) (R.lifted v) = R.roof s 0} =
      (s.val : Set V) := by
    ext v
    exact R.linear_roof_tight_iff s v
  simpa only [faceHull, carrier, ht] using h.symm

theorem faceHull_subset_carrier (s : R.Face) : R.faceHull s ⊆ R.carrier := by
  rw [R.faceHull_eq s]
  exact fun _ hx => hx.1

theorem carrier_below_roof (s : R.Face) {x : Space} (hx : x ∈ R.carrier) :
    x 2 ≤ R.roof s (horizontal x) := by
  apply (roofLinear_iff (R.roof s) x).mp
  exact (convexHull_min (by
      rintro _ ⟨v,rfl⟩
      exact R.linear_roof_bound s v)
    (convex_halfSpace_le (roofLinear (R.roof s)).isLinear (R.roof s 0))) hx

theorem graph_point_mem_faceHull (s : R.Face) {p : ℂ}
    (hp : p ∈ simplex R.point s.val) :
    lift p (R.roof s p) ∈ R.faceHull s := by
  apply (convexHull_min ?_
    ((convex_convexHull ℝ _).affine_preimage (graphLift (R.roof s)))) hp
  rintro _ ⟨v,hv,rfl⟩
  change lift (R.point v) (R.roof s (R.point v)) ∈ R.faceHull s
  rw [R.roof_equal s v hv]
  exact subset_convexHull ℝ _ ⟨v,hv,rfl⟩

theorem horizontal_mem_simplex {s : Finset V} {x : Space}
    (hx : x ∈ convexHull ℝ (R.lifted '' (s : Set V))) :
    horizontal x ∈ simplex R.point s := by
  apply (convexHull_min ?_
    ((convex_convexHull ℝ _).linear_preimage horizontal)) hx
  rintro _ ⟨v,hv,rfl⟩
  change horizontal (R.lifted v) ∈ simplex R.point s
  simpa only [lifted,horizontal_lift] using point_mem_simplex R.point s hv

theorem point_injective : Function.Injective R.point := by
  intro a b hab
  obtain ⟨s,hs,has⟩ := R.vertex_covered a
  obtain ⟨t,ht,hbt⟩ := R.vertex_covered b
  let s' : R.Face := ⟨s,hs⟩
  let t' : R.Face := ⟨t,ht⟩
  have ha := R.roof_bound t' a
  have hb := R.roof_bound s' b
  rw [hab,R.roof_equal t' b hbt] at ha
  rw [← hab,R.roof_equal s' a has] at hb
  have hheight : R.height a = R.height b := le_antisymm ha hb
  apply R.lifted_injective
  change lift (R.point a) (R.height a) = lift (R.point b) (R.height b)
  rw [hab,hheight]

theorem faceHull_intersection (s t : R.Face) :
    R.faceHull s ∩ R.faceHull t =
      convexHull ℝ (R.lifted '' (s.val ∩ t.val : Finset V)) := by
  let l := roofLinear (R.roof s) + roofLinear (R.roof t)
  let h := R.roof s 0 + R.roof t 0
  have hbound : ∀ v, l (R.lifted v) ≤ h := by
    intro v
    exact add_le_add (R.linear_roof_bound s v) (R.linear_roof_bound t v)
  have htight : {v | l (R.lifted v) = h} =
      (s.val ∩ t.val : Finset V) := by
    ext v
    simp only [Finset.mem_coe, Finset.mem_inter, Set.mem_setOf_eq]
    rw [← R.linear_roof_tight_iff s v, ← R.linear_roof_tight_iff t v]
    have hs := R.linear_roof_bound s v
    have ht := R.linear_roof_bound t v
    change roofLinear (R.roof s) (R.lifted v) +
        roofLinear (R.roof t) (R.lifted v) = R.roof s 0 + R.roof t 0 ↔ _
    constructor
    · intro hv
      constructor <;> linarith
    · rintro ⟨hs,ht⟩
      rw [hs,ht]
  have hface := PolarFinite.supporting_face_eq R.lifted l h hbound
  rw [htight] at hface
  rw [← hface, R.faceHull_eq s, R.faceHull_eq t]
  ext x
  change ((x ∈ R.carrier ∧ roofLinear (R.roof s) x = R.roof s 0) ∧
    x ∈ R.carrier ∧ roofLinear (R.roof t) x = R.roof t 0) ↔
    x ∈ R.carrier ∧ l x = h
  constructor
  · rintro ⟨⟨hx,hs⟩,⟨_,ht⟩⟩
    exact ⟨hx,by
      change roofLinear (R.roof s) x + roofLinear (R.roof t) x =
        R.roof s 0 + R.roof t 0
      rw [hs,ht]⟩
  · rintro ⟨hx,hxh⟩
    have hs := (roofLinear_iff (R.roof s) x).mpr (R.carrier_below_roof s hx)
    have ht := (roofLinear_iff (R.roof t) x).mpr (R.carrier_below_roof t hx)
    change roofLinear (R.roof s) x + roofLinear (R.roof t) x =
      R.roof s 0 + R.roof t 0 at hxh
    exact ⟨⟨hx,by linarith⟩,hx,by linarith⟩

/-- Projection preserves the exact common-face intersection of roof facets. -/
theorem projected_intersection (s t : R.Face) :
    simplex R.point s.val ∩ simplex R.point t.val =
      simplex R.point (s.val ∩ t.val) := by
  apply Set.Subset.antisymm
  · intro p hp
    have hs := R.graph_point_mem_faceHull s hp.1
    have ht := R.graph_point_mem_faceHull t hp.2
    have hst := R.carrier_below_roof t (R.faceHull_subset_carrier s hs)
    have hts := R.carrier_below_roof s (R.faceHull_subset_carrier t ht)
    simp only [height_lift,horizontal_lift] at hst hts
    have heq : R.roof s p = R.roof t p := le_antisymm hst hts
    have hx : lift p (R.roof s p) ∈ R.faceHull s ∩ R.faceHull t :=
      ⟨hs,by simpa only [heq] using ht⟩
    rw [R.faceHull_intersection s t] at hx
    simpa only [horizontal_lift] using R.horizontal_mem_simplex hx
  · intro p hp
    exact ⟨convexHull_mono (Set.image_mono Finset.inter_subset_left) hp,
      convexHull_mono (Set.image_mono Finset.inter_subset_right) hp⟩

theorem point_mem_baseTriangle (v : V) : R.point v ∈ baseTriangle := by
  by_cases hv : v ∈ Set.range R.corner
  · obtain ⟨j,rfl⟩ := hv
    rw [R.corner_point]
    intro k
    rw [coordinate_basePoint]
    split_ifs <;> norm_num
  · exact fun j => (R.interior_coordinates v hv j).le

theorem roof_nonnegative_on_base (s : R.Face) {p : ℂ} (hp : p ∈ baseTriangle) :
    0 ≤ R.roof s p := by
  rw [baseTriangle_eq_convexHull] at hp
  apply (convexHull_min ?_ ((convex_Ici (0 : ℝ)).affine_preimage (R.roof s))) hp
  rintro _ ⟨j,rfl⟩
  change 0 ≤ R.roof s (basePoint j)
  have h := R.roof_bound s (R.corner j)
  simpa only [R.corner_point,R.boundary_zero] using h

/-- The horizontal projections of the roof facets cover the entire base. -/
theorem projected_union : (⋃ s : R.Face, simplex R.point s.val) = baseTriangle := by
  classical
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨s,hs⟩ := mem_iUnion.mp hp
    exact (convexHull_min (by
      rintro _ ⟨v,hv,rfl⟩
      exact R.point_mem_baseTriangle v) baseTriangle_convex) hs
  · intro p hp
    obtain ⟨f,hf,hvf⟩ := R.vertex_covered (R.corner 0)
    letI : Nonempty R.Face := ⟨⟨f,hf⟩⟩
    obtain ⟨s,hs,hmin⟩ := Finset.exists_min_image (Finset.univ : Finset R.Face)
      (fun s => R.roof s p) Finset.univ_nonempty
    have hx : lift p (R.roof s p) ∈ R.carrier := by
      change lift p (R.roof s p) ∈
        convexHull ℝ (Set.range (fun v => lift (R.point v) (R.height v)))
      rw [R.hull_eq]
      simp only [Set.mem_setOf_eq,horizontal_lift,height_lift]
      exact ⟨hp,R.roof_nonnegative_on_base s hp,
        fun t => hmin t (Finset.mem_univ t)⟩
    have hxface : lift p (R.roof s p) ∈ R.faceHull s := by
      rw [R.faceHull_eq s]
      refine ⟨hx,?_⟩
      rw [roofLinear_eq_iff]
      simp
    exact mem_iUnion.mpr ⟨s,by
      simpa only [horizontal_lift] using R.horizontal_mem_simplex hxface⟩

/-- The actual projected geometric disk, with all triangulation laws derived. -/
def triangularDisk : TriangularDisk V where
  point := R.point
  point_injective := R.point_injective
  faces := R.faces
  face_card := R.face_card
  face_independent := R.face_independent
  intersection s hs t ht := R.projected_intersection ⟨s,hs⟩ ⟨t,ht⟩
  vertex_covered := R.vertex_covered
  corner := R.corner
  corner_point := R.corner_point
  domain_eq := R.projected_union
  interior_vertex := R.interior_coordinates

/-- Once the three-dimensional supporting-plane and hull data have been
established, their projection supplies a genuine strictly convex cap. -/
def strictConvexCap : StrictConvexCap V where
  disk := R.triangularDisk
  interior_nonempty := R.interior_nonempty
  height := R.height
  boundary_zero := R.boundary_zero
  interior_positive := R.interior_positive
  roof := R.roof
  roof_equal := R.roof_equal
  roof_strict := R.roof_strict

end RoofHullData

end NormalProjective.Planar
end

/- Source: Cor2Candidate/CapSourceRoof.lean -/
section
/-!
# Extracting the genuine triangular roof from the finite polar

The coordinates in `CapPosition` record only an affine placement of the
ordinary finite polar.  The roof facets, their strict supporting inequalities,
and their exact halfspace description are derived from actual vertices of the
original simple polytope.  The planar triangulation is subsequently supplied
by `RoofHullData.strictConvexCap`.
-/

open Set Finset
open scoped BigOperators Topology

namespace NormalProjective.CapSource

open CanonicalModel UnitNormalization NormalHull
open Planar Planar.CapCoordinates

variable {V : Type*} [Fintype V] [DecidableEq V]

structure CapPosition (p : RegularData 3 V) where
  root : Vertices p
  corner : Fin 3 ↪ V
  corner_tight : ∀ j, p.data.1 (corner j) root.val = p.data.2 (corner j)
  frame : Space ≃ᵃ[ℝ] Space
  corner_image : ∀ j, frame (normals p (corner j)) = lift (basePoint j) 0
  height_identity : ∀ x, frame x 2 = 1-rowForm root.val x
  projected_interior : ∀ v, v ∉ Set.range corner → ∀ j,
    0 < triangleCoordinate j (horizontal (frame (normals p v)))

namespace CapPosition

variable (p : RegularData 3 V) (hp : ∀ v, p.data.2 v = 1)
variable (hs : IsSimpleHalfspace (fun v => (p.data.1 v).toLinearMap) p.data.2)
variable (A : CapPosition p)

def lifted (v : V) : Space := A.frame (normals p v)

def point (v : V) : ℂ := horizontal (A.lifted p v)

def height (v : V) : ℝ := A.lifted p v 2

theorem lift_point_height (v : V) : lift (A.point p v) (A.height p v) = A.lifted p v :=
  lift_horizontal _

include hp in
theorem lifted_injective : Function.Injective (A.lifted p) :=
  A.frame.injective.comp (normals_injective p hp)

theorem corner_point (j : Fin 3) : A.point p (A.corner j) = basePoint j := by
  change horizontal (A.frame (normals p (A.corner j))) = _
  rw [A.corner_image,horizontal_lift]

theorem boundary_zero (j : Fin 3) : A.height p (A.corner j) = 0 := by
  change A.frame (normals p (A.corner j)) 2 = 0
  rw [A.corner_image,height_lift]

include hs in
theorem corner_range : Set.range A.corner =
    {v | p.data.1 v A.root.val = p.data.2 v} := by
  exact (simple_active_minor_spans (fun v => (p.data.1 v).toLinearMap)
    p.data.2 hs A.root.property A.corner A.corner_tight).1

include hs in
theorem mem_corner_range (v : V) :
    v ∈ Set.range A.corner ↔ p.data.1 v A.root.val = p.data.2 v := by
  simp only [A.corner_range p hs, Set.mem_setOf_eq]

theorem height_eq (v : V) : A.height p v = 1-p.data.1 v A.root.val := by
  change A.frame (normals p v) 2 = _
  rw [A.height_identity,rowForm_apply,NormalHull.dot_comm,← rowForm_apply,
    normals,rowForm_coefficients]

include hp hs in
theorem interior_positive (v : V) (hv : v ∉ Set.range A.corner) : 0 < A.height p v := by
  have hle : p.data.1 v A.root.val ≤ 1 := by
    have hh := A.root.property.1 v
    change p.data.1 v A.root.val ≤ p.data.2 v at hh
    exact hh.trans_eq (hp v)
  have hne : p.data.1 v A.root.val ≠ 1 := by
    intro he
    apply hv
    rw [A.corner_range p hs]
    exact he.trans (hp v).symm
  rw [A.height_eq p]
  exact sub_pos.mpr (lt_of_le_of_ne hle hne)

include hp in
theorem interior_nonempty : ∃ v, v ∉ Set.range A.corner := by
  by_contra! hall
  have hsub : hull (normals p) ⊆ {x : Space | rowForm A.root.val x = 1} := by
    apply convexHull_min
    · rintro _ ⟨v,rfl⟩
      obtain ⟨j,rfl⟩ := hall v
      change rowForm A.root.val (normals p (A.corner j)) = 1
      rw [rowForm_apply,NormalHull.dot_comm,← rowForm_apply,normals,rowForm_coefficients]
      exact (A.corner_tight j).trans (hp (A.corner j))
    · exact convex_hyperplane (rowForm A.root.val).toLinearMap.isLinear 1
  have hbad := hsub (interior_subset (normals_zero_interior p hp))
  exact zero_ne_one (by simpa only [map_zero,Set.mem_setOf_eq] using hbad)

theorem point_mem_base (v : V) : A.point p v ∈ baseTriangle := by
  by_cases hv : v ∈ Set.range A.corner
  · obtain ⟨j,rfl⟩ := hv
    rw [A.corner_point p]
    intro k
    rw [coordinate_basePoint]
    split_ifs <;> norm_num
  · exact fun j => (A.projected_interior v hv j).le

def dual : RegularData 3 (Vertices p) := affineRegular A.frame (dualRegular p hp)

theorem dual_slack (x : Vertices p) (v : V) :
    (A.dual p hp).data.1 x (A.lifted p v) - (A.dual p hp).data.2 x =
      p.data.1 v x.val-1 := by
  change (affineData A.frame (dualRegular p hp).data).1 x
    (A.frame (normals p v)) - (affineData A.frame (dualRegular p hp).data).2 x = _
  rw [affineData_slack,A.frame.symm_apply_apply]
  change rowForm x.val (normals p v)-1 = _
  rw [rowForm_apply,NormalHull.dot_comm,← rowForm_apply,normals,rowForm_coefficients]

theorem dual_generator_bound (x : Vertices p) (v : V) :
    (A.dual p hp).data.1 x (A.lifted p v) ≤ (A.dual p hp).data.2 x := by
  apply sub_nonpos.mp
  rw [A.dual_slack p hp]
  have hh := x.property.1 v
  change p.data.1 v x.val ≤ p.data.2 v at hh
  rw [hp] at hh
  linarith

theorem dual_generator_tight (x : Vertices p) (v : V) :
    (A.dual p hp).data.1 x (A.lifted p v) = (A.dual p hp).data.2 x ↔
      v ∈ triangleLabels p x := by
  rw [← sub_eq_zero,A.dual_slack p hp,sub_eq_zero,mem_triangleLabels,hp]

theorem dual_generator_strict (x : Vertices p) (v : V)
    (hv : v ∉ triangleLabels p x) :
    (A.dual p hp).data.1 x (A.lifted p v) < (A.dual p hp).data.2 x := by
  exact lt_of_le_of_ne (A.dual_generator_bound p hp x v)
    (fun h => hv ((A.dual_generator_tight p hp x v).mp h))

theorem carrier_eq_dual : convexHull ℝ (Set.range (A.lifted p)) =
    dataRegion (A.dual p hp).data := by
  change _ = dataRegion (affineData A.frame (dualRegular p hp).data)
  rw [dataRegion_affineData]
  change convexHull ℝ (Set.range (A.lifted p)) = A.frame '' dataRegion (dualData p)
  rw [dual_region p hp]
  have hh := A.frame.toAffineMap.image_convexHull (Set.range (normals p))
  have hr : A.frame.toAffineMap '' Set.range (normals p) = Set.range (A.lifted p) := by
    rw [← Set.range_comp'] <;> rfl
  rw [hr] at hh
  exact hh.symm

theorem root_slack (x : Space) :
    (A.dual p hp).data.1 A.root x - (A.dual p hp).data.2 A.root = -x 2 := by
  change (affineData A.frame (dualRegular p hp).data).1 A.root x -
    (affineData A.frame (dualRegular p hp).data).2 A.root = _
  rw [affineData_slack]
  change rowForm A.root.val (A.frame.symm x)-1 = _
  have hh := A.height_identity (A.frame.symm x)
  rw [A.frame.apply_symm_apply] at hh
  linarith

include hs in
theorem labels_root : triangleLabels p A.root = Finset.univ.image A.corner := by
  ext v
  rw [mem_triangleLabels,← A.mem_corner_range p hs]
  simp

include hs in
theorem nonroot_face_has_interior (x : Vertices p) (hx : x ≠ A.root) :
    ∃ v ∈ triangleLabels p x, v ∉ Set.range A.corner := by
  by_contra! hnot
  have hsub : triangleLabels p x ⊆ triangleLabels p A.root := by
    intro v hv
    rw [mem_triangleLabels,← A.mem_corner_range p hs]
    exact hnot v hv
  have heq := Finset.eq_of_subset_of_card_le hsub
    (by rw [triangleLabels_card p hs,triangleLabels_card p hs])
  exact hx (triangleLabels_injective p heq)

include hs in
theorem nonroot_face_misses_corner (x : Vertices p) (hx : x ≠ A.root) :
    ∃ j, A.corner j ∉ triangleLabels p x := by
  by_contra! hnot
  have hsub : triangleLabels p A.root ⊆ triangleLabels p x := by
    intro v hv
    rw [mem_triangleLabels,← A.mem_corner_range p hs] at hv
    obtain ⟨j,rfl⟩ := hv
    exact hnot j
  have heq := Finset.eq_of_subset_of_card_le hsub
    (by rw [triangleLabels_card p hs,triangleLabels_card p hs])
  exact hx (triangleLabels_injective p heq).symm

theorem base_barycentric (z : ℂ) :
    lift z 0 = ∑ j : Fin 3, triangleCoordinate j z • lift (basePoint j) 0 := by
  ext i
  fin_cases i <;> simp [Fin.sum_univ_succ,triangleCoordinate,basePoint,lift]
  <;> ring

include hs in
theorem strict_at_base (x : Vertices p) (hx : x ≠ A.root) {z : ℂ}
    (hz : ∀ j, 0 < triangleCoordinate j z) :
    (A.dual p hp).data.1 x (lift z 0) < (A.dual p hp).data.2 x := by
  obtain ⟨j,hj⟩ := A.nonroot_face_misses_corner p hs x hx
  have hstrict := A.dual_generator_strict p hp x (A.corner j) hj
  have hle (k : Fin 3) := A.dual_generator_bound p hp x (A.corner k)
  have hsum : (∑ k : Fin 3, triangleCoordinate k z *
      (A.dual p hp).data.1 x (A.lifted p (A.corner k))) <
      ∑ k : Fin 3, triangleCoordinate k z * (A.dual p hp).data.2 x := by
    apply Finset.sum_lt_sum
    · intro k hk
      exact mul_le_mul_of_nonneg_left (hle k) (hz k).le
    · exact ⟨j,Finset.mem_univ j,mul_lt_mul_of_pos_left hstrict (hz j)⟩
  have he (k : Fin 3) : A.lifted p (A.corner k) = lift (basePoint k) 0 :=
    A.corner_image k
  simp only [he] at hsum
  rw [← Finset.sum_mul,coordinate_sum,one_mul] at hsum
  rw [base_barycentric z,map_sum]
  simpa only [map_smul,smul_eq_mul] using hsum

theorem linear_vertical (u : Space →L[ℝ] ℝ) (x : Space) :
    u x = u (lift (horizontal x) 0) + x 2 * coefficients u 2 := by
  have he : x = lift (horizontal x) 0 + x 2 • Pi.single 2 1 := by
    ext i
    fin_cases i <;> simp [lift,horizontal,Pi.single_apply]
  calc
    u x = u (lift (horizontal x) 0 + x 2 • Pi.single 2 1) := congrArg u he
    _ = u (lift (horizontal x) 0) + x 2 * coefficients u 2 := by
      rw [map_add,map_smul] <;> rfl

include hs in
theorem vertical_coefficient_pos (x : Vertices p) (hx : x ≠ A.root) :
    0 < coefficients ((A.dual p hp).data.1 x) 2 := by
  obtain ⟨v,hv,hvB⟩ := A.nonroot_face_has_interior p hs x hx
  have he := (A.dual_generator_tight p hp x v).mpr hv
  have hbase := A.strict_at_base p hp hs x hx (A.projected_interior v hvB)
  change (A.dual p hp).data.1 x (lift (A.point p v) 0) <
    (A.dual p hp).data.2 x at hbase
  have hz := A.interior_positive p hp hs v hvB
  have hexp := linear_vertical ((A.dual p hp).data.1 x) (A.lifted p v)
  change (A.dual p hp).data.1 x (A.lifted p v) =
    (A.dual p hp).data.1 x (lift (A.point p v) 0) +
      A.height p v * coefficients ((A.dual p hp).data.1 x) 2 at hexp
  have hm : 0 < A.height p v * coefficients ((A.dual p hp).data.1 x) 2 := by
    linarith
  exact (mul_pos_iff_of_pos_left hz).mp hm

end CapPosition

def planeRoof (u : Space →L[ℝ] ℝ) (h : ℝ) : ℂ →ᵃ[ℝ] ℝ where
  toFun z := (h-coefficients u 0*z.re-coefficients u 1*z.im)/coefficients u 2
  linear := (coefficients u 2)⁻¹ •
    ((-coefficients u 0) • Complex.reCLM.toLinearMap +
      (-coefficients u 1) • Complex.imCLM.toLinearMap)
  map_vadd' x y := by
    simp only [vadd_eq_add,Complex.add_re,Complex.add_im,LinearMap.smul_apply,
      LinearMap.add_apply,ContinuousLinearMap.coe_coe,Complex.reCLM_apply,
      Complex.imCLM_apply,smul_eq_mul]
    ring

theorem linear_coordinates (u : Space →L[ℝ] ℝ) (x : Space) :
    u x = coefficients u 0*x 0 + coefficients u 1*x 1 + coefficients u 2*x 2 := by
  rw [← coefficient_expansion u x]
  simp [Fin.sum_univ_succ]
  <;> ring

theorem planeRoof_le_iff (u : Space →L[ℝ] ℝ) (h : ℝ)
    (hu : 0 < coefficients u 2) (x : Space) :
    x 2 ≤ planeRoof u h (horizontal x) ↔ u x ≤ h := by
  change x 2 ≤ (h-coefficients u 0*x 0-coefficients u 1*x 1)/coefficients u 2 ↔ _
  rw [le_div_iff₀ hu,linear_coordinates]
  constructor <;> intro hh <;> nlinarith

theorem planeRoof_eq_iff (u : Space →L[ℝ] ℝ) (h : ℝ)
    (hu : 0 < coefficients u 2) (x : Space) :
    planeRoof u h (horizontal x) = x 2 ↔ u x = h := by
  change (h-coefficients u 0*x 0-coefficients u 1*x 1)/coefficients u 2 = x 2 ↔ _
  rw [div_eq_iff hu.ne',linear_coordinates]
  constructor <;> intro hh <;> nlinarith

theorem planeRoof_lt_iff (u : Space →L[ℝ] ℝ) (h : ℝ)
    (hu : 0 < coefficients u 2) (x : Space) :
    x 2 < planeRoof u h (horizontal x) ↔ u x < h := by
  change x 2 < (h-coefficients u 0*x 0-coefficients u 1*x 1)/coefficients u 2 ↔ _
  rw [lt_div_iff₀ hu,linear_coordinates]
  constructor <;> intro hh <;> nlinarith

namespace CapPosition

variable (p : RegularData 3 V) (hp : ∀ v, p.data.2 v = 1)
variable (hs : IsSimpleHalfspace (fun v => (p.data.1 v).toLinearMap) p.data.2)
variable (A : CapPosition p)

def faces : Finset (Finset V) := by
  classical
  exact (Finset.univ.erase A.root).image (triangleLabels p)

abbrev Face := {s : Finset V // s ∈ A.faces p}

theorem mem_faces (s : Finset V) : s ∈ A.faces p ↔
    ∃ x : Vertices p, x ≠ A.root ∧ triangleLabels p x = s := by
  simp only [faces,Finset.mem_image,Finset.mem_erase,Finset.mem_univ,and_true]

def faceVertex (s : A.Face p) : Vertices p :=
  ((A.mem_faces p s.val).mp s.property).choose

theorem faceVertex_ne (s : A.Face p) : A.faceVertex p s ≠ A.root :=
  ((A.mem_faces p s.val).mp s.property).choose_spec.1

theorem faceVertex_labels (s : A.Face p) : triangleLabels p (A.faceVertex p s) = s.val :=
  ((A.mem_faces p s.val).mp s.property).choose_spec.2

include hs in
theorem face_card (s : Finset V) (hs' : s ∈ A.faces p) : s.card = 3 := by
  obtain ⟨x,hx,rfl⟩ := (A.mem_faces p s).mp hs'
  exact triangleLabels_card p hs x

def roof (s : A.Face p) : ℂ →ᵃ[ℝ] ℝ :=
  planeRoof ((A.dual p hp).data.1 (A.faceVertex p s))
    ((A.dual p hp).data.2 (A.faceVertex p s))

include hs in
theorem roof_equal (s : A.Face p) (v : V) (hv : v ∈ s.val) :
    A.roof p hp s (A.point p v) = A.height p v := by
  apply (planeRoof_eq_iff _ _
    (A.vertical_coefficient_pos p hp hs _ (A.faceVertex_ne p s)) (A.lifted p v)).mpr
  apply (A.dual_generator_tight p hp _ v).mpr
  rwa [A.faceVertex_labels p s]

include hs in
theorem roof_strict (s : A.Face p) (v : V) (hv : v ∉ s.val) :
    A.height p v < A.roof p hp s (A.point p v) := by
  apply (planeRoof_lt_iff _ _
    (A.vertical_coefficient_pos p hp hs _ (A.faceVertex_ne p s)) (A.lifted p v)).mpr
  apply A.dual_generator_strict p hp
  rwa [A.faceVertex_labels p s]

theorem vertex_covered (v : V) : ∃ s ∈ A.faces p, v ∈ s := by
  obtain ⟨x,hx,hv⟩ := facet_has_nonroot_vertex p A.root v
  exact ⟨triangleLabels p x,(A.mem_faces p _).mpr ⟨x,hx,rfl⟩,
    (mem_triangleLabels p x v).mpr hv⟩

include hs in
theorem normals_face_independent (x : Vertices p) :
    AffineIndependent ℝ (fun v : triangleLabels p x => normals p v.val) := by
  let f := fun v => (p.data.1 v).toLinearMap
  obtain ⟨I,hI,hind⟩ := extremePoint_has_active_basis f p.data.2 x.property
  have hsp := simple_active_minor_spans f p.data.2 hs x.property I hI
  let e : Fin 3 → triangleLabels p x :=
    fun j => ⟨I j,(mem_triangleLabels p x (I j)).mpr (hI j)⟩
  have he : Function.Bijective e := by
    constructor
    · intro j k hjk
      exact I.injective (congrArg Subtype.val hjk)
    · intro v
      have hv : v.val ∈ Set.range I := by
        rw [hsp.1]
        exact (mem_triangleLabels p x v.val).mp v.property
      obtain ⟨j,hj⟩ := hv
      exact ⟨j,Subtype.ext hj⟩
  have hlin : LinearIndependent ℝ (fun j => normals p (I j)) := by
    apply Matrix.linearIndependent_row_iff_isUnit.mpr
    exact (Matrix.isUnit_iff_isUnit_det (rootMatrix p I)).mpr (isUnit_iff_ne_zero.mpr
      (rootMatrix_det p I hind))
  have ha := hlin.affineIndependent
  exact (affineIndependent_equiv (Equiv.ofBijective e he)).mp ha

include hp hs in
theorem face_independent (s : Finset V) (hs' : s ∈ A.faces p) :
    AffineIndependent ℝ (fun v : s => A.point p v.val) := by
  let s' : A.Face p := ⟨s,hs'⟩
  have hnorm : AffineIndependent ℝ (fun v : s => normals p v.val) := by
    have hlabels : triangleLabels p (A.faceVertex p s') = s := A.faceVertex_labels p s'
    rw [← hlabels]
    exact normals_face_independent p hs (A.faceVertex p s')
  have hlift := hnorm.map' A.frame.toAffineMap A.frame.injective
  apply affineIndependent_horizontal_of_roof (fun v : s => A.lifted p v.val)
    (A.roof p hp s')
  · intro v
    exact (A.roof_equal p hp hs s' v.val v.property).symm
  · exact hlift

include hs in
theorem hull_eq : convexHull ℝ (Set.range (fun v => lift (A.point p v) (A.height p v))) =
    {x : Space | horizontal x ∈ baseTriangle ∧ 0 ≤ x 2 ∧
      ∀ s : A.Face p, x 2 ≤ A.roof p hp s (horizontal x)} := by
  simp only [A.lift_point_height p]
  ext x
  constructor
  · intro hx
    have hxD := (A.carrier_eq_dual p hp) ▸ hx
    refine ⟨?_,?_,?_⟩
    · apply (convexHull_min ?_ (baseTriangle_convex.linear_preimage horizontal)) hx
      rintro _ ⟨v,rfl⟩
      exact A.point_mem_base p v
    · have hh := hxD A.root
      change (A.dual p hp).data.1 A.root x ≤ (A.dual p hp).data.2 A.root at hh
      have hsl := A.root_slack p hp x
      linarith
    · intro s
      exact (planeRoof_le_iff _ _
        (A.vertical_coefficient_pos p hp hs _ (A.faceVertex_ne p s)) x).mpr
        (hxD (A.faceVertex p s))
  · rintro ⟨hxB,hxz,hxr⟩
    rw [A.carrier_eq_dual p hp]
    intro v
    change (A.dual p hp).data.1 v x ≤ (A.dual p hp).data.2 v
    by_cases hv : v = A.root
    · subst v
      have hsl := A.root_slack p hp x
      linarith
    · let s : A.Face p := ⟨triangleLabels p v,(A.mem_faces p _).mpr ⟨v,hv,rfl⟩⟩
      have hsV : A.faceVertex p s = v :=
        triangleLabels_injective p (A.faceVertex_labels p s)
      have hh := (planeRoof_le_iff _ _
        (A.vertical_coefficient_pos p hp hs _ (A.faceVertex_ne p s)) x).mp (hxr s)
      simpa only [hsV] using hh

def roofHullData : RoofHullData V where
  point := A.point p
  height := A.height p
  lifted_injective := by
    simpa only [A.lift_point_height p] using A.lifted_injective p hp
  corner := A.corner
  corner_point := A.corner_point p
  boundary_zero := A.boundary_zero p
  interior_nonempty := A.interior_nonempty p hp
  interior_positive := A.interior_positive p hp hs
  interior_coordinates := A.projected_interior
  faces := A.faces p
  face_card := A.face_card p hs
  face_independent := A.face_independent p hp hs
  vertex_covered := A.vertex_covered p
  roof := A.roof p hp
  roof_equal := A.roof_equal p hp hs
  roof_strict := A.roof_strict p hp hs
  hull_eq := A.hull_eq p hp hs

def strictConvexCap : StrictConvexCap V := (A.roofHullData p hp hs).strictConvexCap

end CapPosition
end NormalProjective.CapSource
end

/- Source: Cor2Candidate/CapSourcePosition.lean -/
section
/-!
# Every normalized simple three-polytope admits the cap placement

The choice of root vertex and of its three labelled facets is explicit, so
corresponding realizations can use the same boundary labels.  All coordinate
requirements of `CapPosition` follow from the preceding affine construction.
-/

open Set Finset Filter
open scoped BigOperators Topology

namespace NormalProjective.CapSource

open CanonicalModel UnitNormalization NormalHull
open Planar Planar.CapCoordinates

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_small_positive {P : ℝ → Prop} (hP : ∀ᶠ t in 𝓝 (0 : ℝ), P t) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ P t := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hP
  let t := min (ε/2) (1/2 : ℝ)
  have ht : 0 < t := lt_min (by linarith) (by norm_num)
  have ht1 : t ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hte : t < ε := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨t,ht,ht1,hball ?_⟩
  rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht]
  exact hte

def shrinkRoot (p : RegularData 3 V) (hp : ∀ v, p.data.2 v = 1)
    (r : Vertices p) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    Vertices (shrinkRegular p hp r.val r.property.1 t ht ht1) := by
  refine ⟨r.val,?_⟩
  change r.val ∈ (dataRegion (scaleData
    (affineRegular (rootExpansion r.val t ht.ne') p).data
    (fun v => (rootDenominator p r.val t v)⁻¹))).extremePoints ℝ
  rw [dataRegion_scaleData _ _
    (fun v => inv_pos.mpr (rootDenominator_pos p hp r.property.1 ht ht1 v))]
  change r.val ∈ (dataRegion (affineData (rootExpansion r.val t ht.ne') p.data)).extremePoints ℝ
  rw [dataRegion_affineData,← affine_image_extremePoints]
  exact ⟨r.val,r.property,rootExpansion_root r.val t ht.ne'⟩

theorem shrinkRegular_simple (p : RegularData 3 V) (hp : ∀ v, p.data.2 v = 1)
    (hs : IsSimpleHalfspace (fun v => (p.data.1 v).toLinearMap) p.data.2)
    (r : Vertices p) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    IsSimpleHalfspace
      (fun v => ((shrinkRegular p hp r.val r.property.1 t ht ht1).data.1 v).toLinearMap)
      (shrinkRegular p hp r.val r.property.1 t ht ht1).data.2 := by
  apply (simple_iff_raw _).mp
  have hsimple : (presentation p).Simple := (simple_iff_raw p).mpr hs
  apply hsimple.of_sameLabelledType
  have htype := affinePresentation_sameLabelledType
    (rootExpansion r.val t ht.ne') (presentation p)
  exact (shrinkRegular_presentation p hp r.val r.property.1 t ht ht1).symm ▸ htype

/-- The cap placement is produced from an arbitrary input and an arbitrary
chosen ordering of the three facets at its chosen vertex. -/
theorem exists_position_at_root (p : RegularData 3 V) (hp : ∀ v, p.data.2 v = 1)
    (hs : IsSimpleHalfspace (fun v => (p.data.1 v).toLinearMap) p.data.2)
    (r : Vertices p) (I : Fin 3 ↪ V)
    (hI : ∀ j, p.data.1 (I j) r.val = p.data.2 (I j)) :
    ∃ (q : RegularData 3 V) (hq : ∀ v, q.data.2 v = 1)
      (hqS : IsSimpleHalfspace (fun v => (q.data.1 v).toLinearMap) q.data.2)
      (A : CapPosition q) (a : Space ≃ᵃ[ℝ] Space),
      A.corner = I ∧ triangleLabels q A.root = triangleLabels p r ∧
      presentation q = affinePresentation a (presentation p) := by
  have hsp := simple_active_minor_spans (fun v => (p.data.1 v).toLinearMap)
    p.data.2 hs r.property I hI
  have hdet : (rootMatrix p I).det ≠ 0 := hsp.2
  have htight : ∀ j, p.data.1 (I j) r.val = 1 := fun j => (hI j).trans (hp (I j))
  have hstrict (v : V) (hv : v ∉ Set.range I) : p.data.1 v r.val < 1 := by
    have hle := r.property.1 v
    change p.data.1 v r.val ≤ p.data.2 v at hle
    rw [hp v] at hle
    apply lt_of_le_of_ne hle
    intro he
    apply hv
    rw [hsp.1]
    exact he.trans (hp v).symm
  obtain ⟨t,ht,ht1,hproj⟩ := exists_small_positive
    (rootFrame_shrinking_eventually p r.val I hdet hstrict)
  let q := shrinkRegular p hp r.val r.property.1 t ht ht1
  have hq : ∀ v, q.data.2 v = 1 := shrinkRegular_support p hp r.val r.property.1 t ht ht1
  have hqN : normals q = shrinkingNormal p r.val t :=
    shrinkRegular_normals p hp r.val r.property.1 t ht ht1
  let rq : Vertices q := shrinkRoot p hp r t ht ht1
  have hIq (j : Fin 3) : q.data.1 (I j) rq.val = q.data.2 (I j) := by
    rw [hq,← rowForm_coefficients (q.data.1 (I j))]
    change rowForm (normals q (I j)) r.val = 1
    rw [hqN,shrinkingNormal_tight p r.val t ht.ne' (I j) (htight j),
      normals,rowForm_coefficients]
    exact htight j
  let A : CapPosition q :=
    { root := rq
      corner := I
      corner_tight := hIq
      frame := rootFrame p I hdet
      corner_image := by
        intro j
        rw [hqN,shrinkingNormal_tight p r.val t ht.ne' (I j) (htight j)]
        exact rootFrame_normal p I hdet j
      height_identity := rootFrame_height p r.val I hdet htight
      projected_interior := by
        intro v hv j
        rw [hqN]
        exact hproj v hv j }
  have hqS := shrinkRegular_simple p hp hs r t ht ht1
  refine ⟨q,hq,hqS,A,rootExpansion r.val t ht.ne',rfl,?_,
    shrinkRegular_presentation p hp r.val r.property.1 t ht ht1⟩
  rw [A.labels_root q hqS]
  ext v
  rw [mem_triangleLabels]
  change v ∈ Finset.univ.image I ↔
    v ∈ activeFacetSet (fun v => (p.data.1 v).toLinearMap) p.data.2 r.val
  rw [← hsp.1]
  simp

theorem exists_position (p : RegularData 3 V) (hp : ∀ v, p.data.2 v = 1)
    (hs : IsSimpleHalfspace (fun v => (p.data.1 v).toLinearMap) p.data.2) :
    ∃ (q : RegularData 3 V) (hq : ∀ v, q.data.2 v = 1)
      (hqS : IsSimpleHalfspace (fun v => (q.data.1 v).toLinearMap) q.data.2)
      (A : CapPosition q) (a : Space ≃ᵃ[ℝ] Space),
      presentation q = affinePresentation a (presentation p) := by
  obtain ⟨r⟩ := vertices_nonempty p
  obtain ⟨I,hI,hi⟩ := extremePoint_has_active_basis
    (fun v => (p.data.1 v).toLinearMap) p.data.2 r.property
  obtain ⟨q,hq,hqS,A,a,hc,hr,he⟩ := exists_position_at_root p hp hs r I hI
  exact ⟨q,hq,hqS,A,a,he⟩

end NormalProjective.CapSource
end

/- Source: Cor2Candidate/CapSourceEndpoint.lean -/
section
/-!
# Returning from the cap to the original labelled polytope

An affine change of a finite polar is realized on the primal by an admissible
elementary projectivity followed by an invertible linear map.  This file makes
that statement exact at the level of the manuscript's facet presentations.
-/

open Set
open scoped BigOperators Topology

namespace NormalProjective.CapSource

open CanonicalModel UnitNormalization NormalHull CanonicalModel.Realization
open Planar Planar.CapCoordinates

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The inverse transpose, defined without choosing a second matrix basis. -/
def dualLinear (e : Space ≃ₗ[ℝ] Space) : Space ≃ₗ[ℝ] Space where
  toFun x := coefficients ((rowForm x).comp e.symm.toContinuousLinearMap)
  invFun x := coefficients ((rowForm x).comp e.toContinuousLinearMap)
  map_add' x y := by
    ext j
    change rowForm (x+y) (e.symm (Pi.single j 1)) =
      rowForm x (e.symm (Pi.single j 1)) + rowForm y (e.symm (Pi.single j 1))
    simp only [rowForm_apply,CanonicalModel.dot,Pi.add_apply,add_mul,Finset.sum_add_distrib]
  map_smul' c x := by
    ext j
    change rowForm (c • x) (e.symm (Pi.single j 1)) =
      c * rowForm x (e.symm (Pi.single j 1))
    simp only [rowForm_apply,CanonicalModel.dot,Pi.smul_apply,smul_eq_mul,
      Finset.mul_sum,mul_assoc]
  left_inv x := by
    ext j
    change rowForm (coefficients ((rowForm x).comp e.symm.toContinuousLinearMap))
      (e (Pi.single j 1)) = x j
    rw [rowForm_coefficients]
    change rowForm x (e.symm (e (Pi.single j 1))) = x j
    rw [e.symm_apply_apply]
    exact congrFun (coefficients_rowForm x) j
  right_inv x := by
    ext j
    change rowForm (coefficients ((rowForm x).comp e.toContinuousLinearMap))
      (e.symm (Pi.single j 1)) = x j
    rw [rowForm_coefficients]
    change rowForm x (e (e.symm (Pi.single j 1))) = x j
    rw [e.apply_symm_apply]
    exact congrFun (coefficients_rowForm x) j

theorem pairing_dualLinear (e : Space ≃ₗ[ℝ] Space) (v x : Space) :
    rowForm (e v) (dualLinear e x) = rowForm v x := by
  calc
    rowForm (e v) (dualLinear e x) =
        dot (e v) (coefficients ((rowForm x).comp e.symm.toContinuousLinearMap)) :=
      rowForm_apply _ _
    _ = rowForm x (e.symm (e v)) := coefficients_pairing _ _
    _ = rowForm v x := by
      rw [e.symm_apply_apply]
      simp only [rowForm_apply,NormalHull.dot_comm]

theorem pairing_dualLinear_symm (e : Space ≃ₗ[ℝ] Space) (v x : Space) :
    rowForm v ((dualLinear e).symm x) = rowForm (e v) x := by
  have hh := pairing_dualLinear e v ((dualLinear e).symm x)
  rw [(dualLinear e).apply_symm_apply] at hh
  exact hh.symm

theorem rowForm_sub_vectors (x y : Space) : rowForm (x-y) = rowForm x-rowForm y := by
  ext z
  simp only [rowForm_apply,CanonicalModel.dot,Pi.sub_apply,sub_mul,
    Finset.sum_sub_distrib,ContinuousLinearMap.sub_apply]

namespace CapPosition

variable (p : RegularData 3 V) (hp : ∀ v, p.data.2 v = 1)
variable (hs : IsSimpleHalfspace (fun v => (p.data.1 v).toLinearMap) p.data.2)
variable (A : CapPosition p)

theorem cap_lifted (v : V) : (A.strictConvexCap p hp hs).lifted v = A.lifted p v :=
  A.lift_point_height p v

theorem cap_carrier_image : (A.strictConvexCap p hp hs).carrier =
    A.frame '' hull (normals p) := by
  change convexHull ℝ (Set.range (A.strictConvexCap p hp hs).lifted) = _
  have hlift : (A.strictConvexCap p hp hs).lifted = A.lifted p := by
    funext v
    exact A.cap_lifted p hp hs v
  rw [hlift]
  have hh := A.frame.toAffineMap.image_convexHull (Set.range (normals p))
  have he : A.frame.toAffineMap '' Set.range (normals p) = Set.range (A.lifted p) := by
    rw [← Set.range_comp'] <;> rfl
  rw [he] at hh
  exact hh.symm

def sourceCenter (v₀ : V) : Space := A.frame.symm ((A.strictConvexCap p hp hs).centerAt v₀)

theorem sourceCenter_interior (v₀ : V)
    (hv₀ : v₀ ∉ (A.strictConvexCap p hp hs).disk.boundary) :
    A.sourceCenter p hp hs v₀ ∈ interior (hull (normals p)) := by
  have hc := (A.strictConvexCap p hp hs).centerAt_interior v₀ hv₀
  rw [A.cap_carrier_image p hp hs] at hc
  change (A.strictConvexCap p hp hs).centerAt v₀ ∈
    interior (A.frame.toHomeomorphOfFiniteDimensional '' hull (normals p)) at hc
  rw [← A.frame.toHomeomorphOfFiniteDimensional.image_interior] at hc
  obtain ⟨y,hy,he⟩ := hc
  change A.frame y = (A.strictConvexCap p hp hs).centerAt v₀ at he
  have heq : A.sourceCenter p hp hs v₀ = y := by
    change A.frame.symm _ = y
    rw [← he]
    exact A.frame.symm_apply_apply y
  rwa [heq]

theorem centered_normal (v₀ v : V) :
    (A.strictConvexCap p hp hs).centeredNormal v₀ v =
      A.frame.linear (normals p v-A.sourceCenter p hp hs v₀) := by
  rw [StrictConvexCap.centeredNormal,A.cap_lifted p hp hs]
  have he := A.frame.toAffineMap.linear_apply_vsub (normals p v) (A.sourceCenter p hp hs v₀)
  change A.frame.linear (normals p v-A.sourceCenter p hp hs v₀) =
    A.frame (normals p v)-A.frame (A.sourceCenter p hp hs v₀) at he
  rw [he]
  change A.frame (normals p v)-_ = A.frame (normals p v)-A.frame (A.frame.symm _)
  rw [A.frame.apply_symm_apply]

theorem sourceCenter_denominator (v₀ : V)
    (hv₀ : v₀ ∉ (A.strictConvexCap p hp hs).disk.boundary) :
    ∀ x ∈ dataRegion p.data, 0 < 1+(-rowForm (A.sourceCenter p hp hs v₀)) x := by
  intro x hx
  have hh := interior_center_denominator (normals p)
    (A.sourceCenter_interior p hp hs v₀ hv₀)
    (by rwa [primal_normals p hp])
  simpa only [ContinuousLinearMap.neg_apply,rowForm_apply,sub_eq_add_neg] using hh

def translatedPrimal (v₀ : V)
    (hv₀ : v₀ ∉ (A.strictConvexCap p hp hs).disk.boundary) : RegularData 3 V :=
  elementaryRegular p (-rowForm (A.sourceCenter p hp hs v₀))
    (fun v => by rw [hp]; exact zero_lt_one)
    (A.sourceCenter_denominator p hp hs v₀ hv₀)

theorem cap_polarRegular_eq (v₀ : V)
    (hv₀ : v₀ ∉ (A.strictConvexCap p hp hs).disk.boundary) :
    (A.strictConvexCap p hp hs).polarRegular v₀ hv₀ =
      affineRegular (dualLinear A.frame.linear).toAffineEquiv
        (A.translatedPrimal p hp hs v₀ hv₀) := by
  apply MatrixRealization.regularData_ext
  apply Prod.ext
  · funext v
    apply ContinuousLinearMap.ext
    intro x
    change rowForm ((A.strictConvexCap p hp hs).centeredNormal v₀ v) x =
      (p.data.1 v+p.data.2 v • (-rowForm (A.sourceCenter p hp hs v₀)))
        ((dualLinear A.frame.linear).symm x)
    rw [hp,one_smul,A.centered_normal p hp hs,
      ← pairing_dualLinear_symm,rowForm_sub_vectors,normals,rowForm_coefficients]
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.neg_apply,sub_eq_add_neg]
  · funext v
    change 1 = p.data.2 v-
      (p.data.1 v+p.data.2 v • (-rowForm (A.sourceCenter p hp hs v₀)))
        ((dualLinear A.frame.linear).symm 0)
    rw [map_zero,map_zero,hp,sub_zero]

theorem cap_polar_sameLabelledType (v₀ : V)
    (hv₀ : v₀ ∉ (A.strictConvexCap p hp hs).disk.boundary) :
    (presentation p).SameLabelledType
      (presentation ((A.strictConvexCap p hp hs).polarRegular v₀ hv₀)) := by
  rw [A.cap_polarRegular_eq p hp hs v₀ hv₀]
  exact (elementaryRegular_type p _ _ _).trans
    (affineRegular_sameLabelledType _ _)

/-- The polar of the constructed cap is PN-related to the actual source,
with the source's own labelled face lattice as reference. -/
theorem pnRelated_cap_polar (v₀ : V)
    (hv₀ : v₀ ∉ (A.strictConvexCap p hp hs).disk.boundary) :
    PNRelated
      (⟨presentation p,Presentation.sameLabelledType_refl _⟩ : Realization (presentation p))
      ⟨presentation ((A.strictConvexCap p hp hs).polarRegular v₀ hv₀),
        A.cap_polar_sameLabelledType p hp hs v₀ hv₀⟩ := by
  let q := A.translatedPrimal p hp hs v₀ hv₀
  have htype : (presentation p).SameLabelledType (presentation q) :=
    elementaryRegular_type p _ _ _
  let Q : Realization (presentation p) := ⟨presentation q,htype⟩
  have hjoin : Joined
      (⟨presentation p,Presentation.sameLabelledType_refl _⟩ : Realization (presentation p)) Q :=
    elementary_joined p (Presentation.sameLabelledType_refl _) _ _ _
  have hPN : PNRelated
      (⟨presentation p,Presentation.sameLabelledType_refl _⟩ : Realization (presentation p)) Q := by
    apply (pnRelated_iff_same_component ((simple_iff_raw p).mpr hs) _ _).mpr
    exact pathComponent_subset_component _ (hjoin.map continuous_affineClass)
  have hA := affineAction_related (dualLinear A.frame.linear).toAffineEquiv Q
  have htarget : affineAction (dualLinear A.frame.linear).toAffineEquiv Q =
      (⟨presentation ((A.strictConvexCap p hp hs).polarRegular v₀ hv₀),
        A.cap_polar_sameLabelledType p hp hs v₀ hv₀⟩ : Realization (presentation p)) := by
    apply Subtype.ext
    change affinePresentation (dualLinear A.frame.linear).toAffineEquiv (presentation q) =
      presentation ((A.strictConvexCap p hp hs).polarRegular v₀ hv₀)
    rw [A.cap_polarRegular_eq p hp hs v₀ hv₀,affineRegular_presentation]
  rw [htarget] at hA
  exact hPN.trans hA.pnRelated

end CapPosition
end NormalProjective.CapSource
end

/- Source: Cor2Candidate/CapCompatibility.lean -/
section
/-!
# Matching the labelled triangulations extracted from two realizations

Vertex incidence patterns are transported through the actual face order
isomorphism.  Removing corresponding root vertices therefore removes exactly
the same labelled triangle from the two polar boundaries.
-/

open Set Finset

namespace NormalProjective.CapSource

open CanonicalModel UnitNormalization
open Planar Planar.CapCoordinates

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem vertex_patterns_equiv (p q : RegularData 3 V)
    (htype : (presentation p).SameLabelledType (presentation q)) :
    ∃ e : Vertices p ≃ Vertices q, ∀ x, triangleLabels q (e x) = triangleLabels p x := by
  obtain ⟨e,he⟩ := sameLabelledType_raw p q htype
  let f := fun v => (p.data.1 v).toLinearMap
  let g := fun v => (q.data.1 v).toLinearMap
  let ev := faceIsoVertexEquiv f g p.data.2 q.data.2 p.compact q.compact e
  refine ⟨ev,fun x => ?_⟩
  ext v
  rw [mem_triangleLabels,mem_triangleLabels]
  exact (faceIsoVertexEquiv_incidence f g p.data.2 q.data.2 p.compact q.compact e he x v).symm

theorem positions_same_faces (p q : RegularData 3 V) (A : CapPosition p) (B : CapPosition q)
    (htype : (presentation p).SameLabelledType (presentation q))
    (hroot : triangleLabels p A.root = triangleLabels q B.root) :
    A.faces p = B.faces q := by
  obtain ⟨e,he⟩ := vertex_patterns_equiv p q htype
  have heroot : e A.root = B.root :=
    triangleLabels_injective q ((he A.root).trans hroot)
  ext s
  rw [A.mem_faces p,B.mem_faces q]
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨e x,by
      intro h
      exact hx (e.injective (h.trans heroot.symm)),he x⟩
  · rintro ⟨y,hy,rfl⟩
    refine ⟨e.symm y,?_,?_⟩
    · intro h
      apply hy
      have hh := congrArg e h
      rwa [e.apply_symm_apply,heroot] at hh
    · simpa only [e.apply_symm_apply] using (he (e.symm y)).symm

theorem positions_same_combinatorics
    (p q : RegularData 3 V) (hp : ∀ v, p.data.2 v = 1) (hq : ∀ v, q.data.2 v = 1)
    (hpS : IsSimpleHalfspace (fun v => (p.data.1 v).toLinearMap) p.data.2)
    (hqS : IsSimpleHalfspace (fun v => (q.data.1 v).toLinearMap) q.data.2)
    (A : CapPosition p) (B : CapPosition q)
    (htype : (presentation p).SameLabelledType (presentation q))
    (hroot : triangleLabels p A.root = triangleLabels q B.root)
    (hcorner : A.corner = B.corner) :
    (A.strictConvexCap p hp hpS).SameCombinatorics (B.strictConvexCap q hq hqS) :=
  ⟨positions_same_faces p q A B htype hroot,hcorner⟩

/-- Corresponding source realizations admit cap placements with exactly the
same labelled triangulation and the same ordered three boundary labels. -/
theorem compatible_positions
    (p q : RegularData 3 V) (hp : ∀ v, p.data.2 v = 1) (hq : ∀ v, q.data.2 v = 1)
    (hpS : IsSimpleHalfspace (fun v => (p.data.1 v).toLinearMap) p.data.2)
    (hqS : IsSimpleHalfspace (fun v => (q.data.1 v).toLinearMap) q.data.2)
    (htype : (presentation p).SameLabelledType (presentation q)) :
    ∃ (p' q' : RegularData 3 V) (hp' : ∀ v, p'.data.2 v = 1) (hq' : ∀ v, q'.data.2 v = 1)
      (hp'S : IsSimpleHalfspace (fun v => (p'.data.1 v).toLinearMap) p'.data.2)
      (hq'S : IsSimpleHalfspace (fun v => (q'.data.1 v).toLinearMap) q'.data.2)
      (A : CapPosition p') (B : CapPosition q') (a b : Space ≃ᵃ[ℝ] Space),
      presentation p' = affinePresentation a (presentation p) ∧
      presentation q' = affinePresentation b (presentation q) ∧
      (A.strictConvexCap p' hp' hp'S).SameCombinatorics
        (B.strictConvexCap q' hq' hq'S) := by
  obtain ⟨r⟩ := vertices_nonempty p
  obtain ⟨I,hI,hi⟩ := extremePoint_has_active_basis
    (fun v => (p.data.1 v).toLinearMap) p.data.2 r.property
  obtain ⟨e,he⟩ := vertex_patterns_equiv p q htype
  let s := e r
  have hIq (j : Fin 3) : q.data.1 (I j) s.val = q.data.2 (I j) := by
    apply (mem_triangleLabels q s (I j)).mp
    rw [he]
    exact (mem_triangleLabels p r (I j)).mpr (hI j)
  obtain ⟨p',hp',hp'S,A,a,hAc,hAr,hAp⟩ := exists_position_at_root p hp hpS r I hI
  obtain ⟨q',hq',hq'S,B,b,hBc,hBr,hBq⟩ := exists_position_at_root q hq hqS s I hIq
  have htype' : (presentation p').SameLabelledType (presentation q') := by
    rw [hAp,hBq]
    exact (affinePresentation_sameLabelledType a (presentation p)).symm.trans
      (htype.trans (affinePresentation_sameLabelledType b (presentation q)))
  refine ⟨p',q',hp',hq',hp'S,hq'S,A,B,a,b,hAp,hBq,?_⟩
  apply positions_same_combinatorics p' q' hp' hq' hp'S hq'S A B htype'
  · exact hAr.trans ((he r).symm.trans hBr.symm)
  · exact hAc.trans hBc.symm

end NormalProjective.CapSource
end

#print axioms NormalProjective.Planar.RoofHullData.strictConvexCap
#print axioms NormalProjective.CapSource.exists_position_at_root
#print axioms NormalProjective.CapSource.CapPosition.pnRelated_cap_polar
#print axioms NormalProjective.CapSource.compatible_positions

/-! Read-only actual-body audit; generated from the canonical project root. -/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let localModules : Array Name := #[`cap_extraction_geometry]
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
  IO.FS.writeFile ".lake/reports/audit/final/CapExtractionGeometry_dependencies.json" result.pretty
  logInfo m!"Audited {records.size} local declarations and {boundaryRecords.size} pinned-library boundaries."
