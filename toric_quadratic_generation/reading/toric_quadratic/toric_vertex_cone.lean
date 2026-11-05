module
public import PaperVerification.ToricFaceGeometry
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Ring
@[expose] public section
/-!
# The tangent cone of a finite polytope at a vertex

This file proves the ordinary finite-polytope fact that a linear functional
which is nonnegative on all incident edge directions is nonnegative on every
direction from the vertex into the polytope. The proof uses an actual
height-one section and actual extreme segment faces; no face-lattice or
tangent-cone generation assertion is assumed.
-/

noncomputable section

namespace PaperVerification.ToricVertexCone

open scoped BigOperators
open Set
open PaperVerification.ToricExchange

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite convex hull is the convex hull of its actual extreme points. -/
theorem finite_hull_eq_hull_extremePoints (s : Finset E) :
    convexHull ℝ ((convexHull ℝ (s : Set E)).extremePoints ℝ) =
      convexHull ℝ (s : Set E) := by
  have hfinite : ((convexHull ℝ (s : Set E)).extremePoints ℝ).Finite :=
    s.finite_toSet.subset extremePoints_convexHull_subset
  have hclosed := (hfinite.isCompact_convexHull ℝ).isClosed
  simpa only [hclosed.closure_eq] using
    closure_convexHull_extremePoints (s.finite_toSet.isCompact_convexHull ℝ)
      (convex_convexHull ℝ (s : Set E))

/-- A vertex of a finite convex hull is not in the hull of the other generators. -/
theorem vertex_not_mem_hull_erase (s : Finset E) {v : E}
    (hv : v ∈ (convexHull ℝ (s : Set E)).extremePoints ℝ) :
    v ∉ convexHull ℝ ((s : Set E) \ {v}) := by
  have hv' := ((convex_convexHull ℝ (s : Set E)).mem_extremePoints_iff_mem_sdiff_convexHull_sdiff).mp hv
  intro hmem
  apply hv'.2
  apply convexHull_mono (s := ((s : Set E) \ {v})) ?_ hmem
  intro x hx
  exact ⟨subset_convexHull ℝ (s : Set E) hx.1, hx.2⟩

/-- Every vertex of a finite polytope is strictly exposed on its other generators. -/
theorem exists_strict_vertex_functional (s : Finset E) {v : E}
    (hv : v ∈ (convexHull ℝ (s : Set E)).extremePoints ℝ) :
    ∃ h : E →L[ℝ] ℝ, ∀ w ∈ s, w ≠ v → 0 < h (w - v) := by
  classical
  obtain ⟨h, c, hvc, hc⟩ := geometric_hahn_banach_point_closed
    (convex_convexHull ℝ ((s : Set E) \ {v}))
    ((s.finite_toSet.sdiff : ((s : Set E) \ {v}).Finite).isCompact_convexHull ℝ).isClosed
    (vertex_not_mem_hull_erase s hv)
  refine ⟨h, ?_⟩
  intro w hw hwv
  have hwc := hc w (subset_convexHull ℝ ((s : Set E) \ {v}) ⟨hw, hwv⟩)
  rw [map_sub]
  linarith

/-- Lower bounds of a linear functional on finite generators extend to their convex hull. -/
theorem linear_lower_bound_hull (s : Finset E) (f : E →ₗ[ℝ] ℝ) (c : ℝ)
    (h : ∀ w ∈ s, c ≤ f w) : ∀ x ∈ convexHull ℝ (s : Set E), c ≤ f x := by
  exact convexHull_min h ((convex_Ici c).linear_preimage f)

/-- The zero set of a nonnegative linear slack is an actual face. -/
theorem linear_minimum_face_extreme (P : Set E) (g : E →ₗ[ℝ] ℝ) (v : E)
    (hg : ∀ x ∈ P, g v ≤ g x) :
    IsExtreme ℝ P {x ∈ P | g x = g v} := by
  refine ⟨fun _ hx => hx.1, ?_⟩
  intro x hx y hy z hz hseg
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hseg
  refine ⟨hx, ?_⟩
  have heq := hz.2
  simp only [map_add, map_smul, smul_eq_mul] at heq
  have hxg := hg x hx
  have hyg := hg y hy
  have hbalance : a * (g x - g v) + b * (g y - g v) = 0 := by
    calc
      a * (g x - g v) + b * (g y - g v) =
          (a * g x + b * g y) - (a + b) * g v := by ring
      _ = 0 := by rw [heq, hab, one_mul, sub_self]
  have hax_nonneg := mul_nonneg ha.le (sub_nonneg.mpr hxg)
  have hby_nonneg := mul_nonneg hb.le (sub_nonneg.mpr hyg)
  have hax : a * (g x - g v) = 0 := by
    linarith only [hbalance, hax_nonneg, hby_nonneg]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hax).resolve_left ha.ne')

/-- Normalize a ray from `v` to have height one. -/
def normalizedDirection (h : E →L[ℝ] ℝ) (v w : E) : E :=
  (h (w - v))⁻¹ • (w - v)

theorem scale_normalizedDirection (h : E →L[ℝ] ℝ) (v w : E)
    (hw : h (w - v) ≠ 0) :
    h (w - v) • normalizedDirection h v w = w - v := by
  simp only [normalizedDirection, smul_smul, mul_inv_cancel₀ hw, one_smul]

theorem height_normalizedDirection (h : E →L[ℝ] ℝ) (v w : E)
    (hw : h (w - v) ≠ 0) :
    h (normalizedDirection h v w) = 1 := by
  simp only [normalizedDirection, map_smul, smul_eq_mul, inv_mul_cancel₀ hw]

/-- Finite generators of the actual height-one section at a vertex. -/
def sectionGenerators (s : Finset E) (v : E) (h : E →L[ℝ] ℝ) : Finset E := by
  classical
  exact (s.erase v).image (normalizedDirection h v)

theorem mem_sectionGenerators (s : Finset E) (v : E) (h : E →L[ℝ] ℝ) (u : E) :
    u ∈ sectionGenerators s v h ↔
      ∃ w ∈ s, w ≠ v ∧ normalizedDirection h v w = u := by
  classical
  simp only [sectionGenerators, Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨w, ⟨hwv, hws⟩, hwu⟩
    exact ⟨w, hws, hwv, hwu⟩
  · rintro ⟨w, hws, hwv, hwu⟩
    exact ⟨w, ⟨hwv, hws⟩, hwu⟩

/-- A vertex of the height-one section lies on an actual edge ray of the original
finite polytope. The resulting edge is a nondegenerate extreme segment. -/
theorem section_vertex_gives_edge {n : ℕ} (s : Finset (Fin n → ℝ))
    (v : Fin n → ℝ) (hv : v ∈ s) (h : (Fin n → ℝ) →L[ℝ] ℝ)
    (hpos : ∀ w ∈ s, w ≠ v → 0 < h (w - v))
    (u : Fin n → ℝ)
    (hu : u ∈ (convexHull ℝ (sectionGenerators s v h : Set (Fin n → ℝ))).extremePoints ℝ) :
    ∃ w ∈ s, v ≠ w ∧
      IsExtreme ℝ (convexHull ℝ (s : Set (Fin n → ℝ))) (segment ℝ v w) ∧
      0 < h (w - v) ∧ w - v = h (w - v) • u := by
  classical
  let T := sectionGenerators s v h
  obtain ⟨f, hf⟩ := exists_strict_vertex_functional T hu
  have hfle (q : Fin n → ℝ) (hq : q ∈ T) : f u ≤ f q := by
    by_cases hqu : q = u
    · simp [hqu]
    · have hlt : 0 < f q - f u := by simpa only [map_sub] using hf q hq hqu
      linarith
  let g : (Fin n → ℝ) →ₗ[ℝ] ℝ := f.toLinearMap - (f u) • h.toLinearMap
  have hg_normal (w : Fin n → ℝ) (hw : w ∈ s) (hwv : w ≠ v) :
      g (w - v) = h (w - v) * (f (normalizedDirection h v w) - f u) := by
    have hheight := height_normalizedDirection h v w (hpos w hw hwv).ne'
    calc
      g (w - v) = g (h (w - v) • normalizedDirection h v w) :=
        congrArg g (scale_normalizedDirection h v w (hpos w hw hwv).ne').symm
      _ = h (w - v) * g (normalizedDirection h v w) := by rw [map_smul, smul_eq_mul]
      _ = _ := by simp [g, hheight]
  have hqmem (w : Fin n → ℝ) (hw : w ∈ s) (hwv : w ≠ v) :
      normalizedDirection h v w ∈ T :=
    (mem_sectionGenerators s v h _).mpr ⟨w, hw, hwv, rfl⟩
  have hgnonneg (w : Fin n → ℝ) (hw : w ∈ s) : 0 ≤ g (w - v) := by
    by_cases hwv : w = v
    · simp [hwv]
    · rw [hg_normal w hw hwv]
      exact mul_nonneg (hpos w hw hwv).le (sub_nonneg.mpr (hfle _ (hqmem w hw hwv)))
  have hqeq (w : Fin n → ℝ) (hw : w ∈ s) (hwv : w ≠ v)
      (hgw : g (w - v) = 0) : normalizedDirection h v w = u := by
    by_contra hne
    have hfpos := hf _ (hqmem w hw hwv) hne
    have hfpos' : 0 < f (normalizedDirection h v w) - f u := by
      simpa only [map_sub] using hfpos
    have hprod := mul_pos (hpos w hw hwv) hfpos'
    rw [← hg_normal w hw hwv, hgw] at hprod
    exact (lt_irrefl 0) hprod
  let P : Set (Fin n → ℝ) := convexHull ℝ (s : Set (Fin n → ℝ))
  let F : Set (Fin n → ℝ) := {x ∈ P | g x = g v}
  have hgmin : ∀ x ∈ P, g v ≤ g x := by
    apply linear_lower_bound_hull s g (g v)
    intro x hx
    have hxg := hgnonneg x hx
    simpa only [map_sub, sub_nonneg] using hxg
  have hFext : IsExtreme ℝ P F := linear_minimum_face_extreme P g v hgmin
  have hFconv : Convex ℝ F :=
    (convex_convexHull ℝ (s : Set (Fin n → ℝ))).inter
      ((convex_singleton (g v)).linear_preimage g)
  have hvF : v ∈ F := ⟨subset_convexHull ℝ (s : Set (Fin n → ℝ)) hv, rfl⟩
  have huT : u ∈ T := extremePoints_convexHull_subset hu
  obtain ⟨w₀, hw₀, hw₀v, hq₀⟩ := (mem_sectionGenerators s v h u).mp huT
  have hw₀g : g (w₀ - v) = 0 := by
    rw [hg_normal w₀ hw₀ hw₀v, hq₀, sub_self, mul_zero]
  have hw₀F : w₀ ∈ F :=
    ⟨subset_convexHull ℝ (s : Set (Fin n → ℝ)) hw₀,
      sub_eq_zero.mp (by simpa only [map_sub] using hw₀g)⟩
  let R := faceGenerators s F
  have hRmem (x : Fin n → ℝ) : x ∈ R ↔ x ∈ s ∧ x ∈ F := by
    simp [R, faceGenerators]
  obtain ⟨w, hwR, hmax⟩ := R.exists_max_image (fun x => h (x - v))
    ⟨w₀, (hRmem w₀).mpr ⟨hw₀, hw₀F⟩⟩
  have hws : w ∈ s := ((hRmem w).mp hwR).1
  have hwF : w ∈ F := ((hRmem w).mp hwR).2
  have hwp : 0 < h (w - v) :=
    (hpos w₀ hw₀ hw₀v).trans_le (hmax w₀ ((hRmem w₀).mpr ⟨hw₀, hw₀F⟩))
  have hwv : w ≠ v := by intro he; simp [he] at hwp
  have hscale (x : Fin n → ℝ) (hx : x ∈ R) : x - v = h (x - v) • u := by
    have hxs := ((hRmem x).mp hx).1
    have hxF := ((hRmem x).mp hx).2
    by_cases hxv : x = v
    · simp [hxv]
    · have hxg : g (x - v) = 0 := by simp only [map_sub, hxF.2, sub_self]
      calc
        x - v = h (x - v) • normalizedDirection h v x :=
          (scale_normalizedDirection h v x (hpos x hxs hxv).ne').symm
        _ = h (x - v) • u := by rw [hqeq x hxs hxv hxg]
  have hwscale := hscale w hwR
  have hRsegment : (R : Set (Fin n → ℝ)) ⊆ segment ℝ v w := by
    intro x hx
    have hxs := ((hRmem x).mp hx).1
    have hxheight : 0 ≤ h (x - v) := by
      by_cases hxv : x = v
      · simp [hxv]
      · exact (hpos x hxs hxv).le
    have hratio : h (x - v) / h (w - v) ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hxheight hwp.le, (div_le_one hwp).mpr (hmax x hx)⟩
    have hmul : (h (x - v) / h (w - v)) * h (w - v) = h (x - v) := by
      field_simp [hwp.ne']
    have hsmul : (h (x - v) / h (w - v)) • (w - v) = h (x - v) • u := by
      calc
        _ = (h (x - v) / h (w - v)) • (h (w - v) • u) :=
          congrArg (fun z => (h (x - v) / h (w - v)) • z) hwscale
        _ = ((h (x - v) / h (w - v)) * h (w - v)) • u := smul_smul _ _ _
        _ = h (x - v) • u := by rw [hmul]
    have hline : AffineMap.lineMap v w (h (x - v) / h (w - v)) = x := by
      rw [AffineMap.lineMap_apply_module', hsmul, ← hscale x hx, sub_add_cancel]
    simpa only [hline] using lineMap_mem_segment ℝ v w hratio
  have hFhull : F = convexHull ℝ (R : Set (Fin n → ℝ)) :=
    convex_face_eq_convexHull_filter s F hFconv hFext
  have hFsegment : F = segment ℝ v w := by
    apply Set.Subset.antisymm
    · rw [hFhull]
      exact convexHull_min hRsegment (convex_segment v w)
    · exact hFconv.segment_subset hvF hwF
  refine ⟨w, hws, hwv.symm, ?_, hwp, hwscale⟩
  simpa only [← hFsegment] using hFext

/-- A linear functional that is nonnegative on every actual incident edge
direction is nonnegative on every direction into the finite polytope. -/
theorem linear_nonneg_of_incident_edges {n : ℕ} (s : Finset (Fin n → ℝ))
    (v : Fin n → ℝ)
    (hv : v ∈ (convexHull ℝ (s : Set (Fin n → ℝ))).extremePoints ℝ)
    (f : (Fin n → ℝ) →ₗ[ℝ] ℝ)
    (hedges : ∀ w : Fin n → ℝ, v ≠ w →
      IsExtreme ℝ (convexHull ℝ (s : Set (Fin n → ℝ))) (segment ℝ v w) →
      0 ≤ f (w - v)) :
    ∀ x ∈ convexHull ℝ (s : Set (Fin n → ℝ)), 0 ≤ f (x - v) := by
  classical
  obtain ⟨h, hpos⟩ := exists_strict_vertex_functional s hv
  have hvs : v ∈ s := extremePoints_convexHull_subset hv
  let T := sectionGenerators s v h
  have hext : ∀ u ∈ (convexHull ℝ (T : Set (Fin n → ℝ))).extremePoints ℝ,
      0 ≤ f u := by
    intro u hu
    obtain ⟨w, _, hvw, hwe, hwp, hwscale⟩ := section_vertex_gives_edge s v hvs h hpos u hu
    have hf := hedges w hvw hwe
    rw [hwscale, map_smul, smul_eq_mul] at hf
    exact nonneg_of_mul_nonneg_right hf hwp
  have hsection : ∀ u ∈ convexHull ℝ (T : Set (Fin n → ℝ)), 0 ≤ f u := by
    have hsub :
        convexHull ℝ ((convexHull ℝ (T : Set (Fin n → ℝ))).extremePoints ℝ) ⊆
          {u | 0 ≤ f u} :=
      convexHull_min hext ((convex_Ici (0 : ℝ)).linear_preimage f)
    rw [finite_hull_eq_hull_extremePoints T] at hsub
    exact hsub
  have hgenerators (w : Fin n → ℝ) (hw : w ∈ s) : f v ≤ f w := by
    have hfnonneg : 0 ≤ f (w - v) := by
      by_cases hwv : w = v
      · simp [hwv]
      · have hq : normalizedDirection h v w ∈ T :=
          (mem_sectionGenerators s v h _).mpr ⟨w, hw, hwv, rfl⟩
        have hfq := hsection _ (subset_convexHull ℝ (T : Set (Fin n → ℝ)) hq)
        rw [← scale_normalizedDirection h v w (hpos w hw hwv).ne',
          map_smul, smul_eq_mul]
        exact mul_nonneg (hpos w hw hwv).le hfq
    simpa only [map_sub, sub_nonneg] using hfnonneg
  intro x hx
  have hfx := linear_lower_bound_hull s f (f v) hgenerators x hx
  simpa only [map_sub, sub_nonneg] using hfx

/-- If every actual incident edge lies on a nonnegative basis ray, the whole
polytope lies in the nonnegative cone on that basis at the vertex. This is the
tangent-cone assertion needed to extract the integral dual facet normals at a
smooth vertex. -/
theorem nonnegative_basis_coordinates_of_incident_edges {n : ℕ}
    (s : Finset (Fin n → ℝ)) (v : Fin n → ℝ)
    (hv : v ∈ (convexHull ℝ (s : Set (Fin n → ℝ))).extremePoints ℝ)
    (b : Module.Basis (Fin n) ℝ (Fin n → ℝ))
    (hedges : ∀ w : Fin n → ℝ, v ≠ w →
      IsExtreme ℝ (convexHull ℝ (s : Set (Fin n → ℝ))) (segment ℝ v w) →
      ∃ j : Fin n, ∃ a : ℝ, 0 ≤ a ∧ w - v = a • b j) :
    ∀ x ∈ convexHull ℝ (s : Set (Fin n → ℝ)),
      ∀ i : Fin n, 0 ≤ b.repr (x - v) i := by
  intro x hx i
  apply linear_nonneg_of_incident_edges s v hv (b.coord i) ?_ x hx
  intro w hvw hwedge
  obtain ⟨j, a, ha, hw⟩ := hedges w hvw hwedge
  rw [hw, map_smul]
  by_cases hij : i = j
  · subst j
    simpa using ha
  · simp [Module.Basis.coord_apply, hij, Ne.symm hij]

end PaperVerification.ToricVertexCone
