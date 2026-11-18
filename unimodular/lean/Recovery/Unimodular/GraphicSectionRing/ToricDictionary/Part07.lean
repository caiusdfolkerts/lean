module

public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.Part06
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.Tactic.Abel

@[expose] public section
set_option autoImplicit false

section
-- BEGIN PaperVerification.ToricFiniteDuality



/-!
# Finite cone duality from a strictly positive normalizing functional

The finite generating vectors admit a common strictly positive functional.
Their normalized convex hull is compact. Separating a normalized candidate
from this finite hull proves the relevant dual-cone theorem directly from
Hahn--Banach, including the zero and empty-family cases.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical

section FiniteDuality

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι]
    (v : ι → E) (H : E →ₗ[ℝ] ℝ) (hH : ∀ i, 0 < H (v i))

include hH

/-- In the dual of a finite inequality family, the zero slice of a strictly
positive normalizing functional consists only of the zero vector. -/
theorem finite_dual_zero_of_pairing_zero (c : E)
    (hc : ∀ f : E →ₗ[ℝ] ℝ, (∀ i, 0 ≤ f (v i)) → 0 ≤ f c)
    (hzero : H c = 0) : c = 0 := by
  apply (Module.forall_dual_apply_eq_zero_iff ℝ c).mp
  intro f
  obtain ⟨M, hM⟩ := (Set.finite_range (fun i => |f (v i)| / H (v i))).bddAbove
  have hbound (i : ι) : |f (v i)| ≤ M * H (v i) :=
    (div_le_iff₀ (hH i)).mp (hM (Set.mem_range_self i))
  have hplus : ∀ i, 0 ≤ (M • H + f) (v i) := by
    intro i
    have hb := hbound i
    have hf := neg_abs_le (f (v i))
    change 0 ≤ M * H (v i) + f (v i)
    linarith
  have hminus : ∀ i, 0 ≤ (M • H - f) (v i) := by
    intro i
    have hb := hbound i
    have hf := le_abs_self (f (v i))
    change 0 ≤ M * H (v i) - f (v i)
    linarith
  have hp := hc (M • H + f) hplus
  have hm := hc (M • H - f) hminus
  change 0 ≤ M * H c + f c at hp
  change 0 ≤ M * H c - f c at hm
  rw [hzero, mul_zero, zero_add] at hp
  rw [hzero, mul_zero, zero_sub] at hm
  linarith

theorem finite_dual_pairing_pos (c : E)
    (hc : ∀ f : E →ₗ[ℝ] ℝ, (∀ i, 0 ≤ f (v i)) → 0 ≤ f c)
    (hne : c ≠ 0) : 0 < H c := by
  have hnonneg := hc H (fun i => (hH i).le)
  exact lt_of_le_of_ne hnonneg (fun he =>
    hne (finite_dual_zero_of_pairing_zero v H hH c hc he.symm))

/-- Every nonzero point in the dual of the finite inequalities normalizes
into the actual convex hull of the normalized generating vectors. -/
theorem finite_dual_normalized_mem_convexHull (c : E)
    (hc : ∀ f : E →ₗ[ℝ] ℝ, (∀ i, 0 ≤ f (v i)) → 0 ≤ f c)
    (hne : c ≠ 0) :
    (H c)⁻¹ • c ∈ convexHull ℝ (Set.range (fun i => (H (v i))⁻¹ • v i)) := by
  have hcp := finite_dual_pairing_pos v H hH c hc hne
  by_contra hnot
  obtain ⟨f, t, hct, ht⟩ := geometric_hahn_banach_point_closed
    (convex_convexHull ℝ (Set.range (fun i => (H (v i))⁻¹ • v i)))
    ((Set.finite_range (fun i => (H (v i))⁻¹ • v i)).isClosed_convexHull ℝ) hnot
  have hgenerators : ∀ i, 0 ≤ (f.toLinearMap - t • H) (v i) := by
    intro i
    have hi := ht ((H (v i))⁻¹ • v i)
      (subset_convexHull ℝ _ (Set.mem_range_self i))
    have he : f ((H (v i))⁻¹ • v i) = f (v i) / H (v i) := by
      simp only [map_smul, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rw [he] at hi
    change 0 ≤ f (v i) - t * H (v i)
    exact (sub_pos.mpr ((lt_div_iff₀ (hH i)).mp hi)).le
  have hdual := hc (f.toLinearMap - t • H) hgenerators
  have he : f ((H c)⁻¹ • c) = f c / H c := by
    simp only [map_smul, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [he] at hct
  have hlt := (div_lt_iff₀ hcp).mp hct
  change 0 ≤ f c - t * H c at hdual
  linarith

/-- The needed finite conic bipolar theorem, with the strictly positive
normalizing functional explicitly justified by the mathematical application. -/
theorem mem_finite_cone_of_nonnegative_on_dual (c : E)
    (hc : ∀ f : E →ₗ[ℝ] ℝ, (∀ i, 0 ≤ f (v i)) → 0 ≤ f c) :
    c ∈ PointedCone.hull ℝ (Set.range v) := by
  by_cases hzero : c = 0
  · subst c
    exact Submodule.zero_mem _
  · let C := PointedCone.hull ℝ (Set.range v)
    have hnorm := finite_dual_normalized_mem_convexHull v H hH c hc hzero
    have hsub : convexHull ℝ (Set.range (fun i => (H (v i))⁻¹ • v i)) ⊆ C := by
      apply convexHull_min
      · rintro _ ⟨i, rfl⟩
        exact PointedCone.smul_mem C (inv_nonneg.mpr (hH i).le)
          (PointedCone.subset_hull (Set.mem_range_self i))
      · exact C.convex
    have hcp := finite_dual_pairing_pos v H hH c hc hzero
    have hscaled := PointedCone.smul_mem C hcp.le (hsub hnorm)
    simpa only [smul_smul, mul_inv_cancel₀ (ne_of_gt hcp), one_smul] using hscaled

end FiniteDuality

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- Coefficients representing an arbitrary linear functional on the finite
ray coefficient space. Values away from actual rays are irrelevant and zero. -/
def functionalCoefficients (f : «Σ».RaySpace →ₗ[ℝ] ℝ) (v : Lattice n) : ℝ :=
  if hv : v ∈ «Σ».rays then f (Pi.single ⟨v, hv⟩ 1) else 0

theorem rayPairing_functionalCoefficients (f : «Σ».RaySpace →ₗ[ℝ] ℝ) (c : «Σ».RaySpace) :
    «Σ».rayPairing («Σ».functionalCoefficients f) c = f c := by
  have he := congrArg f ((Pi.basisFun ℝ «Σ».rays).sum_repr c)
  simpa [rayPairing, functionalCoefficients, map_sum, map_smul, smul_eq_mul,
    Pi.basisFun_repr, Pi.basisFun_apply] using he

/-- Nefness detects precisely the nonnegative linear functionals on the
finite canonical primitive family. -/
theorem isNef_functionalCoefficients_iff (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    (f : «Σ».RaySpace →ₗ[ℝ] ℝ) :
    «Σ».IsNef («Σ».functionalCoefficients f) ↔
      ∀ Q : «Σ».primitiveCollections, 0 ≤ f («Σ».canonicalPrimitive Q).vector := by
  rw [«Σ».isNef_iff_canonicalPrimitive_nonneg hpure H hH]
  apply forall_congr'
  intro Q
  rw [← («Σ».canonicalPrimitive Q).vector_pairing,
    «Σ».rayPairing_functionalCoefficients]

/-- An effective relation is nonnegative on every linear functional
nonnegative on the actual finite primitive family. -/
theorem effective_nonnegative_on_finite_dual (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    {c : «Σ».RaySpace} (hc : c ∈ «Σ».effectiveCone) :
    ∀ f : «Σ».RaySpace →ₗ[ℝ] ℝ,
      (∀ Q : «Σ».primitiveCollections, 0 ≤ f («Σ».canonicalPrimitive Q).vector) → 0 ≤ f c := by
  intro f hf
  have hnef := («Σ».isNef_functionalCoefficients_iff hpure H hH f).mpr hf
  have h := hc.2 («Σ».functionalCoefficients f) hnef
  rwa [«Σ».rayPairing_functionalCoefficients] at h

/-- The genuine dual effective cone is generated by the finite primitive
relation family. This is proved, not inserted into a fan or nef definition. -/
theorem effectiveCone_eq_primitive_hull (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ))) :
    «Σ».effectiveCone = PointedCone.hull ℝ
      (Set.range (fun Q : «Σ».primitiveCollections => («Σ».canonicalPrimitive Q).vector)) := by
  apply le_antisymm
  · intro c hc
    exact mem_finite_cone_of_nonnegative_on_dual
      (fun Q : «Σ».primitiveCollections => («Σ».canonicalPrimitive Q).vector)
      («Σ».rayPairing (fun v => (H v : ℝ)))
      (fun Q => by
        rw [(«Σ».canonicalPrimitive Q).vector_pairing]
        exact («Σ».canonicalPrimitive Q).degree_pos_of_strictSupport hH)
      c («Σ».effective_nonnegative_on_finite_dual hpure H hH hc)
  · apply Submodule.span_le.mpr
    rintro _ ⟨Q, rfl⟩
    exact («Σ».canonicalPrimitive Q).vector_effective

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
-- END PaperVerification.ToricFiniteDuality
end

section
-- BEGIN PaperVerification.ToricVertexCone
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
  exact convexHull_min (t := {x | c ≤ f x}) (fun w hw => h w hw)
    ((convex_Ici c).linear_preimage f)

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
end
-- END PaperVerification.ToricVertexCone
end

section
-- BEGIN PaperVerification.ToricExtremalCriterion



/-!
# Extremal primitive rays detect all nef inequalities

The compact normalized primitive hull has genuine extreme points. Each such
point is one of the normalized primitive vectors, and its nonnegative ray is
a Mathlib face of the actual dual effective cone. Taking the convex hull of
these extreme points proves the criterion using only extremal primitive
relations. Together with the proved replacement theorem this gives the
contractible-relation corner criterion.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical
open PaperVerification.ToricVertexCone

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

def normalizedPrimitive (H : Lattice n → ℤ) (Q : «Σ».primitiveCollections) : «Σ».RaySpace :=
  ((«Σ».canonicalPrimitive Q).degree (fun v => (H v : ℝ)))⁻¹ •
    («Σ».canonicalPrimitive Q).vector

def primitiveBase (H : Lattice n → ℤ) : Set «Σ».RaySpace :=
  convexHull ℝ (Set.range («Σ».normalizedPrimitive H))

theorem effective_height_pos (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    {c : «Σ».RaySpace} (hc : c ∈ «Σ».effectiveCone) (hne : c ≠ 0) :
    0 < «Σ».rayPairing (fun v => (H v : ℝ)) c := by
  exact finite_dual_pairing_pos
    (fun Q : «Σ».primitiveCollections => («Σ».canonicalPrimitive Q).vector)
    («Σ».rayPairing (fun v => (H v : ℝ)))
    (fun Q => by
      rw [(«Σ».canonicalPrimitive Q).vector_pairing]
      exact («Σ».canonicalPrimitive Q).degree_pos_of_strictSupport hH)
    c («Σ».effective_nonnegative_on_finite_dual hpure H hH hc) hne

theorem effective_normalized_mem_base (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    {c : «Σ».RaySpace} (hc : c ∈ «Σ».effectiveCone) (hne : c ≠ 0) :
    («Σ».rayPairing (fun v => (H v : ℝ)) c)⁻¹ • c ∈ «Σ».primitiveBase H := by
  have h := finite_dual_normalized_mem_convexHull
    (fun Q : «Σ».primitiveCollections => («Σ».canonicalPrimitive Q).vector)
    («Σ».rayPairing (fun v => (H v : ℝ)))
    (fun Q => by rw [(«Σ».canonicalPrimitive Q).vector_pairing]
                 exact («Σ».canonicalPrimitive Q).degree_pos_of_strictSupport hH)
    c («Σ».effective_nonnegative_on_finite_dual hpure H hH hc) hne
  change («Σ».rayPairing (fun v => (H v : ℝ)) c)⁻¹ • c ∈
    convexHull ℝ (Set.range (fun Q : «Σ».primitiveCollections =>
      ((«Σ».canonicalPrimitive Q).degree (fun v => (H v : ℝ)))⁻¹ •
        («Σ».canonicalPrimitive Q).vector))
  simpa only [PrimitiveRelation.vector_pairing] using h

/-- A genuine extreme point of the normalized base gives an actual
extremal ray of the dual effective cone. -/
theorem primitive_extremal_of_normalized_extreme (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    (R : «Σ».PrimitiveRelation)
    (hR : (R.degree (fun v => (H v : ℝ)))⁻¹ • R.vector ∈
      («Σ».primitiveBase H).extremePoints ℝ) : R.IsExtremal := by
  let F := «Σ».rayPairing (fun v => (H v : ℝ))
  have hFr : 0 < F R.vector := by
    rw [show F R.vector = R.degree (fun v => (H v : ℝ)) from R.vector_pairing _]
    exact R.degree_pos_of_strictSupport hH
  have hR' : (F R.vector)⁻¹ • R.vector ∈ («Σ».primitiveBase H).extremePoints ℝ := by
    simpa only [F, R.vector_pairing] using hR
  refine ⟨Submodule.span_le.mpr ?_, ?_⟩
  · rintro _ rfl
    exact R.vector_effective
  · intro c d α hc hd hα hsum
    by_cases hc0 : c = 0
    · subst c
      exact Submodule.zero_mem _
    obtain ⟨t, ht, he⟩ := PointedCone.mem_hull_singleton.mp hsum
    by_cases hd0 : d = 0
    · apply PointedCone.mem_hull_singleton.mpr
      refine ⟨α⁻¹ * t, mul_nonneg (inv_nonneg.mpr hα.le) ht, ?_⟩
      have hh := congrArg (fun z : «Σ».RaySpace => α⁻¹ • z) he
      simpa only [hd0, add_zero, smul_smul, inv_mul_cancel₀ (ne_of_gt hα), one_smul] using hh
    have hFc : 0 < F c := «Σ».effective_height_pos hpure H hH hc hc0
    have hFd : 0 < F d := «Σ».effective_height_pos hpure H hH hd hd0
    have hcn := «Σ».effective_normalized_mem_base hpure H hH hc hc0
    have hdn := «Σ».effective_normalized_mem_base hpure H hH hd hd0
    have hFt : t * F R.vector = α * F c + F d := by
      have hh := congrArg F he
      simpa only [map_add, map_smul, smul_eq_mul] using hh
    let D : ℝ := α * F c + F d
    have hD : 0 < D := add_pos (mul_pos hα hFc) hFd
    have htpos : 0 < t := by nlinarith
    let p : ℝ := α * F c / D
    let q : ℝ := F d / D
    have hp : 0 < p := div_pos (mul_pos hα hFc) hD
    have hq : 0 < q := div_pos hFd hD
    have hpq : p + q = 1 := by
      dsimp [p, q]
      rw [← add_div]
      exact div_self (ne_of_gt hD)
    have hpc : p * (F c)⁻¹ = D⁻¹ * α := by
      dsimp [p]
      field_simp
    have hqd : q * (F d)⁻¹ = D⁻¹ := by
      dsimp [q]
      field_simp
    have hDr : D⁻¹ * t = (F R.vector)⁻¹ := by
      rw [show D = t * F R.vector from hFt.symm]
      field_simp
    have hcombo : p • ((F c)⁻¹ • c) + q • ((F d)⁻¹ • d) =
        (F R.vector)⁻¹ • R.vector := by
      calc
        p • ((F c)⁻¹ • c) + q • ((F d)⁻¹ • d) = D⁻¹ • (α • c + d) := by
          simp only [smul_smul, smul_add, hpc, hqd]
        _ = D⁻¹ • (t • R.vector) := by rw [← he]
        _ = (F R.vector)⁻¹ • R.vector := by rw [smul_smul, hDr]
    have hnorm : (F c)⁻¹ • c = (F R.vector)⁻¹ • R.vector :=
      hR'.2 hcn hdn ⟨p, q, hp, hq, hpq, hcombo⟩
    apply PointedCone.mem_hull_singleton.mpr
    refine ⟨F c * (F R.vector)⁻¹,
      mul_nonneg hFc.le (inv_nonneg.mpr hFr.le), ?_⟩
    have hh := congrArg (fun z : «Σ».RaySpace => F c • z) hnorm
    simpa only [smul_smul, mul_inv_cancel₀ (ne_of_gt hFc), one_smul] using hh.symm

/-- The convex hull of the actual extreme points is the whole normalized
primitive base, including the empty-base case. -/
theorem primitiveBase_hull_extremePoints (H : Lattice n → ℤ) :
    convexHull ℝ ((«Σ».primitiveBase H).extremePoints ℝ) = «Σ».primitiveBase H := by
  let s := Finset.univ.image («Σ».normalizedPrimitive H)
  have he : (s : Set «Σ».RaySpace) = Set.range («Σ».normalizedPrimitive H) := by
    simp [s]
  have h := finite_hull_eq_hull_extremePoints s
  simpa only [he, primitiveBase] using h

/-- All actual nef inequalities are detected by primitive relations spanning
genuine extremal effective rays. -/
theorem isNef_iff_extremal_primitive_nonneg (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    (a : Lattice n → ℝ) :
    «Σ».IsNef a ↔ ∀ R : «Σ».PrimitiveRelation, R.IsExtremal → 0 ≤ R.degree a := by
  constructor
  · intro ha R hR
    exact R.degree_nonneg_of_nef ha
  · intro ha
    apply («Σ».isNef_iff_canonicalPrimitive_nonneg hpure H hH a).mpr
    intro Q
    let R := «Σ».canonicalPrimitive Q
    let f := «Σ».rayPairing a
    have hnonneg : ∀ x ∈ («Σ».primitiveBase H).extremePoints ℝ, 0 ≤ f x := by
      intro x hx
      obtain ⟨S, hS⟩ := extremePoints_convexHull_subset hx
      subst x
      have hsext := «Σ».primitive_extremal_of_normalized_extreme hpure H hH
        («Σ».canonicalPrimitive S) hx
      have hdeg := ha («Σ».canonicalPrimitive S) hsext
      have hheight := («Σ».canonicalPrimitive S).degree_pos_of_strictSupport hH
      change 0 ≤ f ((«Σ».normalizedPrimitive H) S)
      simp only [normalizedPrimitive, map_smul, smul_eq_mul,
        PrimitiveRelation.vector_pairing, f]
      exact mul_nonneg (inv_nonneg.mpr hheight.le) hdeg
    have hmem : «Σ».normalizedPrimitive H Q ∈ «Σ».primitiveBase H :=
      subset_convexHull ℝ _ (Set.mem_range_self Q)
    have hconv : Convex ℝ {x : «Σ».RaySpace | 0 ≤ f x} :=
      (convex_Ici (0 : ℝ)).linear_preimage f
    have hbase : «Σ».primitiveBase H ⊆ {x : «Σ».RaySpace | 0 ≤ f x} := by
      rw [← «Σ».primitiveBase_hull_extremePoints H]
      exact convexHull_min hnonneg hconv
    have hvalue := hbase hmem
    have hheight := R.degree_pos_of_strictSupport hH
    change 0 ≤ f («Σ».normalizedPrimitive H Q) at hvalue
    have hvalue' : 0 ≤ (R.degree (fun v => (H v : ℝ)))⁻¹ * R.degree a := by
      simpa only [normalizedPrimitive, map_smul, smul_eq_mul, f,
        PrimitiveRelation.vector_pairing, R] using hvalue
    exact nonneg_of_mul_nonneg_right hvalue' (inv_pos.mpr hheight)

/-- The numerical contractible-relation bound forces genuine nefness after
every selected cone-divisor subtraction. This is the support-function core
of the corner-box criterion. -/
theorem nef_sub_cone_selection_of_contractible_degrees (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    (a : Lattice n → ℝ) (side : ℝ) (hside : 0 ≤ side)
    (hdegree : ∀ R : «Σ».PrimitiveRelation, R.IsCombinatoriallyContractible →
      side * R.fiberDimension ≤ R.degree a)
    {s t : Finset (Lattice n)} (hs : s ∈ «Σ».cones) (ht : t ⊆ s) :
    «Σ».IsNef (a - side • (fun v => if v ∈ t then 1 else 0)) := by
  apply («Σ».isNef_iff_extremal_primitive_nonneg hpure H hH _).mpr
  intro R hR
  exact R.degree_sub_corner_selection_nonneg hs ht a side hside
    (hdegree R (R.combinatoriallyContractible_of_extremal hR))

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
-- END PaperVerification.ToricExtremalCriterion
end

section
-- BEGIN PaperVerification.ToricShiftedPolytopes
/-!
# Shifted supporting halfspaces and matched corner centers

The following separation argument proves the center-polytope identity used in
Lemma 4.2. The hypotheses are actual supporting linear functionals and genuine
bases, and the conclusion is equality of ordinary subsets of a real vector space.
The remaining normal-fan construction is independent of this convex argument.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators

variable {E I J K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- The intersection of the specified closed supporting halfspaces. -/
def normalHalfspaces (u : I → E →ₗ[ℝ] ℝ) (a : I → ℝ) : Set E :=
  {x | ∀ i, a i ≤ u i x}

theorem convex_normalHalfspaces (u : I → E →ₗ[ℝ] ℝ) (a : I → ℝ) :
    Convex ℝ (normalHalfspaces u a) := by
  intro x hx y hy r s hr hs hrs i
  simp only [map_add, map_smul, smul_eq_mul]
  have hbound := add_le_add (mul_le_mul_of_nonneg_left (hx i) hr)
    (mul_le_mul_of_nonneg_left (hy i) hs)
  simpa only [← add_mul, hrs, one_mul] using hbound

/-- A finite convex hull is characterized by its lower support values. -/
theorem mem_finite_convexHull_of_lower_support [Finite J] (c : J → E) (x : E)
    (h : ∀ f : E →ₗ[ℝ] ℝ, ∃ j, f (c j) ≤ f x) :
    x ∈ convexHull ℝ (Set.range c) := by
  by_contra hx
  obtain ⟨f, t, hxt, ht⟩ := geometric_hahn_banach_point_closed
    (convex_convexHull ℝ (Set.range c))
    ((Set.finite_range c).isClosed_convexHull ℝ) hx
  obtain ⟨j, hj⟩ := h f.toLinearMap
  have hjt := ht (c j) (subset_convexHull ℝ _ (Set.mem_range_self j))
  exact (not_lt_of_ge hj) (hxt.trans hjt)

/-- Nonnegative coordinates in a basis cone give the expected lower bound
for every linear functional nonnegative on its generating vectors. -/
theorem linear_le_of_basis_coordinates [Fintype K]
    (b : Module.Basis K ℝ E) (f : E →ₗ[ℝ] ℝ) (c x : E)
    (hf : ∀ i, 0 ≤ f (b i)) (hx : ∀ i, 0 ≤ b.repr (x - c) i) :
    f c ≤ f x := by
  have hsum : f (x - c) = ∑ i, b.repr (x - c) i * f (b i) := by
    conv_lhs => rw [← b.sum_repr (x - c)]
    simp only [map_sum, map_smul, smul_eq_mul]
  have hnonneg : 0 ≤ f (x - c) := by
    rw [hsum]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hx i) (hf i))
  simpa only [map_sub, sub_nonneg] using hnonneg

/-- Feasible Cartier points indexed by a complete collection of basis cones
generate precisely the shifted halfspace polytope. The active supporting
functionals are the dual coordinates of each basis. -/
theorem shifted_halfspaces_eq_convexHull [Finite J] [Fintype K]
    (u : I → E →ₗ[ℝ] ℝ) (a : I → ℝ)
    (b : J → Module.Basis K ℝ E) (active : J → K → I) (c : J → E)
    (hdual : ∀ j i x, u (active j i) x = (b j).repr x i)
    (hcomplete : ∀ f : E →ₗ[ℝ] ℝ, ∃ j, ∀ i, 0 ≤ f (b j i))
    (hactive : ∀ j i, u (active j i) (c j) = a (active j i))
    (hfeasible : ∀ j, c j ∈ normalHalfspaces u a) :
    normalHalfspaces u a = convexHull ℝ (Set.range c) := by
  apply Set.Subset.antisymm
  · intro x hx
    apply mem_finite_convexHull_of_lower_support c x
    intro f
    obtain ⟨j, hj⟩ := hcomplete f
    refine ⟨j, linear_le_of_basis_coordinates (b j) f (c j) x hj ?_⟩
    intro i
    rw [← hdual, map_sub, hactive]
    exact sub_nonneg.mpr (hx (active j i))
  · exact convexHull_min (by rintro _ ⟨j, rfl⟩; exact hfeasible j)
      (convex_normalHalfspaces u a)

/-- A nonzero supporting functional is strictly above its support value at
an interior point. The proof uses the open-map theorem for a surjective real
linear functional, so it applies to the actual topological interior. -/
theorem strict_support_of_interior (u : I → E →ₗ[ℝ] ℝ) (a : I → ℝ)
    (x : E) (hx : x ∈ interior (normalHalfspaces u a)) (i : I) (hi : u i ≠ 0) :
    a i < u i x := by
  have hne : ∃ v : E, u i v ≠ 0 := by
    by_contra h
    apply hi
    ext v
    by_contra hv
    exact h ⟨v, hv⟩
  obtain ⟨v, hv⟩ := hne
  have hsurj : Function.Surjective (u i) := by
    intro r
    refine ⟨(r / u i v) • v, ?_⟩
    simp only [map_smul, smul_eq_mul]
    exact div_mul_cancel₀ r hv
  have hopen := (u i).isOpenMap_of_finiteDimensional hsurj
  have hmaps : Set.MapsTo (u i) (normalHalfspaces u a) (Set.Ici (a i)) :=
    fun y hy => hy i
  have h := hopen.mapsTo_interior hmaps hx
  simpa only [interior_Ici, Set.mem_Ioi] using h

/-- Integrality upgrades strict support to an entire unit of facet slack. -/
theorem integral_support_of_interior {n : ℕ}
    (u : I → Ambient n →ₗ[ℝ] ℝ) (a : I → ℤ)
    (hu : ∀ i z, ∃ k : ℤ, u i (embed n z) = k)
    (hne : ∀ i, u i ≠ 0) (m : Lattice n)
    (hm : embed n m ∈ interior (normalHalfspaces u (fun i => (a i : ℝ)))) :
    ∀ i, (a i : ℝ) + 1 ≤ u i (embed n m) := by
  intro i
  have hstrict := strict_support_of_interior u (fun i => (a i : ℝ))
    (embed n m) hm i (hne i)
  obtain ⟨k, hk⟩ := hu i m
  rw [hk] at hstrict ⊢
  have hki : a i < k := by exact_mod_cast hstrict
  have hki' : a i + 1 ≤ k := by omega
  exact_mod_cast hki'

/-- The center of the unit corner box at a specified vertex. -/
def cornerCenter [Fintype K] (v : E) (b : Module.Basis K ℝ E) : E :=
  v + ∑ i, (1 / 2 : ℝ) • b i

/-- Translation from corner coordinates in `[0,1]` to centered coordinates
in `[-1/2,1/2]` does not change the actual box. -/
theorem cornerCenter_box_mem [Fintype K] (P : Set E)
    (v : E) (b : Module.Basis K ℝ E)
    (hbox : ∀ t : K → ℝ, (∀ i, 0 ≤ t i ∧ t i ≤ 1) →
      v + ∑ i, t i • b i ∈ P)
    (t : K → ℝ) (ht : ∀ i, |t i| ≤ 1 / 2) :
    cornerCenter v b + ∑ i, t i • b i ∈ P := by
  have hshift : ∀ i, 0 ≤ 1 / 2 + t i ∧ 1 / 2 + t i ≤ 1 := by
    intro i
    have h := abs_le.mp (ht i)
    constructor <;> linarith
  have h := hbox (fun i => 1 / 2 + t i) hshift
  simpa only [cornerCenter, add_smul, Finset.sum_add_distrib, add_assoc] using h

/-- A corner-box center satisfies all integral supporting inequalities shifted
inward by one half, including normals not incident to its own vertex. -/
theorem integral_cornerCenter_feasible [Fintype K]
    (u : I → E →ₗ[ℝ] ℝ) (a : I → ℝ)
    (v : E) (b : Module.Basis K ℝ E)
    (hu : ∀ i, u i ≠ 0)
    (hint : ∀ i k, ∃ z : ℤ, (z : ℝ) = u i (b k))
    (hbox : ∀ t : K → ℝ, (∀ k, 0 ≤ t k ∧ t k ≤ 1) →
      v + ∑ k, t k • b k ∈ normalHalfspaces u a) :
    cornerCenter v b ∈ normalHalfspaces u (fun i => a i + 1 / 2) := by
  classical
  intro i
  let f : E →ᵃ[ℝ] ℝ := (u i).toAffineMap - AffineMap.const ℝ E (a i)
  have hf : f.linear = u i := by simp [f]
  choose z hz using hint i
  have hboxf : ∀ t : K → ℝ, (∀ k, |t k| ≤ 1 / 2) →
      0 ≤ f (cornerCenter v b + ∑ k, t k • b k) := by
    intro t ht
    have hmem := cornerCenter_box_mem (normalHalfspaces u a) v b hbox t ht
    change 0 ≤ u i (cornerCenter v b + ∑ k, t k • b k) - a i
    exact sub_nonneg.mpr (hmem i)
  have h := PaperVerification.Toric.integral_unit_box_center_slack
    f (by simpa only [hf] using hu i) (cornerCenter v b) b z
    (by simpa only [hf] using hz) hboxf
  change (1 / 2 : ℝ) ≤ u i (cornerCenter v b) - a i at h
  linarith

/-- The active dual coordinate increases by precisely one half at a corner-box
center. This is the Cartier equation behind the shifted-polytope identity. -/
theorem cornerCenter_dual_coordinate [Fintype K] (v : E)
    (b : Module.Basis K ℝ E) (u : E →ₗ[ℝ] ℝ) (k : K)
    (hu : ∀ x, u x = b.repr x k) :
    u (cornerCenter v b) = u v + 1 / 2 := by
  classical
  simp only [cornerCenter, map_add, map_sum, map_smul, smul_eq_mul]
  rw [show (∑ i, (1 / 2 : ℝ) * u (b i)) = 1 / 2 by
    simp [hu, Module.Basis.repr_self, Finsupp.single_apply]]

/-- The exact shifted halfspace description of the convex hull of all unit-box
centers, with every geometric and integrality requirement displayed. -/
theorem corner_centers_convexHull [Finite J] [Fintype K]
    (u : I → E →ₗ[ℝ] ℝ) (a : I → ℝ)
    (v : J → E) (b : J → Module.Basis K ℝ E) (active : J → K → I)
    (hdual : ∀ j k x, u (active j k) x = (b j).repr x k)
    (hcomplete : ∀ f : E →ₗ[ℝ] ℝ, ∃ j, ∀ k, 0 ≤ f (b j k))
    (hactive : ∀ j k, u (active j k) (v j) = a (active j k))
    (hu : ∀ i, u i ≠ 0)
    (hint : ∀ i j k, ∃ z : ℤ, (z : ℝ) = u i (b j k))
    (hbox : ∀ (j : J) (t : K → ℝ), (∀ k, 0 ≤ t k ∧ t k ≤ 1) →
      v j + ∑ k, t k • b j k ∈ normalHalfspaces u a) :
    normalHalfspaces u (fun i => a i + 1 / 2) =
      convexHull ℝ (Set.range fun j => cornerCenter (v j) (b j)) := by
  apply shifted_halfspaces_eq_convexHull u (fun i => a i + 1 / 2)
    b active (fun j => cornerCenter (v j) (b j)) hdual hcomplete
  · intro j k
    rw [cornerCenter_dual_coordinate (v j) (b j) _ k (hdual j k), hactive]
  · intro j
    exact integral_cornerCenter_feasible u a (v j) (b j) hu
      (fun i k => hint i j k) (hbox j)

/-- Sums of matched feasible Cartier points generate the halfspace polytope
with summed support values. This is the normal-fan part of equation (7). -/
theorem matched_centers_convexHull [Finite J] [Fintype K]
    (u : I → E →ₗ[ℝ] ℝ) (a d : I → ℝ)
    (b : J → Module.Basis K ℝ E) (active : J → K → I) (c e : J → E)
    (hdual : ∀ j k x, u (active j k) x = (b j).repr x k)
    (hcomplete : ∀ f : E →ₗ[ℝ] ℝ, ∃ j, ∀ k, 0 ≤ f (b j k))
    (hcactive : ∀ j k, u (active j k) (c j) = a (active j k))
    (heactive : ∀ j k, u (active j k) (e j) = d (active j k))
    (hc : ∀ j, c j ∈ normalHalfspaces u a)
    (he : ∀ j, e j ∈ normalHalfspaces u d) :
    normalHalfspaces u (fun i => a i + d i) =
      convexHull ℝ (Set.range fun j => c j + e j) := by
  apply shifted_halfspaces_eq_convexHull u (fun i => a i + d i)
    b active (fun j => c j + e j) hdual hcomplete
  · intro j k
    rw [map_add, hcactive, heactive]
  · intro j i
    rw [map_add]
    exact add_le_add (hc j i) (he j i)

end PaperVerification.ToricGeometry
end
-- END PaperVerification.ToricShiftedPolytopes
end

section
-- BEGIN PaperVerification.ToricNormalFan
/-!
# Actual vertices, basis cones, and normal-fan matching

All normal cones below are the ordinary supporting cones from the literal
polytope definition. The lemmas identify their dual basis coordinates and
show that equality of integral basis cones preserves primitive directions.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators
open PaperVerification.ToricVertexCone

/-- The coefficient vector representing a real linear functional in the
standard coordinate pairing used by the paper's normal cones. -/
def dualVector {n : ℕ} (f : Ambient n →ₗ[ℝ] ℝ) : Ambient n :=
  fun i => f (Pi.basisFun ℝ (Fin n) i)

@[simp] theorem dualVector_pairing {n : ℕ}
    (f : Ambient n →ₗ[ℝ] ℝ) (x y : Ambient n) :
    (∑ i, dualVector f i * (y i - x i)) = f (y - x) := by
  have h := congrArg f ((Pi.basisFun ℝ (Fin n)).sum_repr (y - x))
  simpa [dualVector, map_sum, map_smul, smul_eq_mul, mul_comm] using h

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

/-- The actual vertex set is finite, independently of the chosen redundant generators. -/
theorem finite_vertices : (P.carrier.extremePoints ℝ).Finite := by
  exact (P.generators.finite_toSet.image (embed n)).subset extremePoints_convexHull_subset

/-- The convex hull of the actual vertices equals the whole polytope. -/
theorem hull_vertices : convexHull ℝ (P.carrier.extremePoints ℝ) = P.carrier := by
  classical
  have h := finite_hull_eq_hull_extremePoints (P.generators.image (embed n))
  simpa [carrier, Finset.coe_image] using h

/-- A lattice polytope has an actual vertex, also in dimension zero. -/
theorem vertices_nonempty : (P.carrier.extremePoints ℝ).Nonempty := by
  apply (convexHull_nonempty_iff (𝕜 := ℝ)).mp
  rw [P.hull_vertices]
  obtain ⟨z, hz⟩ := P.nonempty
  exact ⟨embed n z, subset_convexHull ℝ _ ⟨z, hz, rfl⟩⟩

/-- Every linear functional attains its minimum at an actual vertex. -/
theorem exists_minimizing_vertex (f : Ambient n →ₗ[ℝ] ℝ) :
    ∃ v ∈ P.carrier.extremePoints ℝ, ∀ x ∈ P.carrier, f v ≤ f x := by
  obtain ⟨v, hv, hmin⟩ := Set.exists_min_image (P.carrier.extremePoints ℝ)
    f P.finite_vertices P.vertices_nonempty
  refine ⟨v, hv, ?_⟩
  rw [← P.hull_vertices]
  exact convexHull_min (t := {x | f v ≤ f x}) (fun w hw => hmin w hw)
    ((convex_Ici (f v)).linear_preimage f)

/-- A linear functional is in the actual normal cone precisely when it is
minimized at the selected point. -/
theorem dualVector_mem_normalCone_iff (f : Ambient n →ₗ[ℝ] ℝ) (v : Ambient n) :
    dualVector f ∈ P.normalCone v ↔ ∀ x ∈ P.carrier, f v ≤ f x := by
  simp only [normalCone, Set.mem_setOf_eq, dualVector_pairing, map_sub, sub_nonneg]

/-- Every smooth vertex has a supporting orthant in its actual primitive
integral edge basis. This is a consequence of the finite-polytope tangent-cone
argument, not an extra clause in the definition of smoothness. -/
theorem smooth_vertex_basis_cone (hP : P.Smooth)
    (v : Ambient n) (hv : v ∈ P.carrier.extremePoints ℝ) :
    ∃ (vZ : Lattice n) (b : Module.Basis (Fin n) ℤ (Lattice n))
      (lengths : Fin n → ℕ),
      embed n vZ = v ∧
      (∀ i, 0 < lengths i ∧ P.IsEdge v (embed n (vZ + (lengths i : ℤ) • b i))) ∧
      (∀ x ∈ P.carrier, ∀ i, 0 ≤ (integralBasisReal b).repr (x - v) i) := by
  classical
  obtain ⟨vZ, b, lengths, hvZ, hedges, hall⟩ := hP v hv
  refine ⟨vZ, b, lengths, hvZ, hedges, ?_⟩
  let s := P.generators.image (embed n)
  have hcarrier : convexHull ℝ (s : Set (Ambient n)) = P.carrier := by
    simp [s, carrier, Finset.coe_image]
  have hv' : v ∈ (convexHull ℝ (s : Set (Ambient n))).extremePoints ℝ := by
    simpa only [hcarrier] using hv
  have hedgeRay : ∀ w : Ambient n, v ≠ w →
      IsExtreme ℝ (convexHull ℝ (s : Set (Ambient n))) (segment ℝ v w) →
      ∃ i : Fin n, ∃ a : ℝ, 0 ≤ a ∧ w - v = a • integralBasisReal b i := by
    intro w hvw hface
    have hedge : P.IsEdge v w := ⟨hvw, by simpa only [hcarrier] using hface⟩
    obtain ⟨i, rfl⟩ := hall w hedge
    refine ⟨i, (lengths i : ℝ), Nat.cast_nonneg _, ?_⟩
    rw [map_add, hvZ, integralBasisReal_apply, add_sub_cancel_left]
    ext j
    simp [embed, Int.cast_mul]
  have h := nonnegative_basis_coordinates_of_incident_edges s v hv'
    (integralBasisReal b) hedgeRay
  simpa only [hcarrier] using h

/-- A family containing the primitive edge basis at every actual vertex is
complete: every linear functional is nonnegative on one whole basis. -/
theorem smooth_basis_cones_complete
    (b : P.carrier.extremePoints ℝ → Module.Basis (Fin n) ℤ (Lattice n))
    (vZ : P.carrier.extremePoints ℝ → Lattice n)
    (lengths : P.carrier.extremePoints ℝ → Fin n → ℕ)
    (hvZ : ∀ v, embed n (vZ v) = (v : Ambient n))
    (hedges : ∀ v i, 0 < lengths v i ∧
      P.IsEdge v (embed n (vZ v + (lengths v i : ℤ) • b v i)))
    (f : Ambient n →ₗ[ℝ] ℝ) :
    ∃ v : P.carrier.extremePoints ℝ, ∀ i, 0 ≤ f (integralBasisReal (b v) i) := by
  obtain ⟨v, hv, hmin⟩ := P.exists_minimizing_vertex f
  refine ⟨⟨v, hv⟩, ?_⟩
  intro i
  let j : P.carrier.extremePoints ℝ := ⟨v, hv⟩
  have hedge := (hedges j i).2
  have hm := hmin _ (P.edge_endpoints_extreme hedge).2.1
  have he : embed n (vZ j + (lengths j i : ℤ) • b j i) =
      v + (lengths j i : ℝ) • integralBasisReal (b j) i := by
    rw [map_add, hvZ, integralBasisReal_apply]
    ext k
    simp [embed, Int.cast_mul, j]
  rw [he, map_add, map_smul, smul_eq_mul] at hm
  have hl : (0 : ℝ) < lengths j i := by exact_mod_cast (hedges j i).1
  nlinarith

/-- A point with a supporting real basis orthant is an actual vertex. -/
theorem extreme_of_supporting_basis (v : Ambient n) (hv : v ∈ P.carrier)
    (b : Module.Basis (Fin n) ℝ (Ambient n))
    (hcone : ∀ x ∈ P.carrier, ∀ i, 0 ≤ b.repr (x - v) i) :
    v ∈ P.carrier.extremePoints ℝ := by
  refine ⟨hv, ?_⟩
  intro x hx y hy hseg
  obtain ⟨r, s, hr, hs, hrs, he⟩ := hseg
  apply b.ext_elem
  intro i
  have hx0 := hcone x hx i
  have hy0 := hcone y hy i
  have he' := congrArg (fun z => b.repr z i) he
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at he'
  simp only [map_sub, Finsupp.sub_apply] at hx0 hy0
  have hbalance : r * (b.repr x i - b.repr v i) +
      s * (b.repr y i - b.repr v i) = 0 := by
    calc
      r * (b.repr x i - b.repr v i) + s * (b.repr y i - b.repr v i) =
          (r * b.repr x i + s * b.repr y i) - (r + s) * b.repr v i := by ring
      _ = 0 := by rw [he', hrs, one_mul, sub_self]
  have hrx := mul_nonneg hr.le hx0
  have hsy := mul_nonneg hs.le hy0
  have hzero : r * (b.repr x i - b.repr v i) = 0 := by
    linarith only [hbalance, hrx, hsy]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hr.ne')

/-- Equality of the genuine normal fans matches every supporting-basis vertex
with an actual vertex of the other polytope and preserves its supporting cone. -/
theorem exists_matched_vertex (Q : LatticePolytope n) (hfan : P.SameNormalFan Q)
    (v : Ambient n) (hv : v ∈ P.carrier.extremePoints ℝ)
    (b : Module.Basis (Fin n) ℝ (Ambient n))
    (hcone : ∀ x ∈ P.carrier, ∀ i, 0 ≤ b.repr (x - v) i) :
    ∃ w ∈ Q.carrier.extremePoints ℝ, P.normalCone v = Q.normalCone w ∧
      ∀ x ∈ Q.carrier, ∀ i, 0 ≤ b.repr (x - w) i := by
  have hmem : P.normalCone v ∈ P.normalFan := ⟨v, hv.1, rfl⟩
  rw [show P.normalFan = Q.normalFan from hfan] at hmem
  obtain ⟨w, hw, hcw⟩ := hmem
  have hnew : ∀ x ∈ Q.carrier, ∀ i, 0 ≤ b.repr (x - w) i := by
    intro x hx i
    have hi : dualVector (b.coord i) ∈ P.normalCone v := by
      intro y hy
      simpa only [dualVector_pairing, Module.Basis.coord_apply] using hcone y hy i
    rw [hcw] at hi
    have h := hi x hx
    simpa only [dualVector_pairing, Module.Basis.coord_apply] using h
  exact ⟨w, Q.extreme_of_supporting_basis w hw b hnew, hcw, hnew⟩

end LatticePolytope

/-- Two integral bases spanning the same positive orthant differ by a permutation,
with no rescaling. The proof uses nonnegative integer transition coefficients. -/
theorem integral_bases_perm_of_nonnegative_coordinates {K M : Type*}
    [Fintype K] [AddCommGroup M] [Module ℤ M]
    (b c : Module.Basis K ℤ M)
    (hbc : ∀ i j, 0 ≤ b.repr (c j) i)
    (hcb : ∀ i j, 0 ≤ c.repr (b j) i) :
    ∃ σ : Equiv.Perm K, ∀ i, b i = c (σ i) := by
  classical
  have hcoord (i k : K) :
      (∑ j, c.repr (b i) j * b.repr (c j) k) = if i = k then 1 else 0 := by
    have h := congrArg (fun x : M => b.repr x k) (c.sum_repr (b i))
    simpa only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      smul_eq_mul, Module.Basis.repr_self, Finsupp.single_apply] using h
  have hex (i : K) : ∃ j, c j = b i := by
    have hdiag : (∑ j, c.repr (b i) j * b.repr (c j) i) = 1 := by
      simpa using hcoord i i
    obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (show (∑ j, c.repr (b i) j * b.repr (c j) i) ≠ 0 by rw [hdiag]; norm_num)
    have ha0 := hcb j i
    have hb0 := hbc i j
    have ha1 : 1 ≤ c.repr (b i) j := by
      have hne := (mul_ne_zero_iff.mp hj).1
      omega
    have hb1 : 1 ≤ b.repr (c j) i := by
      have hne := (mul_ne_zero_iff.mp hj).2
      omega
    have hp := Finset.single_le_sum
      (fun k _ => mul_nonneg (hcb k i) (hbc i k)) (Finset.mem_univ j)
    rw [hdiag] at hp
    have ha_le : c.repr (b i) j ≤ c.repr (b i) j * b.repr (c j) i := by
      nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hb1)]
    have ha : c.repr (b i) j = 1 := by omega
    have hb : b.repr (c j) i = 1 := by rw [ha, one_mul] at hp; omega
    refine ⟨j, b.ext_elem (fun k => ?_)⟩
    by_cases hik : i = k
    · subst k
      simpa only [Module.Basis.repr_self, Finsupp.single_eq_same] using hb
    · have hpk := Finset.single_le_sum
        (fun l _ => mul_nonneg (hcb l i) (hbc k l)) (Finset.mem_univ j)
      rw [hcoord i k, if_neg hik, ha, one_mul] at hpk
      have hk : b.repr (c j) k = 0 := le_antisymm hpk (hbc k j)
      simpa only [Module.Basis.repr_self, Finsupp.single_apply, if_neg hik] using hk
  choose σ hσ using hex
  have hσinj : Function.Injective σ := by
    intro i j hij
    apply b.injective
    rw [← hσ i, ← hσ j, hij]
  exact ⟨Equiv.ofBijective σ
    ((Fintype.bijective_iff_injective_and_card σ).mpr ⟨hσinj, rfl⟩),
    fun i => (hσ i).symm⟩

/-- A positive-length integral edge contained in a basis orthant has
nonnegative integer coordinates in that basis. -/
theorem basis_coordinates_nonneg_of_edge {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n))
    (v z : Lattice n) (k : ℕ) (hk : 0 < k)
    (h : ∀ i, 0 ≤ (integralBasisReal b).repr
      (embed n (v + (k : ℤ) • z) - embed n v) i) :
    ∀ i, 0 ≤ b.repr z i := by
  intro i
  have hi := h i
  rw [map_add, add_sub_cancel_left, embed_int_smul, map_smul,
    Finsupp.smul_apply, smul_eq_mul, integralBasisReal_repr] at hi
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hn : (0 : ℝ) ≤ (b.repr z i : ℝ) := by
    push_cast at hi
    nlinarith
  exact_mod_cast hn

namespace LatticePolytope

/-- The actual common normal fan matches smooth vertices with the same
primitive lattice edge directions. Equality of the directions, rather than
merely equality of their rays, follows from integral-basis primitivity. -/
theorem sameNormalFan_matched_bases {n : ℕ} (P Q : LatticePolytope n)
    (hP : P.Smooth) (hQ : Q.Smooth) (hfan : P.SameNormalFan Q)
    (v : Ambient n) (hv : v ∈ P.carrier.extremePoints ℝ) :
    ∃ (w : Ambient n) (vZ wZ : Lattice n)
      (b : Module.Basis (Fin n) ℤ (Lattice n)) (p q : Fin n → ℕ),
      w ∈ Q.carrier.extremePoints ℝ ∧ embed n vZ = v ∧ embed n wZ = w ∧
      P.normalCone v = Q.normalCone w ∧
      (∀ i, 0 < p i ∧ P.IsEdge v (embed n (vZ + (p i : ℤ) • b i))) ∧
      (∀ i, 0 < q i ∧ Q.IsEdge w (embed n (wZ + (q i : ℤ) • b i))) ∧
      (∀ x ∈ P.carrier, ∀ i, 0 ≤ (integralBasisReal b).repr (x - v) i) ∧
      (∀ x ∈ Q.carrier, ∀ i, 0 ≤ (integralBasisReal b).repr (x - w) i) := by
  obtain ⟨vZ, b, p, hvZ, hp, hPb⟩ := P.smooth_vertex_basis_cone hP v hv
  obtain ⟨w, hw, hcones, hQb⟩ :=
    P.exists_matched_vertex Q hfan v hv (integralBasisReal b) hPb
  obtain ⟨wZ, c, q, hwZ, hq, hQc⟩ := Q.smooth_vertex_basis_cone hQ w hw
  have hPc : ∀ x ∈ P.carrier, ∀ i, 0 ≤ (integralBasisReal c).repr (x - v) i := by
    intro x hx i
    have hi : dualVector ((integralBasisReal c).coord i) ∈ Q.normalCone w := by
      intro y hy
      simpa only [dualVector_pairing, Module.Basis.coord_apply] using hQc y hy i
    rw [← hcones] at hi
    have h := hi x hx
    simpa only [dualVector_pairing, Module.Basis.coord_apply] using h
  have hbc : ∀ i j, 0 ≤ b.repr (c j) i := by
    intro i j
    apply basis_coordinates_nonneg_of_edge b wZ (c j) (q j) (hq j).1
    intro k
    have h := hQb _ (Q.edge_endpoints_extreme (hq j).2).2.1 k
    simpa only [hwZ] using h
  have hcb : ∀ i j, 0 ≤ c.repr (b j) i := by
    intro i j
    apply basis_coordinates_nonneg_of_edge c vZ (b j) (p j) (hp j).1
    intro k
    have h := hPc _ (P.edge_endpoints_extreme (hp j).2).2.1 k
    simpa only [hvZ] using h
  obtain ⟨σ, hσ⟩ := integral_bases_perm_of_nonnegative_coordinates b c hbc hcb
  refine ⟨w, vZ, wZ, b, p, fun i => q (σ i), hw, hvZ, hwZ, hcones, hp, ?_, hPb, hQb⟩
  intro i
  simpa only [hσ i] using hq (σ i)

end LatticePolytope

end PaperVerification.ToricGeometry
end
-- END PaperVerification.ToricNormalFan
end

section
-- BEGIN PaperVerification.ToricPolytopeSupport

/-!
# Integral strict support from a genuine lattice polytope

The support coefficients are negatives of actual minima over the polytope.
Every minimum occurs at a genuine lattice vertex, so those coefficients are
integers. Equality of the actual normal fans then supplies strict support on
every cone, including its lower-dimensional cones.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

/-- The negative minimum of a primitive integral linear functional is an
integer, and its equality locus is its actual normal-cone incidence locus. -/
theorem exists_integral_support_value (u : Lattice n) :
    ∃ a : ℤ, ∀ x ∈ P.carrier,
      -(dotProductEquiv ℝ (Fin n) (embed n u)) x ≤ (a : ℝ) ∧
      (-(dotProductEquiv ℝ (Fin n) (embed n u)) x = (a : ℝ) ↔
        embed n u ∈ P.normalCone x) := by
  let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) (embed n u)
  obtain ⟨v, hv, hmin⟩ := P.exists_minimizing_vertex f
  obtain ⟨z, hz, hze⟩ := P.extreme_integral hv
  let a : ℤ := -(∑ i, u i * z i)
  have ha : (a : ℝ) = -f v := by
    rw [← hze]
    simp [a, f, dotProductEquiv, dotProduct, embed]
  refine ⟨a, ?_⟩
  intro x hx
  have hnormal : embed n u ∈ P.normalCone x ↔ ∀ y ∈ P.carrier, f x ≤ f y := by
    change (∀ y ∈ P.carrier, 0 ≤ f (y - x)) ↔ _
    simp only [map_sub, sub_nonneg]
  constructor
  · rw [ha]
    exact neg_le_neg (hmin x hx)
  · rw [ha, neg_inj, hnormal]
    constructor
    · intro he y hy
      rw [he]
      exact hmin y hy
    · intro he
      exact le_antisymm (he v hv.1) (hmin x hx)

/-- Canonical chosen integral support coefficients, defined by actual minima. -/
def integralSupport (u : Lattice n) : ℤ :=
  Classical.choose (P.exists_integral_support_value u)

theorem integralSupport_spec (u : Lattice n) (x : Ambient n) (hx : x ∈ P.carrier) :
    -(dotProductEquiv ℝ (Fin n) (embed n u)) x ≤ (P.integralSupport u : ℝ) ∧
    (-(dotProductEquiv ℝ (Fin n) (embed n u)) x = (P.integralSupport u : ℝ) ↔
      embed n u ∈ P.normalCone x) :=
  Classical.choose_spec (P.exists_integral_support_value u) x hx

/-- The normal fan of an actual lattice polytope has integral strict convex
support. This conclusion follows from literal equality of cone sets. -/
theorem integralSupport_isStrictSupport («Σ» : SmoothCompleteFan n)
    (hfan : «Σ».realCones = P.normalFan) :
    «Σ».IsStrictSupport (fun u => (P.integralSupport u : ℝ)) := by
  intro s hs
  have hmem : (latticeRayCone s : Set (Ambient n)) ∈ «Σ».realCones := ⟨s, hs, rfl⟩
  rw [hfan] at hmem
  obtain ⟨x, hx, hcone⟩ := hmem
  let ℓ : Ambient n →ₗ[ℝ] ℝ := -(dotProductEquiv ℝ (Fin n) x)
  have hpair (u : Lattice n) :
      ℓ (embed n u) = -(dotProductEquiv ℝ (Fin n) (embed n u)) x := by
    simp only [ℓ, LinearMap.neg_apply]
    congr 1
    change (∑ i, x i * embed n u i) = ∑ i, embed n u i * x i
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  refine ⟨ℓ, ?_, ?_⟩
  · intro u hu
    rw [hpair]
    apply (P.integralSupport_spec u x hx).2.mpr
    rw [← hcone]
    exact latticeRayCone_generator s hu
  · intro u hu hus
    rw [hpair]
    apply lt_of_le_of_ne (P.integralSupport_spec u x hx).1
    intro he
    have hnormal := (P.integralSupport_spec u x hx).2.mp he
    rw [← hcone] at hnormal
    exact hus ((«Σ».ray_mem_cone_iff hs hu).mp hnormal)

end LatticePolytope

end PaperVerification.ToricGeometry
end
-- END PaperVerification.ToricPolytopeSupport
end

section
-- BEGIN PaperVerification.ToricDualNormalCone
/-!
# Integral dual bases of actual smooth normal cones

The standard coordinate pairing identifies the dual lattice with the original
coordinate lattice. Under this genuine integral linear equivalence, the dual of
a primitive edge basis is again an integral basis. Its nonnegative real span is
exactly the ordinary supporting normal cone of the polytope.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators

/-- The dual integral basis, represented in the standard coordinate lattice by
the ordinary dot-product pairing. -/
def integralDualBasis {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    Module.Basis (Fin n) ℤ (Lattice n) :=
  b.dualBasis.map (dotProductEquiv ℤ (Fin n)).symm

/-- The defining duality holds for every lattice vector, without any
primitivity or index assumption beyond the genuine integral basis. -/
@[simp] theorem integralDualBasis_pairing {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) (z : Lattice n) :
    (∑ j, integralDualBasis b i j * z j) = b.repr z i := by
  rw [integralDualBasis, Module.Basis.map_apply]
  change (dotProductEquiv ℤ (Fin n)
    ((dotProductEquiv ℤ (Fin n)).symm (b.dualBasis i))) z = _
  rw [LinearEquiv.apply_symm_apply]
  exact b.dualBasis_apply i z

/-- Coordinates in the dual integral basis are evaluations on the original
basis vectors. -/
@[simp] theorem integralDualBasis_repr {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (z : Lattice n) (i : Fin n) :
    (integralDualBasis b).repr z i = ∑ j, z j * b i j := by
  change b.dualBasis.repr ((dotProductEquiv ℤ (Fin n)) z) i = _
  rw [Module.Basis.dualBasis_repr]
  rfl

/-- Real extension of the integral duality. -/
@[simp] theorem integralDualBasis_real_pairing {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) (x : Ambient n) :
    (∑ j, embed n (integralDualBasis b i) j * x j) =
      (integralBasisReal b).repr x i := by
  let f : Ambient n →ₗ[ℝ] ℝ :=
    dotProductEquiv ℝ (Fin n) (embed n (integralDualBasis b i))
  have hf : f = (integralBasisReal b).coord i := by
    apply (integralBasisReal b).ext
    intro k
    change (∑ j, embed n (integralDualBasis b i) j *
      integralBasisReal b k j) = (integralBasisReal b).repr (integralBasisReal b k) i
    rw [integralBasisReal_apply, integralBasisReal_repr]
    have hz := integralDualBasis_pairing b i (b k)
    change (∑ j, (integralDualBasis b i j : ℝ) * (b k j : ℝ)) =
      (b.repr (b k) i : ℝ)
    exact_mod_cast hz
  exact LinearMap.congr_fun hf x

/-- The primitive normal vector is precisely the coefficient vector of the
corresponding real dual coordinate functional. -/
theorem embed_integralDualBasis {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) :
    embed n (integralDualBasis b i) = dualVector ((integralBasisReal b).coord i) := by
  funext j
  change embed n (integralDualBasis b i) j =
    (integralBasisReal b).repr (Pi.basisFun ℝ (Fin n) j) i
  calc
    embed n (integralDualBasis b i) j =
        embed n (integralDualBasis b i) ⬝ᵥ Pi.basisFun ℝ (Fin n) j := by
      rw [Pi.basisFun_apply, dotProduct_single_one]
    _ = _ := integralDualBasis_real_pairing b i (Pi.basisFun ℝ (Fin n) j)

/-- Coordinates in the real dual basis are ordinary pairings with the real
edge basis. This identifies nonnegative coordinates with supporting normals. -/
@[simp] theorem integralDualBasis_real_repr {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (u : Ambient n) (i : Fin n) :
    (integralBasisReal (integralDualBasis b)).repr u i =
      ∑ j, u j * integralBasisReal b i j := by
  let d := integralBasisReal (integralDualBasis b)
  let f : Ambient n →ₗ[ℝ] ℝ :=
    dotProductEquiv ℝ (Fin n) (integralBasisReal b i)
  have hf : d.coord i = f := by
    apply d.ext
    intro k
    change d.repr (d k) i = ∑ j, integralBasisReal b i j * d k j
    rw [Module.Basis.repr_self_apply]
    have hp := integralDualBasis_real_pairing b k (integralBasisReal b i)
    rw [Module.Basis.repr_self_apply] at hp
    simpa only [d, integralBasisReal_apply, mul_comm, eq_comm] using hp.symm
  have h := LinearMap.congr_fun hf u
  change d.repr u i = (integralBasisReal b i) ⬝ᵥ u at h
  simpa only [d, dotProduct, mul_comm] using h

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

/-- Membership of the actual supporting normal cone is exactly
nonnegativity on a complete primitive edge basis. -/
theorem mem_normalCone_iff_basis_pairing
    (vZ : Lattice n) (b : Module.Basis (Fin n) ℤ (Lattice n))
    (lengths : Fin n → ℕ)
    (hedges : ∀ i, 0 < lengths i ∧
      P.IsEdge (embed n vZ) (embed n (vZ + (lengths i : ℤ) • b i)))
    (hcone : ∀ x ∈ P.carrier, ∀ i,
      0 ≤ (integralBasisReal b).repr (x - embed n vZ) i)
    (u : Ambient n) :
    u ∈ P.normalCone (embed n vZ) ↔
      ∀ i, 0 ≤ ∑ j, u j * integralBasisReal b i j := by
  let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) u
  have hnormal : u ∈ P.normalCone (embed n vZ) ↔
      ∀ x ∈ P.carrier, f (embed n vZ) ≤ f x := by
    change (∀ x ∈ P.carrier, 0 ≤ f (x - embed n vZ)) ↔ _
    simp only [map_sub, sub_nonneg]
  rw [hnormal]
  constructor
  · intro hu i
    have h := hu _ (P.edge_endpoints_extreme (hedges i).2).2.1
    rw [map_add, embed_int_smul, map_add, map_smul,
      smul_eq_mul, Int.cast_natCast, ← integralBasisReal_apply b i] at h
    have hl : (0 : ℝ) < lengths i := by exact_mod_cast (hedges i).1
    have hnonneg : 0 ≤ f (integralBasisReal b i) := by nlinarith
    exact hnonneg
  · intro hu x hx
    exact linear_le_of_basis_coordinates (integralBasisReal b) f
      (embed n vZ) x hu (hcone x hx)

/-- The actual normal cone is the nonnegative real cone generated by the
genuine primitive dual integral basis. -/
theorem normalCone_eq_latticeRayCone
    (vZ : Lattice n) (b : Module.Basis (Fin n) ℤ (Lattice n))
    (lengths : Fin n → ℕ)
    (hedges : ∀ i, 0 < lengths i ∧
      P.IsEdge (embed n vZ) (embed n (vZ + (lengths i : ℤ) • b i)))
    (hcone : ∀ x ∈ P.carrier, ∀ i,
      0 ≤ (integralBasisReal b).repr (x - embed n vZ) i) :
    P.normalCone (embed n vZ) =
      (latticeRayCone (Finset.univ.image (integralDualBasis b)) : Set (Ambient n)) := by
  ext u
  change (u ∈ P.normalCone (embed n vZ)) ↔
    u ∈ latticeRayCone (Finset.univ.image (integralDualBasis b))
  rw [P.mem_normalCone_iff_basis_pairing vZ b lengths hedges hcone u,
    mem_latticeRayCone_basis_iff]
  simp only [Finset.mem_univ, not_true_eq_false, false_implies, implies_true,
    and_true, integralDualBasis_real_repr]

/-- Every actual smooth vertex normal cone is generated by a complete
primitive integral basis of normals. No normal-fan smoothness is assumed. -/
theorem smooth_vertex_normalCone_basis (hP : P.Smooth)
    (v : Ambient n) (hv : v ∈ P.carrier.extremePoints ℝ) :
    ∃ d : Module.Basis (Fin n) ℤ (Lattice n),
      P.normalCone v = (latticeRayCone (Finset.univ.image d) : Set (Ambient n)) := by
  obtain ⟨vZ, b, lengths, hvZ, hedges, hcone⟩ := P.smooth_vertex_basis_cone hP v hv
  refine ⟨integralDualBasis b, ?_⟩
  have hedges' : ∀ i, 0 < lengths i ∧
      P.IsEdge (embed n vZ) (embed n (vZ + (lengths i : ℤ) • b i)) := by
    simpa only [hvZ] using hedges
  have hcone' : ∀ x ∈ P.carrier, ∀ i,
      0 ≤ (integralBasisReal b).repr (x - embed n vZ) i := by
    simpa only [hvZ] using hcone
  simpa only [hvZ] using P.normalCone_eq_latticeRayCone vZ b lengths hedges' hcone'

end LatticePolytope

end PaperVerification.ToricGeometry

end
-- END PaperVerification.ToricDualNormalCone
end

section
-- BEGIN PaperVerification.ToricStarBoxCoordinates
/-!
# Integral basis changes and normal heights in a star-subdivision chart

The basis in equation (10) is constructed as an integral transvection.
The height formula and the displacement bounds are then consequences of
its actual vectors, including all tangent directions left unchanged.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

section BasisShear

variable {R E ι : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    [Fintype ι] [DecidableEq ι]

/-- The normal-coordinate functional of the integral shear. -/
def starShearFunctional (b : Module.Basis ι R E) (I : Finset ι) (j : ι) :
    E →ₗ[R] R := -∑ i ∈ I.erase j, b.coord i

theorem starShearFunctional_basis (b : Module.Basis ι R E)
    (I : Finset ι) (j k : ι) :
    starShearFunctional b I j (b k) = if k ∈ I.erase j then -1 else 0 := by
  simp [starShearFunctional, Module.Basis.coord_apply, Module.Basis.repr_self_apply,
    Finsupp.single_apply]
  split_ifs <;> simp

theorem starShearFunctional_pivot (b : Module.Basis ι R E)
    (I : Finset ι) (j : ι) : starShearFunctional b I j (b j) = 0 := by
  simp [starShearFunctional_basis]

/-- The genuine integral basis whose normal vectors are `e_j` and
`e_l-e_j`, with every other direction unchanged. -/
def starShearBasis (b : Module.Basis ι R E) (I : Finset ι) (j : ι) :
    Module.Basis ι R E :=
  b.map (LinearEquiv.transvection (starShearFunctional_pivot b I j))

theorem starShearBasis_apply (b : Module.Basis ι R E)
    (I : Finset ι) (j k : ι) :
    starShearBasis b I j k = if k ∈ I.erase j then b k - b j else b k := by
  simp only [starShearBasis, Module.Basis.map_apply,
    LinearEquiv.transvection.apply, starShearFunctional_basis]
  split_ifs <;> simp [sub_eq_add_neg]

@[simp] theorem starShearBasis_pivot (b : Module.Basis ι R E)
    (I : Finset ι) (j : ι) : starShearBasis b I j j = b j := by
  simp [starShearBasis_apply]

theorem starShearBasis_tangent (b : Module.Basis ι R E)
    (I : Finset ι) (j k : ι) (hk : k ∉ I) :
    starShearBasis b I j k = b k := by
  rw [starShearBasis_apply, if_neg (fun h => hk (Finset.mem_of_mem_erase h))]

/-- The complete box-coordinate sum after the shear. -/
theorem sum_smul_starShearBasis (b : Module.Basis ι R E)
    (I : Finset ι) (j : ι) (a : ι → R) :
    (∑ k, a k • starShearBasis b I j k) =
      (∑ k, a k • b k) - (∑ k ∈ I.erase j, a k) • b j := by
  calc
    (∑ k, a k • starShearBasis b I j k) =
        ∑ k, (a k • b k - (if k ∈ I.erase j then a k else 0) • b j) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [starShearBasis_apply]
      split_ifs <;> simp [smul_sub]
    _ = (∑ k, a k • b k) - (∑ k ∈ I.erase j, a k) • b j := by
      simp only [Finset.sum_sub_distrib, ← Finset.sum_smul, Finset.sum_ite_mem_eq]

/-- All old coordinates of a shifted box, including the special pivot
height, as an exact algebraic identity. -/
theorem coord_shifted_star_box (b : Module.Basis ι R E)
    (I : Finset ι) (j i : ι) (t : R) (a : ι → R) :
    b.coord i (t • b j + ∑ k, a k • starShearBasis b I j k) =
      a i + (if i = j then t - ∑ k ∈ I.erase j, a k else 0) := by
  rw [sum_smul_starShearBasis]
  simp only [map_add, map_sub, map_smul, map_sum,
    Module.Basis.coord_apply, Module.Basis.repr_self_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst i
    simp
    ring
  · simp [hij, Ne.symm hij]

/-- The sum of the old normal heights is precisely `t+a_j`. -/
theorem sum_normal_coords_shifted_star_box (b : Module.Basis ι R E)
    (I : Finset ι) (j : ι) (hj : j ∈ I) (t : R) (a : ι → R) :
    (∑ i ∈ I, b.coord i (t • b j + ∑ k, a k • starShearBasis b I j k)) =
      t + a j := by
  simp only [coord_shifted_star_box, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', if_pos hj]
  rw [← Finset.add_sum_erase I a hj]
  ring

end BasisShear

/-- Extending the integral star-chart basis to the reals gives exactly the
same vectors as performing the real shear. Thus the geometric coordinates
come from a full basis of the ambient integer lattice. -/
theorem integralBasisReal_starShearBasis {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (j : Fin n) :
    integralBasisReal (starShearBasis b I j) =
      starShearBasis (integralBasisReal b) I j := by
  apply Module.Basis.eq_of_apply_eq
  intro k
  rw [integralBasisReal_apply, starShearBasis_apply, starShearBasis_apply]
  split_ifs
  · simp only [map_sub, integralBasisReal_apply]
  · exact (integralBasisReal_apply b k).symm

/-- The new normal heights of every point of a side-`w` shifted box are
nonnegative if the shift is at least `w(q-1)`. Their total lies in
`[t,t+w]`. These are exactly the height bounds used in Section 6.2. -/
theorem shifted_star_box_normal_heights {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (Ambient n))
    (I : Finset (Fin n)) (j : Fin n) (hj : j ∈ I)
    (w t : ℝ) (hw : 0 ≤ w) (ht : w * (I.card - 1 : ℕ) ≤ t)
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ w) :
    (∀ i ∈ I, 0 ≤ b.coord i
      (t • b j + ∑ k, a k • starShearBasis b I j k)) ∧
    t ≤ (∑ i ∈ I, b.coord i
      (t • b j + ∑ k, a k • starShearBasis b I j k)) ∧
    (∑ i ∈ I, b.coord i
      (t • b j + ∑ k, a k • starShearBasis b I j k)) ≤ t + w := by
  have hsum : (∑ k ∈ I.erase j, a k) ≤ w * (I.card - 1 : ℕ) := by
    calc
      (∑ k ∈ I.erase j, a k) ≤ ∑ _k ∈ I.erase j, w :=
        Finset.sum_le_sum (fun k _ => (ha k).2)
      _ = w * (I.card - 1 : ℕ) := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hj]
        ring
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [coord_shifted_star_box]
    by_cases hij : i = j
    · rw [if_pos hij]
      have h := (ha i).1
      linarith
    · rw [if_neg hij, add_zero]
      exact (ha i).1
  · rw [sum_normal_coords_shifted_star_box b I j hj]
    exact le_add_of_nonneg_right (ha j).1
  · rw [sum_normal_coords_shifted_star_box b I j hj]
    exact add_le_add le_rfl (ha j).2

end PaperVerification.ToricGeometry
end
-- END PaperVerification.ToricStarBoxCoordinates
end

#eval "TORIC_DICTIONARY_PART_07_EOF"
