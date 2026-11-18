module

public import Unimodular.Extensions
public import Continuation.Divisor.FanBridgeFoundations
public import Unimodular.FlowOrientations
public import Unimodular.GraphicUniformity
public import Unimodular.RayHyperplanes
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

/-! UNVERIFIED NATIVE RC1 PORT. Exact recovered rc2 proof bodies, with a
smaller genuine import closure. This source is not a record of a new pass.
No theorem from UnimodularPaper, Heller, or series-parallel classification
is assumed or imported. See the adjacent complete provenance manifest. -/

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false




/- Exact recovered source fragment: Unimodular.NormalizedConeFaces. -/
section NativePort_Unimodular_NormalizedConeFaces



noncomputable section

open scoped BigOperators

namespace Unimodular.NormalizedConeFaces

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A geometric face is an actual convex extreme subset of the displayed set. -/
abbrev GeometricFace (A : Set V) := {F : Set V // Convex ℝ F ∧ IsExtreme ℝ A F}

/-- Every conic combination of level-one points has nonnegative level, and a
combination at level zero is the zero vector. No pointedness hypothesis is assumed. -/
theorem level_nonneg_and_zero (A : Set V) (f : V →ₗ[ℝ] ℝ)
    (hf : ∀ x ∈ A, f x = 1) {x : V} (hx : x ∈ PointedCone.hull ℝ A) :
    0 ≤ f x ∧ (f x = 0 → x = 0) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rw [hf x hx]
    exact ⟨zero_le_one,fun h => (one_ne_zero h).elim⟩
  | zero => simp
  | add x y _ _ hx hy =>
    refine ⟨by simpa only [map_add] using add_nonneg hx.1 hy.1,?_⟩
    intro hz
    rw [map_add] at hz
    obtain ⟨hxz,hyz⟩ := (add_eq_zero_iff_of_nonneg hx.1 hy.1).1 hz
    rw [hx.2 hxz,hy.2 hyz,add_zero]
  | smul a x _ hx =>
    have he : f (a • x) = (a : ℝ) * f x := by
      rw [← Nonneg.coe_smul,map_smul,smul_eq_mul]
    refine ⟨by rw [he]; exact mul_nonneg a.2 hx.1,?_⟩
    intro hz
    rw [he] at hz
    rcases mul_eq_zero.1 hz with ha | hfx
    · rw [← Nonneg.coe_smul,ha,zero_smul]
    · rw [hx.2 hfx,smul_zero]

theorem level_pos (A : Set V) (f : V →ₗ[ℝ] ℝ)
    (hf : ∀ x ∈ A, f x = 1) {x : V}
    (hx : x ∈ PointedCone.hull ℝ A) (hne : x ≠ 0) : 0 < f x := by
  obtain ⟨hnon,hzero⟩ := level_nonneg_and_zero A f hf hx
  exact lt_of_le_of_ne hnon (fun h => hne (hzero h.symm))

/-- A level-one section of the conic hull is exactly the original convex set. -/
theorem slice_hull (A : Set V) (hA : Convex ℝ A) (f : V →ₗ[ℝ] ℝ)
    (hf : ∀ x ∈ A, f x = 1) :
    {x | x ∈ PointedCone.hull ℝ A ∧ f x = 1} = A := by
  classical
  ext x
  constructor
  · rintro ⟨hx,hxf⟩
    obtain ⟨c,hcA,hc,hcx⟩ := PointedCone.mem_hull_set.1 hx
    change (∑ y ∈ c.support, c y • y) = x at hcx
    have hh : (∑ y ∈ c.support, c y * f y) = f x := by
      simpa only [map_sum,map_smul,smul_eq_mul] using congrArg f hcx
    have hsum : (∑ y ∈ c.support, c y) = 1 := by
      calc
        (∑ y ∈ c.support, c y) = ∑ y ∈ c.support, c y * f y := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [hf y (hcA hy),mul_one]
        _ = f x := hh
        _ = 1 := hxf
    rw [← hcx]
    exact hA.sum_mem (fun y _ => hc y) hsum (fun y hy => hcA hy)
  · intro hx
    exact ⟨PointedCone.subset_hull hx,hf x hx⟩

theorem normalize_mem (A : Set V) (hA : Convex ℝ A) (f : V →ₗ[ℝ] ℝ)
    (hf : ∀ x ∈ A, f x = 1) {x : V}
    (hx : x ∈ PointedCone.hull ℝ A) (hpos : 0 < f x) : (f x)⁻¹ • x ∈ A := by
  apply (slice_hull A hA f hf).subset
  refine ⟨(PointedCone.hull ℝ A).smul_mem (inv_nonneg.2 hpos.le) hx,?_⟩
  simp only [map_smul,smul_eq_mul,inv_mul_cancel₀ hpos.ne']

/-- Coning a genuine face of a normalized convex set gives a genuine cone face.
This proves the face correspondence needed for both directions of subdivision
constructions; it does not postulate face preservation for coning. -/
theorem hull_isFaceOf (A F : Set V) (hA : Convex ℝ A) (hF : Convex ℝ F)
    (hFA : IsExtreme ℝ A F) (f : V →ₗ[ℝ] ℝ) (hf : ∀ x ∈ A, f x = 1) :
    (PointedCone.hull ℝ F).IsFaceOf (PointedCone.hull ℝ A) := by
  apply PointedCone.IsFaceOf.of_mem_of_add_mem_left (Submodule.span_mono hFA.1)
  intro x y hx hy hxy
  by_cases hx0 : x = 0
  · simpa only [hx0] using (PointedCone.hull ℝ F).zero_mem
  by_cases hy0 : y = 0
  · simpa only [hy0,add_zero] using hxy
  have ha : 0 < f x := level_pos A f hf hx hx0
  have hb : 0 < f y := level_pos A f hf hy hy0
  have hs : 0 < f x + f y := add_pos ha hb
  have hxA := normalize_mem A hA f hf hx ha
  have hyA := normalize_mem A hA f hf hy hb
  have hzF : (f x + f y)⁻¹ • (x + y) ∈ F := by
    simpa only [map_add] using normalize_mem F hF f (fun z hz => hf z (hFA.1 hz))
      hxy (by simpa only [map_add] using hs)
  have hseg : (f x + f y)⁻¹ • (x + y) ∈
      openSegment ℝ ((f x)⁻¹ • x) ((f y)⁻¹ • y) := by
    refine ⟨f x / (f x + f y), f y / (f x + f y),
      div_pos ha hs,div_pos hb hs,?_,?_⟩
    · rw [← add_div,div_self hs.ne']
    · rw [smul_add,smul_smul,smul_smul]
      congr 1 <;> congr 1 <;> field_simp [ha.ne',hb.ne',hs.ne']
  have hxF := hFA.left_mem_of_mem_openSegment hxA hyA hzF hseg
  have hh := (PointedCone.hull ℝ F).smul_mem ha.le (PointedCone.subset_hull hxF)
  simpa only [smul_smul,mul_inv_cancel₀ ha.ne',one_smul] using hh

/-- Slicing any cone face gives a geometric face of the normalized section. -/
theorem section_is_face (A : Set V) (hA : Convex ℝ A)
    {K : PointedCone ℝ V} (hK : K.IsFaceOf (PointedCone.hull ℝ A)) :
    Convex ℝ (A ∩ (K : Set V)) ∧ IsExtreme ℝ A (A ∩ (K : Set V)) := by
  refine ⟨hA.inter K.convex,⟨Set.inter_subset_left,?_⟩⟩
  intro x hx y hy z hz hseg
  exact ⟨hx,hK.isExtreme.left_mem_of_mem_openSegment
    (PointedCone.subset_hull hx) (PointedCone.subset_hull hy) hz.2 hseg⟩

/-- Every cone face is recovered from its actual affine section, including the
zero cone, whose normalized section is empty. -/
theorem hull_section (A : Set V) (hA : Convex ℝ A) (f : V →ₗ[ℝ] ℝ)
    (hf : ∀ x ∈ A, f x = 1) {K : PointedCone ℝ V}
    (hK : K.IsFaceOf (PointedCone.hull ℝ A)) :
    PointedCone.hull ℝ (A ∩ (K : Set V)) = K := by
  apply le_antisymm
  · exact Submodule.span_le.2 Set.inter_subset_right
  · intro x hx
    by_cases hx0 : x = 0
    · simpa only [hx0] using (PointedCone.hull ℝ (A ∩ (K : Set V))).zero_mem
    have hp := level_pos A f hf (hK.le hx) hx0
    have hnorm : (f x)⁻¹ • x ∈ A ∩ (K : Set V) :=
      ⟨normalize_mem A hA f hf (hK.le hx) hp,K.smul_mem (inv_nonneg.2 hp.le) hx⟩
    have hh := (PointedCone.hull ℝ (A ∩ (K : Set V))).smul_mem hp.le
      (PointedCone.subset_hull hnorm)
    simpa only [smul_smul,mul_inv_cancel₀ hp.ne',one_smul] using hh

/-- Every geometric face is recovered by slicing its conic hull. -/
theorem section_hull (A F : Set V) (hF : Convex ℝ F) (hFA : F ⊆ A)
    (f : V →ₗ[ℝ] ℝ) (hf : ∀ x ∈ A, f x = 1) :
    A ∩ (PointedCone.hull ℝ F : Set V) = F := by
  apply Set.Subset.antisymm
  · intro x hx
    exact (slice_hull F hF f (fun x hx => hf x (hFA hx))).subset ⟨hx.2,hf x hx.1⟩
  · exact fun x hx => ⟨hFA hx,PointedCone.subset_hull hx⟩

/-- An order isomorphism between all geometric faces of the affine section and
all genuine faces of its cone. Both directions are the actual coning/section maps. -/
def faceOrderIso (A : Set V) (hA : Convex ℝ A) (f : V →ₗ[ℝ] ℝ)
    (hf : ∀ x ∈ A, f x = 1) :
    GeometricFace A ≃o {K : PointedCone ℝ V // K.IsFaceOf (PointedCone.hull ℝ A)} where
  toFun F := ⟨PointedCone.hull ℝ F.val,hull_isFaceOf A F.val hA F.property.1 F.property.2 f hf⟩
  invFun K := ⟨A ∩ (K.val : Set V),section_is_face A hA K.property⟩
  left_inv F := Subtype.ext (section_hull A F.val F.property.1 F.property.2.1 f hf)
  right_inv K := Subtype.ext (hull_section A hA f hf K.property)
  map_rel_iff' := by
    intro F G
    constructor
    · intro h x hx
      have hm : x ∈ PointedCone.hull ℝ G.val := h (PointedCone.subset_hull hx)
      exact (section_hull A G.val G.property.1 G.property.2.1 f hf).subset
        ⟨F.property.2.1 hx,hm⟩
    · exact fun h => Submodule.span_mono h

/-- A cone generated by level-one points contains no line. -/
theorem hull_salient (A : Set V) (f : V →ₗ[ℝ] ℝ) (hf : ∀ x ∈ A, f x = 1) :
    (PointedCone.hull ℝ A : ConvexCone ℝ V).Salient := by
  intro x hx hne hneg
  have hp := level_pos A f hf hx hne
  have hn := (level_nonneg_and_zero A f hf hneg).1
  rw [map_neg] at hn
  linarith

/-- If two normalized convex sets lie below one another's supporting level,
coning commutes with their intersection. The proof forces their positive radial
scales to agree; no common supporting hyperplane is assumed. -/
theorem hull_inter (A B : Set V) (hA : Convex ℝ A) (hB : Convex ℝ B)
    (f g : V →ₗ[ℝ] ℝ) (hf : ∀ x ∈ A, f x = 1) (hg : ∀ x ∈ B, g x = 1)
    (hfB : ∀ x ∈ B, f x ≤ 1) (hgA : ∀ x ∈ A, g x ≤ 1) :
    PointedCone.hull ℝ (A ∩ B) = PointedCone.hull ℝ A ⊓ PointedCone.hull ℝ B := by
  apply le_antisymm
  · exact le_inf (Submodule.span_mono Set.inter_subset_left)
      (Submodule.span_mono Set.inter_subset_right)
  · intro x hx
    by_cases hx0 : x = 0
    · simpa only [hx0] using (PointedCone.hull ℝ (A ∩ B)).zero_mem
    have hp := level_pos A f hf hx.1 hx0
    have hq := level_pos B g hg hx.2 hx0
    have hnx := normalize_mem A hA f hf hx.1 hp
    have hny := normalize_mem B hB g hg hx.2 hq
    have hfg : f x ≤ g x := by
      have h := hfB _ hny
      have hh : f x / g x ≤ 1 := by
        simpa only [map_smul,smul_eq_mul,div_eq_mul_inv,mul_comm] using h
      exact (div_le_one hq).1 hh
    have hgf : g x ≤ f x := by
      have h := hgA _ hnx
      have hh : g x / f x ≤ 1 := by
        simpa only [map_smul,smul_eq_mul,div_eq_mul_inv,mul_comm] using h
      exact (div_le_one hp).1 hh
    have heq : f x = g x := le_antisymm hfg hgf
    have hn : (f x)⁻¹ • x ∈ A ∩ B := ⟨hnx,by simpa only [heq] using hny⟩
    have hh := (PointedCone.hull ℝ (A ∩ B)).smul_mem hp.le
      (PointedCone.subset_hull hn)
    simpa only [smul_smul,mul_inv_cancel₀ hp.ne',one_smul] using hh

end Unimodular.NormalizedConeFaces

end

end NativePort_Unimodular_NormalizedConeFaces

/- Exact recovered source fragment: Unimodular.PolyhedralSubdivisions. -/
section NativePort_Unimodular_PolyhedralSubdivisions



noncomputable section

namespace Unimodular

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A finite subdivision by actual polytopes, using only genuine extreme points
of the subdivided set. Face closure and intersection compatibility use actual
convex extreme subsets; there is no cone or fan condition among the fields. -/
structure VertexSubdivision (P : Set V) where
  cells : Set (Set V)
  finite_cells : cells.Finite
  vertices : ∀ F ∈ cells, ∃ s : Finset V,
    F = convexHull ℝ (s : Set V) ∧ (s : Set V) ⊆ P.extremePoints ℝ
  cover : ⋃₀ cells = P
  face_closed : ∀ F ∈ cells, ∀ G : Set V,
    Convex ℝ G → IsExtreme ℝ F G → G ∈ cells
  intersection_faces : ∀ F ∈ cells, ∀ G ∈ cells,
    IsExtreme ℝ F (F ∩ G) ∧ IsExtreme ℝ G (F ∩ G)

namespace VertexSubdivision

variable {P : Set V} (D : VertexSubdivision P)

theorem cell_subset {F : Set V} (hF : F ∈ D.cells) : F ⊆ P := by
  intro x hx
  rw [← D.cover]
  exact ⟨F,hF,hx⟩

theorem cell_convex {F : Set V} (hF : F ∈ D.cells) : Convex ℝ F := by
  obtain ⟨s,rfl,hs⟩ := D.vertices F hF
  exact convex_convexHull ℝ _

theorem cell_extremePoints {F : Set V} (hF : F ∈ D.cells) :
    (F.extremePoints ℝ).Finite ∧ F.extremePoints ℝ ⊆ P.extremePoints ℝ := by
  obtain ⟨s,rfl,hs⟩ := D.vertices F hF
  exact ⟨s.finite_toSet.subset extremePoints_convexHull_subset,
    extremePoints_convexHull_subset.trans hs⟩

theorem inter_mem {F G : Set V} (hF : F ∈ D.cells) (hG : G ∈ D.cells) :
    F ∩ G ∈ D.cells :=
  D.face_closed F hF (F ∩ G) ((D.cell_convex hF).inter (D.cell_convex hG))
    (D.intersection_faces F hF G hG).1

theorem empty_mem (hP : P.Nonempty) : (∅ : Set V) ∈ D.cells := by
  obtain ⟨x,hx⟩ := hP
  rw [← D.cover] at hx
  obtain ⟨F,hF,hx⟩ := hx
  exact D.face_closed F hF ∅ convex_empty
    ⟨Set.empty_subset _,fun _ _ _ _ _ h => h.elim⟩

end VertexSubdivision

end Unimodular

end

end NativePort_Unimodular_PolyhedralSubdivisions

/- Exact recovered source fragment: Unimodular.TypeAFanGeometry. -/
section NativePort_Unimodular_TypeAFanGeometry



noncomputable section

namespace Unimodular.TypeAFanGeometry

open scoped BigOperators
open TauCeti.Toric

attribute [local instance] Classical.propDecidable

abbrev Vertex (n : ℕ) := Option (Fin n)
abbrev Edge (n : ℕ) := {pq : Vertex n × Vertex n // pq.1 ≠ pq.2}

/-- Type-A roots in standard integral coordinates, with `none` the root vertex. -/
def latticeRoot {n : ℕ} (p q : Vertex n) : Lattice n :=
  Graphic.vertex (Pi.basisFun ℤ (Fin n)) p - Graphic.vertex (Pi.basisFun ℤ (Fin n)) q

def realRoot {n : ℕ} (p q : Vertex n) : Ambient n := embed (latticeRoot p q)

def rootFamily (n : ℕ) (e : Edge n) : Lattice n := latticeRoot e.val.1 e.val.2

/-- The actual zero-sum coordinates; the omitted root coordinate is recovered
as minus the sum of the other coordinates. -/
def augmented (n : ℕ) : Ambient n →ₗ[ℝ] (Vertex n → ℝ) where
  toFun x p := p.elim (-(∑ i, x i)) x
  map_add' x y := by
    ext p
    cases p <;> simp [Finset.sum_add_distrib, add_comm]
  map_smul' a x := by
    ext p
    cases p <;> simp [Finset.mul_sum, mul_neg]

@[simp] theorem augmented_some {n : ℕ} (x : Ambient n) (i : Fin n) :
    augmented n x (some i) = x i := rfl

@[simp] theorem augmented_none {n : ℕ} (x : Ambient n) :
    augmented n x none = -(∑ i, x i) := rfl

theorem augmented_vertex {n : ℕ} (p : Vertex n) :
    augmented n (embed (Graphic.vertex (Pi.basisFun ℤ (Fin n)) p)) =
      Pi.single p 1 - Pi.single none 1 := by
  ext q
  cases p <;> cases q <;>
    simp [augmented, Graphic.vertex, embed, Pi.basisFun_apply, Pi.single_apply]

@[simp] theorem augmented_root {n : ℕ} (p q : Vertex n) :
    augmented n (realRoot p q) = Pi.single p 1 - Pi.single q 1 := by
  have he : realRoot p q = embed (Graphic.vertex (Pi.basisFun ℤ (Fin n)) p) -
      embed (Graphic.vertex (Pi.basisFun ℤ (Fin n)) q) := by
    ext i
    simp [realRoot, latticeRoot, embed]
  rw [he, map_sub, augmented_vertex, augmented_vertex]
  abel

theorem realRoot_ne_zero {n : ℕ} {p q : Vertex n} (hpq : p ≠ q) :
    realRoot p q ≠ 0 := by
  intro he
  have h := congrFun (congrArg (augmented n) he) p
  simp [Pi.single_apply, hpq, Ne.symm hpq] at h

theorem realRoot_reverse {n : ℕ} (p q : Vertex n) :
    realRoot q p = -realRoot p q := by
  ext i
  simp [realRoot, latticeRoot, embed] <;> ring

@[simp] theorem realRoot_compose {n : ℕ} (p q r : Vertex n) :
    realRoot p q + realRoot q r = realRoot p r := by
  ext i
  simp [realRoot, latticeRoot, embed] <;> ring

/-- The key geometric obstruction in Theorem7.1: two composable directed
root edges cannot lie in one actual fan cone. This uses its face axiom and
salience, including the antipodal case. -/
theorem no_composable_edges {n : ℕ} (Φ : Fan (FanBridge.standardEmbedding n))
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ)
    {C : PointedCone ℝ (Ambient n)} (hC : C ∈ Φ.cones)
    {p q r : Vertex n} (hpq : p ≠ q) (hqr : q ≠ r)
    (hx : realRoot p q ∈ C) (hy : realRoot q r ∈ C) : False := by
  by_cases hpr : p = r
  · subst r
    have hneg : -realRoot p q ∈ C := by
      rw [← realRoot_reverse p q]
      exact hy
    exact (Φ.isToricCone hC).salient _ hx (realRoot_ne_zero hpq) hneg
  have hz : realRoot p r ∈ C := by
    simpa only [realRoot_compose] using C.add_mem hx hy
  have hr : AllowedBlocks.ray (realRoot p r) ∈ Φ.cones :=
    ((hrays _).2 ⟨⟨(p,r),hpr⟩,rfl⟩).1
  have hface : (AllowedBlocks.ray (realRoot p r)).IsFaceOf C := by
    apply Φ.isFaceOf_of_le hC hr
    exact Submodule.span_le.2 (fun _ h => by simpa using h ▸ hz)
  have hxy : realRoot p q + realRoot q r ∈ AllowedBlocks.ray (realRoot p r) := by
    rw [realRoot_compose]
    exact PointedCone.subset_hull (by simp)
  have hin := hface.mem_of_add_mem_left hx hy hxy
  obtain ⟨a, _, ha⟩ := PointedCone.mem_hull_singleton.1 hin
  have hq := congrFun (congrArg (augmented n) ha) q
  simp [map_smul, Pi.single_apply, hpq, Ne.symm hpq, hqr, Ne.symm hqr] at hq

/-- The source vertices of all prescribed roots in a given cone. -/
def sources {n : ℕ} (C : PointedCone ℝ (Ambient n)) : Finset (Vertex n) :=
  Finset.univ.filter (fun p => ∃ q, p ≠ q ∧ realRoot p q ∈ C)

@[simp] theorem mem_sources {n : ℕ} (C : PointedCone ℝ (Ambient n)) (p : Vertex n) :
    p ∈ sources C ↔ ∃ q, p ≠ q ∧ realRoot p q ∈ C := by
  classical
  simp [sources]

/-- The lattice vertices of the cut facet, as the paper specifies them. -/
def cutRoots {n : ℕ} (S : Finset (Vertex n)) : Set (Lattice n) :=
  {x | ∃ p ∈ S, ∃ q, q ∉ S ∧ x = latticeRoot p q}

/-- The cone over one cut facet of the type-A root polytope. -/
def cutCone {n : ℕ} (S : Finset (Vertex n)) : PointedCone ℝ (Ambient n) :=
  PointedCone.hull ℝ (embed '' cutRoots S)

@[simp] theorem cutCone_empty (n : ℕ) : cutCone (∅ : Finset (Vertex n)) = ⊥ := by
  simp [cutCone, cutRoots]

@[simp] theorem cutCone_univ (n : ℕ) : cutCone (Finset.univ : Finset (Vertex n)) = ⊥ := by
  simp [cutCone, cutRoots]

/-- Every edge in a fan cone goes from one of its sources to a nonsource. -/
theorem root_crosses_sources {n : ℕ} (Φ : Fan (FanBridge.standardEmbedding n))
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ)
    {C : PointedCone ℝ (Ambient n)} (hC : C ∈ Φ.cones)
    {p q : Vertex n} (hpq : p ≠ q) (hx : realRoot p q ∈ C) :
    p ∈ sources C ∧ q ∉ sources C := by
  refine ⟨(mem_sources C p).2 ⟨q,hpq,hx⟩, ?_⟩
  intro hq
  obtain ⟨r,hqr,hy⟩ := (mem_sources C q).1 hq
  exact no_composable_edges Φ hrays hC hpq hqr hx hy

/-- Each cone of a genuine fan on the complete root system is contained in a
cut cone. No simpliciality, smoothness, or projectivity is assumed. -/
theorem cone_le_cutCone {n : ℕ} (Φ : Fan (FanBridge.standardEmbedding n))
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ)
    {C : PointedCone ℝ (Ambient n)} (hC : C ∈ Φ.cones) :
    C ≤ cutCone (sources C) := by
  classical
  have hnz (e : Edge n) : FanBridge.standardEmbedding n (rootFamily n e) ≠ 0 :=
    realRoot_ne_zero e.property
  obtain ⟨_,he⟩ := AllowedBlocks.fan_cone_allowed
    (FanBridge.standardEmbedding n) (rootFamily n) hnz hrays hC
  calc
    C = AllowedBlocks.blockCone (FanBridge.standardEmbedding n) (rootFamily n)
        (AllowedBlocks.blockOfCone (FanBridge.standardEmbedding n) (rootFamily n) C) := he.symm
    _ ≤ cutCone (sources C) := by
      apply Submodule.span_le.2
      rintro x ⟨e,he,rfl⟩
      have hx : realRoot e.val.1 e.val.2 ∈ C :=
        (AllowedBlocks.mem_blockOfCone _ _ _ _).1 he
      obtain ⟨hp,hq⟩ := root_crosses_sources Φ hrays hC e.property hx
      exact PointedCone.subset_hull
        ⟨latticeRoot e.val.1 e.val.2,⟨e.val.1,hp,e.val.2,hq,rfl⟩,rfl⟩

/-- A full cone in positive rank selects a nonempty proper cut. -/
theorem full_cone_cut_nontrivial {n : ℕ} (hn : 0 < n)
    (Φ : Fan (FanBridge.standardEmbedding n))
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ)
    {C : PointedCone ℝ (Ambient n)} (hC : C ∈ Φ.cones)
    (hfull : Submodule.span ℝ (C : Set (Ambient n)) = ⊤) :
    (sources C).Nonempty ∧ sources C ≠ Finset.univ := by
  have hnot : C ≠ ⊥ := by
    intro he
    let i : Fin n := ⟨0,hn⟩
    have hm : (Pi.basisFun ℝ (Fin n)) i ∈ Submodule.span ℝ (C : Set (Ambient n)) := by
      rw [hfull]
      trivial
    rw [he] at hm
    have hz : (Pi.basisFun ℝ (Fin n)) i = 0 := by simpa using hm
    exact (Pi.basisFun ℝ (Fin n)).ne_zero i hz
  have hle := cone_le_cutCone Φ hrays hC
  constructor
  · by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.1 h
    rw [he,cutCone_empty] at hle
    exact hnot (bot_unique hle)
  · intro he
    rw [he,cutCone_univ] at hle
    exact hnot (bot_unique hle)

/-- The supporting functional of a cut facet. -/
def cutFunctional {n : ℕ} (S : Finset (Vertex n)) : Ambient n →ₗ[ℝ] ℝ :=
  ∑ p ∈ S, (LinearMap.proj p).comp (augmented n)

theorem cutFunctional_root {n : ℕ} (S : Finset (Vertex n)) (p q : Vertex n) :
    cutFunctional S (realRoot p q) = (if p ∈ S then 1 else 0) - (if q ∈ S then 1 else 0) := by
  classical
  simp [cutFunctional, augmented_root, Finset.sum_sub_distrib, Pi.single_apply, eq_comm]

theorem cutFunctional_root_le_one {n : ℕ} (S : Finset (Vertex n)) (p q : Vertex n) :
    cutFunctional S (realRoot p q) ≤ 1 := by
  classical
  rw [cutFunctional_root]
  split_ifs <;> norm_num

theorem cutFunctional_crossing {n : ℕ} (S : Finset (Vertex n))
    {p q : Vertex n} (hp : p ∈ S) (hq : q ∉ S) :
    cutFunctional S (realRoot p q) = 1 := by
  rw [cutFunctional_root]
  simp [hp,hq]

end Unimodular.TypeAFanGeometry

end

end NativePort_Unimodular_TypeAFanGeometry

/- Exact recovered source fragment: Unimodular.TypeACutCones. -/
section NativePort_Unimodular_TypeACutCones



noncomputable section

namespace Unimodular.TypeAFanGeometry

open scoped BigOperators
open TauCeti.Toric

attribute [local instance] Classical.propDecidable

theorem augmented_nonneg_on_cutCone {n : ℕ} (S : Finset (Vertex n))
    {p : Vertex n} (hp : p ∈ S) {x : Ambient n} (hx : x ∈ cutCone S) :
    0 ≤ augmented n x p := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨v,⟨a,ha,b,hb,rfl⟩,rfl⟩ := hy
      change 0 ≤ augmented n (realRoot a b) p
      rw [augmented_root]
      have hpb : p ≠ b := fun h => hb (h ▸ hp)
      simp only [Pi.sub_apply, Pi.single_apply, if_neg (Ne.symm hpb), sub_zero]
      split_ifs <;> simp_all
  | zero => simp
  | add y z _ _ hy hz =>
      simpa only [map_add, Pi.add_apply] using add_nonneg hy hz
  | smul c y _ hy =>
      rw [← Nonneg.coe_smul, map_smul]
      exact mul_nonneg c.2 hy

theorem augmented_nonpos_on_cutCone {n : ℕ} (S : Finset (Vertex n))
    {p : Vertex n} (hp : p ∉ S) {x : Ambient n} (hx : x ∈ cutCone S) :
    augmented n x p ≤ 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨v,⟨a,ha,b,hb,rfl⟩,rfl⟩ := hy
      change augmented n (realRoot a b) p ≤ 0
      rw [augmented_root]
      have hpa : p ≠ a := fun h => hp (h.symm ▸ ha)
      simp only [Pi.sub_apply, Pi.single_apply, if_neg (Ne.symm hpa), zero_sub]
      split_ifs <;> simp_all
  | zero => simp
  | add y z _ _ hy hz =>
      simpa only [map_add, Pi.add_apply] using add_nonpos hy hz
  | smul c y _ hy =>
      rw [← Nonneg.coe_smul, map_smul]
      exact mul_nonpos_of_nonneg_of_nonpos c.2 hy

/-- A prescribed nonzero root belongs to a cut cone exactly when it crosses
that cut in its displayed orientation. Thus no extra root is hidden in a cut. -/
theorem root_mem_cutCone_iff {n : ℕ} (S : Finset (Vertex n))
    {p q : Vertex n} (hpq : p ≠ q) :
    realRoot p q ∈ cutCone S ↔ p ∈ S ∧ q ∉ S := by
  constructor
  · intro hx
    constructor
    · by_contra hp
      have h := augmented_nonpos_on_cutCone S hp hx
      norm_num [Pi.single_apply, hpq, Ne.symm hpq] at h
    · intro hq
      have h := augmented_nonneg_on_cutCone S hq hx
      norm_num [Pi.single_apply, hpq, Ne.symm hpq] at h
  · rintro ⟨hp,hq⟩
    exact PointedCone.subset_hull ⟨latticeRoot p q,⟨p,hp,q,hq,rfl⟩,rfl⟩

/-- Full-dimensionality forces every label to participate, expressed without
assuming the graph incidence-rank formula. An omitted label would give a
nonzero linear functional annihilating the whole cone. -/
theorem sources_eq_of_full_le_cutCone {n : ℕ} (hn : 0 < n)
    (Φ : Fan (FanBridge.standardEmbedding n))
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ)
    {C : PointedCone ℝ (Ambient n)} (hC : C ∈ Φ.cones)
    (hfull : Submodule.span ℝ (C : Set (Ambient n)) = ⊤)
    (S : Finset (Vertex n)) (hCS : C ≤ cutCone S) : sources C = S := by
  apply Finset.Subset.antisymm
  · intro p hp
    obtain ⟨q,hpq,hx⟩ := (mem_sources C p).1 hp
    exact ((root_mem_cutCone_iff S hpq).1 (hCS hx)).1
  · intro p hp
    by_contra hpn
    let f : Ambient n →ₗ[ℝ] ℝ := (LinearMap.proj p).comp (augmented n)
    have hnz (e : Edge n) : FanBridge.standardEmbedding n (rootFamily n e) ≠ 0 :=
      realRoot_ne_zero e.property
    obtain ⟨_,he⟩ := AllowedBlocks.fan_cone_allowed
      (FanBridge.standardEmbedding n) (rootFamily n) hnz hrays hC
    have hker : C ≤ PointedCone.ofSubmodule (LinearMap.ker f) := by
      calc
        C = AllowedBlocks.blockCone (FanBridge.standardEmbedding n) (rootFamily n)
            (AllowedBlocks.blockOfCone (FanBridge.standardEmbedding n) (rootFamily n) C) := he.symm
        _ ≤ PointedCone.ofSubmodule (LinearMap.ker f) := by
          apply Submodule.span_le.2
          rintro x ⟨e,he,rfl⟩
          have hx : realRoot e.val.1 e.val.2 ∈ C :=
            (AllowedBlocks.mem_blockOfCone _ _ _ _).1 he
          have hcross := (root_mem_cutCone_iff S e.property).1 (hCS hx)
          have hpa : p ≠ e.val.1 := by
            intro heq
            apply hpn
            rw [heq]
            exact (mem_sources C e.val.1).2 ⟨e.val.2,e.property,hx⟩
          have hpb : p ≠ e.val.2 := fun h => hcross.2 (h ▸ hp)
          change f (realRoot e.val.1 e.val.2) = 0
          simp [f, Pi.single_apply, Ne.symm hpa, Ne.symm hpb]
    have hspan : Submodule.span ℝ (C : Set (Ambient n)) ≤ LinearMap.ker f :=
      Submodule.span_le.2 hker
    rw [hfull] at hspan
    have hex : ∃ q : Vertex n, p ≠ q := by
      cases p with
      | none => exact ⟨some ⟨0,hn⟩,by simp⟩
      | some i => exact ⟨none,by simp⟩
    obtain ⟨q,hpq⟩ := hex
    have hz : f (realRoot p q) = 0 := hspan (Submodule.mem_top : realRoot p q ∈ ⊤)
    simp [f, Pi.single_apply, hpq, Ne.symm hpq] at hz

/-- The unique-cut assertion for every full cone of every fan on the full
root system. It is independent of projectivity and smoothness. -/
theorem full_cone_unique_cut {n : ℕ} (hn : 0 < n)
    (Φ : Fan (FanBridge.standardEmbedding n))
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ)
    {C : PointedCone ℝ (Ambient n)} (hC : C ∈ Φ.cones)
    (hfull : Submodule.span ℝ (C : Set (Ambient n)) = ⊤) :
    ∃! S : Finset (Vertex n), S.Nonempty ∧ S ≠ Finset.univ ∧ C ≤ cutCone S := by
  have hnon := full_cone_cut_nontrivial hn Φ hrays hC hfull
  refine ⟨sources C,⟨hnon.1,hnon.2,cone_le_cutCone Φ hrays hC⟩,?_⟩
  intro S hS
  exact (sources_eq_of_full_le_cutCone hn Φ hrays hC hfull S hS.2.2).symm

end Unimodular.TypeAFanGeometry

end

end NativePort_Unimodular_TypeACutCones

/- Exact recovered source fragment: Unimodular.TypeAFacets. -/
section NativePort_Unimodular_TypeAFacets



noncomputable section

namespace Unimodular.TypeAFanGeometry

open scoped BigOperators
open Set

attribute [local instance] Classical.propDecidable

/-- The actual type-A root polytope in the standard rank-n real vector space. -/
def rootPolytope (n : ℕ) : Set (Ambient n) :=
  convexHull ℝ (Set.range (fun e : Edge n => realRoot e.val.1 e.val.2))

/-- The actual exposed cut face, defined by a supporting hyperplane of the
root polytope rather than by a combinatorial model of a face. -/
def cutFace {n : ℕ} (S : Finset (Vertex n)) : Set (Ambient n) :=
  {x | x ∈ rootPolytope n ∧ cutFunctional S x = 1}

/-- A convex face of a convex hull is generated by exactly the original generators
it contains. The argument works for arbitrary generator sets and includes the empty face. -/
theorem convex_face_eq_hull_generators {V : Type*} [AddCommGroup V] [Module ℝ V]
    (U F : Set V) (hF : Convex ℝ F) (he : IsExtreme ℝ (convexHull ℝ U) F) :
    F = convexHull ℝ (U ∩ F) := by
  let H := convexHull ℝ (U ∩ F)
  have hHF : H ⊆ F := convexHull_min Set.inter_subset_right hF
  let T : Set V := {x | x ∈ convexHull ℝ U ∧ (x ∈ F → x ∈ H)}
  have hT : Convex ℝ T := by
    rintro x ⟨hx,hxf⟩ y ⟨hy,hyf⟩ a b ha hb hab
    refine ⟨(convex_convexHull ℝ U) hx hy ha hb hab, ?_⟩
    intro hz
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simpa [ha0,hb1] using hyf (by simpa [ha0,hb1] using hz)
    by_cases hb0 : b = 0
    · have ha1 : a = 1 := by linarith
      simpa [hb0,ha1] using hxf (by simpa [hb0,ha1] using hz)
    have hs : a • x + b • y ∈ openSegment ℝ x y :=
      ⟨a,b,lt_of_le_of_ne ha (Ne.symm ha0),lt_of_le_of_ne hb (Ne.symm hb0),hab,rfl⟩
    exact (convex_convexHull ℝ (U ∩ F))
      (hxf (he.left_mem_of_mem_openSegment hx hy hz hs))
      (hyf (he.right_mem_of_mem_openSegment hx hy hz hs)) ha hb hab
  have hUT : convexHull ℝ U ⊆ T := convexHull_min (by
    intro x hx
    exact ⟨subset_convexHull ℝ U hx, fun hf => subset_convexHull ℝ (U ∩ F) ⟨hx,hf⟩⟩) hT
  exact Set.Subset.antisymm (fun x hx => (hUT (he.subset hx)).2 hx) hHF

variable {n : ℕ}

theorem root_mem_rootPolytope {p q : Vertex n} (hpq : p ≠ q) :
    realRoot p q ∈ rootPolytope n :=
  subset_convexHull ℝ _ ⟨⟨(p,q),hpq⟩,rfl⟩

theorem cutFunctional_le_one_on_polytope (S : Finset (Vertex n))
    {x : Ambient n} (hx : x ∈ rootPolytope n) : cutFunctional S x ≤ 1 := by
  apply convexHull_min (t := {x | cutFunctional S x ≤ 1}) ?_ ?_ hx
  · rintro x ⟨e,rfl⟩
    exact cutFunctional_root_le_one S _ _
  · intro x hx y hy a b ha hb hab
    change cutFunctional S (a • x + b • y) ≤ 1
    rw [map_add,map_smul,map_smul]
    change a * cutFunctional S x + b * cutFunctional S y ≤ 1
    calc
      _ ≤ a * 1 + b * 1 := add_le_add (mul_le_mul_of_nonneg_left hx ha)
        (mul_le_mul_of_nonneg_left hy hb)
      _ = 1 := by simpa using hab

theorem cutFace_convex (S : Finset (Vertex n)) : Convex ℝ (cutFace S) := by
  intro x hx y hy a b ha hb hab
  refine ⟨(convex_convexHull ℝ _) hx.1 hy.1 ha hb hab, ?_⟩
  rw [map_add,map_smul,map_smul,hx.2,hy.2]
  simpa using hab

theorem cutFace_extreme (S : Finset (Vertex n)) :
    IsExtreme ℝ (rootPolytope n) (cutFace S) := by
  refine ⟨fun x hx => hx.1, ?_⟩
  rintro x hx y hy z hz ⟨a,b,ha,hb,hab,he⟩
  refine ⟨hx,?_⟩
  have hxl := cutFunctional_le_one_on_polytope S hx
  have hyl := cutFunctional_le_one_on_polytope S hy
  have hh := congrArg (cutFunctional S) he
  rw [map_add,map_smul,map_smul,hz.2] at hh
  change a * cutFunctional S x + b * cutFunctional S y = 1 at hh
  nlinarith

theorem cutFunctional_root_eq_one_iff (S : Finset (Vertex n)) (p q : Vertex n) :
    cutFunctional S (realRoot p q) = 1 ↔ p ∈ S ∧ q ∉ S := by
  rw [cutFunctional_root]
  by_cases hp : p ∈ S <;> by_cases hq : q ∈ S <;> norm_num [hp,hq]

theorem root_mem_cutFace_iff (S : Finset (Vertex n)) {p q : Vertex n} (hpq : p ≠ q) :
    realRoot p q ∈ cutFace S ↔ p ∈ S ∧ q ∉ S := by
  change (realRoot p q ∈ rootPolytope n ∧ cutFunctional S (realRoot p q) = 1) ↔ _
  rw [cutFunctional_root_eq_one_iff]
  exact and_iff_right (root_mem_rootPolytope hpq)

/-- The supporting cut face consists of the convex hull of precisely the crossing
roots. In particular, its proposed vertices are verified against the full root polytope. -/
theorem cutFace_eq_convexHull (S : Finset (Vertex n)) :
    cutFace S = convexHull ℝ (embed '' cutRoots S) := by
  rw [convex_face_eq_hull_generators
    (Set.range (fun e : Edge n => realRoot e.val.1 e.val.2)) (cutFace S)
    (cutFace_convex S) (cutFace_extreme S)]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨e,rfl⟩,he⟩
    obtain ⟨hp,hq⟩ := (root_mem_cutFace_iff S e.property).1 he
    exact ⟨latticeRoot e.val.1 e.val.2,⟨e.val.1,hp,e.val.2,hq,rfl⟩,rfl⟩
  · rintro ⟨v,⟨p,hp,q,hq,rfl⟩,rfl⟩
    have hpq : p ≠ q := fun h => hq (h ▸ hp)
    exact ⟨⟨⟨(p,q),hpq⟩,rfl⟩,(root_mem_cutFace_iff S hpq).2 ⟨hp,hq⟩⟩

/-- The cut cone used by the fan theorem is literally the conic hull of the
geometric supporting facet just identified. -/
theorem cutCone_eq_hull_cutFace (S : Finset (Vertex n)) :
    cutCone S = PointedCone.hull ℝ (cutFace S) := by
  rw [cutFace_eq_convexHull]
  change PointedCone.hull ℝ (embed '' cutRoots S) =
    PointedCone.hull ℝ (convexHull ℝ (embed '' cutRoots S))
  apply le_antisymm
  · exact Submodule.span_mono (subset_convexHull ℝ _)
  · exact Submodule.span_le.2 (convexHull_min PointedCone.subset_hull
      (PointedCone.convex _))

/-- Slicing the conic hull of a convex set on an affine level-one hyperplane
recovers that set exactly. The proof turns actual conic coefficients into convex
coefficients by applying the supporting functional. -/
theorem hull_slice_eq_of_level_one {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Set V) (hA : Convex ℝ A) (f : V →ₗ[ℝ] ℝ)
    (hf : ∀ x ∈ A, f x = 1) :
    {x | x ∈ PointedCone.hull ℝ A ∧ f x = 1} = A := by
  classical
  ext x
  constructor
  · rintro ⟨hx,hxf⟩
    obtain ⟨c,hcA,hc,hcx⟩ := PointedCone.mem_hull_set.1 hx
    change (∑ y ∈ c.support, c y • y) = x at hcx
    have hh : (∑ y ∈ c.support, c y * f y) = f x := by
      simpa only [map_sum,map_smul,smul_eq_mul] using congrArg f hcx
    have hsum : (∑ y ∈ c.support, c y) = 1 := by
      calc
        (∑ y ∈ c.support, c y) = ∑ y ∈ c.support, c y * f y := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [hf y (hcA hy),mul_one]
        _ = f x := hh
        _ = 1 := hxf
    rw [← hcx]
    exact hA.sum_mem (fun y _ => hc y) hsum (fun y hy => hcA hy)
  · intro hx
    exact ⟨PointedCone.subset_hull hx,hf x hx⟩

/-- The canonical facet slice of a cut cone recovers the actual cut facet,
which is the geometric bridge needed when passing from fans to subdivisions. -/
theorem cutCone_slice_eq_cutFace (S : Finset (Vertex n)) :
    {x | x ∈ cutCone S ∧ cutFunctional S x = 1} = cutFace S := by
  rw [cutCone_eq_hull_cutFace]
  exact hull_slice_eq_of_level_one (cutFace S) (cutFace_convex S)
    (cutFunctional S) (fun x hx => hx.2)

abbrev Source (S : Finset (Vertex n)) := {p : Vertex n // p ∈ S}
abbrev Target (S : Finset (Vertex n)) := {q : Vertex n // q ∉ S}

/-- Source and target barycentric coordinates are read directly from the actual
zero-sum root coordinates, with a minus sign on the target side. -/
def cutCoordinates (S : Finset (Vertex n)) :
    Ambient n →ₗ[ℝ] (Source S → ℝ) × (Target S → ℝ) where
  toFun x := (fun p => augmented n x p.val, fun q => -augmented n x q.val)
  map_add' x y := by
    apply Prod.ext <;> funext p <;> simp [add_comm]
  map_smul' a x := by
    apply Prod.ext <;> funext p <;> simp [smul_eq_mul]

/-- The inverse linear map forgets the root coordinate after putting the two
barycentric coordinate lists in their disjoint source and target positions. -/
def cutSynthesis (S : Finset (Vertex n)) :
    ((Source S → ℝ) × (Target S → ℝ)) →ₗ[ℝ] Ambient n where
  toFun w i := if h : some i ∈ S then w.1 ⟨some i,h⟩ else -w.2 ⟨some i,h⟩
  map_add' x y := by
    ext i
    by_cases h : some i ∈ S <;> simp [h,neg_add,add_comm]
  map_smul' a x := by
    ext i
    by_cases h : some i ∈ S <;> simp [h,smul_eq_mul]

@[simp] theorem cutSynthesis_coordinates (S : Finset (Vertex n)) (x : Ambient n) :
    cutSynthesis S (cutCoordinates S x) = x := by
  ext i
  by_cases h : some i ∈ S <;> simp [cutSynthesis,cutCoordinates,h]

theorem cutCoordinates_injective (S : Finset (Vertex n)) :
    Function.Injective (cutCoordinates S) :=
  Function.LeftInverse.injective (cutSynthesis_coordinates S)

@[simp] theorem cutCoordinates_crossing (S : Finset (Vertex n))
    (p : Source S) (q : Target S) :
    cutCoordinates S (realRoot p.val q.val) = (Pi.single p 1, Pi.single q 1) := by
  apply Prod.ext
  · funext i
    change augmented n (realRoot p.val q.val) i.val = (Pi.single p (1 : ℝ) : Source S → ℝ) i
    rw [augmented_root]
    have hqi : q.val ≠ i.val := fun h => q.property (h.symm ▸ i.property)
    by_cases hpi : p = i
    · subst i
      simp [Pi.single_apply, hqi, Ne.symm hqi]
    · have hpi' : p.val ≠ i.val := fun h => hpi (Subtype.ext h)
      simp [Pi.single_apply, hpi, Ne.symm hpi, hpi', Ne.symm hpi', hqi, Ne.symm hqi]
  · funext i
    change -augmented n (realRoot p.val q.val) i.val = (Pi.single q (1 : ℝ) : Target S → ℝ) i
    rw [augmented_root]
    have hpi : p.val ≠ i.val := fun h => i.property (h ▸ p.property)
    by_cases hqi : q = i
    · subst i
      simp [Pi.single_apply, hpi, Ne.symm hpi]
    · have hqi' : q.val ≠ i.val := fun h => hqi (Subtype.ext h)
      simp [Pi.single_apply, hpi, Ne.symm hpi, hqi, Ne.symm hqi, hqi', Ne.symm hqi']

theorem cutCoordinates_crossing_image (S : Finset (Vertex n)) :
    cutCoordinates S '' (embed '' cutRoots S) =
      Set.range (fun p : Source S => Pi.single p (1 : ℝ)) ×ˢ
        Set.range (fun q : Target S => Pi.single q (1 : ℝ)) := by
  ext w
  constructor
  · rintro ⟨x,⟨v,⟨p,hp,q,hq,rfl⟩,rfl⟩,rfl⟩
    change cutCoordinates S (realRoot p q) ∈ _
    rw [cutCoordinates_crossing S ⟨p,hp⟩ ⟨q,hq⟩]
    exact ⟨⟨⟨p,hp⟩,rfl⟩,⟨⟨q,hq⟩,rfl⟩⟩
  · rcases w with ⟨w₁,w₂⟩
    rintro ⟨⟨p,hp⟩,⟨q,hq⟩⟩
    change Pi.single p (1 : ℝ) = w₁ at hp
    change Pi.single q (1 : ℝ) = w₂ at hq
    rw [← hp,← hq]
    exact ⟨realRoot p.val q.val,
      ⟨latticeRoot p.val q.val,⟨p.val,p.property,q.val,q.property,rfl⟩,rfl⟩,
      cutCoordinates_crossing S p q⟩

/-- The cut face maps onto the literal product of the two standard simplices.
Their index types have cardinalities |S| and n+1-|S|, respectively. -/
theorem cutCoordinates_image_face (S : Finset (Vertex n)) :
    cutCoordinates S '' cutFace S = stdSimplex ℝ (Source S) ×ˢ stdSimplex ℝ (Target S) := by
  rw [cutFace_eq_convexHull, LinearMap.image_convexHull, cutCoordinates_crossing_image,
    convexHull_prod, convexHull_rangle_single_eq_stdSimplex,
    convexHull_rangle_single_eq_stdSimplex]

theorem cutSynthesis_mem_face (S : Finset (Vertex n))
    {w : (Source S → ℝ) × (Target S → ℝ)}
    (hw : w ∈ stdSimplex ℝ (Source S) ×ˢ stdSimplex ℝ (Target S)) :
    cutSynthesis S w ∈ cutFace S := by
  obtain ⟨x,hx,rfl⟩ := (cutCoordinates_image_face S).symm ▸ hw
  simpa only [cutSynthesis_coordinates] using hx

theorem cutCoordinates_synthesis (S : Finset (Vertex n))
    {w : (Source S → ℝ) × (Target S → ℝ)}
    (hw : w ∈ stdSimplex ℝ (Source S) ×ˢ stdSimplex ℝ (Target S)) :
    cutCoordinates S (cutSynthesis S w) = w := by
  obtain ⟨x,hx,rfl⟩ := (cutCoordinates_image_face S).symm ▸ hw
  rw [cutSynthesis_coordinates]

/-- An explicit equivalence of points of the actual cut face and the product of
standard simplices. Both directions are restrictions of the displayed ambient
linear maps, so this is in particular an affine isomorphism of polytopes. -/
def cutFaceSimplexEquiv (S : Finset (Vertex n)) :
    {x : Ambient n // x ∈ cutFace S} ≃
      {w : (Source S → ℝ) × (Target S → ℝ) //
        w ∈ stdSimplex ℝ (Source S) ×ˢ stdSimplex ℝ (Target S)} where
  toFun x := ⟨cutCoordinates S x.val,
    (cutCoordinates_image_face S).subset ⟨x.val,x.property,rfl⟩⟩
  invFun w := ⟨cutSynthesis S w.val,cutSynthesis_mem_face S w.property⟩
  left_inv x := Subtype.ext (cutSynthesis_coordinates S x.val)
  right_inv w := Subtype.ext (cutCoordinates_synthesis S w.property)

/-- The geometric affine-isomorphism statement, spelled out as actual affine
maps between the ambient spaces with inverse restrictions on the two polytopes. -/
theorem cutFace_affine_product (S : Finset (Vertex n)) :
    ∃ (f : Ambient n →ᵃ[ℝ] ((Source S → ℝ) × (Target S → ℝ)))
      (g : ((Source S → ℝ) × (Target S → ℝ)) →ᵃ[ℝ] Ambient n),
      f '' cutFace S = stdSimplex ℝ (Source S) ×ˢ stdSimplex ℝ (Target S) ∧
      (∀ x ∈ cutFace S, g (f x) = x) ∧
      (∀ w ∈ stdSimplex ℝ (Source S) ×ˢ stdSimplex ℝ (Target S), f (g w) = w) :=
  ⟨(cutCoordinates S).toAffineMap,(cutSynthesis S).toAffineMap,
    cutCoordinates_image_face S,fun x _ => cutSynthesis_coordinates S x,
    fun _ hw => cutCoordinates_synthesis S hw⟩

/-- The origin is genuinely in the root polytope whenever a nonzero root exists. -/
theorem zero_mem_rootPolytope {p q : Vertex n} (hpq : p ≠ q) :
    (0 : Ambient n) ∈ rootPolytope n := by
  have hp := root_mem_rootPolytope hpq
  have hq := root_mem_rootPolytope hpq.symm
  have h := (convex_convexHull ℝ _) hp hq
    (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  rw [realRoot_reverse] at h
  simpa only [rootPolytope,smul_neg,add_neg_cancel,neg_add_cancel] using h

/-- A proper actual convex face cannot contain the origin, since every root and
its negative have the origin in their open segment. -/
theorem zero_not_mem_proper_face {F : Set (Ambient n)} (hF : Convex ℝ F)
    (he : IsExtreme ℝ (rootPolytope n) F) (hp : F ≠ rootPolytope n) :
    (0 : Ambient n) ∉ F := by
  intro hz
  apply hp
  apply Set.Subset.antisymm he.subset
  apply convexHull_min _ hF
  rintro x ⟨e,rfl⟩
  apply he.left_mem_of_mem_openSegment (root_mem_rootPolytope e.property)
    (root_mem_rootPolytope e.property.symm) hz
  refine ⟨(1 / 2 : ℝ),1 / 2,by norm_num,by norm_num,by norm_num,?_⟩
  rw [realRoot_reverse,smul_neg,neg_add_cancel]

/-- Two composable roots cannot belong to one proper convex face of the root
polytope. This is a face statement, independent of any fan axioms. -/
theorem face_no_composable {F : Set (Ambient n)} (hF : Convex ℝ F)
    (he : IsExtreme ℝ (rootPolytope n) F) (hproper : F ≠ rootPolytope n)
    {p q r : Vertex n} (hpq : p ≠ q) (hqr : q ≠ r)
    (hx : realRoot p q ∈ F) (hy : realRoot q r ∈ F) : False := by
  have hzP := zero_mem_rootPolytope hpq
  have hpr : realRoot p r ∈ rootPolytope n := by
    by_cases h : p = r
    · subst r
      convert hzP using 1
      ext i
      simp [realRoot,latticeRoot,embed]
    · exact root_mem_rootPolytope h
  let z : Ambient n := (1 / 2 : ℝ) • realRoot p q + (1 / 2 : ℝ) • realRoot q r
  have hz : z ∈ F := hF hx hy (by norm_num) (by norm_num) (by norm_num)
  apply zero_not_mem_proper_face hF he hproper
  apply he.right_mem_of_mem_openSegment hpr hzP hz
  refine ⟨(1 / 2 : ℝ),1 / 2,by norm_num,by norm_num,by norm_num,?_⟩
  dsimp [z]
  rw [← realRoot_compose p q r]
  simp only [smul_add,smul_zero,add_zero]

def faceSources (F : Set (Ambient n)) : Finset (Vertex n) :=
  Finset.univ.filter (fun p => ∃ q, p ≠ q ∧ realRoot p q ∈ F)

@[simp] theorem mem_faceSources (F : Set (Ambient n)) (p : Vertex n) :
    p ∈ faceSources F ↔ ∃ q, p ≠ q ∧ realRoot p q ∈ F := by
  simp [faceSources]

/-- Every nonempty proper actual convex face lies in a cut face. This proves
that the cut list exhausts geometric facets, rather than just producing some faces. -/
theorem proper_face_subset_cut {F : Set (Ambient n)} (hF : Convex ℝ F)
    (he : IsExtreme ℝ (rootPolytope n) F) (hproper : F ≠ rootPolytope n)
    (hne : F.Nonempty) :
    ∃ S : Finset (Vertex n), S.Nonempty ∧ S ≠ Finset.univ ∧ F ⊆ cutFace S := by
  let S := faceSources F
  have hcross : ∀ e : Edge n, realRoot e.val.1 e.val.2 ∈ F →
      e.val.1 ∈ S ∧ e.val.2 ∉ S := by
    intro e hx
    refine ⟨(mem_faceSources F _).2 ⟨e.val.2,e.property,hx⟩,?_⟩
    intro hq
    obtain ⟨r,hqr,hy⟩ := (mem_faceSources F _).1 hq
    exact face_no_composable hF he hproper e.property hqr hx hy
  have hgen := convex_face_eq_hull_generators
    (Set.range (fun e : Edge n => realRoot e.val.1 e.val.2)) F hF he
  have hnegen : (Set.range (fun e : Edge n => realRoot e.val.1 e.val.2) ∩ F).Nonempty := by
    apply (convexHull_nonempty_iff (𝕜 := ℝ)).1
    rwa [← hgen]
  obtain ⟨x,⟨e,rfl⟩,hx⟩ := hnegen
  have hecross := hcross e hx
  refine ⟨S,⟨e.val.1,hecross.1⟩,?_,?_⟩
  · intro hS
    exact hecross.2 (hS.symm ▸ Finset.mem_univ _)
  · rw [hgen]
    apply convexHull_min _ (cutFace_convex S)
    rintro y ⟨⟨f,rfl⟩,hf⟩
    exact (root_mem_cutFace_iff S f.property).2 (hcross f hf)

theorem cutFace_nonempty (S : Finset (Vertex n)) (hne : S.Nonempty)
    (hproper : S ≠ Finset.univ) : (cutFace S).Nonempty := by
  obtain ⟨p,hp⟩ := hne
  have hq : ∃ q : Vertex n, q ∉ S := by
    by_contra h
    push_neg at h
    exact hproper (Finset.eq_univ_iff_forall.2 h)
  obtain ⟨q,hq⟩ := hq
  have hpq : p ≠ q := fun h => hq (h ▸ hp)
  exact ⟨realRoot p q,(root_mem_cutFace_iff S hpq).2 ⟨hp,hq⟩⟩

/-- Distinct proper nonempty cuts give incomparable supporting faces. -/
theorem cutFace_subset_iff {S T : Finset (Vertex n)} (hne : S.Nonempty)
    (hproper : S ≠ Finset.univ) : cutFace S ⊆ cutFace T ↔ S = T := by
  constructor
  · intro hST
    obtain ⟨p,hp⟩ := hne
    have hq : ∃ q : Vertex n, q ∉ S := by
      by_contra h
      push_neg at h
      exact hproper (Finset.eq_univ_iff_forall.2 h)
    obtain ⟨q,hq⟩ := hq
    apply Finset.Subset.antisymm
    · intro a ha
      have haq : a ≠ q := fun h => hq (h ▸ ha)
      exact ((root_mem_cutFace_iff T haq).1
        (hST ((root_mem_cutFace_iff S haq).2 ⟨ha,hq⟩))).1
    · intro b hb
      by_contra hbS
      have hpb : p ≠ b := fun h => hbS (h ▸ hp)
      exact ((root_mem_cutFace_iff T hpb).1
        (hST ((root_mem_cutFace_iff S hpb).2 ⟨hp,hbS⟩))).2 hb
  · rintro rfl
    exact Set.Subset.rfl

/-- A facet is a nonempty maximal proper convex extreme subset of the actual
root polytope. This is the same geometric convention used for other polytopes. -/
def IsRootFacet (F : Set (Ambient n)) : Prop :=
  F.Nonempty ∧ Convex ℝ F ∧ IsExtreme ℝ (rootPolytope n) F ∧
    F ≠ rootPolytope n ∧ ∀ G : Set (Ambient n), Convex ℝ G →
      IsExtreme ℝ (rootPolytope n) G → G ≠ rootPolytope n → F ⊆ G → G = F

/-- Every proper nonempty cut really is a geometric facet. The proof establishes
maximality among all convex faces, without assuming a facet enumeration. -/
theorem cutFace_is_facet (S : Finset (Vertex n)) (hne : S.Nonempty)
    (hproper : S ≠ Finset.univ) : IsRootFacet (cutFace S) := by
  have hFn := cutFace_nonempty S hne hproper
  have hFp : cutFace S ≠ rootPolytope n := by
    obtain ⟨p,hp⟩ := hne
    have hq : ∃ q : Vertex n, q ∉ S := by
      by_contra h
      push_neg at h
      exact hproper (Finset.eq_univ_iff_forall.2 h)
    obtain ⟨q,hq⟩ := hq
    have hpq : p ≠ q := fun h => hq (h ▸ hp)
    intro heq
    have hz : (0 : Ambient n) ∈ cutFace S := heq.symm ▸ zero_mem_rootPolytope hpq
    have hh := hz.2
    simpa using hh
  refine ⟨hFn,cutFace_convex S,cutFace_extreme S,hFp,?_⟩
  intro G hGc hGe hGp hFG
  obtain ⟨T,hTn,hTp,hGT⟩ := proper_face_subset_cut hGc hGe hGp (hFn.mono hFG)
  have hST : S = T := (cutFace_subset_iff hne hproper).1 (hFG.trans hGT)
  subst T
  exact Set.Subset.antisymm hGT hFG

/-- Exact classification of all actual facets of the type-A root polytope. -/
theorem isRootFacet_iff_cutFace (F : Set (Ambient n)) :
    IsRootFacet F ↔ ∃ S : Finset (Vertex n), S.Nonempty ∧ S ≠ Finset.univ ∧ F = cutFace S := by
  constructor
  · rintro ⟨hFn,hFc,hFe,hFp,hmax⟩
    obtain ⟨S,hSn,hSp,hFS⟩ := proper_face_subset_cut hFc hFe hFp hFn
    have hs := cutFace_is_facet S hSn hSp
    exact ⟨S,hSn,hSp,(hmax _ hs.2.1 hs.2.2.1 hs.2.2.2.1 hFS).symm⟩
  · rintro ⟨S,hSn,hSp,rfl⟩
    exact cutFace_is_facet S hSn hSp

/-- Each nonzero root is an actual vertex of the root polytope: intersecting the
source-singleton and target-complement cut faces exposes exactly that point. -/
theorem root_is_extremePoint {p q : Vertex n} (hpq : p ≠ q) :
    realRoot p q ∈ (rootPolytope n).extremePoints ℝ := by
  let A : Finset (Vertex n) := {p}
  let B : Finset (Vertex n) := Finset.univ.erase q
  let F : Set (Ambient n) := cutFace A ∩ cutFace B
  have hFc : Convex ℝ F := (cutFace_convex A).inter (cutFace_convex B)
  have hFe : IsExtreme ℝ (rootPolytope n) F :=
    (cutFace_extreme A).inter (cutFace_extreme B)
  have hroot : realRoot p q ∈ F := by
    constructor
    · apply (root_mem_cutFace_iff A hpq).2
      simp [A,hpq,Ne.symm hpq]
    · apply (root_mem_cutFace_iff B hpq).2
      simp [B,hpq]
  have hgen : Set.range (fun e : Edge n => realRoot e.val.1 e.val.2) ∩ F =
      {realRoot p q} := by
    ext x
    constructor
    · rintro ⟨⟨e,rfl⟩,he⟩
      have ha := (root_mem_cutFace_iff A e.property).1 he.1
      have hb := (root_mem_cutFace_iff B e.property).1 he.2
      have he1 : e.val.1 = p := by simpa [A] using ha.1
      have he2 : e.val.2 = q := by simpa [B] using hb.2
      simp only [Set.mem_singleton_iff,he1,he2]
    · rintro rfl
      exact ⟨⟨⟨(p,q),hpq⟩,rfl⟩,hroot⟩
  have hF : F = {realRoot p q} := by
    rw [convex_face_eq_hull_generators
      (Set.range (fun e : Edge n => realRoot e.val.1 e.val.2)) F hFc hFe,
      hgen,convexHull_singleton]
  rw [hF] at hFe
  exact isExtreme_singleton.1 hFe

/-- The proposed type-A roots are exactly all actual polytope vertices. -/
theorem rootPolytope_extremePoints :
    (rootPolytope n).extremePoints ℝ =
      Set.range (fun e : Edge n => realRoot e.val.1 e.val.2) := by
  apply Set.Subset.antisymm extremePoints_convexHull_subset
  rintro x ⟨e,rfl⟩
  exact root_is_extremePoint e.property

/-- The crossing roots are exactly, and not just a generating subset of, the
vertices of the actual cut facet. -/
theorem cutFace_extremePoints (S : Finset (Vertex n)) :
    (cutFace S).extremePoints ℝ = embed '' cutRoots S := by
  apply Set.Subset.antisymm
  · rw [cutFace_eq_convexHull]
    exact extremePoints_convexHull_subset
  · rintro x ⟨v,⟨p,hp,q,hq,rfl⟩,rfl⟩
    have hpq : p ≠ q := fun h => hq (h ▸ hp)
    exact inter_extremePoints_subset_extremePoints_of_subset (cutFace_extreme S).subset
      ⟨(root_mem_cutFace_iff S hpq).2 ⟨hp,hq⟩,root_is_extremePoint hpq⟩

end Unimodular.TypeAFanGeometry

end

end NativePort_Unimodular_TypeAFacets

/- Exact recovered source fragment: Unimodular.TypeASubdivisions. -/
section NativePort_Unimodular_TypeASubdivisions



noncomputable section

namespace Unimodular.TypeAFanGeometry

open scoped BigOperators Topology
open Filter Set TauCeti.Toric

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

/-- A literal sum of all crossing roots. Its augmented coordinates have the
strict signs of the cut whenever the cut is nonempty and proper. -/
def cutInteriorVector (S : Finset (Vertex n)) : Ambient n :=
  ∑ e : Source S × Target S, realRoot e.1.val e.2.val

theorem crossing_root_mem_cutCone (S : Finset (Vertex n))
    (p : Source S) (q : Target S) : realRoot p.val q.val ∈ cutCone S :=
  PointedCone.subset_hull
    ⟨latticeRoot p.val q.val,⟨p.val,p.property,q.val,q.property,rfl⟩,rfl⟩

theorem cutInteriorVector_mem (S : Finset (Vertex n)) :
    cutInteriorVector S ∈ cutCone S :=
  (cutCone S).sum_mem (fun e _ => crossing_root_mem_cutCone S e.1 e.2)

theorem cutInteriorVector_pos (S : Finset (Vertex n)) (hproper : S ≠ Finset.univ)
    {p : Vertex n} (hp : p ∈ S) : 0 < augmented n (cutInteriorVector S) p := by
  have hq : ∃ q : Vertex n, q ∉ S := by
    by_contra h
    push_neg at h
    exact hproper (Finset.eq_univ_iff_forall.2 h)
  obtain ⟨q,hq⟩ := hq
  have hpq : p ≠ q := fun h => hq (h ▸ hp)
  simp only [cutInteriorVector,map_sum,Finset.sum_apply]
  apply Finset.sum_pos'
  · intro e he
    exact augmented_nonneg_on_cutCone S hp (crossing_root_mem_cutCone S e.1 e.2)
  · refine ⟨(⟨p,hp⟩,⟨q,hq⟩),Finset.mem_univ _,?_⟩
    simp [augmented_root,Pi.single_apply,hpq,Ne.symm hpq]

theorem cutInteriorVector_neg (S : Finset (Vertex n)) (hne : S.Nonempty)
    {q : Vertex n} (hq : q ∉ S) : augmented n (cutInteriorVector S) q < 0 := by
  obtain ⟨p,hp⟩ := hne
  have hpq : p ≠ q := fun h => hq (h ▸ hp)
  simp only [cutInteriorVector,map_sum,Finset.sum_apply]
  apply Finset.sum_neg'
  · intro e he
    exact augmented_nonpos_on_cutCone S hq (crossing_root_mem_cutCone S e.1 e.2)
  · refine ⟨(⟨p,hp⟩,⟨q,hq⟩),Finset.mem_univ _,?_⟩
    simp [augmented_root,Pi.single_apply,hpq,Ne.symm hpq]

/-- Every positive perturbation into the cut has strict signs on every label,
including when the starting point lies on several cut-cone boundaries. -/
theorem cut_perturbation_strict (S : Finset (Vertex n)) (hne : S.Nonempty)
    (hproper : S ≠ Finset.univ) {x : Ambient n} (hx : x ∈ cutCone S)
    {t : ℝ} (ht : 0 < t) :
    (∀ p ∈ S, 0 < augmented n (x + t • cutInteriorVector S) p) ∧
      (∀ q ∉ S, augmented n (x + t • cutInteriorVector S) q < 0) := by
  constructor
  · intro p hp
    have h0 := augmented_nonneg_on_cutCone S hp hx
    have hw := cutInteriorVector_pos S hproper hp
    simp only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    exact add_pos_of_nonneg_of_pos h0 (mul_pos ht hw)
  · intro q hq
    have h0 := augmented_nonpos_on_cutCone S hq hx
    have hw := cutInteriorVector_neg S hne hq
    simp only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    exact add_neg_of_nonpos_of_neg h0 (mul_neg_of_pos_of_neg ht hw)

/-- Strict cut signs identify the cut of any actual fan cone containing the point.
This argument uses both signs, so no unused vertex label is silently discarded. -/
theorem sources_eq_of_strict_signs
    (Φ : Fan (FanBridge.standardEmbedding n))
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ)
    {C : PointedCone ℝ (Ambient n)} (hC : C ∈ Φ.cones)
    (S : Finset (Vertex n)) {x : Ambient n} (hx : x ∈ C)
    (hpos : ∀ p ∈ S, 0 < augmented n x p)
    (hneg : ∀ q ∉ S, augmented n x q < 0) : sources C = S := by
  have hxc := cone_le_cutCone Φ hrays hC hx
  apply Finset.Subset.antisymm
  · intro p hp
    by_contra hpS
    exact (not_le_of_gt (hneg p hpS)) (augmented_nonneg_on_cutCone (sources C) hp hxc)
  · intro p hp
    by_contra hpc
    exact (not_le_of_gt (hpos p hp)) (augmented_nonpos_on_cutCone (sources C) hpc hxc)

/-- Each cut cone is covered by the full-dimensional cones of the complete fan
having precisely that source cut. Boundary points are obtained as limits of strict
cut-sign perturbations in a finite union of genuinely closed fan cones. -/
theorem cutCone_full_cones_cover
    (Φ : Fan (FanBridge.standardEmbedding n)) (hcomplete : Φ.IsComplete)
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ)
    (S : Finset (Vertex n)) (hne : S.Nonempty) (hproper : S ≠ Finset.univ)
    {x : Ambient n} (hx : x ∈ cutCone S) :
    ∃ C ∈ Φ.cones, Submodule.span ℝ (C : Set (Ambient n)) = ⊤ ∧
      sources C = S ∧ x ∈ C := by
  let Q := {C : Φ.cones // Submodule.span ℝ (C.1 : Set (Ambient n)) = ⊤ ∧ sources C.1 = S}
  let T : Set (Ambient n) := ⋃ C : Q, (C.1.1 : Set (Ambient n))
  have hTc : IsClosed T := isClosed_iUnion_of_finite
    (fun C : Q => ConeInterior.isClosed_of_fg (Φ.isToricCone C.1.2).fg)
  have hperturb : ∀ t : ℝ, 0 < t → x + t • cutInteriorVector S ∈ T := by
    intro t ht
    obtain ⟨C,hC,hfull,hxC⟩ := FanMaximalCones.full_cones_cover Φ hcomplete
      (x + t • cutInteriorVector S)
    have hsign := cut_perturbation_strict S hne hproper hx ht
    have hsource := sources_eq_of_strict_signs Φ hrays hC S hxC hsign.1 hsign.2
    exact Set.mem_iUnion.2 ⟨⟨⟨C,hC⟩,hfull,hsource⟩,hxC⟩
  have hc : Continuous (fun t : ℝ => x + t • cutInteriorVector S) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have ht : Tendsto (fun t : ℝ => x + t • cutInteriorVector S) (𝓝[>] 0) (𝓝 x) := by
    have h := (hc.tendsto (0 : ℝ)).mono_left
      (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
    simpa only [zero_smul,add_zero] using h
  have hxT : x ∈ T := hTc.mem_of_tendsto ht (by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hperturb t ht)
  obtain ⟨C,hxC⟩ := Set.mem_iUnion.1 hxT
  exact ⟨C.1.1,C.1.2,C.2.1,C.2.2,hxC⟩

/-- Equality of actual point sets, not a definition of subdivision. -/
theorem cutCone_eq_union_fan_cones
    (Φ : Fan (FanBridge.standardEmbedding n)) (hcomplete : Φ.IsComplete)
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ)
    (S : Finset (Vertex n)) (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    (cutCone S : Set (Ambient n)) =
      {x | ∃ C ∈ Φ.cones, sources C = S ∧ x ∈ C} := by
  ext x
  constructor
  · intro hx
    obtain ⟨C,hC,hfull,hsource,hxC⟩ := cutCone_full_cones_cover
      Φ hcomplete hrays S hne hproper hx
    exact ⟨C,hC,hsource,hxC⟩
  · rintro ⟨C,hC,hsource,hxC⟩
    have h := cone_le_cutCone Φ hrays hC hxC
    rwa [hsource] at h

/-- The actual bounded slice of a fan cone in the supporting hyperplane of a cut. -/
def sliceCell (S : Finset (Vertex n)) (C : PointedCone ℝ (Ambient n)) : Set (Ambient n) :=
  {x | x ∈ C ∧ cutFunctional S x = 1}

theorem sliceCell_convex (S : Finset (Vertex n)) (C : PointedCone ℝ (Ambient n)) :
    Convex ℝ (sliceCell S C) := by
  intro x hx y hy a b ha hb hab
  refine ⟨C.convex hx.1 hy.1 ha hb hab,?_⟩
  rw [map_add,map_smul,map_smul,hx.2,hy.2]
  simpa using hab

theorem sliceCell_inf (S : Finset (Vertex n)) (C D : PointedCone ℝ (Ambient n)) :
    sliceCell S (C ⊓ D) = sliceCell S C ∩ sliceCell S D := by
  ext x
  simp only [sliceCell,Set.mem_setOf_eq,Submodule.mem_inf,Set.mem_inter_iff]
  tauto

theorem sliceCell_isExtreme_of_face (S : Finset (Vertex n))
    {C D : PointedCone ℝ (Ambient n)} (hD : D.IsFaceOf C) :
    IsExtreme ℝ (sliceCell S C) (sliceCell S D) := by
  refine ⟨fun x hx => ⟨hD.le hx.1,hx.2⟩,?_⟩
  intro x hx y hy z hz hseg
  exact ⟨hD.isExtreme.left_mem_of_mem_openSegment hx.1 hy.1 hz.1 hseg,hx.2⟩

/-- Actual fan intersections slice to common geometric faces of the cells. -/
theorem sliceCell_intersection_face (Φ : Fan (FanBridge.standardEmbedding n))
    (S : Finset (Vertex n)) {C D : PointedCone ℝ (Ambient n)}
    (hC : C ∈ Φ.cones) (hD : D ∈ Φ.cones) :
    IsExtreme ℝ (sliceCell S C) (sliceCell S C ∩ sliceCell S D) ∧
      IsExtreme ℝ (sliceCell S D) (sliceCell S C ∩ sliceCell S D) := by
  rw [← sliceCell_inf]
  exact ⟨sliceCell_isExtreme_of_face S (Φ.inf_isFaceOf_left hC hD),
    sliceCell_isExtreme_of_face S (Φ.inf_isFaceOf_right hC hD)⟩

/-- Every point of the actual cut facet is covered by a slice of a full fan cone
with that cut; conversely each such slice is contained in that facet. -/
theorem cutFace_eq_union_full_slices
    (Φ : Fan (FanBridge.standardEmbedding n)) (hcomplete : Φ.IsComplete)
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ)
    (S : Finset (Vertex n)) (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    cutFace S = {x | ∃ C ∈ Φ.cones,
      Submodule.span ℝ (C : Set (Ambient n)) = ⊤ ∧ sources C = S ∧ x ∈ sliceCell S C} := by
  ext x
  constructor
  · intro hx
    have hxc : x ∈ cutCone S := by
      have h := (cutCone_slice_eq_cutFace S).symm ▸ hx
      exact h.1
    obtain ⟨C,hC,hfull,hsource,hxC⟩ := cutCone_full_cones_cover
      Φ hcomplete hrays S hne hproper hxc
    exact ⟨C,hC,hfull,hsource,hxC,hx.2⟩
  · rintro ⟨C,hC,hfull,hsource,hxC,hlevel⟩
    apply (cutCone_slice_eq_cutFace S).subset
    have hxc := cone_le_cutCone Φ hrays hC hxC
    rw [hsource] at hxc
    exact ⟨hxc,hlevel⟩

/-- The actual prescribed root points lying in a cone; these are finite because
there are only finitely many directed label pairs. -/
def coneRootSet (C : PointedCone ℝ (Ambient n)) : Set (Ambient n) :=
  (fun e : Edge n => realRoot e.val.1 e.val.2) ''
    {e | realRoot e.val.1 e.val.2 ∈ C}

theorem coneRootSet_finite (C : PointedCone ℝ (Ambient n)) : (coneRootSet C).Finite :=
  (Set.toFinite _).image _

theorem fan_cone_eq_hull_roots (Φ : Fan (FanBridge.standardEmbedding n))
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ)
    {C : PointedCone ℝ (Ambient n)} (hC : C ∈ Φ.cones) :
    C = PointedCone.hull ℝ (coneRootSet C) := by
  have hnz (e : Edge n) : FanBridge.standardEmbedding n (rootFamily n e) ≠ 0 :=
    realRoot_ne_zero e.property
  obtain ⟨ha,he⟩ := AllowedBlocks.fan_cone_allowed
    (FanBridge.standardEmbedding n) (rootFamily n) hnz hrays hC
  have hset : ((fun e : Edge n => FanBridge.standardEmbedding n (rootFamily n e)) ''
      (AllowedBlocks.blockOfCone (FanBridge.standardEmbedding n) (rootFamily n) C : Set (Edge n))) =
        coneRootSet C := by
    ext x
    constructor
    · rintro ⟨e,he,rfl⟩
      exact ⟨e,(AllowedBlocks.mem_blockOfCone _ _ _ _).1 he,rfl⟩
    · rintro ⟨e,he,rfl⟩
      exact ⟨e,(AllowedBlocks.mem_blockOfCone _ _ _ _).2 he,rfl⟩
  exact he.symm.trans (congrArg (PointedCone.hull ℝ) hset)

/-- A fan cone's canonical slice is the convex hull of exactly its root generators.
The supporting functional normalizes the conic coefficients, so there are no added
intersection vertices in the slice. -/
theorem sliceCell_eq_convexHull_roots (Φ : Fan (FanBridge.standardEmbedding n))
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ)
    (S : Finset (Vertex n)) {C : PointedCone ℝ (Ambient n)}
    (hC : C ∈ Φ.cones) (hCS : C ≤ cutCone S) :
    sliceCell S C = convexHull ℝ (coneRootSet C) := by
  let R := coneRootSet C
  have hlevel : ∀ x ∈ R, cutFunctional S x = 1 := by
    rintro x ⟨e,he,rfl⟩
    obtain ⟨hp,hq⟩ := (root_mem_cutCone_iff S e.property).1 (hCS he)
    exact cutFunctional_crossing S hp hq
  have hlevelH : ∀ x ∈ convexHull ℝ R, cutFunctional S x = 1 := by
    apply convexHull_min (t := {x | cutFunctional S x = 1}) hlevel
    intro x hx y hy a b ha hb hab
    change cutFunctional S (a • x + b • y) = 1
    rw [map_add,map_smul,map_smul,hx,hy]
    simpa using hab
  have hh : PointedCone.hull ℝ (convexHull ℝ R) = PointedCone.hull ℝ R := by
    apply le_antisymm
    · exact Submodule.span_le.2 (convexHull_min PointedCone.subset_hull
        (PointedCone.convex _))
    · exact Submodule.span_mono (subset_convexHull ℝ R)
  have hgen : C = PointedCone.hull ℝ (convexHull ℝ R) :=
    (fan_cone_eq_hull_roots Φ hrays hC).trans hh.symm
  exact (congrArg (fun K : PointedCone ℝ (Ambient n) =>
    {x | x ∈ K ∧ cutFunctional S x = 1}) hgen).trans
      (hull_slice_eq_of_level_one (convexHull ℝ R) (convex_convexHull ℝ R)
        (cutFunctional S) hlevelH)

theorem coneRootSet_subset_facet_vertices (S : Finset (Vertex n))
    {C : PointedCone ℝ (Ambient n)} (hCS : C ≤ cutCone S) :
    coneRootSet C ⊆ (cutFace S).extremePoints ℝ := by
  rw [cutFace_extremePoints]
  rintro x ⟨e,he,rfl⟩
  obtain ⟨hp,hq⟩ := (root_mem_cutCone_iff S e.property).1 (hCS he)
  exact ⟨latticeRoot e.val.1 e.val.2,⟨e.val.1,hp,e.val.2,hq,rfl⟩,rfl⟩

/-- Every slice's roots are all its actual vertices, not merely a convenient
finite generating set. -/
theorem sliceCell_extremePoints (Φ : Fan (FanBridge.standardEmbedding n))
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ)
    (S : Finset (Vertex n)) {C : PointedCone ℝ (Ambient n)}
    (hC : C ∈ Φ.cones) (hCS : C ≤ cutCone S) :
    (sliceCell S C).extremePoints ℝ = coneRootSet C := by
  rw [sliceCell_eq_convexHull_roots Φ hrays S hC hCS]
  apply Set.Subset.antisymm extremePoints_convexHull_subset
  intro x hx
  have hR : coneRootSet C ⊆ rootPolytope n := by
    rintro y ⟨e,he,rfl⟩
    exact root_mem_rootPolytope e.property
  have hHP : convexHull ℝ (coneRootSet C) ⊆ rootPolytope n :=
    convexHull_min hR (convex_convexHull ℝ _)
  obtain ⟨e,he,rfl⟩ := hx
  exact inter_extremePoints_subset_extremePoints_of_subset hHP
    ⟨subset_convexHull ℝ _ ⟨e,he,rfl⟩,root_is_extremePoint e.property⟩

/-- Each sliced fan cell is an actual finite polytope, with its entire vertex set
contained in the genuine vertex set of the cut facet. -/
theorem sliceCell_finite_vertex_polytope (Φ : Fan (FanBridge.standardEmbedding n))
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ)
    (S : Finset (Vertex n)) {C : PointedCone ℝ (Ambient n)}
    (hC : C ∈ Φ.cones) (hCS : C ≤ cutCone S) :
    ∃ V : Finset (Ambient n), (V : Set (Ambient n)) ⊆ (cutFace S).extremePoints ℝ ∧
      sliceCell S C = convexHull ℝ (V : Set (Ambient n)) ∧
      (sliceCell S C).extremePoints ℝ = (V : Set (Ambient n)) := by
  classical
  let hfin := coneRootSet_finite C
  refine ⟨hfin.toFinset,?_,?_,?_⟩
  · simpa only [Set.Finite.coe_toFinset] using coneRootSet_subset_facet_vertices S hCS
  · simpa only [Set.Finite.coe_toFinset] using sliceCell_eq_convexHull_roots Φ hrays S hC hCS
  · simpa only [Set.Finite.coe_toFinset] using sliceCell_extremePoints Φ hrays S hC hCS

/-- The intrinsic cell of a root cone, independent of which cut contains it. -/
def rootCell (C : PointedCone ℝ (Ambient n)) : Set (Ambient n) :=
  convexHull ℝ (coneRootSet C)

theorem coneRootSet_mono {C D : PointedCone ℝ (Ambient n)} (hCD : C ≤ D) :
    coneRootSet C ⊆ coneRootSet D := by
  rintro x ⟨e,he,rfl⟩
  exact ⟨e,hCD he,rfl⟩

theorem rootCell_mono {C D : PointedCone ℝ (Ambient n)} (hCD : C ≤ D) :
    rootCell C ⊆ rootCell D := convexHull_mono (coneRootSet_mono hCD)

theorem rootCell_subset_cone (C : PointedCone ℝ (Ambient n)) :
    rootCell C ⊆ (C : Set (Ambient n)) := by
  apply convexHull_min _ C.convex
  rintro x ⟨e,he,rfl⟩
  exact he

/-- Slicing in two different containing cut facets gives precisely the same
polytope. Thus cells on shared faces do not depend on a chosen facet label. -/
theorem sliceCell_eq_of_two_cuts (Φ : Fan (FanBridge.standardEmbedding n))
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ)
    {C : PointedCone ℝ (Ambient n)} (hC : C ∈ Φ.cones)
    {S T : Finset (Vertex n)} (hS : C ≤ cutCone S) (hT : C ≤ cutCone T) :
    sliceCell S C = sliceCell T C := by
  rw [sliceCell_eq_convexHull_roots Φ hrays S hC hS,
    sliceCell_eq_convexHull_roots Φ hrays T hC hT]

/-- Cells from any two facets, not merely cells inside a fixed cut, meet in the
cell of the literal intersection cone. -/
theorem rootCell_inf (Φ : Fan (FanBridge.standardEmbedding n))
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ)
    {C D : PointedCone ℝ (Ambient n)} (hC : C ∈ Φ.cones) (hD : D ∈ Φ.cones) :
    rootCell (C ⊓ D) = rootCell C ∩ rootCell D := by
  apply Set.Subset.antisymm
  · exact fun x hx => ⟨rootCell_mono inf_le_left hx, rootCell_mono inf_le_right hx⟩
  · intro x hx
    have hCS := cone_le_cutCone Φ hrays hC
    have hCDS : C ⊓ D ≤ cutCone (sources C) := inf_le_left.trans hCS
    have hslice : x ∈ sliceCell (sources C) C := by
      rw [sliceCell_eq_convexHull_roots Φ hrays (sources C) hC hCS]
      exact hx.1
    rw [rootCell, ← sliceCell_eq_convexHull_roots Φ hrays (sources C)
      (Φ.inf_mem hC hD) hCDS]
    exact ⟨⟨rootCell_subset_cone C hx.1,rootCell_subset_cone D hx.2⟩,hslice.2⟩

/-- Global face-to-face compatibility of the actual boundary polytopes, including
cells belonging to different cut facets. -/
theorem rootCell_intersection_faces (Φ : Fan (FanBridge.standardEmbedding n))
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ)
    {C D : PointedCone ℝ (Ambient n)} (hC : C ∈ Φ.cones) (hD : D ∈ Φ.cones) :
    IsExtreme ℝ (rootCell C) (rootCell C ∩ rootCell D) ∧
      IsExtreme ℝ (rootCell D) (rootCell C ∩ rootCell D) := by
  rw [← rootCell_inf Φ hrays hC hD]
  have hCS := cone_le_cutCone Φ hrays hC
  have hDS := cone_le_cutCone Φ hrays hD
  constructor
  · change IsExtreme ℝ (convexHull ℝ (coneRootSet C))
      (convexHull ℝ (coneRootSet (C ⊓ D)))
    rw [← sliceCell_eq_convexHull_roots Φ hrays (sources C) hC hCS,
      ← sliceCell_eq_convexHull_roots Φ hrays (sources C) (Φ.inf_mem hC hD)
        (inf_le_left.trans hCS)]
    exact sliceCell_isExtreme_of_face (sources C) (Φ.inf_isFaceOf_left hC hD)
  · change IsExtreme ℝ (convexHull ℝ (coneRootSet D))
      (convexHull ℝ (coneRootSet (C ⊓ D)))
    rw [← sliceCell_eq_convexHull_roots Φ hrays (sources D) hD hDS,
      ← sliceCell_eq_convexHull_roots Φ hrays (sources D) (Φ.inf_mem hC hD)
        (inf_le_right.trans hDS)]
    exact sliceCell_isExtreme_of_face (sources D) (Φ.inf_isFaceOf_right hC hD)

/-- Coning the intrinsic cell recovers exactly the original fan cone. This is
also valid for the zero cone, whose cell is empty. -/
theorem hull_rootCell (Φ : Fan (FanBridge.standardEmbedding n))
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ)
    {C : PointedCone ℝ (Ambient n)} (hC : C ∈ Φ.cones) :
    PointedCone.hull ℝ (rootCell C) = C := by
  apply le_antisymm
  · exact Submodule.span_le.2 (rootCell_subset_cone C)
  · calc
      C = PointedCone.hull ℝ (coneRootSet C) := fan_cone_eq_hull_roots Φ hrays hC
      _ ≤ PointedCone.hull ℝ (rootCell C) :=
        Submodule.span_mono (subset_convexHull ℝ (coneRootSet C))

/-- The boundary cell family determines the genuine fan uniquely; taking cones
from the origin is a proved inverse, not part of a definition of compatibility. -/
theorem cones_eq_of_rootCells_eq
    (Φ Ψ : Fan (FanBridge.standardEmbedding n))
    (hΦ : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ)
    (hΨ : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Ψ)
    (hCells : rootCell '' Φ.cones = rootCell '' Ψ.cones) : Φ.cones = Ψ.cones := by
  ext C
  constructor
  · intro hC
    obtain ⟨D,hD,hCD⟩ := hCells ▸ (show rootCell C ∈ rootCell '' Φ.cones from ⟨C,hC,rfl⟩)
    have he := congrArg (PointedCone.hull ℝ) hCD
    rw [hull_rootCell Ψ hΨ hD,hull_rootCell Φ hΦ hC] at he
    exact he ▸ hD
  · intro hC
    obtain ⟨D,hD,hCD⟩ := hCells.symm ▸ (show rootCell C ∈ rootCell '' Ψ.cones from ⟨C,hC,rfl⟩)
    have he := congrArg (PointedCone.hull ℝ) hCD
    rw [hull_rootCell Φ hΦ hD,hull_rootCell Ψ hΨ hC] at he
    exact he ▸ hD

/-- An intrinsic cell in a cut cone lies in the actual cut facet. -/
theorem rootCell_subset_cutFace (Φ : Fan (FanBridge.standardEmbedding n))
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ)
    {C : PointedCone ℝ (Ambient n)} (hC : C ∈ Φ.cones)
    {S : Finset (Vertex n)} (hCS : C ≤ cutCone S) : rootCell C ⊆ cutFace S := by
  rw [rootCell, ← sliceCell_eq_convexHull_roots Φ hrays S hC hCS]
  intro x hx
  exact (cutCone_slice_eq_cutFace S).subset ⟨hCS hx.1,hx.2⟩

/-- Restricting one cell to any other cut facet yields the cell of an actual face
cone of the original fan. The exposing functional is the difference of the two
cut functionals; its nonnegativity is proved on all generating roots. -/
theorem rootCell_inter_cutFace (Φ : Fan (FanBridge.standardEmbedding n))
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ)
    {C : PointedCone ℝ (Ambient n)} (hC : C ∈ Φ.cones)
    (S T : Finset (Vertex n)) (hCS : C ≤ cutCone S) :
    ∃ D ∈ Φ.cones, D.IsFaceOf C ∧ D ≤ cutCone S ∧ D ≤ cutCone T ∧
      rootCell C ∩ cutFace T = rootCell D := by
  let φ : Ambient n →ₗ[ℝ] ℝ := cutFunctional S - cutFunctional T
  have hφR : ∀ x ∈ coneRootSet C, 0 ≤ φ x := by
    rintro x ⟨e,he,rfl⟩
    obtain ⟨hp,hq⟩ := (root_mem_cutCone_iff S e.property).1 (hCS he)
    change 0 ≤ cutFunctional S (realRoot e.val.1 e.val.2) -
      cutFunctional T (realRoot e.val.1 e.val.2)
    rw [cutFunctional_crossing S hp hq]
    exact sub_nonneg.2 (cutFunctional_root_le_one T _ _)
  have hφ : ∀ x ∈ C, 0 ≤ φ x := by
    intro x hx
    rw [fan_cone_eq_hull_roots Φ hrays hC] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hφR x hx
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_nonneg hx hy
    | smul a x _ hx =>
      rw [← Nonneg.coe_smul, map_smul, smul_eq_mul]
      exact mul_nonneg a.2 hx
  let D := C ⊓ PointedCone.ofSubmodule (LinearMap.ker φ)
  have hDC : D.IsFaceOf C := by
    refine ⟨inf_le_left,fun {x y a} hx hy ha hxy => ⟨hx,?_⟩⟩
    have hker : φ (a • x + y) = 0 := hxy.2
    rw [map_add,map_smul,smul_eq_mul] at hker
    have haz : a * φ x = 0 :=
      ((add_eq_zero_iff_of_nonneg (mul_nonneg ha.le (hφ x hx)) (hφ y hy)).1 hker).1
    exact (mul_eq_zero.1 haz).resolve_left ha.ne'
  have hD : D ∈ Φ.cones := Φ.mem_of_isFaceOf hC hDC
  have hDS : D ≤ cutCone S := hDC.le.trans hCS
  have hDT : D ≤ cutCone T := by
    calc
      D = PointedCone.hull ℝ (coneRootSet D) := fan_cone_eq_hull_roots Φ hrays hD
      _ ≤ cutCone T := by
        apply Submodule.span_le.2
        rintro x ⟨e,he,rfl⟩
        obtain ⟨hp,hq⟩ := (root_mem_cutCone_iff S e.property).1 (hDS he)
        have hz : φ (realRoot e.val.1 e.val.2) = 0 := he.2
        have ht : cutFunctional T (realRoot e.val.1 e.val.2) = 1 := by
          change cutFunctional S (realRoot e.val.1 e.val.2) -
            cutFunctional T (realRoot e.val.1 e.val.2) = 0 at hz
          rw [cutFunctional_crossing S hp hq] at hz
          linarith
        obtain ⟨hpt,hqt⟩ := (cutFunctional_root_eq_one_iff T _ _).1 ht
        exact (root_mem_cutCone_iff T e.property).2 ⟨hpt,hqt⟩
  refine ⟨D,hD,hDC,hDS,hDT,?_⟩
  apply Set.Subset.antisymm
  · intro x hx
    have hs := rootCell_subset_cutFace Φ hrays hC hCS hx.1
    rw [rootCell, ← sliceCell_eq_convexHull_roots Φ hrays S hD hDS]
    refine ⟨⟨rootCell_subset_cone C hx.1,?_⟩,hs.2⟩
    change cutFunctional S x - cutFunctional T x = 0
    rw [hs.2,hx.2.2,sub_self]
  · exact fun x hx => ⟨rootCell_mono hDC.le hx,
      rootCell_subset_cutFace Φ hrays hD hDT hx⟩

/-- The cells assigned to one cut facet are literal geometric polytopes. -/
def cutCells (Φ : Fan (FanBridge.standardEmbedding n)) (S : Finset (Vertex n)) :
    Set (Set (Ambient n)) := {F | ∃ C ∈ Φ.cones, C ≤ cutCone S ∧ F = rootCell C}

theorem cutCells_finite (Φ : Fan (FanBridge.standardEmbedding n))
    (S : Finset (Vertex n)) : (cutCells Φ S).Finite := by
  apply (Φ.finite_cones.image rootCell).subset
  rintro F ⟨C,hC,hCS,rfl⟩
  exact ⟨C,hC,rfl⟩

/-- The cells exhaust the actual facet, including all boundary points. -/
theorem cutCells_cover (Φ : Fan (FanBridge.standardEmbedding n))
    (hcomplete : Φ.IsComplete)
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ)
    (S : Finset (Vertex n)) (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    ⋃₀ cutCells Φ S = cutFace S := by
  ext x
  constructor
  · rintro ⟨F,⟨C,hC,hCS,rfl⟩,hx⟩
    exact rootCell_subset_cutFace Φ hrays hC hCS hx
  · intro hx
    rw [cutFace_eq_union_full_slices Φ hcomplete hrays S hne hproper] at hx
    obtain ⟨C,hC,hfull,hsource,hxC⟩ := hx
    have hCS : C ≤ cutCone S := by simpa only [hsource] using cone_le_cutCone Φ hrays hC
    refine ⟨rootCell C,⟨C,hC,hCS,rfl⟩,?_⟩
    exact (sliceCell_eq_convexHull_roots Φ hrays S hC hCS).subset hxC

/-- Restricting the subdivision from either facet to their common face yields
exactly the same family of cells. This is the paper's common-face compatibility
condition as equality of actual sets of actual polytopes. -/
theorem cutCells_commonFace (Φ : Fan (FanBridge.standardEmbedding n))
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ)
    (S T : Finset (Vertex n)) :
    (fun F => F ∩ cutFace T) '' cutCells Φ S =
      (fun F => F ∩ cutFace S) '' cutCells Φ T := by
  have hrestrict (S T : Finset (Vertex n)) :
      (fun F => F ∩ cutFace T) '' cutCells Φ S =
        {F | ∃ C ∈ Φ.cones, C ≤ cutCone S ∧ C ≤ cutCone T ∧ F = rootCell C} := by
    ext F
    constructor
    · rintro ⟨G,⟨C,hC,hCS,rfl⟩,rfl⟩
      obtain ⟨D,hD,hDC,hDS,hDT,he⟩ := rootCell_inter_cutFace Φ hrays hC S T hCS
      exact ⟨D,hD,hDS,hDT,he⟩
    · rintro ⟨C,hC,hCS,hCT,rfl⟩
      refine ⟨rootCell C,⟨C,hC,hCS,rfl⟩,?_⟩
      exact Set.inter_eq_left.2 (rootCell_subset_cutFace Φ hrays hC hCT)
  rw [hrestrict S T,hrestrict T S]
  ext F
  constructor <;> rintro ⟨C,hC,hS,hT,he⟩ <;> exact ⟨C,hC,hT,hS,he⟩

/-- Every actual geometric face of an intrinsic fan cell is itself the cell of
an actual fan face cone. This includes the empty face and the entire cell. -/
theorem rootCell_face (Φ : Fan (FanBridge.standardEmbedding n))
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ)
    {C : PointedCone ℝ (Ambient n)} (hC : C ∈ Φ.cones)
    {F : Set (Ambient n)} (hF : Convex ℝ F) (hFC : IsExtreme ℝ (rootCell C) F) :
    ∃ D ∈ Φ.cones, D.IsFaceOf C ∧ F = rootCell D := by
  have hCS := cone_le_cutCone Φ hrays hC
  have hlevel : ∀ x ∈ rootCell C, cutFunctional (sources C) x = 1 :=
    fun x hx => (rootCell_subset_cutFace Φ hrays hC hCS hx).2
  have hDC := NormalizedConeFaces.hull_isFaceOf (rootCell C) F
    (convex_convexHull ℝ _) hF hFC (cutFunctional (sources C)) hlevel
  rw [hull_rootCell Φ hrays hC] at hDC
  let D := PointedCone.hull ℝ F
  have hD : D ∈ Φ.cones := Φ.mem_of_isFaceOf hC hDC
  have hDS : D ≤ cutCone (sources C) := hDC.le.trans hCS
  refine ⟨D,hD,hDC,?_⟩
  have hslice := NormalizedConeFaces.slice_hull F hF (cutFunctional (sources C))
    (fun x hx => hlevel x (hFC.1 hx))
  change sliceCell (sources C) D = F at hslice
  exact hslice.symm.trans (sliceCell_eq_convexHull_roots Φ hrays (sources C) hD hDS)

/-- The finite cell family is closed under all genuine geometric faces, the
remaining face-closure axiom of a polyhedral subdivision. -/
theorem cutCells_closed_faces (Φ : Fan (FanBridge.standardEmbedding n))
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ)
    (S : Finset (Vertex n)) {F G : Set (Ambient n)}
    (hF : F ∈ cutCells Φ S) (hG : Convex ℝ G) (hGF : IsExtreme ℝ F G) :
    G ∈ cutCells Φ S := by
  obtain ⟨C,hC,hCS,rfl⟩ := hF
  obtain ⟨D,hD,hDC,he⟩ := rootCell_face Φ hrays hC hG hGF
  exact ⟨D,hD,hDC.le.trans hCS,he⟩

/-- The complete standard subdivision object attached to an arbitrary complete
fan with the exact root rays. All fields are proved from the fan axioms. -/
def cutSubdivision (Φ : Fan (FanBridge.standardEmbedding n)) (hcomplete : Φ.IsComplete)
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ)
    (S : Finset (Vertex n)) (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    VertexSubdivision (cutFace S) where
  cells := cutCells Φ S
  finite_cells := cutCells_finite Φ S
  vertices F hF := by
    obtain ⟨C,hC,hCS,rfl⟩ := hF
    obtain ⟨s,hs,hcell,hverts⟩ := sliceCell_finite_vertex_polytope Φ hrays S hC hCS
    refine ⟨s,?_,hs⟩
    exact (sliceCell_eq_convexHull_roots Φ hrays S hC hCS).symm.trans hcell
  cover := cutCells_cover Φ hcomplete hrays S hne hproper
  face_closed F hF G hG hGF := cutCells_closed_faces Φ hrays S hF hG hGF
  intersection_faces F hF G hG := by
    obtain ⟨C,hC,hCS,rfl⟩ := hF
    obtain ⟨D,hD,hDS,rfl⟩ := hG
    exact rootCell_intersection_faces Φ hrays hC hD

/-- The finite index type of the paper's nonempty proper cuts. -/
abbrev ProperCut (n : ℕ) :=
  {S : Finset (Vertex n) // S.Nonempty ∧ S ≠ Finset.univ}

/-- Independent vertex subdivisions of every cut facet, agreeing as actual
cell families on each common face. No fan or coning conclusion is assumed. -/
structure CompatibleCutSubdivisions (n : ℕ) where
  subdivision : (S : ProperCut n) → VertexSubdivision (cutFace S.val)
  compatibility : ∀ S T : ProperCut n,
    (fun F => F ∩ cutFace T.val) '' (subdivision S).cells =
      (fun F => F ∩ cutFace S.val) '' (subdivision T).cells

/-- The forward geometric classification: every complete fan on the type-A
roots supplies a compatible family of ordinary vertex subdivisions. -/
def fanCutSubdivisions (Φ : Fan (FanBridge.standardEmbedding n)) (hcomplete : Φ.IsComplete)
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ) :
    CompatibleCutSubdivisions n where
  subdivision S := cutSubdivision Φ hcomplete hrays S.val S.property.1 S.property.2
  compatibility S T := cutCells_commonFace Φ hrays S.val T.val

end Unimodular.TypeAFanGeometry

end

end NativePort_Unimodular_TypeASubdivisions

/- Exact recovered source fragment: Unimodular.TypeAConing. -/
section NativePort_Unimodular_TypeAConing



noncomputable section

namespace Unimodular.TypeAFanGeometry

open scoped BigOperators
open TauCeti.Toric

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

@[simp] theorem augmented_sum (x : Ambient n) :
    ∑ p : Vertex n, augmented n x p = 0 := by
  simp [Fintype.sum_option]

theorem cutFunctional_eq_source_sum (S : Finset (Vertex n)) (x : Ambient n) :
    cutFunctional S x = ∑ p : Source S, augmented n x p.val := by
  change (∑ p ∈ S, (LinearMap.proj p).comp (augmented n)) x = _
  simp only [LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.proj_apply]
  exact Finset.sum_subtype S (fun _ => Iff.rfl) _

/-- The cut facet is exactly the normalized section of its coordinate orthant.
This uses the previously proved affine product of actual standard simplices. -/
theorem mem_cutFace_of_signs (S : Finset (Vertex n)) {x : Ambient n}
    (hpos : ∀ p ∈ S, 0 ≤ augmented n x p)
    (hneg : ∀ q ∉ S, augmented n x q ≤ 0)
    (hlevel : cutFunctional S x = 1) : x ∈ cutFace S := by
  have hs : (∑ p : Source S, augmented n x p.val) = 1 := by
    rw [← cutFunctional_eq_source_sum,hlevel]
  have ht : (∑ q : Target S, -augmented n x q.val) = 1 := by
    have hh : (∑ p : Source S, augmented n x p.val) +
        (∑ q : Target S, augmented n x q.val) = ∑ p : Vertex n, augmented n x p := by
      calc
        _ = (∑ p ∈ S, augmented n x p) + (∑ q ∈ Sᶜ, augmented n x q) := by
          congr 1
          · exact (Finset.sum_subtype S (fun _ => Iff.rfl) _).symm
          · exact (Finset.sum_subtype Sᶜ (fun q => by simp) _).symm
        _ = _ := Finset.sum_add_sum_compl S _
    rw [augmented_sum,hs] at hh
    rw [Finset.sum_neg_distrib]
    linarith
  have hw : cutCoordinates S x ∈ stdSimplex ℝ (Source S) ×ˢ stdSimplex ℝ (Target S) :=
    ⟨⟨fun p => hpos p.val p.property,hs⟩,
      ⟨fun q => neg_nonneg.2 (hneg q.val q.property),ht⟩⟩
  obtain ⟨y,hy,he⟩ := (cutCoordinates_image_face S).symm ▸ hw
  exact (cutCoordinates_injective S he) ▸ hy

theorem exists_positive_augmented {x : Ambient n} (hx : x ≠ 0) :
    ∃ p : Vertex n, 0 < augmented n x p := by
  by_contra h
  push_neg at h
  have hz : ∀ p : Vertex n, augmented n x p = 0 := by
    exact fun p => (Finset.sum_eq_zero_iff_of_nonpos (fun q _ => h q)).1
      (augmented_sum x) p (Finset.mem_univ p)
  apply hx
  ext i
  exact hz (some i)

/-- Every nonzero vector is a strictly positive multiple of a point of one of
the actual cut facets. The cut is the set of positive augmented coordinates. -/
theorem exists_positive_cut_normalization {x : Ambient n} (hx : x ≠ 0) :
    ∃ S : ProperCut n, ∃ t : ℝ, 0 < t ∧ ∃ y ∈ cutFace S.val, x = t • y := by
  classical
  let S : Finset (Vertex n) := Finset.univ.filter (fun p => 0 < augmented n x p)
  have hmem (p : Vertex n) : p ∈ S ↔ 0 < augmented n x p := by simp [S]
  obtain ⟨p,hp⟩ := exists_positive_augmented hx
  have hne : S.Nonempty := ⟨p,(hmem p).2 hp⟩
  have hproper : S ≠ Finset.univ := by
    intro he
    have hsum : 0 < ∑ q : Vertex n, augmented n x q := by
      apply Finset.sum_pos
      · intro q hq
        exact (hmem q).1 (he.symm ▸ hq)
      · exact Finset.univ_nonempty
    rw [augmented_sum] at hsum
    exact lt_irrefl 0 hsum
  let t := cutFunctional S x
  have ht : 0 < t := by
    change 0 < (∑ p ∈ S, (LinearMap.proj p).comp (augmented n)) x
    simp only [LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.proj_apply]
    exact Finset.sum_pos (fun q hq => (hmem q).1 hq) hne
  let y : Ambient n := t⁻¹ • x
  have hy : y ∈ cutFace S := by
    apply mem_cutFace_of_signs S
    · intro q hq
      change 0 ≤ augmented n (t⁻¹ • x) q
      rw [map_smul]
      exact mul_nonneg (inv_nonneg.2 ht.le) ((hmem q).1 hq).le
    · intro q hq
      change augmented n (t⁻¹ • x) q ≤ 0
      rw [map_smul]
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 ht.le)
        (le_of_not_gt (fun h => hq ((hmem q).2 h)))
    · change cutFunctional S (t⁻¹ • x) = 1
      simp only [map_smul,smul_eq_mul]
      exact inv_mul_cancel₀ ht.ne'
  exact ⟨⟨S,hne,hproper⟩,t,ht,y,hy,by
    dsimp only [y]
    rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul]⟩

namespace CompatibleCutSubdivisions

variable (D : CompatibleCutSubdivisions n)

/-- Cones over the actual cells of the supplied facet subdivisions. -/
def coneFamily : Set (PointedCone ℝ (Ambient n)) :=
  {C | ∃ S : ProperCut n, ∃ F ∈ (D.subdivision S).cells, C = PointedCone.hull ℝ F}

theorem coneFamily_finite : D.coneFamily.Finite := by
  have hf : (⋃ S : ProperCut n, (D.subdivision S).cells).Finite :=
    Set.finite_iUnion (fun S => (D.subdivision S).finite_cells)
  apply (hf.image (PointedCone.hull ℝ)).subset
  rintro C ⟨S,F,hF,rfl⟩
  exact ⟨F,Set.mem_iUnion.2 ⟨S,hF⟩,rfl⟩

theorem cell_level {S : ProperCut n} {F : Set (Ambient n)}
    (hF : F ∈ (D.subdivision S).cells) {x : Ambient n} (hx : x ∈ F) :
    cutFunctional S.val x = 1 := ((D.subdivision S).cell_subset hF hx).2

theorem cell_polytope {S : ProperCut n} {F : Set (Ambient n)}
    (hF : F ∈ (D.subdivision S).cells) : F ⊆ rootPolytope n :=
  fun _ hx => ((D.subdivision S).cell_subset hF hx).1

/-- An intersection with another supporting facet is an actual face of a cell. -/
theorem inter_cutFace_extreme {S : ProperCut n} {F : Set (Ambient n)}
    (hF : F ∈ (D.subdivision S).cells) (T : ProperCut n) :
    IsExtreme ℝ F (F ∩ cutFace T.val) := by
  refine ⟨Set.inter_subset_left,?_⟩
  intro x hx y hy z hz hseg
  exact ⟨hx,(cutFace_extreme T.val).left_mem_of_mem_openSegment
    (D.cell_polytope hF hx) (D.cell_polytope hF hy) hz.2 hseg⟩

/-- Common-face compatibility implies that restricting any cell from one
facet to another is a cell of the latter subdivision as well. -/
theorem inter_cutFace_mem {S : ProperCut n} {F : Set (Ambient n)}
    (hF : F ∈ (D.subdivision S).cells) (T : ProperCut n) :
    F ∩ cutFace T.val ∈ (D.subdivision T).cells := by
  have hh : F ∩ cutFace T.val ∈
      (fun G => G ∩ cutFace S.val) '' (D.subdivision T).cells := by
    rw [← D.compatibility S T]
    exact ⟨F,hF,rfl⟩
  obtain ⟨G,hG,hGF⟩ := hh
  rw [← hGF]
  exact (D.subdivision T).face_closed G hG _
    (((D.subdivision T).cell_convex hG).inter (cutFace_convex S.val))
    (D.inter_cutFace_extreme hG S)

/-- Cells from different cut facets also meet face-to-face. The hypothesis
is ordinary equality of the subdivisions on the common geometric face. -/
theorem intersection_extreme {S T : ProperCut n} {F G : Set (Ambient n)}
    (hF : F ∈ (D.subdivision S).cells) (hG : G ∈ (D.subdivision T).cells) :
    IsExtreme ℝ F (F ∩ G) ∧ IsExtreme ℝ G (F ∩ G) := by
  have hH := D.inter_cutFace_mem hF T
  have hi := (D.subdivision T).intersection_faces _ hH G hG
  have he : (F ∩ cutFace T.val) ∩ G = F ∩ G := by
    ext x
    constructor
    · exact fun h => ⟨h.1.1,h.2⟩
    · exact fun h => ⟨⟨h.1,(D.subdivision T).cell_subset hG h.2⟩,h.2⟩
  rw [he] at hi
  exact ⟨(D.inter_cutFace_extreme hF T).trans hi.1,hi.2⟩

/-- Finite vertex generation and the actual vertex theorem provide a literal
finite set of lattice generators for each coned cell. -/
theorem hull_cell_rational {S : ProperCut n} {F : Set (Ambient n)}
    (hF : F ∈ (D.subdivision S).cells) :
    IsLatticeRational (FanBridge.standardEmbedding n) (PointedCone.hull ℝ F) := by
  classical
  obtain ⟨s,hs,hsv⟩ := (D.subdivision S).vertices F hF
  let es : Finset (Edge n) := Finset.univ.filter
    (fun e => realRoot e.val.1 e.val.2 ∈ s)
  let ls : Finset (Lattice n) := es.image (rootFamily n)
  have hgen : FanBridge.standardEmbedding n '' (ls : Set (Lattice n)) =
      (s : Set (Ambient n)) := by
    ext x
    constructor
    · rintro ⟨v,hv,rfl⟩
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.1 hv
      exact (Finset.mem_filter.1 he).2
    · intro hx
      have he := hsv hx
      rw [cutFace_extremePoints] at he
      obtain ⟨v,⟨p,hp,q,hq,rfl⟩,rfl⟩ := he
      have hpq : p ≠ q := fun h => hq (h ▸ hp)
      refine ⟨latticeRoot p q,?_,rfl⟩
      exact Finset.mem_image.2 ⟨⟨(p,q),hpq⟩,Finset.mem_filter.2 ⟨Finset.mem_univ _,hx⟩,rfl⟩
  refine isLatticeRational_iff.2 ⟨ls,?_⟩
  rw [hgen,hs]
  apply le_antisymm
  · exact Submodule.span_le.2 (convexHull_min PointedCone.subset_hull
      (PointedCone.hull ℝ (s : Set (Ambient n))).convex)
  · exact Submodule.span_mono (subset_convexHull ℝ _)

theorem hull_cell_toric {S : ProperCut n} {F : Set (Ambient n)}
    (hF : F ∈ (D.subdivision S).cells) :
    IsToricCone (FanBridge.standardEmbedding n) (PointedCone.hull ℝ F) :=
  ⟨D.hull_cell_rational hF,
    NormalizedConeFaces.hull_salient F (cutFunctional S.val) (fun _ hx => D.cell_level hF hx)⟩

/-- Every genuine face of a coned cell is the cone of a genuine geometric
face in the supplied subdivision. No additional cone closure is required. -/
theorem coneFamily_face_closed {C K : PointedCone ℝ (Ambient n)}
    (hC : C ∈ D.coneFamily) (hK : K.IsFaceOf C) : K ∈ D.coneFamily := by
  obtain ⟨S,F,hF,rfl⟩ := hC
  obtain ⟨hc,he⟩ := NormalizedConeFaces.section_is_face F
    ((D.subdivision S).cell_convex hF) hK
  refine ⟨S,F ∩ (K : Set (Ambient n)),
    (D.subdivision S).face_closed F hF _ hc he,?_⟩
  exact (NormalizedConeFaces.hull_section F ((D.subdivision S).cell_convex hF)
    (cutFunctional S.val) (fun _ hx => D.cell_level hF hx) hK).symm

/-- The cross-facet radial-scale argument proves the actual fan intersection
axiom, even when the two cells lie in different supporting hyperplanes. -/
theorem coneFamily_inf_isFaceOf_left {C K : PointedCone ℝ (Ambient n)}
    (hC : C ∈ D.coneFamily) (hK : K ∈ D.coneFamily) : (C ⊓ K).IsFaceOf C := by
  obtain ⟨S,F,hF,rfl⟩ := hC
  obtain ⟨T,G,hG,rfl⟩ := hK
  have hFc := (D.subdivision S).cell_convex hF
  have hGc := (D.subdivision T).cell_convex hG
  have he := NormalizedConeFaces.hull_inter F G hFc hGc
    (cutFunctional S.val) (cutFunctional T.val)
    (fun _ hx => D.cell_level hF hx) (fun _ hx => D.cell_level hG hx)
    (fun _ hx => cutFunctional_le_one_on_polytope S.val (D.cell_polytope hG hx))
    (fun _ hx => cutFunctional_le_one_on_polytope T.val (D.cell_polytope hF hx))
  rw [← he]
  exact NormalizedConeFaces.hull_isFaceOf F (F ∩ G) hFc (hFc.inter hGc)
    (D.intersection_extreme hF hG).1 (cutFunctional S.val) (fun _ hx => D.cell_level hF hx)

/-- Coning the ordinary compatible vertex subdivisions constructs a genuine
finite rational salient fan with every face and every intersection verified. -/
def toFan : Fan (FanBridge.standardEmbedding n) where
  lattice := FanBridge.standardEmbedding_isIntegralLattice n
  cones := D.coneFamily
  finite_cones := D.coneFamily_finite
  isToricCone := by
    intro C hC
    obtain ⟨S,F,hF,rfl⟩ := hC
    exact D.hull_cell_toric hF
  mem_of_isFaceOf := by
    intro C K hC hK
    exact D.coneFamily_face_closed hC hK
  inf_isFaceOf_left := by
    intro C K hC hK
    exact D.coneFamily_inf_isFaceOf_left hC hK

/-- Coning all cells covers the whole ambient vector space in every positive
rank. Completeness is proved by normalization, including the zero vector. -/
theorem toFan_complete (hn : 0 < n) : D.toFan.IsComplete := by
  apply (D.toFan.isComplete_iff).2
  intro x
  by_cases hx : x = 0
  · let S : ProperCut n := ⟨{none},by simp,by
      intro h
      have hh : (some ⟨0,hn⟩ : Vertex n) ∈ ({none} : Finset (Vertex n)) := by
        rw [h]
        exact Finset.mem_univ _
      simpa using hh⟩
    have hP := cutFace_nonempty S.val S.property.1 S.property.2
    have hF := (D.subdivision S).empty_mem hP
    exact ⟨PointedCone.hull ℝ ∅,⟨S,∅,hF,rfl⟩,by simpa only [hx] using
      (PointedCone.hull ℝ (∅ : Set (Ambient n))).zero_mem⟩
  · obtain ⟨S,t,ht,y,hy,rfl⟩ := exists_positive_cut_normalization hx
    rw [← (D.subdivision S).cover] at hy
    obtain ⟨F,hF,hy⟩ := hy
    exact ⟨PointedCone.hull ℝ F,⟨S,F,hF,rfl⟩,
      (PointedCone.hull ℝ F).smul_mem ht.le (PointedCone.subset_hull hy)⟩

/-- The rays of the constructed fan are exactly all nonzero type-A roots.
Every root is a genuine vertex and hence a singleton cell; no new ray can
arise because a one-dimensional cell cone is generated by one of its vertices. -/
theorem toFan_hasRays :
    AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) D.toFan := by
  classical
  intro R
  constructor
  · rintro ⟨hR,hdim⟩
    obtain ⟨S,F,hF,rfl⟩ := hR
    obtain ⟨s,hs,hsv⟩ := (D.subdivision S).vertices F hF
    let ρ : ToricRay (PointedCone.hull ℝ F) :=
      ⟨⟨PointedCone.hull ℝ F,PointedCone.IsFaceOf.refl _⟩,hdim⟩
    have hsne : s.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.2
      intro he
      apply ρ.toPointedCone_ne_bot
      change PointedCone.hull ℝ F = ⊥
      simp [hs,he]
    obtain ⟨v,hv⟩ := hsne
    have hroot := hsv hv
    rw [cutFace_extremePoints] at hroot
    obtain ⟨w,⟨p,hp,q,hq,rfl⟩,he⟩ := hroot
    have hpq : p ≠ q := fun h => hq (h ▸ hp)
    have hvF : v ∈ F := by
      rw [hs]
      exact subset_convexHull ℝ _ hv
    refine ⟨⟨(p,q),hpq⟩,?_⟩
    change PointedCone.hull ℝ F = PointedCone.hull ℝ {realRoot p q}
    have hvR : v ∈ ρ := PointedCone.subset_hull hvF
    have hvr : realRoot p q = v := he
    rw [← hvr] at hvR
    exact ρ.eq_hull_singleton (D.hull_cell_toric hF).salient hvR (realRoot_ne_zero hpq)
  · rintro ⟨e,rfl⟩
    let S : ProperCut n := ⟨{e.val.1},by simp,by
      intro h
      have hh : e.val.2 ∈ ({e.val.1} : Finset (Vertex n)) := by
        rw [h]
        exact Finset.mem_univ _
      exact e.property (Finset.mem_singleton.1 hh).symm⟩
    have hr : realRoot e.val.1 e.val.2 ∈ cutFace S.val := by
      apply (root_mem_cutFace_iff S.val e.property).2
      simp [S,Ne.symm e.property]
    rw [← (D.subdivision S).cover] at hr
    obtain ⟨F,hF,hrF⟩ := hr
    have hext : realRoot e.val.1 e.val.2 ∈ F.extremePoints ℝ :=
      inter_extremePoints_subset_extremePoints_of_subset (D.cell_polytope hF)
        ⟨hrF,root_is_extremePoint e.property⟩
    have hsingleton := (D.subdivision S).face_closed F hF
      {realRoot e.val.1 e.val.2} (convex_singleton _) (isExtreme_singleton.2 hext)
    exact ⟨⟨S,{realRoot e.val.1 e.val.2},hsingleton,rfl⟩,
      PointedCone.finrank_span_coe_hull_singleton (realRoot_ne_zero e.property)⟩

/-- The cone of a cell has exactly that cell as its intrinsic root-polytope
section. This is a genuine inverse statement, using all actual root rays. -/
theorem rootCell_hull {S : ProperCut n} {F : Set (Ambient n)}
    (hF : F ∈ (D.subdivision S).cells) : rootCell (PointedCone.hull ℝ F) = F := by
  have hC : PointedCone.hull ℝ F ∈ D.toFan.cones := ⟨S,F,hF,rfl⟩
  have hCS : PointedCone.hull ℝ F ≤ cutCone S.val := by
    rw [cutCone_eq_hull_cutFace]
    exact Submodule.span_mono ((D.subdivision S).cell_subset hF)
  have hs := sliceCell_eq_convexHull_roots D.toFan D.toFan_hasRays S.val hC hCS
  change sliceCell S.val (PointedCone.hull ℝ F) = rootCell (PointedCone.hull ℝ F) at hs
  have hn := NormalizedConeFaces.slice_hull F ((D.subdivision S).cell_convex hF)
    (cutFunctional S.val) (fun _ hx => D.cell_level hF hx)
  exact hs.symm.trans hn

/-- Recovering the cut subdivision from the coned fan returns exactly the
original cell family, including boundary cells shared with other facets. -/
theorem cutCells_toFan (S : ProperCut n) :
    cutCells D.toFan S.val = (D.subdivision S).cells := by
  apply Set.Subset.antisymm
  · rintro F ⟨C,⟨T,G,hG,rfl⟩,hCS,rfl⟩
    rw [D.rootCell_hull hG]
    have hGP : G ⊆ cutFace S.val := by
      rw [← D.rootCell_hull hG]
      exact rootCell_subset_cutFace D.toFan D.toFan_hasRays ⟨T,G,hG,rfl⟩ hCS
    have hi := D.inter_cutFace_mem hG S
    simpa only [Set.inter_eq_left.2 hGP] using hi
  · intro F hF
    refine ⟨PointedCone.hull ℝ F,⟨S,F,hF,rfl⟩,?_,(D.rootCell_hull hF).symm⟩
    rw [cutCone_eq_hull_cutFace]
    exact Submodule.span_mono ((D.subdivision S).cell_subset hF)

end CompatibleCutSubdivisions

/-- A finite complete root fan is recovered exactly by coning its intrinsic
cut subdivisions, including all lower-dimensional face cones. -/
theorem toFan_fanCutSubdivisions (hn : 0 < n)
    (Φ : Fan (FanBridge.standardEmbedding n)) (hcomplete : Φ.IsComplete)
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ) :
    (fanCutSubdivisions Φ hcomplete hrays).toFan = Φ := by
  apply Fan.ext
  ext C
  constructor
  · rintro ⟨S,F,⟨K,hK,hKS,rfl⟩,rfl⟩
    simpa only [hull_rootCell Φ hrays hK] using hK
  · intro hC
    obtain ⟨K,hK,hfull,hCK⟩ := FanMaximalCones.exists_full_supercone Φ hcomplete hC
    have hproper := full_cone_cut_nontrivial hn Φ hrays hK hfull
    let S : ProperCut n := ⟨sources K,hproper⟩
    refine ⟨S,rootCell C,⟨C,hC,hCK.le.trans (cone_le_cutCone Φ hrays hK),rfl⟩,?_⟩
    exact (hull_rootCell Φ hrays hC).symm

/-- Equality of actual cell families determines the whole subdivision object;
all remaining fields merely certify the stated geometric properties. -/
theorem vertexSubdivision_ext {V : Type*} [AddCommGroup V] [Module ℝ V]
    {P : Set V} {D E : VertexSubdivision P} (h : D.cells = E.cells) : D = E := by
  cases D
  cases E
  cases h
  rfl

theorem compatibleCutSubdivisions_ext {D E : CompatibleCutSubdivisions n}
    (h : ∀ S, (D.subdivision S).cells = (E.subdivision S).cells) : D = E := by
  have he : D.subdivision = E.subdivision := funext (fun S => vertexSubdivision_ext (h S))
  cases D
  cases E
  cases he
  rfl

/-- Reconstructing the canonical compatible subdivisions from a coned family
returns the supplied subdivisions as actual finite cell sets. -/
theorem fanCutSubdivisions_toFan (D : CompatibleCutSubdivisions n) (hn : 0 < n) :
    fanCutSubdivisions D.toFan (D.toFan_complete hn) D.toFan_hasRays = D := by
  apply compatibleCutSubdivisions_ext
  intro S
  exact D.cutCells_toFan S

/-- The geometric classification in Theorem 7.1 is a literal bijection between
complete fans on the type-A roots and compatible vertex subdivisions of all
actual cut facets. Its maps are slicing and coning, and both inverse laws are
proved using genuine cone and polytope faces. -/
def fanSubdivisionEquiv (hn : 0 < n) :
    {Φ : Fan (FanBridge.standardEmbedding n) // Φ.IsComplete ∧
      AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ} ≃
        CompatibleCutSubdivisions n where
  toFun Φ := fanCutSubdivisions Φ.val Φ.property.1 Φ.property.2
  invFun D := ⟨D.toFan,D.toFan_complete hn,D.toFan_hasRays⟩
  left_inv Φ := Subtype.ext (toFan_fanCutSubdivisions hn Φ.val Φ.property.1 Φ.property.2)
  right_inv D := fanCutSubdivisions_toFan D hn

end Unimodular.TypeAFanGeometry

end

end NativePort_Unimodular_TypeAConing

/- Exact recovered source fragment: Unimodular.TypeATriangulations. -/
section NativePort_Unimodular_TypeATriangulations



noncomputable section

open scoped BigOperators
open TauCeti.Toric

namespace Unimodular

namespace VertexSubdivision

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {P : Set V}

/-- Each cell is the convex hull of exactly its genuine extreme points. This
follows from vertex generation and is not an extra subdivision assumption. -/
theorem cell_eq_convexHull_extremePoints (D : VertexSubdivision P)
    {F : Set V} (hF : F ∈ D.cells) : F = convexHull ℝ (F.extremePoints ℝ) := by
  obtain ⟨s,hs,hsv⟩ := D.vertices F hF
  have he : F.extremePoints ℝ = (s : Set V) := by
    apply Set.Subset.antisymm
    · rw [hs]
      exact extremePoints_convexHull_subset
    · intro x hx
      apply inter_extremePoints_subset_extremePoints_of_subset (D.cell_subset hF)
      exact ⟨hs.symm ▸ subset_convexHull ℝ (s : Set V) hx,hsv hx⟩
  rw [he]
  exact hs

/-- A subdivision is a triangulation when the actual vertices of each actual
cell are affinely independent. Finite vertex generation has already been proved. -/
def IsTriangulation (D : VertexSubdivision P) : Prop :=
  ∀ F ∈ D.cells, AffineIndependent ℝ (Subtype.val : F.extremePoints ℝ → V)

end VertexSubdivision

namespace NormalizedConeFaces

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- On a level-one affine hyperplane, affine and linear independence coincide.
Applying the supporting functional supplies the zero-sum coefficient condition. -/
theorem affineIndependent_iff_linearIndependent {κ : Type*} (v : κ → V)
    (f : V →ₗ[ℝ] ℝ) (hf : ∀ j, f (v j) = 1) :
    AffineIndependent ℝ v ↔ LinearIndependent ℝ v := by
  constructor
  · intro ha
    apply linearIndependent_iff'.2
    intro s w hw i hi
    have hsum : ∑ j ∈ s, w j = 0 := by
      have h := congrArg f hw
      simpa only [map_sum,map_smul,hf,smul_eq_mul,mul_one,map_zero] using h
    apply ha s w hsum ?_ i hi
    rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hsum 0,
      Finset.weightedVSubOfPoint_apply]
    simpa only [vsub_eq_sub,sub_zero] using hw
  · exact LinearIndependent.affineIndependent ℝ

/-- The actual vertices of a normalized section of a regular cone are linearly
independent. Every vertex yields a genuine ray; regularity makes their primitive
generators independent, and normalization merely rescales them nontrivially. -/
theorem regular_vertices_linearIndependent {N : Type*} [AddCommGroup N]
    (i : N →+ V) (hi : IsIntegralLattice i) (F : Set V) (hF : Convex ℝ F)
    (f : V →ₗ[ℝ] ℝ) (hf : ∀ x ∈ F, f x = 1)
    (hreg : IsRegularCone i (PointedCone.hull ℝ F)) :
    LinearIndependent ℝ (Subtype.val : F.extremePoints ℝ → V) := by
  classical
  have hnz (v : F.extremePoints ℝ) : v.val ≠ 0 := by
    intro hv
    have h := hf v.val v.property.1
    rw [hv,map_zero] at h
    exact zero_ne_one h
  let ray : F.extremePoints ℝ → ToricRay (PointedCone.hull ℝ F) := fun v =>
    ⟨⟨PointedCone.hull ℝ {v.val},hull_isFaceOf F {v.val} hF (convex_singleton _)
      (isExtreme_singleton.2 v.property) f hf⟩,
      PointedCone.finrank_span_coe_hull_singleton (hnz v)⟩
  have hray : Function.Injective ray := by
    intro v w h
    have hc := congrArg ToricRay.toPointedCone h
    change PointedCone.hull ℝ {v.val} = PointedCone.hull ℝ {w.val} at hc
    have hv : v.val ∈ PointedCone.hull ℝ {w.val} := by
      rw [← hc]
      exact PointedCone.subset_hull (by simp)
    obtain ⟨a,ha,he⟩ := PointedCone.mem_hull_singleton.1 hv
    have hh := congrArg f he
    rw [map_smul,hf w.val w.property.1,hf v.val v.property.1] at hh
    have ha1 : a = 1 := by simpa only [smul_eq_mul,mul_one] using hh
    apply Subtype.ext
    simpa only [ha1,one_smul] using he.symm
  let g : F.extremePoints ℝ → V :=
    fun v => i (primitiveGenerator hi hreg.toIsToricCone (ray v))
  have hg : LinearIndependent ℝ g :=
    (hreg.linearIndependent_primitiveGenerator hi).comp ray hray
  have hex (v : F.extremePoints ℝ) : ∃ a : ℝ, a ≠ 0 ∧ a • g v = v.val := by
    have hv : v.val ∈ ray v := PointedCone.subset_hull (by simp)
    have hcone := (ray v).eq_hull_singleton
      (hreg.salient.anti (ray v).val.isFaceOf.le)
      (primitiveGenerator_mem hi hreg.toIsToricCone (ray v))
      (by simpa using hi.injective.ne (primitiveGenerator_ne_zero hi hreg.toIsToricCone (ray v)))
    change v.val ∈ (ray v).toPointedCone at hv
    rw [hcone] at hv
    obtain ⟨a,ha,he⟩ := PointedCone.mem_hull_singleton.1 hv
    refine ⟨a,?_,he⟩
    intro ha0
    exact hnz v (by simpa only [ha0,zero_smul] using he.symm)
  choose a ha he using hex
  apply linearIndependent_iff'.2
  intro s w hw j hj
  have hsum : ∑ v ∈ s, (w v * a v) • g v = 0 := by
    simpa only [mul_smul,he] using hw
  have hh := linearIndependent_iff'.1 hg s (fun v => w v * a v) hsum j hj
  exact (mul_eq_zero.1 hh).resolve_right (ha j)

end NormalizedConeFaces

namespace TypeAFanGeometry

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

/-- The actual finite set of all nonzero type-A lattice roots. -/
def rootSet (n : ℕ) : Set (Lattice n) := Set.range (rootFamily n)

theorem rootSet_uniform : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
    (fun u : rootSet n => u.val) := by
  apply Graphic.uniform_of_incidence_representation
  intro u
  obtain ⟨e,he⟩ := u.property
  exact ⟨e.val.1,e.val.2,he.symm⟩

theorem rootSet_spans : Submodule.span ℝ (embed '' rootSet n) = ⊤ := by
  apply top_unique
  calc
    ⊤ = Submodule.span ℝ (Set.range (Pi.basisFun ℝ (Fin n))) :=
      (Pi.basisFun ℝ (Fin n)).span_eq.symm
    _ ≤ Submodule.span ℝ (embed '' rootSet n) := by
      apply Submodule.span_mono
      rintro x ⟨j,rfl⟩
      refine ⟨latticeRoot (some j) none,⟨⟨(some j,none),by simp⟩,rfl⟩,?_⟩
      ext k
      by_cases h : j = k <;> simp [latticeRoot,Graphic.vertex,embed,Pi.basisFun_apply,
        Pi.single_apply,h]

namespace CompatibleCutSubdivisions

variable (D : CompatibleCutSubdivisions n)

/-- A simplex cell in a root-facet subdivision cones to an actually regular
cone. Graphic uniform unimodularity extends every independent root set to an
integral basis, so this proves smoothness in the original ambient lattice. -/
theorem hull_cell_regular_of_affineIndependent {S : ProperCut n} {F : Set (Ambient n)}
    (hF : F ∈ (D.subdivision S).cells)
    (ha : AffineIndependent ℝ (Subtype.val : F.extremePoints ℝ → Ambient n)) :
    IsRegularCone (FanBridge.standardEmbedding n) (PointedCone.hull ℝ F) := by
  classical
  have hli : LinearIndependent ℝ (Subtype.val : F.extremePoints ℝ → Ambient n) :=
    (NormalizedConeFaces.affineIndependent_iff_linearIndependent Subtype.val
      (cutFunctional S.val) (fun v => D.cell_level hF v.property.1)).1 ha
  have hex (v : F.extremePoints ℝ) : ∃ u : rootSet n, embed u.val = v.val := by
    have he := ((D.subdivision S).cell_extremePoints hF).2 v.property
    rw [cutFace_extremePoints] at he
    obtain ⟨u,⟨p,hp,q,hq,rfl⟩,he⟩ := he
    have hpq : p ≠ q := fun h => hq (h ▸ hp)
    exact ⟨⟨latticeRoot p q,⟨⟨(p,q),hpq⟩,rfl⟩⟩,he⟩
  choose a hea using hex
  have haind : LinearIndependent ℝ (fun v => embed (a v).val) := by
    simpa only [hea] using hli
  obtain ⟨b,hb,hba⟩ := LatticeHull.exists_lattice_basis_extension (rootSet n)
    rootSet_uniform rootSet_spans a haind
  let B : Set (Fin n) := {j | embed (b j) ∈ F.extremePoints ℝ}
  have hgen : FanBridge.standardEmbedding n '' (b '' B) = F.extremePoints ℝ := by
    ext x
    constructor
    · rintro ⟨u,⟨j,hj,rfl⟩,rfl⟩
      exact hj
    · intro hx
      obtain ⟨j,hj⟩ := hba ⟨x,hx⟩
      refine ⟨b j,⟨j,?_,rfl⟩,?_⟩
      · change embed (b j) ∈ F.extremePoints ℝ
        rw [hj,hea]
        exact hx
      · change embed (b j) = x
        rw [hj,hea]
  have hc : PointedCone.hull ℝ F = PointedCone.hull ℝ (F.extremePoints ℝ) := by
    calc
      PointedCone.hull ℝ F = PointedCone.hull ℝ (convexHull ℝ (F.extremePoints ℝ)) :=
        congrArg (PointedCone.hull ℝ) ((D.subdivision S).cell_eq_convexHull_extremePoints hF)
      _ = PointedCone.hull ℝ (F.extremePoints ℝ) := le_antisymm
        (Submodule.span_le.2 (convexHull_min PointedCone.subset_hull
          (PointedCone.hull ℝ (F.extremePoints ℝ)).convex))
        (Submodule.span_mono (subset_convexHull ℝ _))
  rw [hc,← hgen]
  exact isRegularCone_hull_image_basis (FanBridge.standardEmbedding_isIntegralLattice n) b B

/-- Smoothness of the constructed fan is equivalent to all the supplied
subdivisions being actual triangulations, with affine-independent cell vertices. -/
theorem toFan_isRegular_iff :
    D.toFan.IsRegular ↔ ∀ S : ProperCut n, (D.subdivision S).IsTriangulation := by
  constructor
  · intro hreg S F hF
    exact (NormalizedConeFaces.regular_vertices_linearIndependent
      (FanBridge.standardEmbedding n) (FanBridge.standardEmbedding_isIntegralLattice n)
      F ((D.subdivision S).cell_convex hF) (cutFunctional S.val)
      (fun _ hx => D.cell_level hF hx)
      (Fan.isRegular_iff.mp hreg _ ⟨S,F,hF,rfl⟩)).affineIndependent
  · intro htri
    apply Fan.isRegular_iff.mpr
    intro C hC
    obtain ⟨S,F,hF,rfl⟩ := hC
    exact D.hull_cell_regular_of_affineIndependent hF (htri S F hF)

end CompatibleCutSubdivisions

/-- The smooth-fan clause of the type-A classification, stated for every
complete root fan and the genuine geometric subdivisions obtained by slicing. -/
theorem fan_isRegular_iff_cut_triangulations (hn : 0 < n)
    (Φ : Fan (FanBridge.standardEmbedding n)) (hcomplete : Φ.IsComplete)
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ) :
    Φ.IsRegular ↔ ∀ S : ProperCut n,
      ((fanCutSubdivisions Φ hcomplete hrays).subdivision S).IsTriangulation := by
  have h := (fanCutSubdivisions Φ hcomplete hrays).toFan_isRegular_iff
  simpa only [toFan_fanCutSubdivisions hn Φ hcomplete hrays] using h

end TypeAFanGeometry

end Unimodular

end

end NativePort_Unimodular_TypeATriangulations

#print axioms Unimodular.TypeAFanGeometry.fanSubdivisionEquiv
#print axioms Unimodular.TypeAFanGeometry.fan_isRegular_iff_cut_triangulations
#check "UNIMODULAR_A3_NATIVE_GEOMETRY_EOF_V2"
