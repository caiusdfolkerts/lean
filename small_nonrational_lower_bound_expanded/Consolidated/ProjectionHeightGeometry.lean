module
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic.Abel
public import Papers.SupportFormIndependence
public import Mathlib.Tactic.FieldSimp
public import Papers.ActualHomogeneousFaceRanks
public import Papers.ActualSmallFacetIndependence
public import Mathlib.Logic.Equiv.Option
public import Papers.PolytopeIncidenceConfiguration
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Papers.PolytopeSmallFacetBounds
public import Papers.PolytopeNonedgeAllocation
public import Mathlib.Data.Fin.Embedding
public import Papers.RationalOrthogonalityPeeling
public import Mathlib.Data.Finset.Max
public import Lean.Elab.Tactic.Omega
public import Papers.BipartiteOrthogonalityDensity
public import Papers.RationalityTenFacetExtension
public import Papers.RationalityTenPolygonRelationRanks
public import Papers.RationalKernelCharts
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Tactic.FunProp
public import Papers.ConstantRankVectorCharts
public import Papers.AffineRelationLift
public import Papers.ProjectedRelationTemplate

/-! Canonical source bundle; each original file retains its own scopes. -/

section BundlePart0
/- Source: Papers/PrescribedHeightChart.lean -/







@[expose] public section

noncomputable section

/-!
# An affine chart with a prescribed height functional

A nonzero linear functional admits a scalar direction w with value one.
Subtracting its value times w splits the ambient space as ker(l) times R.
This supplies the precise affine normalization for vertex projection: an
exposing affine form becomes the last coordinate, and the exposed vertex
becomes the origin.
-/

namespace Papers.RationalityTen

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- An explicit splitting of a nonzero linear functional. -/
def kernelScalarSplit (l : V →ₗ[ℝ] ℝ) (w : V) (hw : l w = 1) :
    V ≃ₗ[ℝ] l.ker × ℝ where
  toFun x :=
    (⟨x - l x • w, by
      change l (x - l x • w) = 0
      simp [hw]⟩, l x)
  invFun p := p.1.1 + p.2 • w
  left_inv x := by
    change x - l x • w + l x • w = x
    exact sub_add_cancel _ _
  right_inv p := by
    have hp : l p.1.1 = 0 := p.1.2
    apply Prod.ext
    · apply Subtype.ext
      change p.1.1 + p.2 • w - l (p.1.1 + p.2 • w) • w = p.1.1
      simp [hp, hw]
    · change l (p.1.1 + p.2 • w) = p.2
      simp [hp, hw]
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      change x + y - l (x + y) • w =
        (x - l x • w) + (y - l y • w)
      rw [map_add, add_smul]
      abel
    · exact map_add l x y
  map_smul' c x := by
    apply Prod.ext
    · apply Subtype.ext
      change c • x - l (c • x) • w = c • (x - l x • w)
      simp [smul_sub, smul_smul]
    · exact map_smul l c x

@[simp]
theorem kernelScalarSplit_snd (l : V →ₗ[ℝ] ℝ) (w : V) (hw : l w = 1) (x : V) :
    (kernelScalarSplit l w hw x).2 = l x := rfl

theorem exists_value_one (l : V →ₗ[ℝ] ℝ) (hl : l ≠ 0) :
    ∃ w, l w = 1 := by
  classical
  have hnot : ¬ ∀ x, l x = 0 := by
    intro h
    apply hl
    ext x
    exact h x
  obtain ⟨x, hx⟩ := not_forall.mp hnot
  refine ⟨(l x)⁻¹ • x, ?_⟩
  simp [hx]

theorem kernelScalarSplit_finrank [FiniteDimensional ℝ V]
    (l : V →ₗ[ℝ] ℝ) (w : V) (hw : l w = 1) :
    Module.finrank ℝ l.ker + 1 = Module.finrank ℝ V := by
  simpa using (kernelScalarSplit l w hw).finrank_eq.symm

/-- Prescribe a nonzero functional as the last coordinate of a linear
equivalence. The dimension hypothesis is exact and explicit. -/
theorem exists_prescribedHeight_linearEquiv
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (l : V →ₗ[ℝ] ℝ) (hl : l ≠ 0)
    (hdim : Module.finrank ℝ V = Module.finrank ℝ W + 1) :
    ∃ T : V ≃ₗ[ℝ] W × ℝ, ∀ x, (T x).2 = l x := by
  obtain ⟨w, hw⟩ := exists_value_one l hl
  have hker : Module.finrank ℝ l.ker = Module.finrank ℝ W :=
    Nat.add_right_cancel ((kernelScalarSplit_finrank l w hw).trans hdim)
  let e : l.ker ≃ₗ[ℝ] W := LinearEquiv.ofFinrankEq l.ker W hker
  refine ⟨(kernelScalarSplit l w hw).trans
    (e.prodCongr (LinearEquiv.refl ℝ ℝ)), ?_⟩
  intro x
  rfl

theorem affine_linear_ne_zero_of_zero_and_pos
    (f : V →ᵃ[ℝ] ℝ) (a b : V) (ha : f a = 0) (hb : 0 < f b) :
    f.linear ≠ 0 := by
  intro hzero
  have h := f.linear_apply_vsub b a
  have hfb : f b = 0 := by simpa [hzero, ha] using h.symm
  exact hb.ne' hfb

/-- A vertex exposed by f is sent to zero and f itself becomes height.
Positivity of the height at every other body point can therefore be read
directly from its original exposing inequality. -/
theorem exists_prescribedHeight_affineEquiv
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (f : V →ᵃ[ℝ] ℝ) (a : V) (ha : f a = 0) (hl : f.linear ≠ 0)
    (hdim : Module.finrank ℝ V = Module.finrank ℝ W + 1) :
    ∃ T : V ≃ᵃ[ℝ] W × ℝ, T a = 0 ∧ ∀ x, (T x).2 = f x := by
  obtain ⟨L, hL⟩ := exists_prescribedHeight_linearEquiv
    (W := W) f.linear hl hdim
  refine ⟨(AffineEquiv.vaddConst ℝ a).symm.trans L.toAffineEquiv, ?_, ?_⟩
  · change L (a - a) = 0
    simp
  · intro x
    change (L (x - a)).2 = f x
    rw [hL]
    simpa [ha] using f.linear_apply_vsub x a

end Papers.RationalityTen

end
end
end BundlePart0

section BundlePart1
/- Source: Papers/CentralProjectionSupports.lean -/




@[expose] public section

noncomputable section

/-!
# Supporting planes under central projection

The origin is the projection center. A point (u,t), t > 0, is sent to u/t.
For an ordinary supporting form vanishing at the origin, evaluation on the
projected plane is divided by t. For a face in an affine hyperplane f = 0
avoiding the origin, subtracting g(0)/f(0) times f produces its projected
supporting form. All zero and strict inequalities are transported exactly.

These lemmas use actual affine functions and convex support sets. In
particular, the independence statements make no genericity assumption.
-/

namespace Papers.RationalityTen

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The affine height-one section used for central projection. -/
def heightOneMap : V →ᵃ[ℝ] V × ℝ :=
  (AffineMap.id ℝ V).prod (AffineMap.const ℝ V 1)

/-- Projection from the origin onto the height-one affine chart. -/
def centralProjection (x : V × ℝ) : V := x.2⁻¹ • x.1

/-- Restriction of an ambient affine form to the height-one chart. -/
def originProjectionForm (f : (V × ℝ) →ᵃ[ℝ] ℝ) : V →ᵃ[ℝ] ℝ :=
  f.comp heightOneMap

/-- The projected supporting form of g on the hyperplane f = 0. -/
def projectedFacetPlane (f g : (V × ℝ) →ᵃ[ℝ] ℝ) : V →ᵃ[ℝ] ℝ :=
  originProjectionForm (g - (g 0 / f 0) • f)

theorem affine_smul_formula {W : Type*} [AddCommGroup W] [Module ℝ W]
    (f : W →ᵃ[ℝ] ℝ) (c : ℝ) (x : W) :
    f (c • x) = c * f x + (1 - c) * f 0 := by
  simpa only [AffineMap.lineMap_apply_module, smul_zero, zero_add, add_zero,
    smul_eq_mul, add_comm] using f.apply_lineMap (0 : W) x c

theorem heightOne_centralProjection (x : V × ℝ) (ht : x.2 ≠ 0) :
    heightOneMap (centralProjection x) = x.2⁻¹ • x := by
  apply Prod.ext
  · rfl
  · change 1 = x.2⁻¹ * x.2
    exact (inv_mul_cancel₀ ht).symm

theorem originProjectionForm_eval (f : (V × ℝ) →ᵃ[ℝ] ℝ)
    (hf0 : f 0 = 0) (x : V × ℝ) (ht : x.2 ≠ 0) :
    originProjectionForm f (centralProjection x) = x.2⁻¹ * f x := by
  change f (heightOneMap (centralProjection x)) = _
  rw [heightOne_centralProjection x ht, affine_smul_formula, hf0]
  ring

theorem projectedFacetPlane_eval (f g : (V × ℝ) →ᵃ[ℝ] ℝ)
    (hf0 : f 0 ≠ 0) (x : V × ℝ) (ht : x.2 ≠ 0) (hfx : f x = 0) :
    projectedFacetPlane f g (centralProjection x) = x.2⁻¹ * g x := by
  have hz : (g - (g 0 / f 0) • f) 0 = 0 := by
    change g 0 - (g 0 / f 0) * f 0 = 0
    field_simp [hf0] <;> ring
  unfold projectedFacetPlane
  rw [originProjectionForm_eval _ hz x ht]
  change x.2⁻¹ * (g x - (g 0 / f 0) * f x) = _
  rw [hfx, mul_zero, sub_zero]

theorem projectedFacetPlane_zero_iff (f g : (V × ℝ) →ᵃ[ℝ] ℝ)
    (hf0 : f 0 ≠ 0) (x : V × ℝ) (ht : x.2 ≠ 0) (hfx : f x = 0) :
    projectedFacetPlane f g (centralProjection x) = 0 ↔ g x = 0 := by
  rw [projectedFacetPlane_eval f g hf0 x ht hfx]
  simp [ht]

theorem projectedFacetPlane_pos (f g : (V × ℝ) →ᵃ[ℝ] ℝ)
    (hf0 : f 0 ≠ 0) (x : V × ℝ) (ht : 0 < x.2) (hfx : f x = 0)
    (hg : 0 < g x) :
    0 < projectedFacetPlane f g (centralProjection x) := by
  rw [projectedFacetPlane_eval f g hf0 x ht.ne' hfx]
  exact mul_pos (inv_pos.mpr ht) hg

/-- Three supporting forms of the projection of one face are independent
whenever their original support sets are distinct in the concrete sense
recorded by the positive witnesses. -/
theorem three_projectedFacetPlanes_independent
    (f : (V × ℝ) →ᵃ[ℝ] ℝ) (hf0 : f 0 ≠ 0)
    (g : Fin 3 → (V × ℝ) →ᵃ[ℝ] ℝ)
    (S : Fin 3 → Set (V × ℝ))
    (hconvex : ∀ i, Convex ℝ (S i))
    (hne : ∀ i, (S i).Nonempty)
    (hface : ∀ i x, x ∈ S i → f x = 0)
    (hheight : ∀ i x, x ∈ S i → 0 < x.2)
    (hzero : ∀ i x, x ∈ S i → g i x = 0)
    (hnonneg : ∀ i j x, x ∈ S i → 0 ≤ g j x)
    (hwitness : ∀ i j, i ≠ j → ∃ x ∈ S i, 0 < g j x) :
    LinearIndependent ℝ (fun i => projectedFacetPlane f (g i)) := by
  classical
  have hp : ∀ i, ∃ p ∈ S i, ∀ j, i ≠ j → 0 < g j p := by
    intro i
    obtain ⟨p, hp, hpp⟩ := exists_all_affine_positive
      (S i) (hconvex i) (hne i)
      (fun j : {j : Fin 3 // i ≠ j} => g j.1)
      (fun j x hx => hnonneg i j.1 x hx)
      (fun j => hwitness i j.1 j.2)
    exact ⟨p, hp, fun j hij => hpp ⟨j, hij⟩⟩
  choose p hmem hpos using hp
  apply three_affineForms_independent_of_evaluations
    (fun i => projectedFacetPlane f (g i)) (fun i => centralProjection (p i))
  · intro i
    rw [projectedFacetPlane_eval f (g i) hf0 (p i)
      (hheight i (p i) (hmem i)).ne' (hface i (p i) (hmem i)),
      hzero i (p i) (hmem i), mul_zero]
  · intro i j hij
    exact projectedFacetPlane_pos f (g j) hf0 (p i)
      (hheight i (p i) (hmem i)) (hface i (p i) (hmem i)) (hpos i j hij)

/-- Three ordinary planes are independent. Strict positivity of the chart
height is needed only away from the apex; the support witnesses themselves
force the chosen evaluation points to be different from the apex. -/
theorem three_ordinaryProjectionForms_independent
    (g : Fin 3 → (V × ℝ) →ᵃ[ℝ] ℝ) (hg0 : ∀ i, g i 0 = 0)
    (S : Fin 3 → Set (V × ℝ))
    (hconvex : ∀ i, Convex ℝ (S i))
    (hne : ∀ i, (S i).Nonempty)
    (hheight : ∀ i x, x ∈ S i → x ≠ 0 → 0 < x.2)
    (hzero : ∀ i x, x ∈ S i → g i x = 0)
    (hnonneg : ∀ i j x, x ∈ S i → 0 ≤ g j x)
    (hwitness : ∀ i j, i ≠ j → ∃ x ∈ S i, 0 < g j x) :
    LinearIndependent ℝ (fun i => originProjectionForm (g i)) := by
  classical
  have hp : ∀ i, ∃ p ∈ S i, ∀ j, i ≠ j → 0 < g j p := by
    intro i
    obtain ⟨p, hp, hpp⟩ := exists_all_affine_positive
      (S i) (hconvex i) (hne i)
      (fun j : {j : Fin 3 // i ≠ j} => g j.1)
      (fun j x hx => hnonneg i j.1 x hx)
      (fun j => hwitness i j.1 j.2)
    exact ⟨p, hp, fun j hij => hpp ⟨j, hij⟩⟩
  choose p hmem hpos using hp
  have ht : ∀ i, 0 < (p i).2 := by
    intro i
    apply hheight i (p i) (hmem i)
    intro hpi
    obtain ⟨j, hji⟩ := exists_ne i
    have h := hpos i j hji.symm
    rw [hpi, hg0 j] at h
    exact (lt_irrefl 0) h
  apply three_affineForms_independent_of_evaluations
    (fun i => originProjectionForm (g i)) (fun i => centralProjection (p i))
  · intro i
    rw [originProjectionForm_eval (g i) (hg0 i) (p i) (ht i).ne',
      hzero i (p i) (hmem i), mul_zero]
  · intro i j hij
    rw [originProjectionForm_eval (g j) (hg0 j) (p i) (ht i).ne']
    exact mul_pos (inv_pos.mpr (ht i)) (hpos i j hij)

/-- Distinct ordinary facets give independent projected planes from two
explicit strict-support witnesses. -/
theorem two_ordinaryProjectionForms_independent
    (f g : (V × ℝ) →ᵃ[ℝ] ℝ) (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (x y : V × ℝ) (htx : 0 < x.2) (hty : 0 < y.2)
    (hfx : f x = 0) (hgx : 0 < g x)
    (hfy : 0 < f y) :
    LinearIndependent ℝ ![originProjectionForm f, originProjectionForm g] := by
  apply two_affineForms_independent_of_separating_evaluations
    (originProjectionForm f) (originProjectionForm g)
    (centralProjection x) (centralProjection y)
  · rw [originProjectionForm_eval f hf0 x htx.ne', hfx, mul_zero]
  · rw [originProjectionForm_eval g hg0 x htx.ne']
    exact (mul_pos (inv_pos.mpr htx) hgx).ne'
  · rw [originProjectionForm_eval f hf0 y hty.ne']
    exact (mul_pos (inv_pos.mpr hty) hfy).ne'

/-- An extra plane is independent of every ordinary plane whose facet does
not contain the original polygon. The witnesses are a polygon point strictly
outside the ordinary facet and a point of its containing facet outside the
polygon. -/
theorem extra_ordinaryProjectionForms_independent
    (f r g : (V × ℝ) →ᵃ[ℝ] ℝ)
    (hf0 : f 0 ≠ 0) (hg0 : g 0 = 0)
    (x y : V × ℝ) (htx : 0 < x.2) (hty : 0 < y.2)
    (hfx : f x = 0) (hfy : f y = 0)
    (hrx : r x = 0) (hgx : 0 < g x) (hry : 0 < r y) :
    LinearIndependent ℝ ![projectedFacetPlane f r, originProjectionForm g] := by
  apply two_affineForms_independent_of_separating_evaluations
    (projectedFacetPlane f r) (originProjectionForm g)
    (centralProjection x) (centralProjection y)
  · exact (projectedFacetPlane_zero_iff f r hf0 x htx.ne' hfx).2 hrx
  · rw [originProjectionForm_eval g hg0 x htx.ne']
    exact (mul_pos (inv_pos.mpr htx) hgx).ne'
  · exact (projectedFacetPlane_pos f r hf0 y hty hfy hry).ne'


end Papers.RationalityTen

end
end
end BundlePart1

section BundlePart2
/- Source: Papers/ActualVertexProjection.lean -/







@[expose] public section

/-!
# Actual normalization for projection from a four-polytope vertex

The normalizing affine equivalence is constructed from an exposing form of
the actual extreme vertex. Its height is positive at every other body point.
The projected point vectors are independent for any two distinct labels,
and for any three labels on a face avoiding the apex. These conclusions
come from actual vertex extremality, with no generic-position assumption.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.ActualThreeVertexIndependence
open Papers.PolytopeIncidenceConfiguration

structure VertexProjectionChart (P : ConvexPolytope 4) (a : VertexType P) where
  affine : E 4 ≃ᵃ[ℝ] (E 3 × ℝ)
  apex : affine a.val = 0
  positive : ∀ x ∈ P.toSet, x ≠ a.val → 0 < (affine x).2

theorem exists_vertexProjectionChart (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (a : VertexType P) : Nonempty (VertexProjectionChart P a) := by
  obtain ⟨f, hf⟩ := exists_supportsFace P (vertex_isFace P a.property)
  have ha : f a.val = 0 := hf.eq_zero (Set.mem_singleton _)
  have hpos (x : E 4) (hx : x ∈ P.toSet) (hxa : x ≠ a.val) : 0 < f x := by
    apply lt_of_le_of_ne (hf.1 x hx)
    intro hz
    exact hxa ((hf.mem_iff x).mpr ⟨hx, hz.symm⟩)
  have hc := actual_vertices_card_gt_dim P
  rw [hP] at hc
  obtain ⟨b, hb, hba⟩ := P.vertices.exists_mem_ne (by omega) a.val
  have hlin : f.linear ≠ 0 := affine_linear_ne_zero_of_zero_and_pos
    f a.val b ha (hpos b (vertex_mem_body P hb) hba)
  obtain ⟨T, hTa, hTf⟩ := exists_prescribedHeight_affineEquiv
    (W := E 3) f a.val ha hlin (by simp [finrank_euclideanSpace_fin])
  exact ⟨⟨T, hTa, fun x hx hxa => by rw [hTf]; exact hpos x hx hxa⟩⟩

abbrev ProjectionPoint (P : ConvexPolytope 4) (a : VertexType P) :=
  {v : VertexType P // v ≠ a}

namespace VertexProjectionChart

variable {P : ConvexPolytope 4} {a : VertexType P}

def projectedPoint (D : VertexProjectionChart P a) (v : ProjectionPoint P a) : E 3 :=
  centralProjection (D.affine v.val.val)

def projectedVector (D : VertexProjectionChart P a) (v : ProjectionPoint P a) :
    Fin 4 → ℝ :=
  homogeneousVertex (D.projectedPoint v)

def reciprocalHeight (D : VertexProjectionChart P a) (v : ProjectionPoint P a) : ℝ :=
  (D.affine v.val.val).2⁻¹

theorem height_pos (D : VertexProjectionChart P a) (v : ProjectionPoint P a) :
    0 < (D.affine v.val.val).2 :=
  D.positive _ (vertex_mem_body P v.val.property)
    (fun h => v.property (Subtype.ext h))

theorem reciprocalHeight_pos (D : VertexProjectionChart P a) (v : ProjectionPoint P a) :
    0 < D.reciprocalHeight v := inv_pos.mpr (D.height_pos v)

theorem projectedVector_lift (D : VertexProjectionChart P a) (v : ProjectionPoint P a) :
    coordinateHomogeneousEquiv 3 (D.projectedVector v) =
      D.reciprocalHeight v • D.affine v.val.val := by
  rw [projectedVector, coordinateHomogeneousEquiv_vertex]
  exact heightOne_centralProjection _ (D.height_pos v).ne'

theorem linear_inverse_at (D : VertexProjectionChart P a) (x : E 4) :
    D.affine.linear.symm (D.affine x) = x - a.val := by
  have h := D.affine.toAffineMap.linear_apply_vsub x a.val
  change D.affine.linear (x - a.val) = D.affine x - D.affine a.val at h
  rw [D.apex, sub_zero] at h
  rw [← h, LinearEquiv.symm_apply_apply]

def transportForm (D : VertexProjectionChart P a) (f : E 4 →ᵃ[ℝ] ℝ) :
    (E 3 × ℝ) →ᵃ[ℝ] ℝ := f.comp D.affine.symm.toAffineMap

@[simp] theorem transportForm_affine (D : VertexProjectionChart P a)
    (f : E 4 →ᵃ[ℝ] ℝ) (x : E 4) :
    D.transportForm f (D.affine x) = f x := by
  simp only [transportForm, AffineMap.comp_apply, AffineEquiv.coe_toAffineMap,
    AffineEquiv.symm_apply_apply]

@[simp] theorem transportForm_zero (D : VertexProjectionChart P a)
    (f : E 4 →ᵃ[ℝ] ℝ) : D.transportForm f 0 = f a.val := by
  rw [← D.apex, D.transportForm_affine]

def ordinaryForm (D : VertexProjectionChart P a) (f : E 4 →ᵃ[ℝ] ℝ) :
    E 3 →ᵃ[ℝ] ℝ := originProjectionForm (D.transportForm f)

theorem ordinaryForm_eval (D : VertexProjectionChart P a)
    (f : E 4 →ᵃ[ℝ] ℝ) (hfa : f a.val = 0) (v : ProjectionPoint P a) :
    D.ordinaryForm f (D.projectedPoint v) = D.reciprocalHeight v * f v.val.val := by
  unfold ordinaryForm projectedPoint
  rw [originProjectionForm_eval _ (by simpa using hfa) _ (D.height_pos v).ne',
    D.transportForm_affine]
  rfl

/-- Independence of the normalized homogeneous directions follows from
independence before positive rescaling. -/
theorem projected_independent_of_directions
    {I : Type*} [Fintype I] (D : VertexProjectionChart P a)
    (v : I → ProjectionPoint P a)
    (h : LinearIndependent ℝ (fun i => D.affine (v i).val.val)) :
    LinearIndependent ℝ (fun i => D.projectedVector (v i)) := by
  let w : I → ℝˣ := fun i => Units.mk0 (D.reciprocalHeight (v i))
    (D.reciprocalHeight_pos (v i)).ne'
  have hs := h.units_smul w
  apply LinearIndependent.of_comp (coordinateHomogeneousEquiv 3).toLinearMap
  simpa only [Function.comp_def, LinearEquiv.coe_coe, projectedVector_lift, Pi.smul_def', Pi.smul_apply,
    Units.smul_def, w, Units.val_mk0] using hs

theorem two_projected_points_independent
    {I : Type*} [Fintype I] (D : VertexProjectionChart P a)
    (hP : P.IsFullDim) (v : I → ProjectionPoint P a)
    (hinj : Function.Injective v) (hI : Fintype.card I ≤ 2) :
    LinearIndependent ℝ (fun i => D.projectedVector (v i)) := by
  let w : Option I → VertexType P := Option.elim' a (fun i => (v i).val)
  have hwinj : Function.Injective w := by
    intro i j h
    cases i <;> cases j
    · rfl
    · rename_i j
      exact False.elim ((v j).property h.symm)
    · rename_i i
      exact False.elim ((v i).property h)
    · rename_i i j
      exact congrArg some (hinj (Subtype.ext h))
  have hc := actual_vertices_card_gt_dim P
  rw [hP] at hc
  have hw := small_homogeneous_vertex_family_independent P (by omega) w hwinj
    (by simpa only [Fintype.card_option] using Nat.succ_le_succ hI)
  apply D.projected_independent_of_directions v
  apply Fintype.linearIndependent_iff.mpr
  intro c hsum i
  have hshift : ∑ j, c j • ((v j).val.val - a.val) = 0 := by
    have hh := congrArg D.affine.linear.symm hsum
    simpa only [map_sum, map_smul, map_zero, D.linear_inverse_at] using hh
  have hvec : ∑ j, c j • (v j).val.val = (∑ j, c j) • a.val := by
    rw [show (∑ j, c j • ((v j).val.val - a.val)) =
      (∑ j, c j • (v j).val.val) - (∑ j, c j) • a.val by
        simp only [smul_sub, Finset.sum_sub_distrib, Finset.sum_smul]] at hshift
    exact sub_eq_zero.mp hshift
  let b : Option I → ℝ := Option.elim' (-(∑ j, c j)) c
  have hb : ∑ j, b j • homogeneousVertex (w j).val = 0 := by
    apply (coordinateHomogeneousEquiv 4).injective
    simp only [map_sum, map_smul, map_zero, coordinateHomogeneousEquiv_vertex]
    apply Prod.ext
    · simpa only [Fintype.sum_option, w, b, Option.elim'_none, Option.elim'_some,
        Prod.fst_sum, Prod.fst_add, Prod.smul_fst, Papers.HomogeneousSpanDimension.liftPoint,
        hvec, neg_smul, Prod.fst_neg, Prod.fst_zero, neg_add_cancel]
    · simp only [Fintype.sum_option, w, b, Option.elim'_none, Option.elim'_some,
        Prod.snd_sum, Prod.snd_add, Prod.smul_snd, Papers.HomogeneousSpanDimension.liftPoint,
        smul_eq_mul, mul_one, Prod.snd_zero, neg_add_cancel]
  exact Fintype.linearIndependent_iff.mp hw b hb (some i)

def avoidingHeight (D : VertexProjectionChart P a) (f : E 4 →ᵃ[ℝ] ℝ) :
    (E 3 × ℝ) →ₗ[ℝ] ℝ :=
  (-(f a.val)⁻¹) • (f.linear.comp D.affine.linear.symm.toLinearMap)

/-- Linear reconstruction of homogeneous points on a hyperplane avoiding
the projection center. This is the exact projective-isomorphism argument. -/
def avoidingFaceLift (D : VertexProjectionChart P a) (f : E 4 →ᵃ[ℝ] ℝ) :
    (E 3 × ℝ) →ₗ[ℝ] (E 4 × ℝ) where
  toFun x := (D.affine.linear.symm x + D.avoidingHeight f x • a.val,
    D.avoidingHeight f x)
  map_add' x y := by
    apply Prod.ext
    · simp only [map_add, add_smul, Prod.fst_add]
      abel
    · exact map_add _ _ _
  map_smul' t x := by
    apply Prod.ext
    · simp only [map_smul, smul_add, smul_smul, smul_eq_mul, Prod.smul_fst,
        RingHom.id_apply]
    · exact map_smul _ _ _

theorem avoidingFaceLift_apply (D : VertexProjectionChart P a)
    (f : E 4 →ᵃ[ℝ] ℝ) (hfa : f a.val ≠ 0) (x : E 4) (hfx : f x = 0) :
    D.avoidingFaceLift f (D.affine x) = (x, 1) := by
  have hlinear := f.linear_apply_vsub x a.val
  change f.linear (x - a.val) = f x - f a.val at hlinear
  have hheight : D.avoidingHeight f (D.affine x) = 1 := by
    change -(f a.val)⁻¹ * f.linear (D.affine.linear.symm (D.affine x)) = 1
    rw [D.linear_inverse_at, hlinear, hfx]
    field_simp [hfa] <;> ring
  apply Prod.ext
  · change D.affine.linear.symm (D.affine x) +
      D.avoidingHeight f (D.affine x) • a.val = x
    rw [D.linear_inverse_at, hheight, one_smul, sub_add_cancel]
  · exact hheight

theorem projected_independent_of_homogeneous_on_avoiding_face
    {I : Type*} [Fintype I] (D : VertexProjectionChart P a)
    (v : I → ProjectionPoint P a)
    (hbase : LinearIndependent ℝ (fun i => homogeneousVertex (v i).val.val))
    (F : FaceType P)
    (haF : a.val ∉ F.val) (hvF : ∀ i, (v i).val.val ∈ F.val) :
    LinearIndependent ℝ (fun i => D.projectedVector (v i)) := by
  obtain ⟨f, hf⟩ := exists_supportsFace P F.property
  have hfa : f a.val ≠ 0 := by
    intro h
    exact haF ((hf.mem_iff a.val).mpr ⟨vertex_mem_body P a.property, h⟩)
  have hlift := hbase.map' (coordinateHomogeneousEquiv 4).toLinearMap
    (LinearMap.ker_eq_bot.mpr (coordinateHomogeneousEquiv 4).injective)
  apply D.projected_independent_of_directions v
  apply LinearIndependent.of_comp (D.avoidingFaceLift f)
  have heq : (fun i => D.avoidingFaceLift f (D.affine (v i).val.val)) =
      (fun i => coordinateHomogeneousEquiv 4 (homogeneousVertex (v i).val.val)) := by
    funext i
    rw [D.avoidingFaceLift_apply f hfa _ (hf.eq_zero (hvF i)),
      coordinateHomogeneousEquiv_vertex]
    rfl
  change LinearIndependent ℝ (fun i => D.avoidingFaceLift f (D.affine (v i).val.val))
  rw [heq]
  exact hlift

theorem projected_points_on_avoiding_face_independent
    {I : Type*} [Fintype I] (D : VertexProjectionChart P a) (hP : P.IsFullDim)
    (v : I → ProjectionPoint P a) (hinj : Function.Injective v)
    (hI : Fintype.card I ≤ 3) (F : FaceType P)
    (haF : a.val ∉ F.val) (hvF : ∀ i, (v i).val.val ∈ F.val) :
    LinearIndependent ℝ (fun i => D.projectedVector (v i)) := by
  have hc := actual_vertices_card_gt_dim P
  rw [hP] at hc
  have hbase := small_homogeneous_vertex_family_independent P (by omega)
    (fun i => (v i).val) (Subtype.val_injective.comp hinj) hI
  exact D.projected_independent_of_homogeneous_on_avoiding_face v hbase F haF hvF

/-- A separating functional adjoins one new independent vector. This
formulation works directly with the arbitrary finite label set. -/
theorem independent_of_except_functional {I V : Type*} [Fintype I]
    [AddCommGroup V] [Module ℝ V] (p : I → V) (k : I)
    (hrest : LinearIndependent ℝ (fun i : {i : I // i ≠ k} => p i.val))
    (ell : V →ₗ[ℝ] ℝ) (hzero : ∀ i, i ≠ k → ell (p i) = 0)
    (hne : ell (p k) ≠ 0) : LinearIndependent ℝ p := by
  have hspan : Submodule.span ℝ
      (Set.range (fun i : {i : I // i ≠ k} => p i.val)) ≤ ell.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hzero i.val i.property
  have hk : p k ∉ Submodule.span ℝ
      (Set.range (fun i : {i : I // i ≠ k} => p i.val)) :=
    fun h => hne (hspan h)
  apply (linearIndependent_equiv (Equiv.optionSubtypeNe k)).mp
  apply linearIndependent_option.mpr
  constructor
  · simpa only [Function.comp_def, Equiv.optionSubtypeNe_some] using hrest
  · simpa only [Function.comp_def, Equiv.optionSubtypeNe_some,
      Equiv.optionSubtypeNe_none] using hk

/-- The ordinary three-point facial witness of rule (i): the apex and
all but one retained point lie in a face, and the remaining point lies
outside it. The complementary case, where the apex is outside the face,
is already `projected_points_on_avoiding_face_independent`. -/
theorem projected_points_of_facial_witness_independent
    {I : Type*} [Fintype I] (D : VertexProjectionChart P a) (hP : P.IsFullDim)
    (v : I → ProjectionPoint P a) (hinj : Function.Injective v)
    (hI : Fintype.card I ≤ 3) (k : I) (F : FaceType P)
    (haF : a.val ∈ F.val) (hout : (v k).val.val ∉ F.val)
    (hin : ∀ i, i ≠ k → (v i).val.val ∈ F.val) :
    LinearIndependent ℝ (fun i => D.projectedVector (v i)) := by
  obtain ⟨f, hf⟩ := exists_supportsFace P F.property
  have hfa : f a.val = 0 := hf.eq_zero haF
  have hrestcard : Fintype.card {i : I // i ≠ k} ≤ 2 := by
    have hh := Fintype.card_congr (Equiv.optionSubtypeNe k)
    rw [Fintype.card_option] at hh
    omega
  have hrest := D.two_projected_points_independent hP
    (fun i : {i : I // i ≠ k} => v i.val)
    (hinj.comp Subtype.val_injective) hrestcard
  let ell := dotLinear (coefficientVector (D.ordinaryForm f))
  have heval (i : I) : ell (D.projectedVector (v i)) =
      D.reciprocalHeight (v i) * f (v i).val.val := by
    change coefficientVector (D.ordinaryForm f) ⬝ᵥ
      homogeneousVertex (D.projectedPoint (v i)) = _
    rw [coefficient_dot_homogeneous, D.ordinaryForm_eval f hfa]
  apply independent_of_except_functional _ k hrest ell
  · intro i hi
    rw [heval, hf.eq_zero (hin i hi), mul_zero]
  · rw [heval]
    apply mul_ne_zero (D.reciprocalHeight_pos (v k)).ne'
    intro hz
    exact hout ((hf.mem_iff _).mpr ⟨vertex_mem_body P (v k).val.property, hz⟩)

/-- A facially certified four-point frame stays independent after projecting
an avoiding facet: three points lie on one of its faces and the fourth does
not. This is also valid for every subfamily of such a frame. -/
theorem projected_frame_of_facial_witness_independent
    {I : Type*} [Fintype I] (D : VertexProjectionChart P a) (hP : P.IsFullDim)
    (v : I → ProjectionPoint P a) (hinj : Function.Injective v)
    (hI : Fintype.card I ≤ 4) (k : I) (R F : FaceType P)
    (hout : (v k).val.val ∉ R.val)
    (hin : ∀ i, i ≠ k → (v i).val.val ∈ R.val)
    (haF : a.val ∉ F.val) (hvF : ∀ i, (v i).val.val ∈ F.val) :
    LinearIndependent ℝ (fun i => D.projectedVector (v i)) := by
  obtain ⟨f, hf⟩ := exists_supportsFace P R.property
  have hrestcard : Fintype.card {i : I // i ≠ k} ≤ 3 := by
    have hh := Fintype.card_congr (Equiv.optionSubtypeNe k)
    rw [Fintype.card_option] at hh
    omega
  have hc := actual_vertices_card_gt_dim P
  rw [hP] at hc
  have hrest := small_homogeneous_vertex_family_independent P (by omega)
    (fun i : {i : I // i ≠ k} => (v i.val).val)
    (Subtype.val_injective.comp (hinj.comp Subtype.val_injective)) hrestcard
  have hbase : LinearIndependent ℝ (fun i => homogeneousVertex (v i).val.val) := by
    apply independent_of_except_functional _ k hrest (dotLinear (coefficientVector f))
    · intro i hi
      change coefficientVector f ⬝ᵥ homogeneousVertex (v i).val.val = 0
      rw [coefficient_dot_homogeneous]
      exact hf.eq_zero (hin i hi)
    · change coefficientVector f ⬝ᵥ homogeneousVertex (v k).val.val ≠ 0
      rw [coefficient_dot_homogeneous]
      intro hz
      exact hout ((hf.mem_iff _).mpr ⟨vertex_mem_body P (v k).val.property, hz⟩)
  exact D.projected_independent_of_homogeneous_on_avoiding_face v hbase F haF hvF

end VertexProjectionChart
end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart2

section BundlePart3
/- Source: Papers/ProjectionPlaneForms.lean -/





@[expose] public section

/-!
# Uniqueness of a plane through an independent projected triangle

Plane forms are actual affine functionals. Three independent homogeneous
point vectors have a one-dimensional annihilator, so two nonzero forms
vanishing on them differ by a nonzero scalar. This permits changing the
containing facet used to describe an extra plane without changing its
incidences or its linear independence with other planes.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Matrix Module Set
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open Papers.PolytopeIncidenceConfiguration
open Papers.ActualThreeVertexIndependence

theorem forms_proportional_of_three_independent_zeros
    (q : Fin 3 → E 3)
    (hq : LinearIndependent ℝ (fun i => homogeneousVertex (q i)))
    (f g : E 3 →ᵃ[ℝ] ℝ) (hf : f ≠ 0) (hg : g ≠ 0)
    (hfq : ∀ i, f (q i) = 0) (hgq : ∀ i, g (q i) = 0) :
    ∃ c : ℝ, c ≠ 0 ∧ f = c • g := by
  let M : Matrix (Fin 3) (Fin 4) ℝ := fun i => homogeneousVertex (q i)
  let L := Matrix.mulVecLin M
  have hM : LinearIndependent ℝ M.row := hq
  have hrank : M.rank = 3 := by
    simpa only [Fintype.card_fin] using (hM.rank_matrix (M := M))
  have hdim : finrank ℝ L.ker = 1 := by
    have h := L.finrank_range_add_finrank_ker
    change M.rank + finrank ℝ L.ker = finrank ℝ (Fin 4 → ℝ) at h
    rw [hrank] at h
    simp only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] at h
    omega
  have hmem (u : E 3 →ᵃ[ℝ] ℝ) (hu : ∀ i, u (q i) = 0) :
      coefficientVector u ∈ L.ker := by
    apply LinearMap.mem_ker.mpr
    ext i
    change homogeneousVertex (q i) ⬝ᵥ coefficientVector u = 0
    rw [dotProduct_comm, coefficient_dot_homogeneous]
    exact hu i
  have hne (u : E 3 →ᵃ[ℝ] ℝ) (hu : u ≠ 0) : coefficientVector u ≠ 0 := by
    intro h
    apply hu
    apply coefficientVector_injective
    simpa only [show coefficientVector (0 : E 3 →ᵃ[ℝ] ℝ) = 0 from
      coefficientVectorLinear.map_zero] using h
  let x : L.ker := ⟨coefficientVector g, hmem g hgq⟩
  let y : L.ker := ⟨coefficientVector f, hmem f hfq⟩
  have hx : x ≠ 0 := fun h => hne g hg (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hdim hx y
  have hcoeff : coefficientVector f = c • coefficientVector g :=
    (congrArg Subtype.val hc).symm
  have hfg : f = c • g := by
    apply coefficientVector_injective
    simpa only [show coefficientVector (c • g) = c • coefficientVector g from
      coefficientVectorLinear.map_smul c g] using hcoeff
  refine ⟨c, ?_, hfg⟩
  intro hc0
  exact hf (by simpa only [hc0, zero_smul] using hfg)

/-- Independently rescaling each nonzero plane form preserves independence. -/
theorem independent_forms_of_proportional
    {I : Type*} (f g : I → E 3 →ᵃ[ℝ] ℝ)
    (hg : LinearIndependent ℝ g)
    (hfg : ∀ i, ∃ c : ℝ, c ≠ 0 ∧ f i = c • g i) :
    LinearIndependent ℝ f := by
  choose c hc hfg using hfg
  let u : I → ℝˣ := fun i => Units.mk0 (c i) (hc i)
  have h := hg.units_smul u
  convert h using 1
  funext i
  simpa only [Pi.smul_def', Pi.smul_apply, Units.smul_def, u, Units.val_mk0]
    using hfg i

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart3

section BundlePart4
/- Source: Papers/ActualProjectedPlanes.lean -/







@[expose] public section

/-!
# The actual plane nodes in a vertex projection

Ordinary nodes are the actual facets containing the selected vertex.
Extra nodes are the actual two-faces avoiding it whose incidences are not
already contained in an ordinary node. An extra form is constructed in a
containing facet avoiding the center. Any other such containing facet gives
the same plane up to a nonzero scalar, proved from three actual extreme
vertices of the polygon.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds Papers.PolytopeNonedgeAllocation
open Papers.PolytopeIncidenceConfiguration

abbrev OrdinaryProjectionPlane (P : ConvexPolytope 4) (a : VertexType P) :=
  {F : FacetType P // a.val ∈ F.val.val}

abbrev ExtraProjectionPlane (P : ConvexPolytope 4) (a : VertexType P) :=
  {R : Face P 2 // a.val ∉ R.val.carrier ∧
    ∀ F : OrdinaryProjectionPlane P a, ¬ R.val.carrier ⊆ F.val.val.val}

abbrev ActualProjectionPlane (P : ConvexPolytope 4) (a : VertexType P) :=
  OrdinaryProjectionPlane P a ⊕ ExtraProjectionPlane P a

def projectionPlaneCarrier {P : ConvexPolytope 4} {a : VertexType P} :
    ActualProjectionPlane P a → Set (E 4)
  | Sum.inl F => F.val.val.val
  | Sum.inr R => R.val.val.carrier

theorem projectionPlaneCarrier_isFace {P : ConvexPolytope 4} {a : VertexType P}
    (B : ActualProjectionPlane P a) : P.IsFace (projectionPlaneCarrier B) := by
  cases B with
  | inl F => exact F.val.property.1
  | inr R => exact R.val.val.isFace

def actualProjectionIncidence {P : ConvexPolytope 4} {a : VertexType P}
    (v : ProjectionPoint P a) (B : ActualProjectionPlane P a) : Prop :=
  v.val.val ∈ projectionPlaneCarrier B

theorem extra_exists_avoiding_facet (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (a : VertexType P) (R : ExtraProjectionPlane P a) :
    ∃ F : FacetType P, R.val.val.carrier ⊆ F.val.val ∧ a.val ∉ F.val.val := by
  obtain ⟨F, hF, hRF, haF⟩ := exists_facet_containing_not_mem P hP
    R.val.val.carrier R.val.val.isFace a.val (vertex_mem_body P a.property) R.property.1
  exact ⟨⟨⟨F, hF.1⟩, hF⟩, hRF, haF⟩

def extraContainingFacet (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (a : VertexType P) (R : ExtraProjectionPlane P a) : FacetType P :=
  (extra_exists_avoiding_facet P hP a R).choose

theorem extraContainingFacet_spec (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (a : VertexType P) (R : ExtraProjectionPlane P a) :
    R.val.val.carrier ⊆ (extraContainingFacet P hP a R).val.val ∧
      a.val ∉ (extraContainingFacet P hP a R).val.val :=
  (extra_exists_avoiding_facet P hP a R).choose_spec

def projectedPolygonSupport (P : ConvexPolytope 4) (R : Face P 2) : E 4 →ᵃ[ℝ] ℝ :=
  (exists_supportsFace P R.val.isFace).choose

theorem projectedPolygonSupport_spec (P : ConvexPolytope 4) (R : Face P 2) :
    SupportsFace P R.val.carrier (projectedPolygonSupport P R) :=
  (exists_supportsFace P R.val.isFace).choose_spec

def projectionCarrierSupport {P : ConvexPolytope 4} {a : VertexType P} :
    ActualProjectionPlane P a → E 4 →ᵃ[ℝ] ℝ
  | Sum.inl F => chosenFacetForm P F.val
  | Sum.inr R => projectedPolygonSupport P R.val

theorem projectionCarrierSupport_spec {P : ConvexPolytope 4} {a : VertexType P}
    (B : ActualProjectionPlane P a) :
    SupportsFace P (projectionPlaneCarrier B) (projectionCarrierSupport B) := by
  cases B with
  | inl F => exact chosenFacetForm_supports P F.val
  | inr R => exact projectedPolygonSupport_spec P R.val

namespace VertexProjectionChart

variable {P : ConvexPolytope 4} {a : VertexType P}

def extraForm (D : VertexProjectionChart P a) (hP : P.IsFullDim)
    (R : ExtraProjectionPlane P a) : E 3 →ᵃ[ℝ] ℝ :=
  projectedFacetPlane
    (D.transportForm (chosenFacetForm P (extraContainingFacet P hP a R)))
    (D.transportForm (projectedPolygonSupport P R.val))

def planeForm (D : VertexProjectionChart P a) (hP : P.IsFullDim) :
    ActualProjectionPlane P a → E 3 →ᵃ[ℝ] ℝ
  | Sum.inl F => D.ordinaryForm (chosenFacetForm P F.val)
  | Sum.inr R => D.extraForm hP R

def planeVector (D : VertexProjectionChart P a) (hP : P.IsFullDim)
    (B : ActualProjectionPlane P a) : Fin 4 → ℝ :=
  coefficientVector (D.planeForm hP B)

theorem support_at_apex_ne_zero (D : VertexProjectionChart P a)
    (F : FacetType P) (haF : a.val ∉ F.val.val) :
    D.transportForm (chosenFacetForm P F) 0 ≠ 0 := by
  rw [D.transportForm_zero]
  intro hz
  exact haF (((chosenFacetForm_supports P F).mem_iff a.val).mpr
    ⟨vertex_mem_body P a.property, hz⟩)

theorem extraForm_eval_on_facet (D : VertexProjectionChart P a)
    (hP : P.IsFullDim) (R : ExtraProjectionPlane P a)
    (x : E 4) (hx : x ∈ (extraContainingFacet P hP a R).val.val) :
    D.extraForm hP R (centralProjection (D.affine x)) =
      (D.affine x).2⁻¹ * projectedPolygonSupport P R.val x := by
  have haF := (extraContainingFacet_spec P hP a R).2
  have hxP := face_subset_toSet P (extraContainingFacet P hP a R).property.1 hx
  have hxa : x ≠ a.val := fun heq => haF (heq ▸ hx)
  unfold extraForm
  rw [projectedFacetPlane_eval _ _ (D.support_at_apex_ne_zero _ haF)
    _ (D.positive x hxP hxa).ne' (by
      rw [D.transportForm_affine]
      exact (chosenFacetForm_supports P _).eq_zero hx), D.transportForm_affine]

theorem planeForm_zero_of_incident (D : VertexProjectionChart P a)
    (hP : P.IsFullDim) (v : ProjectionPoint P a) (B : ActualProjectionPlane P a)
    (hvB : actualProjectionIncidence v B) :
    D.planeForm hP B (D.projectedPoint v) = 0 := by
  cases B with
  | inl F =>
    change D.ordinaryForm (chosenFacetForm P F.val) (D.projectedPoint v) = 0
    rw [D.ordinaryForm_eval _ ((chosenFacetForm_supports P F.val).eq_zero F.property) v,
      (chosenFacetForm_supports P F.val).eq_zero hvB, mul_zero]
  | inr R =>
    change D.extraForm hP R (centralProjection (D.affine v.val.val)) = 0
    rw [D.extraForm_eval_on_facet hP R _
      ((extraContainingFacet_spec P hP a R).1 hvB),
      (projectedPolygonSupport_spec P R.val).eq_zero hvB, mul_zero]

theorem planeVector_dot_projectedVector (D : VertexProjectionChart P a)
    (hP : P.IsFullDim) (v : ProjectionPoint P a) (B : ActualProjectionPlane P a)
    (hvB : actualProjectionIncidence v B) :
    D.planeVector hP B ⬝ᵥ D.projectedVector v = 0 := by
  rw [planeVector, projectedVector, coefficient_dot_homogeneous]
  exact D.planeForm_zero_of_incident hP v B hvB

theorem ordinaryForm_positive_outside (D : VertexProjectionChart P a)
    (F : OrdinaryProjectionPlane P a) (x : E 4)
    (hx : x ∈ P.toSet) (hxF : x ∉ F.val.val.val) :
    0 < D.ordinaryForm (chosenFacetForm P F.val) (centralProjection (D.affine x)) := by
  have hxa : x ≠ a.val := fun h => hxF (h.symm ▸ F.property)
  have hzero := (chosenFacetForm_supports P F.val).eq_zero F.property
  have hpos : 0 < chosenFacetForm P F.val x := by
    apply lt_of_le_of_ne ((chosenFacetForm_supports P F.val).1 x hx)
    intro hz
    exact hxF (((chosenFacetForm_supports P F.val).mem_iff x).mpr ⟨hx, hz.symm⟩)
  unfold ordinaryForm
  rw [originProjectionForm_eval _ (by simpa using hzero)
    _ (D.positive x hx hxa).ne', D.transportForm_affine]
  exact mul_pos (inv_pos.mpr (D.positive x hx hxa)) hpos

theorem ordinaryForm_ne_zero (D : VertexProjectionChart P a)
    (F : OrdinaryProjectionPlane P a) :
    D.ordinaryForm (chosenFacetForm P F.val) ≠ 0 := by
  have hnot : ¬ P.toSet ⊆ F.val.val.val := fun h =>
    F.val.property.ne_toSet (Set.Subset.antisymm
      (face_subset_toSet P F.val.property.1) h)
  obtain ⟨x, hx, hxF⟩ := Set.not_subset.mp hnot
  have hpos := D.ordinaryForm_positive_outside F x hx hxF
  intro heq
  rw [heq] at hpos
  exact (lt_irrefl 0) hpos

theorem exists_facet_point_outside_polygon (D : VertexProjectionChart P a)
    (hP : P.IsFullDim) (F : FacetType P) (R : Face P 2) :
    ∃ x ∈ F.val.val, x ∉ R.val.carrier := by
  apply Set.not_subset.mp
  intro hFR
  have hle : faceDim F.val.val ≤ faceDim R.val.carrier :=
    Submodule.finrank_mono (vectorSpan_mono ℝ hFR)
  have hdF := F.property.2
  rw [hP, R.property] at *
  omega

theorem extraForm_ne_zero (D : VertexProjectionChart P a)
    (hP : P.IsFullDim) (R : ExtraProjectionPlane P a) : D.extraForm hP R ≠ 0 := by
  let F := extraContainingFacet P hP a R
  obtain ⟨x, hx, hxR⟩ := D.exists_facet_point_outside_polygon hP F R.val
  have hxP := face_subset_toSet P F.property.1 hx
  have hxa : x ≠ a.val := fun heq =>
    (extraContainingFacet_spec P hP a R).2 (heq ▸ hx)
  have hpos : 0 < projectedPolygonSupport P R.val x := by
    apply lt_of_le_of_ne ((projectedPolygonSupport_spec P R.val).1 x hxP)
    intro hz
    exact hxR (((projectedPolygonSupport_spec P R.val).mem_iff x).mpr ⟨hxP, hz.symm⟩)
  have heval := D.extraForm_eval_on_facet hP R x hx
  have hp : 0 < D.extraForm hP R (centralProjection (D.affine x)) := by
    rw [heval]
    exact mul_pos (inv_pos.mpr (D.positive x hxP hxa)) hpos
  intro hz
  rw [hz] at hp
  exact (lt_irrefl 0) hp

theorem planeForm_ne_zero (D : VertexProjectionChart P a)
    (hP : P.IsFullDim) (B : ActualProjectionPlane P a) : D.planeForm hP B ≠ 0 := by
  cases B with
  | inl F => exact D.ordinaryForm_ne_zero F
  | inr R => exact D.extraForm_ne_zero hP R

theorem planeVector_ne_zero (D : VertexProjectionChart P a)
    (hP : P.IsFullDim) (B : ActualProjectionPlane P a) : D.planeVector hP B ≠ 0 := by
  intro hz
  apply D.planeForm_ne_zero hP B
  apply coefficientVector_injective
  simpa only [planeVector, show coefficientVector (0 : E 3 →ᵃ[ℝ] ℝ) = 0 from
    coefficientVectorLinear.map_zero] using hz

/-- Every actual polygon avoiding the center supplies an independent
projected triangle, without selecting a nondegenerate realization. -/
theorem exists_projected_polygon_triangle (D : VertexProjectionChart P a)
    (hP : P.IsFullDim) (R : Face P 2) (haR : a.val ∉ R.val.carrier) :
    ∃ v : Fin 3 → ProjectionPoint P a,
      Function.Injective v ∧ (∀ i, (v i).val.val ∈ R.val.carrier) ∧
      LinearIndependent ℝ (fun i => D.projectedVector (v i)) := by
  have hc : 3 ≤ Fintype.card (VerticesOn P R.val.carrier) := by
    simpa only [Nat.card_eq_fintype_card] using face_vertices_card_ge_dim_add_one P 2 R
  let e : Fin 3 ↪ VerticesOn P R.val.carrier :=
    (Fin.castLEEmb hc).trans (Fintype.equivFin (VerticesOn P R.val.carrier)).symm.toEmbedding
  let v : Fin 3 → ProjectionPoint P a := fun i =>
    ⟨(e i).val, fun h => haR (congrArg Subtype.val h ▸ (e i).property)⟩
  have hinj : Function.Injective v := by
    intro i j h
    apply e.injective
    apply Subtype.ext
    exact congrArg (fun w : ProjectionPoint P a => w.val) h
  have hmem : ∀ i, (v i).val.val ∈ R.val.carrier := fun i => (e i).property
  exact ⟨v, hinj, hmem, D.projected_points_on_avoiding_face_independent hP v hinj
    (by simp) ⟨R.val.carrier, R.val.isFace⟩ haR hmem⟩

end VertexProjectionChart
end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart4

section BundlePart5
/- Source: Papers/ProjectionPlaneIndependence.lean -/



@[expose] public section

/-!
# Geometric independence in the projection deletion rules

All certificates in this file concern actual faces and their incidences.
The conclusions are linear independence of the actual projected affine
forms. In particular, no independence or general-position condition is
inserted into the combinatorial input.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds Papers.PolytopeNonedgeAllocation
open Papers.PolytopeIncidenceConfiguration

/-- The plane is a supporting plane of the projection of `F` precisely
when its original carrier cuts out the actual polygon `R` in `F`. -/
def ProjectedFacetTrace {P : ConvexPolytope 4} {a : VertexType P}
    (B : ActualProjectionPlane P a) (F : FacetType P) (R : Face P 2) : Prop :=
  R.val.carrier = F.val.val ∩ projectionPlaneCarrier B

namespace VertexProjectionChart

variable {P : ConvexPolytope 4} {a : VertexType P}

theorem ordinaryForm_pair_independent (D : VertexProjectionChart P a)
    (F G : OrdinaryProjectionPlane P a) (hFG : F ≠ G) :
    LinearIndependent ℝ
      ![D.ordinaryForm (chosenFacetForm P F.val),
        D.ordinaryForm (chosenFacetForm P G.val)] := by
  have hval : F.val ≠ G.val := fun h => hFG (Subtype.ext h)
  obtain ⟨x, hxF, hxG⟩ := exists_facet_point_strict_other P F.val G.val hval
  obtain ⟨y, hyG, hyF⟩ := exists_facet_point_strict_other P G.val F.val hval.symm
  have hxP := face_subset_toSet P F.val.property.1 hxF
  have hyP := face_subset_toSet P G.val.property.1 hyG
  have hxa : x ≠ a.val := by
    intro h
    rw [h, (chosenFacetForm_supports P G.val).eq_zero G.property] at hxG
    exact (lt_irrefl 0) hxG
  have hya : y ≠ a.val := by
    intro h
    rw [h, (chosenFacetForm_supports P F.val).eq_zero F.property] at hyF
    exact (lt_irrefl 0) hyF
  apply two_ordinaryProjectionForms_independent
    (D.transportForm (chosenFacetForm P F.val))
    (D.transportForm (chosenFacetForm P G.val))
    (by simpa using (chosenFacetForm_supports P F.val).eq_zero F.property)
    (by simpa using (chosenFacetForm_supports P G.val).eq_zero G.property)
    (D.affine x) (D.affine y) (D.positive x hxP hxa) (D.positive y hyP hya)
  · simpa using (chosenFacetForm_supports P F.val).eq_zero hxF
  · simpa using hxG
  · simpa using hyF

theorem ordinaryForms_three_independent (D : VertexProjectionChart P a)
    (F : Fin 3 → OrdinaryProjectionPlane P a) (hF : Function.Injective F) :
    LinearIndependent ℝ (fun i => D.ordinaryForm (chosenFacetForm P (F i).val)) := by
  apply three_ordinaryProjectionForms_independent
    (fun i => D.transportForm (chosenFacetForm P (F i).val))
    (fun i => by simpa using (chosenFacetForm_supports P (F i).val).eq_zero (F i).property)
    (fun i => D.affine '' (F i).val.val.val)
  · intro i
    exact Convex.affine_image D.affine.toAffineMap
      ((F i).val.property.1.1.convex (convex_convexHull ℝ _))
  · intro i
    exact (F i).val.property.1.2.image D.affine
  · rintro i _ ⟨x, hx, rfl⟩ hxa
    apply D.positive x (face_subset_toSet P (F i).val.property.1 hx)
    intro h
    exact hxa (by rw [h, D.apex])
  · rintro i _ ⟨x, hx, rfl⟩
    simpa using (chosenFacetForm_supports P (F i).val).eq_zero hx
  · rintro i j _ ⟨x, hx, rfl⟩
    simpa using (chosenFacetForm_supports P (F j).val).1 x
      (face_subset_toSet P (F i).val.property.1 hx)
  · intro i j hij
    obtain ⟨x, hx, hpos⟩ := exists_facet_point_strict_other P (F i).val (F j).val
      (fun heq => hij (hF (Subtype.ext heq)))
    exact ⟨D.affine x, ⟨x, hx, rfl⟩, by simpa using hpos⟩

theorem small_ordinaryForms_independent {I : Type*} [Fintype I]
    (D : VertexProjectionChart P a) (F : I → OrdinaryProjectionPlane P a)
    (hF : Function.Injective F) (hI : Fintype.card I ≤ 3) :
    LinearIndependent ℝ (fun i => D.ordinaryForm (chosenFacetForm P (F i).val)) := by
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have hfin : LinearIndependent ℝ
      (fun i => D.ordinaryForm (chosenFacetForm P (F (e i)).val)) := by
    apply linearIndependent_fin_of_le_three _ hI
    · intro i
      exact D.ordinaryForm_ne_zero (F (e i))
    · intro i j hij
      exact D.ordinaryForm_pair_independent _ _ (fun h => hij (e.injective (hF h)))
    · intro i j k hij hik hjk
      let G : Fin 3 → OrdinaryProjectionPlane P a := ![F (e i), F (e j), F (e k)]
      have hG : Function.Injective G := by
        intro u v huv
        have hei := fun {u v} (h : F (e u) = F (e v)) => e.injective (hF h)
        fin_cases u <;> fin_cases v <;> simp_all [G]
        all_goals have h := hei huv; simp_all
      convert D.ordinaryForms_three_independent G hG using 1
      ext u
      fin_cases u <;> rfl
  have h := hfin.comp e.symm e.symm.injective
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using h

theorem extra_ordinaryForm_pair_independent (D : VertexProjectionChart P a)
    (hP : P.IsFullDim) (R : ExtraProjectionPlane P a)
    (G : OrdinaryProjectionPlane P a) :
    LinearIndependent ℝ ![D.extraForm hP R, D.ordinaryForm (chosenFacetForm P G.val)] := by
  let F := extraContainingFacet P hP a R
  have hRF := (extraContainingFacet_spec P hP a R).1
  have haF := (extraContainingFacet_spec P hP a R).2
  obtain ⟨x, hxR, hxG⟩ := Set.not_subset.mp (R.property.2 G)
  obtain ⟨y, hyF, hyR⟩ := D.exists_facet_point_outside_polygon hP F R.val
  have hxF := hRF hxR
  have hxP := face_subset_toSet P F.property.1 hxF
  have hyP := face_subset_toSet P F.property.1 hyF
  have hxa : x ≠ a.val := fun heq => haF (heq ▸ hxF)
  have hya : y ≠ a.val := fun heq => haF (heq ▸ hyF)
  have hgx : 0 < chosenFacetForm P G.val x := by
    apply lt_of_le_of_ne ((chosenFacetForm_supports P G.val).1 x hxP)
    intro hz
    exact hxG (((chosenFacetForm_supports P G.val).mem_iff x).mpr ⟨hxP, hz.symm⟩)
  have hry : 0 < projectedPolygonSupport P R.val y := by
    apply lt_of_le_of_ne ((projectedPolygonSupport_spec P R.val).1 y hyP)
    intro hz
    exact hyR (((projectedPolygonSupport_spec P R.val).mem_iff y).mpr ⟨hyP, hz.symm⟩)
  apply extra_ordinaryProjectionForms_independent
    (D.transportForm (chosenFacetForm P F))
    (D.transportForm (projectedPolygonSupport P R.val))
    (D.transportForm (chosenFacetForm P G.val))
    (D.support_at_apex_ne_zero F haF)
    (by simpa using (chosenFacetForm_supports P G.val).eq_zero G.property)
    (D.affine x) (D.affine y) (D.positive x hxP hxa) (D.positive y hyP hya)
  · simpa using (chosenFacetForm_supports P F).eq_zero hxF
  · simpa using (chosenFacetForm_supports P F).eq_zero hyF
  · simpa using (projectedPolygonSupport_spec P R.val).eq_zero hxR
  · simpa using hgx
  · simpa using hry

def traceForm (D : VertexProjectionChart P a)
    (F : FacetType P) (B : ActualProjectionPlane P a) : E 3 →ᵃ[ℝ] ℝ :=
  projectedFacetPlane (D.transportForm (chosenFacetForm P F))
    (D.transportForm (projectionCarrierSupport B))

theorem traceForm_eval (D : VertexProjectionChart P a)
    (F : FacetType P) (haF : a.val ∉ F.val.val)
    (B : ActualProjectionPlane P a) (x : E 4) (hxF : x ∈ F.val.val) :
    D.traceForm F B (centralProjection (D.affine x)) =
      (D.affine x).2⁻¹ * projectionCarrierSupport B x := by
  have hxP := face_subset_toSet P F.property.1 hxF
  have hxa : x ≠ a.val := fun heq => haF (heq ▸ hxF)
  unfold traceForm
  rw [projectedFacetPlane_eval _ _ (D.support_at_apex_ne_zero F haF)
    _ (D.positive x hxP hxa).ne' (by
      rw [D.transportForm_affine]
      exact (chosenFacetForm_supports P F).eq_zero hxF), D.transportForm_affine]

theorem traceForm_positive_outside (D : VertexProjectionChart P a)
    (F : FacetType P) (haF : a.val ∉ F.val.val)
    (B : ActualProjectionPlane P a) (x : E 4) (hxF : x ∈ F.val.val)
    (hxB : x ∉ projectionPlaneCarrier B) :
    0 < D.traceForm F B (centralProjection (D.affine x)) := by
  have hxP := face_subset_toSet P F.property.1 hxF
  have hxa : x ≠ a.val := fun heq => haF (heq ▸ hxF)
  have hpos : 0 < projectionCarrierSupport B x := by
    apply lt_of_le_of_ne ((projectionCarrierSupport_spec B).1 x hxP)
    intro hz
    exact hxB (((projectionCarrierSupport_spec B).mem_iff x).mpr ⟨hxP, hz.symm⟩)
  rw [D.traceForm_eval F haF B x hxF]
  exact mul_pos (inv_pos.mpr (D.positive x hxP hxa)) hpos

theorem traceForm_ne_zero (D : VertexProjectionChart P a) (hP : P.IsFullDim)
    (F : FacetType P) (haF : a.val ∉ F.val.val)
    (B : ActualProjectionPlane P a) (R : Face P 2)
    (hR : ProjectedFacetTrace B F R) : D.traceForm F B ≠ 0 := by
  obtain ⟨x, hxF, hxR⟩ := D.exists_facet_point_outside_polygon hP F R
  have hxB : x ∉ projectionPlaneCarrier B := fun hx => hxR (hR.symm ▸ ⟨hxF, hx⟩)
  have hp := D.traceForm_positive_outside F haF B x hxF hxB
  intro hz
  rw [hz] at hp
  exact (lt_irrefl 0) hp

/-- The canonical extra plane and any actual supporting description in a
common avoiding facet have the same one-dimensional space of forms. -/
theorem planeForm_eq_smul_traceForm (D : VertexProjectionChart P a) (hP : P.IsFullDim)
    (F : FacetType P) (haF : a.val ∉ F.val.val)
    (B : ActualProjectionPlane P a) (R : Face P 2)
    (hR : ProjectedFacetTrace B F R) :
    ∃ c : ℝ, c ≠ 0 ∧ D.planeForm hP B = c • D.traceForm F B := by
  have haR : a.val ∉ R.val.carrier := fun ha => haF ((hR ▸ ha).1)
  obtain ⟨v, _, hmem, hli⟩ := D.exists_projected_polygon_triangle hP R haR
  apply forms_proportional_of_three_independent_zeros (fun i => D.projectedPoint (v i))
    hli (D.planeForm hP B) (D.traceForm F B)
    (D.planeForm_ne_zero hP B) (D.traceForm_ne_zero hP F haF B R hR)
  · intro i
    exact D.planeForm_zero_of_incident hP (v i) B ((hR ▸ hmem i).2)
  · intro i
    change D.traceForm F B (centralProjection (D.affine (v i).val.val)) = 0
    rw [D.traceForm_eval F haF B _ ((hR ▸ hmem i).1),
      (projectionCarrierSupport_spec B).eq_zero ((hR ▸ hmem i).2), mul_zero]

theorem distinct_traces_strict_witness
    (F : FacetType P) (B C : ActualProjectionPlane P a)
    (R S : Face P 2) (hR : ProjectedFacetTrace B F R)
    (hS : ProjectedFacetTrace C F S) (hne : R ≠ S) :
    ∃ x ∈ R.val.carrier, 0 < projectionCarrierSupport C x := by
  have hnot : ¬ R.val.carrier ⊆ S.val.carrier := by
    intro hsub
    apply hne
    apply Subtype.ext
    apply PolytopeFace.ext
    exact face_eq_of_subset_equal_dimension P R.val.isFace S.val.isFace hsub
      (R.property.trans S.property.symm)
  obtain ⟨x, hxR, hxS⟩ := Set.not_subset.mp hnot
  have hxF := (hR ▸ hxR).1
  have hxP := face_subset_toSet P F.property.1 hxF
  refine ⟨x, hxR, lt_of_le_of_ne ((projectionCarrierSupport_spec C).1 x hxP) ?_⟩
  intro hz
  have hxC := ((projectionCarrierSupport_spec C).mem_iff x).mpr ⟨hxP, hz.symm⟩
  exact hxS (hS.symm ▸ ⟨hxF, hxC⟩)

theorem commonFacet_planeForms_three_independent (D : VertexProjectionChart P a)
    (hP : P.IsFullDim) (F : FacetType P) (haF : a.val ∉ F.val.val)
    (B : Fin 3 → ActualProjectionPlane P a) (R : Fin 3 → Face P 2)
    (hR : ∀ i, ProjectedFacetTrace (B i) F (R i)) (hinj : Function.Injective R) :
    LinearIndependent ℝ (fun i => D.planeForm hP (B i)) := by
  apply independent_forms_of_proportional _ (fun i => D.traceForm F (B i))
  · apply three_projectedFacetPlanes_independent
      (D.transportForm (chosenFacetForm P F)) (D.support_at_apex_ne_zero F haF)
      (fun i => D.transportForm (projectionCarrierSupport (B i)))
      (fun i => D.affine '' (R i).val.carrier)
    · intro i
      exact Convex.affine_image D.affine.toAffineMap
        ((R i).val.isFace.1.convex (convex_convexHull ℝ _))
    · intro i
      exact (R i).val.isFace.2.image D.affine
    · rintro i _ ⟨x, hx, rfl⟩
      simpa using (chosenFacetForm_supports P F).eq_zero ((hR i ▸ hx).1)
    · rintro i _ ⟨x, hx, rfl⟩
      have hxF := (hR i ▸ hx).1
      exact D.positive x (face_subset_toSet P F.property.1 hxF)
        (fun h => haF (h ▸ hxF))
    · rintro i _ ⟨x, hx, rfl⟩
      simpa using (projectionCarrierSupport_spec (B i)).eq_zero ((hR i ▸ hx).2)
    · rintro i j _ ⟨x, hx, rfl⟩
      simpa using (projectionCarrierSupport_spec (B j)).1 x
        (face_subset_toSet P (R i).val.isFace hx)
    · intro i j hij
      obtain ⟨x, hx, hpos⟩ := distinct_traces_strict_witness F (B i) (B j)
        (R i) (R j) (hR i) (hR j) (fun h => hij (hinj h))
      exact ⟨D.affine x, ⟨x, hx, rfl⟩, by simpa using hpos⟩
  · intro i
    exact D.planeForm_eq_smul_traceForm hP F haF (B i) (R i) (hR i)

theorem commonFacet_planeForm_pair_independent (D : VertexProjectionChart P a)
    (hP : P.IsFullDim) (F : FacetType P) (haF : a.val ∉ F.val.val)
    (B C : ActualProjectionPlane P a) (R S : Face P 2)
    (hR : ProjectedFacetTrace B F R) (hS : ProjectedFacetTrace C F S)
    (hne : R ≠ S) : LinearIndependent ℝ ![D.planeForm hP B, D.planeForm hP C] := by
  have htrace : LinearIndependent ℝ ![D.traceForm F B, D.traceForm F C] := by
    obtain ⟨x, hxR, hxC⟩ := distinct_traces_strict_witness F B C R S hR hS hne
    obtain ⟨y, hyS, hyB⟩ := distinct_traces_strict_witness F C B S R hS hR hne.symm
    have hxF := (hR ▸ hxR).1
    have hyF := (hS ▸ hyS).1
    have htx := D.positive x (face_subset_toSet P F.property.1 hxF)
      (fun h => haF (h ▸ hxF))
    have hty := D.positive y (face_subset_toSet P F.property.1 hyF)
      (fun h => haF (h ▸ hyF))
    apply two_affineForms_independent_of_separating_evaluations
      (D.traceForm F B) (D.traceForm F C)
      (centralProjection (D.affine x)) (centralProjection (D.affine y))
    · rw [D.traceForm_eval F haF B x hxF,
        (projectionCarrierSupport_spec B).eq_zero ((hR ▸ hxR).2), mul_zero]
    · rw [D.traceForm_eval F haF C x hxF]
      exact (mul_pos (inv_pos.mpr htx) hxC).ne'
    · rw [D.traceForm_eval F haF B y hyF]
      exact (mul_pos (inv_pos.mpr hty) hyB).ne'
  apply independent_forms_of_proportional _ ![D.traceForm F B, D.traceForm F C] htrace
  intro i
  fin_cases i
  · exact D.planeForm_eq_smul_traceForm hP F haF B R hR
  · exact D.planeForm_eq_smul_traceForm hP F haF C S hS

theorem commonFacet_small_planeForms_independent {I : Type*} [Fintype I]
    (D : VertexProjectionChart P a) (hP : P.IsFullDim)
    (F : FacetType P) (haF : a.val ∉ F.val.val)
    (B : I → ActualProjectionPlane P a) (R : I → Face P 2)
    (hR : ∀ i, ProjectedFacetTrace (B i) F (R i))
    (hinj : Function.Injective R) (hI : Fintype.card I ≤ 3) :
    LinearIndependent ℝ (fun i => D.planeForm hP (B i)) := by
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have hfin : LinearIndependent ℝ (fun i => D.planeForm hP (B (e i))) := by
    apply linearIndependent_fin_of_le_three _ hI
    · intro i
      exact D.planeForm_ne_zero hP (B (e i))
    · intro i j hij
      exact D.commonFacet_planeForm_pair_independent hP F haF
        (B (e i)) (B (e j)) (R (e i)) (R (e j)) (hR _) (hR _)
        (fun h => hij (e.injective (hinj h)))
    · intro i j k hij hik hjk
      let b : Fin 3 → ActualProjectionPlane P a := ![B (e i), B (e j), B (e k)]
      let r : Fin 3 → Face P 2 := ![R (e i), R (e j), R (e k)]
      have hr : Function.Injective r := by
        intro u v huv
        have hei := fun {u v} (h : R (e u) = R (e v)) => e.injective (hinj h)
        fin_cases u <;> fin_cases v <;> simp_all [r]
        all_goals have h := hei huv; simp_all
      have hbr : ∀ t, ProjectedFacetTrace (b t) F (r t) := by
        intro t
        fin_cases t <;> exact hR _
      convert D.commonFacet_planeForms_three_independent hP F haF b r hbr hr using 1
      ext t
      fin_cases t <;> rfl
  have h := hfin.comp e.symm e.symm.injective
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using h

/-- Rule (iv), after geometric certification of the first pair. -/
theorem planeForms_three_of_common_point (D : VertexProjectionChart P a)
    (hP : P.IsFullDim) (B C : ActualProjectionPlane P a)
    (F : OrdinaryProjectionPlane P a) (w : ProjectionPoint P a)
    (hpair : LinearIndependent ℝ ![D.planeForm hP B, D.planeForm hP C])
    (hwB : actualProjectionIncidence w B) (hwC : actualProjectionIncidence w C)
    (hwF : ¬ actualProjectionIncidence w (Sum.inl F)) :
    LinearIndependent ℝ
      ![D.planeForm hP B, D.planeForm hP C, D.planeForm hP (Sum.inl F)] := by
  apply three_vectors_independent_of_pair_and_functional
    (D.planeForm hP B) (D.planeForm hP C) (D.planeForm hP (Sum.inl F))
    (affineFormEvaluation (D.projectedPoint w)) hpair
  · exact D.planeForm_zero_of_incident hP w B hwB
  · exact D.planeForm_zero_of_incident hP w C hwC
  · exact (D.ordinaryForm_positive_outside F w.val.val
      (vertex_mem_body P w.val.property) hwF).ne'

end VertexProjectionChart
end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart5

section BundlePart6
/- Source: Papers/ProjectionCertificateLinearAlgebra.lean -/





@[expose] public section
noncomputable section
open Matrix Set Filter Topology
open scoped BigOperators

namespace Papers.ProjectionCertificateLinearAlgebra

open Papers.RationalOrthogonalityPeeling

/-- An explicit insertion order supplies the induced-subsystem hypothesis
of the rational orthogonality theorem. Only the original vectors occur
in the independent-neighbour conditions. -/
theorem rational_density_of_order {I : Type*} [Fintype I] [DecidableEq I] {d : ℕ}
    (R : I → I → Prop) [DecidableRel R]
    (hsymm : ∀i j,R i j → R j i) (hirr : ∀i,¬R i i)
    (p : I → Fin d → ℝ) (hp : ∀i j,R i j → p i ⬝ᵥ p j=0)
    (priority : I → ℕ) (hinj : Function.Injective priority)
    (hLI : ∀i,LinearIndependent ℝ
      (fun j : {j // priority i<priority j ∧ R i j} => p j.val)) :
    p∈closure {q | RationalFamily q ∧ ∀i j,R i j → q i ⬝ᵥ q j=0} := by
  apply rational_orthogonality_density R hsymm hirr p hp
  intro S hS
  obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image S priority hS
  refine ⟨i,hi,?_⟩
  let f : {j // j∈S ∧ R i j} → {j // priority i<priority j ∧ R i j} :=
    fun j => ⟨j.val,⟨lt_of_le_of_ne (hmin j.val j.property.1)
      (fun heq => hirr i (by
        have hij : i = j.val := hinj heq
        simpa only [← hij] using j.property.2)),j.property.2⟩⟩
  have hf : Function.Injective f := by
    intro j k heq
    apply Subtype.ext
    exact congrArg (fun z : {j // priority i < priority j ∧ R i j} => z.val) heq
  exact (hLI i).comp f hf

/-- Leaf pivots give full row rank. A possible nonzero support does not
suffice: the chosen pivot entry itself must be proved nonzero. -/
theorem pivot_order_independent {c n : ℕ} (C : Matrix (Fin c) (Fin n) ℝ)
    (pivot : Fin c → Fin n) (hdiag : ∀i,C i (pivot i)≠0)
    (hlater : ∀i j,i<j → C j (pivot i)=0) :
    LinearIndependent ℝ C.row := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha
  have hzero : ∀k:ℕ,∀i:Fin c,i.val=k → a i=0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hik
      have heq : (∑j:Fin c,a j*C j (pivot i))=a i*C i (pivot i) := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          rcases lt_or_gt_of_ne hji with hlt | hgt
          · have haj : a j=0 := ih j.val (by omega) j rfl
            rw [haj,zero_mul]
          · rw [hlater i j hgt,mul_zero]
        · simp
      have h := congrFun ha (pivot i)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        Matrix.row_apply] at h
      rw [heq] at h
      exact (mul_eq_zero.mp h).resolve_right (hdiag i)
  exact fun i => hzero i.val i rfl

end Papers.ProjectionCertificateLinearAlgebra

end
end
end BundlePart6

section BundlePart7
/- Source: Papers/ActualProjectionCertificates.lean -/






@[expose] public section

/-!
# Actual geometric deletion certificates imply projected rational density

The certificate constructors use only actual face membership, face
intersection, distinctness, and finite cardinalities. Linear independence
is proved from these constructors. The resulting density theorem preserves
every required point--plane incidence with a nonzero plane vector.

This is the geometric content of Lemma 6 of the paper. 
-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix Filter Topology
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeIncidenceConfiguration Papers.BipartiteOrthogonalityDensity
open Papers.RationalOrthogonalityPeeling Papers.ProjectionCertificateLinearAlgebra

variable {P : ConvexPolytope 4} {a : VertexType P}

/-- Geometric certificates for the point equations imposed when a plane
is reinserted. The two facial cases are exactly the four-point witness. -/
inductive ProjectionPointRule (S : Finset (ProjectionPoint P a)) : Prop
  | atMostTwo (h : S.card ≤ 2)
  | avoidingPolygon (h : S.card ≤ 3) (R : Face P 2)
      (ha : a.val ∉ R.val.carrier)
      (hmem : ∀ v ∈ S, v.val.val ∈ R.val.carrier)
  | facialWitness (h : S.card ≤ 3) (R : Face P 2)
      (ha : a.val ∈ R.val.carrier) (v : ProjectionPoint P a) (hv : v ∈ S)
      (hout : v.val.val ∉ R.val.carrier)
      (hin : ∀ w ∈ S, w ≠ v → w.val.val ∈ R.val.carrier)

/-- Distinctness of a pair of projected planes is certified geometrically,
without assuming their forms are independent. -/
inductive ProjectionPlanePairRule :
    ActualProjectionPlane P a → ActualProjectionPlane P a → Prop
  | ordinary (F G : OrdinaryProjectionPlane P a) (hne : F ≠ G) :
      ProjectionPlanePairRule (Sum.inl F) (Sum.inl G)
  | extraOrdinary (R : ExtraProjectionPlane P a) (F : OrdinaryProjectionPlane P a) :
      ProjectionPlanePairRule (Sum.inr R) (Sum.inl F)
  | ordinaryExtra (F : OrdinaryProjectionPlane P a) (R : ExtraProjectionPlane P a) :
      ProjectionPlanePairRule (Sum.inl F) (Sum.inr R)
  | commonFacet (F : FacetType P) (ha : a.val ∉ F.val.val)
      (B C : ActualProjectionPlane P a) (R S : Face P 2)
      (hR : ProjectedFacetTrace B F R) (hS : ProjectedFacetTrace C F S) (hne : R ≠ S) :
      ProjectionPlanePairRule B C

/-- Geometric certificates for the plane equations imposed when a point
is reinserted. The common-point constructor is rule (iv). -/
inductive ProjectionPlaneRule (S : Finset (ActualProjectionPlane P a)) : Prop
  | atMostOne (h : S.card ≤ 1)
  | atMostTwo (h : S.card ≤ 2)
      (hpairs : ∀ B ∈ S, ∀ C ∈ S, B ≠ C → ProjectionPlanePairRule B C)
  | ordinary (h : S.card ≤ 3)
      (hordinary : ∀ B ∈ S, ∃ F : OrdinaryProjectionPlane P a, B = Sum.inl F)
  | commonFacet (h : S.card ≤ 3) (F : FacetType P) (ha : a.val ∉ F.val.val)
      (R : S → Face P 2) (hinj : Function.Injective R)
      (htrace : ∀ B : S, ProjectedFacetTrace B.val F (R B))
  | commonPoint (B C : ActualProjectionPlane P a) (F : OrdinaryProjectionPlane P a)
      (w : ProjectionPoint P a) (hpair : ProjectionPlanePairRule B C)
      (hwB : actualProjectionIncidence w B) (hwC : actualProjectionIncidence w C)
      (hwF : ¬ actualProjectionIncidence w (Sum.inl F))
      (hS : S ⊆ {B, C, Sum.inl F})

theorem independent_pair_reverse {V : Type*} [AddCommGroup V] [Module ℝ V]
    (x y : V) (h : LinearIndependent ℝ ![x, y]) :
    LinearIndependent ℝ ![y, x] := by
  have hh := h.comp (Equiv.swap (0 : Fin 2) 1) (Equiv.swap _ _).injective
  convert hh using 1
  funext i
  fin_cases i <;> simp [Function.comp_def]

theorem independent_on_subset_range {J K V : Type*} [DecidableEq K]
    [AddCommGroup V] [Module ℝ V] (b : J → K) (f : K → V)
    (h : LinearIndependent ℝ (fun j => f (b j))) (S : Finset K)
    (hS : ∀ k ∈ S, k ∈ Set.range b) :
    LinearIndependent ℝ (fun k : S => f k.val) := by
  have he (k : S) : ∃ j, b j = k.val := hS k.val k.property
  choose c hc using he
  have hinj : Function.Injective c := by
    intro k l hkl
    apply Subtype.ext
    rw [← hc k, ← hc l, hkl]
  have hh := h.comp c hinj
  simpa only [Function.comp_def, hc] using hh

theorem linearIndependent_fin_of_le_two
    {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (p : Fin n → V) (hn : n ≤ 2) (h1 : ∀ i, p i ≠ 0)
    (h2 : ∀ i j, i ≠ j → LinearIndependent ℝ ![p i, p j]) :
    LinearIndependent ℝ p := by
  interval_cases n
  · exact linearIndependent_empty_type
  · exact linearIndependent_unique_iff.mpr (h1 _)
  · convert h2 0 1 (by decide) using 1
    funext i
    fin_cases i <;> rfl

namespace VertexProjectionChart

theorem pointRule_independent (D : VertexProjectionChart P a) (hP : P.IsFullDim)
    (S : Finset (ProjectionPoint P a)) (hS : ProjectionPointRule S) :
    LinearIndependent ℝ (fun v : S => D.projectedVector v.val) := by
  cases hS with
  | atMostTwo h =>
    exact D.two_projected_points_independent hP (fun v : S => v.val)
      Subtype.val_injective (by simpa using h)
  | avoidingPolygon h R ha hmem =>
    exact D.projected_points_on_avoiding_face_independent hP (fun v : S => v.val)
      Subtype.val_injective (by simpa using h) ⟨R.val.carrier, R.val.isFace⟩ ha
      (fun v => hmem v.val v.property)
  | facialWitness h R ha v hv hout hin =>
    exact D.projected_points_of_facial_witness_independent hP (fun w : S => w.val)
      Subtype.val_injective (by simpa using h) ⟨v, hv⟩ ⟨R.val.carrier, R.val.isFace⟩
      ha hout (fun w hw => hin w.val w.property (fun h => hw (Subtype.ext h)))

theorem planePairRule_independent (D : VertexProjectionChart P a) (hP : P.IsFullDim)
    (B C : ActualProjectionPlane P a) (h : ProjectionPlanePairRule B C) :
    LinearIndependent ℝ ![D.planeForm hP B, D.planeForm hP C] := by
  cases h with
  | ordinary F G hne => exact D.ordinaryForm_pair_independent F G hne
  | extraOrdinary R F => exact D.extra_ordinaryForm_pair_independent hP R F
  | ordinaryExtra F R =>
    exact independent_pair_reverse _ _ (D.extra_ordinaryForm_pair_independent hP R F)
  | commonFacet F ha B C R S hR hS hne =>
    exact D.commonFacet_planeForm_pair_independent hP F ha B C R S hR hS hne

theorem planeRule_forms_independent (D : VertexProjectionChart P a) (hP : P.IsFullDim)
    (S : Finset (ActualProjectionPlane P a)) (hS : ProjectionPlaneRule S) :
    LinearIndependent ℝ (fun B : S => D.planeForm hP B.val) := by
  cases hS with
  | atMostOne h =>
    haveI : Subsingleton S := Fintype.card_le_one_iff_subsingleton.mp (by simpa using h)
    exact (linearIndependent_subsingleton_index_iff _).mpr
      (fun B => D.planeForm_ne_zero hP B.val)
  | atMostTwo h hpairs =>
    let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
    have hh : LinearIndependent ℝ (fun i => D.planeForm hP (e i).val) := by
      apply linearIndependent_fin_of_le_two _ (by simpa using h)
      · intro i
        exact D.planeForm_ne_zero hP (e i).val
      · intro i j hij
        exact D.planePairRule_independent hP _ _
          (hpairs (e i).val (e i).property (e j).val (e j).property
            (fun h => hij (e.injective (Subtype.ext h))))
    have hh' := hh.comp e.symm e.symm.injective
    simpa only [Function.comp_def, Equiv.apply_symm_apply] using hh'
  | ordinary h hord =>
    have hchoose (B : S) : ∃ F : OrdinaryProjectionPlane P a, B.val = Sum.inl F :=
      hord B.val B.property
    choose F hF using hchoose
    have hinj : Function.Injective F := by
      intro B C hBC
      apply Subtype.ext
      rw [hF B, hF C, hBC]
    have hh := D.small_ordinaryForms_independent F hinj (by simpa using h)
    convert hh using 1
    funext B
    rw [hF B]
    rfl
  | commonFacet h F ha R hinj htrace =>
    exact D.commonFacet_small_planeForms_independent hP F ha (fun B : S => B.val)
      R htrace hinj (by simpa using h)
  | commonPoint B C F w hpair hwB hwC hwF hsub =>
    have hh := D.planeForms_three_of_common_point hP B C F w
      (D.planePairRule_independent hP B C hpair) hwB hwC hwF
    have hh' : LinearIndependent ℝ (fun j : Fin 3 =>
        D.planeForm hP (![B, C, Sum.inl F] j)) := by
      convert hh using 1
      funext j
      fin_cases j <;> rfl
    apply independent_on_subset_range ![B, C, Sum.inl F] (D.planeForm hP) hh' S
    intro G hG
    have hG' : G = B ∨ G = C ∨ G = Sum.inl F := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hsub hG
    rcases hG' with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

theorem planeRule_vectors_independent (D : VertexProjectionChart P a) (hP : P.IsFullDim)
    (S : Finset (ActualProjectionPlane P a)) (hS : ProjectionPlaneRule S) :
    LinearIndependent ℝ (fun B : S => D.planeVector hP B.val) :=
  (D.planeRule_forms_independent hP S hS).map' coefficientVectorLinear
    (LinearMap.ker_eq_bot.mpr coefficientVector_injective)

end VertexProjectionChart

abbrev ProjectionNode (P : ConvexPolytope 4) (a : VertexType P) :=
  ProjectionPoint P a ⊕ ActualProjectionPlane P a

def retainedProjectionPoints (priority : ProjectionNode P a → ℕ)
    (B : ActualProjectionPlane P a) : Finset (ProjectionPoint P a) :=
  Finset.univ.filter fun v => priority (Sum.inr B) < priority (Sum.inl v) ∧
    actualProjectionIncidence v B

def retainedProjectionPlanes (priority : ProjectionNode P a → ℕ)
    (v : ProjectionPoint P a) : Finset (ActualProjectionPlane P a) :=
  Finset.univ.filter fun B => priority (Sum.inl v) < priority (Sum.inr B) ∧
    actualProjectionIncidence v B

structure ActualProjectionDeletionCertificate (P : ConvexPolytope 4) (a : VertexType P) where
  priority : ProjectionNode P a → ℕ
  injective : Function.Injective priority
  plane_rule : ∀ B, ProjectionPointRule (retainedProjectionPoints priority B)
  point_rule : ∀ v, ProjectionPlaneRule (retainedProjectionPlanes priority v)

def higherPointNeighbors (priority : ProjectionNode P a → ℕ) (v : ProjectionPoint P a) :
    {j : ProjectionNode P a // priority (Sum.inl v) < priority j ∧
      incidenceRelation actualProjectionIncidence (Sum.inl v) j} ≃
        retainedProjectionPlanes priority v where
  toFun j := match j with
    | ⟨Sum.inr B, hp, hB⟩ => ⟨B, by simp only [retainedProjectionPlanes,
        Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hp, hB⟩⟩
    | ⟨Sum.inl _, _, h⟩ => False.elim h
  invFun B := ⟨Sum.inr B.val, by
    simpa only [retainedProjectionPlanes, Finset.mem_filter, Finset.mem_univ, true_and,
      incidenceRelation]
      using B.property⟩
  left_inv := by
    rintro ⟨j | j, hp, hR⟩
    · exact False.elim hR
    · rfl
  right_inv _ := rfl

def higherPlaneNeighbors (priority : ProjectionNode P a → ℕ) (B : ActualProjectionPlane P a) :
    {j : ProjectionNode P a // priority (Sum.inr B) < priority j ∧
      incidenceRelation actualProjectionIncidence (Sum.inr B) j} ≃
        retainedProjectionPoints priority B where
  toFun j := match j with
    | ⟨Sum.inl v, hp, hv⟩ => ⟨v, by simp only [retainedProjectionPoints,
        Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hp, hv⟩⟩
    | ⟨Sum.inr _, _, h⟩ => False.elim h
  invFun v := ⟨Sum.inl v.val, by
    simpa only [retainedProjectionPoints, Finset.mem_filter, Finset.mem_univ, true_and,
      incidenceRelation]
      using v.property⟩
  left_inv := by
    rintro ⟨j | j, hp, hR⟩
    · rfl
    · exact False.elim hR
  right_inv _ := rfl

namespace VertexProjectionChart

def nodeVectors (D : VertexProjectionChart P a) (hP : P.IsFullDim) :
    ProjectionNode P a → Fin 4 → ℝ := Sum.elim D.projectedVector (D.planeVector hP)

theorem nodeVectors_rational_incidence_density (D : VertexProjectionChart P a)
    (hP : P.IsFullDim) (C : ActualProjectionDeletionCertificate P a) :
    D.nodeVectors hP ∈ closure {z : ProjectionNode P a → Fin 4 → ℝ |
      RationalFamily z ∧ ∀ v B, actualProjectionIncidence v B →
        z (Sum.inl v) ⬝ᵥ z (Sum.inr B) = 0} := by
  have hsymm : ∀ i j : ProjectionNode P a,
      incidenceRelation actualProjectionIncidence i j →
        incidenceRelation actualProjectionIncidence j i := by
    intro i j
    cases i <;> cases j <;> simp only [incidenceRelation, imp_self]
  have hirr : ∀ i : ProjectionNode P a, ¬ incidenceRelation actualProjectionIncidence i i := by
    intro i
    cases i <;> simp only [incidenceRelation, not_false_eq_true]
  have hz : ∀ i j : ProjectionNode P a, incidenceRelation actualProjectionIncidence i j →
      D.nodeVectors hP i ⬝ᵥ D.nodeVectors hP j = 0 := by
    intro i j hij
    cases i with
    | inl v =>
      cases j with
      | inl w => exact False.elim hij
      | inr B =>
        simpa only [nodeVectors, Sum.elim_inl, Sum.elim_inr, dotProduct_comm]
          using D.planeVector_dot_projectedVector hP v B hij
    | inr B =>
      cases j with
      | inl v => exact D.planeVector_dot_projectedVector hP v B hij
      | inr C => exact False.elim hij
  have hLI : ∀ i : ProjectionNode P a, LinearIndependent ℝ
      (fun j : {j // C.priority i < C.priority j ∧
        incidenceRelation actualProjectionIncidence i j} => D.nodeVectors hP j.val) := by
    intro i
    cases i with
    | inl v =>
      let e := higherPointNeighbors C.priority v
      have hh := (D.planeRule_vectors_independent hP _ (C.point_rule v)).comp e e.injective
      convert hh using 1
      funext j
      rcases j with ⟨j | j, hp, hR⟩
      · exact False.elim hR
      · rfl
    | inr B =>
      let e := higherPlaneNeighbors C.priority B
      have hh := (D.pointRule_independent hP _ (C.plane_rule B)).comp e e.injective
      convert hh using 1
      funext j
      rcases j with ⟨j | j, hp, hR⟩
      · rfl
      · exact False.elim hR
  have h := rational_density_of_order (incidenceRelation actualProjectionIncidence)
    hsymm hirr (D.nodeVectors hP) hz C.priority C.injective hLI
  apply closure_mono ?_ h
  intro z hz
  exact ⟨hz.1, fun v B hvB => hz.2 (Sum.inl v) (Sum.inr B) hvB⟩

end VertexProjectionChart

/-- Every required actual plane has a nonzero annihilator. There is no
unverified realization-space chart in this predicate. -/
def PreservesProjectedIncidences {n : ℕ} (e : Fin n ≃ ProjectionPoint P a)
    (q : Fin n → Fin 4 → ℝ) : Prop :=
  ∀ B : ActualProjectionPlane P a, ∃ b : Fin 4 → ℝ, b ≠ 0 ∧
    ∀ i, actualProjectionIncidence (e i) B → b ⬝ᵥ q i = 0

theorem projected_configuration_rational_density {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (a : VertexType P)
    (D : VertexProjectionChart P a) (e : Fin n ≃ ProjectionPoint P a)
    (C : ActualProjectionDeletionCertificate P a) :
    (fun i => D.projectedVector (e i)) ∈ closure
      {q : Fin n → Fin 4 → ℝ |
        Papers.RationalKernelCharts.RationalCoordinates q ∧ PreservesProjectedIncidences e q} := by
  let p := D.nodeVectors hP
  have hnonzero : ∀ᶠ z in 𝓝 p,
      ∀ B : ActualProjectionPlane P a, z (Sum.inr B) ≠ 0 := by
    apply eventually_all.mpr
    intro B
    exact (continuous_apply (Sum.inr B)).continuousAt.eventually_ne (D.planeVector_ne_zero hP B)
  have hcl := mem_closure_inter_of_eventually
    (D.nodeVectors_rational_incidence_density hP C) hnonzero
  let project := fun z : ProjectionNode P a → Fin 4 → ℝ => fun i => z (Sum.inl (e i))
  have hcont : Continuous project := continuous_pi fun i => continuous_apply (Sum.inl (e i))
  have himage := mem_closure_image hcont.continuousAt hcl
  apply closure_mono (s := project '' _) ?_ himage
  rintro _ ⟨z, ⟨⟨hzrat, hzinc⟩, hzne⟩, rfl⟩
  refine ⟨fun i j => hzrat (Sum.inl (e i)) j, ?_⟩
  intro B
  exact ⟨z (Sum.inr B), hzne B, fun i hi => by
    change z (Sum.inr B) ⬝ᵥ z (Sum.inl (e i)) = 0
    rw [dotProduct_comm]
    exact hzinc (e i) B hi⟩

theorem projected_incidence_rank_upper {n : ℕ} (e : Fin n ≃ ProjectionPoint P a)
    (q : Fin n → Fin 4 → ℝ) (hq : PreservesProjectedIncidences e q)
    (B : ActualProjectionPlane P a) (S : Finset (Fin n))
    (hS : ∀ i ∈ S, actualProjectionIncidence (e i) B) : subsetRank q S ≤ 3 := by
  obtain ⟨b, hb, hzero⟩ := hq B
  have h := subsetRank_add_one_le_of_annihilator q S b hb (fun i hi => hzero i (hS i hi))
  omega

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart7

section BundlePart8
/- Source: Papers/ProjectionFundamentalRelations.lean -/







@[expose] public section

/-!
# Continuous rational fundamental relations in a projected facet

An independent ordered frame gives coordinates by its nonsingular Gram
matrix.  Every remaining vertex then gives an actual linear relation,
supported on that vertex and the frame.  These relations span the complete
relation space.  No generic-position premise is used: a nonzero coefficient
is obtained precisely when the corresponding replacement frame is independent.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Matrix Module Set Filter Topology
open scoped Classical BigOperators
open Papers.RationalKernelCharts

def projectedFrame {n r k : ℕ} (q : Fin n → Fin r → ℝ) (b : Fin k → Fin n) :
    Matrix (Fin k) (Fin r) ℝ := fun i => q (b i)

def fundamentalCoefficients {n r k : ℕ} (q : Fin n → Fin r → ℝ)
    (b : Fin k → Fin n) (v : Fin n) : Fin k → ℝ :=
  let B := projectedFrame q b
  (B * B.transpose)⁻¹.mulVec (B.mulVec (q v))

def fundamentalRow {n r k : ℕ} (q : Fin n → Fin r → ℝ)
    (b : Fin k → Fin n) (v : Fin n) : Fin n → ℝ :=
  Pi.single v 1 - ∑ i, fundamentalCoefficients q b v i • Pi.single (b i) 1

theorem projectedFrame_gram_isUnit {n r k : ℕ}
    (q : Fin n → Fin r → ℝ) (b : Fin k → Fin n)
    (hB : LinearIndependent ℝ (fun i => q (b i))) :
    IsUnit ((projectedFrame q b) * (projectedFrame q b).transpose).det := by
  have hs := transpose_spans_of_rowIndependent
    (A := projectedFrame q b) hB
  simpa only [Matrix.transpose_transpose] using gram_isUnit hs

theorem fundamentalCoefficients_reconstruct {n r k : ℕ}
    (q : Fin n → Fin r → ℝ) (b : Fin k → Fin n) (v : Fin n)
    (hB : LinearIndependent ℝ (fun i => q (b i)))
    (hv : q v ∈ Submodule.span ℝ (Set.range (fun i => q (b i)))) :
    ∑ i, fundamentalCoefficients q b v i • q (b i) = q v := by
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv
  let B := projectedFrame q b
  have hqa : B.transpose.mulVec a = q v := by
    ext j
    simpa [B, projectedFrame, Matrix.mulVec, dotProduct, mul_comm]
      using congrFun ha j
  have hcoeff : fundamentalCoefficients q b v = a := by
    change (B * B.transpose)⁻¹.mulVec (B.mulVec (q v)) = a
    rw [← hqa, Matrix.mulVec_mulVec a B B.transpose, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (projectedFrame_gram_isUnit q b hB), Matrix.one_mulVec]
  rw [hcoeff]
  exact ha

theorem fundamentalCoefficients_rational {n r k : ℕ}
    (q : Fin n → Fin r → ℝ) (b : Fin k → Fin n) (v : Fin n)
    (hq : RationalCoordinates q) :
    ∀ i, RatScalar (fundamentalCoefficients q b v i) := by
  have hB : RationalCoordinates (projectedFrame q b) := fun i j => hq (b i) j
  have hG := rationalCoordinates_inv
    (rationalCoordinates_mul hB (rationalCoordinates_transpose hB))
  intro i
  unfold fundamentalCoefficients Matrix.mulVec dotProduct
  exact RatScalar.finset_sum Finset.univ _ fun j _ =>
    (hG i j).mul (RatScalar.finset_sum Finset.univ _ fun a _ =>
      (hB j a).mul (hq v a))

theorem fundamentalCoefficients_continuousAt {n r k : ℕ}
    (q : Fin n → Fin r → ℝ) (b : Fin k → Fin n) (v : Fin n)
    (hB : LinearIndependent ℝ (fun i => q (b i))) :
    ContinuousAt (fun q' => fundamentalCoefficients q' b v) q := by
  have hframe : Continuous (fun q' : Fin n → Fin r → ℝ => projectedFrame q' b) :=
    continuous_pi fun i => continuous_apply (b i)
  have hgram := hframe.matrix_mul hframe.matrix_transpose
  have hinv : ContinuousAt
      (fun q' : Fin n → Fin r → ℝ =>
        (projectedFrame q' b * (projectedFrame q' b).transpose)⁻¹) q := by
    have hi : ContinuousAt (Inv.inv : Matrix (Fin k) (Fin k) ℝ → _)
        (projectedFrame q b * (projectedFrame q b).transpose) := continuousAt_matrix_inv
      (projectedFrame q b * (projectedFrame q b).transpose) (by
        simpa only [Ring.inverse_eq_inv'] using
          continuousAt_inv₀ (isUnit_iff_ne_zero.mp (projectedFrame_gram_isUnit q b hB)))
    exact hi.comp_of_eq (hgram.continuousAt (x := q)) rfl
  have hright := hframe.matrix_mulVec (continuous_apply v)
  have hmul : Continuous
      (fun z : Matrix (Fin k) (Fin k) ℝ × (Fin k → ℝ) => z.1.mulVec z.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  exact hmul.continuousAt.comp (hinv.prodMk hright.continuousAt)

theorem fundamentalRow_rational {n r k : ℕ}
    (q : Fin n → Fin r → ℝ) (b : Fin k → Fin n) (v : Fin n)
    (hq : RationalCoordinates q) : ∀ j, RatScalar (fundamentalRow q b v j) := by
  intro j
  have hs (w : Fin n) : RatScalar ((Pi.single w (1 : ℝ) : Fin n → ℝ) j) := by
    by_cases h : w = j
    · subst w; exact ⟨1, by simp⟩
    · exact ⟨0, by simp [Pi.single_apply, h, Ne.symm h]⟩
  simpa only [fundamentalRow, Pi.sub_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul] using
    (hs v).sub (RatScalar.finset_sum Finset.univ _ fun i _ =>
      (fundamentalCoefficients_rational q b v hq i).mul (hs (b i)))

theorem fundamentalRow_continuousAt {n r k : ℕ}
    (q : Fin n → Fin r → ℝ) (b : Fin k → Fin n) (v : Fin n)
    (hB : LinearIndependent ℝ (fun i => q (b i))) :
    ContinuousAt (fun q' => fundamentalRow q' b v) q := by
  have hf : Continuous (fun a : Fin k → ℝ =>
      Pi.single v (1 : ℝ) - ∑ i, a i • Pi.single (b i) 1) := by
    fun_prop
  exact hf.continuousAt.comp (fundamentalCoefficients_continuousAt q b v hB)

theorem fundamentalRow_outside_frame {n r k : ℕ}
    (q : Fin n → Fin r → ℝ) (b : Fin k → Fin n) (v w : Fin n)
    (hw : w ∉ Set.range b) :
    fundamentalRow q b v w = if w = v then 1 else 0 := by
  have hb : ∀ i, b i ≠ w := fun i hi => hw ⟨i, hi⟩
  simp [fundamentalRow, Pi.single_apply, hb, fun i => Ne.symm (hb i), eq_comm]

theorem fundamentalRow_pivot {n r k : ℕ}
    (q : Fin n → Fin r → ℝ) (b : Fin k → Fin n) (v : Fin n)
    (hv : v ∉ Set.range b) : fundamentalRow q b v v = 1 := by
  simp only [fundamentalRow_outside_frame q b v v hv, if_pos rfl, ite_true]

theorem fundamentalRow_frame_entry {n r k : ℕ}
    (q : Fin n → Fin r → ℝ) (b : Fin k → Fin n) (v : Fin n)
    (hb : Function.Injective b) (hv : v ∉ Set.range b) (t : Fin k) :
    fundamentalRow q b v (b t) = - fundamentalCoefficients q b v t := by
  have hvt : v ≠ b t := fun h => hv ⟨t, h.symm⟩
  simp [fundamentalRow, Pi.single_apply, hb.eq_iff, hvt, Ne.symm hvt, eq_comm]

theorem fundamentalRow_mem_globalRelationSpace {n r k : ℕ}
    (q : Fin n → Fin r → ℝ) (b : Fin k → Fin n) (v : Fin n)
    (S : Finset (Fin n)) (hB : LinearIndependent ℝ (fun i => q (b i)))
    (hbS : ∀ i, b i ∈ S) (hvS : v ∈ S)
    (hv : q v ∈ Submodule.span ℝ (Set.range (fun i => q (b i)))) :
    fundamentalRow q b v ∈ globalRelationSpace q S := by
  apply (mem_globalRelationSpace_iff q S _).mpr
  constructor
  · intro w hw
    have hb : w ∉ Set.range b := by
      rintro ⟨i, rfl⟩
      exact hw (hbS i)
    rw [fundamentalRow_outside_frame q b v w hb, if_neg]
    exact fun h => hw (h.symm ▸ hvS)
  · change (Matrix.mulVecLin (Matrix.of q).transpose) (fundamentalRow q b v) = 0
    simp only [fundamentalRow, map_sub, map_sum, map_smul,
      Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_transpose,
      Matrix.row_apply, Matrix.of_apply]
    exact sub_eq_zero.mpr (fundamentalCoefficients_reconstruct q b v hB hv).symm

theorem fundamentalCoefficients_ne_zero_of_replacement {n r k : ℕ}
    (q : Fin n → Fin r → ℝ) (b : Fin k → Fin n) (v : Fin n) (t : Fin k)
    (hB : LinearIndependent ℝ (fun i => q (b i)))
    (hv : q v ∈ Submodule.span ℝ (Set.range (fun i => q (b i))))
    (hreplace : LinearIndependent ℝ (fun i => q (Function.update b t v i))) :
    fundamentalCoefficients q b v t ≠ 0 := by
  intro ht
  let W := Submodule.span ℝ
    ((fun i => q (Function.update b t v i)) '' ({t}ᶜ : Set (Fin k)))
  have hsum : ∑ i, fundamentalCoefficients q b v i • q (b i) ∈ W := by
    apply Submodule.sum_mem
    intro i _
    by_cases hit : i = t
    · subst i; simp [ht]
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      exact ⟨i, by simpa using hit, by simp [Function.update_of_ne hit]⟩
  rw [fundamentalCoefficients_reconstruct q b v hB hv] at hsum
  have hn := hreplace.notMem_span_image
    (s := ({t}ᶜ : Set (Fin k))) (x := t) (by simp)
  apply hn
  simpa only [Function.update_self] using hsum

theorem relation_supported_on_independent_frame_eq_zero {n r k : ℕ}
    (q : Fin n → Fin r → ℝ) (b : Fin k → Fin n)
    (hB : LinearIndependent ℝ (fun i => q (b i)))
    (a : Fin n → ℝ) (ha : (Matrix.of q).transpose.mulVec a = 0)
    (hs : ∀ w, w ∉ Set.range b → a w = 0) : a = 0 := by
  have hb : Function.Injective b := fun i j hij => hB.injective (congrArg q hij)
  have hexp : a = ∑ i, a (b i) • Pi.single (b i) 1 := by
    ext w
    by_cases hw : w ∈ Set.range b
    · obtain ⟨i, rfl⟩ := hw
      simp [Pi.single_apply, hb.eq_iff, eq_comm]
    · have hbw : ∀ i, b i ≠ w := fun i hi => hw ⟨i, hi⟩
      simp [hs w hw, Pi.single_apply, hbw, fun i => Ne.symm (hbw i)]
  have hsum : ∑ i, a (b i) • q (b i) = 0 := by
    have hmap := congrArg (Matrix.mulVecLin (Matrix.of q).transpose) hexp
    change (Matrix.of q).transpose.mulVec a = _ at hmap
    rw [ha] at hmap
    simpa only [map_sum, map_smul, Matrix.mulVecLin_apply,
      Matrix.mulVec_single_one, Matrix.col_transpose, Matrix.of_row, Matrix.row_apply,
      Matrix.of_apply] using hmap.symm
  have hc : ∀ i, a (b i) = 0 := fun i =>
    (linearIndependent_iff'.mp hB) Finset.univ _ hsum i (Finset.mem_univ i)
  rw [hexp]
  simp only [hc, zero_smul, Finset.sum_const_zero]

theorem fundamentalRows_span_globalRelationSpace {n r k : ℕ}
    (q : Fin n → Fin r → ℝ) (b : Fin k → Fin n) (S : Finset (Fin n))
    (hB : LinearIndependent ℝ (fun i => q (b i)))
    (hbS : ∀ i, b i ∈ S)
    (hspan : ∀ v ∈ S, q v ∈ Submodule.span ℝ (Set.range (fun i => q (b i)))) :
    globalRelationSpace q S =
      Submodule.span ℝ (fundamentalRow q b ''
        (↑(S.filter (fun v => v ∉ Set.range b)) : Set (Fin n))) := by
  let T := S.filter (fun v => v ∉ Set.range b)
  let W := Submodule.span ℝ (fundamentalRow q b '' (↑T : Set (Fin n)))
  have hrow (v : Fin n) (hv : v ∈ T) :
      fundamentalRow q b v ∈ globalRelationSpace q S :=
    fundamentalRow_mem_globalRelationSpace q b v S hB hbS
      (Finset.mem_filter.mp hv).1 (hspan v (Finset.mem_filter.mp hv).1)
  apply le_antisymm
  · intro a ha
    let s := ∑ v ∈ T, a v • fundamentalRow q b v
    have hs : s ∈ W := by
      apply Submodule.sum_mem
      intro v hv
      exact Submodule.smul_mem W (a v) (Submodule.subset_span ⟨v, hv, rfl⟩)
    have hsr : s ∈ globalRelationSpace q S := by
      apply Submodule.sum_mem
      intro v hv
      exact Submodule.smul_mem _ (a v) (hrow v hv)
    have hr := (globalRelationSpace q S).sub_mem ha hsr
    have hzero : a - s = 0 := by
      apply relation_supported_on_independent_frame_eq_zero q b hB
        (a - s) ((mem_globalRelationSpace_iff q S _).mp hr).2
      intro w hw
      have hvalue : s w = if w ∈ T then a w else 0 := by
        simp only [s, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          fundamentalRow_outside_frame q b _ w hw]
        simp [mul_ite]
      by_cases hwS : w ∈ S
      · have hwT : w ∈ T := Finset.mem_filter.mpr ⟨hwS, hw⟩
        simp only [Pi.sub_apply, hvalue, if_pos hwT, sub_self]
      · have hwT : w ∉ T := fun h => hwS (Finset.mem_filter.mp h).1
        simp only [Pi.sub_apply, hvalue, if_neg hwT,
          ((mem_globalRelationSpace_iff q S _).mp ha).1 w hwS, sub_self]
    exact (sub_eq_zero.mp hzero).symm ▸ hs
  · apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    exact hrow v hv

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart8

section BundlePart9
/- Source: Papers/ProjectionHeightLifting.lean -/




@[expose] public section

/-!
# Solving reciprocal heights after rationalizing a projected configuration

The height matrix is a continuous rational function of the projected point
configuration. Its rows are independent at the original realization, as
proved from the certified leaf pivots. A Gram-kernel projector reconstructs
all heights simultaneously and fixes the original heights. Positivity is
an open condition and is retained in the resulting approximation.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix Filter Topology
open scoped Classical BigOperators
open PlaneRationalization

theorem rationalScalarFamily_dense (n : ℕ) :
    Dense {w : Fin n → ℝ | ∀ i, RatScalar (w i)} := by
  have h : DenseRange (fun w : Fin n → ℚ => fun i => (w i : ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  apply h.mono
  rintro w ⟨w', rfl⟩ i
  exact ⟨w' i, rfl⟩

/-- The height solve is performed on a genuine open full-row-rank chart.
The admissible projected configurations remain arbitrary; their rational
density is proved separately by the incidence insertion theorem. -/
theorem rational_positive_height_lift {m r c n : ℕ}
    (q : Fin m → Fin r → ℝ) (h : Fin n → ℝ)
    (Allowed : Set (Fin m → Fin r → ℝ))
    (C : (Fin m → Fin r → ℝ) → Matrix (Fin c) (Fin n) ℝ)
    (hCcont : ContinuousAt C q)
    (hCrat : ∀ q', RationalCoordinates q' → RationalCoordinates (C q'))
    (hCind : LinearIndependent ℝ (C q).row)
    (hCh : (C q).mulVec h = 0) (hpos : ∀ i, 0 < h i)
    (hq : q ∈ closure {q' | RationalCoordinates q' ∧ q' ∈ Allowed}) :
    (q, h) ∈ closure
      {z : (Fin m → Fin r → ℝ) × (Fin n → ℝ) |
        RationalCoordinates z.1 ∧ z.1 ∈ Allowed ∧
        (∀ i, RatScalar (z.2 i)) ∧ (C z.1).mulVec z.2 = 0 ∧
        ∀ i, 0 < z.2 i} := by
  let H := fun z : (Fin m → Fin r → ℝ) × (Fin n → ℝ) =>
    rowKernelVector (C z.1) z.2
  have hparam : ContinuousAt
      (fun z : (Fin m → Fin r → ℝ) × (Fin n → ℝ) => (C z.1, z.2)) (q, h) :=
    (hCcont.comp_of_eq continuous_fst.continuousAt rfl).prodMk continuous_snd.continuousAt
  have hHcont : ContinuousAt H (q, h) :=
    (rowKernelVector_continuousAt hCind h).comp_of_eq hparam rfl
  have hHbase : H (q, h) = h := rowKernelVector_self _ _ hCh
  let F := fun z : (Fin m → Fin r → ℝ) × (Fin n → ℝ) => (z.1, H z)
  have hFcont : ContinuousAt F (q, h) :=
    continuous_fst.continuousAt.prodMk hHcont
  have hFbase : F (q, h) = (q, h) := by
    change (q, H (q, h)) = (q, h)
    rw [hHbase]
  have hrows : ∀ᶠ z in 𝓝 (q, h), LinearIndependent ℝ (C z.1).row :=
    (hCcont.comp_of_eq (continuous_fst.continuousAt (x := (q, h))) rfl).tendsto.eventually
      hCind.eventually
  have hpositive : ∀ᶠ z in 𝓝 (q, h), ∀ i, 0 < H z i := by
    apply eventually_all.mpr
    intro i
    have hcoord := (continuous_apply i).continuousAt.comp hHcont
    apply hcoord.tendsto.eventually
    apply isOpen_Ioi.mem_nhds
    change 0 < H (q, h) i
    rw [hHbase]
    exact hpos i
  have hprod : (q, h) ∈ closure
      ({q' | RationalCoordinates q' ∧ q' ∈ Allowed} ×ˢ
        {w : Fin n → ℝ | ∀ i, RatScalar (w i)}) := by
    rw [closure_prod_eq]
    exact ⟨hq, rationalScalarFamily_dense n h⟩
  have hcl := mem_closure_inter_of_eventually hprod (hrows.and hpositive)
  have himage := mem_closure_image hFcont hcl
  rw [hFbase] at himage
  apply closure_mono (s := F '' _) ?_ himage
  rintro _ ⟨⟨q', w⟩, ⟨⟨⟨hqr, hqa⟩, hwr⟩, hgood⟩, rfl⟩
  exact ⟨hqr, hqa, rowKernelVector_rational (hCrat q' hqr) hwr,
    rowKernelVector_mem hgood.1 w, hgood.2⟩

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart9

section BundlePart10
/- Source: Papers/ProjectionHeightMatrix.lean -/






@[expose] public section

/-!
# Height matrices from finite geometric relation templates

Each row is the fundamental relation of a chosen projected frame and one
additional vertex.  The finite template specifies only labels.  Independence
is proved from explicit nonzero pivots; a frame-entry pivot requires an
independent replacement frame.  Later rows must have no occurrence of that
pivot label, so the triangularity proof does not assume symbolic nonvanishing.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Matrix Module Set Filter Topology
open scoped Classical BigOperators
open Papers.RationalKernelCharts

def projectedHeightMatrix {n r c : ℕ}
    (T : Fin c → ProjectedRelationTemplate n) (q : Fin n → Fin r → ℝ) :
    Matrix (Fin c) (Fin n) ℝ :=
  fun i => fundamentalRow q (T i).frame (T i).vertex

theorem projectedHeightMatrix_rational {n r c : ℕ}
    (T : Fin c → ProjectedRelationTemplate n) (q : Fin n → Fin r → ℝ)
    (hq : RationalCoordinates q) : RationalCoordinates (projectedHeightMatrix T q) :=
  fun i => fundamentalRow_rational q (T i).frame (T i).vertex hq

theorem projectedHeightMatrix_continuousAt {n r c : ℕ}
    (T : Fin c → ProjectedRelationTemplate n) (q : Fin n → Fin r → ℝ)
    (hframes : ∀ i, LinearIndependent ℝ (fun j => q ((T i).frame j))) :
    ContinuousAt (projectedHeightMatrix T) q := by
  apply continuousAt_pi.mpr
  intro i
  exact fundamentalRow_continuousAt q (T i).frame (T i).vertex (hframes i)

theorem fundamentalRow_eq_zero_of_no_label {n r k : ℕ}
    (q : Fin n → Fin r → ℝ) (b : Fin k → Fin n) (v w : Fin n)
    (hb : w ∉ Set.range b) (hv : w ≠ v) : fundamentalRow q b v w = 0 := by
  rw [fundamentalRow_outside_frame q b v w hb, if_neg hv]

/-- Every nonzero pivot is justified either by its defining coefficient 1,
or by a geometrically independent replacement frame. -/
theorem projectedHeightMatrix_independent {n r c : ℕ}
    (T : Fin c → ProjectedRelationTemplate n) (q : Fin n → Fin r → ℝ)
    (hframes : ∀ i, LinearIndependent ℝ (fun j => q ((T i).frame j)))
    (houtside : ∀ i, (T i).vertex ∉ Set.range (T i).frame)
    (hspan : ∀ i, q (T i).vertex ∈
      Submodule.span ℝ (Set.range (fun j => q ((T i).frame j))))
    (pivot : Fin c → Fin n)
    (hpivot : ∀ i, pivot i = (T i).vertex ∨
      ∃ j : Fin (T i).frameSize,
        pivot i = (T i).frame j ∧
        LinearIndependent ℝ
          (fun t => q (Function.update (T i).frame j (T i).vertex t)))
    (hlater : ∀ i j, i < j →
      pivot i ≠ (T j).vertex ∧ pivot i ∉ Set.range (T j).frame) :
    LinearIndependent ℝ (projectedHeightMatrix T q).row := by
  apply Papers.ProjectionCertificateLinearAlgebra.pivot_order_independent
    (projectedHeightMatrix T q) pivot
  · intro i
    rcases hpivot i with hi | ⟨j, hij, hreplace⟩
    · rw [hi]
      change fundamentalRow q (T i).frame (T i).vertex (T i).vertex ≠ 0
      rw [fundamentalRow_pivot q _ _ (houtside i)]
      exact one_ne_zero
    · rw [hij]
      have hinj : Function.Injective (T i).frame := by
        intro j k hjk
        exact (hframes i).injective (congrArg q hjk)
      change fundamentalRow q (T i).frame (T i).vertex ((T i).frame j) ≠ 0
      rw [fundamentalRow_frame_entry q _ _ hinj (houtside i) j]
      exact neg_ne_zero.mpr
        (fundamentalCoefficients_ne_zero_of_replacement q _ _ j
          (hframes i) (hspan i) hreplace)
  · intro i j hij
    exact fundamentalRow_eq_zero_of_no_label q _ _ _
      (hlater i j hij).2 (hlater i j hij).1

/-- A finite list that contains each fundamental relation of a facet spans
the whole facet relation space, including all its unlisted equations. -/
theorem globalRelationSpace_le_projectedHeightMatrix {n r c k : ℕ}
    (T : Fin c → ProjectedRelationTemplate n) (q : Fin n → Fin r → ℝ)
    (S : Finset (Fin n)) (b : Fin k → Fin n)
    (hB : LinearIndependent ℝ (fun j => q (b j)))
    (hbS : ∀ j, b j ∈ S)
    (hspan : ∀ v ∈ S, q v ∈ Submodule.span ℝ (Set.range (fun j => q (b j))))
    (hcovered : ∀ v ∈ S, v ∉ Set.range b →
      fundamentalRow q b v ∈ Submodule.span ℝ (Set.range (projectedHeightMatrix T q))) :
    globalRelationSpace q S ≤
      Submodule.span ℝ (Set.range (projectedHeightMatrix T q)) := by
  rw [fundamentalRows_span_globalRelationSpace q b S hB hbS hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, rfl⟩
  exact hcovered v (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2

theorem projectedHeightMatrix_mulVec_zero {n r c : ℕ}
    (T : Fin c → ProjectedRelationTemplate n) (q : Fin n → Fin r → ℝ)
    (h : Fin n → ℝ) (S : Fin c → Finset (Fin n))
    (hframes : ∀ i, LinearIndependent ℝ (fun j => q ((T i).frame j)))
    (hframeS : ∀ i j, (T i).frame j ∈ S i)
    (hvertexS : ∀ i, (T i).vertex ∈ S i)
    (hspan : ∀ i, q (T i).vertex ∈
      Submodule.span ℝ (Set.range (fun j => q ((T i).frame j))))
    (hheight : ∀ i, ∀ v ∈ globalRelationSpace q (S i), h ⬝ᵥ v = 0) :
    (projectedHeightMatrix T q).mulVec h = 0 := by
  ext i
  rw [Matrix.mulVec, dotProduct_comm]
  exact hheight i _ (fundamentalRow_mem_globalRelationSpace q _ _ (S i)
    (hframes i) (hframeS i) (hvertexS i) (hspan i))

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart10

section BundlePart11
/- Source: Papers/ActualProjectedHeights.lean -/




@[expose] public section

/-!
# Actual reciprocal heights and geometric relation templates

Reciprocal height is the restriction of a linear functional on the
homogeneous projection of any face avoiding the apex. Consequently every
actual relation on that face annihilates the original height vector.

The finite row templates below carry only face membership and facial
independence witnesses. Their rank, continuity, rationality, and nonzero
pivots are conclusions. No matrix-rank or genericity assumption is hidden
inside the certificate data.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix Filter Topology
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeIncidenceConfiguration Papers.RationalOrthogonalityPeeling

variable {P : ConvexPolytope 4} {a : VertexType P} {n : ℕ}

def projectedFaceLabels (e : Fin n ≃ ProjectionPoint P a) (F : FaceType P) :
    Finset (Fin n) := Finset.univ.filter fun i => (e i).val.val ∈ F.val

@[simp] theorem mem_projectedFaceLabels (e : Fin n ≃ ProjectionPoint P a)
    (F : FaceType P) (i : Fin n) :
    i ∈ projectedFaceLabels e F ↔ (e i).val.val ∈ F.val := by
  simp only [projectedFaceLabels, Finset.mem_filter, Finset.mem_univ, true_and]

theorem projectedFaceLabels_mono (e : Fin n ≃ ProjectionPoint P a)
    (F G : FaceType P) (hFG : F.val ⊆ G.val) :
    projectedFaceLabels e F ⊆ projectedFaceLabels e G := by
  intro i hi
  exact (mem_projectedFaceLabels e G i).mpr (hFG ((mem_projectedFaceLabels e F i).mp hi))

theorem exists_plane_containing_avoiding_polygon (P : ConvexPolytope 4)
    (a : VertexType P) (R : Face P 2) (haR : a.val ∉ R.val.carrier) :
    ∃ B : ActualProjectionPlane P a, R.val.carrier ⊆ projectionPlaneCarrier B := by
  by_cases h : ∃ F : OrdinaryProjectionPlane P a, R.val.carrier ⊆ F.val.val.val
  · obtain ⟨F, hF⟩ := h
    exact ⟨Sum.inl F, hF⟩
  · refine ⟨Sum.inr ⟨R, haR, ?_⟩, Set.Subset.rfl⟩
    intro F hF
    exact h ⟨F, hF⟩

theorem relation_annihilates_restricted_linear_functional {r : ℕ}
    (q : Fin n → Fin r → ℝ) (h : Fin n → ℝ) (S : Finset (Fin n))
    (ell : (Fin r → ℝ) →ₗ[ℝ] ℝ) (hell : ∀ i ∈ S, ell (q i) = h i) :
    ∀ v ∈ globalRelationSpace q S, h ⬝ᵥ v = 0 := by
  intro v hv
  obtain ⟨hsupport, hzero⟩ := (mem_globalRelationSpace_iff q S v).mp hv
  have hsum : ∑ i, v i • q i = 0 := by
    ext j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
      Matrix.transpose_apply, Matrix.of_apply, dotProduct, mul_comm]
      using congrFun hzero j
  have heval := congrArg ell hsum
  simp only [map_sum, map_smul, map_zero, smul_eq_mul] at heval
  calc
    h ⬝ᵥ v = ∑ i, v i * ell (q i) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ S
      · rw [hell i hi, mul_comm]
      · rw [hsupport i hi, mul_zero, zero_mul]
    _ = 0 := heval

namespace VertexProjectionChart

def projectedFamily (D : VertexProjectionChart P a) (e : Fin n ≃ ProjectionPoint P a) :
    Fin n → Fin 4 → ℝ := fun i => D.projectedVector (e i)

def heightFamily (D : VertexProjectionChart P a) (e : Fin n ≃ ProjectionPoint P a) :
    Fin n → ℝ := fun i => D.reciprocalHeight (e i)

theorem projectedFamily_preserves_incidences (D : VertexProjectionChart P a)
    (hP : P.IsFullDim) (e : Fin n ≃ ProjectionPoint P a) :
    PreservesProjectedIncidences e (D.projectedFamily e) := by
  intro B
  exact ⟨D.planeVector hP B, D.planeVector_ne_zero hP B,
    fun i hi => D.planeVector_dot_projectedVector hP (e i) B hi⟩

theorem avoidingHeight_projectedVector (D : VertexProjectionChart P a)
    (f : E 4 →ᵃ[ℝ] ℝ) (hfa : f a.val ≠ 0) (v : ProjectionPoint P a)
    (hfv : f v.val.val = 0) :
    D.avoidingHeight f (coordinateHomogeneousEquiv 3 (D.projectedVector v)) =
      D.reciprocalHeight v := by
  rw [D.projectedVector_lift, map_smul]
  have hh := congrArg Prod.snd (D.avoidingFaceLift_apply f hfa v.val.val hfv)
  change D.avoidingHeight f (D.affine v.val.val) = 1 at hh
  rw [hh, smul_eq_mul, mul_one]

theorem height_annihilates_face_relations (D : VertexProjectionChart P a)
    (e : Fin n ≃ ProjectionPoint P a) (F : FaceType P) (haF : a.val ∉ F.val) :
    ∀ v ∈ globalRelationSpace (D.projectedFamily e) (projectedFaceLabels e F),
      D.heightFamily e ⬝ᵥ v = 0 := by
  obtain ⟨f, hf⟩ := exists_supportsFace P F.property
  have hfa : f a.val ≠ 0 := by
    intro hz
    exact haF ((hf.mem_iff a.val).mpr ⟨vertex_mem_body P a.property, hz⟩)
  apply relation_annihilates_restricted_linear_functional
    (D.projectedFamily e) (D.heightFamily e) (projectedFaceLabels e F)
    ((D.avoidingHeight f).comp (coordinateHomogeneousEquiv 3).toLinearMap)
  intro i hi
  exact D.avoidingHeight_projectedVector f hfa (e i)
    (hf.eq_zero ((mem_projectedFaceLabels e F i).mp hi))

end VertexProjectionChart

/-- A selected frame is certified by actual polygon membership or an
actual facial four-point witness. -/
inductive ProjectedFrameCertificate (e : Fin n ≃ ProjectionPoint P a)
    {k : ℕ} (b : Fin k → Fin n) : Prop
  | polygon (hk : k ≤ 3) (hinj : Function.Injective b) (R : Face P 2)
      (ha : a.val ∉ R.val.carrier) (hmem : ∀ j, (e (b j)).val.val ∈ R.val.carrier)
  | facial (hk : k ≤ 4) (hinj : Function.Injective b)
      (R : Face P 2) (F : FacetType P) (ha : a.val ∉ F.val.val)
      (hmem : ∀ j, (e (b j)).val.val ∈ F.val.val)
      (t : Fin k) (hout : (e (b t)).val.val ∉ R.val.carrier)
      (hin : ∀ j, j ≠ t → (e (b j)).val.val ∈ R.val.carrier)

theorem ProjectedFrameCertificate.independent
    (e : Fin n ≃ ProjectionPoint P a) {k : ℕ} (b : Fin k → Fin n)
    (hb : ProjectedFrameCertificate e b) (D : VertexProjectionChart P a)
    (hP : P.IsFullDim) :
    LinearIndependent ℝ (fun j => D.projectedFamily e (b j)) := by
  cases hb with
  | polygon hk hinj R ha hmem =>
    exact D.projected_points_on_avoiding_face_independent hP (fun j => e (b j))
      (e.injective.comp hinj) (by simpa using hk) ⟨R.val.carrier, R.val.isFace⟩ ha hmem
  | facial hk hinj R F ha hmem t hout hin =>
    exact D.projected_frame_of_facial_witness_independent hP (fun j => e (b j))
      (e.injective.comp hinj) (by simpa using hk) t
      ⟨R.val.carrier, R.val.isFace⟩ F.val hout hin ha hmem

theorem ProjectedFrameCertificate.injective
    (e : Fin n ≃ ProjectionPoint P a) {k : ℕ} (b : Fin k → Fin n)
    (hb : ProjectedFrameCertificate e b) : Function.Injective b := by
  cases hb with
  | polygon _ hinj _ _ _ => exact hinj
  | facial _ hinj _ _ _ _ _ _ _ => exact hinj

/-- A supported height row. In the four-point case the independent frame
spans the full projected ambient space. In the three-point case its actual
carrier is contained in one of the required projected planes. -/
structure CertifiedHeightRow (e : Fin n ≃ ProjectionPoint P a)
    extends ProjectedRelationTemplate n where
  carrier : FaceType P
  avoids : a.val ∉ carrier.val
  frame_mem : ∀ j, (e (frame j)).val.val ∈ carrier.val
  vertex_mem : (e vertex).val.val ∈ carrier.val
  vertex_outside_frame : vertex ∉ Set.range frame
  frame_certificate : ProjectedFrameCertificate e frame
  spanning_certificate : frameSize = 4 ∨
    (frameSize = 3 ∧ ∃ B : ActualProjectionPlane P a, carrier.val ⊆ projectionPlaneCarrier B)

theorem independent_frame_spans_of_rank_bound {r k : ℕ}
    (q : Fin n → Fin r → ℝ) (b : Fin k → Fin n) (S : Finset (Fin n))
    (hb : LinearIndependent ℝ (fun j => q (b j)))
    (hmem : ∀ j, b j ∈ S) (hrank : subsetRank q S ≤ k) :
    ∀ v ∈ S, q v ∈ Submodule.span ℝ (Set.range (fun j => q (b j))) := by
  let U := Submodule.span ℝ (Set.range (fun j => q (b j)))
  let W := Submodule.span ℝ (q '' (↑S : Set (Fin n)))
  have hUW : U ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Submodule.subset_span ⟨b j, hmem j, rfl⟩
  have hdim : finrank ℝ U = k := by
    simpa only [Fintype.card_fin] using finrank_span_eq_card hb
  have heq : U = W := Submodule.eq_of_le_of_finrank_le hUW (by
    change subsetRank q S ≤ finrank ℝ U
    rw [hdim]
    exact hrank)
  intro v hv
  change q v ∈ U
  rw [heq]
  exact Submodule.subset_span ⟨v, hv, rfl⟩

theorem CertifiedHeightRow.frame_spans (e : Fin n ≃ ProjectionPoint P a)
    (R : CertifiedHeightRow e) (q : Fin n → Fin 4 → ℝ)
    (hq : PreservesProjectedIncidences e q)
    (hb : LinearIndependent ℝ (fun j => q (R.frame j))) :
    ∀ v ∈ projectedFaceLabels e R.carrier,
      q v ∈ Submodule.span ℝ (Set.range (fun j => q (R.frame j))) := by
  apply independent_frame_spans_of_rank_bound q R.frame (projectedFaceLabels e R.carrier)
    hb (fun j => (mem_projectedFaceLabels e R.carrier _).mpr (R.frame_mem j))
  rcases R.spanning_certificate with hfour | ⟨hthree, B, hB⟩
  · rw [hfour]
    have h := (Submodule.span ℝ (q '' (↑(projectedFaceLabels e R.carrier) : Set (Fin n)))).finrank_le
    change finrank ℝ (Submodule.span ℝ (q '' (↑(projectedFaceLabels e R.carrier) : Set (Fin n)))) ≤ 4
    simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] using h
  · rw [hthree]
    exact projected_incidence_rank_upper e q hq B (projectedFaceLabels e R.carrier)
      (fun i hi => hB ((mem_projectedFaceLabels e R.carrier i).mp hi))

theorem CertifiedHeightRow.mem_relationSpace (e : Fin n ≃ ProjectionPoint P a)
    (R : CertifiedHeightRow e) (q : Fin n → Fin 4 → ℝ)
    (hq : PreservesProjectedIncidences e q)
    (hb : LinearIndependent ℝ (fun j => q (R.frame j))) :
    fundamentalRow q R.frame R.vertex ∈
      globalRelationSpace q (projectedFaceLabels e R.carrier) :=
  fundamentalRow_mem_globalRelationSpace q R.frame R.vertex (projectedFaceLabels e R.carrier) hb
    (fun j => (mem_projectedFaceLabels e R.carrier _).mpr (R.frame_mem j))
    ((mem_projectedFaceLabels e R.carrier _).mpr R.vertex_mem)
    (R.frame_spans e q hq hb _ ((mem_projectedFaceLabels e R.carrier _).mpr R.vertex_mem))

theorem CertifiedHeightRow.nonzero (e : Fin n ≃ ProjectionPoint P a)
    (R : CertifiedHeightRow e) (q : Fin n → Fin 4 → ℝ) :
    fundamentalRow q R.frame R.vertex ≠ 0 := by
  intro h
  have hp := fundamentalRow_pivot q R.frame R.vertex R.vertex_outside_frame
  have hz := congrFun h R.vertex
  rw [hp] at hz
  exact one_ne_zero hz

/-- Certified leaf deletion of the height rows, including nonzero
replacement-frame coefficients when a leaf lies in the chosen frame. -/
structure ActualHeightRowCertificate (e : Fin n ≃ ProjectionPoint P a) (c : ℕ) where
  rows : Fin c → CertifiedHeightRow e
  pivot : Fin c → Fin n
  pivot_certificate : ∀ i, pivot i = (rows i).vertex ∨
    ∃ j : Fin (rows i).frameSize, pivot i = (rows i).frame j ∧
      ProjectedFrameCertificate e (Function.update (rows i).frame j (rows i).vertex)
  later_absent : ∀ i j, i < j →
    pivot i ≠ (rows j).vertex ∧ pivot i ∉ Set.range (rows j).frame

namespace ActualHeightRowCertificate

variable {e : Fin n ≃ ProjectionPoint P a}

def templates {c : ℕ} (H : ActualHeightRowCertificate e c) :
    Fin c → ProjectedRelationTemplate n := fun i => (H.rows i).toProjectedRelationTemplate

def matrix {c : ℕ} (H : ActualHeightRowCertificate e c) (q : Fin n → Fin 4 → ℝ) :
    Matrix (Fin c) (Fin n) ℝ := projectedHeightMatrix H.templates q

theorem original_frames_independent {c : ℕ} (H : ActualHeightRowCertificate e c)
    (D : VertexProjectionChart P a) (hP : P.IsFullDim) :
    ∀ i, LinearIndependent ℝ (fun j => D.projectedFamily e ((H.rows i).frame j)) :=
  fun i => (H.rows i).frame_certificate.independent e _ D hP

theorem original_rows_independent {c : ℕ} (H : ActualHeightRowCertificate e c)
    (D : VertexProjectionChart P a) (hP : P.IsFullDim) :
    LinearIndependent ℝ (H.matrix (D.projectedFamily e)).row := by
  have hframes := H.original_frames_independent D hP
  have hq := D.projectedFamily_preserves_incidences hP e
  apply projectedHeightMatrix_independent H.templates (D.projectedFamily e) hframes
    (fun i => (H.rows i).vertex_outside_frame)
    (fun i => (H.rows i).frame_spans e _ hq (hframes i) _
      ((mem_projectedFaceLabels e (H.rows i).carrier _).mpr (H.rows i).vertex_mem))
    H.pivot _ H.later_absent
  intro i
  rcases H.pivot_certificate i with hi | ⟨j, hij, hc⟩
  · exact Or.inl hi
  · exact Or.inr ⟨j, hij, hc.independent e _ D hP⟩

theorem original_heights_in_kernel {c : ℕ} (H : ActualHeightRowCertificate e c)
    (D : VertexProjectionChart P a) (hP : P.IsFullDim) :
    (H.matrix (D.projectedFamily e)).mulVec (D.heightFamily e) = 0 := by
  ext i
  change fundamentalRow (D.projectedFamily e) (H.rows i).frame (H.rows i).vertex
    ⬝ᵥ D.heightFamily e = 0
  rw [dotProduct_comm]
  exact D.height_annihilates_face_relations e (H.rows i).carrier (H.rows i).avoids _
    ((H.rows i).mem_relationSpace e _ (D.projectedFamily_preserves_incidences hP e)
      (H.original_frames_independent D hP i))

theorem continuousAt_matrix {c : ℕ} (H : ActualHeightRowCertificate e c)
    (D : VertexProjectionChart P a) (hP : P.IsFullDim) :
    ContinuousAt H.matrix (D.projectedFamily e) :=
  projectedHeightMatrix_continuousAt H.templates _ (H.original_frames_independent D hP)

theorem matrix_rational {c : ℕ} (H : ActualHeightRowCertificate e c)
    (q : Fin n → Fin 4 → ℝ) (hq : RationalCoordinates q) : RationalCoordinates (H.matrix q) :=
  projectedHeightMatrix_rational H.templates q hq

theorem eventually_frames_independent {c : ℕ} (H : ActualHeightRowCertificate e c)
    (D : VertexProjectionChart P a) (hP : P.IsFullDim) :
    ∀ᶠ q in 𝓝 (D.projectedFamily e),
      ∀ i, LinearIndependent ℝ (fun j => q ((H.rows i).frame j)) := by
  apply eventually_all.mpr
  intro i
  have hc : Continuous (fun q : Fin n → Fin 4 → ℝ => fun j => q ((H.rows i).frame j)) :=
    continuous_pi fun j => continuous_apply ((H.rows i).frame j)
  exact hc.continuousAt.tendsto.eventually (H.original_frames_independent D hP i).eventually

end ActualHeightRowCertificate
end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart11

section BundlePart12
/- Source: Papers/ActualProjectionHeightCoverage.lean -/



@[expose] public section

/-!
# Complete facet coverage by the certified height rows

A facet with a selected four-point frame is covered either by all its
fundamental rows, or, when it has at most five vertices, by one nonzero
supported row. The second construction includes square pyramids: the
quadrilateral row spans their one-dimensional relation space. Tetrahedra
are the first construction with no remaining vertex and no height row.

Every neighborhood condition used below is proved open at the actual
configuration. The finite certificate itself contains no analytic or
linear-independence hypothesis.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix Filter Topology
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeIncidenceConfiguration Papers.RationalOrthogonalityPeeling

variable {P : ConvexPolytope 4} {a : VertexType P} {n c : ℕ}

abbrev AvoidingProjectionFacet (P : ConvexPolytope 4) (a : VertexType P) :=
  {F : FacetType P // a.val ∉ F.val.val}

inductive ProjectionFacetHeightCoverage (e : Fin n ≃ ProjectionPoint P a)
    (H : ActualHeightRowCertificate e c) (F : FacetType P) : Type
  | fundamental (b : Fin 4 → Fin n)
      (hframe : ProjectedFrameCertificate e b)
      (hmem : ∀ j, (e (b j)).val.val ∈ F.val.val)
      (hcovered : ∀ v ∈ projectedFaceLabels e F.val, v ∉ Set.range b →
        ∃ i : Fin c, H.templates i = {frameSize := 4, frame := b, vertex := v})
  | oneRow (b : Fin 4 → Fin n)
      (hframe : ProjectedFrameCertificate e b)
      (hmem : ∀ j, (e (b j)).val.val ∈ F.val.val)
      (hcard : (projectedFaceLabels e F.val).card ≤ 5)
      (i : Fin c) (hsupport : (H.rows i).carrier.val ⊆ F.val.val)
  | fromLargerFacet (b : Fin 4 → Fin n)
      (hframe : ProjectedFrameCertificate e b)
      (hmem : ∀ j, (e (b j)).val.val ∈ F.val.val)
      (hcard : (projectedFaceLabels e F.val).card ≤ 5)
      (R : Face P 2) (haR : a.val ∉ R.val.carrier)
      (hRcard : 4 ≤ (projectedFaceLabels e ⟨R.val.carrier, R.val.isFace⟩).card)
      (hRF : R.val.carrier ⊆ F.val.val)
      (G : FacetType P) (g : Fin 4 → Fin n)
      (hgframe : ProjectedFrameCertificate e g)
      (hgmem : ∀ j, (e (g j)).val.val ∈ G.val.val)
      (hRG : R.val.carrier ⊆ G.val.val)
      (hcovered : ∀ v ∈ projectedFaceLabels e G.val, v ∉ Set.range g →
        ∃ i : Fin c, H.templates i = {frameSize := 4, frame := g, vertex := v})

namespace ProjectionFacetHeightCoverage

variable {e : Fin n ≃ ProjectionPoint P a} {H : ActualHeightRowCertificate e c}
    {F : FacetType P}

def frame (K : ProjectionFacetHeightCoverage e H F) : Fin 4 → Fin n :=
  match K with
  | .fundamental b _ _ _ => b
  | .oneRow b _ _ _ _ _ => b
  | .fromLargerFacet b _ _ _ _ _ _ _ _ _ _ _ _ _ => b

def auxiliaryFrame (K : ProjectionFacetHeightCoverage e H F) : Fin 4 → Fin n :=
  match K with
  | .fundamental b _ _ _ => b
  | .oneRow b _ _ _ _ _ => b
  | .fromLargerFacet _ _ _ _ _ _ _ _ _ g _ _ _ _ => g

theorem frame_certificate (K : ProjectionFacetHeightCoverage e H F) :
    ProjectedFrameCertificate e K.frame := by
  cases K with
  | fundamental b hframe _ _ => exact hframe
  | oneRow b hframe _ _ _ _ => exact hframe
  | fromLargerFacet b hframe _ _ _ _ _ _ _ _ _ _ _ _ => exact hframe

theorem auxiliaryFrame_certificate (K : ProjectionFacetHeightCoverage e H F) :
    ProjectedFrameCertificate e K.auxiliaryFrame := by
  cases K with
  | fundamental b hframe _ _ => exact hframe
  | oneRow b hframe _ _ _ _ => exact hframe
  | fromLargerFacet _ _ _ _ _ _ _ _ _ g hgframe _ _ _ => exact hgframe

theorem frame_mem (K : ProjectionFacetHeightCoverage e H F) :
    ∀ j, (e (K.frame j)).val.val ∈ F.val.val := by
  cases K with
  | fundamental b _ hmem _ => exact hmem
  | oneRow b _ hmem _ _ _ => exact hmem
  | fromLargerFacet b _ hmem _ _ _ _ _ _ _ _ _ _ _ => exact hmem

theorem complete_relations (K : ProjectionFacetHeightCoverage e H F)
    (q : Fin n → Fin 4 → ℝ) (hq : PreservesProjectedIncidences e q)
    (hrows : ∀ i, LinearIndependent ℝ (fun j => q ((H.rows i).frame j)))
    (hframe : LinearIndependent ℝ (fun j => q (K.frame j)))
    (hauxiliary : LinearIndependent ℝ (fun j => q (K.auxiliaryFrame j))) :
    globalRelationSpace q (projectedFaceLabels e F.val) ≤
      Submodule.span ℝ (Set.range (H.matrix q)) := by
  have hspan : ∀ v : Fin n,
      q v ∈ Submodule.span ℝ (Set.range (fun j => q (K.frame j))) := by
    have htop := hframe.span_eq_top_of_card_eq_finrank' (by simp)
    intro v
    rw [htop]
    exact Submodule.mem_top
  cases K with
  | fundamental b hframeCert hmem hcovered =>
    apply globalRelationSpace_le_projectedHeightMatrix H.templates q
      (projectedFaceLabels e F.val) b hframe
      (fun j => (mem_projectedFaceLabels e F.val _).mpr (hmem j))
      (fun v _ => hspan v)
    intro v hv hvb
    obtain ⟨i, hi⟩ := hcovered v hv hvb
    have heq : H.matrix q i = fundamentalRow q b v := by
      change fundamentalRow q (H.templates i).frame (H.templates i).vertex = _
      rw [hi]
    rw [← heq]
    exact Submodule.subset_span ⟨i, rfl⟩
  | oneRow b hframeCert hmem hcard i hsupport =>
    let S := projectedFaceLabels e F.val
    let U := globalRelationSpace q S
    have hrel : H.matrix q i ∈ U := by
      apply globalRelationSpace_mono q
        (projectedFaceLabels_mono e (H.rows i).carrier F.val hsupport)
      exact (H.rows i).mem_relationSpace e q hq (hrows i)
    have hne : H.matrix q i ≠ 0 := (H.rows i).nonzero e q
    have hframele : Submodule.span ℝ (Set.range (fun j => q (b j))) ≤
        Submodule.span ℝ (q '' (↑S : Set (Fin n))) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact Submodule.subset_span ⟨b j,
        (mem_projectedFaceLabels e F.val _).mpr (hmem j), rfl⟩
    have hfrank : finrank ℝ (Submodule.span ℝ (Set.range (fun j => q (b j)))) = 4 := by
      change LinearIndependent ℝ (fun j => q (b j)) at hframe
      simpa only [Fintype.card_fin] using finrank_span_eq_card hframe
    have hlow : 4 ≤ subsetRank q S := by
      have hh := Submodule.finrank_mono hframele
      rw [hfrank] at hh
      exact hh
    have hdim := globalRelationSpace_finrank q S
    have hUpos : finrank ℝ U ≠ 0 := by
      intro hz
      have hbot := Submodule.finrank_eq_zero.mp hz
      exact hne (by simpa only [hbot, Submodule.mem_bot] using hrel)
    have hUdim : finrank ℝ U = 1 := by
      change finrank ℝ U + subsetRank q S = S.card at hdim
      change S.card ≤ 5 at hcard
      omega
    change U ≤ Submodule.span ℝ (Set.range (H.matrix q))
    rw [eq_span_singleton_of_mem_of_finrank_eq_one hUdim hrel hne]
    apply Submodule.span_le.mpr
    intro x hx
    have heq : x = H.matrix q i := Set.mem_singleton_iff.mp hx
    subst x
    exact Submodule.subset_span ⟨i, rfl⟩
  | fromLargerFacet b hframeCert hmem hcard R haR hRcard hRF G g hgframe hgmem hRG hcovered =>
    let SR := projectedFaceLabels e (⟨R.val.carrier, R.val.isFace⟩ : FaceType P)
    let SF := projectedFaceLabels e F.val
    let SG := projectedFaceLabels e G.val
    let U := globalRelationSpace q SF
    have hGspan : ∀ v : Fin n, q v ∈ Submodule.span ℝ (Set.range (fun j => q (g j))) := by
      change LinearIndependent ℝ (fun j => q (g j)) at hauxiliary
      have htop := hauxiliary.span_eq_top_of_card_eq_finrank' (by simp)
      intro v
      rw [htop]
      exact Submodule.mem_top
    have hGrel : globalRelationSpace q SG ≤ Submodule.span ℝ (Set.range (H.matrix q)) := by
      apply globalRelationSpace_le_projectedHeightMatrix H.templates q SG g hauxiliary
        (fun j => (mem_projectedFaceLabels e G.val _).mpr (hgmem j))
        (fun v _ => hGspan v)
      intro v hv hvg
      obtain ⟨i, hi⟩ := hcovered v hv hvg
      have heq : H.matrix q i = fundamentalRow q g v := by
        change fundamentalRow q (H.templates i).frame (H.templates i).vertex = _
        rw [hi]
      rw [← heq]
      exact Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨plane, hRplane⟩ := exists_plane_containing_avoiding_polygon P a R haR
    have hRrank : subsetRank q SR ≤ 3 :=
      projected_incidence_rank_upper e q hq plane SR (fun i hi =>
        hRplane ((mem_projectedFaceLabels e _ i).mp hi))
    have hRdim := globalRelationSpace_finrank q SR
    have hRnonzero : globalRelationSpace q SR ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hRdim
      change 4 ≤ SR.card at hRcard
      omega
    obtain ⟨v, hv, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hRnonzero
    have hvF : v ∈ U := globalRelationSpace_mono q
      (projectedFaceLabels_mono e _ F.val hRF) hv
    have hvW : v ∈ Submodule.span ℝ (Set.range (H.matrix q)) := hGrel
      (globalRelationSpace_mono q (projectedFaceLabels_mono e _ G.val hRG) hv)
    have hframele : Submodule.span ℝ (Set.range (fun j => q (b j))) ≤
        Submodule.span ℝ (q '' (↑SF : Set (Fin n))) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact Submodule.subset_span ⟨b j,
        (mem_projectedFaceLabels e F.val _).mpr (hmem j), rfl⟩
    have hfrank : finrank ℝ (Submodule.span ℝ (Set.range (fun j => q (b j)))) = 4 := by
      change LinearIndependent ℝ (fun j => q (b j)) at hframe
      simpa only [Fintype.card_fin] using finrank_span_eq_card hframe
    have hlow : 4 ≤ subsetRank q SF := by
      have hh := Submodule.finrank_mono hframele
      rw [hfrank] at hh
      exact hh
    have hdim := globalRelationSpace_finrank q SF
    have hUpos : finrank ℝ U ≠ 0 := by
      intro hz
      have hbot := Submodule.finrank_eq_zero.mp hz
      exact hvne (by simpa only [hbot, Submodule.mem_bot] using hvF)
    have hUdim : finrank ℝ U = 1 := by
      change finrank ℝ U + subsetRank q SF = SF.card at hdim
      change SF.card ≤ 5 at hcard
      omega
    change U ≤ Submodule.span ℝ (Set.range (H.matrix q))
    rw [eq_span_singleton_of_mem_of_finrank_eq_one hUdim hvF hvne]
    exact Submodule.span_le.mpr (fun x hx => by
      have heq : x = v := Set.mem_singleton_iff.mp hx
      subst x
      exact hvW)

end ProjectionFacetHeightCoverage

/-- The full finite incidence and height certificate. All fields can be
transported along an actual labelled face-lattice equivalence. -/
structure ActualProjectionReconstructionCertificate
    (e : Fin n ≃ ProjectionPoint P a) (c : ℕ) where
  incidence : ActualProjectionDeletionCertificate P a
  heights : ActualHeightRowCertificate e c
  facet : ∀ F : AvoidingProjectionFacet P a, ProjectionFacetHeightCoverage e heights F.val

namespace ActualProjectionReconstructionCertificate

variable {e : Fin n ≃ ProjectionPoint P a}

def Allowed (K : ActualProjectionReconstructionCertificate e c) : Set (Fin n → Fin 4 → ℝ) :=
  {q | PreservesProjectedIncidences e q ∧
    (∀ i, LinearIndependent ℝ (fun j => q ((K.heights.rows i).frame j))) ∧
    ∀ F : AvoidingProjectionFacet P a,
      LinearIndependent ℝ (fun j => q ((K.facet F).frame j)) ∧
        LinearIndependent ℝ (fun j => q ((K.facet F).auxiliaryFrame j))}

theorem eventually_coverage_frames (K : ActualProjectionReconstructionCertificate e c)
    (D : VertexProjectionChart P a) (hP : P.IsFullDim) :
    ∀ᶠ q in 𝓝 (D.projectedFamily e), ∀ F : AvoidingProjectionFacet P a,
      LinearIndependent ℝ (fun j => q ((K.facet F).frame j)) ∧
        LinearIndependent ℝ (fun j => q ((K.facet F).auxiliaryFrame j)) := by
  apply eventually_all.mpr
  intro F
  have hc : Continuous (fun q : Fin n → Fin 4 → ℝ => fun j => q ((K.facet F).frame j)) :=
    continuous_pi fun j => continuous_apply ((K.facet F).frame j)
  have hg : Continuous (fun q : Fin n → Fin 4 → ℝ => fun j => q ((K.facet F).auxiliaryFrame j)) :=
    continuous_pi fun j => continuous_apply ((K.facet F).auxiliaryFrame j)
  exact (hc.continuousAt.tendsto.eventually
    ((K.facet F).frame_certificate.independent e _ D hP).eventually).and
      (hg.continuousAt.tendsto.eventually
        ((K.facet F).auxiliaryFrame_certificate.independent e _ D hP).eventually)

theorem rational_projected_density (K : ActualProjectionReconstructionCertificate e c)
    (D : VertexProjectionChart P a) (hP : P.IsFullDim) :
    D.projectedFamily e ∈ closure
      {q : Fin n → Fin 4 → ℝ | RationalCoordinates q ∧ q ∈ K.Allowed} := by
  have hbase := projected_configuration_rational_density P hP a D e K.incidence
  have hopen := (K.heights.eventually_frames_independent D hP).and
    (K.eventually_coverage_frames D hP)
  have hcl := mem_closure_inter_of_eventually hbase hopen
  apply closure_mono ?_ hcl
  intro q hq
  exact ⟨hq.1.1, hq.1.2, hq.2.1, hq.2.2⟩

theorem allowed_ordinary_rank (K : ActualProjectionReconstructionCertificate e c)
    (q : Fin n → Fin 4 → ℝ) (hq : q ∈ K.Allowed)
    (F : OrdinaryProjectionPlane P a) :
    subsetRank q (projectedFaceLabels e F.val.val) ≤ 3 :=
  projected_incidence_rank_upper e q hq.1 (Sum.inl F)
    (projectedFaceLabels e F.val.val)
    (fun i hi => (mem_projectedFaceLabels e F.val.val i).mp hi)

theorem allowed_complete_relations (K : ActualProjectionReconstructionCertificate e c)
    (q : Fin n → Fin 4 → ℝ) (hq : q ∈ K.Allowed)
    (F : AvoidingProjectionFacet P a) :
    globalRelationSpace q (projectedFaceLabels e F.val.val) ≤
      Submodule.span ℝ (Set.range (K.heights.matrix q)) :=
  (K.facet F).complete_relations q hq.1 hq.2.1 (hq.2.2 F).1 (hq.2.2 F).2

end ActualProjectionReconstructionCertificate
end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart12
