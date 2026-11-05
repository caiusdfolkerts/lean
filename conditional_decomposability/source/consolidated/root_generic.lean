module
public import consolidated.deletion_geometry
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Tactic.Continuity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.IntermediateValue

set_option Elab.async false

section BundlePart0
/- Source: Papers/FiniteEnvelopeLabels.lean -/







@[expose] public section

/-!
# Coherent labels on finite upper envelopes

No choice of a normal fan is assumed.  A finite collection of closed
maximizer regions covers the parameter line.  If the labels of tied
maximizers agree, connectedness forces the same label at any two
maximizers, even across all changes of maximizing vertex.
-/

noncomputable section
namespace Papers.FiniteEnvelopeLabels

open Set
open scoped Classical

theorem labels_eq_of_finite_closed_cover
    {X I Z : Type*} [TopologicalSpace X] [PreconnectedSpace X] [Finite I]
    (region : I → Set X) (label : I → Z)
    (hclosed : ∀ i, IsClosed (region i))
    (hcover : ∀ x, ∃ i, x ∈ region i)
    (hcoherent : ∀ i j, (region i ∩ region j).Nonempty → label i = label j)
    (i j : I) (hi : (region i).Nonempty) (hj : (region j).Nonempty) :
    label i = label j := by
  by_contra hij
  let A := {k : I // label k = label i}
  let B := {k : I // label k ≠ label i}
  let U : Set X := ⋃ k : A, region k.val
  let V : Set X := ⋃ k : B, region k.val
  have hU : IsClosed U := isClosed_iUnion_of_finite (fun k : A => hclosed k.val)
  have hV : IsClosed V := isClosed_iUnion_of_finite (fun k : B => hclosed k.val)
  have hUV : (Set.univ : Set X) ⊆ U ∪ V := by
    intro x hx
    obtain ⟨k,hk⟩ := hcover x
    by_cases he : label k = label i
    · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨k,he⟩,hk⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨k,he⟩,hk⟩)
  obtain ⟨x,hxi⟩ := hi
  obtain ⟨y,hyj⟩ := hj
  have hUn : ((Set.univ : Set X) ∩ U).Nonempty :=
    ⟨x,Set.mem_univ x,Set.mem_iUnion.mpr ⟨⟨i,rfl⟩,hxi⟩⟩
  have hVn : ((Set.univ : Set X) ∩ V).Nonempty :=
    ⟨y,Set.mem_univ y,Set.mem_iUnion.mpr ⟨⟨j,Ne.symm hij⟩,hyj⟩⟩
  obtain ⟨z,_hz,hzU,hzV⟩ :=
    isPreconnected_closed_iff.mp isPreconnected_univ U V hU hV hUV hUn hVn
  obtain ⟨a,ha⟩ := Set.mem_iUnion.mp hzU
  obtain ⟨b,hb⟩ := Set.mem_iUnion.mp hzV
  exact b.property ((hcoherent a.val b.val ⟨z,ha,hb⟩).symm.trans a.property)

def maximizingRegion {I : Type*} (intercept slope : I → ℝ) (i : I) : Set ℝ :=
  {t | ∀ j, intercept j + t * slope j ≤ intercept i + t * slope i}

theorem maximizingRegion_closed {I : Type*} (intercept slope : I → ℝ) (i : I) :
    IsClosed (maximizingRegion intercept slope i) := by
  have he : maximizingRegion intercept slope i = ⋂ j, {t : ℝ |
      intercept j + t * slope j ≤ intercept i + t * slope i} := by
    ext t
    simp only [maximizingRegion, Set.mem_setOf_eq, Set.mem_iInter]
  rw [he]
  apply isClosed_iInter
  intro j
  exact isClosed_le (continuous_const.add (continuous_id.mul continuous_const))
    (continuous_const.add (continuous_id.mul continuous_const))

theorem maximizingRegion_cover {I : Type*} [Fintype I] [Nonempty I]
    (intercept slope : I → ℝ) (t : ℝ) :
    ∃ i, t ∈ maximizingRegion intercept slope i := by
  obtain ⟨i,_hi,hmax⟩ := Finset.exists_max_image Finset.univ
    (fun j => intercept j + t * slope j) Finset.univ_nonempty
  exact ⟨i,fun j => hmax j (Finset.mem_univ j)⟩

theorem upper_envelope_labels_eq
    {I Z : Type*} [Fintype I] [Nonempty I]
    (intercept slope : I → ℝ) (label : I → Z)
    (hcoherent : ∀ t i j,
      t ∈ maximizingRegion intercept slope i →
      t ∈ maximizingRegion intercept slope j → label i = label j)
    (t u : ℝ) (i j : I)
    (hi : t ∈ maximizingRegion intercept slope i)
    (hj : u ∈ maximizingRegion intercept slope j) :
    label i = label j :=
  labels_eq_of_finite_closed_cover
    (maximizingRegion intercept slope) label
    (maximizingRegion_closed intercept slope)
    (maximizingRegion_cover intercept slope)
    (fun i j ⟨v,hvi,hvj⟩ => hcoherent v i j hvi hvj)
    i j ⟨t,hi⟩ ⟨u,hj⟩

end Papers.FiniteEnvelopeLabels

end
end
end BundlePart0

section BundlePart1
/- Source: Papers/HomogeneousSpanDimension.lean -/







@[expose] public section

namespace Papers.HomogeneousSpanDimension

open Set Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def liftPoint (x : E) : E × ℝ := (x, 1)

def liftSpan (S : Set E) : Submodule ℝ (E × ℝ) :=
  Submodule.span ℝ (liftPoint '' S)

theorem liftPoint_mem {S : Set E} {p : E} (hp : p ∈ S) :
    liftPoint p ∈ liftSpan S :=
  Submodule.subset_span ⟨p, hp, rfl⟩

theorem liftSpan_eq_direction_sup_point {S : Set E} {p : E} (hp : p ∈ S) :
    liftSpan S = (vectorSpan ℝ S).map (LinearMap.inl ℝ E ℝ) ⊔
      Submodule.span ℝ {liftPoint p} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨x, hx, rfl⟩
    refine Submodule.mem_sup.mpr
      ⟨(LinearMap.inl ℝ E ℝ) (x - p), ?_, liftPoint p, ?_, ?_⟩
    · exact Submodule.mem_map.mpr
        ⟨x - p, vsub_mem_vectorSpan ℝ hx hp, rfl⟩
    · exact Submodule.subset_span (Set.mem_singleton _)
    · ext <;> simp [liftPoint]
  · apply sup_le
    · rw [Submodule.map_le_iff_le_comap,
        vectorSpan_eq_span_vsub_set_right ℝ hp]
      apply Submodule.span_le.mpr
      rintro z ⟨x, hx, rfl⟩
      change (LinearMap.inl ℝ E ℝ) (x -ᵥ p) ∈ liftSpan S
      have h := (liftSpan S).sub_mem (liftPoint_mem hx) (liftPoint_mem hp)
      simpa [liftPoint, vsub_eq_sub] using h
    · apply Submodule.span_le.mpr
      intro z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      exact liftPoint_mem hp

theorem liftPoint_not_mem_direction {S : Set E} (p : E) :
    liftPoint p ∉ (vectorSpan ℝ S).map (LinearMap.inl ℝ E ℝ) := by
  intro h
  obtain ⟨x, hx, heq⟩ := Submodule.mem_map.mp h
  have hzero : (0 : ℝ) = 1 := by
    simpa [liftPoint] using congrArg Prod.snd heq
  exact zero_ne_one hzero

theorem finrank_map_inl (U : Submodule ℝ E) :
    finrank ℝ (U.map (LinearMap.inl ℝ E ℝ)) = finrank ℝ U := by
  have hinj : Function.Injective
      ((LinearMap.inl ℝ E ℝ).comp U.subtype) :=
    (LinearMap.inl_injective (R := ℝ) (M := E) (M₂ := ℝ)).comp
      Subtype.val_injective
  have he : ((LinearMap.inl ℝ E ℝ).comp U.subtype).range =
      U.map (LinearMap.inl ℝ E ℝ) := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u.val, u.property, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
  rw [← he]
  exact LinearMap.finrank_range_of_inj hinj

variable [FiniteDimensional ℝ E]

theorem finrank_liftSpan {S : Set E} (hS : S.Nonempty) :
    finrank ℝ (liftSpan S) = finrank ℝ (vectorSpan ℝ S) + 1 := by
  obtain ⟨p, hp⟩ := hS
  rw [liftSpan_eq_direction_sup_point hp,
    Submodule.finrank_sup_span_singleton (liftPoint_not_mem_direction p),
    finrank_map_inl]

/-- A genuine affine two-face spans a three-dimensional homogeneous
linear subspace.  Nonemptiness is explicit; no face data are encoded in
the definition of the homogeneous span. -/
theorem finrank_liftSpan_eq_three {S : Set E} (hS : S.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ S) = 2) :
    finrank ℝ (liftSpan S) = 3 := by
  rw [finrank_liftSpan hS, hdim]

end Papers.HomogeneousSpanDimension

end
end BundlePart1

section BundlePart2
/- Source: Papers/HomotheticFiberCore.lean -/









@[expose] public section

/-!
# The convex hull of positive homothetic fibres

These are statements about actual subsets of a product vector space.  The
scale and translation vary affinely over the quotient.  In particular,
there are no assumed face-lattice or Minkowski-summand certificates.
-/

namespace Papers.HomotheticFiberCore

open Set
open scoped BigOperators

variable {E F G : Type*}
  [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G]

theorem affine_map_weighted_sum {ι : Type*} [Fintype ι]
    (f : F →ᵃ[ℝ] G) (w : ι → ℝ) (p : ι → F)
    (hw : ∑ i, w i = 1) :
    f (∑ i, w i • p i) = ∑ i, w i • f (p i) := by
  have h := Finset.map_affineCombination Finset.univ p w hw f
  simpa only [Finset.affineCombination_eq_linear_combination _ _ _ hw,
    Function.comp_apply] using h

theorem weighted_sum_positive {ι : Type*} [Fintype ι]
    (w a : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (ha : ∀ i, 0 < a i) :
    0 < ∑ i, w i * a i := by
  classical
  have hpos : ∃ i, 0 < w i := by
    by_contra h
    push_neg at h
    have hz : ∀ i, w i = 0 :=
      fun i => le_antisymm (h i) (hw i)
    have : (1 : ℝ) = 0 := by simpa only [hz, Finset.sum_const_zero] using hw1.symm
    exact one_ne_zero this
  obtain ⟨i, hi⟩ := hpos
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hw j) (ha j).le)
    ⟨i, Finset.mem_univ i, mul_pos hi (ha i)⟩

def fibres (A : Set E) (Q : Set F)
    (scale : F →ᵃ[ℝ] ℝ) (shift : F →ᵃ[ℝ] E) : Set (E × F) :=
  {z | z.2 ∈ Q ∧ ∃ a ∈ A, z.1 = scale z.2 • a + shift z.2}

theorem positive_on_convexHull {Q : Set F}
    (scale : F →ᵃ[ℝ] ℝ)
    (hscale : ∀ q ∈ Q, 0 < scale q) :
    ∀ q ∈ convexHull ℝ Q, 0 < scale q := by
  intro q hq
  obtain ⟨ι, hi, w, p, hw, hw1, hp, hsum⟩ :=
    mem_convexHull_iff_exists_fintype.mp hq
  letI := hi
  rw [← hsum, affine_map_weighted_sum scale w p hw1]
  simpa only [smul_eq_mul] using
    weighted_sum_positive w (fun i => scale (p i)) hw hw1
      (fun i => hscale _ (hp i))

theorem convexHull_fibres {A : Set E} {Q : Set F}
    (hA : Convex ℝ A) (scale : F →ᵃ[ℝ] ℝ)
    (shift : F →ᵃ[ℝ] E) (hscale : ∀ q ∈ Q, 0 < scale q) :
    convexHull ℝ (fibres A Q scale shift) =
      fibres A (convexHull ℝ Q) scale shift := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨ι, hi, w, p, hw, hw1, hp, hsum⟩ :=
      mem_convexHull_iff_exists_fintype.mp hz
    letI := hi
    have hqsum : (∑ i, w i • (p i).2) = z.2 := by
      have h := congrArg (LinearMap.snd ℝ E F) hsum
      simpa only [map_sum, map_smul, LinearMap.snd_apply] using h
    have hxsum : (∑ i, w i • (p i).1) = z.1 := by
      have h := congrArg (LinearMap.fst ℝ E F) hsum
      simpa only [map_sum, map_smul, LinearMap.fst_apply] using h
    have hq : z.2 ∈ convexHull ℝ Q :=
      mem_convexHull_of_exists_fintype w (fun i => (p i).2)
        hw hw1 (fun i => (hp i).1) hqsum
    have hs : scale z.2 = ∑ i, w i * scale (p i).2 := by
      rw [← hqsum, affine_map_weighted_sum scale w (fun i => (p i).2) hw1]
      simp only [smul_eq_mul]
    have ht : shift z.2 = ∑ i, w i • shift (p i).2 := by
      rw [← hqsum, affine_map_weighted_sum shift w (fun i => (p i).2) hw1]
    have hspos : 0 < scale z.2 := positive_on_convexHull scale hscale _ hq
    have hsne : scale z.2 ≠ 0 := ne_of_gt hspos
    choose a ha hpa using fun i => (hp i).2
    let v : ι → ℝ := fun i => (w i * scale (p i).2) / scale z.2
    have hv : ∀ i, 0 ≤ v i := fun i =>
      div_nonneg (mul_nonneg (hw i) (hscale _ (hp i).1).le) hspos.le
    have hv1 : ∑ i, v i = 1 := by
      dsimp [v]
      rw [← Finset.sum_div, ← hs, div_self hsne]
    have ha' : (∑ i, v i • a i) ∈ A :=
      hA.sum_mem (fun i _ => hv i) hv1 (fun i _ => ha i)
    refine ⟨hq, ∑ i, v i • a i, ha', ?_⟩
    symm
    calc
      scale z.2 • (∑ i, v i • a i) + shift z.2 =
          (∑ i, (scale z.2 * v i) • a i) +
            (∑ i, w i • shift (p i).2) := by
              rw [Finset.smul_sum, ht]
              simp only [smul_smul]
      _ = (∑ i, (w i * scale (p i).2) • a i) +
            (∑ i, w i • shift (p i).2) := by
              congr 1
              apply Finset.sum_congr rfl
              intro i _
              congr 1
              dsimp [v]
              field_simp [hsne]
      _ = ∑ i, w i • (scale (p i).2 • a i + shift (p i).2) := by
              simp only [smul_add, smul_smul, Finset.sum_add_distrib]
      _ = ∑ i, w i • (p i).1 := by
              apply Finset.sum_congr rfl
              intro i _
              rw [hpa i]
      _ = z.1 := hxsum
  · rintro ⟨hq, a, ha, hz⟩
    obtain ⟨ι, hi, w, q, hw, hw1, hqQ, hsum⟩ :=
      mem_convexHull_iff_exists_fintype.mp hq
    letI := hi
    let p : ι → E × F := fun i => (scale (q i) • a + shift (q i), q i)
    refine mem_convexHull_of_exists_fintype w p hw hw1
      (fun i => ⟨hqQ i, a, ha, rfl⟩) ?_
    apply Prod.ext
    · change (∑ i, w i • p i).1 = z.1
      have hfirst : (∑ i, w i • p i).1 =
          ∑ i, w i • (scale (q i) • a + shift (q i)) := by
        exact (map_sum (LinearMap.fst ℝ E F) _ _).trans (by simp [p])
      rw [hfirst, hz]
      simp only [smul_add, smul_smul, Finset.sum_add_distrib]
      rw [← Finset.sum_smul]
      have hsc := affine_map_weighted_sum scale w q hw1
      have hsh := affine_map_weighted_sum shift w q hw1
      rw [hsum] at hsc hsh
      simpa only [smul_eq_mul, hsc, hsh]
    · have h := map_sum (LinearMap.snd ℝ E F) (fun i => w i • p i) Finset.univ
      simpa only [map_smul, LinearMap.snd_apply, p] using h.trans hsum

theorem fibres_mem_iff_normalized {A : Set E} {Q : Set F}
    {scale : F →ᵃ[ℝ] ℝ} {shift : F →ᵃ[ℝ] E} {z : E × F}
    (hs : scale z.2 ≠ 0) :
    z ∈ fibres A Q scale shift ↔
      z.2 ∈ Q ∧ (scale z.2)⁻¹ • (z.1 - shift z.2) ∈ A := by
  constructor
  · rintro ⟨hq, a, ha, hz⟩
    refine ⟨hq, ?_⟩
    simpa [hz, smul_smul, hs] using ha
  · rintro ⟨hq, ha⟩
    refine ⟨hq, _, ha, ?_⟩
    simp [smul_smul, hs]

theorem exists_violated_side {A : Set E} {Q : Set F} {I : Type*}
    (hA : Convex ℝ A) (scale : F →ᵃ[ℝ] ℝ) (shift : F →ᵃ[ℝ] E)
    (hscale : ∀ q ∈ Q, 0 < scale q)
    (normal : I → E →ₗ[ℝ] ℝ) (bound : I → ℝ)
    (hdescr : ∀ a, a ∈ A ↔ ∀ i, normal i a ≤ bound i)
    {z : E × F} (hq : z.2 ∈ convexHull ℝ Q)
    (hz : z ∉ convexHull ℝ (fibres A Q scale shift)) :
    ∃ i, scale z.2 * bound i + normal i (shift z.2) < normal i z.1 := by
  classical
  have hs := positive_on_convexHull scale hscale _ hq
  have hsne : scale z.2 ≠ 0 := ne_of_gt hs
  by_contra h
  push_neg at h
  apply hz
  rw [convexHull_fibres hA scale shift hscale,
    fibres_mem_iff_normalized hsne]
  refine ⟨hq, (hdescr _).mpr ?_⟩
  intro i
  apply (mul_le_mul_iff_of_pos_left hs).mp
  have heq : scale z.2 *
      normal i ((scale z.2)⁻¹ • (z.1 - shift z.2)) =
      normal i z.1 - normal i (shift z.2) := by
    simp only [map_smul, map_sub, smul_eq_mul]
    field_simp [hsne]
  rw [heq]
  linarith [h i]

end Papers.HomotheticFiberCore

end
end BundlePart2

section BundlePart3
/- Source: Papers/FaceSaturation.lean -/







@[expose] public section

noncomputable section
namespace Papers.FaceSaturation
open Finset Module
open scoped Classical

variable {I E : Type*} [DecidableEq I]
  [AddCommGroup E] [Module ℝ E]

/-- Independent edge directions already filling the direction space of a
face exclude every further incident edge direction from that space. -/
theorem index_mem_of_saturated_direction_space
    (f : I → E) (hli : LinearIndependent ℝ f)
    (U : Submodule ℝ E) [FiniteDimensional ℝ U]
    (S : Finset I) (hS : ∀ i ∈ S, f i ∈ U)
    (hcard : S.card = finrank ℝ U)
    {j : I} (hj : f j ∈ U) :
    j ∈ S := by
  by_contra hn
  let T : Finset I := insert j S
  have hT : ∀ i ∈ T, f i ∈ U := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hj
    · exact hS i hi
  let g : T → U := fun i => ⟨f i,hT i i.2⟩
  have hg : LinearIndependent ℝ g :=
    LinearIndependent.of_comp U.subtype
      (hli.comp (fun i : T => (i : I)) Subtype.val_injective)
  have hc := hg.fintype_card_le_finrank
  have hTc : Fintype.card T = S.card + 1 := by
    simp [T,Finset.card_insert_of_notMem hn]
  rw [hTc,hcard] at hc
  omega

section Graph
variable {V : Type*} (G : SimpleGraph V)

/-- This form only uses actual graph connectivity and closure under edges. -/
theorem closed_nonempty_subset_eq_univ
    (hconn : G.Connected) (S : Set V) (hS : S.Nonempty)
    (hclosed : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S) :
    S = Set.univ := by
  have walk_mem {x y : V} (p : G.Walk x y) : x ∈ S → y ∈ S := by
    induction p with
    | nil => exact fun h => h
    | cons h p ih => exact fun hx => ih (hclosed _ hx _ h)
  apply Set.eq_univ_iff_forall.mpr
  intro y
  obtain ⟨x,hx⟩ := hS
  obtain ⟨p⟩ := hconn.preconnected x y
  exact walk_mem p hx

end Graph
end Papers.FaceSaturation

end
end
end BundlePart3

section BundlePart4
/- Source: Papers/FaceIncidenceEuler.lean -/






@[expose] public section

/-!
# Euler's equation in dimension four from local three-dimensional equations

The relations are ordinary incidences between vertices, edges, two-faces,
and facets.  This double-counting lemma supplies no geometric hypotheses:
the vertex-figure and facet Euler equations must be proved for the actual
polytope before it can be applied.
-/

noncomputable section
namespace Papers.FaceIncidenceEuler

open scoped BigOperators Classical

variable {X Y V E R F : Type*}
  [Fintype X] [Fintype Y] [Fintype V] [Fintype E] [Fintype R] [Fintype F]

def rowCount (inc : X → Y → Prop) (x : X) : ℤ :=
  ∑ y, if inc x y then 1 else 0

def colCount (inc : X → Y → Prop) (y : Y) : ℤ :=
  ∑ x, if inc x y then 1 else 0

theorem total_rows_eq_columns (inc : X → Y → Prop) :
    (∑ x, rowCount inc x) = ∑ y, colCount inc y := by
  unfold rowCount colCount
  exact Finset.sum_comm

theorem sum_constant_columns (inc : X → Y → Prop) (k : ℤ)
    (h : ∀ y, colCount inc y = k) :
    (∑ x, rowCount inc x) = k * Fintype.card Y := by
  rw [total_rows_eq_columns]
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_comm _ _

theorem euler_four_from_local_three
    (ve : V → E → Prop) (vr : V → R → Prop) (vf : V → F → Prop)
    (er : E → R → Prop) (ef : E → F → Prop) (rf : R → F → Prop)
    (hendpoints : ∀ e, colCount ve e = 2)
    (hridge : ∀ r, rowCount rf r = 2)
    (hpolygon : ∀ r, colCount vr r = colCount er r)
    (hedgeFigure : ∀ e, rowCount er e = rowCount ef e)
    (hvertexEuler : ∀ v, rowCount ve v - rowCount vr v + rowCount vf v = 2)
    (hfacetEuler : ∀ f, colCount vf f - colCount ef f + colCount rf f = 2) :
    (Fintype.card V : ℤ) - Fintype.card E +
      Fintype.card R - Fintype.card F = 0 := by
  have he := sum_constant_columns ve 2 hendpoints
  have hr : (∑ f, colCount rf f) = 2 * Fintype.card R := by
    rw [← total_rows_eq_columns]
    simp only [hridge, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_comm _ _
  have h01 : (∑ v, rowCount vr v) = ∑ e, rowCount ef e := by
    rw [total_rows_eq_columns vr]
    calc
      (∑ r, colCount vr r) = ∑ r, colCount er r :=
        Finset.sum_congr rfl (fun r _ => hpolygon r)
      _ = ∑ e, rowCount er e := (total_rows_eq_columns er).symm
      _ = ∑ e, rowCount ef e :=
        Finset.sum_congr rfl (fun e _ => hedgeFigure e)
  have hv : (∑ v, rowCount ve v) - (∑ v, rowCount vr v) +
      (∑ v, rowCount vf v) = 2 * Fintype.card V := by
    calc
      _ = ∑ v, (rowCount ve v - rowCount vr v + rowCount vf v) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = ∑ _v : V, (2 : ℤ) :=
        Finset.sum_congr rfl (fun v _ => hvertexEuler v)
      _ = _ := by simp [mul_comm]
  have hf : (∑ f, colCount vf f) - (∑ f, colCount ef f) +
      (∑ f, colCount rf f) = 2 * Fintype.card F := by
    calc
      _ = ∑ f, (colCount vf f - colCount ef f + colCount rf f) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = ∑ _f : F, (2 : ℤ) :=
        Finset.sum_congr rfl (fun f _ => hfacetEuler f)
      _ = _ := by simp [mul_comm]
  rw [he, h01] at hv
  rw [← total_rows_eq_columns vf, ← total_rows_eq_columns ef, hr] at hf
  omega

/-- In dimension three, these are the numerical consequences used by the
small-facet template enumeration once Euler and the genuine incidence
bounds have been supplied. -/
theorem three_dimensional_facet_bound
    {n e f : ℤ} (heuler : n - e + f = 2)
    (hfaceDegree : 3 * f ≤ 2 * e) :
    f ≤ 2 * n - 4 := by
  omega

theorem short_three_dimensional_triangle_bound
    {n e f : ℤ} (hn : n ≤ 7) (heuler : n - e + f = 2)
    (hvertexDegree : 3 * n ≤ 2 * e) :
    2 * e < 4 * f := by
  omega

theorem exists_triangular_face_of_counts
    {I : Type*} [Fintype I] (corners : I → ℕ)
    {n e f : ℤ} (hf : (Fintype.card I : ℤ) = f) (hn : n ≤ 7)
    (heuler : n - e + f = 2) (hvertexDegree : 3 * n ≤ 2 * e)
    (hinc : (∑ i, (corners i : ℤ)) = 2 * e)
    (hmin : ∀ i, 3 ≤ corners i) :
    ∃ i, corners i = 3 := by
  by_contra h
  have hfour : ∀ i, (4 : ℤ) ≤ corners i := by
    intro i
    have hne : corners i ≠ 3 := fun hi => h ⟨i, hi⟩
    have hm := hmin i
    omega
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hfour i)
  have hbound := short_three_dimensional_triangle_bound hn heuler hvertexDegree
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hf, hinc] at hsum
  omega

end Papers.FaceIncidenceEuler

end
end
end BundlePart4

section BundlePart5
/- Source: Papers/MinkowskiExposedFaces.lean -/





@[expose] public section

/-!
# Actual exposed faces of Minkowski sums

The face is the set of maximizers of a linear functional on the actual
set of points.  These statements have no face-lattice or summand
certificates among their hypotheses.  In finite-dimensional Euclidean
space they agree with Mathlib's continuous exposed-face definition.
-/

namespace Papers.MinkowskiFaces

open Set
open scoped Pointwise

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

def maxFace (S : Set E) (u : E →ₗ[ℝ] ℝ) : Set E :=
  {x ∈ S | ∀ y ∈ S, u y ≤ u x}

theorem maxFace_subset (S : Set E) (u : E →ₗ[ℝ] ℝ) :
    maxFace S u ⊆ S := fun _ h => h.1

theorem components_maximize {S T : Set E} {u : E →ₗ[ℝ] ℝ}
    {a b : E} (ha : a ∈ S) (hb : b ∈ T)
    (hab : a + b ∈ maxFace (S + T) u) :
    a ∈ maxFace S u ∧ b ∈ maxFace T u := by
  constructor
  · refine ⟨ha, ?_⟩
    intro x hx
    have h := hab.2 (x + b) (Set.mem_add.mpr ⟨x, hx, b, hb, rfl⟩)
    simpa only [map_add, add_le_add_iff_right] using h
  · refine ⟨hb, ?_⟩
    intro y hy
    have h := hab.2 (a + y) (Set.mem_add.mpr ⟨a, ha, y, hy, rfl⟩)
    simpa only [map_add, add_le_add_iff_left] using h

theorem maxFace_add (S T : Set E) (u : E →ₗ[ℝ] ℝ) :
    maxFace (S + T) u = maxFace S u + maxFace T u := by
  ext z
  constructor
  · intro hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hz.1
    obtain ⟨hfa, hfb⟩ := components_maximize ha hb hz
    exact Set.mem_add.mpr ⟨a, hfa, b, hfb, rfl⟩
  · intro hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hz
    refine ⟨Set.mem_add.mpr ⟨a, ha.1, b, hb.1, rfl⟩, ?_⟩
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_add.mp hz
    simpa only [map_add] using add_le_add (ha.2 x hx) (hb.2 y hy)

theorem maxFace_eq_of_constant (S : Set E) (u : E →ₗ[ℝ] ℝ)
    (h : ∀ x ∈ S, ∀ y ∈ S, u x = u y) :
    maxFace S u = S := by
  apply Set.Subset.antisymm (maxFace_subset S u)
  intro x hx
  exact ⟨hx, fun y hy => le_of_eq (h y hy x hx)⟩

theorem maxFace_add_of_constant_left (S T : Set E) (u : E →ₗ[ℝ] ℝ)
    (h : ∀ x ∈ S, ∀ y ∈ S, u (x - y) = 0) :
    maxFace (S + T) u = S + maxFace T u := by
  rw [maxFace_add, maxFace_eq_of_constant S u]
  intro x hx y hy
  exact sub_eq_zero.mp (by simpa only [map_sub] using h x hx y hy)

theorem maxFace_linear_image (S : Set E) (L : E →ₗ[ℝ] F)
    (u : F →ₗ[ℝ] ℝ) :
    maxFace (L '' S) u = L '' maxFace S (u.comp L) := by
  ext z
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hmax⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro y hy
    exact hmax (L y) ⟨y, hy, rfl⟩
  · rintro ⟨x, ⟨hx, hmax⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro z ⟨y, hy, rfl⟩
    exact hmax y hy

theorem maxFace_translate (S : Set E) (u : E →ₗ[ℝ] ℝ) (b : E) :
    maxFace ((fun x => x + b) '' S) u =
      (fun x => x + b) '' maxFace S u := by
  ext z
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hmax⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro y hy
    have h := hmax (y + b) ⟨y, hy, rfl⟩
    simpa only [map_add, add_le_add_iff_right] using h
  · rintro ⟨x, ⟨hx, hmax⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro z ⟨y, hy, rfl⟩
    simpa only [map_add, add_le_add_iff_right] using hmax y hy

theorem maxFace_positive_smul (S : Set E) (u : E →ₗ[ℝ] ℝ)
    {a : ℝ} (ha : 0 < a) :
    maxFace ((fun x => a • x) '' S) u =
      (fun x => a • x) '' maxFace S u := by
  ext z
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hmax⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro y hy
    have h := hmax (a • y) ⟨y, hy, rfl⟩
    exact (mul_le_mul_iff_of_pos_left ha).mp (by simpa only [map_smul, smul_eq_mul] using h)
  · rintro ⟨x, ⟨hx, hmax⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro z ⟨y, hy, rfl⟩
    simpa only [map_smul, smul_eq_mul] using
      (mul_le_mul_iff_of_pos_left ha).mpr (hmax y hy)

section Continuous
variable [TopologicalSpace E]

theorem maxFace_eq_toExposed (S : Set E) (u : E →L[ℝ] ℝ) :
    maxFace S u.toLinearMap = u.toExposed S := rfl

end Continuous
end Papers.MinkowskiFaces

end
end BundlePart5

section BundlePart6
/- Source: Papers/SimpleCornerFaces.lean -/








@[expose] public section

noncomputable section
namespace Papers.SimpleCornerFaces
open Finset Set Module Papers.MinkowskiFaces
open scoped BigOperators Classical Pointwise

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [AddCommGroup E] [Module ℝ E]

def selectedSpan (b : Basis I ℝ E) (S : Finset I) : Submodule ℝ E :=
  Submodule.span ℝ (b '' (S : Set I))

theorem mem_selectedSpan_iff (b : Basis I ℝ E) (S : Finset I) (x : E) :
    x ∈ selectedSpan b S ↔ ∀ i ∉ S, b.repr x i = 0 := by
  rw [selectedSpan,b.mem_span_image]
  constructor
  · intro h i hi
    by_contra hn
    exact hi (h (Finsupp.mem_support_iff.mpr hn))
  · intro h i hi
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hi) (h i hn)

def coordinate (b : Basis I ℝ E) (i : I) : E →ₗ[ℝ] ℝ :=
  (Finsupp.lapply i).comp b.repr.toLinearMap

def cornerNormal (b : Basis I ℝ E) (S : Finset I) : E →ₗ[ℝ] ℝ :=
  -(∑ i ∈ Sᶜ, coordinate b i)

theorem cornerNormal_apply (b : Basis I ℝ E) (S : Finset I) (x : E) :
    cornerNormal b S x = -(∑ i ∈ Sᶜ, b.repr x i) := by
  simp [cornerNormal,coordinate]

theorem cornerNormal_le (b : Basis I ℝ E) (S : Finset I)
    {v x : E} (hx : ∀ i, 0 ≤ b.repr (x - v) i) :
    cornerNormal b S x ≤ cornerNormal b S v := by
  have h : cornerNormal b S (x - v) ≤ 0 := by
    rw [cornerNormal_apply]
    exact neg_nonpos.mpr (Finset.sum_nonneg fun i _ => hx i)
  simpa only [map_sub,sub_nonpos] using h

theorem maxFace_eq_corner_section
    (b : Basis I ℝ E) (S : Finset I) (P : Set E) (v : E)
    (hv : v ∈ P) (hcone : ∀ x ∈ P, ∀ i, 0 ≤ b.repr (x - v) i) :
    maxFace P (cornerNormal b S) =
      {x ∈ P | x - v ∈ selectedSpan b S} := by
  ext x
  constructor
  · rintro ⟨hx,hmax⟩
    refine ⟨hx, (mem_selectedSpan_iff b S (x-v)).mpr ?_⟩
    have he : cornerNormal b S x = cornerNormal b S v :=
      (cornerNormal_le b S (hcone x hx)).antisymm (hmax v hv)
    have hz : (∑ i ∈ Sᶜ, b.repr (x-v) i) = 0 := by
      have h : cornerNormal b S (x-v) = 0 := by rw [map_sub,he,sub_self]
      rw [cornerNormal_apply,neg_eq_zero] at h
      exact h
    have hz' := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Sᶜ) => hcone x hx i)).mp hz
    intro i hi
    exact hz' i (Finset.mem_compl.mpr hi)
  · rintro ⟨hx,hspan⟩
    refine ⟨hx,?_⟩
    have hzero := (mem_selectedSpan_iff b S (x-v)).mp hspan
    have he : cornerNormal b S x = cornerNormal b S v := by
      apply sub_eq_zero.mp
      rw [← map_sub,cornerNormal_apply]
      apply neg_eq_zero.mpr
      exact Finset.sum_eq_zero fun i hi => hzero i (Finset.mem_compl.mp hi)
    intro y hy
    rw [he]
    exact cornerNormal_le b S (hcone y hy)

theorem selectedSpan_finrank (b : Basis I ℝ E) (S : Finset I) :
    finrank ℝ (selectedSpan b S) = S.card := by
  have he : b '' (S : Set I) = Set.range (fun i : S => b i) := by
    ext x
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,hi⟩,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨i,i.2,rfl⟩
  rw [selectedSpan,he]
  have h := finrank_span_eq_card (b.linearIndependent.comp
    (fun i : S => (i : I)) Subtype.val_injective)
  simpa only [Function.comp_def, Fintype.card_coe] using h

theorem corner_section_vectorSpan
    (b : Basis I ℝ E) (S : Finset I) (P : Set E) (v : E)
    (hv : v ∈ P) (hneighbors : ∀ i ∈ S, v + b i ∈ P) :
    vectorSpan ℝ {x ∈ P | x - v ∈ selectedSpan b S} = selectedSpan b S := by
  apply le_antisymm
  · rw [vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro z ⟨x,hx,y,hy,rfl⟩
    have h := (selectedSpan b S).sub_mem hx.2 hy.2
    change x - y ∈ selectedSpan b S
    convert h using 1 <;> abel
  · apply Submodule.span_le.mpr
    rintro x ⟨i,hi,rfl⟩
    have hbi : b i ∈ selectedSpan b S := Submodule.subset_span ⟨i,hi,rfl⟩
    have hvF : v ∈ {x ∈ P | x-v ∈ selectedSpan b S} :=
      ⟨hv,by simp⟩
    have hiF : v + b i ∈ {x ∈ P | x-v ∈ selectedSpan b S} :=
      ⟨hneighbors i hi,by simpa only [add_sub_cancel_left] using hbi⟩
    change b i ∈ vectorSpan ℝ {x ∈ P | x-v ∈ selectedSpan b S}
    simpa only [vsub_eq_sub,add_sub_cancel_left] using vsub_mem_vectorSpan ℝ hiF hvF

theorem corner_section_dimension
    (b : Basis I ℝ E) (S : Finset I) (P : Set E) (v : E)
    (hv : v ∈ P) (hneighbors : ∀ i ∈ S, v + b i ∈ P) :
    finrank ℝ (vectorSpan ℝ {x ∈ P | x-v ∈ selectedSpan b S}) = S.card := by
  rw [corner_section_vectorSpan b S P v hv hneighbors,selectedSpan_finrank]

theorem exposed_corner_of_basis_cone
    (b : Basis I ℝ E) (S : Finset I) (P : Set E) (v : E)
    (hv : v ∈ P) (hcone : ∀ x ∈ P, ∀ i, 0 ≤ b.repr (x-v) i)
    (hneighbors : ∀ i ∈ S, v + b i ∈ P) :
    ∃ u : E →ₗ[ℝ] ℝ,
      maxFace P u = {x ∈ P | x-v ∈ selectedSpan b S} ∧
      vectorSpan ℝ (maxFace P u) = selectedSpan b S ∧
      finrank ℝ (vectorSpan ℝ (maxFace P u)) = S.card := by
  refine ⟨cornerNormal b S,maxFace_eq_corner_section b S P v hv hcone,?_,?_⟩
  · rw [maxFace_eq_corner_section b S P v hv hcone]
    exact corner_section_vectorSpan b S P v hv hneighbors
  · rw [maxFace_eq_corner_section b S P v hv hcone]
    exact corner_section_dimension b S P v hv hneighbors

end Papers.SimpleCornerFaces

end
end
end BundlePart6

section BundlePart7
/- Source: Papers/HomotheticFiberSide.lean -/






@[expose] public section

/-!
# Side inequalities and exposed faces beyond a fibre core

The side normal has the prescribed restriction to the summand direction.
Its exposed face in the Minkowski sum therefore contains a translate of
the corresponding exposed summand face.  If a point violates the side
inequality, that whole exposed face is disjoint from the fibre core.
-/

namespace Papers.HomotheticFiberSide

open Set Papers.MinkowskiFaces Papers.HomotheticFiberCore
open scoped Pointwise

variable {E F : Type*}
  [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

theorem affine_apply_eq (f : F →ᵃ[ℝ] E) (q : F) :
    f q = f.linear q + f 0 := by
  simpa using f.map_vadd (0 : F) q

def sideNormal (scale : F →ᵃ[ℝ] ℝ) (shift : F →ᵃ[ℝ] E)
    (u : E →ₗ[ℝ] ℝ) (c : ℝ) : E × F →ₗ[ℝ] ℝ :=
  u.comp (LinearMap.fst ℝ E F) -
    (c • scale.linear + u.comp shift.linear).comp (LinearMap.snd ℝ E F)

def sideConstant (scale : F →ᵃ[ℝ] ℝ) (shift : F →ᵃ[ℝ] E)
    (u : E →ₗ[ℝ] ℝ) (c : ℝ) : ℝ :=
  c * scale 0 + u (shift 0)

theorem sideNormal_apply (scale : F →ᵃ[ℝ] ℝ) (shift : F →ᵃ[ℝ] E)
    (u : E →ₗ[ℝ] ℝ) (c : ℝ) (z : E × F) :
    sideNormal scale shift u c z =
      u z.1 - (c * scale.linear z.2 + u (shift.linear z.2)) := rfl

theorem sideNormal_le_iff (scale : F →ᵃ[ℝ] ℝ) (shift : F →ᵃ[ℝ] E)
    (u : E →ₗ[ℝ] ℝ) (c : ℝ) (z : E × F) :
    sideNormal scale shift u c z ≤ sideConstant scale shift u c ↔
      u z.1 ≤ scale z.2 * c + u (shift z.2) := by
  rw [sideNormal_apply, sideConstant,
    affine_apply_eq scale z.2, affine_apply_eq shift z.2, map_add]
  ring_nf
  constructor <;> intro h <;> linarith

theorem sideNormal_restrict (scale : F →ᵃ[ℝ] ℝ) (shift : F →ᵃ[ℝ] E)
    (u : E →ₗ[ℝ] ℝ) (c : ℝ) :
    (sideNormal scale shift u c).comp (LinearMap.inl ℝ E F) = u := by
  ext a
  simp [sideNormal]

theorem side_inequality_on_core {A : Set E} {Q : Set F}
    (hA : Convex ℝ A) (scale : F →ᵃ[ℝ] ℝ) (shift : F →ᵃ[ℝ] E)
    (hscale : ∀ q ∈ Q, 0 < scale q)
    (u : E →ₗ[ℝ] ℝ) (c : ℝ) (hu : ∀ a ∈ A, u a ≤ c) :
    ∀ z ∈ convexHull ℝ (fibres A Q scale shift),
      sideNormal scale shift u c z ≤ sideConstant scale shift u c := by
  intro z hz
  rw [convexHull_fibres hA scale shift hscale] at hz
  obtain ⟨hq, a, ha, hza⟩ := hz
  rw [sideNormal_le_iff, hza, map_add, map_smul, smul_eq_mul]
  have hm := mul_le_mul_of_nonneg_left (hu a ha)
      (positive_on_convexHull scale hscale _ hq).le
  linarith

theorem maxFace_disjoint_of_strict_witness
    {P C : Set (E × F)} (u : E × F →ₗ[ℝ] ℝ) (c : ℝ)
    (hC : ∀ z ∈ C, u z ≤ c)
    (hw : ∃ w ∈ P, c < u w) :
    Disjoint (maxFace P u) C := by
  refine Set.disjoint_left.mpr ?_
  intro z hz hzc
  obtain ⟨w, hwP, hwc⟩ := hw
  have hmax := hz.2 w hwP
  exact (not_lt_of_ge ((hC z hzc).trans' hmax)) hwc

theorem maxFace_embedded (A : Set E) (scale : F →ᵃ[ℝ] ℝ)
    (shift : F →ᵃ[ℝ] E) (u : E →ₗ[ℝ] ℝ) (c : ℝ) :
    maxFace ((LinearMap.inl ℝ E F) '' A) (sideNormal scale shift u c) =
      (LinearMap.inl ℝ E F) '' maxFace A u := by
  rw [maxFace_linear_image, sideNormal_restrict]

theorem contains_translated_summand_face
    (A : Set E) (B : Set (E × F)) (scale : F →ᵃ[ℝ] ℝ)
    (shift : F →ᵃ[ℝ] E) (u : E →ₗ[ℝ] ℝ) (c : ℝ)
    (hne : (maxFace (((LinearMap.inl ℝ E F) '' A) + B)
      (sideNormal scale shift u c)).Nonempty) :
    ∃ b ∈ maxFace B (sideNormal scale shift u c),
      (fun a => (LinearMap.inl ℝ E F) a + b) '' maxFace A u ⊆
        maxFace (((LinearMap.inl ℝ E F) '' A) + B)
          (sideNormal scale shift u c) := by
  rw [maxFace_add, maxFace_embedded] at hne ⊢
  obtain ⟨z, hz⟩ := hne
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hz
  refine ⟨b, hb, ?_⟩
  rintro x ⟨a, ha, rfl⟩
  exact Set.mem_add.mpr
    ⟨(LinearMap.inl ℝ E F) a, ⟨a, ha, rfl⟩, b, hb, rfl⟩

theorem exposed_translate_outside_core
    {A : Set E} {Q : Set F} (B : Set (E × F))
    (hA : Convex ℝ A) (scale : F →ᵃ[ℝ] ℝ) (shift : F →ᵃ[ℝ] E)
    (hscale : ∀ q ∈ Q, 0 < scale q)
    (u : E →ₗ[ℝ] ℝ) (c : ℝ) (hu : ∀ a ∈ A, u a ≤ c)
    (hw : ∃ w ∈ ((LinearMap.inl ℝ E F) '' A) + B,
      sideConstant scale shift u c < sideNormal scale shift u c w)
    (hne : (maxFace (((LinearMap.inl ℝ E F) '' A) + B)
      (sideNormal scale shift u c)).Nonempty) :
    ∃ b ∈ maxFace B (sideNormal scale shift u c),
      ∀ a ∈ maxFace A u,
        (LinearMap.inl ℝ E F) a + b ∈
          maxFace (((LinearMap.inl ℝ E F) '' A) + B)
            (sideNormal scale shift u c) ∧
        (LinearMap.inl ℝ E F) a + b ∉
          convexHull ℝ (fibres A Q scale shift) := by
  obtain ⟨b, hb, hsub⟩ :=
    contains_translated_summand_face A B scale shift u c hne
  have hdis := maxFace_disjoint_of_strict_witness
    (sideNormal scale shift u c) (sideConstant scale shift u c)
    (side_inequality_on_core hA scale shift hscale u c hu) hw
  refine ⟨b, hb, ?_⟩
  intro a ha
  have hm := hsub ⟨a, ha, rfl⟩
  exact ⟨hm, fun hc => Set.disjoint_left.mp hdis hm hc⟩

end Papers.HomotheticFiberSide

end
end BundlePart7

