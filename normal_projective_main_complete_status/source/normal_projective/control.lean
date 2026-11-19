module
public import normal_projective.stable_incidence
public import normal_projective.unit_normalization
public import normal_projective.normalization_topology
public import normal_projective.elementary_projectivity
public import normal_projective.local_control
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import normal_projective.face_correspondence
public import normal_projective.simple_vertices
public import Mathlib.Analysis.LocallyConvex.Separation
public import normal_projective.halfspace_faces

/-! Exact source consolidation of the canonical and geometric integration layer. -/
@[expose] public section
noncomputable section

/- Source: NormalProjective/RegularStability.lean -/
section
/-! # Irredundant labelled facets persist, and normalization preserves their order -/
open Set Filter
open scoped Topology
namespace NormalProjective

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]

def StrictFacetPoints (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ) : Prop :=
  ∀ i, ∃ x ∈ halfspaceRegion f h,
    f i x = h i ∧ ∀ j, j ≠ i → f j x < h j

theorem strictFacetPoints_transfer
    (f g : ι → E →ₗ[ℝ] ℝ) (h k : ι → ℝ)
    (hc : IsCompact (halfspaceRegion f h))
    (e : HalfspaceVertices f h ≃ HalfspaceVertices g k)
    (hinc : ∀ (v : HalfspaceVertices f h) i, f i v.val = h i ↔ g i (e v).val = k i)
    (hstrict : StrictFacetPoints f h) : StrictFacetPoints g k := by
  classical
  intro i
  obtain ⟨x, hxP, hxi, hxs⟩ := hstrict i
  let F : HalfspaceFaces f h := ⟨tightFace f h {i}, tightFace_isExposed f h {i}⟩
  let G : Set E := tightFace g k {i}
  have hxF : x ∈ F.val := ⟨hxP, by simpa using hxi⟩
  have hGexp : IsExposed ℝ (halfspaceRegion g k) G := tightFace_isExposed g k {i}
  have hGn : G.Nonempty := by
    obtain ⟨v, hv⟩ := (F.property.isCompact hc).extremePoints_nonempty ⟨x, hxF⟩
    let w : HalfspaceVertices f h :=
      ⟨v, F.property.isExtreme.extremePoints_subset_extremePoints hv⟩
    refine ⟨(e w).val, (e w).property.1, ?_⟩
    have hwi : f i w.val = h i := hv.1.2 i (Set.mem_singleton i)
    simpa using (hinc w i).mp hwi
  have hnot (j : ι) (hji : j ≠ i) : ¬∀ y ∈ G, g j y = k j := by
    have hv : ∃ v : HalfspaceVertices f h, v.val ∈ F.val ∧ f j v.val ≠ h j := by
      by_contra hn
      let J : HalfspaceFaces f h := ⟨tightFace f h {j}, tightFace_isExposed f h {j}⟩
      have hFJ : F.val ⊆ J.val :=
        (halfspace_face_subset_iff_vertices f h hc F J).mpr (fun v hvF => by
          refine ⟨v.property.1, ?_⟩
          have hveq : f j v.val = h j := by
            by_contra hneq
            exact hn ⟨v, hvF, hneq⟩
          simpa using hveq)
      have heq : f j x = h j := (hFJ hxF).2 j (Set.mem_singleton j)
      exact (ne_of_lt (hxs j hji)) heq
    obtain ⟨v, hvF, hvj⟩ := hv
    intro hall
    have hvi : f i v.val = h i := hvF.2 i (Set.mem_singleton i)
    have hevi : g i (e v).val = k i := (hinc v i).mp hvi
    have hevG : (e v).val ∈ G := ⟨(e v).property.1, by simpa using hevi⟩
    exact hvj ((hinc v j).mpr (hall _ hevG))
  obtain ⟨y, hyG, hy⟩ := exists_common_tight_point g k hGn
    (hGexp.convex (convex_halfspaceRegion g k)) hGexp.subset
  refine ⟨y, hyG.1, hyG.2 i (Set.mem_singleton i), fun j hji => ?_⟩
  apply lt_of_le_of_ne (hyG.1 j)
  intro heq
  exact hnot j hji ((hy j).mp heq)

namespace UnitNormalization
variable {d : ℕ}

def faceOrderEquiv (p : RegularData d ι) :
    (presentation p).Faces ≃o
      HalfspaceFaces (fun i => (p.data.1 i).toLinearMap) p.data.2 where
  toFun F := ⟨F.val, by simpa only [presentation_carrier, dataRegion] using F.property⟩
  invFun F := ⟨F.val, by simpa only [presentation_carrier, dataRegion] using F.property⟩
  left_inv F := Subtype.ext rfl
  right_inv F := Subtype.ext rfl
  map_rel_iff' := Iff.rfl

theorem sameLabelledType_of_faceOrderIso (p q : RegularData d ι)
    (e : HalfspaceFaces (fun i => (p.data.1 i).toLinearMap) p.data.2 ≃o
      HalfspaceFaces (fun i => (q.data.1 i).toLinearMap) q.data.2)
    (he : ∀ i, e ⟨tightFace (fun j => (p.data.1 j).toLinearMap) p.data.2 {i},
          tightFace_isExposed _ _ _⟩ =
        ⟨tightFace (fun j => (q.data.1 j).toLinearMap) q.data.2 {i},
          tightFace_isExposed _ _ _⟩) :
    (presentation p).SameLabelledType (presentation q) := by
  refine ⟨(faceOrderEquiv p).trans (e.trans (faceOrderEquiv q).symm), ?_⟩
  intro i
  let F : HalfspaceFaces (fun j => (p.data.1 j).toLinearMap) p.data.2 :=
    ⟨tightFace (fun j => (p.data.1 j).toLinearMap) p.data.2 {i}, tightFace_isExposed _ _ _⟩
  refine ⟨(faceOrderEquiv p).symm F, ?_, ?_⟩
  · change F.val = (presentation p).facet i
    rw [presentation_facet]
    ext x
    simp [F, tightFace, dataRegion]
  · change ((faceOrderEquiv q).symm (e F)).val = (presentation q).facet i
    have hei := he i
    change e F = _ at hei
    rw [hei]
    rw [presentation_facet]
    ext x
    simp [faceOrderEquiv, tightFace, dataRegion]

end UnitNormalization

open UnitNormalization

/-- The stable neighborhood consists of actual irredundant realizations of the
same labelled face lattice, with a common bound on every carrier. -/
theorem normalized_regular_eventually_stable
    {d : ℕ} (p₀ : RegularData d ι)
    (f : ι → (Fin d → ℝ) →L[ℝ] ℝ) (hp₀ : p₀.data = (f, fun _ => 1))
    (hs : IsSimpleHalfspace (fun i => (f i).toLinearMap) (fun _ => 1)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ p : HalfspaceData ι (Fin d → ℝ) in 𝓝 (f, fun _ => 1),
        dataRegion p ⊆ Metric.closedBall 0 C ∧ (∀ i, 0 < p.2 i) ∧
        ∃ q : RegularData d ι, q.data = p ∧
          (presentation p₀).SameLabelledType (presentation q) := by
  classical
  have hc : IsCompact (dataRegion (f, fun _ => 1)) := hp₀ ▸ p₀.compact
  obtain ⟨C, hC, hevent⟩ := normalized_data_eventually_minor_stable f hc hs
  have hpos : ∀ᶠ p : HalfspaceData ι (Fin d → ℝ) in 𝓝 (f, fun _ => 1),
      ∀ i, 0 < p.2 i := by
    apply Filter.eventually_all.mpr
    intro i
    exact Filter.Tendsto.eventually_const_lt (by norm_num)
      ((continuous_apply i).comp continuous_snd).continuousAt
  refine ⟨C, hC, ?_⟩
  filter_upwards [hevent, hpos] with p hp hpos
  have hcq : IsCompact (dataRegion p) :=
    (isCompact_closedBall (0 : Fin d → ℝ) C).of_isClosed_subset (dataRegion_closed p) hp.1
  let e := stableVertexEquiv (f, fun _ => 1) p hc hs hp.2.2
  have he := stableVertexEquiv_incidence (f, fun _ => 1) p hc hs hp.2.2
  have hstrict₀ : StrictFacetPoints (fun i => (f i).toLinearMap) (fun _ => 1) := by
    have hh := p₀.strict_facet_point
    rw [hp₀] at hh
    exact hh
  have hstrict := strictFacetPoints_transfer (fun i => (f i).toLinearMap)
    (fun i => (p.1 i).toLinearMap) (fun _ => 1) p.2 hc e he hstrict₀
  let q : RegularData d ι := {
    data := p
    normal_ne_zero := by
      intro i hi
      obtain ⟨x, _, hxi, _⟩ := hstrict i
      have hz : p.2 i = 0 := by simpa [hi] using hxi.symm
      exact (ne_of_gt (hpos i)) hz
    compact := hcq
    full_dimensional := ⟨0, hp.2.1⟩
    strict_facet_point := hstrict }
  refine ⟨hp.1, hpos, q, rfl, ?_⟩
  let p₁ : RegularData d ι := {
    data := (f, fun _ => 1)
    normal_ne_zero := by
      have hh := p₀.normal_ne_zero
      rw [hp₀] at hh
      exact hh
    compact := hc
    full_dimensional := hp₀ ▸ p₀.full_dimensional
    strict_facet_point := hstrict₀ }
  have hp₁ : presentation p₀ = presentation p₁ := by
    have hext {P Q : CanonicalModel.Presentation d ι}
        (hn : P.normal = Q.normal) (hh : P.support = Q.support) : P = Q := by
      cases P
      cases Q
      cases hn
      cases hh
      rfl
    apply hext
    · change (fun i => unitRow (p₀.data.1 i)) = (fun i => unitRow (f i))
      rw [hp₀]
    · change (fun i => p₀.data.2 i / length (p₀.data.1 i)) =
        (fun i => 1 / length (f i))
      rw [hp₀]
  rw [hp₁]
  exact sameLabelledType_of_faceOrderIso p₁ q
    (halfspaceFaceOrderIso (fun i => (f i).toLinearMap)
      (fun i => (p.1 i).toLinearMap) (fun _ => 1) p.2 hc hcq e he)
    (fun i => halfspaceFaceOrderIso_facet _ _ _ _ _ _ _ _ i)

end NormalProjective

end

/- Source: NormalProjective/RealizationRelations.lean -/
section
/-! # Labelled face type is a genuine equivalence relation -/
open Set
namespace NormalProjective.CanonicalModel.Presentation
open UnitNormalization
variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem sameLabelledType_refl (P : Presentation d ι) : P.SameLabelledType P := by
  have hh := sameLabelledType_of_faceOrderIso (ofCanonical P) (ofCanonical P)
    (OrderIso.refl _) (fun i => rfl)
  simpa only [presentation_ofCanonical] using hh

theorem SameLabelledType.symm {P Q : Presentation d ι} (h : P.SameLabelledType Q) :
    Q.SameLabelledType P := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, ?_⟩
  intro i
  obtain ⟨F, hF, hEF⟩ := he i
  exact ⟨e F, hEF, by simpa using hF⟩

theorem SameLabelledType.trans {P Q S : Presentation d ι}
    (hPQ : P.SameLabelledType Q) (hQS : Q.SameLabelledType S) :
    P.SameLabelledType S := by
  obtain ⟨e, he⟩ := hPQ
  obtain ⟨f, hf⟩ := hQS
  refine ⟨e.trans f, ?_⟩
  intro i
  obtain ⟨F, hF, hEF⟩ := he i
  obtain ⟨G, hG, hFG⟩ := hf i
  have hh : e F = G := Subtype.ext (hEF.trans hG.symm)
  refine ⟨F, hF, ?_⟩
  change (f (e F)).val = S.facet i
  rw [hh]
  exact hFG

end NormalProjective.CanonicalModel.Presentation

end

/- Source: NormalProjective/MatrixRealization.lean -/
section
/-! # Literal matrix presentations and genuine canonical moves -/
open Set Matrix Filter
open scoped Topology BigOperators
namespace NormalProjective.MatrixRealization
open UnitNormalization
open CanonicalModel CanonicalModel.Realization
variable {d : ℕ} {ι : Type*} [Fintype ι]

abbrev MatrixData (d : ℕ) (ι : Type*) := Matrix ι (Fin d) ℝ × (ι → ℝ)

def asData (D : MatrixData d ι) : HalfspaceData ι (CanonicalModel.Space d) :=
  (fun i => rowForm (D.1 i), D.2)

theorem continuous_asData : Continuous (asData : MatrixData d ι →
    HalfspaceData ι (CanonicalModel.Space d)) := by
  apply Continuous.prodMk _ continuous_snd
  apply continuous_pi
  intro i
  exact continuous_rowForm.comp ((continuous_apply i).comp continuous_fst)

theorem regularData_ext {p q : RegularData d ι} (h : p.data = q.data) : p = q := by
  cases p
  cases q
  cases h
  rfl

def Realizes (R : Presentation d ι) (D : MatrixData d ι) : Prop :=
  ∃ p : RegularData d ι, p.data = asData D ∧ R.SameLabelledType (presentation p)

def regular (R : Presentation d ι) (D : MatrixData d ι) (h : Realizes R D) :
    RegularData d ι := h.choose

theorem regular_data (R : Presentation d ι) (D : MatrixData d ι) (h : Realizes R D) :
    (regular R D h).data = asData D := h.choose_spec.1

def realization (R : Presentation d ι) (D : MatrixData d ι) (h : Realizes R D) :
    Realization R := ⟨presentation (regular R D h), h.choose_spec.2⟩

theorem realization_carrier (R : Presentation d ι) (D : MatrixData d ι)
    (h : Realizes R D) :
    (realization R D h).carrier = dataRegion (asData D) := by
  change (presentation (regular R D h)).carrier = _
  rw [presentation_carrier, regular_data]

theorem realization_facet (R : Presentation d ι) (D : MatrixData d ι)
    (h : Realizes R D) (i : ι) :
    (realization R D h).facet i =
      {x ∈ dataRegion (asData D) | rowForm (D.1 i) x = D.2 i} := by
  change (presentation (regular R D h)).facet i = _
  rw [presentation_facet, regular_data]
  rfl

theorem realization_eq_of_regular (R : Presentation d ι) (D : MatrixData d ι)
    (h : Realizes R D) (p : RegularData d ι) (hp : p.data = asData D)
    (hRp : R.SameLabelledType (presentation p)) :
    realization R D h = ⟨presentation p, hRp⟩ := by
  apply Subtype.ext
  change presentation (regular R D h) = presentation p
  rw [regularData_ext ((regular_data R D h).trans hp.symm)]

theorem normal_step (R : Presentation d ι) (D E : MatrixData d ι)
    (hD : Realizes R D) (hE : Realizes R E) (hn : D.1 = E.1) :
    NormalStep (realization R D hD) (realization R E hE) := by
  change (fun i => unitRow ((regular R D hD).data.1 i)) =
    (fun i => unitRow ((regular R E hE).data.1 i))
  rw [regular_data, regular_data]
  simp only [asData, hn]

theorem realization_eq_of_positive_rows (R : Presentation d ι) (D E : MatrixData d ι)
    (hD : Realizes R D) (hE : Realizes R E) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hn : ∀ i j, E.1 i j = r i * D.1 i j)
    (hh : ∀ i, E.2 i = r i * D.2 i) :
    realization R E hE = realization R D hD := by
  apply Subtype.ext
  apply presentation_eq_of_positive_rows (regular R D hD) (regular R E hE) r hr
  · intro i
    rw [regular_data, regular_data]
    ext x
    simp only [asData, rowForm_apply, dot, hn, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · intro i
    rw [regular_data, regular_data]
    exact hh i

theorem rowForm_update (D : MatrixData d ι) (u : CanonicalModel.Space d) (i : ι) :
    (rowForm (fun j => D.1 i j + D.2 i * u j)).toLinearMap =
      (rowForm (D.1 i)).toLinearMap + D.2 i • (rowForm u).toLinearMap := by
  apply LinearMap.ext
  intro x
  change rowForm (fun j => D.1 i j + D.2 i * u j) x =
    rowForm (D.1 i) x + D.2 i * rowForm u x
  simp only [rowForm_apply, dot, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

/-- A literal row update, with the affine denominator verified on the entire
carrier, is a genuine labelled projective move. -/
theorem projective_step (R : Presentation d ι) (D E : MatrixData d ι)
    (hD : Realizes R D) (hE : Realizes R E) (u : CanonicalModel.Space d)
    (hn : ∀ i j, E.1 i j = D.1 i j + D.2 i * u j)
    (hh : E.2 = D.2) (hpos : ∀ i, 0 ≤ D.2 i)
    (hforward : ∀ x ∈ dataRegion (asData D), 0 < 1 + rowForm u x) :
    ProjectiveStep (realization R D hD) (realization R E hE) := by
  let f : ι → CanonicalModel.Space d →ₗ[ℝ] ℝ := fun i => (rowForm (D.1 i)).toLinearMap
  have hforms : (fun i => (rowForm (E.1 i)).toLinearMap) =
      ProjectiveBridge.changedNormals f D.2 (rowForm u).toLinearMap := by
    funext i
    have hi : E.1 i = fun j => D.1 i j + D.2 i * u j := funext (hn i)
    rw [hi, rowForm_update]
    rfl
  have hcompact : IsCompact (dataRegion (asData D)) := by
    rw [← regular_data R D hD]
    exact (regular R D hD).compact
  apply ElementaryProjectivity.canonical_step
    (realization R D hD) (realization R E hE) f D.2 hpos hcompact.isBounded (rowForm u)
  · exact hforward
  · exact realization_carrier R D hD
  · rw [realization_carrier]
    change ProjectiveBridge.HRegion (fun i => (rowForm (E.1 i)).toLinearMap) E.2 = _
    rw [hforms, hh]
  · exact realization_facet R D hD
  · intro i
    rw [realization_facet]
    change {x ∈ ProjectiveBridge.HRegion (fun i => (rowForm (E.1 i)).toLinearMap) E.2 |
      (rowForm (E.1 i)).toLinearMap x = E.2 i} = _
    rw [hforms, hh]
    rw [congrFun hforms i]

end NormalProjective.MatrixRealization

end

/- Source: NormalProjective/LocalControlOpen.lean -/
section
/-! # One open neighbourhood contains every stage of the explicit local word -/
open Set Filter Matrix
open scoped Topology BigOperators
namespace NormalProjective.LocalControl
variable {n : ℕ} {ι : Type*} [Fintype ι]

theorem direction_abs_le {η : ℝ} (hη : 0 < η) (j k : Fin (n + 1)) :
    |direction η j k| ≤ η := by
  by_cases hj : j = Fin.last n <;> by_cases hk : k.val < n <;> by_cases hkj : k = j <;>
    simp [direction, hj, hk, hkj, abs_of_pos hη, hη.le]

theorem direction_denominator_pos {η C : ℝ} (hη : 0 < η) (hC : 0 < C)
    (hsmall : η < 1 / ((n + 1 : ℕ) * (C + 1)))
    (j : Fin (n + 1)) {x : Fin (n + 1) → ℝ} (hx : ‖x‖ ≤ C) :
    0 < 1 + UnitNormalization.rowForm (direction η j) x := by
  have hcoord (k : Fin (n + 1)) : |x k| ≤ C := by
    have hk : |x k| ≤ ‖x‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm x k
    exact hk.trans hx
  have habs : |∑ k, direction η j k * x k| ≤ (n + 1 : ℕ) * η * C := by
    calc
      |∑ k, direction η j k * x k| ≤ ∑ k, |direction η j k * x k| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin (n + 1), η * C := by
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_mul]
        exact mul_le_mul (direction_abs_le hη j k) (hcoord k) (abs_nonneg _) hη.le
      _ = _ := by simp; ring
  have hd : (0 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
  have hden : (0 : ℝ) < (n + 1 : ℕ) * (C + 1) := mul_pos hd (by linarith)
  have hm := (lt_div_iff₀ hden).mp hsmall
  have hprod : (n + 1 : ℕ) * η * C < 1 := by
    calc
      (n + 1 : ℕ) * η * C ≤ (n + 1 : ℕ) * η * (C + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hd.le hη.le)
      _ < 1 := by nlinarith [hm]
  rw [UnitNormalization.rowForm_apply]
  unfold CanonicalModel.dot
  have hl := neg_abs_le (∑ k, direction η j k * x k)
  linarith

/-- There is one fixed nonzero projective step size for an entire target neighbourhood. -/
theorem exists_local_control_neighbourhood
    (A : NormalMatrix ι n) (hA : ∀ i, A i (Fin.last n) ≠ 0)
    {U : Set (MatrixData ι n)} (hU : U ∈ 𝓝 (A, fun _ => 1))
    {C : ℝ} (hC : 0 < C) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / ((n + 1 : ℕ) * (C + 1)) ∧
      ∀ᶠ B : NormalMatrix ι n in 𝓝 A,
        (∀ j : Fin (n + 1), beforeData A B η j ∈ U ∧ afterNormalData A B η j ∈ U) ∧
        finalData A B ∈ U ∧
        (∀ j i, 0 < support A B η j i) ∧
        (∀ i, 0 < ratio A B i) ∧ (∀ i, B i (Fin.last n) ≠ 0) := by
  classical
  obtain ⟨V, hVU, hVo, hAV⟩ := mem_nhds_iff.mp hU
  have hV : V ∈ 𝓝 (A, fun _ => 1) := hVo.mem_nhds hAV
  have hbase : ∀ j : Fin (n + 1), ∀ᶠ η : ℝ in 𝓝 0,
      beforeData A A η j ∈ V ∧ afterNormalData A A η j ∈ V := by
    intro j
    have hp := (baseline_before_continuous A hA j).continuousAt.eventually
      (show V ∈ 𝓝 (beforeData A A 0 j) by simpa [baseline_before_zero A hA] using hV)
    have hq := (baseline_after_continuous A hA j).continuousAt.eventually
      (show V ∈ 𝓝 (afterNormalData A A 0 j) by simpa [baseline_after_zero A hA] using hV)
    exact hp.and hq
  have hδ : (0 : ℝ) < 1 / ((n + 1 : ℕ) * (C + 1)) := by positivity
  have hall := (Filter.eventually_all.mpr hbase).and (eventually_lt_nhds hδ)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hall
  let η : ℝ := ε / 2
  have hη : 0 < η := by dsimp [η]; linarith
  have hηball : η ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hη]
    dsimp [η]
    linarith
  have hstage := (hball hηball).1
  refine ⟨η, hη, (hball hηball).2, ?_⟩
  have hst : ∀ j : Fin (n + 1), ∀ᶠ B : NormalMatrix ι n in 𝓝 A,
      beforeData A B η j ∈ U ∧ afterNormalData A B η j ∈ U := by
    intro j
    exact ((continuousAt_before A hA η j).eventually
      (Filter.mem_of_superset (hVo.mem_nhds (hstage j).1) hVU)).and
      ((continuousAt_after A hA η j).eventually
        (Filter.mem_of_superset (hVo.mem_nhds (hstage j).2) hVU))
  have hfinal : ∀ᶠ B : NormalMatrix ι n in 𝓝 A, finalData A B ∈ U :=
    (continuousAt_final A hA).eventually (by simpa [final_self A hA] using hU)
  have hs : ∀ j : Fin (n + 1), ∀ i : ι, ∀ᶠ B : NormalMatrix ι n in 𝓝 A,
      0 < support A B η j i := by
    intro j i
    exact Filter.Tendsto.eventually_const_lt (by simp [support_self A hA])
      (continuousAt_pi.mp (continuousAt_support A hA η j) i)
  have hr : ∀ i : ι, ∀ᶠ B : NormalMatrix ι n in 𝓝 A, 0 < ratio A B i := by
    intro i
    exact Filter.Tendsto.eventually_const_lt (by simp [ratio_self A hA])
      (continuousAt_pi.mp (continuousAt_ratio A hA) i)
  have hn : ∀ i : ι, ∀ᶠ B : NormalMatrix ι n in 𝓝 A, B i (Fin.last n) ≠ 0 := by
    intro i
    exact (isOpen_ne_fun ((continuous_apply (Fin.last n)).comp (continuous_apply i))
      continuous_const).mem_nhds (hA i)
  filter_upwards [Filter.eventually_all.mpr hst, hfinal,
    Filter.eventually_all.mpr (fun j => Filter.eventually_all.mpr (hs j)),
    Filter.eventually_all.mpr hr, Filter.eventually_all.mpr hn] with B hB hF hS hR hN
  exact ⟨hB, hF, hS, hR, hN⟩

end NormalProjective.LocalControl

end

/- Source: NormalProjective/LocalWord.lean -/
section
/-! # The explicit local controller is a word of actual labelled moves -/
open Set Matrix Filter
open scoped Topology
namespace NormalProjective
open UnitNormalization CanonicalModel CanonicalModel.Realization

theorem PNWord.of_alternating {d k : ℕ} {ι : Type*} [Fintype ι]
    {R : Presentation d ι} (X : Fin (k + 1) → Realization R)
    (Y : Fin k → Realization R)
    (hN : ∀ j, NormalStep (X j.castSucc) (Y j))
    (hP : ∀ j, ProjectiveStep (Y j) (X j.succ)) :
    PNWord (X 0) (X (Fin.last k)) k k := by
  have hall : ∀ j : Fin (k + 1), PNWord (X 0) (X j) j.val j.val := by
    intro j
    induction j using Fin.induction with
    | zero => exact PNWord.nil _
    | succ i ih =>
        simpa using ih.append
          (PNWord.normal (hN i) (PNWord.projective (hP i) (PNWord.nil _)))
  exact hall (Fin.last k)

namespace LocalControl
variable {n : ℕ} {ι : Type*} [Fintype ι]

@[simp] theorem beforeData_first (A B : NormalMatrix ι n) (η : ℝ) :
    beforeData A B η 0 = (A, fun _ => 1) := by
  simp [beforeData]

theorem beforeData_succ (A B : NormalMatrix ι n) (η : ℝ) (j : Fin n) :
    beforeData A B η j.succ = (stage A B η (j.val + 1), support A B η j.castSucc) := by
  simp [beforeData]
  congr 1

/-- No abstract controllability assumption occurs here: every displayed matrix
stage is normalized to its actual labelled polytope, and every P-step uses an
invertible homogeneous matrix with denominator positive on its whole carrier. -/
theorem actual_local_word (R : Presentation (n + 1) ι)
    (A B : NormalMatrix ι n) (η C : ℝ)
    (hη : 0 < η) (hC : 0 < C)
    (hsmall : η < 1 / ((n + 1 : ℕ) * (C + 1)))
    (hB : ∀ i, B i (Fin.last n) ≠ 0)
    (hbefore : ∀ j, MatrixRealization.Realizes R (beforeData A B η j))
    (hafter : ∀ j, MatrixRealization.Realizes R (afterNormalData A B η j))
    (hfinal : MatrixRealization.Realizes R (finalData A B))
    (hpos : ∀ j i, 0 < support A B η j i)
    (hbound : ∀ j, dataRegion (MatrixRealization.asData (afterNormalData A B η j)) ⊆
      Metric.closedBall 0 C) :
    PNWord
      (MatrixRealization.realization R (beforeData A B η 0) (hbefore 0))
      (MatrixRealization.realization R (finalData A B) hfinal) (n + 1) (n + 1) := by
  classical
  let P (j : Fin (n + 1)) := MatrixRealization.realization R (beforeData A B η j) (hbefore j)
  let Q (j : Fin (n + 1)) := MatrixRealization.realization R (afterNormalData A B η j) (hafter j)
  let Z := MatrixRealization.realization R (finalData A B) hfinal
  have hN (j : Fin (n + 1)) : NormalStep (P j) (Q j) :=
    MatrixRealization.normal_step R _ _ (hbefore j) (hafter j) rfl
  have hforward (j : Fin (n + 1)) :
      ∀ x ∈ dataRegion (MatrixRealization.asData (afterNormalData A B η j)),
        0 < 1 + rowForm (direction η j) x := by
    intro x hx
    apply direction_denominator_pos hη hC hsmall j
    have hh := hbound j hx
    simpa [Metric.mem_closedBall, dist_zero_right] using hh
  have hP (j : Fin n) : ProjectiveStep (Q j.castSucc) (P j.succ) := by
    apply MatrixRealization.projective_step R _ _ (hafter j.castSucc)
      (hbefore j.succ) (direction η j.castSucc)
    · intro i k
      rw [beforeData_succ]
      exact congrFun (congrFun (stage_step A B η j) i) k
    · rw [beforeData_succ]
      rfl
    · exact fun i => (hpos j.castSucc i).le
    · exact hforward j.castSucc
  have hlast : ProjectiveStep (Q (Fin.last n)) Z := by
    apply MatrixRealization.projective_step R _ _ (hafter (Fin.last n)) hfinal
      (direction η (Fin.last n))
    · intro i k
      exact (congrFun (congrFun (final_step A B η (ne_of_gt hη) hB) i) k).symm
    · funext i
      simp [afterNormalData, finalData, LocalControl.support]
    · exact fun i => (hpos (Fin.last n) i).le
    · exact hforward (Fin.last n)
  let X : Fin (n + 1 + 1) → Realization R :=
    fun j => if hj : j.val < n + 1 then P ⟨j.val, hj⟩ else Z
  have hXcast (j : Fin (n + 1)) : X j.castSucc = P j := by
    change (if hj : j.val < n + 1 then P ⟨j.val, hj⟩ else Z) = P j
    rw [dif_pos j.isLt]
  have hXsucc (j : Fin n) : X j.castSucc.succ = P j.succ := by
    have hj : j.val + 1 < n + 1 := Nat.succ_lt_succ j.isLt
    change (if h : j.val + 1 < n + 1 then P ⟨j.val + 1, h⟩ else Z) = P j.succ
    rw [dif_pos hj]
    apply congrArg P
    apply Fin.ext
    simp
  have hXlast : X (Fin.last (n + 1)) = Z := by simp [X]
  have hXzero : X 0 = P 0 := by simp [X]
  have hPX (j : Fin (n + 1)) : ProjectiveStep (Q j) (X j.succ) := by
    induction j using Fin.lastCases with
    | last =>
        have hh : (Fin.last n).succ = Fin.last (n + 1) := rfl
        rw [hh, hXlast]
        exact hlast
    | cast j =>
        rw [hXsucc]
        exact hP j
  have hw := PNWord.of_alternating X Q (fun j => by rw [hXcast]; exact hN j) hPX
  simpa only [hXzero, hXlast, P, Z] using hw

end LocalControl
end NormalProjective

end

/- Source: NormalProjective/LocalNeighbourhood.lean -/
section
/-! # A whole neighborhood is reached by the actual local word -/
open Set Filter Matrix
open scoped Topology
namespace NormalProjective.LocalControl
open UnitNormalization CanonicalModel CanonicalModel.Realization
variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The generic-coordinate normalized form of the local 2d-move theorem.
The ambient-coordinate removal is a separate affine-conjugacy bridge. -/
theorem normalized_local_neighbourhood
    (p₀ : RegularData (n + 1) ι) (A : NormalMatrix ι n)
    (hp₀ : p₀.data = MatrixRealization.asData (A, fun _ => 1))
    (hs : IsSimpleHalfspace (fun i => (rowForm (A i)).toLinearMap) (fun _ => 1))
    (hA : ∀ i, A i (Fin.last n) ≠ 0) :
    ∀ᶠ B : NormalMatrix ι n in 𝓝 A,
      ∃ hB : MatrixRealization.Realizes (presentation p₀) (B, fun _ => 1),
        PNWord
          ⟨presentation p₀, Presentation.sameLabelledType_refl (presentation p₀)⟩
          (MatrixRealization.realization (presentation p₀) (B, fun _ => 1) hB)
          (n + 1) (n + 1) := by
  classical
  let R := presentation p₀
  let f := fun i => rowForm (A i)
  obtain ⟨C, hC, hstable⟩ := normalized_regular_eventually_stable p₀ f hp₀ hs
  let U : Set (MatrixData ι n) := {D |
    dataRegion (MatrixRealization.asData D) ⊆ Metric.closedBall 0 C ∧
      MatrixRealization.Realizes R D}
  have hU : U ∈ 𝓝 (A, fun _ => 1) := by
    have hc : Tendsto (MatrixRealization.asData : MatrixData ι n →
        HalfspaceData ι (Fin (n + 1) → ℝ)) (𝓝 (A, fun _ => 1)) (𝓝 (f, fun _ => 1)) :=
      MatrixRealization.continuous_asData.continuousAt
    have hh := hc.eventually hstable
    filter_upwards [hh] with D hD
    obtain ⟨hbound, _, q, hq, hRq⟩ := hD
    exact ⟨hbound, q, hq, hRq⟩
  obtain ⟨η, hη, hsmall, hcontrol⟩ :=
    exists_local_control_neighbourhood A hA hU hC
  have htarget : ∀ᶠ B : NormalMatrix ι n in 𝓝 A, (B, fun _ => 1) ∈ U :=
    (continuous_id.prodMk continuous_const).continuousAt.eventually hU
  filter_upwards [hcontrol, htarget] with B hB htarget
  have hbefore := fun j => (hB.1 j).1.2
  have hafter := fun j => (hB.1 j).2.2
  have hfinal := hB.2.1.2
  have hword := actual_local_word R A B η C hη hC hsmall hB.2.2.2.2
    hbefore hafter hfinal hB.2.2.1 (fun j => (hB.1 j).2.1)
  have hstart :
      MatrixRealization.realization R (beforeData A B η 0) (hbefore 0) =
        ⟨presentation p₀, Presentation.sameLabelledType_refl (presentation p₀)⟩ := by
    apply MatrixRealization.realization_eq_of_regular R _ _ p₀
    · simpa only [beforeData_first] using hp₀
  have hend :
      MatrixRealization.realization R (finalData A B) hfinal =
        MatrixRealization.realization R (B, fun _ => 1) htarget.2 := by
    apply MatrixRealization.realization_eq_of_positive_rows R _ _ htarget.2 hfinal
      (ratio A B) hB.2.2.2.1
    · intro i j
      rfl
    · intro i
      simp [finalData]
  refine ⟨htarget.2, ?_⟩
  rw [hstart, hend] at hword
  exact hword

end NormalProjective.LocalControl

end

/- Source: NormalProjective/GeneralProjectivity.lean -/
section
/-! # Composition, inversion, and reversibility of genuine projective words -/
open Set Matrix
open scoped BigOperators
namespace NormalProjective.CanonicalModel.Realization
variable {d : ℕ}

def homogeneousPoint (x : Space d) : Option (Fin d) → ℝ
  | none => 1
  | some j => x j

@[simp] theorem mulVec_homogeneousPoint_none (M : HomogeneousMatrix d) (x : Space d) :
    (M *ᵥ homogeneousPoint x) none = denominator M x := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_option, homogeneousPoint, denominator]

@[simp] theorem mulVec_homogeneousPoint_some (M : HomogeneousMatrix d) (x : Space d)
    (j : Fin d) :
    (M *ᵥ homogeneousPoint x) (some j) = numerator M x j := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_option, homogeneousPoint, numerator]

theorem mulVec_homogeneousPoint (M : HomogeneousMatrix d) (x : Space d)
    (hx : denominator M x ≠ 0) :
    M *ᵥ homogeneousPoint x = denominator M x • homogeneousPoint (projectiveMap M x) := by
  funext i
  cases i with
  | none => simp [homogeneousPoint]
  | some j =>
      simp only [mulVec_homogeneousPoint_some, Pi.smul_apply, smul_eq_mul,
        homogeneousPoint, projectiveMap]
      field_simp

theorem product_mulVec_homogeneousPoint (N M : HomogeneousMatrix d) (x : Space d)
    (hx : denominator M x ≠ 0) :
    (N * M) *ᵥ homogeneousPoint x =
      denominator M x • (N *ᵥ homogeneousPoint (projectiveMap M x)) := by
  rw [← Matrix.mulVec_mulVec, mulVec_homogeneousPoint M x hx, Matrix.mulVec_smul]

theorem denominator_mul (N M : HomogeneousMatrix d) (x : Space d)
    (hx : denominator M x ≠ 0) :
    denominator (N * M) x = denominator M x * denominator N (projectiveMap M x) := by
  have hh := congrFun (product_mulVec_homogeneousPoint N M x hx) none
  simpa only [mulVec_homogeneousPoint_none, Pi.smul_apply, smul_eq_mul] using hh

theorem numerator_mul (N M : HomogeneousMatrix d) (x : Space d)
    (hx : denominator M x ≠ 0) (j : Fin d) :
    numerator (N * M) x j = denominator M x * numerator N (projectiveMap M x) j := by
  have hh := congrFun (product_mulVec_homogeneousPoint N M x hx) (some j)
  simpa only [mulVec_homogeneousPoint_some, Pi.smul_apply, smul_eq_mul] using hh

theorem projectiveMap_mul (N M : HomogeneousMatrix d) (x : Space d)
    (hx : denominator M x ≠ 0) :
    projectiveMap (N * M) x = projectiveMap N (projectiveMap M x) := by
  funext j
  simp only [projectiveMap, numerator_mul N M x hx j, denominator_mul N M x hx]
  exact mul_div_mul_left _ _ hx

@[simp] theorem denominator_one (x : Space d) :
    denominator (1 : HomogeneousMatrix d) x = 1 := by
  simp [denominator, Matrix.one_apply]

@[simp] theorem projectiveMap_one (x : Space d) :
    projectiveMap (1 : HomogeneousMatrix d) x = x := by
  ext j
  simp [projectiveMap, denominator, numerator, Matrix.one_apply, ite_mul]

theorem denominator_inverse_ne_zero (M : HomogeneousMatrix d) (hM : M.det ≠ 0)
    (x : Space d) (hx : denominator M x ≠ 0) :
    denominator M⁻¹ (projectiveMap M x) ≠ 0 := by
  have hh := denominator_mul M⁻¹ M x hx
  rw [Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM), denominator_one] at hh
  intro hz
  rw [hz, mul_zero] at hh
  exact one_ne_zero hh

theorem projectiveMap_inverse (M : HomogeneousMatrix d) (hM : M.det ≠ 0)
    (x : Space d) (hx : denominator M x ≠ 0) :
    projectiveMap M⁻¹ (projectiveMap M x) = x := by
  rw [← projectiveMap_mul M⁻¹ M x hx,
    Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM), projectiveMap_one]

theorem inverse_image_image (M : HomogeneousMatrix d) (hM : M.det ≠ 0)
    (S : Set (Space d)) (hS : ∀ x ∈ S, denominator M x ≠ 0) :
    projectiveMap M⁻¹ '' (projectiveMap M '' S) = S := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    simpa only [projectiveMap_inverse M hM y (hS y hy)] using hy
  · intro hx
    exact ⟨projectiveMap M x, ⟨x, hx, rfl⟩,
      projectiveMap_inverse M hM x (hS x hx)⟩

variable {ι : Type*} [Fintype ι] {R : Presentation d ι}

theorem projectiveStep_refl (P : Realization R) : ProjectiveStep P P := by
  refine ⟨1, by simp, ?_, ?_, ?_⟩
  · intro x hx
    simp
  · simp
  · intro i
    simp

theorem ProjectiveStep.trans {P Q S : Realization R}
    (hPQ : ProjectiveStep P Q) (hQS : ProjectiveStep Q S) : ProjectiveStep P S := by
  obtain ⟨M, hM, hdenM, hcarM, hfacM⟩ := hPQ
  obtain ⟨N, hN, hdenN, hcarN, hfacN⟩ := hQS
  refine ⟨N * M, by rw [Matrix.det_mul]; exact mul_ne_zero hN hM, ?_, ?_, ?_⟩
  · intro x hx
    rw [denominator_mul N M x (hdenM x hx)]
    exact mul_ne_zero (hdenM x hx) (hdenN _ (hcarM ▸ ⟨x, hx, rfl⟩))
  · calc
      projectiveMap (N * M) '' P.carrier =
          projectiveMap N '' (projectiveMap M '' P.carrier) := by
            rw [Set.image_image]
            apply Set.image_congr
            intro x hx
            exact projectiveMap_mul N M x (hdenM x hx)
      _ = S.carrier := by rw [hcarM, hcarN]
  · intro i
    calc
      projectiveMap (N * M) '' P.facet i =
          projectiveMap N '' (projectiveMap M '' P.facet i) := by
            rw [Set.image_image]
            apply Set.image_congr
            intro x hx
            exact projectiveMap_mul N M x (hdenM x hx.1)
      _ = S.facet i := by rw [hfacM, hfacN]

theorem ProjectiveStep.symm {P Q : Realization R}
    (hPQ : ProjectiveStep P Q) : ProjectiveStep Q P := by
  obtain ⟨M, hM, hden, hcar, hfac⟩ := hPQ
  refine ⟨M⁻¹, Matrix.det_ne_zero_of_left_inverse
    (Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM)), ?_, ?_, ?_⟩
  · intro y hy
    rw [← hcar] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact denominator_inverse_ne_zero M hM x (hden x hx)
  · rw [← hcar]
    exact inverse_image_image M hM _ hden
  · intro i
    rw [← hfac i]
    exact inverse_image_image M hM _ (fun x hx => hden x hx.1)

theorem PNWord.reverse {P Q : Realization R} {p n : ℕ}
    (h : PNWord P Q p n) : PNWord Q P p n := by
  induction h with
  | nil P => exact PNWord.nil P
  | projective hstep htail ih =>
      simpa using ih.append (PNWord.projective hstep.symm (PNWord.nil _))
  | normal hstep htail ih =>
      simpa using ih.append (PNWord.normal hstep.symm (PNWord.nil _))

theorem PNRelated.symm {P Q : Realization R} (h : PNRelated P Q) : PNRelated Q P := by
  obtain ⟨p, n, h⟩ := h
  exact ⟨p, n, h.reverse⟩

end NormalProjective.CanonicalModel.Realization

end

/- Source: NormalProjective/AffineProjectivity.lean -/
section
/-! # Every labelled affine equivalence is an actual projective step -/
open Set Matrix
open scoped BigOperators
namespace NormalProjective.CanonicalModel.Realization
open NormalProjective.UnitNormalization
variable {d : ℕ}

theorem homogeneous_ext {M N : HomogeneousMatrix d}
    (h : ∀ x : Space d, M *ᵥ homogeneousPoint x = N *ᵥ homogeneousPoint x) : M = N := by
  ext i j
  have h0 := congrFun (h 0) i
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_option, homogeneousPoint,
    Pi.zero_apply, mul_one, mul_zero, Finset.sum_const_zero, add_zero] at h0
  cases j with
  | none => exact h0
  | some j =>
      have hj := congrFun (h (Pi.single j 1)) i
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_option, homogeneousPoint,
        mul_one] at hj
      simp [Pi.single_apply] at hj
      linarith

def affineHomogeneous (a : Space d ≃ᵃ[ℝ] Space d) : HomogeneousMatrix d :=
  fun i j => match i, j with
  | none, none => 1
  | none, some _ => 0
  | some i, none => a 0 i
  | some i, some j => a.linear (Pi.single j 1) i

@[simp] theorem affineHomogeneous_denominator (a : Space d ≃ᵃ[ℝ] Space d)
    (x : Space d) : denominator (affineHomogeneous a) x = 1 := by
  simp [denominator, affineHomogeneous]

@[simp] theorem affineHomogeneous_numerator (a : Space d ≃ᵃ[ℝ] Space d)
    (x : Space d) : numerator (affineHomogeneous a) x = a x := by
  have ha : a x = a.linear x + a 0 := by
    simpa using a.map_vadd (0 : Space d) x
  ext i
  let f : Space d →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp a.linear.toContinuousLinearMap
  have hf := coefficient_expansion f x
  change (∑ j, a.linear (Pi.single j 1) i * x j) = a.linear x i at hf
  change a 0 i + (∑ j, a.linear (Pi.single j 1) i * x j) = a x i
  rw [hf, ha]
  simp only [Pi.add_apply]
  ring

@[simp] theorem affineHomogeneous_map (a : Space d ≃ᵃ[ℝ] Space d)
    (x : Space d) : projectiveMap (affineHomogeneous a) x = a x := by
  ext i
  simp [projectiveMap]

theorem affineHomogeneous_mulVec (a : Space d ≃ᵃ[ℝ] Space d) (x : Space d) :
    affineHomogeneous a *ᵥ homogeneousPoint x = homogeneousPoint (a x) := by
  ext i
  cases i <;> simp [homogeneousPoint]

theorem affineHomogeneous_inverse (a : Space d ≃ᵃ[ℝ] Space d) :
    affineHomogeneous a.symm * affineHomogeneous a = 1 := by
  apply homogeneous_ext
  intro x
  rw [← Matrix.mulVec_mulVec, affineHomogeneous_mulVec, affineHomogeneous_mulVec]
  simp

theorem affineHomogeneous_det_ne_zero (a : Space d ≃ᵃ[ℝ] Space d) :
    (affineHomogeneous a).det ≠ 0 :=
  Matrix.det_ne_zero_of_left_inverse (affineHomogeneous_inverse a)

variable {ι : Type*} [Fintype ι] {R : Presentation d ι}

theorem AffineRelated.projectiveStep {P Q : Realization R}
    (h : AffineRelated P Q) : ProjectiveStep P Q := by
  obtain ⟨a, hcar, hfac⟩ := h
  refine ⟨affineHomogeneous a, affineHomogeneous_det_ne_zero a, ?_, ?_, ?_⟩
  · intro x hx
    simp
  · simpa only [affineHomogeneous_map] using hcar
  · intro i
    simpa only [affineHomogeneous_map] using hfac i

theorem AffineRelated.pnRelated {P Q : Realization R}
    (h : AffineRelated P Q) : PNRelated P Q :=
  ⟨1, 0, PNWord.projective h.projectiveStep (PNWord.nil _)⟩

end NormalProjective.CanonicalModel.Realization

end

/- Source: NormalProjective/FaceVertices.lean -/
section
/-! # Actual face isomorphisms induce actual vertex and incidence isomorphisms -/
open Set
namespace NormalProjective
variable {d : ℕ} {ι : Type*} [Fintype ι]

def vertexFace (f : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ) (h : ι → ℝ)
    (v : HalfspaceVertices f h) : HalfspaceFaces f h := by
  refine ⟨{v.val}, ?_⟩
  obtain ⟨I, hI, hli⟩ := extremePoint_has_active_basis f h v.property
  have hdet := facetCoefficientMatrix_det_ne_zero (fun j => f (I j)) hli
  have heq : tightFace f h (Set.range I) = {v.val} := by
    ext y
    constructor
    · intro hy
      exact Set.mem_singleton_iff.mpr
        (tight_minor_unique f h I hdet (fun j => hy.2 _ ⟨j, rfl⟩) hI)
    · rintro rfl
      exact ⟨v.property.1, fun i ⟨j, hij⟩ => hij ▸ hI j⟩
  rw [← heq]
  exact tightFace_isExposed f h _

def emptyFace (f : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ) (h : ι → ℝ) :
    HalfspaceFaces f h := ⟨∅, isExposed_empty⟩

theorem faceIso_empty
    (f g : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ) (h k : ι → ℝ)
    (e : HalfspaceFaces f h ≃o HalfspaceFaces g k) :
    e (emptyFace f h) = emptyFace g k := by
  apply le_antisymm
  · have hh : emptyFace f h ≤ e.symm (emptyFace g k) := Set.empty_subset _
    simpa using e.monotone hh
  · exact Set.empty_subset _

theorem faceIso_nonempty_iff
    (f g : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ) (h k : ι → ℝ)
    (e : HalfspaceFaces f h ≃o HalfspaceFaces g k) (F : HalfspaceFaces f h) :
    (e F).val.Nonempty ↔ F.val.Nonempty := by
  have he := faceIso_empty f g h k e
  constructor
  · intro hne
    by_contra hno
    have hf : F = emptyFace f h :=
      Subtype.ext (Set.not_nonempty_iff_eq_empty.mp hno)
    rw [hf, he] at hne
    exact Set.not_nonempty_empty hne
  · intro hne
    by_contra hno
    have hEF : e F = emptyFace g k :=
      Subtype.ext (Set.not_nonempty_iff_eq_empty.mp hno)
    have hf : F = emptyFace f h := e.injective (hEF.trans he.symm)
    rw [hf] at hne
    exact Set.not_nonempty_empty hne

theorem faceIso_vertex_exists
    (f g : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ) (h k : ι → ℝ)
    (hcq : IsCompact (halfspaceRegion g k))
    (e : HalfspaceFaces f h ≃o HalfspaceFaces g k) (v : HalfspaceVertices f h) :
    ∃ w : HalfspaceVertices g k, e (vertexFace f h v) = vertexFace g k w := by
  let F := vertexFace f h v
  let G := e F
  have hGn : G.val.Nonempty :=
    (faceIso_nonempty_iff f g h k e F).mpr ⟨v.val, rfl⟩
  obtain ⟨w, hw⟩ := (G.property.isCompact hcq).extremePoints_nonempty hGn
  let w' : HalfspaceVertices g k := ⟨w,
    G.property.isExtreme.extremePoints_subset_extremePoints hw⟩
  let H := vertexFace g k w'
  have hHG : H ≤ G := by
    intro x hx
    have hxw : x = w := hx
    simpa only [hxw] using hw.1
  have hpre : e.symm H ≤ F := by
    simpa only [G, e.symm_apply_apply] using e.symm.monotone hHG
  have hpren : (e.symm H).val.Nonempty :=
    (faceIso_nonempty_iff g f k h e.symm H).mpr ⟨w, rfl⟩
  have heq : e.symm H = F := by
    apply le_antisymm hpre
    intro x hx
    have hxv : x = v.val := hx
    obtain ⟨y, hy⟩ := hpren
    have hyv : y = v.val := hpre hy
    simpa only [hxv, hyv] using hy
  refine ⟨w', ?_⟩
  have := congrArg e heq
  simpa only [e.apply_symm_apply, F, H] using this.symm

def faceIsoVertexEquiv
    (f g : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ) (h k : ι → ℝ)
    (hcp : IsCompact (halfspaceRegion f h)) (hcq : IsCompact (halfspaceRegion g k))
    (e : HalfspaceFaces f h ≃o HalfspaceFaces g k) :
    HalfspaceVertices f h ≃ HalfspaceVertices g k := by
  classical
  let t (v : HalfspaceVertices f h) :=
    (faceIso_vertex_exists f g h k hcq e v).choose
  have ht (v : HalfspaceVertices f h) :
      e (vertexFace f h v) = vertexFace g k (t v) :=
    (faceIso_vertex_exists f g h k hcq e v).choose_spec
  apply Equiv.ofBijective t
  constructor
  · intro v w hvw
    have heq : vertexFace f h v = vertexFace f h w := by
      apply e.injective
      rw [ht, ht, hvw]
    apply Subtype.ext
    exact Set.singleton_injective (congrArg Subtype.val heq)
  · intro w
    obtain ⟨v, hv⟩ := faceIso_vertex_exists g f k h hcp e.symm w
    refine ⟨v, ?_⟩
    have heq : vertexFace g k (t v) = vertexFace g k w := by
      rw [← ht, ← hv, e.apply_symm_apply]
    apply Subtype.ext
    exact Set.singleton_injective (congrArg Subtype.val heq)

theorem faceIsoVertexEquiv_vertexFace
    (f g : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ) (h k : ι → ℝ)
    (hcp : IsCompact (halfspaceRegion f h)) (hcq : IsCompact (halfspaceRegion g k))
    (e : HalfspaceFaces f h ≃o HalfspaceFaces g k) (v : HalfspaceVertices f h) :
    e (vertexFace f h v) =
      vertexFace g k (faceIsoVertexEquiv f g h k hcp hcq e v) :=
  (faceIso_vertex_exists f g h k hcq e v).choose_spec

theorem faceIsoVertexEquiv_incidence
    (f g : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ) (h k : ι → ℝ)
    (hcp : IsCompact (halfspaceRegion f h)) (hcq : IsCompact (halfspaceRegion g k))
    (e : HalfspaceFaces f h ≃o HalfspaceFaces g k)
    (he : ∀ i, e ⟨tightFace f h {i}, tightFace_isExposed f h {i}⟩ =
      ⟨tightFace g k {i}, tightFace_isExposed g k {i}⟩)
    (v : HalfspaceVertices f h) (i : ι) :
    f i v.val = h i ↔ g i (faceIsoVertexEquiv f g h k hcp hcq e v).val = k i := by
  let F : HalfspaceFaces f h := ⟨tightFace f h {i}, tightFace_isExposed f h {i}⟩
  let G : HalfspaceFaces g k := ⟨tightFace g k {i}, tightFace_isExposed g k {i}⟩
  have hp : f i v.val = h i ↔ vertexFace f h v ≤ F := by
    simp [vertexFace, F, tightFace, Set.singleton_subset_iff, v.property.1]
  have hq : g i (faceIsoVertexEquiv f g h k hcp hcq e v).val = k i ↔
      vertexFace g k (faceIsoVertexEquiv f g h k hcp hcq e v) ≤ G := by
    simp [vertexFace, G, tightFace, Set.singleton_subset_iff,
      (faceIsoVertexEquiv f g h k hcp hcq e v).property.1]
  have hei : e F = G := he i
  rw [hp, hq, ← faceIsoVertexEquiv_vertexFace, ← hei]
  exact e.le_iff_le.symm

end NormalProjective

end

/- Source: NormalProjective/NormalCones.lean -/
section
/-! # Feasible directions and normal-cone certificates at simple vertices -/
open Set Matrix Filter
open scoped Topology BigOperators
namespace NormalProjective

theorem halfspace_one_sided_perturbation
    {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]
    (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ) {x v : E}
    (hx : x ∈ halfspaceRegion f h)
    (hv : ∀ i, f i x = h i → f i v ≤ 0) :
    ∃ δ : ℝ, 0 < δ ∧ x + δ • v ∈ halfspaceRegion f h := by
  classical
  have hnear : ∀ i, ∀ᶠ t : ℝ in 𝓝 0, 0 ≤ t → f i (x + t • v) ≤ h i := by
    intro i
    by_cases hi : f i x = h i
    · filter_upwards [] with t ht
      have hh := mul_nonpos_of_nonneg_of_nonpos ht (hv i hi)
      simpa only [map_add, map_smul, smul_eq_mul, hi] using
        (show h i + t * f i v ≤ h i by linarith)
    · have his : f i x < h i := lt_of_le_of_ne (hx i) hi
      have ho : IsOpen {t : ℝ | f i x + t * f i v < h i} :=
        isOpen_lt (continuous_const.add (continuous_id.mul continuous_const)) continuous_const
      have hz : (0 : ℝ) ∈ {t : ℝ | f i x + t * f i v < h i} := by simpa using his
      filter_upwards [ho.mem_nhds hz] with t ht hnonneg
      simpa only [map_add, map_smul, smul_eq_mul] using ht.le
  have hall := Filter.eventually_all.mpr hnear
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hall
  have hδ : (0 : ℝ) < ε / 2 := by linarith
  have hb : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hδ]
    linarith
  exact ⟨ε / 2, hδ, fun i => hball hb i hδ.le⟩

variable {d : ℕ} {ι : Type*} [Fintype ι]

def activeInverseVector (f : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (I : Fin d ↪ ι) (j : Fin d) : Fin d → ℝ :=
  (facetCoefficientMatrix (fun k => f (I k)))⁻¹ *ᵥ Pi.single j 1

theorem activeInverseVector_eval
    (f : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ) (I : Fin d ↪ ι)
    (hdet : (facetCoefficientMatrix (fun k => f (I k))).det ≠ 0)
    (j k : Fin d) :
    f (I k) (activeInverseVector f I j) = (Pi.single j (1 : ℝ) : Fin d → ℝ) k := by
  let A := facetCoefficientMatrix (fun k => f (I k))
  have hh : A *ᵥ (A⁻¹ *ᵥ Pi.single j 1) = Pi.single j 1 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  have hk := congrFun hh k
  simpa only [A, facetCoefficientMatrix_mulVec, activeInverseVector] using hk

theorem maximizing_functional_active_coefficients_nonneg
    (f : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ) (h : ι → ℝ)
    (hs : IsSimpleHalfspace f h) {x : Fin d → ℝ}
    (hx : x ∈ (halfspaceRegion f h).extremePoints ℝ)
    (I : Fin d ↪ ι) (hI : ∀ j, f (I j) x = h (I j))
    (u : (Fin d → ℝ) →L[ℝ] ℝ)
    (hmax : ∀ y ∈ halfspaceRegion f h, u y ≤ u x) :
    ∀ j, 0 ≤ u (activeInverseVector f I j) := by
  obtain ⟨hrange, hdet⟩ := simple_active_minor_spans f h hs hx I hI
  intro j
  have hdir : ∀ i, f i x = h i → f i (-activeInverseVector f I j) ≤ 0 := by
    intro i hi
    have hmem : i ∈ Set.range I := by rw [hrange]; exact hi
    obtain ⟨k, rfl⟩ := hmem
    rw [map_neg, activeInverseVector_eval f I hdet]
    simp [Pi.single_apply]
    split_ifs <;> norm_num
  obtain ⟨δ, hδ, hp⟩ := halfspace_one_sided_perturbation f h hx.1 hdir
  have hh := hmax _ hp
  simp only [map_add, map_smul, map_neg, smul_eq_mul] at hh
  nlinarith

/-- A supporting functional at a simple vertex remains supporting after changing
supports, provided the same labelled active basis is tight at the new point. -/
theorem fixed_normals_transfer_maximum
    (f : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ) (h k : ι → ℝ)
    (hs : IsSimpleHalfspace f h) {x z : Fin d → ℝ}
    (hx : x ∈ (halfspaceRegion f h).extremePoints ℝ)
    (I : Fin d ↪ ι) (hI : ∀ j, f (I j) x = h (I j))
    (hz : ∀ j, f (I j) z = k (I j))
    (u : (Fin d → ℝ) →L[ℝ] ℝ)
    (hmax : ∀ y ∈ halfspaceRegion f h, u y ≤ u x) :
    ∀ y ∈ halfspaceRegion f k, u y ≤ u z := by
  have hdet := (simple_active_minor_spans f h hs hx I hI).2
  have hcoeff := maximizing_functional_active_coefficients_nonneg f h hs hx I hI u hmax
  intro y hy
  let A := facetCoefficientMatrix (fun j => f (I j))
  let l : (Fin d → ℝ) →L[ℝ] ℝ :=
    u.comp (Matrix.mulVecLin A⁻¹).toContinuousLinearMap
  have hexp := UnitNormalization.coefficient_expansion l (A *ᵥ (y - z))
  have hcancel : A⁻¹ *ᵥ (A *ᵥ (y - z)) = y - z := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  have hleft : (∑ j, u (activeInverseVector f I j) * (f (I j) y - k (I j))) = u y - u z := by
    have hr : l (A *ᵥ (y - z)) = u y - u z := by
      change u (A⁻¹ *ᵥ (A *ᵥ (y - z))) = _
      rw [hcancel, map_sub]
    rw [hr] at hexp
    simpa only [l, UnitNormalization.coefficients, ContinuousLinearMap.coe_comp,
      Function.comp_apply, LinearMap.coe_toContinuousLinearMap', Matrix.mulVecLin_apply,
      activeInverseVector, A, facetCoefficientMatrix_mulVec, map_sub, hz] using hexp
  have hnonpos : (∑ j, u (activeInverseVector f I j) * (f (I j) y - k (I j))) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j hj
    exact mul_nonpos_of_nonneg_of_nonpos (hcoeff j) (sub_nonpos.mpr (hy (I j)))
  rw [hleft] at hnonpos
  linarith

end NormalProjective

end

/- Source: NormalProjective/NormalInterpolation.lean -/
section
/-! # Exact interpolation of normally equivalent simple halfspace polytopes -/
open Set Matrix
open scoped BigOperators
namespace NormalProjective
variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem compact_halfspace_max_vertex
    (f : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ) (h : ι → ℝ)
    (hc : IsCompact (halfspaceRegion f h)) (hn : (halfspaceRegion f h).Nonempty)
    (u : (Fin d → ℝ) →L[ℝ] ℝ) :
    ∃ v : HalfspaceVertices f h, ∀ y ∈ halfspaceRegion f h, u y ≤ u v.val := by
  have hvfin := halfspace_extremePoints_finite f h
  obtain ⟨v, hv, hmax⟩ := hvfin.isCompact.exists_isMaxOn
    (compact_halfspace_has_extremePoint f h hc hn) u.continuous.continuousOn
  refine ⟨⟨v, hv⟩, ?_⟩
  have hh : halfspaceRegion f h ⊆ {y | u y ≤ u v} := by
    rw [compact_halfspace_eq_convexHull_extremePoints f h hc]
    apply convexHull_min hmax
    simpa [halfspaceRegion] using
      convex_halfspaceRegion (ι := Unit) (fun _ => u.toLinearMap) (fun _ => u v)
  exact hh

def interpolatedSupport (h k : ι → ℝ) (t : ℝ) : ι → ℝ :=
  fun i => (1 - t) * h i + t * k i

def interpolatedVertex (f : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ) (h k : ι → ℝ)
    (e : HalfspaceVertices f h ≃ HalfspaceVertices f k) (t : ℝ)
    (v : HalfspaceVertices f h) : Fin d → ℝ :=
  (1 - t) • v.val + t • (e v).val

theorem interpolatedVertex_mem
    (f : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ) (h k : ι → ℝ)
    (e : HalfspaceVertices f h ≃ HalfspaceVertices f k) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (v : HalfspaceVertices f h) :
    interpolatedVertex f h k e t v ∈ halfspaceRegion f (interpolatedSupport h k t) := by
  intro i
  change f i ((1 - t) • v.val + t • (e v).val) ≤ (1 - t) * h i + t * k i
  simp only [map_add, map_smul, smul_eq_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (v.property.1 i) (sub_nonneg.mpr ht.2))
    (mul_le_mul_of_nonneg_left ((e v).property.1 i) ht.1)

theorem interpolatedVertex_incidence
    (f : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ) (h k : ι → ℝ)
    (e : HalfspaceVertices f h ≃ HalfspaceVertices f k)
    (he : ∀ (v : HalfspaceVertices f h) i, f i v.val = h i ↔ f i (e v).val = k i)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (v : HalfspaceVertices f h) (i : ι) :
    f i (interpolatedVertex f h k e t v) = interpolatedSupport h k t i ↔
      f i v.val = h i := by
  simp only [interpolatedVertex, interpolatedSupport, map_add, map_smul, smul_eq_mul]
  constructor
  · intro hh
    by_contra hne
    have ha : 0 < h i - f i v.val :=
      sub_pos.mpr (lt_of_le_of_ne (v.property.1 i) hne)
    have hb : 0 < k i - f i (e v).val :=
      sub_pos.mpr (lt_of_le_of_ne ((e v).property.1 i) (fun hz => hne ((he v i).mpr hz)))
    by_cases ht0 : t = 0
    · simp only [ht0, sub_zero, one_mul, zero_mul, add_zero] at hh
      exact hne hh
    · have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have hpos := mul_pos htp hb
      have hnonneg := mul_nonneg (sub_nonneg.mpr ht.2) ha.le
      nlinarith
  · intro hh
    rw [hh, (he v i).mp hh]

theorem interpolatedVertex_is_vertex
    (f : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ) (h k : ι → ℝ)
    (hs : IsSimpleHalfspace f h)
    (e : HalfspaceVertices f h ≃ HalfspaceVertices f k)
    (he : ∀ (v : HalfspaceVertices f h) i, f i v.val = h i ↔ f i (e v).val = k i)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (v : HalfspaceVertices f h) :
    interpolatedVertex f h k e t v ∈
      (halfspaceRegion f (interpolatedSupport h k t)).extremePoints ℝ := by
  obtain ⟨I, hI, hli⟩ := extremePoint_has_active_basis f h v.property
  apply nonsingular_tight_minor_is_vertex f (interpolatedSupport h k t) I
    (facetCoefficientMatrix_det_ne_zero (fun j => f (I j)) hli)
    (interpolatedVertex_mem f h k e ht v)
  exact fun j => (interpolatedVertex_incidence f h k e he ht v (I j)).mpr (hI j)

/-- The whole interpolated halfspace region is the finite convex hull of the
interpolated vertices. This proves boundedness and excludes every extra vertex. -/
theorem fixed_normals_interpolated_hull
    (f : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ) (h k : ι → ℝ)
    (hc : IsCompact (halfspaceRegion f h)) (hn : (halfspaceRegion f h).Nonempty)
    (hs : IsSimpleHalfspace f h)
    (e : HalfspaceVertices f h ≃ HalfspaceVertices f k)
    (he : ∀ (v : HalfspaceVertices f h) i, f i v.val = h i ↔ f i (e v).val = k i)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    halfspaceRegion f (interpolatedSupport h k t) =
      convexHull ℝ (Set.range (interpolatedVertex f h k e t)) := by
  classical
  letI : Fintype (HalfspaceVertices f h) := (halfspace_extremePoints_finite f h).fintype
  have hclosed := (Set.finite_range (interpolatedVertex f h k e t)).isClosed_convexHull ℝ
  apply Set.Subset.antisymm
  · intro y hy
    by_contra hyout
    obtain ⟨u, c, hsep, hcy⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ _) hclosed hyout
    obtain ⟨v, hvmax⟩ := compact_halfspace_max_vertex f h hc hn u
    obtain ⟨I, hI, _⟩ := extremePoint_has_active_basis f h v.property
    have hzt : ∀ j, f (I j) (interpolatedVertex f h k e t v) =
        interpolatedSupport h k t (I j) :=
      fun j => (interpolatedVertex_incidence f h k e he ht v (I j)).mpr (hI j)
    have hmax := fixed_normals_transfer_maximum f h (interpolatedSupport h k t)
      hs v.property I hI hzt u hvmax y hy
    have hzc := hsep _ (subset_convexHull ℝ _ ⟨v, rfl⟩)
    linarith
  · apply convexHull_min
    · rintro y ⟨v, rfl⟩
      exact interpolatedVertex_mem f h k e ht v
    · exact convex_halfspaceRegion f _

theorem fixed_normals_interpolated_compact
    (f : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ) (h k : ι → ℝ)
    (hc : IsCompact (halfspaceRegion f h)) (hn : (halfspaceRegion f h).Nonempty)
    (hs : IsSimpleHalfspace f h)
    (e : HalfspaceVertices f h ≃ HalfspaceVertices f k)
    (he : ∀ (v : HalfspaceVertices f h) i, f i v.val = h i ↔ f i (e v).val = k i)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IsCompact (halfspaceRegion f (interpolatedSupport h k t)) := by
  classical
  letI : Fintype (HalfspaceVertices f h) := (halfspace_extremePoints_finite f h).fintype
  rw [fixed_normals_interpolated_hull f h k hc hn hs e he ht]
  exact (Set.finite_range _).isCompact_convexHull ℝ

def interpolatedVertexEquiv
    (f : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ) (h k : ι → ℝ)
    (hc : IsCompact (halfspaceRegion f h)) (hn : (halfspaceRegion f h).Nonempty)
    (hs : IsSimpleHalfspace f h)
    (e : HalfspaceVertices f h ≃ HalfspaceVertices f k)
    (he : ∀ (v : HalfspaceVertices f h) i, f i v.val = h i ↔ f i (e v).val = k i)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HalfspaceVertices f h ≃ HalfspaceVertices f (interpolatedSupport h k t) := by
  classical
  let F (v : HalfspaceVertices f h) :
      HalfspaceVertices f (interpolatedSupport h k t) :=
    ⟨interpolatedVertex f h k e t v, interpolatedVertex_is_vertex f h k hs e he ht v⟩
  apply Equiv.ofBijective F
  constructor
  · intro v w hvw
    apply extreme_activeFacetSet_injective f h
    ext i
    change f i v.val = h i ↔ f i w.val = h i
    rw [← interpolatedVertex_incidence f h k e he ht v i,
      ← interpolatedVertex_incidence f h k e he ht w i]
    have hval := congrArg Subtype.val hvw
    change interpolatedVertex f h k e t v = interpolatedVertex f h k e t w at hval
    rw [hval]
  · intro y
    have hy := y.property
    change y.val ∈ (halfspaceRegion f (interpolatedSupport h k t)).extremePoints ℝ at hy
    rw [fixed_normals_interpolated_hull f h k hc hn hs e he ht] at hy
    obtain ⟨v, hv⟩ := extremePoints_convexHull_subset hy
    exact ⟨v, Subtype.ext hv⟩

end NormalProjective

end

/- Source: NormalProjective/AffineGeometry.lean -/
section
/-! # Affine transport of genuine carriers, faces, and raw halfspace data -/
open Set Filter
open scoped Topology
namespace NormalProjective
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]

theorem affine_decomposition (a : E ≃ᵃ[ℝ] E) (x : E) :
    a x = a.linear x + a 0 := by
  simpa using a.map_vadd (0 : E) x

theorem affine_pull_value (a : E ≃ᵃ[ℝ] E) (u : E →L[ℝ] ℝ) (y : E) :
    u (a.symm y) =
      (u.comp a.symm.linear.toContinuousLinearMap) y + u (a.symm 0) := by
  rw [affine_decomposition a.symm y, map_add]
  rfl

theorem isExposed_affine_image (a : E ≃ᵃ[ℝ] E) {K F : Set E}
    (hF : IsExposed ℝ K F) : IsExposed ℝ (a '' K) (a '' F) := by
  intro hn
  obtain ⟨_, ⟨x₀, hx₀, rfl⟩⟩ := hn
  obtain ⟨u, hu⟩ := hF ⟨x₀, hx₀⟩
  let v := u.comp a.symm.linear.toContinuousLinearMap
  have hv (x : E) : v (a x) = u x - u (a.symm 0) := by
    have hh := affine_pull_value a u (a x)
    rw [a.symm_apply_apply] at hh
    change u x = v (a x) + u (a.symm 0) at hh
    linarith
  refine ⟨v, ?_⟩
  ext y
  obtain ⟨x, rfl⟩ := a.surjective y
  rw [a.injective.mem_set_image, hu]
  constructor
  · rintro ⟨hx, hmax⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [hv, hv]
    exact sub_le_sub_right (hmax z hz) _
  · rintro ⟨hx, hmax⟩
    have hx' : x ∈ K := a.injective.mem_set_image.mp hx
    refine ⟨hx', fun z hz => ?_⟩
    have hh := hmax (a z) ⟨z, hz, rfl⟩
    rw [hv, hv] at hh
    exact (sub_le_sub_iff_right _).mp hh

theorem affine_image_extremePoints (a : E ≃ᵃ[ℝ] E) (K : Set E) :
    a '' K.extremePoints ℝ = (a '' K).extremePoints ℝ := by
  ext y
  obtain ⟨x, rfl⟩ := a.surjective y
  have hseg : ∀ x y, a '' openSegment ℝ x y = openSegment ℝ (a x) (a y) :=
    fun x y => image_openSegment ℝ a.toAffineMap x y
  rw [a.injective.mem_set_image]
  constructor
  · intro hx
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ hsegx
    have hxseg : x ∈ openSegment ℝ u v := by
      apply a.injective.mem_set_image.mp
      rw [hseg]
      exact hsegx
    exact congrArg a (hx.2 hu hv hxseg)
  · intro hx
    refine ⟨a.injective.mem_set_image.mp hx.1, ?_⟩
    intro u hu v hv hxseg
    apply a.injective
    apply hx.2 ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    rw [← hseg]
    exact ⟨x, hxseg, rfl⟩

def affineData (a : E ≃ᵃ[ℝ] E) (p : HalfspaceData ι E) : HalfspaceData ι E :=
  (fun i => (p.1 i).comp a.symm.linear.toContinuousLinearMap,
    fun i => p.2 i - p.1 i (a.symm 0))

theorem affineData_slack (a : E ≃ᵃ[ℝ] E) (p : HalfspaceData ι E) (i : ι) (y : E) :
    (affineData a p).1 i y - (affineData a p).2 i =
      p.1 i (a.symm y) - p.2 i := by
  rw [affine_pull_value a (p.1 i) y]
  change (p.1 i).comp a.symm.linear.toContinuousLinearMap y -
    (p.2 i - p.1 i (a.symm 0)) = _
  ring

theorem dataRegion_affineData (a : E ≃ᵃ[ℝ] E) (p : HalfspaceData ι E) :
    dataRegion (affineData a p) = a '' dataRegion p := by
  ext y
  constructor
  · intro hy
    refine ⟨a.symm y, fun i => ?_, a.apply_symm_apply y⟩
    have hh := sub_nonpos.mpr (hy i)
    change (affineData a p).1 i y - (affineData a p).2 i ≤ 0 at hh
    rw [affineData_slack] at hh
    exact sub_nonpos.mp hh
  · rintro ⟨x, hx, rfl⟩ i
    apply sub_nonpos.mp
    change (affineData a p).1 i (a x) - (affineData a p).2 i ≤ 0
    rw [affineData_slack, a.symm_apply_apply]
    exact sub_nonpos.mpr (hx i)

theorem facet_affineData (a : E ≃ᵃ[ℝ] E) (p : HalfspaceData ι E) (i : ι) :
    {y ∈ dataRegion (affineData a p) |
      (affineData a p).1 i y = (affineData a p).2 i} =
      a '' {x ∈ dataRegion p | p.1 i x = p.2 i} := by
  ext y
  constructor
  · rintro ⟨hy, hyi⟩
    rw [dataRegion_affineData] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    have hh := sub_eq_zero.mpr hyi
    rw [affineData_slack, a.symm_apply_apply] at hh
    exact sub_eq_zero.mp hh
  · rintro ⟨x, ⟨hx, hxi⟩, rfl⟩
    refine ⟨by rw [dataRegion_affineData]; exact ⟨x, hx, rfl⟩, ?_⟩
    apply sub_eq_zero.mp
    rw [affineData_slack, a.symm_apply_apply, hxi, sub_self]

theorem continuous_affineData (a : E ≃ᵃ[ℝ] E) :
    Continuous (affineData a : HalfspaceData ι E → HalfspaceData ι E) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro i
    exact ((continuous_apply i).comp continuous_fst).clm_comp continuous_const
  · apply continuous_pi
    intro i
    exact ((continuous_apply i).comp continuous_snd).sub
      (((continuous_apply i).comp continuous_fst).clm_apply continuous_const)

end NormalProjective

end

/- Source: NormalProjective/FacetNormals.lean -/
section
/-! # Interior strictness and uniqueness of the outward normal of a genuine facet -/
open Set Filter
open scoped Topology BigOperators
namespace NormalProjective

theorem interior_lt_support
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (f : E →L[ℝ] ℝ) (hf : f ≠ 0) (h : ℝ)
    (hK : ∀ y ∈ K, f y ≤ h) {x : E} (hx : x ∈ interior K) : f x < h := by
  have hxK : x ∈ K := interior_subset hx
  apply lt_of_le_of_ne (hK x hxK)
  intro heq
  have hne : ∃ v : E, f v ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hf
    ext v
    exact hn v
  obtain ⟨v, hv⟩ := hne
  let w : E := (f v)⁻¹ • v
  have hw : f w = 1 := by simp [w, hv]
  have hline : ContinuousAt (fun t : ℝ => x + t • w) 0 :=
    (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, x + t • w ∈ K := by
    apply hline.eventually
    simpa using mem_interior_iff_mem_nhds.mp hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have ht : (0 : ℝ) < ε / 2 := by linarith
  have hb : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]
    linarith
  have hh := hK _ (hball hb)
  simp only [map_add, map_smul, smul_eq_mul, hw, mul_one, heq] at hh
  linarith

namespace UnitNormalization
variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem regular_interior_strict (p : RegularData d ι) {x : Space d}
    (hx : x ∈ interior (dataRegion p.data)) (i : ι) :
    p.data.1 i x < p.data.2 i :=
  interior_lt_support (dataRegion p.data) (p.data.1 i) (p.normal_ne_zero i)
    (p.data.2 i) (fun y hy => hy i) hx

/-- Equality of a genuine facet, together with its supporting orientation,
determines its normal and support up to one positive scalar. -/
theorem positive_multiple_of_same_facet
    (p : RegularData d ι) (i : ι) (g : Space d →L[ℝ] ℝ) (hg : g ≠ 0) (b : ℝ)
    (hvalid : ∀ x ∈ dataRegion p.data, g x ≤ b)
    (hfacet : {x ∈ dataRegion p.data | p.data.1 i x = p.data.2 i} =
      {x ∈ dataRegion p.data | g x = b}) :
    ∃ c : ℝ, 0 < c ∧ g = c • p.data.1 i ∧ b = c * p.data.2 i := by
  obtain ⟨w, hwK, hwi, hwstrict⟩ := p.strict_facet_point i
  have hwg : g w = b := by
    have hm : w ∈ {x ∈ dataRegion p.data | p.data.1 i x = p.data.2 i} := ⟨hwK, hwi⟩
    rw [hfacet] at hm
    exact hm.2
  have hker (v : Space d) (hv : p.data.1 i v = 0) : g v = 0 := by
    have hvactive : ∀ j, p.data.1 j w = p.data.2 j → p.data.1 j v = 0 := by
      intro j hj
      by_cases hji : j = i
      · simpa [hji] using hv
      · exact False.elim ((ne_of_lt (hwstrict j hji)) hj)
    obtain ⟨δ, hδ, hp, hm⟩ := halfspace_two_sided_perturbation
      (fun j => (p.data.1 j).toLinearMap) p.data.2 hwK hvactive
    have hpt : p.data.1 i (w + δ • v) = p.data.2 i := by simp [hwi, hv]
    have hmt : p.data.1 i (w - δ • v) = p.data.2 i := by simp [hwi, hv]
    have hgp : g (w + δ • v) = b := by
      have hm : w + δ • v ∈ {x ∈ dataRegion p.data | p.data.1 i x = p.data.2 i} := ⟨hp, hpt⟩
      rw [hfacet] at hm
      exact hm.2
    have hgm : g (w - δ • v) = b := by
      have hm : w - δ • v ∈ {x ∈ dataRegion p.data | p.data.1 i x = p.data.2 i} := ⟨hm, hmt⟩
      rw [hfacet] at hm
      exact hm.2
    simp only [map_add, map_sub, map_smul, smul_eq_mul] at hgp hgm
    have hprod : δ * g v = 0 := by linarith
    exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hδ)
  have hne : ∃ v : Space d, p.data.1 i v ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply p.normal_ne_zero i
    ext v
    exact hn v
  obtain ⟨v, hv⟩ := hne
  let z : Space d := (p.data.1 i v)⁻¹ • v
  have hz : p.data.1 i z = 1 := by simp [z, hv]
  let c := g z
  have hgform : g = c • p.data.1 i := by
    ext x
    have hzker : p.data.1 i (x - p.data.1 i x • z) = 0 := by simp [hz]
    have hh := hker _ hzker
    simp only [map_sub, map_smul, smul_eq_mul] at hh
    change g x = c * p.data.1 i x
    dsimp only [c]
    nlinarith
  have hb : b = c * p.data.2 i := by
    have hh := congrArg (fun f : Space d →L[ℝ] ℝ => f w) hgform
    simpa only [hwg, ContinuousLinearMap.smul_apply, smul_eq_mul, hwi] using hh
  obtain ⟨x, hx⟩ := p.full_dimensional
  have hfi := regular_interior_strict p hx i
  have hgi := interior_lt_support _ g hg b hvalid hx
  rw [hgform, hb] at hgi
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul] at hgi
  refine ⟨c, ?_, hgform, hb⟩
  by_contra hn
  have hc : c ≤ 0 := le_of_not_gt hn
  have hmul := mul_nonpos_of_nonpos_of_nonneg hc (sub_nonneg.mpr hfi.le)
  nlinarith

/-- Actual carrier and labelled facet equality determine a canonical presentation. -/
theorem presentation_eq_of_carrier_facets (P Q : CanonicalModel.Presentation d ι)
    (hK : P.carrier = Q.carrier) (hF : ∀ i, P.facet i = Q.facet i) : P = Q := by
  let p := ofCanonical P
  let q := ofCanonical Q
  have hpK : dataRegion p.data = P.carrier := by
    simpa only [p, presentation_ofCanonical] using (presentation_carrier p).symm
  have hqK : dataRegion q.data = Q.carrier := by
    simpa only [q, presentation_ofCanonical] using (presentation_carrier q).symm
  have hforms (i : ι) : q.data.1 i = p.data.1 i ∧ q.data.2 i = p.data.2 i := by
    have hvalid : ∀ x ∈ dataRegion p.data, q.data.1 i x ≤ q.data.2 i := by
      intro x hx
      have hxq : x ∈ dataRegion q.data := by rw [hqK, ← hK, ← hpK]; exact hx
      exact hxq i
    have hfacet : {x ∈ dataRegion p.data | p.data.1 i x = p.data.2 i} =
        {x ∈ dataRegion p.data | q.data.1 i x = q.data.2 i} := by
      rw [← presentation_facet p i]
      have hset : dataRegion p.data = dataRegion q.data := hpK.trans (hK.trans hqK.symm)
      rw [hset, ← presentation_facet q i]
      simpa only [p, q, presentation_ofCanonical] using hF i
    obtain ⟨c, hc, hform, hs⟩ := positive_multiple_of_same_facet
      p i (q.data.1 i) (q.normal_ne_zero i) (q.data.2 i) hvalid hfacet
    have hlp : length (p.data.1 i) = 1 := by
      simp [p, ofCanonical, length, coefficients_rowForm, P.unit_normal i]
    have hlq : length (q.data.1 i) = 1 := by
      simp [q, ofCanonical, length, coefficients_rowForm, Q.unit_normal i]
    have hh := congrArg length hform
    rw [hlq, length_pos_smul c hc, hlp, mul_one] at hh
    have hc1 : c = 1 := hh.symm
    simpa [hc1] using And.intro hform hs
  apply presentation_ext
  · funext i
    have hh := congrArg coefficients (hforms i).1
    simpa [p, q, ofCanonical] using hh.symm
  · funext i
    exact (hforms i).2.symm

end UnitNormalization
end NormalProjective

end

/- Source: NormalProjective/AffineAction.lean -/
section
/-! # Continuous affine action on actual labelled realizations -/
open Set Filter
open scoped Topology
namespace NormalProjective.UnitNormalization
open CanonicalModel
variable {d : ℕ} {ι : Type*} [Fintype ι]

def affineRegular (a : Space d ≃ᵃ[ℝ] Space d) (p : RegularData d ι) :
    RegularData d ι where
  data := affineData a p.data
  normal_ne_zero := by
    intro i hi
    apply p.normal_ne_zero i
    ext z
    obtain ⟨y, rfl⟩ := a.symm.linear.surjective z
    have hh := congrArg (fun f : Space d →L[ℝ] ℝ => f y) hi
    exact hh
  compact := by
    rw [dataRegion_affineData]
    exact p.compact.image a.continuous_of_finiteDimensional
  full_dimensional := by
    rw [dataRegion_affineData]
    let b := (AffineEquiv.toContinuousAffineEquiv a).toHomeomorph
    change (interior (b '' dataRegion p.data)).Nonempty
    rw [← b.image_interior]
    exact p.full_dimensional.image b
  strict_facet_point := by
    intro i
    obtain ⟨x, hx, hxi, hxs⟩ := p.strict_facet_point i
    refine ⟨a x, ?_, ?_, ?_⟩
    · rw [dataRegion_affineData]
      exact ⟨x, hx, rfl⟩
    · apply sub_eq_zero.mp
      rw [affineData_slack, a.symm_apply_apply, hxi, sub_self]
    · intro j hji
      apply sub_neg.mp
      rw [affineData_slack, a.symm_apply_apply]
      exact sub_neg.mpr (hxs j hji)

theorem continuous_affineRegular (a : Space d ≃ᵃ[ℝ] Space d) :
    Continuous (affineRegular a : RegularData d ι → RegularData d ι) := by
  apply continuous_induced_rng.mpr
  exact (continuous_affineData a).comp continuous_data

theorem affineRegular_carrier (a : Space d ≃ᵃ[ℝ] Space d) (p : RegularData d ι) :
    (presentation (affineRegular a p)).carrier = a '' (presentation p).carrier := by
  rw [presentation_carrier, presentation_carrier]
  exact dataRegion_affineData a p.data

theorem affineRegular_facet (a : Space d ≃ᵃ[ℝ] Space d) (p : RegularData d ι) (i : ι) :
    (presentation (affineRegular a p)).facet i = a '' (presentation p).facet i := by
  rw [presentation_facet, presentation_facet]
  exact facet_affineData a p.data i

def affineFaceOrderIso (a : Space d ≃ᵃ[ℝ] Space d) (p : RegularData d ι) :
    (presentation p).Faces ≃o (presentation (affineRegular a p)).Faces where
  toFun F := ⟨a '' F.val, by
    rw [affineRegular_carrier]
    exact isExposed_affine_image a F.property⟩
  invFun G := ⟨a.symm '' G.val, by
    have hh := isExposed_affine_image a.symm G.property
    have heq : a.symm '' (presentation (affineRegular a p)).carrier =
        (presentation p).carrier := by
      rw [affineRegular_carrier, Set.image_image]
      simp
    simpa only [heq] using hh⟩
  left_inv F := by
    apply Subtype.ext
    change a.symm '' (a '' F.val) = F.val
    rw [Set.image_image]
    simp
  right_inv G := by
    apply Subtype.ext
    change a '' (a.symm '' G.val) = G.val
    rw [Set.image_image]
    simp
  map_rel_iff' := by
    intro F G
    constructor
    · intro h x hx
      have hh := h ⟨x, hx, rfl⟩
      exact a.injective.mem_set_image.mp hh
    · exact fun h => Set.image_mono h

def facetFace (p : RegularData d ι) (i : ι) : (presentation p).Faces :=
  ⟨(presentation p).facet i, by
    rw [presentation_carrier, presentation_facet]
    have hset : {x ∈ dataRegion p.data | p.data.1 i x = p.data.2 i} =
        tightFace (fun j => (p.data.1 j).toLinearMap) p.data.2 {i} := by
      ext x
      simp [tightFace, dataRegion]
    rw [hset]
    simpa only [dataRegion] using
      tightFace_isExposed (fun j => (p.data.1 j).toLinearMap) p.data.2 {i}⟩

theorem affineRegular_sameLabelledType (a : Space d ≃ᵃ[ℝ] Space d) (p : RegularData d ι) :
    (presentation p).SameLabelledType (presentation (affineRegular a p)) := by
  refine ⟨affineFaceOrderIso a p, fun i => ?_⟩
  refine ⟨facetFace p i, rfl, ?_⟩
  change a '' (presentation p).facet i = (presentation (affineRegular a p)).facet i
  exact (affineRegular_facet a p i).symm

def affinePresentation (a : Space d ≃ᵃ[ℝ] Space d) (P : Presentation d ι) :
    Presentation d ι := presentation (affineRegular a (ofCanonical P))

theorem continuous_affinePresentation (a : Space d ≃ᵃ[ℝ] Space d) :
    Continuous (affinePresentation a : Presentation d ι → Presentation d ι) :=
  continuous_presentation.comp ((continuous_affineRegular a).comp continuous_ofCanonical)

theorem affinePresentation_carrier (a : Space d ≃ᵃ[ℝ] Space d) (P : Presentation d ι) :
    (affinePresentation a P).carrier = a '' P.carrier := by
  simpa only [affinePresentation, presentation_ofCanonical] using
    affineRegular_carrier a (ofCanonical P)

theorem affinePresentation_facet (a : Space d ≃ᵃ[ℝ] Space d) (P : Presentation d ι) (i : ι) :
    (affinePresentation a P).facet i = a '' P.facet i := by
  simpa only [affinePresentation, presentation_ofCanonical] using
    affineRegular_facet a (ofCanonical P) i

theorem affinePresentation_sameLabelledType (a : Space d ≃ᵃ[ℝ] Space d) (P : Presentation d ι) :
    P.SameLabelledType (affinePresentation a P) := by
  simpa only [affinePresentation, presentation_ofCanonical] using
    affineRegular_sameLabelledType a (ofCanonical P)

end NormalProjective.UnitNormalization

namespace NormalProjective.CanonicalModel.Realization
open UnitNormalization
variable {d : ℕ} {ι : Type*} [Fintype ι] {R : Presentation d ι}

def affineAction (a : Space d ≃ᵃ[ℝ] Space d) (P : Realization R) : Realization R :=
  ⟨affinePresentation a P.val, P.property.trans (affinePresentation_sameLabelledType a P.val)⟩

theorem continuous_affineAction (a : Space d ≃ᵃ[ℝ] Space d) :
    Continuous (affineAction a : Realization R → Realization R) :=
  ((continuous_affinePresentation a).comp continuous_subtype_val).subtype_mk _

theorem affineAction_related (a : Space d ≃ᵃ[ℝ] Space d) (P : Realization R) :
    AffineRelated P (affineAction a P) :=
  ⟨a, (affinePresentation_carrier a P.val).symm,
    fun i => (affinePresentation_facet a P.val i).symm⟩

theorem affineAction_normal (a : Space d ≃ᵃ[ℝ] Space d) {P Q : Realization R}
    (h : NormalStep P Q) : NormalStep (affineAction a P) (affineAction a Q) := by
  change (fun i => unitRow ((rowForm (P.val.normal i)).comp
    a.symm.linear.toContinuousLinearMap)) =
    (fun i => unitRow ((rowForm (Q.val.normal i)).comp
      a.symm.linear.toContinuousLinearMap))
  rw [h]

theorem affineAction_projective (a : Space d ≃ᵃ[ℝ] Space d) {P Q : Realization R}
    (h : ProjectiveStep P Q) : ProjectiveStep (affineAction a P) (affineAction a Q) :=
  (affineRelated_symm (affineAction_related a P)).projectiveStep.trans
    (h.trans (affineAction_related a Q).projectiveStep)

theorem PNWord.affineAction (a : Space d ≃ᵃ[ℝ] Space d) {P Q : Realization R} {p n : ℕ}
    (h : PNWord P Q p n) : PNWord (affineAction a P) (affineAction a Q) p n := by
  induction h with
  | nil P => exact PNWord.nil _
  | projective hs ht ih => exact PNWord.projective (affineAction_projective a hs) ih
  | normal hs ht ih => exact PNWord.normal (affineAction_normal a hs) ih

theorem affineAction_inverse (a : Space d ≃ᵃ[ℝ] Space d) (P : Realization R) :
    affineAction a.symm (affineAction a P) = P := by
  apply Subtype.ext
  apply presentation_eq_of_carrier_facets
  · change (affinePresentation a.symm (affinePresentation a P.val)).carrier = P.val.carrier
    rw [affinePresentation_carrier, affinePresentation_carrier, Set.image_image]
    simp
  · intro i
    change (affinePresentation a.symm (affinePresentation a P.val)).facet i = P.val.facet i
    rw [affinePresentation_facet, affinePresentation_facet, Set.image_image]
    simp

theorem PNWord.of_affineAction (a : Space d ≃ᵃ[ℝ] Space d)
    {P Q : Realization R} {p n : ℕ}
    (h : PNWord (Realization.affineAction a P) (Realization.affineAction a Q) p n) : PNWord P Q p n := by
  have hh := h.affineAction a.symm
  simpa only [affineAction_inverse] using hh

def rebase {S : Presentation d ι} (h : S.SameLabelledType R)
    (P : Realization R) : Realization S := ⟨P.val, h.trans P.property⟩

theorem PNWord.rebase {S : Presentation d ι} (hSR : S.SameLabelledType R)
    {P Q : Realization R} {p n : ℕ} (h : PNWord P Q p n) :
    PNWord (rebase hSR P) (rebase hSR Q) p n := by
  induction h with
  | nil P => exact PNWord.nil _
  | projective hs ht ih =>
      refine PNWord.projective (Q := Realization.rebase hSR _) ?_ ih
      exact hs
  | normal hs ht ih =>
      refine PNWord.normal (Q := Realization.rebase hSR _) ?_ ih
      exact hs

end NormalProjective.CanonicalModel.Realization

end

/- Source: NormalProjective/SupportNormalization.lean -/
section
/-! # Positive support normalization is equality of canonical presentations -/
open Set Filter
open scoped Topology
namespace NormalProjective.UnitNormalization
variable {d : ℕ} {ι : Type*} [Fintype ι]

@[simp] theorem rowForm_coefficients (f : Space d →L[ℝ] ℝ) :
    rowForm (coefficients f) = f := by
  ext x
  rw [rowForm_apply]
  exact coefficient_expansion f x

def scaleData (p : HalfspaceData ι (Space d)) (r : ι → ℝ) :
    HalfspaceData ι (Space d) := (fun i => r i • p.1 i, fun i => r i * p.2 i)

theorem dataRegion_scaleData (p : HalfspaceData ι (Space d)) (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) : dataRegion (scaleData p r) = dataRegion p := by
  ext x
  change (∀ i, r i * p.1 i x ≤ r i * p.2 i) ↔ ∀ i, p.1 i x ≤ p.2 i
  exact forall_congr' (fun i => mul_le_mul_iff_right₀ (hr i))

def scaleRegular (p : RegularData d ι) (r : ι → ℝ) (hr : ∀ i, 0 < r i) :
    RegularData d ι where
  data := scaleData p.data r
  normal_ne_zero := fun i => smul_ne_zero (ne_of_gt (hr i)) (p.normal_ne_zero i)
  compact := (dataRegion_scaleData p.data r hr).symm ▸ p.compact
  full_dimensional := (dataRegion_scaleData p.data r hr).symm ▸ p.full_dimensional
  strict_facet_point := by
    intro i
    obtain ⟨x, hx, hxi, hxs⟩ := p.strict_facet_point i
    refine ⟨x, (dataRegion_scaleData p.data r hr).symm ▸ hx, ?_, ?_⟩
    · change r i * p.data.1 i x = r i * p.data.2 i
      rw [hxi]
    · intro j hji
      change r j * p.data.1 j x < r j * p.data.2 j
      exact (mul_lt_mul_iff_right₀ (hr j)).mpr (hxs j hji)

theorem presentation_scaleRegular (p : RegularData d ι) (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) : presentation (scaleRegular p r hr) = presentation p :=
  presentation_eq_of_positive_rows p (scaleRegular p r hr) r hr
    (fun i => rfl) (fun i => rfl)

def normalizedRegular (p : RegularData d ι) (hp : ∀ i, 0 < p.data.2 i) :
    RegularData d ι :=
  scaleRegular p (fun i => (p.data.2 i)⁻¹) (fun i => inv_pos.mpr (hp i))

def normalizedMatrix (p : RegularData d ι) : Matrix ι (Fin d) ℝ :=
  fun i => coefficients ((p.data.2 i)⁻¹ • p.data.1 i)

theorem normalizedRegular_data (p : RegularData d ι) (hp : ∀ i, 0 < p.data.2 i) :
    (normalizedRegular p hp).data =
      MatrixRealization.asData (normalizedMatrix p, fun _ => 1) := by
  apply Prod.ext
  · funext i
    change (p.data.2 i)⁻¹ • p.data.1 i =
      rowForm (coefficients ((p.data.2 i)⁻¹ • p.data.1 i))
    rw [rowForm_coefficients]
  · funext i
    exact inv_mul_cancel₀ (ne_of_gt (hp i))

theorem presentation_normalizedRegular (p : RegularData d ι)
    (hp : ∀ i, 0 < p.data.2 i) :
    presentation (normalizedRegular p hp) = presentation p :=
  presentation_scaleRegular p _ _

theorem continuousAt_normalizedMatrix (p : RegularData d ι)
    (hp : ∀ i, p.data.2 i ≠ 0) :
    ContinuousAt (normalizedMatrix : RegularData d ι → Matrix ι (Fin d) ℝ) p := by
  apply continuousAt_pi.mpr
  intro i
  apply continuous_coefficients.continuousAt.comp
  exact (((continuous_apply i).comp continuous_data.snd).continuousAt.inv₀ (hp i)).smul
    ((continuous_apply i).comp continuous_data.fst).continuousAt

theorem supports_pos_of_zero_interior (p : RegularData d ι)
    (hp : (0 : Space d) ∈ interior (dataRegion p.data)) : ∀ i, 0 < p.data.2 i := by
  intro i
  simpa only [map_zero] using regular_interior_strict p hp i

end NormalProjective.UnitNormalization

end

/- Source: NormalProjective/DimensionZero.lean -/
section
/-! # The zero-dimensional case is retained explicitly -/
namespace NormalProjective.CanonicalModel
open Realization
variable {ι : Type*} [Fintype ι]

theorem presentation_zero_eq (P Q : Presentation 0 ι) : P = Q := by
  have hι : IsEmpty ι := ⟨fun i => by
    have h := P.unit_normal i
    simpa using h⟩
  letI := hι
  apply UnitNormalization.presentation_ext
  · exact Subsingleton.elim _ _
  · exact Subsingleton.elim _ _

theorem zero_dimensional_word {R : Presentation 0 ι} (P Q : Realization R) :
    PNWord P Q 0 0 := by
  have hh : P = Q := Subtype.ext (presentation_zero_eq P.val Q.val)
  subst Q
  exact PNWord.nil P

theorem zero_dimensional_pn {R : Presentation 0 ι} (P Q : Realization R) :
    PNRelated P Q := ⟨0, 0, zero_dimensional_word P Q⟩

end NormalProjective.CanonicalModel

end
