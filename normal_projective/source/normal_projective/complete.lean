module
public import normal_projective.control
public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Logic.Relation
public import normal_projective.connected_classes
public import normal_projective.rank_obstruction
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.Convex.Combination

/-! Full normal-projective geometry: local control, components, and exact cube bounds.
All proof bodies are preserved verbatim from the recorded source fragments.
-/
@[expose] public section
noncomputable section

/- Source: NormalProjective/GlobalLocal.lean -/
section
/-! # Coordinate-independent local controllability of actual labelled polytopes -/
open Set Filter
open scoped Topology BigOperators
namespace NormalProjective
namespace UnitNormalization
variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem sameLabelledType_raw (p q : RegularData d ι)
    (h : (presentation p).SameLabelledType (presentation q)) :
    ∃ e : HalfspaceFaces (fun i => (p.data.1 i).toLinearMap) p.data.2 ≃o
      HalfspaceFaces (fun i => (q.data.1 i).toLinearMap) q.data.2,
      ∀ i, e ⟨tightFace (fun j => (p.data.1 j).toLinearMap) p.data.2 {i},
        tightFace_isExposed _ _ _⟩ =
        ⟨tightFace (fun j => (q.data.1 j).toLinearMap) q.data.2 {i},
          tightFace_isExposed _ _ _⟩ := by
  obtain ⟨e, he⟩ := h
  let f := (faceOrderEquiv p).symm.trans (e.trans (faceOrderEquiv q))
  refine ⟨f, fun i => ?_⟩
  obtain ⟨F, hF, heF⟩ := he i
  have hF' : (faceOrderEquiv p).symm
      ⟨tightFace (fun j => (p.data.1 j).toLinearMap) p.data.2 {i},
        tightFace_isExposed _ _ _⟩ = F := by
    apply Subtype.ext
    rw [hF, presentation_facet]
    ext x
    simp [faceOrderEquiv, tightFace, dataRegion]
  apply Subtype.ext
  change ((faceOrderEquiv q) (e ((faceOrderEquiv p).symm _))).val = _
  rw [hF']
  change (e F).val = _
  rw [heF, presentation_facet]
  ext x
  simp [tightFace, dataRegion]

theorem simple_iff_raw (p : RegularData d ι) :
    (presentation p).Simple ↔
      IsSimpleHalfspace (fun i => (p.data.1 i).toLinearMap) p.data.2 := by
  have hK : (presentation p).carrier =
      halfspaceRegion (fun i => (p.data.1 i).toLinearMap) p.data.2 :=
    presentation_carrier p
  have hcard (x : Space d) (hx : x ∈ dataRegion p.data) :
      Nat.card {i : ι // x ∈ (presentation p).facet i} =
      Nat.card (ActiveFacet (fun i => (p.data.1 i).toLinearMap) p.data.2 x) := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun i => by
      rw [presentation_facet]
      exact and_iff_right hx)
  constructor
  · intro hs x hx
    rw [← hcard x hx.1]
    apply hs x
    simpa only [hK] using hx
  · intro hs x hx
    have hx' : x ∈ (halfspaceRegion (fun i => (p.data.1 i).toLinearMap)
        p.data.2).extremePoints ℝ := by simpa only [hK] using hx
    rw [hcard x hx'.1]
    exact hs x hx'

theorem simple_of_sameLabelledType (p q : RegularData d ι)
    (hs : (presentation p).Simple)
    (h : (presentation p).SameLabelledType (presentation q)) :
    (presentation q).Simple := by
  obtain ⟨e, he⟩ := sameLabelledType_raw p q h
  let f := fun i => (p.data.1 i).toLinearMap
  let g := fun i => (q.data.1 i).toLinearMap
  let ev := faceIsoVertexEquiv f g p.data.2 q.data.2 p.compact q.compact e
  have hinc := faceIsoVertexEquiv_incidence f g p.data.2 q.data.2
    p.compact q.compact e he
  apply (simple_iff_raw q).mpr
  intro x hx
  let v := ev.symm ⟨x, hx⟩
  have hv := (simple_iff_raw p).mp hs v.val v.property
  have hc : Nat.card (ActiveFacet f p.data.2 v.val) =
      Nat.card (ActiveFacet g q.data.2 x) := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro i
    have hh := hinc v i
    simpa only [v, ev, Equiv.apply_symm_apply] using hh
  exact hc.symm.trans hv

end UnitNormalization

namespace CanonicalModel.Presentation
variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem Simple.of_sameLabelledType {P Q : Presentation d ι}
    (hs : P.Simple) (h : P.SameLabelledType Q) : Q.Simple := by
  simpa only [UnitNormalization.presentation_ofCanonical] using
    UnitNormalization.simple_of_sameLabelledType
      (UnitNormalization.ofCanonical P) (UnitNormalization.ofCanonical Q)
      (by simpa only [UnitNormalization.presentation_ofCanonical] using hs)
      (by simpa only [UnitNormalization.presentation_ofCanonical] using h)

end CanonicalModel.Presentation

namespace GenericCoordinates
open UnitNormalization
variable {n : ℕ} {ι : Type*} [Fintype ι]

def lastColumnEquiv (v : Space (n + 1)) (hv : v (Fin.last n) ≠ 0) :
    Space (n + 1) ≃ₗ[ℝ] Space (n + 1) where
  toFun x := x + x (Fin.last n) • (v - Pi.single (Fin.last n) 1)
  invFun y := y - (y (Fin.last n) / v (Fin.last n)) •
    (v - Pi.single (Fin.last n) 1)
  map_add' x y := by
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  map_smul' c x := by
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, RingHom.id_apply]
    ring
  left_inv x := by
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same, smul_eq_mul]
    field_simp [hv]
    <;> ring
  right_inv y := by
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same, smul_eq_mul]
    field_simp [hv]
    <;> ring

@[simp] theorem lastColumnEquiv_single (v : Space (n + 1))
    (hv : v (Fin.last n) ≠ 0) :
    lastColumnEquiv v hv (Pi.single (Fin.last n) 1) = v := by
  ext j
  simp only [lastColumnEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same,
    smul_eq_mul, one_mul]
  ring

theorem exists_generic_vector (p : RegularData (n + 1) ι) :
    ∃ v : Space (n + 1), v (Fin.last n) ≠ 0 ∧ ∀ i, p.data.1 i v ≠ 0 := by
  let f : Option ι → Module.Dual ℝ (Space (n + 1)) :=
    fun i => match i with
      | none => (ContinuousLinearMap.proj (Fin.last n)).toLinearMap
      | some i => (p.data.1 i).toLinearMap
  have hf : ∀ i, ∃ x, f i x ≠ 0 := by
    intro i
    cases i with
    | none => exact ⟨Pi.single (Fin.last n) 1, by simp [f]⟩
    | some i =>
        by_contra hn
        push_neg at hn
        apply p.normal_ne_zero i
        apply ContinuousLinearMap.ext
        intro x
        exact hn x
  obtain ⟨v, hv⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists f hf
  exact ⟨v, hv none, fun i => hv (some i)⟩

/-- One fixed affine chart centers the entire polytope and makes every last
normal coordinate nonzero. No projective or normal move is charged for changing
this chart: the final word will be conjugated back with the same counts. -/
theorem exists_generic_centered_chart (p : RegularData (n + 1) ι) :
    ∃ a : Space (n + 1) ≃ᵃ[ℝ] Space (n + 1),
      (∀ i, 0 < (affineRegular a p).data.2 i) ∧
      (∀ i, coefficients ((affineRegular a p).data.1 i) (Fin.last n) ≠ 0) := by
  obtain ⟨x₀, hx₀⟩ := p.full_dimensional
  obtain ⟨v, hv, hfi⟩ := exists_generic_vector p
  let T := lastColumnEquiv v hv
  let b := T.toAffineEquiv.trans (AffineEquiv.constVAdd ℝ (Space (n + 1)) x₀)
  refine ⟨b.symm, ?_, ?_⟩
  · intro i
    change 0 < p.data.2 i - p.data.1 i (b 0)
    have hb : b 0 = x₀ := by simp [b]
    rw [hb]
    exact sub_pos.mpr (regular_interior_strict p hx₀ i)
  · intro i
    change p.data.1 i (b.linear (Pi.single (Fin.last n) 1)) ≠ 0
    have hb : b.linear (Pi.single (Fin.last n) 1) = v := by
      change T (Pi.single (Fin.last n) 1) = v
      exact lastColumnEquiv_single v hv
    rw [hb]
    exact hfi i

end GenericCoordinates
end NormalProjective

namespace NormalProjective.CanonicalModel.Realization
open UnitNormalization
variable {ι : Type*} [Fintype ι]

/-- The local bound counts actual admissible moves, in the original coordinates,
for every simple realization and with no generic-coordinate hypothesis. -/
theorem local_word_neighbourhood_succ {n : ℕ} {R : Presentation (n + 1) ι}
    (P : Realization R) (hs : P.val.Simple) :
    ∀ᶠ Q : Realization R in 𝓝 P, PNWord P Q (n + 1) (n + 1) := by
  classical
  obtain ⟨a, hpos, hlast⟩ := GenericCoordinates.exists_generic_centered_chart (ofCanonical P.val)
  let r : Realization R → RegularData (n + 1) ι :=
    fun Q => affineRegular a (ofCanonical Q.val)
  have hr : Continuous r :=
    (continuous_affineRegular a).comp (continuous_ofCanonical.comp continuous_subtype_val)
  let p₀ := normalizedRegular (r P) hpos
  let A := normalizedMatrix (r P)
  have hp₀ : p₀.data = MatrixRealization.asData (A, fun _ => 1) :=
    normalizedRegular_data (r P) hpos
  have hpPres : presentation p₀ = (affineAction a P).val := by
    exact presentation_normalizedRegular (r P) hpos
  have hs₀ : (presentation p₀).Simple := by
    rw [hpPres]
    exact hs.of_sameLabelledType (affinePresentation_sameLabelledType a P.val)
  have hsA : IsSimpleHalfspace (fun i => (rowForm (A i)).toLinearMap) (fun _ => 1) := by
    have hh := (simple_iff_raw p₀).mp hs₀
    rw [hp₀] at hh
    exact hh
  have hA : ∀ i, A i (Fin.last n) ≠ 0 := by
    intro i
    change coefficients (((r P).data.2 i)⁻¹ • (r P).data.1 i) (Fin.last n) ≠ 0
    rw [coefficients_smul]
    exact mul_ne_zero (inv_ne_zero (ne_of_gt (hpos i))) (hlast i)
  have hlocal := LocalControl.normalized_local_neighbourhood p₀ A hp₀ hsA hA
  have hBcont : ContinuousAt (fun Q : Realization R => normalizedMatrix (r Q)) P :=
    (continuousAt_normalizedMatrix (r P) (fun i => ne_of_gt (hpos i))).comp hr.continuousAt
  have hnear := hBcont.eventually hlocal
  have hqpos : ∀ᶠ Q : Realization R in 𝓝 P, ∀ i, 0 < (r Q).data.2 i := by
    apply Filter.eventually_all.mpr
    intro i
    exact Filter.Tendsto.eventually_const_lt (hpos i)
      (((continuous_apply i).comp (continuous_data.comp hr).snd).continuousAt)
  filter_upwards [hnear, hqpos] with Q hQ hQpos
  obtain ⟨hB, hword⟩ := hQ
  let q₀ := normalizedRegular (r Q) hQpos
  have hq₀ : q₀.data = MatrixRealization.asData (normalizedMatrix (r Q), fun _ => 1) :=
    normalizedRegular_data (r Q) hQpos
  have hR : R.SameLabelledType (presentation p₀) := by
    rw [hpPres]
    exact (affineAction a P).property
  have hw := hword.rebase hR
  have hstart : rebase hR
      (⟨presentation p₀, Presentation.sameLabelledType_refl (presentation p₀)⟩ :
        Realization (presentation p₀)) = affineAction a P := by
    apply Subtype.ext
    exact hpPres
  have hend : rebase hR
      (MatrixRealization.realization (presentation p₀)
        (normalizedMatrix (r Q), fun _ => 1) hB) = affineAction a Q := by
    apply Subtype.ext
    change presentation (MatrixRealization.regular (presentation p₀)
      (normalizedMatrix (r Q), fun _ => 1) hB) = _
    have heq := MatrixRealization.regularData_ext
      ((MatrixRealization.regular_data (presentation p₀)
        (normalizedMatrix (r Q), fun _ => 1) hB).trans hq₀.symm)
    rw [heq]
    exact presentation_normalizedRegular (r Q) hQpos
  rw [hstart, hend] at hw
  exact hw.of_affineAction a

/-- Dimension zero is included explicitly; in positive dimensions the bound is
exactly d projective and d normal steps (identity moves are allowed). -/
theorem local_word_neighbourhood {d : ℕ} {R : Presentation d ι}
    (P : Realization R) (hs : P.val.Simple) :
    ∀ᶠ Q : Realization R in 𝓝 P, PNWord P Q d d := by
  cases d with
  | zero => exact Filter.Eventually.of_forall (fun Q => zero_dimensional_word P Q)
  | succ n => exact local_word_neighbourhood_succ P hs

theorem pn_equivalence {d : ℕ} {R : Presentation d ι} :
    Equivalence (PNRelated (R := R)) :=
  ⟨PNRelated.refl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- The orbit of every simple labelled polytope is open in the genuine
unit-normal/support realization topology. -/
theorem isOpen_pn_class {d : ℕ} {R : Presentation d ι} (hs : R.Simple)
    (P : Realization R) : IsOpen {Q : Realization R | PNRelated P Q} := by
  apply isOpen_iff_mem_nhds.mpr
  intro Q hPQ
  filter_upwards [local_word_neighbourhood Q (hs.of_sameLabelledType Q.property)] with U hQU
  exact hPQ.trans ⟨d, d, hQU⟩

end NormalProjective.CanonicalModel.Realization
end

/- Source: NormalProjective/NormalPath.lean -/
section
/-! # Every normal step has a continuous path of the same labelled face type -/
open Set Filter unitInterval
open scoped Topology
namespace NormalProjective.UnitNormalization
variable {d : ℕ} {ι : Type*} [Fintype ι]

def normalIntervalRegular (p : RegularData d ι) (k : ι → ℝ)
    (hk : ∃ y : Space d, ∀ i, p.data.1 i y < k i)
    (hs : (presentation p).Simple)
    (e : HalfspaceVertices (fun i => (p.data.1 i).toLinearMap) p.data.2 ≃
      HalfspaceVertices (fun i => (p.data.1 i).toLinearMap) k)
    (he : ∀ v i, p.data.1 i v.val = p.data.2 i ↔ p.data.1 i (e v).val = k i)
    (t : I) : RegularData d ι := by
  let f := fun i => (p.data.1 i).toLinearMap
  have hn : (dataRegion p.data).Nonempty := p.full_dimensional.mono interior_subset
  have hs' := (simple_iff_raw p).mp hs
  let ev := interpolatedVertexEquiv f p.data.2 k p.compact hn hs' e he t.property
  have he' : ∀ v i, f i v.val = p.data.2 i ↔
      f i (ev v).val = interpolatedSupport p.data.2 k t.val i := by
    intro v i
    exact (interpolatedVertex_incidence f p.data.2 k e he t.property v i).symm
  refine {
    data := (p.data.1, interpolatedSupport p.data.2 k t.val)
    normal_ne_zero := p.normal_ne_zero
    compact := fixed_normals_interpolated_compact f p.data.2 k p.compact hn hs' e he t.property
    full_dimensional := ?_
    strict_facet_point := strictFacetPoints_transfer f f p.data.2
      (interpolatedSupport p.data.2 k t.val) p.compact ev he' p.strict_facet_point }
  obtain ⟨x, hx⟩ := p.full_dimensional
  obtain ⟨y, hy⟩ := hk
  refine ⟨(1 - t.val) • x + t.val • y, strict_mem_dataRegion_interior _ (fun i => ?_)⟩
  change p.data.1 i ((1 - t.val) • x + t.val • y) <
    (1 - t.val) * p.data.2 i + t.val * k i
  simp only [map_add, map_smul, smul_eq_mul]
  have hpx := regular_interior_strict p hx i
  have hqy := hy i
  have ht0 := t.property.1
  have ht1 := t.property.2
  by_cases ht : t.val = 0
  · simpa only [ht, sub_zero, one_mul, zero_mul, add_zero] using hpx
  · have htp : 0 < t.val := lt_of_le_of_ne ht0 (Ne.symm ht)
    have h₁ := mul_le_mul_of_nonneg_left hpx.le (sub_nonneg.mpr ht1)
    have h₂ := mul_lt_mul_of_pos_left hqy htp
    linarith

theorem normalIntervalRegular_data (p : RegularData d ι) (k : ι → ℝ)
    (hk : ∃ y : Space d, ∀ i, p.data.1 i y < k i)
    (hs : (presentation p).Simple)
    (e : HalfspaceVertices (fun i => (p.data.1 i).toLinearMap) p.data.2 ≃
      HalfspaceVertices (fun i => (p.data.1 i).toLinearMap) k)
    (he : ∀ v i, p.data.1 i v.val = p.data.2 i ↔ p.data.1 i (e v).val = k i)
    (t : I) : (normalIntervalRegular p k hk hs e he t).data =
      (p.data.1, interpolatedSupport p.data.2 k t.val) := rfl

theorem continuous_normalIntervalRegular (p : RegularData d ι) (k : ι → ℝ)
    (hk : ∃ y : Space d, ∀ i, p.data.1 i y < k i)
    (hs : (presentation p).Simple)
    (e : HalfspaceVertices (fun i => (p.data.1 i).toLinearMap) p.data.2 ≃
      HalfspaceVertices (fun i => (p.data.1 i).toLinearMap) k)
    (he : ∀ v i, p.data.1 i v.val = p.data.2 i ↔ p.data.1 i (e v).val = k i) :
    Continuous (normalIntervalRegular p k hk hs e he) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun t : I => (p.data.1, interpolatedSupport p.data.2 k t.val))
  apply continuous_const.prodMk
  apply continuous_pi
  intro i
  exact ((continuous_const.sub continuous_subtype_val).mul continuous_const).add
    (continuous_subtype_val.mul continuous_const)

theorem normalIntervalRegular_type (p : RegularData d ι) (k : ι → ℝ)
    (hk : ∃ y : Space d, ∀ i, p.data.1 i y < k i)
    (hs : (presentation p).Simple)
    (e : HalfspaceVertices (fun i => (p.data.1 i).toLinearMap) p.data.2 ≃
      HalfspaceVertices (fun i => (p.data.1 i).toLinearMap) k)
    (he : ∀ v i, p.data.1 i v.val = p.data.2 i ↔ p.data.1 i (e v).val = k i)
    (t : I) : (presentation p).SameLabelledType
      (presentation (normalIntervalRegular p k hk hs e he t)) := by
  let f := fun i => (p.data.1 i).toLinearMap
  have hn : (dataRegion p.data).Nonempty := p.full_dimensional.mono interior_subset
  have hs' := (simple_iff_raw p).mp hs
  let ev := interpolatedVertexEquiv f p.data.2 k p.compact hn hs' e he t.property
  have he' : ∀ v i, f i v.val = p.data.2 i ↔
      f i (ev v).val = interpolatedSupport p.data.2 k t.val i := by
    intro v i
    exact (interpolatedVertex_incidence f p.data.2 k e he t.property v i).symm
  apply sameLabelledType_of_faceOrderIso p (normalIntervalRegular p k hk hs e he t)
    (halfspaceFaceOrderIso f f p.data.2 (interpolatedSupport p.data.2 k t.val)
      p.compact (normalIntervalRegular p k hk hs e he t).compact ev he')
  exact fun i => halfspaceFaceOrderIso_facet _ _ _ _ _ _ _ _ i

end NormalProjective.UnitNormalization

namespace NormalProjective.CanonicalModel.Realization
open UnitNormalization
variable {d : ℕ} {ι : Type*} [Fintype ι] {R : Presentation d ι}

/-- Straight support interpolation is a path through actual realizations;
its validity was proved by the finite vertex hull and normal-cone argument. -/
theorem NormalStep.joined {P Q : Realization R} (hs : P.val.Simple)
    (h : NormalStep P Q) : Joined P Q := by
  classical
  let p := ofCanonical P.val
  let q := ofCanonical Q.val
  have hn : p.data.1 = q.data.1 := by
    change (fun i => rowForm (P.val.normal i)) = (fun i => rowForm (Q.val.normal i))
    rw [h]
  have htype : (presentation p).SameLabelledType (presentation q) := by
    simpa only [p, q, presentation_ofCanonical] using P.property.symm.trans Q.property
  have hs' : (presentation p).Simple := by
    simpa only [p, presentation_ofCanonical] using hs
  have hraw := sameLabelledType_raw p q htype
  rw [← hn] at hraw
  obtain ⟨ef, hef⟩ := hraw
  let f := fun i => (p.data.1 i).toLinearMap
  have hqcompact : IsCompact (halfspaceRegion f q.data.2) := by
    change IsCompact (halfspaceRegion (fun i => (p.data.1 i).toLinearMap) q.data.2)
    rw [hn]
    exact q.compact
  let e := faceIsoVertexEquiv f f p.data.2 q.data.2 p.compact hqcompact ef
  have he := faceIsoVertexEquiv_incidence f f p.data.2 q.data.2 p.compact hqcompact ef hef
  have hk : ∃ y : CanonicalModel.Space d, ∀ i, p.data.1 i y < q.data.2 i := by
    obtain ⟨y, hy⟩ := q.full_dimensional
    refine ⟨y, fun i => ?_⟩
    rw [hn]
    exact regular_interior_strict q hy i
  let w := normalIntervalRegular p q.data.2 hk hs' e he
  have hRw (t : I) : R.SameLabelledType (presentation (w t)) := by
    apply P.property.trans
    simpa only [p, presentation_ofCanonical] using
      normalIntervalRegular_type p q.data.2 hk hs' e he t
  let γ : I → Realization R := fun t => ⟨presentation (w t), hRw t⟩
  have hc : Continuous γ :=
    (continuous_presentation.comp (continuous_normalIntervalRegular p q.data.2 hk hs' e he)).subtype_mk _
  have h0 : γ 0 = P := by
    apply Subtype.ext
    have hp : w 0 = p := by
      apply MatrixRealization.regularData_ext
      rw [normalIntervalRegular_data]
      apply Prod.ext
      · rfl
      · funext i
        simp [interpolatedSupport]
    change presentation (w 0) = P.val
    rw [hp]
    exact presentation_ofCanonical P.val
  have h1 : γ 1 = Q := by
    apply Subtype.ext
    have hq : w 1 = q := by
      apply MatrixRealization.regularData_ext
      rw [normalIntervalRegular_data]
      apply Prod.ext
      · exact hn
      · funext i
        simp [interpolatedSupport]
    change presentation (w 1) = Q.val
    rw [hq]
    exact presentation_ofCanonical Q.val
  exact ⟨{ toFun := γ, continuous_toFun := hc, source' := h0, target' := h1 }⟩

end NormalProjective.CanonicalModel.Realization
end

/- Source: NormalProjective/ProjectiveFactor.lean -/
section
/-! # An admissible projectivity factors into an elementary map and an affine map -/
open Set Matrix
open scoped BigOperators
namespace NormalProjective.CanonicalModel.Realization
open UnitNormalization
variable {d : ℕ}

def projectiveForm (M : HomogeneousMatrix d) : Space d →L[ℝ] ℝ :=
  (M none none)⁻¹ • rowForm (fun j => M none (some j))

def projectiveBase (M : HomogeneousMatrix d) : Space d :=
  fun j => (M none none)⁻¹ * M (some j) none

def projectiveLinearPart (M : HomogeneousMatrix d) : Space d →ₗ[ℝ] Space d :=
  LinearMap.pi (fun j =>
    (M none none)⁻¹ • (rowForm (fun k => M (some j) (some k))).toLinearMap -
      projectiveBase M j • (projectiveForm M).toLinearMap)

theorem alpha_projectiveForm (M : HomogeneousMatrix d) (hα : M none none ≠ 0)
    (x : Space d) :
    M none none * projectiveForm M x = ∑ j, M none (some j) * x j := by
  change M none none * ((M none none)⁻¹ * rowForm (fun j => M none (some j)) x) = _
  rw [← mul_assoc, mul_inv_cancel₀ hα, one_mul, rowForm_apply]
  rfl

theorem alpha_projectiveBase (M : HomogeneousMatrix d) (hα : M none none ≠ 0)
    (j : Fin d) : M none none * projectiveBase M j = M (some j) none := by
  simp [projectiveBase, ← mul_assoc, hα]

theorem alpha_projectiveLinearPart (M : HomogeneousMatrix d) (hα : M none none ≠ 0)
    (x : Space d) (j : Fin d) :
    M none none * projectiveLinearPart M x j =
      (∑ k, M (some j) (some k) * x k) - M (some j) none * projectiveForm M x := by
  change M none none * ((M none none)⁻¹ * rowForm (fun k => M (some j) (some k)) x -
    projectiveBase M j * projectiveForm M x) = _
  rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hα, one_mul, ← mul_assoc,
    alpha_projectiveBase M hα j, rowForm_apply]
  rfl

theorem denominator_factor (M : HomogeneousMatrix d) (hα : M none none ≠ 0)
    (x : Space d) : denominator M x = M none none * (1 + projectiveForm M x) := by
  rw [mul_add, mul_one, alpha_projectiveForm M hα x]
  rfl

theorem numerator_factor (M : HomogeneousMatrix d) (hα : M none none ≠ 0)
    (x : Space d) (j : Fin d) : numerator M x j =
      M none none * ((1 + projectiveForm M x) * projectiveBase M j +
        projectiveLinearPart M x j) := by
  rw [mul_add, alpha_projectiveLinearPart M hα x j]
  have hb := alpha_projectiveBase M hα j
  unfold numerator
  rw [show M none none * ((1 + projectiveForm M x) * projectiveBase M j) =
    (1 + projectiveForm M x) * (M none none * projectiveBase M j) by ring, hb]
  ring

theorem projectiveLinearPart_injective (M : HomogeneousMatrix d)
    (hM : M.det ≠ 0) (hα : M none none ≠ 0) :
    Function.Injective (projectiveLinearPart M) := by
  have hker (v : Space d) (hv : projectiveLinearPart M v = 0) : v = 0 := by
    let w : Option (Fin d) → ℝ := fun i => match i with
      | none => -projectiveForm M v
      | some j => v j
    have hw : M *ᵥ w = 0 := by
      funext i
      cases i with
      | none =>
          change (∑ j, M none j * w j) = 0
          rw [Fintype.sum_option]
          change M none none * (-projectiveForm M v) +
            (∑ j, M none (some j) * v j) = 0
          rw [← alpha_projectiveForm M hα v]
          ring
      | some j =>
          change (∑ k, M (some j) k * w k) = 0
          rw [Fintype.sum_option]
          change M (some j) none * (-projectiveForm M v) +
            (∑ k, M (some j) (some k) * v k) = 0
          have hL := alpha_projectiveLinearPart M hα v j
          rw [hv] at hL
          simp only [Pi.zero_apply, mul_zero] at hL
          linarith
    have hw0 : w = 0 := Matrix.mulVec_injective_of_det_ne_zero hM
      (hw.trans (Matrix.mulVec_zero M).symm)
    funext j
    exact congrFun hw0 (some j)
  intro x y hxy
  apply sub_eq_zero.mp
  apply hker
  rw [map_sub, hxy, sub_self]

def projectiveAffineFactor (M : HomogeneousMatrix d)
    (hM : M.det ≠ 0) (hα : M none none ≠ 0) : Space d ≃ᵃ[ℝ] Space d :=
  (LinearEquiv.ofInjectiveEndo (projectiveLinearPart M)
    (projectiveLinearPart_injective M hM hα)).toAffineEquiv.trans
    (AffineEquiv.constVAdd ℝ (Space d) (projectiveBase M))

theorem projectiveMap_factor (M : HomogeneousMatrix d)
    (hM : M.det ≠ 0) (hα : M none none ≠ 0) (x : Space d)
    (hx : denominator M x ≠ 0) : projectiveMap M x =
      projectiveAffineFactor M hM hα
        (ProjectiveBridge.elementary (projectiveForm M).toLinearMap x) := by
  have hu : 1 + projectiveForm M x ≠ 0 := by
    rw [denominator_factor M hα] at hx
    exact (mul_ne_zero_iff.mp hx).2
  ext j
  change numerator M x j / denominator M x =
    projectiveBase M j + projectiveLinearPart M
      ((1 + projectiveForm M x)⁻¹ • x) j
  rw [map_smul]
  change numerator M x j / denominator M x =
    projectiveBase M j + (1 + projectiveForm M x)⁻¹ * projectiveLinearPart M x j
  rw [numerator_factor M hα x j, denominator_factor M hα x]
  field_simp [hα, hu]
  <;> ring

/-- On a convex set containing zero, an affine denominator normalized to one
at zero and never vanishing is positive everywhere. -/
theorem normalized_denominator_positive (K : Set (Space d)) (hK : Convex ℝ K)
    (h0 : (0 : Space d) ∈ K) (u : Space d →L[ℝ] ℝ)
    (hu : ∀ x ∈ K, 1 + u x ≠ 0) : ∀ x ∈ K, 0 < 1 + u x := by
  intro x hx
  by_contra hn
  have hux : 1 ≤ -u x := by linarith [le_of_not_gt hn]
  have hu0 : 0 < -u x := lt_of_lt_of_le zero_lt_one hux
  let t : ℝ := 1 / (-u x)
  have ht0 : 0 ≤ t := le_of_lt (one_div_pos.mpr hu0)
  have ht1 : t ≤ 1 := (div_le_one hu0).mpr hux
  have htx : t • x ∈ K := by
    have hm := hK h0 hx (sub_nonneg.mpr ht1) ht0 (by ring : (1 - t) + t = 1)
    simpa only [smul_zero, zero_add] using hm
  apply hu (t • x) htx
  rw [map_smul, smul_eq_mul]
  dsimp only [t]
  have huv : u x ≠ 0 := neg_ne_zero.mp (ne_of_gt hu0)
  field_simp [huv]
  <;> ring

end NormalProjective.CanonicalModel.Realization
end

/- Source: NormalProjective/ProjectivePath.lean -/
section
/-! # Genuine elementary projectivities preserve the full labelled face lattice -/
open Set Filter unitInterval
open scoped Topology BigOperators
namespace NormalProjective
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]

theorem image_tightFace_of_incidence
    (f g : ι → E →ₗ[ℝ] ℝ) (h k : ι → ℝ) (T : E → E)
    (hTK : T '' halfspaceRegion f h = halfspaceRegion g k)
    (hinc : ∀ x ∈ halfspaceRegion f h, ∀ i, f i x = h i ↔ g i (T x) = k i)
    (J : Set ι) : T '' tightFace f h J = tightFace g k J := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hxi⟩, rfl⟩
    refine ⟨hTK ▸ ⟨x, hx, rfl⟩, fun i hi => (hinc x hx i).mp (hxi i hi)⟩
  · intro hy
    have hyK : y ∈ T '' halfspaceRegion f h := hTK.symm ▸ hy.1
    obtain ⟨x, hx, rfl⟩ := hyK
    exact ⟨x, ⟨hx, fun i hi => (hinc x hx i).mpr (hy.2 i hi)⟩, rfl⟩

theorem image_face_of_incidence
    (f g : ι → E →ₗ[ℝ] ℝ) (h k : ι → ℝ) (T : E → E)
    (hTK : T '' halfspaceRegion f h = halfspaceRegion g k)
    (hinc : ∀ x ∈ halfspaceRegion f h, ∀ i, f i x = h i ↔ g i (T x) = k i)
    (F : HalfspaceFaces f h) : IsExposed ℝ (halfspaceRegion g k) (T '' F.val) := by
  by_cases hn : F.val.Nonempty
  · rw [exposedFace_eq_tightFace f h F.property hn,
      image_tightFace_of_incidence f g h k T hTK hinc]
    exact tightFace_isExposed g k _
  · rw [Set.not_nonempty_iff_eq_empty.mp hn, Set.image_empty]
    exact isExposed_empty

def halfspaceFaceOrderIsoOfBijection
    (f g : ι → E →ₗ[ℝ] ℝ) (h k : ι → ℝ) (T S : E → E)
    (hTK : T '' halfspaceRegion f h = halfspaceRegion g k)
    (hSK : S '' halfspaceRegion g k = halfspaceRegion f h)
    (hleft : ∀ x ∈ halfspaceRegion f h, S (T x) = x)
    (hright : ∀ y ∈ halfspaceRegion g k, T (S y) = y)
    (hinc : ∀ x ∈ halfspaceRegion f h, ∀ i, f i x = h i ↔ g i (T x) = k i) :
    HalfspaceFaces f h ≃o HalfspaceFaces g k := by
  have hSinc : ∀ y ∈ halfspaceRegion g k, ∀ i, g i y = k i ↔ f i (S y) = h i := by
    intro y hy i
    have hSy : S y ∈ halfspaceRegion f h := hSK ▸ ⟨y, hy, rfl⟩
    simpa only [hright y hy] using (hinc (S y) hSy i).symm
  refine {
    toFun := fun F => ⟨T '' F.val, image_face_of_incidence f g h k T hTK hinc F⟩
    invFun := fun G => ⟨S '' G.val, image_face_of_incidence g f k h S hSK hSinc G⟩
    left_inv := ?_
    right_inv := ?_
    map_rel_iff' := ?_ }
  · intro F
    apply Subtype.ext
    change S '' (T '' F.val) = F.val
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa only [hleft z (F.property.subset hz)] using hz
    · intro hx
      exact ⟨T x, ⟨x, hx, rfl⟩, hleft x (F.property.subset hx)⟩
  · intro G
    apply Subtype.ext
    change T '' (S '' G.val) = G.val
    ext y
    constructor
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      simpa only [hright z (G.property.subset hz)] using hz
    · intro hy
      exact ⟨S y, ⟨y, hy, rfl⟩, hright y (G.property.subset hy)⟩
  · intro F G
    constructor
    · intro hh x hx
      obtain ⟨y, hy, heq⟩ := hh ⟨x, hx, rfl⟩
      have hxy : y = x := by
        have hs := congrArg S heq
        rwa [hleft y (G.property.subset hy), hleft x (F.property.subset hx)] at hs
      simpa only [hxy] using hy
    · exact fun hh => Set.image_mono hh

namespace UnitNormalization
variable {d : ℕ}

def elementaryData (p : RegularData d ι) (u : Space d →L[ℝ] ℝ) :
    HalfspaceData ι (Space d) := (fun i => p.data.1 i + p.data.2 i • u, p.data.2)

theorem elementaryData_image (p : RegularData d ι) (u : Space d →L[ℝ] ℝ)
    (hp : ∀ i, 0 < p.data.2 i)
    (hu : ∀ x ∈ dataRegion p.data, 0 < 1 + u x) :
    ProjectiveBridge.elementary u.toLinearMap '' dataRegion p.data =
      dataRegion (elementaryData p u) :=
  ProjectiveBridge.elementary_image_HRegion (fun i => (p.data.1 i).toLinearMap)
    p.data.2 (fun i => (hp i).le) p.compact.isBounded u.toLinearMap hu

def elementaryRegular (p : RegularData d ι) (u : Space d →L[ℝ] ℝ)
    (hp : ∀ i, 0 < p.data.2 i)
    (hu : ∀ x ∈ dataRegion p.data, 0 < 1 + u x) : RegularData d ι := by
  let f := fun i => (p.data.1 i).toLinearMap
  let T := ProjectiveBridge.elementary u.toLinearMap
  have hT : T '' dataRegion p.data = dataRegion (elementaryData p u) :=
    elementaryData_image p u hp hu
  have hinc (x : Space d) (hx : x ∈ dataRegion p.data) (i : ι) :
      (elementaryData p u).1 i (T x) = p.data.2 i ↔ p.data.1 i x = p.data.2 i :=
    ElementaryProjectivity.tight_iff f p.data.2 u.toLinearMap x (hu x hx) i
  have hct : ContinuousOn T (dataRegion p.data) := by
    exact (((continuousOn_const.add u.continuous.continuousOn).inv₀
      (fun x hx => ne_of_gt (hu x hx))).smul continuousOn_id)
  refine {
    data := elementaryData p u
    normal_ne_zero := ?_
    compact := hT ▸ p.compact.image_of_continuousOn hct
    full_dimensional := ⟨0, strict_mem_dataRegion_interior _ (by
      intro i
      change (p.data.1 i + p.data.2 i • u) 0 < p.data.2 i
      simpa only [map_zero] using hp i)⟩
    strict_facet_point := ?_ }
  · intro i hi
    obtain ⟨x, hx, hxi, _⟩ := p.strict_facet_point i
    have hh := (hinc x hx i).mpr hxi
    rw [hi] at hh
    exact (ne_of_gt (hp i)) (by simpa using hh.symm)
  · intro i
    obtain ⟨x, hx, hxi, hxs⟩ := p.strict_facet_point i
    have hTx : T x ∈ dataRegion (elementaryData p u) := hT ▸ ⟨x, hx, rfl⟩
    refine ⟨T x, hTx, (hinc x hx i).mpr hxi, fun j hji => ?_⟩
    apply lt_of_le_of_ne (hTx j)
    intro heq
    exact (ne_of_lt (hxs j hji)) ((hinc x hx j).mp heq)

theorem elementaryRegular_type (p : RegularData d ι) (u : Space d →L[ℝ] ℝ)
    (hp : ∀ i, 0 < p.data.2 i)
    (hu : ∀ x ∈ dataRegion p.data, 0 < 1 + u x) :
    (presentation p).SameLabelledType (presentation (elementaryRegular p u hp hu)) := by
  let f := fun i => (p.data.1 i).toLinearMap
  let g := ProjectiveBridge.changedNormals f p.data.2 u.toLinearMap
  let T := ProjectiveBridge.elementary u.toLinearMap
  let S := ProjectiveBridge.elementary (-u.toLinearMap)
  have hT : T '' halfspaceRegion f p.data.2 = halfspaceRegion g p.data.2 :=
    elementaryData_image p u hp hu
  have hback : ∀ y ∈ halfspaceRegion g p.data.2, 0 < 1 + (-u.toLinearMap) y := by
    intro y hy
    exact ProjectiveBridge.inverse_denominator_pos f p.data.2
      (fun i => (hp i).le) p.compact.isBounded u.toLinearMap hy
  have hS : S '' halfspaceRegion g p.data.2 = halfspaceRegion f p.data.2 := by
    have hh := ProjectiveBridge.elementary_image_HRegion g p.data.2
      (fun i => (hp i).le) (elementaryRegular p u hp hu).compact.isBounded
      (-u.toLinearMap) hback
    simpa only [g, S, ProjectiveBridge.changedNormals_neg, ProjectiveBridge.HRegion, halfspaceRegion] using hh
  have hleft : ∀ x ∈ halfspaceRegion f p.data.2, S (T x) = x :=
    fun x hx => ProjectiveBridge.elementary_inverse _ _ (ne_of_gt (hu x hx))
  have hright : ∀ y ∈ halfspaceRegion g p.data.2, T (S y) = y := by
    intro y hy
    simpa only [neg_neg] using ProjectiveBridge.elementary_inverse
      (-u.toLinearMap) y (ne_of_gt (hback y hy))
  have hinc : ∀ x ∈ halfspaceRegion f p.data.2, ∀ i,
      f i x = p.data.2 i ↔ g i (T x) = p.data.2 i := by
    intro x hx i
    exact (ElementaryProjectivity.tight_iff f p.data.2 u.toLinearMap x (hu x hx) i).symm
  apply sameLabelledType_of_faceOrderIso p (elementaryRegular p u hp hu)
    (halfspaceFaceOrderIsoOfBijection f g p.data.2 p.data.2 T S hT hS hleft hright hinc)
  intro i
  apply Subtype.ext
  exact image_tightFace_of_incidence f g p.data.2 p.data.2 T hT hinc {i}

theorem elementary_segment_positive (p : RegularData d ι) (u : Space d →L[ℝ] ℝ)
    (hu : ∀ x ∈ dataRegion p.data, 0 < 1 + u x) (t : I) :
    ∀ x ∈ dataRegion p.data, 0 < 1 + (t.val • u) x := by
  intro x hx
  have hh := hu x hx
  have ht0 := t.property.1
  have ht1 := t.property.2
  change 0 < 1 + t.val * u x
  by_cases ht : t.val = 0
  · simp [ht]
  · have htpos : 0 < t.val := lt_of_le_of_ne ht0 (Ne.symm ht)
    have hm := mul_pos htpos hh
    nlinarith

theorem continuous_elementaryRegular (p : RegularData d ι) (u : Space d →L[ℝ] ℝ)
    (hp : ∀ i, 0 < p.data.2 i)
    (hu : ∀ x ∈ dataRegion p.data, 0 < 1 + u x) :
    Continuous (fun t : I => elementaryRegular p (t.val • u) hp
      (elementary_segment_positive p u hu t)) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun t : I =>
    (fun i => p.data.1 i + p.data.2 i • (t.val • u), p.data.2))
  apply Continuous.prodMk _ continuous_const
  apply continuous_pi
  intro i
  have hc : Continuous ((fun _ : I => p.data.1 i) +
      (fun t : I => (p.data.2 i * t.val) • u)) :=
    continuous_const.add ((continuous_const.mul continuous_subtype_val).smul continuous_const)
  apply hc.congr
  intro t
  simp only [Pi.add_apply, smul_smul]

end UnitNormalization
end NormalProjective

namespace NormalProjective.UnitNormalization
open CanonicalModel.Realization
variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem elementaryRegular_carrier (p : RegularData d ι) (u : Space d →L[ℝ] ℝ)
    (hp : ∀ i, 0 < p.data.2 i)
    (hu : ∀ x ∈ dataRegion p.data, 0 < 1 + u x) :
    (presentation (elementaryRegular p u hp hu)).carrier =
      ProjectiveBridge.elementary u.toLinearMap '' (presentation p).carrier := by
  rw [presentation_carrier, presentation_carrier]
  exact (elementaryData_image p u hp hu).symm

theorem elementaryRegular_facet (p : RegularData d ι) (u : Space d →L[ℝ] ℝ)
    (hp : ∀ i, 0 < p.data.2 i)
    (hu : ∀ x ∈ dataRegion p.data, 0 < 1 + u x) (i : ι) :
    (presentation (elementaryRegular p u hp hu)).facet i =
      ProjectiveBridge.elementary u.toLinearMap '' (presentation p).facet i := by
  rw [presentation_facet, presentation_facet]
  exact (ElementaryProjectivity.elementary_image_facet
    (fun i => (p.data.1 i).toLinearMap) p.data.2 (fun i => (hp i).le)
    p.compact.isBounded u.toLinearMap hu i).symm

end NormalProjective.UnitNormalization

namespace NormalProjective.CanonicalModel.Realization
open UnitNormalization
variable {d : ℕ} {ι : Type*} [Fintype ι] {R : Presentation d ι}

theorem continuous_affineClass : Continuous (affineClass (R := R)) :=
  continuous_coinduced_rng

theorem affineClass_eq_of_affineRelated {P Q : Realization R}
    (h : AffineRelated P Q) : affineClass P = affineClass Q := Quotient.sound h

theorem affineRelated_of_affineClass_eq {P Q : Realization R}
    (h : affineClass P = affineClass Q) : AffineRelated P Q := Quotient.exact h

theorem elementary_joined (p : RegularData d ι) (hRp : R.SameLabelledType (presentation p))
    (u : CanonicalModel.Space d →L[ℝ] ℝ) (hp : ∀ i, 0 < p.data.2 i)
    (hu : ∀ x ∈ dataRegion p.data, 0 < 1 + u x) :
    Joined (⟨presentation p, hRp⟩ : Realization R)
      ⟨presentation (elementaryRegular p u hp hu),
        hRp.trans (elementaryRegular_type p u hp hu)⟩ := by
  let w (t : I) := elementaryRegular p (t.val • u) hp
    (elementary_segment_positive p u hu t)
  let γ : I → Realization R := fun t => ⟨presentation (w t),
    hRp.trans (elementaryRegular_type p (t.val • u) hp
      (elementary_segment_positive p u hu t))⟩
  have hc : Continuous γ :=
    (continuous_presentation.comp (continuous_elementaryRegular p u hp hu)).subtype_mk _
  have h0 : γ 0 = ⟨presentation p, hRp⟩ := by
    apply Subtype.ext
    have hw : w 0 = p := by
      apply MatrixRealization.regularData_ext
      change (fun i => p.data.1 i + p.data.2 i • ((0 : I).val • u), p.data.2) = p.data
      simp
    change presentation (w 0) = presentation p
    rw [hw]
  have h1 : γ 1 = ⟨presentation (elementaryRegular p u hp hu),
      hRp.trans (elementaryRegular_type p u hp hu)⟩ := by
    apply Subtype.ext
    have hw : w 1 = elementaryRegular p u hp hu := by
      apply MatrixRealization.regularData_ext
      change (fun i => p.data.1 i + p.data.2 i • ((1 : I).val • u), p.data.2) =
        (fun i => p.data.1 i + p.data.2 i • u, p.data.2)
      simp
    change presentation (w 1) = presentation (elementaryRegular p u hp hu)
    rw [hw]
  exact ⟨{ toFun := γ, continuous_toFun := hc, source' := h0, target' := h1 }⟩

/-- An arbitrary admissible projectivity gives a path after quotienting by
actual affine equivalence. The elementary factor remains admissible throughout. -/
theorem ProjectiveStep.affineJoined {P Q : Realization R} (h : ProjectiveStep P Q) :
    Joined (affineClass P) (affineClass Q) := by
  classical
  let p₀ := ofCanonical P.val
  obtain ⟨x₀, hx₀⟩ := p₀.full_dimensional
  let a := AffineEquiv.constVAdd ℝ (CanonicalModel.Space d) (-x₀)
  let p := affineRegular a p₀
  let P' := affineAction a P
  have hpPres : presentation p = P'.val := rfl
  have hPcarrier : P'.carrier = dataRegion p.data := by
    change P'.val.carrier = dataRegion p.data
    rw [← hpPres, presentation_carrier]
  have hpos : ∀ i, 0 < p.data.2 i := by
    intro i
    change 0 < p₀.data.2 i - p₀.data.1 i (a.symm 0)
    have ha : a.symm 0 = x₀ := by simp [a]
    rw [ha]
    exact sub_pos.mpr (regular_interior_strict p₀ hx₀ i)
  have h0 : (0 : CanonicalModel.Space d) ∈ dataRegion p.data := by
    intro i
    simpa using (hpos i).le
  have hstep : ProjectiveStep P' Q :=
    (affineRelated_symm (affineAction_related a P)).projectiveStep.trans h
  obtain ⟨M, hM, hden, hMK, hMF⟩ := hstep
  have hα : M none none ≠ 0 := by
    have hh := hden 0 (hPcarrier.symm ▸ h0)
    simpa [denominator] using hh
  let u := projectiveForm M
  have hu : ∀ x ∈ dataRegion p.data, 0 < 1 + u x := by
    apply normalized_denominator_positive (dataRegion p.data)
      (convex_halfspaceRegion (fun i => (p.data.1 i).toLinearMap) p.data.2) h0 u
    intro x hx
    have hx' : x ∈ P'.carrier := by
      exact hPcarrier.symm ▸ hx
    have hh := hden x hx'
    rw [denominator_factor M hα x] at hh
    exact (mul_ne_zero_iff.mp hh).2
  let E : Realization R := ⟨presentation (elementaryRegular p u hpos hu),
    P'.property.trans (by simpa only [← hpPres] using elementaryRegular_type p u hpos hu)⟩
  have hPE : Joined P' E := by
    have hj := elementary_joined p (by simpa only [hpPres] using P'.property) u hpos hu
    exact hj
  let b := projectiveAffineFactor M hM hα
  have hEQ : AffineRelated E Q := by
    refine ⟨b, ?_, fun i => ?_⟩
    · change b '' (presentation (elementaryRegular p u hpos hu)).carrier = Q.carrier
      rw [elementaryRegular_carrier, Set.image_image]
      calc
        (fun x => b (ProjectiveBridge.elementary u.toLinearMap x)) '' (presentation p).carrier =
            projectiveMap M '' P'.carrier := by
          rw [hpPres]
          apply Set.image_congr
          intro x hx
          exact (projectiveMap_factor M hM hα x (hden x hx)).symm
        _ = Q.carrier := hMK
    · change b '' (presentation (elementaryRegular p u hpos hu)).facet i = Q.facet i
      rw [elementaryRegular_facet, Set.image_image]
      calc
        (fun x => b (ProjectiveBridge.elementary u.toLinearMap x)) '' (presentation p).facet i =
            projectiveMap M '' P'.facet i := by
          rw [hpPres]
          apply Set.image_congr
          intro x hx
          exact (projectiveMap_factor M hM hα x (hden x hx.1)).symm
        _ = Q.facet i := hMF i
  have hj := hPE.map continuous_affineClass
  have hPclass := affineClass_eq_of_affineRelated (affineAction_related a P)
  have hQclass := affineClass_eq_of_affineRelated hEQ
  rwa [← hPclass, hQclass] at hj

theorem PNWord.affineJoined (hs : R.Simple) {P Q : Realization R} {p n : ℕ}
    (h : PNWord P Q p n) : Joined (affineClass P) (affineClass Q) := by
  induction h with
  | nil P => exact Joined.refl _
  | projective hstep htail ih => exact hstep.affineJoined.trans ih
  | @normal P Q U p n hstep htail ih =>
      exact ((hstep.joined (hs.of_sameLabelledType P.property)).map continuous_affineClass).trans ih

theorem PNRelated.affineJoined (hs : R.Simple) {P Q : Realization R}
    (h : PNRelated P Q) : Joined (affineClass P) (affineClass Q) := by
  obtain ⟨p, n, hw⟩ := h
  exact hw.affineJoined hs

end NormalProjective.CanonicalModel.Realization
end

/- Source: NormalProjective/Components.lean -/
section
/-! # PN classes are precisely components of the actual affine quotient -/
open Set Filter
open scoped Topology
namespace NormalProjective.CanonicalModel.Realization
variable {d : ℕ} {ι : Type*} [Fintype ι] {R : Presentation d ι}

def quotientPNClass (P : Realization R) : Set (AffineQuotient R) :=
  affineClass '' {Q : Realization R | PNRelated P Q}

theorem quotientPNClass_preimage (P : Realization R) :
    affineClass ⁻¹' quotientPNClass P = {Q : Realization R | PNRelated P Q} := by
  ext Q
  constructor
  · rintro ⟨U, hPU, hUQ⟩
    exact hPU.trans (affineRelated_of_affineClass_eq hUQ).pnRelated
  · intro hPQ
    exact ⟨Q, hPQ, rfl⟩

theorem quotientPNClass_isClopen (hs : R.Simple) (P : Realization R) :
    IsClopen (quotientPNClass P) := by
  have hlocal (Q : Realization R) : {U : Realization R | PNRelated Q U} ∈ 𝓝 Q := by
    filter_upwards [local_word_neighbourhood Q (hs.of_sameLabelledType Q.property)] with U hU
    exact ⟨d, d, hU⟩
  have hcl := ConnectedClasses.isClopen_class (PNRelated (R := R)) pn_equivalence hlocal P
  constructor
  · apply isClosed_coinduced.mpr
    change IsClosed (affineClass ⁻¹' quotientPNClass P)
    rw [quotientPNClass_preimage]
    exact hcl.1
  · apply isOpen_coinduced.mpr
    change IsOpen (affineClass ⁻¹' quotientPNClass P)
    rw [quotientPNClass_preimage]
    exact hcl.2

/-- The central equivalence, with genuine labelled facet realizations, true
admissible projectivities, equality of outward unit normals, and the full affine
quotient. There is no local-path-connectedness or connectivity hypothesis. -/
theorem pnRelated_iff_same_component (hs : R.Simple) (P Q : Realization R) :
    PNRelated P Q ↔ affineClass Q ∈ connectedComponent (affineClass P) := by
  constructor
  · intro h
    exact pathComponent_subset_component _ (h.affineJoined hs)
  · intro h
    have hP : affineClass P ∈ quotientPNClass P := ⟨P, PNRelated.refl P, rfl⟩
    have hQ := (quotientPNClass_isClopen hs P).connectedComponent_subset hP h
    have hm : Q ∈ affineClass ⁻¹' quotientPNClass P := hQ
    rwa [quotientPNClass_preimage] at hm

end NormalProjective.CanonicalModel.Realization
end

/- Source: NormalProjective/RawLocal.lean -/
section
/-! # The paper's raw normalized matrix formulation, with no genericity restriction -/
open Set Filter
open scoped Topology
namespace NormalProjective
open UnitNormalization CanonicalModel CanonicalModel.Realization
variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- Lemma 4 in the paper's literal coordinates: every sufficiently small change
of the normalized facet matrix is realized by d projective and d normal steps.
All intermediate carriers are actual bounded full-dimensional polytopes of the
same labelled face lattice. -/
theorem normalized_matrix_local_word
    (p₀ : RegularData d ι) (A : Matrix ι (Fin d) ℝ)
    (hp₀ : p₀.data = MatrixRealization.asData (A, fun _ => 1))
    (hs : IsSimpleHalfspace (fun i => (rowForm (A i)).toLinearMap) (fun _ => 1)) :
    ∀ᶠ B : Matrix ι (Fin d) ℝ in 𝓝 A,
      ∃ hB : MatrixRealization.Realizes (presentation p₀) (B, fun _ => 1),
        PNWord
          (⟨presentation p₀, Presentation.sameLabelledType_refl (presentation p₀)⟩ :
            Realization (presentation p₀))
          (MatrixRealization.realization (presentation p₀) (B, fun _ => 1) hB) d d := by
  classical
  let R := presentation p₀
  let P : Realization R := ⟨R, Presentation.sameLabelledType_refl R⟩
  let D (B : Matrix ι (Fin d) ℝ) := (B, fun _ : ι => (1 : ℝ))
  have hA : MatrixRealization.Realizes R (D A) :=
    ⟨p₀, hp₀, Presentation.sameLabelledType_refl R⟩
  obtain ⟨C, hC, hstable⟩ := normalized_regular_eventually_stable p₀
    (fun i => rowForm (A i)) hp₀ hs
  have hnear : ∀ᶠ B : Matrix ι (Fin d) ℝ in 𝓝 A,
      MatrixRealization.Realizes R (D B) := by
    have hc : Continuous (fun B : Matrix ι (Fin d) ℝ => MatrixRealization.asData (D B)) :=
      MatrixRealization.continuous_asData.comp (continuous_id.prodMk continuous_const)
    have hh := hc.continuousAt.eventually hstable
    filter_upwards [hh] with B hB
    obtain ⟨_, _, p, hp, hRp⟩ := hB
    exact ⟨p, hp, hRp⟩
  let r : Matrix ι (Fin d) ℝ → RegularData d ι := fun B =>
    if hB : MatrixRealization.Realizes R (D B) then MatrixRealization.regular R (D B) hB else p₀
  have hrdata : ∀ᶠ B : Matrix ι (Fin d) ℝ in 𝓝 A,
      (r B).data = MatrixRealization.asData (D B) := by
    filter_upwards [hnear] with B hB
    dsimp only [r]
    rw [dif_pos hB]
    exact MatrixRealization.regular_data R (D B) hB
  have hr : Tendsto r (𝓝 A) (𝓝 p₀) := by
    have hind : Topology.IsInducing (RegularData.data : RegularData d ι →
        HalfspaceData ι (CanonicalModel.Space d)) := ⟨rfl⟩
    apply hind.tendsto_nhds_iff.mpr
    have hc : Tendsto (fun B : Matrix ι (Fin d) ℝ => MatrixRealization.asData (D B))
        (𝓝 A) (𝓝 p₀.data) := by
      rw [hp₀]
      exact (MatrixRealization.continuous_asData.comp
        (continuous_id.prodMk continuous_const)).continuousAt
    exact hc.congr' (Filter.EventuallyEq.symm hrdata)
  have hrType (B : Matrix ι (Fin d) ℝ) : R.SameLabelledType (presentation (r B)) := by
    dsimp only [r]
    split_ifs with hB
    · exact hB.choose_spec.2
    · exact Presentation.sameLabelledType_refl R
  let Q (B : Matrix ι (Fin d) ℝ) : Realization R := ⟨presentation (r B), hrType B⟩
  have hQ : Tendsto Q (𝓝 A) (𝓝 P) := by
    apply tendsto_subtype_rng.mpr
    exact continuous_presentation.continuousAt.tendsto.comp hr
  have hsP : P.val.Simple := by
    apply (simple_iff_raw p₀).mpr
    rw [hp₀]
    exact hs
  have hword := hQ.eventually (local_word_neighbourhood P hsP)
  filter_upwards [hword, hnear] with B hw hB
  refine ⟨hB, ?_⟩
  have heq : Q B = MatrixRealization.realization R (D B) hB := by
    apply Subtype.ext
    change presentation (r B) = _
    dsimp only [r]
    rw [dif_pos hB]
    rfl
  rwa [heq] at hw

end NormalProjective
end

/- Source: NormalProjective/FacetFaithfulness.lean -/
section
/-! # The displayed labels are precisely the actual nonempty facets -/
open Set
namespace NormalProjective.UnitNormalization
variable {d : ℕ} {ι : Type*} [Fintype ι]

def IsActualFacet (p : RegularData d ι)
    (F : HalfspaceFaces (fun i => (p.data.1 i).toLinearMap) p.data.2) : Prop :=
  F.val.Nonempty ∧ F.val ≠ dataRegion p.data ∧
    ∀ G : HalfspaceFaces (fun i => (p.data.1 i).toLinearMap) p.data.2,
      F ≤ G → G.val ≠ dataRegion p.data → G = F

def displayedFacet (p : RegularData d ι) (i : ι) :
    HalfspaceFaces (fun j => (p.data.1 j).toLinearMap) p.data.2 :=
  ⟨tightFace (fun j => (p.data.1 j).toLinearMap) p.data.2 {i},
    tightFace_isExposed _ _ _⟩

theorem displayedFacet_ne_carrier (p : RegularData d ι) (i : ι) :
    (displayedFacet p i).val ≠ dataRegion p.data := by
  obtain ⟨x, hx⟩ := p.full_dimensional
  intro heq
  have hxF : x ∈ (displayedFacet p i).val := heq.symm ▸ interior_subset hx
  have hxi : p.data.1 i x = p.data.2 i := hxF.2 i (Set.mem_singleton i)
  exact (ne_of_lt (regular_interior_strict p hx i)) hxi

theorem displayedFacet_isActualFacet (p : RegularData d ι) (i : ι) :
    IsActualFacet p (displayedFacet p i) := by
  obtain ⟨w, hw, hwi, hws⟩ := p.strict_facet_point i
  have hwF : w ∈ (displayedFacet p i).val := ⟨hw, by simpa using hwi⟩
  refine ⟨⟨w, hwF⟩, displayedFacet_ne_carrier p i, ?_⟩
  intro G hFG hGK
  have hwG := hFG hwF
  let I : Set ι := {j | ∀ x ∈ G.val, p.data.1 j x = p.data.2 j}
  have heq : G.val = tightFace (fun j => (p.data.1 j).toLinearMap) p.data.2 I :=
    exposedFace_eq_tightFace _ _ G.property ⟨w, hwG⟩
  have hsub : I ⊆ {i} := by
    intro j hj
    by_contra hji
    have hh := hj w hwG
    exact (ne_of_lt (hws j hji)) hh
  have hi : i ∈ I := by
    by_contra hni
    have hI : I = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro j hj
      exact hni ((Set.mem_singleton_iff.mp (hsub hj)) ▸ hj)
    apply hGK
    rw [heq, hI]
    ext x
    simp [tightFace, dataRegion]
  apply Subtype.ext
  rw [heq]
  ext x
  constructor
  · intro hx
    exact ⟨hx.1, by simpa using hx.2 i hi⟩
  · intro hx
    refine ⟨hx.1, fun j hj => ?_⟩
    have hji : j = i := Set.mem_singleton_iff.mp (hsub hj)
    simpa only [hji] using hx.2 i (Set.mem_singleton i)

theorem actualFacet_is_displayed (p : RegularData d ι)
    (F : HalfspaceFaces (fun i => (p.data.1 i).toLinearMap) p.data.2)
    (hF : IsActualFacet p F) : ∃ i, F = displayedFacet p i := by
  let I : Set ι := {j | ∀ x ∈ F.val, p.data.1 j x = p.data.2 j}
  have heq : F.val = tightFace (fun j => (p.data.1 j).toLinearMap) p.data.2 I :=
    exposedFace_eq_tightFace _ _ F.property hF.1
  have hn : I.Nonempty := by
    by_contra hno
    have hI := Set.not_nonempty_iff_eq_empty.mp hno
    apply hF.2.1
    rw [heq, hI]
    ext x
    simp [tightFace, dataRegion]
  obtain ⟨i, hi⟩ := hn
  refine ⟨i, (hF.2.2 (displayedFacet p i) ?_ (displayedFacet_ne_carrier p i)).symm⟩
  intro x hx
  exact ⟨F.property.subset hx, by simpa using hi x hx⟩

theorem displayedFacet_injective (p : RegularData d ι) :
    Function.Injective (displayedFacet p) := by
  intro i j hij
  by_contra hne
  obtain ⟨x, hx, hxi, hxs⟩ := p.strict_facet_point i
  have hxF : x ∈ (displayedFacet p i).val := ⟨hx, by simpa using hxi⟩
  rw [hij] at hxF
  have hxj := hxF.2 j (Set.mem_singleton j)
  exact (ne_of_lt (hxs j (Ne.symm hne))) hxj

/-- A finite bounded halfspace presentation is a finite vertex polytope. -/
theorem carrier_finite_vertex_hull (p : RegularData d ι) :
    ((dataRegion p.data).extremePoints ℝ).Finite ∧
      dataRegion p.data = convexHull ℝ ((dataRegion p.data).extremePoints ℝ) :=
  ⟨halfspace_extremePoints_finite _ _, compact_halfspace_eq_convexHull_extremePoints _ _ p.compact⟩

end NormalProjective.UnitNormalization
end

/- Source: NormalProjective/FacetModelCoverage.lean -/
section
/-! # The strict-facet presentation agrees with ordinary complete facet data -/
open Set
namespace NormalProjective.UnitNormalization
variable {d : ℕ} {ι : Type*} [Fintype ι]

def rawDisplayedFacet (p : HalfspaceData ι (Space d)) (i : ι) :
    HalfspaceFaces (fun j => (p.1 j).toLinearMap) p.2 :=
  ⟨tightFace (fun j => (p.1 j).toLinearMap) p.2 {i}, tightFace_isExposed _ _ _⟩

/-- The ordinary geometric statement that the displayed faces are distinct
nonempty maximal proper exposed faces. This does not assume strict facet points. -/
def ActualFacetData (p : HalfspaceData ι (Space d)) : Prop :=
  Function.Injective (rawDisplayedFacet p) ∧
    ∀ i, (rawDisplayedFacet p i).val.Nonempty ∧
      (rawDisplayedFacet p i).val ≠ dataRegion p ∧
      ∀ G : HalfspaceFaces (fun j => (p.1 j).toLinearMap) p.2,
        rawDisplayedFacet p i ≤ G → G.val ≠ dataRegion p → G = rawDisplayedFacet p i

theorem regular_actualFacetData (p : RegularData d ι) : ActualFacetData p.data :=
  ⟨displayedFacet_injective p, fun i => displayedFacet_isActualFacet p i⟩

theorem actualFacetData_strict_points (p : HalfspaceData ι (Space d))
    (hp : ActualFacetData p) (i : ι) :
    ∃ x ∈ dataRegion p, p.1 i x = p.2 i ∧ ∀ j, j ≠ i → p.1 j x < p.2 j := by
  let f := fun j => (p.1 j).toLinearMap
  let F := rawDisplayedFacet p i
  obtain ⟨x, hxF, hx⟩ := exists_common_tight_point f p.2 (hp.2 i).1
    (F.property.convex (convex_halfspaceRegion f p.2)) F.property.subset
  refine ⟨x, hxF.1, hxF.2 i (Set.mem_singleton i), fun j hji => ?_⟩
  apply lt_of_le_of_ne (hxF.1 j)
  intro heq
  have hsub : F ≤ rawDisplayedFacet p j := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    intro k hk
    have hkj := Set.mem_singleton_iff.mp hk
    subst k
    exact (hx j).mp heq y hy
  have heF : rawDisplayedFacet p j = F :=
    (hp.2 i).2.2 (rawDisplayedFacet p j) hsub (hp.2 j).2.1
  exact hji (hp.1 heF)

theorem actualFacetData_nonzero (p : HalfspaceData ι (Space d))
    (hp : ActualFacetData p) (i : ι) : p.1 i ≠ 0 := by
  intro hf
  obtain ⟨x, hx⟩ := (hp.2 i).1
  have hxi := hx.2 i (Set.mem_singleton i)
  change p.1 i x = p.2 i at hxi
  simp only [hf, ContinuousLinearMap.zero_apply] at hxi
  apply (hp.2 i).2.1
  ext y
  constructor
  · exact fun hy => hy.1
  · intro hy
    refine ⟨hy, ?_⟩
    intro j hj
    have hji := Set.mem_singleton_iff.mp hj
    subst j
    simp only [hf, ContinuousLinearMap.zero_apply]
    exact hxi

/-- Every compact full-dimensional ordinary complete facet presentation is
accepted by the canonical model, with exactly the original carrier and labels. -/
def regularOfActualFacets (p : HalfspaceData ι (Space d))
    (hc : IsCompact (dataRegion p)) (hf : (interior (dataRegion p)).Nonempty)
    (hp : ActualFacetData p) : RegularData d ι where
  data := p
  normal_ne_zero := actualFacetData_nonzero p hp
  compact := hc
  full_dimensional := hf
  strict_facet_point := actualFacetData_strict_points p hp

def displayedFacetEquiv (p : RegularData d ι) :
    ι ≃ {F : HalfspaceFaces (fun j => (p.data.1 j).toLinearMap) p.data.2 // IsActualFacet p F} := by
  apply Equiv.ofBijective (fun i => ⟨displayedFacet p i, displayedFacet_isActualFacet p i⟩)
  constructor
  · intro i j hij
    exact displayedFacet_injective p (congrArg Subtype.val hij)
  · intro F
    obtain ⟨i, hi⟩ := actualFacet_is_displayed p F.val F.property
    exact ⟨i, Subtype.ext hi.symm⟩

/-- Canonical objects are genuine finite vertex polytopes, and their labels
enumerate every actual facet exactly once. -/
theorem presentation_finite_vertices_and_all_facets (P : CanonicalModel.Presentation d ι) :
    (P.carrier.extremePoints ℝ).Finite ∧
      P.carrier = convexHull ℝ (P.carrier.extremePoints ℝ) ∧
      Nonempty (ι ≃ {F : HalfspaceFaces
        (fun j => ((ofCanonical P).data.1 j).toLinearMap) (ofCanonical P).data.2 //
          IsActualFacet (ofCanonical P) F}) := by
  obtain ⟨hfinite, hhull⟩ := carrier_finite_vertex_hull (ofCanonical P)
  have hcar : dataRegion (ofCanonical P).data = P.carrier := by
    rw [← presentation_carrier, presentation_ofCanonical]
  rw [hcar] at hfinite hhull
  exact ⟨hfinite, hhull, ⟨displayedFacetEquiv (ofCanonical P)⟩⟩

end NormalProjective.UnitNormalization
end

/- Source: NormalProjective/RootedGeometry.lean -/
section
/-! # Rooted facet coordinates for actual PN moves -/
open Set Matrix
open scoped BigOperators
namespace NormalProjective.UnitNormalization
variable {d : ℕ} {ι : Type*} [Fintype ι]

@[simp] theorem coefficients_neg (f : Space d →L[ℝ] ℝ) :
    coefficients (-f) = -coefficients f := by ext j; rfl

@[simp] theorem length_neg (f : Space d →L[ℝ] ℝ) : length (-f) = length f := by
  simp [length, coefficients_neg]

@[simp] theorem unitRow_neg (f : Space d →L[ℝ] ℝ) : unitRow (-f) = -unitRow f := by
  ext j
  simp [unitRow, neg_div]

theorem form_eq_positive_smul_of_unitRow_eq
    (f g : Space d →L[ℝ] ℝ) (hf : f ≠ 0) (hg : g ≠ 0)
    (h : unitRow f = unitRow g) :
    g = (length g / length f) • f := by
  have hlf := ne_of_gt (length_pos f hf)
  have hlg := ne_of_gt (length_pos g hg)
  have hcoeff : coefficients g = (length g / length f) • coefficients f := by
    funext j
    have hh := congrFun h j
    change coefficients f j / length f = coefficients g j / length g at hh
    change coefficients g j = (length g / length f) * coefficients f j
    field_simp at hh ⊢
    nlinarith
  apply ContinuousLinearMap.ext
  intro x
  change g x = (length g / length f) * f x
  rw [← coefficient_expansion g x, ← coefficient_expansion f x]
  simp only [hcoeff, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- Two raw systems with equal outward unit normals differ by positive row
scalings, with the scalars determined by the actual Euclidean row lengths. -/
def alignedRegular (p q : RegularData d ι)
    (h : (presentation p).normal = (presentation q).normal) : RegularData d ι :=
  scaleRegular q (fun i => length (p.data.1 i) / length (q.data.1 i))
    (fun i => div_pos (length_pos _ (p.normal_ne_zero i)) (length_pos _ (q.normal_ne_zero i)))

theorem alignedRegular_normals (p q : RegularData d ι)
    (h : (presentation p).normal = (presentation q).normal) :
    (alignedRegular p q h).data.1 = p.data.1 := by
  funext i
  have hh : unitRow (p.data.1 i) = unitRow (q.data.1 i) := congrFun h i
  have hform := form_eq_positive_smul_of_unitRow_eq (p.data.1 i) (q.data.1 i)
    (p.normal_ne_zero i) (q.normal_ne_zero i) hh
  change (length (p.data.1 i) / length (q.data.1 i)) • q.data.1 i = p.data.1 i
  have hr : (length (p.data.1 i) / length (q.data.1 i)) *
      (length (q.data.1 i) / length (p.data.1 i)) = 1 := by
    field_simp [ne_of_gt (length_pos _ (p.normal_ne_zero i)),
      ne_of_gt (length_pos _ (q.normal_ne_zero i))]
  calc
    (length (p.data.1 i) / length (q.data.1 i)) • q.data.1 i =
        (length (p.data.1 i) / length (q.data.1 i)) •
          ((length (q.data.1 i) / length (p.data.1 i)) • p.data.1 i) :=
      congrArg (fun z => (length (p.data.1 i) / length (q.data.1 i)) • z) hform
    _ = p.data.1 i := by rw [smul_smul, hr, one_smul]

theorem presentation_alignedRegular (p q : RegularData d ι)
    (h : (presentation p).normal = (presentation q).normal) :
    presentation (alignedRegular p q h) = presentation q :=
  presentation_scaleRegular q _ _

/-- The elementary construction also applies to rooted systems, whose supports
at the distinguished vertex are zero. Full dimension is witnessed by the image
of an actual strictly feasible point, rather than by the root. -/
def elementaryRegularNonnegative (p : RegularData d ι) (u : Space d →L[ℝ] ℝ)
    (hp : ∀ i, 0 ≤ p.data.2 i)
    (hu : ∀ x ∈ dataRegion p.data, 0 < 1 + u x) : RegularData d ι := by
  let f := fun i => (p.data.1 i).toLinearMap
  let T := ProjectiveBridge.elementary u.toLinearMap
  have hT : T '' dataRegion p.data = dataRegion (elementaryData p u) :=
    ProjectiveBridge.elementary_image_HRegion f p.data.2 hp p.compact.isBounded u.toLinearMap hu
  have hinc (x : Space d) (hx : x ∈ dataRegion p.data) (i : ι) :
      (elementaryData p u).1 i (T x) = p.data.2 i ↔ p.data.1 i x = p.data.2 i :=
    ElementaryProjectivity.tight_iff f p.data.2 u.toLinearMap x (hu x hx) i
  have hct : ContinuousOn T (dataRegion p.data) :=
    ((continuousOn_const.add u.continuous.continuousOn).inv₀
      (fun x hx => ne_of_gt (hu x hx))).smul continuousOn_id
  refine {
    data := elementaryData p u
    normal_ne_zero := ?_
    compact := hT ▸ p.compact.image_of_continuousOn hct
    full_dimensional := ?_
    strict_facet_point := ?_ }
  · intro i hi
    by_cases hz : p.data.2 i = 0
    · have hh : p.data.1 i = 0 := by simpa [elementaryData, hz] using hi
      exact p.normal_ne_zero i hh
    · obtain ⟨x, hx, hxi, _⟩ := p.strict_facet_point i
      have hh := (hinc x hx i).mpr hxi
      rw [hi] at hh
      exact hz (by simpa using hh.symm)
  · obtain ⟨x, hx⟩ := p.full_dimensional
    have hxK := interior_subset hx
    refine ⟨T x, strict_mem_dataRegion_interior _ (fun i => ?_)⟩
    change ProjectiveBridge.changedNormals f p.data.2 u.toLinearMap i (T x) < p.data.2 i
    rw [ProjectiveBridge.linear_elementary, ProjectiveBridge.changedNormals_apply]
    apply (div_lt_iff₀ (hu x hxK)).mpr
    have hh := regular_interior_strict p hx i
    change p.data.1 i x + p.data.2 i * u x < p.data.2 i * (1 + u x)
    nlinarith
  · intro i
    obtain ⟨x, hx, hxi, hxs⟩ := p.strict_facet_point i
    have hTx : T x ∈ dataRegion (elementaryData p u) := hT ▸ ⟨x, hx, rfl⟩
    refine ⟨T x, hTx, (hinc x hx i).mpr hxi, fun j hji => ?_⟩
    apply lt_of_le_of_ne (hTx j)
    intro heq
    exact (ne_of_lt (hxs j hji)) ((hinc x hx j).mp heq)

theorem elementaryRegularNonnegative_carrier
    (p : RegularData d ι) (u : Space d →L[ℝ] ℝ)
    (hp : ∀ i, 0 ≤ p.data.2 i)
    (hu : ∀ x ∈ dataRegion p.data, 0 < 1 + u x) :
    (presentation (elementaryRegularNonnegative p u hp hu)).carrier =
      ProjectiveBridge.elementary u.toLinearMap '' (presentation p).carrier := by
  rw [presentation_carrier, presentation_carrier]
  exact (ProjectiveBridge.elementary_image_HRegion (fun i => (p.data.1 i).toLinearMap)
    p.data.2 hp p.compact.isBounded u.toLinearMap hu).symm

theorem elementaryRegularNonnegative_facet
    (p : RegularData d ι) (u : Space d →L[ℝ] ℝ)
    (hp : ∀ i, 0 ≤ p.data.2 i)
    (hu : ∀ x ∈ dataRegion p.data, 0 < 1 + u x) (i : ι) :
    (presentation (elementaryRegularNonnegative p u hp hu)).facet i =
      ProjectiveBridge.elementary u.toLinearMap '' (presentation p).facet i := by
  rw [presentation_facet, presentation_facet]
  exact (ElementaryProjectivity.elementary_image_facet
    (fun i => (p.data.1 i).toLinearMap) p.data.2 hp p.compact.isBounded u.toLinearMap hu i).symm

end NormalProjective.UnitNormalization

namespace NormalProjective.RootedGeometry
open UnitNormalization CanonicalModel CanonicalModel.Realization
variable {d : ℕ}

abbrev Labels (d : ℕ) := Sum (Fin d) (Fin d)

def rootedData (A : Matrix (Fin d) (Fin d) ℝ) :
    HalfspaceData (Labels d) (CanonicalModel.Space d) :=
  (Sum.elim (fun j => -ContinuousLinearMap.proj j) (fun i => rowForm (A i)),
    Sum.elim (fun _ => 0) (fun _ => 1))

theorem rootedRegion (A : Matrix (Fin d) (Fin d) ℝ) :
    dataRegion (rootedData A) =
      {x : CanonicalModel.Space d | (∀ j, 0 ≤ x j) ∧ ∀ i, CanonicalModel.dot (A i) x ≤ 1} := by
  ext x
  simp [dataRegion, halfspaceRegion, rootedData, Sum.forall]

theorem rooted_zero_mem (A : Matrix (Fin d) (Fin d) ℝ) :
    (0 : CanonicalModel.Space d) ∈ dataRegion (rootedData A) := by
  rw [rootedRegion]
  simp [CanonicalModel.dot]

def lowerEmbedding (d : ℕ) : Fin d ↪ Labels d := ⟨Sum.inl, Sum.inl_injective⟩

theorem rooted_lower_matrix (A : Matrix (Fin d) (Fin d) ℝ) :
    facetCoefficientMatrix (fun j => ((rootedData A).1 (lowerEmbedding d j)).toLinearMap) =
      -(1 : Matrix (Fin d) (Fin d) ℝ) := by
  ext i j
  simp [facetCoefficientMatrix, rootedData, lowerEmbedding, Matrix.one_apply, Pi.single_apply]

theorem rooted_zero_vertex (A : Matrix (Fin d) (Fin d) ℝ) :
    (0 : CanonicalModel.Space d) ∈ (dataRegion (rootedData A)).extremePoints ℝ := by
  apply nonsingular_tight_minor_is_vertex (fun i => ((rootedData A).1 i).toLinearMap)
    (rootedData A).2 (lowerEmbedding d)
  · rw [rooted_lower_matrix, Matrix.det_neg, Matrix.det_one]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) one_ne_zero
  · exact rooted_zero_mem A
  · intro j
    simp [rootedData, lowerEmbedding]

/-- A frame is an actual affine coordinate map and an exact normalized facet
presentation; it is not an assumed matrix reduction of a PN sequence. -/
structure Frame (P : Presentation d (Labels d)) where
  matrix : Matrix (Fin d) (Fin d) ℝ
  regular : RegularData d (Labels d)
  data_eq : regular.data = rootedData matrix
  affine : CanonicalModel.Space d ≃ᵃ[ℝ] CanonicalModel.Space d
  presentation_eq : presentation regular = affinePresentation affine P

theorem Frame.root_mem {P : Presentation d (Labels d)} (F : Frame P) :
    (0 : CanonicalModel.Space d) ∈ (presentation F.regular).carrier := by
  rw [presentation_carrier, F.data_eq]
  exact rooted_zero_mem F.matrix

theorem rooted_elementary_data (A : Matrix (Fin d) (Fin d) ℝ)
    (p : RegularData d (Labels d)) (hp : p.data = rootedData A)
    (u : CanonicalModel.Space d →L[ℝ] ℝ) :
    elementaryData p u = rootedData (A + RankObstruction.outer (coefficients u)) := by
  apply Prod.ext
  · funext i
    cases i with
    | inl j => simp [elementaryData, hp, rootedData]
    | inr i =>
        change p.data.1 (Sum.inr i) + p.data.2 (Sum.inr i) • u = _
        rw [hp]
        change rowForm (A i) + (1 : ℝ) • u =
          rowForm (fun j => A i j + 1 * coefficients u j)
        apply ContinuousLinearMap.ext
        intro x
        simp only [one_smul, ContinuousLinearMap.add_apply, map_add, rowForm_apply, CanonicalModel.dot,
          one_mul, add_mul, Finset.sum_add_distrib]
        rw [coefficient_expansion]
  · change p.data.2 = (rootedData (A + RankObstruction.outer (coefficients u))).2
    rw [hp]
    rfl

end NormalProjective.RootedGeometry
end

/- Source: NormalProjective/RootedProjective.lean -/
section
/-! # A genuine projective step induces one rooted rank-one row addition -/
open Set Matrix
namespace NormalProjective.RootedGeometry
open UnitNormalization CanonicalModel CanonicalModel.Realization
variable {d : ℕ} {R : Presentation d (Labels d)}

theorem Frame.projective {P Q : Realization R} (F : Frame P.val)
    (h : ProjectiveStep P Q) :
    ∃ (G : Frame Q.val) (c : CanonicalModel.Space d),
      G.matrix = F.matrix + RankObstruction.outer c := by
  classical
  let p := F.regular
  let P' := affineAction F.affine P
  have hpPres : presentation p = P'.val := F.presentation_eq
  have hPK : P'.carrier = dataRegion p.data := by
    change P'.val.carrier = _
    rw [← hpPres, presentation_carrier]
  have h0 : (0 : CanonicalModel.Space d) ∈ P'.carrier := by
    rw [hPK, F.data_eq]
    exact rooted_zero_mem F.matrix
  have hstep : ProjectiveStep P' Q :=
    (affineRelated_symm (affineAction_related F.affine P)).projectiveStep.trans h
  obtain ⟨M, hM, hden, hMK, hMF⟩ := hstep
  have hα : M none none ≠ 0 := by simpa [denominator] using hden 0 h0
  let u := projectiveForm M
  have hp : ∀ i, 0 ≤ p.data.2 i := by
    rw [F.data_eq]
    intro i
    cases i <;> norm_num [rootedData]
  have hu : ∀ x ∈ dataRegion p.data, 0 < 1 + u x := by
    apply normalized_denominator_positive (dataRegion p.data)
      (convex_halfspaceRegion (fun i => (p.data.1 i).toLinearMap) p.data.2)
      (hPK ▸ h0) u
    intro x hx
    have hh := hden x (hPK.symm ▸ hx)
    rw [denominator_factor M hα] at hh
    exact (mul_ne_zero_iff.mp hh).2
  let q := elementaryRegularNonnegative p u hp hu
  let b := projectiveAffineFactor M hM hα
  have hqK : b '' (presentation q).carrier = Q.carrier := by
    rw [elementaryRegularNonnegative_carrier, Set.image_image]
    calc
      (fun x => b (ProjectiveBridge.elementary u.toLinearMap x)) '' (presentation p).carrier =
          projectiveMap M '' P'.carrier := by
        rw [hpPres]
        apply Set.image_congr
        intro x hx
        exact (projectiveMap_factor M hM hα x (hden x hx)).symm
      _ = Q.carrier := hMK
  have hqF (i : Labels d) : b '' (presentation q).facet i = Q.facet i := by
    rw [elementaryRegularNonnegative_facet, Set.image_image]
    calc
      (fun x => b (ProjectiveBridge.elementary u.toLinearMap x)) '' (presentation p).facet i =
          projectiveMap M '' P'.facet i := by
        rw [hpPres]
        apply Set.image_congr
        intro x hx
        exact (projectiveMap_factor M hM hα x (hden x hx.1)).symm
      _ = Q.facet i := hMF i
  have hpres : presentation q = affinePresentation b.symm Q.val := by
    apply presentation_eq_of_carrier_facets
    · rw [affinePresentation_carrier]
      change (presentation q).carrier = b.symm '' Q.carrier
      rw [← hqK, Set.image_image]
      simp
    · intro i
      rw [affinePresentation_facet]
      change (presentation q).facet i = b.symm '' Q.facet i
      rw [← hqF i, Set.image_image]
      simp
  refine ⟨{
    matrix := F.matrix + RankObstruction.outer (coefficients u)
    regular := q
    data_eq := rooted_elementary_data F.matrix p F.data_eq u
    affine := b.symm
    presentation_eq := hpres }, coefficients u, rfl⟩

end NormalProjective.RootedGeometry
end

/- Source: NormalProjective/RootedNormal.lean -/
section
/-! # A genuine normal step induces positive diagonal row scaling in a rooted frame -/
open Set Matrix
namespace NormalProjective.UnitNormalization
variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem affineRegular_presentation (a : Space d ≃ᵃ[ℝ] Space d) (p : RegularData d ι) :
    presentation (affineRegular a p) = affinePresentation a (presentation p) := by
  apply presentation_eq_of_carrier_facets
  · rw [affineRegular_carrier, affinePresentation_carrier]
  · intro i
    rw [affineRegular_facet, affinePresentation_facet]

theorem affinePresentation_trans (a b : Space d ≃ᵃ[ℝ] Space d)
    (P : CanonicalModel.Presentation d ι) :
    affinePresentation b (affinePresentation a P) = affinePresentation (a.trans b) P := by
  apply presentation_eq_of_carrier_facets
  · simp only [affinePresentation_carrier, Set.image_image]
    rfl
  · intro i
    simp only [affinePresentation_facet, Set.image_image]
    rfl

theorem affineData_translation (p : HalfspaceData ι (Space d)) (v : Space d) :
    affineData (AffineEquiv.constVAdd ℝ (Space d) v) p =
      (p.1, fun i => p.2 i + p.1 i v) := by
  apply Prod.ext
  · funext i
    apply ContinuousLinearMap.ext
    intro x
    simp [affineData]
  · funext i
    simp [affineData]

end NormalProjective.UnitNormalization

namespace NormalProjective.RootedGeometry
open UnitNormalization CanonicalModel CanonicalModel.Realization
variable {d : ℕ} {R : Presentation d (Labels d)}

theorem Frame.normal {P Q : Realization R} (F : Frame P.val)
    (h : NormalStep P Q) :
    ∃ (G : Frame Q.val) (w : CanonicalModel.Space d),
      (∀ i, 0 < w i) ∧ G.matrix = Matrix.diagonal w * F.matrix := by
  classical
  let p := F.regular
  let Q' := affineAction F.affine Q
  let q := ofCanonical Q'.val
  have hpPres : presentation p = (affineAction F.affine P).val := F.presentation_eq
  have hnorm : (presentation p).normal = (presentation q).normal := by
    rw [hpPres, presentation_ofCanonical]
    exact affineAction_normal F.affine h
  let r := alignedRegular p q hnorm
  have hrn : r.data.1 = p.data.1 := alignedRegular_normals p q hnorm
  have hrPres : presentation r = Q'.val := by
    rw [presentation_alignedRegular]
    exact presentation_ofCanonical _
  have htype : (presentation p).SameLabelledType (presentation r) := by
    rw [hpPres, hrPres]
    exact (affineAction F.affine P).property.symm.trans Q'.property
  have hraw := sameLabelledType_raw p r htype
  rw [hrn] at hraw
  obtain ⟨ef, hef⟩ := hraw
  let f := fun i => (p.data.1 i).toLinearMap
  have hrc : IsCompact (halfspaceRegion f r.data.2) := by
    change IsCompact (halfspaceRegion (fun i => (p.data.1 i).toLinearMap) r.data.2)
    rw [← hrn]
    exact r.compact
  let ev := faceIsoVertexEquiv f f p.data.2 r.data.2 p.compact hrc ef
  let z : HalfspaceVertices f p.data.2 := ⟨0, by
    change (0 : CanonicalModel.Space d) ∈ (dataRegion p.data).extremePoints ℝ
    rw [F.data_eq]
    exact rooted_zero_vertex F.matrix⟩
  let v := (ev z).val
  have hinc := faceIsoVertexEquiv_incidence f f p.data.2 r.data.2 p.compact hrc ef hef z
  have hv : v ∈ dataRegion r.data := by
    change ∀ i, r.data.1 i v ≤ r.data.2 i
    rw [hrn]
    exact (ev z).property.1
  have hlower (j : Fin d) : r.data.1 (Sum.inl j) v = r.data.2 (Sum.inl j) := by
    rw [hrn]
    apply (hinc (Sum.inl j)).mp
    change p.data.1 (Sum.inl j) 0 = p.data.2 (Sum.inl j)
    rw [F.data_eq]
    simp [rootedData]
  have hupper (i : Fin d) : r.data.1 (Sum.inr i) v < r.data.2 (Sum.inr i) := by
    apply lt_of_le_of_ne (hv (Sum.inr i))
    intro heq
    rw [hrn] at heq
    have hz := (hinc (Sum.inr i)).mpr heq
    change p.data.1 (Sum.inr i) 0 = p.data.2 (Sum.inr i) at hz
    rw [F.data_eq] at hz
    norm_num [rootedData, CanonicalModel.dot] at hz
  let a := AffineEquiv.constVAdd ℝ (CanonicalModel.Space d) (-v)
  let r' := affineRegular a r
  have hr'data : r'.data = (p.data.1, fun i => r.data.2 i - r.data.1 i v) := by
    change affineData a r.data = _
    rw [affineData_translation]
    simp only [hrn, map_neg, sub_eq_add_neg]
  let w : CanonicalModel.Space d := fun i =>
    (r.data.2 (Sum.inr i) - r.data.1 (Sum.inr i) v)⁻¹
  have hw : ∀ i, 0 < w i := fun i => inv_pos.mpr (sub_pos.mpr (hupper i))
  let ρ : Labels d → ℝ := Sum.elim (fun _ => 1) w
  have hρ : ∀ i, 0 < ρ i := by intro i; cases i <;> simp [ρ, hw]
  let s := scaleRegular r' ρ hρ
  have hsdata : s.data = rootedData (Matrix.diagonal w * F.matrix) := by
    apply Prod.ext
    · funext i
      cases i with
      | inl j =>
          change ρ (Sum.inl j) • r'.data.1 (Sum.inl j) = _
          rw [hr'data, F.data_eq]
          simp [ρ, rootedData]
      | inr i =>
          change ρ (Sum.inr i) • r'.data.1 (Sum.inr i) = _
          rw [hr'data, F.data_eq]
          apply ContinuousLinearMap.ext
          intro x
          simp only [ρ, Sum.elim_inr, rootedData, Matrix.diagonal_mul,
            ContinuousLinearMap.smul_apply, smul_eq_mul, rowForm_apply, CanonicalModel.dot]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
    · funext i
      cases i with
      | inl j =>
          change ρ (Sum.inl j) * r'.data.2 (Sum.inl j) = 0
          rw [hr'data]
          simp [ρ, hlower]
      | inr i =>
          change ρ (Sum.inr i) * r'.data.2 (Sum.inr i) = 1
          rw [hr'data]
          exact inv_mul_cancel₀ (ne_of_gt (sub_pos.mpr (hupper i)))
  have hpres : presentation s = affinePresentation (F.affine.trans a) Q.val := by
    rw [presentation_scaleRegular, affineRegular_presentation, hrPres]
    change affinePresentation a (affinePresentation F.affine Q.val) = _
    exact affinePresentation_trans F.affine a Q.val
  exact ⟨{
    matrix := Matrix.diagonal w * F.matrix
    regular := s
    data_eq := hsdata
    affine := F.affine.trans a
    presentation_eq := hpres }, w, hw, rfl⟩

end NormalProjective.RootedGeometry
end

/- Source: NormalProjective/RootedWords.lean -/
section
/-! # Every actual geometric word has the claimed rooted matrix word -/
open Set Matrix
open scoped BigOperators
namespace NormalProjective.RankObstruction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem RootedWord.append {A B C : Matrix ι ι ℝ} {p n q m : ℕ}
    (h₁ : RootedWord A B p n) (h₂ : RootedWord B C q m) :
    RootedWord A C (p + q) (n + m) := by
  induction h₂ with
  | nil => simpa using h₁
  | projective h c ih => simpa only [Nat.add_assoc] using ih.projective c
  | normal h w hw ih => simpa only [Nat.add_assoc] using ih.normal w hw

end NormalProjective.RankObstruction

namespace NormalProjective.RootedGeometry
open UnitNormalization CanonicalModel CanonicalModel.Realization RankObstruction
variable {d : ℕ} {R : Presentation d (Labels d)}

theorem rooted_word_of_actual_word {P Q : Realization R} {p n : ℕ}
    (h : PNWord P Q p n) (F : Frame P.val) :
    ∃ G : Frame Q.val, RootedWord F.matrix G.matrix p n := by
  induction h with
  | nil P => exact ⟨F, RootedWord.nil _⟩
  | @projective P Q U p n hs ht ih =>
      obtain ⟨G, c, hG⟩ := F.projective hs
      obtain ⟨H, hH⟩ := ih G
      have hFG : RootedWord F.matrix G.matrix 1 0 := by
        rw [hG]
        exact (RootedWord.nil F.matrix).projective c
      exact ⟨H, by simpa [Nat.add_comm] using hFG.append hH⟩
  | @normal P Q U p n hs ht ih =>
      obtain ⟨G, w, hw, hG⟩ := F.normal hs
      obtain ⟨H, hH⟩ := ih G
      have hFG : RootedWord F.matrix G.matrix 0 1 := by
        rw [hG]
        exact (RootedWord.nil F.matrix).normal w hw
      exact ⟨H, by simpa [Nat.add_comm] using hFG.append hH⟩

def OppositeNormals (P : Presentation d (Labels d)) : Prop :=
  ∀ i, P.normal (Sum.inr i) = -P.normal (Sum.inl i)

theorem rowForm_neg (v : CanonicalModel.Space d) : rowForm (-v) = -rowForm v := by
  apply ContinuousLinearMap.ext
  intro x
  simp [rowForm_apply, CanonicalModel.dot, Finset.sum_neg_distrib]

theorem oppositeNormals_affine (P : Presentation d (Labels d)) (h : OppositeNormals P)
    (a : CanonicalModel.Space d ≃ᵃ[ℝ] CanonicalModel.Space d) :
    OppositeNormals (affinePresentation a P) := by
  intro i
  change unitRow ((rowForm (P.normal (Sum.inr i))).comp a.symm.linear.toContinuousLinearMap) =
    -unitRow ((rowForm (P.normal (Sum.inl i))).comp a.symm.linear.toContinuousLinearMap)
  rw [h i, rowForm_neg]
  simp

@[simp] theorem unitRow_proj (i : Fin d) :
    unitRow (ContinuousLinearMap.proj i : CanonicalModel.Space d →L[ℝ] ℝ) = Pi.single i 1 := by
  ext j
  simp [unitRow, length, coefficients, Pi.single_apply, eq_comm]

theorem Frame.diagonal_of_oppositeNormals {P : Presentation d (Labels d)}
    (F : Frame P) (h : OppositeNormals P) :
    ∃ w : CanonicalModel.Space d, F.matrix = Matrix.diagonal w := by
  have hp := oppositeNormals_affine P h F.affine
  rw [← F.presentation_eq] at hp
  let w : CanonicalModel.Space d := fun i => length (rowForm (F.matrix i))
  refine ⟨w, ?_⟩
  ext i j
  have hu := hp i
  change unitRow (F.regular.data.1 (Sum.inr i)) =
    -unitRow (F.regular.data.1 (Sum.inl i)) at hu
  rw [F.data_eq] at hu
  change unitRow (rowForm (F.matrix i)) = -unitRow (-ContinuousLinearMap.proj i) at hu
  rw [unitRow_neg, unitRow_proj, neg_neg] at hu
  have hn : rowForm (F.matrix i) ≠ 0 := by
    have hh := F.regular.normal_ne_zero (Sum.inr i)
    rw [F.data_eq] at hh
    exact hh
  have hlen := ne_of_gt (length_pos _ hn)
  have hh := congrFun hu j
  change coefficients (rowForm (F.matrix i)) j / length (rowForm (F.matrix i)) =
    (Pi.single i (1 : ℝ) : CanonicalModel.Space d) j at hh
  rw [coefficients_rowForm, div_eq_iff hlen] at hh
  simpa [w, Matrix.diagonal, Pi.single_apply, eq_comm, mul_comm] using hh

/-- This is a theorem about arbitrary actual PN-sequences. The rooted matrix
word is constructed from every allowed move; it is not an additional premise. -/
theorem actual_cyclic_word_counts {n : ℕ} {ε : ℝ} (hε : ε ≠ 0)
    {R : Presentation (n + 1) (Labels (n + 1))}
    {P Q : Realization R} (F : Frame P.val)
    (hF : F.matrix = cyclicMatrix n ε) (hQ : OppositeNormals Q.val)
    {p q : ℕ} (h : PNWord P Q p q) :
    n ≤ p ∧ n ≤ q + 1 ∧ 2 * n - 1 ≤ p + q := by
  obtain ⟨G, hw⟩ := rooted_word_of_actual_word h F
  obtain ⟨w, hG⟩ := G.diagonal_of_oppositeNormals hQ
  rw [hF, hG] at hw
  exact cyclic_word_counts n hε hw

end NormalProjective.RootedGeometry
end

/- Source: NormalProjective/CyclicCube.lean -/
section
/-! # All vertices and the actual labelled cube type of the entire cyclic family -/
open Set Matrix
open scoped BigOperators
namespace NormalProjective.CyclicCube
open UnitNormalization CanonicalModel CanonicalModel.Realization RootedGeometry RankObstruction
variable {n : ℕ}

abbrev E (n : ℕ) := Fin (n + 1) → ℝ

def cubeData (n : ℕ) (ε : ℝ) := rootedData (cyclicMatrix n ε)

def unitBox (n : ℕ) : Set (E n) := Set.Icc (fun _ => 0) (fun _ => 1)

theorem cyclic_dot (ε : ℝ) (i : Fin (n + 1)) (x : E n) :
    CanonicalModel.dot (cyclicMatrix n ε i) x = x i + ε * x (cyclicSucc n i) := by
  classical
  simp [CanonicalModel.dot, cyclicMatrix, add_mul, Finset.sum_add_distrib, ite_mul]

theorem cubeRegion (ε : ℝ) :
    dataRegion (cubeData n ε) =
      {x : E n | (∀ i, 0 ≤ x i) ∧ ∀ i, x i + ε * x (cyclicSucc n i) ≤ 1} := by
  rw [cubeData, rootedRegion]
  simp only [cyclic_dot]

theorem feasible_bounds {ε : ℝ} (hε : 0 ≤ ε) {x : E n}
    (hx : x ∈ dataRegion (cubeData n ε)) : x ∈ unitBox n := by
  rw [cubeRegion] at hx
  refine ⟨hx.1, fun i => ?_⟩
  have hmul := mul_nonneg hε (hx.1 (cyclicSucc n i))
  linarith [hx.2 i]

theorem cubeRegion_compact {ε : ℝ} (hε : 0 ≤ ε) :
    IsCompact (dataRegion (cubeData n ε)) :=
  isCompact_Icc.of_isClosed_subset (dataRegion_closed _) (fun _ hx => feasible_bounds hε hx)

def assignmentMap (ε : ℝ) (b : Fin (n + 1) → Bool) (x : E n) : E n :=
  fun i => if b i then 1 - ε * x (cyclicSucc n i) else 0

theorem assignment_contracting {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (b : Fin (n + 1) → Bool) : ContractingWith ⟨ε, hε0⟩ (assignmentMap ε b) := by
  refine ⟨hε1, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
  apply (dist_pi_le_iff (mul_nonneg hε0 dist_nonneg)).mpr
  intro i
  by_cases hi : b i = true
  · simp only [assignmentMap, hi, Bool.true_eq, if_true]
    calc
      dist (1 - ε * x (cyclicSucc n i)) (1 - ε * y (cyclicSucc n i)) =
          ε * dist (x (cyclicSucc n i)) (y (cyclicSucc n i)) := by
        rw [Real.dist_eq, Real.dist_eq,
          show (1 - ε * x (cyclicSucc n i)) - (1 - ε * y (cyclicSucc n i)) =
            -ε * (x (cyclicSucc n i) - y (cyclicSucc n i)) by ring,
          abs_mul, abs_neg, abs_of_nonneg hε0]
      _ ≤ ε * dist x y := mul_le_mul_of_nonneg_left
        (dist_le_pi_dist x y (cyclicSucc n i)) hε0
  · have hif : b i = false := Bool.eq_false_iff.mpr hi
    simp only [assignmentMap, hif, Bool.false_eq_true, if_false, dist_self]
    exact mul_nonneg hε0 dist_nonneg

theorem assignment_mapsTo {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (b : Fin (n + 1) → Bool) : MapsTo (assignmentMap ε b) (unitBox n) (unitBox n) := by
  intro x hx
  constructor <;> intro i
  · by_cases hi : b i = true
    · simp only [assignmentMap, hi, Bool.true_eq, if_true]
      have hh := mul_le_mul_of_nonneg_left (hx.2 (cyclicSucc n i)) hε0
      linarith
    · have hif : b i = false := Bool.eq_false_iff.mpr hi
      simp [assignmentMap, hif]
  · by_cases hi : b i = true
    · simp only [assignmentMap, hi, Bool.true_eq, if_true]
      have hh := mul_nonneg hε0 (hx.1 (cyclicSucc n i))
      linarith
    · have hif : b i = false := Bool.eq_false_iff.mpr hi
      simp [assignmentMap, hif]

theorem assignment_exists {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (b : Fin (n + 1) → Bool) :
    ∃ x ∈ unitBox n, Function.IsFixedPt (assignmentMap ε b) x := by
  have hm := assignment_mapsTo hε0 hε1 b
  have hc := assignment_contracting hε0 hε1 b
  obtain ⟨x, hx, hfix, _⟩ := ContractingWith.exists_fixedPoint'
    (s := unitBox n) isClosed_Icc.isComplete hm (hc.restrict hm)
    (show (0 : E n) ∈ unitBox n by constructor <;> intro i <;> norm_num)
    (edist_ne_top (0 : E n) _)
  exact ⟨x, hx, hfix⟩

def assignedVertex {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (b : Fin (n + 1) → Bool) : E n := (assignment_exists hε0 hε1 b).choose

theorem assignedVertex_bounds {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (b : Fin (n + 1) → Bool) : assignedVertex hε0 hε1 b ∈ unitBox n :=
  (assignment_exists hε0 hε1 b).choose_spec.1

theorem assignedVertex_fixed {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (b : Fin (n + 1) → Bool) :
    Function.IsFixedPt (assignmentMap ε b) (assignedVertex hε0 hε1 b) :=
  (assignment_exists hε0 hε1 b).choose_spec.2

def Chosen (b : Fin (n + 1) → Bool) : Labels (n + 1) → Prop :=
  Sum.elim (fun i => b i = false) (fun i => b i = true)

theorem assignedVertex_mem {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (b : Fin (n + 1) → Bool) : assignedVertex hε0 hε1 b ∈ dataRegion (cubeData n ε) := by
  let x := assignedVertex hε0 hε1 b
  have hb := assignedVertex_bounds hε0 hε1 b
  have hf := assignedVertex_fixed hε0 hε1 b
  rw [cubeRegion]
  refine ⟨hb.1, fun i => ?_⟩
  have hi := congrFun hf i
  by_cases hbi : b i = true
  · simp only [assignmentMap, hbi, Bool.true_eq, if_true] at hi
    linarith
  · have hbi' : b i = false := Bool.eq_false_iff.mpr hbi
    simp only [assignmentMap, hbi', Bool.false_eq_true, if_false] at hi
    have hmul := mul_le_mul_of_nonneg_left (hb.2 (cyclicSucc n i)) hε0
    linarith

theorem assignedVertex_incidence {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (b : Fin (n + 1) → Bool) (i : Labels (n + 1)) :
    (cubeData n ε).1 i (assignedVertex hε0 hε1 b) = (cubeData n ε).2 i ↔ Chosen b i := by
  let x := assignedVertex hε0 hε1 b
  have hb := assignedVertex_bounds hε0 hε1 b
  have hf := assignedVertex_fixed hε0 hε1 b
  cases i with
  | inl i =>
      change -x i = 0 ↔ b i = false
      have hi := congrFun hf i
      cases hbi : b i with
      | false =>
          simp only [assignmentMap, hbi, Bool.false_eq_true, if_false] at hi
          have hxi : x i = 0 := hi.symm
          simp [hxi]
      | true =>
          simp only [assignmentMap, hbi, Bool.true_eq, if_true] at hi
          have hm := mul_le_mul_of_nonneg_left (hb.2 (cyclicSucc n i)) hε0
          have hx : 0 < x i := by change 0 < assignedVertex hε0 hε1 b i; linarith
          have hnx : -x i ≠ 0 := by linarith
          simp [hnx]
  | inr i =>
      change rowForm (cyclicMatrix n ε i) x = 1 ↔ b i = true
      rw [rowForm_apply, cyclic_dot]
      have hi := congrFun hf i
      cases hbi : b i with
      | false =>
          simp only [assignmentMap, hbi, Bool.false_eq_true, if_false] at hi
          have hm := mul_le_mul_of_nonneg_left (hb.2 (cyclicSucc n i)) hε0
          have hh : x i + ε * x (cyclicSucc n i) < 1 := by
            change assignedVertex hε0 hε1 b i + ε * assignedVertex hε0 hε1 b (cyclicSucc n i) < 1
            linarith
          simp [ne_of_lt hh]
      | true =>
          simp only [assignmentMap, hbi, Bool.true_eq, if_true] at hi
          have hh : x i + ε * x (cyclicSucc n i) = 1 := by
            change assignedVertex hε0 hε1 b i + ε * assignedVertex hε0 hε1 b (cyclicSucc n i) = 1
            linarith
          simp [hh]

theorem fixed_of_chosen_tight (ε : ℝ) (b : Fin (n + 1) → Bool) (x : E n)
    (hx : ∀ i, Chosen b i → (cubeData n ε).1 i x = (cubeData n ε).2 i) :
    Function.IsFixedPt (assignmentMap ε b) x := by
  funext i
  cases hbi : b i with
  | false =>
      have hi := hx (Sum.inl i) hbi
      change -x i = 0 at hi
      simp only [assignmentMap, hbi, Bool.false_eq_true, if_false]
      linarith
  | true =>
      have hi := hx (Sum.inr i) hbi
      change rowForm (cyclicMatrix n ε i) x = 1 at hi
      rw [rowForm_apply, cyclic_dot] at hi
      simp only [assignmentMap, hbi, Bool.true_eq, if_true]
      linarith

theorem assignedVertex_extreme {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (b : Fin (n + 1) → Bool) :
    assignedVertex hε0 hε1 b ∈ (dataRegion (cubeData n ε)).extremePoints ℝ := by
  let f := fun i => ((cubeData n ε).1 i).toLinearMap
  let h := (cubeData n ε).2
  have heq : tightFace f h {i | Chosen b i} = {assignedVertex hε0 hε1 b} := by
    ext x
    constructor
    · intro hx
      exact Set.mem_singleton_iff.mpr ((assignment_contracting hε0 hε1 b).fixedPoint_unique'
        (fixed_of_chosen_tight ε b x hx.2) (assignedVertex_fixed hε0 hε1 b))
    · rintro rfl
      exact ⟨assignedVertex_mem hε0 hε1 b,
        fun i hi => (assignedVertex_incidence hε0 hε1 b i).mpr hi⟩
  have hh := (tightFace_isExposed f h {i | Chosen b i}).isExtreme
  rw [heq] at hh
  exact isExtreme_singleton.mp hh

end NormalProjective.CyclicCube

namespace NormalProjective.CyclicCube
open UnitNormalization CanonicalModel CanonicalModel.Realization RootedGeometry RankObstruction
variable {n : ℕ}

/-- Two different labelled sides can be distinguished by a cube assignment. -/
theorem chosen_separates (i j : Labels (n + 1)) (hji : j ≠ i) :
    ∃ b : Fin (n + 1) → Bool, Chosen b i ∧ ¬Chosen b j := by
  classical
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          have hij : i ≠ j := fun hh => hji (by simpa [hh])
          exact ⟨fun k => decide (k = j), by simp [Chosen, hij], by simp [Chosen]⟩
      | inr j => exact ⟨fun _ => false, rfl, by simp [Chosen]⟩
  | inr i =>
      cases j with
      | inl j => exact ⟨fun _ => true, rfl, by simp [Chosen]⟩
      | inr j =>
          have hji' : j ≠ i := fun hh => hji (by simpa [hh])
          exact ⟨fun k => decide (k = i), by simp [Chosen], by simp [Chosen, hji']⟩

theorem chosen_exists (i : Labels (n + 1)) :
    ∃ b : Fin (n + 1) → Bool, Chosen b i := by
  cases i with
  | inl i => exact ⟨fun _ => false, rfl⟩
  | inr i => exact ⟨fun _ => true, rfl⟩

theorem cyclic_strict_facets {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    StrictFacetPoints (fun i => ((cubeData n ε).1 i).toLinearMap) (cubeData n ε).2 := by
  classical
  let f := fun i => ((cubeData n ε).1 i).toLinearMap
  let h := (cubeData n ε).2
  intro i
  let F := tightFace f h {i}
  have hFexp := tightFace_isExposed f h {i}
  have hFn : F.Nonempty := by
    obtain ⟨b, hb⟩ := chosen_exists i
    exact ⟨assignedVertex hε0 hε1 b, assignedVertex_mem hε0 hε1 b,
      by simpa only [Set.mem_singleton_iff, forall_eq, ContinuousLinearMap.coe_coe, f, h] using (assignedVertex_incidence hε0 hε1 b i).mpr hb⟩
  have hnot (j : Labels (n + 1)) (hji : j ≠ i) : ¬∀ x ∈ F, f j x = h j := by
    obtain ⟨b, hbi, hbj⟩ := chosen_separates i j hji
    intro hall
    have hxF : assignedVertex hε0 hε1 b ∈ F :=
      ⟨assignedVertex_mem hε0 hε1 b,
        by simpa only [Set.mem_singleton_iff, forall_eq, ContinuousLinearMap.coe_coe, f, h] using (assignedVertex_incidence hε0 hε1 b i).mpr hbi⟩
    exact hbj ((assignedVertex_incidence hε0 hε1 b j).mp (hall _ hxF))
  obtain ⟨x, hxF, hx⟩ := exists_common_tight_point f h hFn
    (hFexp.convex (convex_halfspaceRegion f h)) hFexp.subset
  refine ⟨x, hxF.1, hxF.2 i (Set.mem_singleton i), fun j hji => ?_⟩
  apply lt_of_le_of_ne (hxF.1 j)
  intro heq
  exact hnot j hji ((hx j).mp heq)

def cyclicRegular {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    RegularData (n + 1) (Labels (n + 1)) where
  data := cubeData n ε
  normal_ne_zero := by
    intro i hi
    cases i with
    | inl j =>
        have hh := congrArg (fun f : E n →L[ℝ] ℝ => f (Pi.single j 1)) hi
        norm_num [cubeData, rootedData] at hh
    | inr i =>
        have hh := congrArg (fun f : E n →L[ℝ] ℝ => f (fun _ => 1)) hi
        change rowForm (cyclicMatrix n ε i) (fun _ => 1) = 0 at hh
        rw [rowForm_apply, cyclic_dot] at hh
        linarith
  compact := cubeRegion_compact hε0
  full_dimensional := by
    refine ⟨fun _ => (1 / 4 : ℝ), strict_mem_dataRegion_interior _ (fun i => ?_)⟩
    cases i with
    | inl j => norm_num [cubeData, rootedData]
    | inr i =>
        change rowForm (cyclicMatrix n ε i) (fun _ => (1 / 4 : ℝ)) < 1
        rw [rowForm_apply, cyclic_dot]
        linarith
  strict_facet_point := cyclic_strict_facets hε0 hε1

theorem opposite_not_both_tight {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    {x : E n} (hx : x ∈ dataRegion (cubeData n ε)) (i : Fin (n + 1)) :
    ¬((cubeData n ε).1 (Sum.inl i) x = (cubeData n ε).2 (Sum.inl i) ∧
      (cubeData n ε).1 (Sum.inr i) x = (cubeData n ε).2 (Sum.inr i)) := by
  rintro ⟨hlo, hup⟩
  change -x i = 0 at hlo
  change rowForm (cyclicMatrix n ε i) x = 1 at hup
  rw [rowForm_apply, cyclic_dot] at hup
  have hb := feasible_bounds hε0 hx
  have hm := mul_le_mul_of_nonneg_left (hb.2 (cyclicSucc n i)) hε0
  linarith

def labelCoordinate : Labels (n + 1) → Fin (n + 1) := Sum.elim id id

theorem tight_labels_coordinate_injective {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    {x : E n} (hx : x ∈ dataRegion (cubeData n ε))
    {i j : Labels (n + 1)}
    (hi : (cubeData n ε).1 i x = (cubeData n ε).2 i)
    (hj : (cubeData n ε).1 j x = (cubeData n ε).2 j)
    (hij : labelCoordinate i = labelCoordinate j) : i = j := by
  cases i with
  | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl hij
      | inr j =>
          have heq : i = j := hij
          subst j
          exact False.elim (opposite_not_both_tight hε0 hε1 hx i ⟨hi, hj⟩)
  | inr i =>
      cases j with
      | inl j =>
          have heq : i = j := hij
          subst j
          exact False.elim (opposite_not_both_tight hε0 hε1 hx i ⟨hj, hi⟩)
      | inr j => exact congrArg Sum.inr hij

theorem every_vertex_assigned {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (x : HalfspaceVertices (fun i => ((cubeData n ε).1 i).toLinearMap) (cubeData n ε).2) :
    ∃ b : Fin (n + 1) → Bool, assignedVertex hε0 hε1 b = x.val := by
  classical
  let f := fun i => ((cubeData n ε).1 i).toLinearMap
  let h := (cubeData n ε).2
  obtain ⟨J, hJ, _⟩ := extremePoint_has_active_basis f h x.property
  have hinj : Function.Injective (fun k => labelCoordinate (J k)) := by
    intro j k heq
    exact J.injective (tight_labels_coordinate_injective hε0 hε1 x.property.1
      (hJ j) (hJ k) heq)
  have hsurj : Function.Surjective (fun k => labelCoordinate (J k)) :=
    Finite.surjective_of_injective hinj
  have hpair (i : Fin (n + 1)) : f (Sum.inl i) x.val = h (Sum.inl i) ∨
      f (Sum.inr i) x.val = h (Sum.inr i) := by
    obtain ⟨j, hj⟩ := hsurj i
    have ht := hJ j
    cases he : J j with
    | inl k =>
        have hki : k = i := by simpa only [he, labelCoordinate, Sum.elim_inl, id_eq] using hj
        left
        simpa only [he, hki] using ht
    | inr k =>
        have hki : k = i := by simpa only [he, labelCoordinate, Sum.elim_inr, id_eq] using hj
        right
        simpa only [he, hki] using ht
  let b : Fin (n + 1) → Bool := fun i => decide (f (Sum.inr i) x.val = h (Sum.inr i))
  have ht : ∀ i, Chosen b i → f i x.val = h i := by
    intro i hi
    cases i with
    | inl j =>
        have hno : ¬f (Sum.inr j) x.val = h (Sum.inr j) := by
          simpa [Chosen, b] using hi
        exact (hpair j).resolve_right hno
    | inr j => simpa [Chosen, b] using hi
  refine ⟨b, ?_⟩
  exact (assignment_contracting hε0 hε1 b).fixedPoint_unique'
    (assignedVertex_fixed hε0 hε1 b) (fixed_of_chosen_tight ε b x.val ht)

def verticesEquiv {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    (Fin (n + 1) → Bool) ≃
      HalfspaceVertices (fun i => ((cubeData n ε).1 i).toLinearMap) (cubeData n ε).2 := by
  classical
  let V (b : Fin (n + 1) → Bool) :=
    (⟨assignedVertex hε0 hε1 b, assignedVertex_extreme hε0 hε1 b⟩ :
      HalfspaceVertices (fun i => ((cubeData n ε).1 i).toLinearMap) (cubeData n ε).2)
  apply Equiv.ofBijective V
  constructor
  · intro a b hab
    have hv := congrArg Subtype.val hab
    funext i
    have he : (a i = true) ↔ (b i = true) := by
      change Chosen a (Sum.inr i) ↔ Chosen b (Sum.inr i)
      rw [← assignedVertex_incidence hε0 hε1 a (Sum.inr i),
        ← assignedVertex_incidence hε0 hε1 b (Sum.inr i)]
      change (cubeData n ε).1 (Sum.inr i) (V a).val = _ ↔
        (cubeData n ε).1 (Sum.inr i) (V b).val = _
      rw [hab]
    cases ha : a i <;> cases hb : b i <;> simp_all
  · intro x
    obtain ⟨b, hb⟩ := every_vertex_assigned hε0 hε1 x
    exact ⟨b, Subtype.ext hb⟩

end NormalProjective.CyclicCube

namespace NormalProjective.CyclicCube
open UnitNormalization CanonicalModel CanonicalModel.Realization RootedGeometry RankObstruction
variable {n : ℕ}

@[simp] theorem verticesEquiv_val {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (b : Fin (n + 1) → Bool) : (verticesEquiv hε0 hε1 b).val = assignedVertex hε0 hε1 b := rfl

def chosenLabelsEquiv (b : Fin (n + 1) → Bool) :
    {i : Labels (n + 1) // Chosen b i} ≃ Fin (n + 1) where
  toFun i := labelCoordinate i.val
  invFun i := if hi : b i = true then ⟨Sum.inr i, hi⟩ else
    ⟨Sum.inl i, Bool.eq_false_iff.mpr hi⟩
  left_inv i := by
    rcases i with ⟨i, hi⟩
    cases i with
    | inl i =>
        change b i = false at hi
        simp [labelCoordinate, hi]
    | inr i =>
        change b i = true at hi
        simp [labelCoordinate, hi]
  right_inv i := by
    dsimp only
    split_ifs <;> rfl

theorem cyclic_simple {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    (presentation (cyclicRegular (n := n) hε0 hε1)).Simple := by
  apply (simple_iff_raw _).mpr
  intro x hx
  obtain ⟨b, hb⟩ := every_vertex_assigned hε0 hε1 ⟨x, hx⟩
  change assignedVertex hε0 hε1 b = x at hb
  rw [← hb]
  calc
    Nat.card (ActiveFacet (fun i => ((cubeData n ε).1 i).toLinearMap)
        (cubeData n ε).2 (assignedVertex hε0 hε1 b)) =
        Nat.card {i : Labels (n + 1) // Chosen b i} :=
      Nat.card_congr (Equiv.subtypeEquivRight (assignedVertex_incidence hε0 hε1 b))
    _ = Nat.card (Fin (n + 1)) := Nat.card_congr (chosenLabelsEquiv b)
    _ = n + 1 := by simp

theorem cyclic_sameLabelledType {ε δ : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (presentation (cyclicRegular (n := n) hε0 hε1)).SameLabelledType
      (presentation (cyclicRegular hδ0 hδ1)) := by
  let f := fun i => ((cubeData n ε).1 i).toLinearMap
  let g := fun i => ((cubeData n δ).1 i).toLinearMap
  let h := (cubeData n ε).2
  let k := (cubeData n δ).2
  let e := (verticesEquiv (n := n) hε0 hε1).symm.trans (verticesEquiv (n := n) hδ0 hδ1)
  have he : ∀ (v : HalfspaceVertices f h) i, f i v.val = h i ↔ g i (e v).val = k i := by
    intro v i
    let b := (verticesEquiv hε0 hε1).symm v
    have h₁ := assignedVertex_incidence hε0 hε1 b i
    have h₂ := assignedVertex_incidence hδ0 hδ1 b i
    have hv : assignedVertex hε0 hε1 b = v.val := by
      simpa only [b, verticesEquiv_val] using
        congrArg Subtype.val ((verticesEquiv hε0 hε1).apply_symm_apply v)
    change _ ↔ _
    rw [hv] at h₁
    exact h₁.trans h₂.symm
  apply sameLabelledType_of_faceOrderIso (cyclicRegular hε0 hε1) (cyclicRegular hδ0 hδ1)
    (halfspaceFaceOrderIso f g h k (cubeRegion_compact hε0) (cubeRegion_compact hδ0) e he)
  exact fun i => halfspaceFaceOrderIso_facet _ _ _ _ _ _ _ _ i

/-- The reference realization is literally the ordinary closed unit cube. -/
def referenceCube (n : ℕ) : Presentation (n + 1) (Labels (n + 1)) :=
  presentation (cyclicRegular (n := n) (ε := 0) le_rfl zero_lt_one)

theorem referenceCube_carrier (n : ℕ) :
    (referenceCube n).carrier = unitBox n := by
  rw [referenceCube, presentation_carrier]
  change dataRegion (cubeData n 0) = _
  rw [cubeRegion]
  ext x
  simp [unitBox, Pi.le_def]

theorem referenceCube_oppositeNormals (n : ℕ) : OppositeNormals (referenceCube n) := by
  intro i
  change unitRow (rowForm (cyclicMatrix n 0 i)) =
    -unitRow (-ContinuousLinearMap.proj i)
  rw [unitRow_neg, neg_neg]
  congr 1
  apply ContinuousLinearMap.ext
  intro x
  rw [rowForm_apply, cyclic_dot]
  simp

def standardRealization (n : ℕ) : Realization (referenceCube n) :=
  ⟨referenceCube n, Presentation.sameLabelledType_refl _⟩

/-- The actual affine conversion from the convenient [0,1] chart to the paper's
specified target C_d=[-1,1]^d. It will be absorbed into the final P-step. -/
def cubeCentering (n : ℕ) : E n ≃ᵃ[ℝ] E n :=
  (LinearEquiv.smulOfNeZero ℝ (E n) 2 (by norm_num)).toAffineEquiv.trans
    (AffineEquiv.constVAdd ℝ (E n) (fun _ => -1))

@[simp] theorem cubeCentering_apply (n : ℕ) (x : E n) (i : Fin (n + 1)) :
    cubeCentering n x i = 2 * x i - 1 := by
  change -1 + 2 * x i = _
  ring

def centeredRealization (n : ℕ) : Realization (referenceCube n) :=
  affineAction (cubeCentering n) (standardRealization n)

theorem centeredRealization_carrier (n : ℕ) :
    (centeredRealization n).carrier = Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) := by
  change (affinePresentation (cubeCentering n) (referenceCube n)).carrier = _
  rw [affinePresentation_carrier, referenceCube_carrier]
  ext y
  obtain ⟨x, rfl⟩ := (cubeCentering n).surjective y
  rw [(cubeCentering n).injective.mem_set_image]
  change ((∀ i, 0 ≤ x i) ∧ ∀ i, x i ≤ 1) ↔
    ((∀ i, -1 ≤ cubeCentering n x i) ∧ ∀ i, cubeCentering n x i ≤ 1)
  simp only [cubeCentering_apply]
  constructor
  · rintro ⟨hl, hu⟩
    constructor <;> intro i <;> linarith [hl i, hu i]
  · rintro ⟨hl, hu⟩
    constructor <;> intro i <;> linarith [hl i, hu i]

theorem centeredRealization_oppositeNormals (n : ℕ) :
    OppositeNormals (centeredRealization n).val :=
  oppositeNormals_affine (referenceCube n) (referenceCube_oppositeNormals n) (cubeCentering n)

def realization {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) : Realization (referenceCube n) :=
  ⟨presentation (cyclicRegular hε0 hε1), cyclic_sameLabelledType le_rfl zero_lt_one hε0 hε1⟩

theorem realization_carrier {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    (realization (n := n) hε0 hε1).carrier =
      {x : E n | (∀ i, 0 ≤ x i) ∧ ∀ i, x i + ε * x (cyclicSucc n i) ≤ 1} := by
  change (presentation (cyclicRegular hε0 hε1)).carrier = _
  rw [presentation_carrier]
  exact cubeRegion ε

def initialFrame {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    Frame (realization (n := n) hε0 hε1).val where
  matrix := cyclicMatrix n ε
  regular := cyclicRegular hε0 hε1
  data_eq := rfl
  affine := AffineEquiv.refl ℝ (E n)
  presentation_eq := by
    apply presentation_eq_of_carrier_facets
    · rw [affinePresentation_carrier]
      change (presentation (cyclicRegular hε0 hε1)).carrier =
        (fun x : E n => x) '' (presentation (cyclicRegular hε0 hε1)).carrier
      exact (Set.image_id' _).symm
    · intro i
      rw [affinePresentation_facet]
      change (presentation (cyclicRegular hε0 hε1)).facet i =
        (fun x : E n => x) '' (presentation (cyclicRegular hε0 hε1)).facet i
      exact (Set.image_id' _).symm

/-- The geometric lower bound holds for every parameter 0 < ε < 1 and every
actual PN word to a realization with parallel opposite facets. All assertions
that the source is a simple labelled cube have been proved above. -/
theorem cyclic_geometric_lower_bound {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hn : 1 ≤ n) (Q : Realization (referenceCube n)) (hQ : OppositeNormals Q.val)
    {p q : ℕ} (hword : PNWord (realization hε0.le hε1) Q p q) :
    n ≤ p ∧ n - 1 ≤ q ∧ 2 * (n + 1) - 3 ≤ p + q := by
  have hh := actual_cyclic_word_counts (ne_of_gt hε0) (initialFrame hε0.le hε1) rfl hQ hword
  omega

/-- The lower-bound assertion of Theorem 3, with the literal unit cube as target
and every parameter in the paper's full open interval. -/
theorem cyclic_to_unitCube_lower_bound {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hn : 1 ≤ n) {p q : ℕ}
    (hword : PNWord (realization (n := n) hε0.le hε1) (standardRealization n) p q) :
    n ≤ p ∧ n - 1 ≤ q ∧ 2 * (n + 1) - 3 ≤ p + q :=
  cyclic_geometric_lower_bound hε0 hε1 hn (standardRealization n)
    (referenceCube_oppositeNormals n) hword

/-- The literal lower-bound target is exactly the paper's centered cube. -/
theorem cyclic_to_centeredCube_lower_bound {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hn : 1 ≤ n) {p q : ℕ}
    (hword : PNWord (realization (n := n) hε0.le hε1) (centeredRealization n) p q) :
    n ≤ p ∧ n - 1 ≤ q ∧ 2 * (n + 1) - 3 ≤ p + q :=
  cyclic_geometric_lower_bound hε0 hε1 hn (centeredRealization n)
    (centeredRealization_oppositeNormals n) hword

end NormalProjective.CyclicCube
end

/- Source: NormalProjective/PairedHalfspaces.lean -/
section
/-! # Recognition of a cube from disjoint opposite halfspaces

This is Lemma 6 of the paper. The proof first identifies the active labels at
every actual vertex. Releasing one tight inequality produces a point of an
actual exposed edge face; its finite vertex hull supplies the opposite endpoint.
Thus every Boolean assignment occurs, and actual vertex--facet incidence gives
the full exposed-face order isomorphism.
-/
open Set Matrix
namespace NormalProjective.PairedHalfspaces
open UnitNormalization CanonicalModel RootedGeometry CyclicCube
variable {n : ℕ}
abbrev L (n : ℕ) := Labels (n + 1)
abbrev V (n : ℕ) := Fin (n + 1) → ℝ

def NoOppositeTight (f : L n → V n →ₗ[ℝ] ℝ) (h : L n → ℝ) : Prop :=
  ∀ x ∈ halfspaceRegion f h, ∀ i,
    ¬(f (Sum.inl i) x = h (Sum.inl i) ∧ f (Sum.inr i) x = h (Sum.inr i))

theorem active_coordinate_injective
    (f : L n → V n →ₗ[ℝ] ℝ) (h : L n → ℝ) (hn : NoOppositeTight f h)
    {x : V n} (hx : x ∈ halfspaceRegion f h) {i j : L n}
    (hi : f i x = h i) (hj : f j x = h j)
    (he : labelCoordinate i = labelCoordinate j) : i = j := by
  cases i with
  | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl he
      | inr j =>
          have hij : i = j := he
          subst j
          exact False.elim (hn x hx i ⟨hi, hj⟩)
  | inr i =>
      cases j with
      | inl j =>
          have hij : i = j := he
          subst j
          exact False.elim (hn x hx i ⟨hj, hi⟩)
      | inr j => exact congrArg Sum.inr he

theorem vertex_pattern
    (f : L n → V n →ₗ[ℝ] ℝ) (h : L n → ℝ) (hn : NoOppositeTight f h)
    {x : V n} (hx : x ∈ (halfspaceRegion f h).extremePoints ℝ) :
    ∃ b : Fin (n + 1) → Bool, ∀ i, f i x = h i ↔ Chosen b i := by
  classical
  obtain ⟨J, hJ, _⟩ := extremePoint_has_active_basis f h hx
  have hinj : Function.Injective (fun k => labelCoordinate (J k)) := by
    intro j k he
    exact J.injective (active_coordinate_injective f h hn hx.1 (hJ j) (hJ k) he)
  have hsurj : Function.Surjective (fun k => labelCoordinate (J k)) :=
    Finite.surjective_of_injective hinj
  have hpair (i : Fin (n + 1)) : f (Sum.inl i) x = h (Sum.inl i) ∨
      f (Sum.inr i) x = h (Sum.inr i) := by
    obtain ⟨j, hj⟩ := hsurj i
    have ht := hJ j
    cases he : J j with
    | inl k =>
        have hki : k = i := by simpa only [he, labelCoordinate, Sum.elim_inl, id_eq] using hj
        left
        simpa only [he, hki] using ht
    | inr k =>
        have hki : k = i := by simpa only [he, labelCoordinate, Sum.elim_inr, id_eq] using hj
        right
        simpa only [he, hki] using ht
  let b : Fin (n + 1) → Bool := fun i => decide (f (Sum.inr i) x = h (Sum.inr i))
  refine ⟨b, fun i => ?_⟩
  cases i with
  | inl i =>
      change f (Sum.inl i) x = h (Sum.inl i) ↔ b i = false
      simp only [b, decide_eq_false_iff_not]
      constructor
      · intro hl hr
        exact hn x hx.1 i ⟨hl, hr⟩
      · intro hr
        exact (hpair i).resolve_right hr
  | inr i => simp [Chosen, b]

theorem simple_of_noOpposite
    (f : L n → V n →ₗ[ℝ] ℝ) (h : L n → ℝ) (hn : NoOppositeTight f h) :
    IsSimpleHalfspace f h := by
  intro x hx
  obtain ⟨b, hb⟩ := vertex_pattern f h hn hx
  calc
    Nat.card (ActiveFacet f h x) = Nat.card {i : L n // Chosen b i} :=
      Nat.card_congr (Equiv.subtypeEquivRight hb)
    _ = Nat.card (Fin (n + 1)) := Nat.card_congr (chosenLabelsEquiv b)
    _ = n + 1 := by simp

def selectedEmbedding (b : Fin (n + 1) → Bool) : Fin (n + 1) ↪ L n where
  toFun i := if b i then Sum.inr i else Sum.inl i
  inj' := by
    intro i j he
    have hh := congrArg labelCoordinate he
    simpa only [labelCoordinate, apply_ite, Sum.elim_inl, Sum.elim_inr, id_eq,
      ite_self] using hh

theorem selected_chosen (b : Fin (n + 1) → Bool) (i : Fin (n + 1)) :
    Chosen b (selectedEmbedding b i) := by
  cases hi : b i <;> simp [selectedEmbedding, Chosen, hi]

theorem selected_range (b : Fin (n + 1) → Bool) :
    Set.range (selectedEmbedding b) = {i | Chosen b i} := by
  ext i
  constructor
  · rintro ⟨j, rfl⟩
    exact selected_chosen b j
  · intro hi
    cases i with
    | inl i =>
        refine ⟨i, ?_⟩
        change b i = false at hi
        simp [selectedEmbedding, hi]
    | inr i =>
        refine ⟨i, ?_⟩
        change b i = true at hi
        simp [selectedEmbedding, hi]

theorem vertex_releasing_one_label
    (f : L n → V n →ₗ[ℝ] ℝ) (h : L n → ℝ)
    (hc : IsCompact (halfspaceRegion f h)) (hn : NoOppositeTight f h)
    {x : V n} (hx : x ∈ (halfspaceRegion f h).extremePoints ℝ)
    (b : Fin (n + 1) → Bool) (hb : ∀ i, f i x = h i ↔ Chosen b i)
    (j : Fin (n + 1)) :
    ∃ y ∈ (halfspaceRegion f h).extremePoints ℝ,
      (∀ k, k ≠ j → f (selectedEmbedding b k) y = h (selectedEmbedding b k)) ∧
      f (selectedEmbedding b j) y < h (selectedEmbedding b j) := by
  classical
  let I := selectedEmbedding b
  have hI (k : Fin (n + 1)) : f (I k) x = h (I k) := (hb _).mpr (selected_chosen b k)
  have hs := simple_of_noOpposite f h hn
  obtain ⟨hrange, hdet⟩ := simple_active_minor_spans f h hs hx I hI
  let v := -activeInverseVector f I j
  have hv (k : Fin (n + 1)) : f (I k) v = -((Pi.single j (1 : ℝ) : V n) k) := by
    rw [map_neg, activeInverseVector_eval f I hdet]
  have hdir : ∀ i, f i x = h i → f i v ≤ 0 := by
    intro i hi
    have hiR : i ∈ Set.range I := by rw [hrange]; exact hi
    obtain ⟨k, rfl⟩ := hiR
    rw [hv]
    simp [Pi.single_apply]
    split_ifs <;> norm_num
  obtain ⟨δ, hδ, hy⟩ := halfspace_one_sided_perturbation f h hx.1 hdir
  let F := tightFace f h {i | ∃ k, k ≠ j ∧ I k = i}
  have hF := tightFace_isExposed f h {i | ∃ k, k ≠ j ∧ I k = i}
  have hyF : x + δ • v ∈ F := by
    refine ⟨hy, ?_⟩
    rintro i ⟨k, hkj, rfl⟩
    rw [map_add, map_smul, hI, hv]
    simp [Pi.single_apply, hkj, Ne.symm hkj]
  have hystrict : f (I j) (x + δ • v) < h (I j) := by
    rw [map_add, map_smul, hI, hv]
    simp only [Pi.single_eq_same, neg_smul, one_smul, smul_eq_mul, mul_neg, mul_one]
    linarith
  have hface := exposedFace_eq_convexHull_vertices f h hc hF
  have hex : ∃ y ∈ F ∩ (halfspaceRegion f h).extremePoints ℝ,
      f (I j) y < h (I j) := by
    by_contra hno
    have hall : ∀ y ∈ F ∩ (halfspaceRegion f h).extremePoints ℝ,
        f (I j) y = h (I j) := by
      intro y hy
      have hle := hy.2.1 (I j)
      have hge : ¬f (I j) y < h (I j) := fun ht => hno ⟨y, hy, ht⟩
      exact le_antisymm hle (not_lt.mp hge)
    have hsub : convexHull ℝ (F ∩ (halfspaceRegion f h).extremePoints ℝ) ⊆
        {z | f (I j) z = h (I j)} := by
      apply convexHull_min hall
      exact convex_hyperplane (f (I j)).isLinear (h (I j))
    have hyHull : x + δ • v ∈ convexHull ℝ (F ∩ (halfspaceRegion f h).extremePoints ℝ) := by
      rw [← hface]
      exact hyF
    have hyeq := hsub hyHull
    exact (ne_of_lt hystrict) hyeq
  obtain ⟨y, hyF, hyt⟩ := hex
  exact ⟨y, hyF.2, (fun k hkj => hyF.1.2 _ ⟨k, hkj, rfl⟩), hyt⟩

theorem chosen_selected_iff (b c : Fin (n + 1) → Bool) (j : Fin (n + 1)) :
    Chosen c (selectedEmbedding b j) ↔ c j = b j := by
  cases hb : b j <;> simp [selectedEmbedding, Chosen, hb]

theorem vertex_change_bit
    (f : L n → V n →ₗ[ℝ] ℝ) (h : L n → ℝ)
    (hc : IsCompact (halfspaceRegion f h)) (hn : NoOppositeTight f h)
    {x : V n} (hx : x ∈ (halfspaceRegion f h).extremePoints ℝ)
    (b : Fin (n + 1) → Bool) (hb : ∀ i, f i x = h i ↔ Chosen b i)
    (j : Fin (n + 1)) (t : Bool) :
    ∃ y ∈ (halfspaceRegion f h).extremePoints ℝ,
      ∀ i, f i y = h i ↔ Chosen (Function.update b j t) i := by
  classical
  by_cases ht : t = b j
  · refine ⟨x, hx, ?_⟩
    simpa only [ht, Function.update_eq_self] using hb
  obtain ⟨y, hy, hrest, hdrop⟩ := vertex_releasing_one_label f h hc hn hx b hb j
  obtain ⟨c, hcpat⟩ := vertex_pattern f h hn hy
  have hcj : c j ≠ b j := by
    intro heq
    have hchosen := (chosen_selected_iff b c j).mpr heq
    exact (ne_of_lt hdrop) ((hcpat _).mpr hchosen)
  have hct : c j = t := by
    cases hj : b j <;> cases hct : c j <;> cases htt : t <;> simp_all
  have heq : c = Function.update b j t := by
    funext k
    by_cases hkj : k = j
    · subst k
      simpa using hct
    · rw [Function.update_of_ne hkj]
      exact (chosen_selected_iff b c k).mp ((hcpat _).mp (hrest k hkj))
  exact ⟨y, hy, heq ▸ hcpat⟩

theorem exists_vertex_of_pattern
    (f : L n → V n →ₗ[ℝ] ℝ) (h : L n → ℝ)
    (hc : IsCompact (halfspaceRegion f h)) (hne : (halfspaceRegion f h).Nonempty)
    (hn : NoOppositeTight f h) (b : Fin (n + 1) → Bool) :
    ∃ x ∈ (halfspaceRegion f h).extremePoints ℝ,
      ∀ i, f i x = h i ↔ Chosen b i := by
  classical
  have hpartial (S : Finset (Fin (n + 1))) :
      ∃ x ∈ (halfspaceRegion f h).extremePoints ℝ,
        ∃ c : Fin (n + 1) → Bool,
          (∀ i, f i x = h i ↔ Chosen c i) ∧ ∀ k ∈ S, c k = b k := by
    induction S using Finset.induction_on with
    | empty =>
        obtain ⟨x, hx⟩ := compact_halfspace_has_extremePoint f h hc hne
        obtain ⟨c, hc⟩ := vertex_pattern f h hn hx
        exact ⟨x, hx, c, hc, by simp⟩
    | @insert j S hj ih =>
        obtain ⟨x, hx, c, hcpat, hmatch⟩ := ih
        obtain ⟨y, hy, hypat⟩ := vertex_change_bit f h hc hn hx c hcpat j (b j)
        refine ⟨y, hy, Function.update c j (b j), hypat, ?_⟩
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · simp
        · have hkj : k ≠ j := fun he => hj (he ▸ hk)
          rw [Function.update_of_ne hkj]
          exact hmatch k hk
  obtain ⟨x, hx, c, hcpat, hmatch⟩ := hpartial Finset.univ
  have heq : c = b := funext (fun k => hmatch k (Finset.mem_univ k))
  exact ⟨x, hx, heq ▸ hcpat⟩

def patternVertex
    (f : L n → V n →ₗ[ℝ] ℝ) (h : L n → ℝ)
    (hc : IsCompact (halfspaceRegion f h)) (hne : (halfspaceRegion f h).Nonempty)
    (hn : NoOppositeTight f h) (b : Fin (n + 1) → Bool) :
    HalfspaceVertices f h :=
  ⟨(exists_vertex_of_pattern f h hc hne hn b).choose,
    (exists_vertex_of_pattern f h hc hne hn b).choose_spec.1⟩

theorem patternVertex_incidence
    (f : L n → V n →ₗ[ℝ] ℝ) (h : L n → ℝ)
    (hc : IsCompact (halfspaceRegion f h)) (hne : (halfspaceRegion f h).Nonempty)
    (hn : NoOppositeTight f h) (b : Fin (n + 1) → Bool) (i : L n) :
    f i (patternVertex f h hc hne hn b).val = h i ↔ Chosen b i :=
  (exists_vertex_of_pattern f h hc hne hn b).choose_spec.2 i

theorem vertex_unique_of_pattern
    (f : L n → V n →ₗ[ℝ] ℝ) (h : L n → ℝ)
    (hn : NoOppositeTight f h) {x y : V n}
    (hx : x ∈ (halfspaceRegion f h).extremePoints ℝ)
    (b : Fin (n + 1) → Bool)
    (hxb : ∀ i, Chosen b i → f i x = h i)
    (hyb : ∀ i, Chosen b i → f i y = h i) : x = y := by
  have hI (j : Fin (n + 1)) := hxb _ (selected_chosen b j)
  have hdet := (simple_active_minor_spans f h (simple_of_noOpposite f h hn)
    hx (selectedEmbedding b) hI).2
  exact tight_minor_unique f h (selectedEmbedding b) hdet hI
    (fun j => hyb _ (selected_chosen b j))

def patternVerticesEquiv
    (f : L n → V n →ₗ[ℝ] ℝ) (h : L n → ℝ)
    (hc : IsCompact (halfspaceRegion f h)) (hne : (halfspaceRegion f h).Nonempty)
    (hn : NoOppositeTight f h) :
    (Fin (n + 1) → Bool) ≃ HalfspaceVertices f h := by
  classical
  apply Equiv.ofBijective (patternVertex f h hc hne hn)
  constructor
  · intro b c he
    funext j
    have hi : b j = true ↔ c j = true := by
      change Chosen b (Sum.inr j) ↔ Chosen c (Sum.inr j)
      rw [← patternVertex_incidence f h hc hne hn b (Sum.inr j),
        ← patternVertex_incidence f h hc hne hn c (Sum.inr j), he]
    cases hb : b j <;> cases hc : c j <;> simp_all
  · intro x
    obtain ⟨b, hb⟩ := vertex_pattern f h hn x.property
    refine ⟨b, Subtype.ext ?_⟩
    exact vertex_unique_of_pattern f h hn
      (patternVertex f h hc hne hn b).property b
      (fun i hi => (patternVertex_incidence f h hc hne hn b i).mpr hi)
      (fun i hi => (hb i).mpr hi)

theorem strict_facets_of_noOpposite
    (f : L n → V n →ₗ[ℝ] ℝ) (h : L n → ℝ)
    (hc : IsCompact (halfspaceRegion f h)) (hne : (halfspaceRegion f h).Nonempty)
    (hn : NoOppositeTight f h) (i : L n) :
    ∃ x ∈ halfspaceRegion f h, f i x = h i ∧ ∀ j, j ≠ i → f j x < h j := by
  let F := tightFace f h {i}
  have hF := tightFace_isExposed f h {i}
  obtain ⟨b, hb⟩ := chosen_exists i
  let x := patternVertex f h hc hne hn b
  have hxF : x.val ∈ F :=
    ⟨x.property.1, by simpa using (patternVertex_incidence f h hc hne hn b i).mpr hb⟩
  obtain ⟨z, hzF, hz⟩ := exists_common_tight_point f h ⟨x.val, hxF⟩
    (hF.convex (convex_halfspaceRegion f h)) hF.subset
  refine ⟨z, hzF.1, hzF.2 i (Set.mem_singleton i), fun j hji => ?_⟩
  apply lt_of_le_of_ne (hzF.1 j)
  intro heq
  obtain ⟨c, hci, hcj⟩ := chosen_separates i j hji
  let y := patternVertex f h hc hne hn c
  have hyF : y.val ∈ F :=
    ⟨y.property.1, by simpa using (patternVertex_incidence f h hc hne hn c i).mpr hci⟩
  exact hcj ((patternVertex_incidence f h hc hne hn c j).mp ((hz j).mp heq y.val hyF))

def regularOfNoOpposite
    (p : HalfspaceData (L n) (V n))
    (hc : IsCompact (dataRegion p)) (hfull : (interior (dataRegion p)).Nonempty)
    (hn : NoOppositeTight (fun i => (p.1 i).toLinearMap) p.2) : RegularData (n + 1) (L n) where
  data := p
  compact := hc
  full_dimensional := hfull
  normal_ne_zero i := by
    obtain ⟨x, hx, hxi, hxs⟩ := strict_facets_of_noOpposite
      (fun i => (p.1 i).toLinearMap) p.2 hc (hfull.mono interior_subset) hn i
    obtain ⟨b, hb⟩ := chosen_exists i
    let c : Fin (n + 1) → Bool := fun j => !(b j)
    have hnot : ¬Chosen c i := by
      cases i with
      | inl j => simpa [Chosen, c, show b j = false from hb]
      | inr j => simpa [Chosen, c, show b j = true from hb]
    let y := patternVertex (fun i => (p.1 i).toLinearMap) p.2 hc
      (hfull.mono interior_subset) hn c
    have hstrict : p.1 i y.val < p.2 i := lt_of_le_of_ne (y.property.1 i)
      (fun he => hnot ((patternVertex_incidence (fun j => (p.1 j).toLinearMap) p.2 hc
        (hfull.mono interior_subset) hn c i).mp he))
    intro hf
    simp only [ContinuousLinearMap.coe_coe] at hxi
    simp only [hf, ContinuousLinearMap.zero_apply] at hxi hstrict
    linarith
  strict_facet_point := strict_facets_of_noOpposite
    (fun i => (p.1 i).toLinearMap) p.2 hc (hfull.mono interior_subset) hn

theorem cube_type_of_noOpposite
    (p : HalfspaceData (L n) (V n))
    (hc : IsCompact (dataRegion p)) (hfull : (interior (dataRegion p)).Nonempty)
    (hn : NoOppositeTight (fun i => (p.1 i).toLinearMap) p.2) :
    (referenceCube n).SameLabelledType (presentation (regularOfNoOpposite p hc hfull hn)) := by
  let f := fun i => ((cubeData n 0).1 i).toLinearMap
  let g := fun i => (p.1 i).toLinearMap
  let h := (cubeData n 0).2
  let k := p.2
  let e := (verticesEquiv (n := n) (ε := 0) le_rfl zero_lt_one).symm.trans
    (patternVerticesEquiv g k hc (hfull.mono interior_subset) hn)
  have hi : ∀ v : HalfspaceVertices f h, ∀ i,
      f i v.val = h i ↔ g i (e v).val = k i := by
    intro v i
    let b := (verticesEquiv (n := n) (ε := 0) le_rfl zero_lt_one).symm v
    have hleft := assignedVertex_incidence (n := n) (ε := 0) le_rfl zero_lt_one b i
    have hv : assignedVertex le_rfl zero_lt_one b = v.val := by
      simpa only [b, verticesEquiv_val] using
        congrArg Subtype.val ((verticesEquiv (n := n) (ε := 0) le_rfl zero_lt_one).apply_symm_apply v)
    rw [hv] at hleft
    exact hleft.trans (patternVertex_incidence g k hc (hfull.mono interior_subset) hn b i).symm
  apply sameLabelledType_of_faceOrderIso (cyclicRegular le_rfl zero_lt_one)
    (regularOfNoOpposite p hc hfull hn)
    (halfspaceFaceOrderIso f g h k (cubeRegion_compact (ε := 0) le_rfl) hc e hi)
  exact fun i => halfspaceFaceOrderIso_facet _ _ _ _ _ _ _ _ i

end NormalProjective.PairedHalfspaces
end

/- Source: NormalProjective/FiniteHullGeometry.lean -/
section
/-! # Finite convex combinations and radial enlargement

These are geometric statements about the ordinary convex hull, used by the
diagonal-concurrency construction. No desired PN relation occurs in their
hypotheses or definitions.
-/
open Set Filter
open scoped Topology BigOperators
namespace NormalProjective.FiniteHullGeometry
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_hull_iff_weights (v : ι → E) (x : E) :
    x ∈ convexHull ℝ (Set.range v) ↔
      ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • v i = x := by
  classical
  constructor
  · intro hx
    rw [convexHull_range_eq_exists_affineCombination] at hx
    obtain ⟨s, w, hw, hsum, hx⟩ := hx
    let W : ι → ℝ := fun i => if i ∈ s then w i else 0
    refine ⟨W, fun i => by dsimp [W]; split_ifs with hi; exact hw i hi; exact le_rfl, ?_, ?_⟩
    · simpa [W] using hsum
    · rw [← hx, Finset.affineCombination_eq_linear_combination s v w hsum]
      simp [W, ite_smul]
  · rintro ⟨w, hw, hsum, rfl⟩
    exact (convex_convexHull ℝ (Set.range v)).sum_mem
      (fun i _ => hw i) hsum (fun i _ => subset_convexHull ℝ _ ⟨i, rfl⟩)

theorem interior_has_positive_weights [Nonempty ι] (v : ι → E) {x : E}
    (hx : x ∈ interior (convexHull ℝ (Set.range v))) :
    ∃ w : ι → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • v i = x := by
  classical
  let N : ℝ := Fintype.card ι
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  let r : ℝ := N⁻¹
  have hr : 0 < r := inv_pos.mpr hN
  have hrsum : (∑ _ : ι, r) = 1 := by simp [r, N, ne_of_gt hN]
  let c : E := ∑ i, r • v i
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, x + t • (x - c) ∈ convexHull ℝ (Set.range v) := by
    have hc : Continuous (fun t : ℝ => x + t • (x - c)) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have htend : Tendsto (fun t : ℝ => x + t • (x - c)) (𝓝 0) (𝓝 x) := by
      simpa using hc.tendsto 0
    exact htend.eventually (show ∀ᶠ y in 𝓝 x, y ∈ convexHull ℝ (Set.range v) from
      mem_interior_iff_mem_nhds.mp hx)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let t : ℝ := ε / 2
  have ht : 0 < t := by dsimp [t]; linarith
  have hyt : x + t • (x - c) ∈ convexHull ℝ (Set.range v) := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]
    dsimp [t]
    linarith
  obtain ⟨a, ha, hasum, hax⟩ := (mem_hull_iff_weights v _).mp hyt
  let α := (1 + t)⁻¹
  let β := t / (1 + t)
  have ht1 : 0 < 1 + t := by linarith
  have hα : 0 < α := inv_pos.mpr ht1
  have hβ : 0 < β := div_pos ht ht1
  have hsum : α + β = 1 := by dsimp [α, β]; field_simp <;> ring
  have hαt : α * t = β := by dsimp [α, β]; ring
  refine ⟨fun i => α * a i + β * r, fun i =>
    add_pos_of_nonneg_of_pos (mul_nonneg hα.le (ha i)) (mul_pos hβ hr), ?_, ?_⟩
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, hasum, mul_one,
      ← Finset.mul_sum, hrsum, mul_one]
    exact hsum
  · have hcombine : (∑ i, (α * a i + β * r) • v i) =
        α • (∑ i, a i • v i) + β • c := by
      simp only [c, add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
    rw [hcombine, hax]
    rw [smul_add, smul_smul, hαt, smul_sub]
    calc
      α • x + (β • x - β • c) + β • c = (α + β) • x := by
        rw [add_smul]
        abel
      _ = x := by rw [hsum, one_smul]

theorem zero_mem_radial_hull (v : ι → E) (γ : ι → ℝ) (hγ : ∀ i, 0 < γ i)
    (hzero : (0 : E) ∈ convexHull ℝ (Set.range v)) :
    (0 : E) ∈ convexHull ℝ (Set.range (fun i => γ i • v i)) := by
  classical
  obtain ⟨a, ha, hasum, hazero⟩ := (mem_hull_iff_weights v 0).mp hzero
  have hex : ∃ i, 0 < a i := by
    by_contra hn
    have hz : ∀ i, a i = 0 := fun i => le_antisymm (not_lt.mp (fun hi => hn ⟨i, hi⟩)) (ha i)
    simp [hz] at hasum
  let S : ℝ := ∑ i, a i / γ i
  have hS : 0 < S := by
    obtain ⟨i, hi⟩ := hex
    exact Finset.sum_pos' (fun j _ => div_nonneg (ha j) (hγ j).le)
      ⟨i, Finset.mem_univ i, div_pos hi (hγ i)⟩
  apply (mem_hull_iff_weights (fun i => γ i • v i) 0).mpr
  refine ⟨fun i => (a i / γ i) / S, fun i => div_nonneg
    (div_nonneg (ha i) (hγ i).le) hS.le, ?_, ?_⟩
  · rw [← Finset.sum_div]
    exact div_self (ne_of_gt hS)
  · have hterm (i : ι) : ((a i / γ i) / S) • (γ i • v i) = S⁻¹ • (a i • v i) := by
      rw [smul_smul, smul_smul]
      congr 1
      field_simp [ne_of_gt (hγ i), ne_of_gt hS]
    simp only [hterm, ← Finset.smul_sum, hazero, smul_zero]

theorem hull_subset_radial_hull (v : ι → E) (γ : ι → ℝ) (hγ : ∀ i, 1 ≤ γ i)
    (hzero : (0 : E) ∈ convexHull ℝ (Set.range v)) :
    convexHull ℝ (Set.range v) ⊆ convexHull ℝ (Set.range (fun i => γ i • v i)) := by
  have hγpos : ∀ i, 0 < γ i := fun i => lt_of_lt_of_le zero_lt_one (hγ i)
  have hz := zero_mem_radial_hull v γ hγpos hzero
  apply convexHull_min _ (convex_convexHull ℝ _)
  rintro _ ⟨i, rfl⟩
  have hinv : 0 ≤ (γ i)⁻¹ := (inv_pos.mpr (hγpos i)).le
  have hinvle : (γ i)⁻¹ ≤ 1 := (inv_le_one₀ (hγpos i)).mpr (hγ i)
  have hh := (convex_convexHull ℝ (Set.range (fun i => γ i • v i)))
    (subset_convexHull ℝ _ (Set.mem_range_self i)) hz hinv (sub_nonneg.mpr hinvle)
    (show (γ i)⁻¹ + (1 - (γ i)⁻¹) = 1 by ring)
  simpa only [smul_zero, add_zero, smul_smul, inv_mul_cancel₀ (ne_of_gt (hγpos i)),
    one_smul] using hh

end NormalProjective.FiniteHullGeometry
end

/- Source: NormalProjective/NormalHull.lean -/
section
/-! # The finite convex hull of normalized facet normals

The cube construction only needs this finite hull and the displayed primal
inequalities. These lemmas prove the required interior and admissibility facts
directly, without treating an unproved polar face-duality theorem as a premise.
-/
open Set Matrix
open scoped BigOperators
namespace NormalProjective.NormalHull
open UnitNormalization CanonicalModel RootedGeometry CyclicCube
variable {d : ℕ} {ι : Type*} [Fintype ι]

def hull (v : ι → CanonicalModel.Space d) : Set (CanonicalModel.Space d) :=
  convexHull ℝ (Set.range v)

def primal (v : ι → CanonicalModel.Space d) : Set (CanonicalModel.Space d) :=
  dataRegion (fun i => rowForm (v i), fun _ => 1)

theorem dot_comm (x y : CanonicalModel.Space d) : dot x y = dot y x := by
  simp only [dot, mul_comm]

theorem coefficients_pairing (u : CanonicalModel.Space d →L[ℝ] ℝ)
    (v : CanonicalModel.Space d) : dot v (coefficients u) = u v := by
  rw [dot_comm]
  exact coefficient_expansion u v

theorem coefficients_nonzero (u : CanonicalModel.Space d →L[ℝ] ℝ) (hu : u ≠ 0) :
    coefficients u ≠ 0 := by
  intro hz
  apply hu
  apply ContinuousLinearMap.ext
  intro x
  rw [← coefficient_expansion, hz]
  simp

theorem functional_norm_bound (u : CanonicalModel.Space d →L[ℝ] ℝ)
    (x : CanonicalModel.Space d) :
    u x ≤ (d : ℝ) * ‖coefficients u‖ * ‖x‖ := by
  rw [← coefficient_expansion]
  calc
    (∑ j, coefficients u j * x j) ≤ ∑ j, |coefficients u j| * |x j| := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [abs_mul] using le_abs_self (coefficients u j * x j)
    _ ≤ ∑ _ : Fin d, ‖coefficients u‖ * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (coefficients u) j)
        (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j)
        (abs_nonneg _) (norm_nonneg _)
    _ = (d : ℝ) * ‖coefficients u‖ * ‖x‖ := by simp [mul_assoc]

theorem zero_interior_of_primal_bounded [Nonempty ι] (hd : 0 < d)
    (v : ι → CanonicalModel.Space d) (hb : Bornology.IsBounded (primal v)) :
    (0 : CanonicalModel.Space d) ∈ interior (hull v) := by
  classical
  obtain ⟨c, hc, hsep⟩ := bounded_normals_separate_directions (fun i => rowForm (v i)) hb
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hr : 0 < c / (d : ℝ) := div_pos hc hdR
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (Metric.ball_mem_nhds _ hr)
  intro y hy
  by_contra hno
  obtain ⟨u, a, huK, hay⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (Set.range v)) ((Set.finite_range v).isClosed_convexHull ℝ) hno
  have hu : u ≠ 0 := by
    intro he
    have hh := huK (v (Classical.arbitrary ι)) (subset_convexHull ℝ _ (Set.mem_range_self _))
    simp only [he, ContinuousLinearMap.zero_apply] at hh hay
    linarith
  let w := coefficients u
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr (coefficients_nonzero u hu)
  have hwunit : ‖‖w‖⁻¹ • w‖ = 1 := by
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hwn), ne_of_gt hwn]
  obtain ⟨i, hi⟩ := hsep (‖w‖⁻¹ • w) hwunit
  have hival : c * ‖w‖ < u (v i) := by
    have hpair : rowForm (v i) w = u (v i) := by
      rw [rowForm_apply]
      exact coefficients_pairing u (v i)
    rw [map_smul, smul_eq_mul, hpair] at hi
    calc
      c * ‖w‖ < (‖w‖⁻¹ * u (v i)) * ‖w‖ := mul_lt_mul_of_pos_right hi hwn
      _ = u (v i) := by rw [mul_right_comm, inv_mul_cancel₀ (ne_of_gt hwn), one_mul]
  have hyNorm : ‖y‖ < c / (d : ℝ) := by simpa only [Metric.mem_ball, dist_zero_right] using hy
  have hyMul : (d : ℝ) * ‖y‖ < c := by
    simpa only [mul_comm] using (lt_div_iff₀ hdR).mp hyNorm
  have hbound := functional_norm_bound u y
  have hsmall : u y < c * ‖w‖ := by
    have hh := mul_lt_mul_of_pos_right hyMul hwn
    dsimp only [w] at hh ⊢
    nlinarith
  have hii := huK (v i) (subset_convexHull ℝ _ (Set.mem_range_self i))
  linarith

theorem primal_iff_hull (v : ι → CanonicalModel.Space d) (x : CanonicalModel.Space d) :
    x ∈ primal v ↔ ∀ y ∈ hull v, dot y x ≤ 1 := by
  constructor
  · intro hx
    have hraw : ∀ i, rowForm (v i) x ≤ 1 := hx
    have hsub : hull v ⊆ {y | rowForm x y ≤ 1} := by
      apply convexHull_min
      · rintro _ ⟨i, rfl⟩
        change rowForm x (v i) ≤ 1
        rw [rowForm_apply, dot_comm]
        simpa only [rowForm_apply] using hraw i
      · exact convex_halfSpace_le (rowForm x).toLinearMap.isLinear 1
    intro y hy
    have hh : rowForm x y ≤ 1 := hsub hy
    simpa only [rowForm_apply, dot_comm] using hh
  · intro hx i
    change rowForm (v i) x ≤ 1
    rw [rowForm_apply]
    exact hx (v i) (subset_convexHull ℝ _ (Set.mem_range_self i))

theorem primal_compact_of_zero_interior (v : ι → CanonicalModel.Space d)
    (hz : (0 : CanonicalModel.Space d) ∈ interior (hull v)) : IsCompact (primal v) := by
  classical
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz)
  have hb : Bornology.IsBounded (primal v) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨2 / r, fun x hx => ?_⟩
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 / r)).mpr
    intro j
    have ht : 0 < r / 2 := by linarith
    have hplus : (Pi.single j (r / 2) : CanonicalModel.Space d) ∈ hull v := by
      apply hball
      rw [Metric.mem_ball, dist_zero_right, Pi.norm_single, Real.norm_eq_abs, abs_of_pos ht]
      linarith
    have hminus : (Pi.single j (-(r / 2)) : CanonicalModel.Space d) ∈ hull v := by
      apply hball
      rw [Metric.mem_ball, dist_zero_right, Pi.norm_single, Real.norm_eq_abs, abs_neg, abs_of_pos ht]
      linarith
    have h₁ := (primal_iff_hull v x).mp hx _ hplus
    have h₂ := (primal_iff_hull v x).mp hx _ hminus
    simp only [dot, Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h₁ h₂
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have hn : -x j ≤ 2 / r := by
        apply (le_div_iff₀ hr).mpr
        nlinarith
      linarith
    · apply (le_div_iff₀ hr).mpr
      nlinarith
  exact Metric.isCompact_of_isClosed_isBounded (dataRegion_closed _) hb

theorem primal_zero_interior (v : ι → CanonicalModel.Space d) :
    (0 : CanonicalModel.Space d) ∈ interior (primal v) := by
  apply strict_mem_dataRegion_interior
  intro i
  simp [rowForm_apply, dot]

theorem interior_center_denominator (v : ι → CanonicalModel.Space d)
    {O : CanonicalModel.Space d} (hO : O ∈ interior (hull v))
    {x : CanonicalModel.Space d} (hx : x ∈ primal v) : 0 < 1 - dot O x := by
  by_cases hx0 : x = 0
  · simp [hx0, dot]
  have hrow : rowForm x ≠ 0 := by
    intro he
    have hh := congrArg coefficients he
    exact hx0 (by simpa only [coefficients_rowForm, coefficients_zero] using hh)
  have hh := interior_lt_support (hull v) (rowForm x) hrow 1
    (fun y hy => by simpa only [rowForm_apply, dot_comm] using (primal_iff_hull v x).mp hx y hy) hO
  rw [rowForm_apply, dot_comm] at hh
  linarith

theorem open_pair_interior {n : ℕ} (v : Labels (n + 1) → CanonicalModel.Space (n + 1))
    (hz : (0 : CanonicalModel.Space (n + 1)) ∈ interior (hull v))
    (hn : PairedHalfspaces.NoOppositeTight (fun i => (rowForm (v i)).toLinearMap) (fun _ => 1))
    (i : Fin (n + 1)) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    (1 - t) • v (Sum.inl i) + t • v (Sum.inr i) ∈ interior (hull v) := by
  let z := (1 - t) • v (Sum.inl i) + t • v (Sum.inr i)
  by_contra hno
  obtain ⟨u, hu, hmax⟩ := geometric_hahn_banach_of_nonempty_interior_point
    (convex_convexHull ℝ (Set.range v)) hno ⟨0, hz⟩
  have hpos : 0 < u z := by
    have hh := interior_lt_support (hull v) u hu (u z) hmax hz
    simpa only [map_zero] using hh
  have hl := hmax (v (Sum.inl i)) (subset_convexHull ℝ _ (Set.mem_range_self _))
  have hr := hmax (v (Sum.inr i)) (subset_convexHull ℝ _ (Set.mem_range_self _))
  have hzval : u z = (1 - t) * u (v (Sum.inl i)) + t * u (v (Sum.inr i)) := by
    simp only [z, map_add, map_smul, smul_eq_mul]
  have hlEq : u (v (Sum.inl i)) = u z := by nlinarith
  have hrEq : u (v (Sum.inr i)) = u z := by nlinarith
  let x := (u z)⁻¹ • coefficients u
  have hx : x ∈ primal v := by
    intro j
    change rowForm (v j) ((u z)⁻¹ • coefficients u) ≤ 1
    rw [map_smul, smul_eq_mul, rowForm_apply, coefficients_pairing]
    apply (inv_mul_le_iff₀ hpos).mpr
    simpa only [mul_one] using
      (hmax (v j) (subset_convexHull ℝ _ (Set.mem_range_self j)))
  apply hn x hx i
  constructor
  · change rowForm (v (Sum.inl i)) ((u z)⁻¹ • coefficients u) = 1
    rw [map_smul, smul_eq_mul, rowForm_apply, coefficients_pairing, hlEq,
      inv_mul_cancel₀ (ne_of_gt hpos)]
  · change rowForm (v (Sum.inr i)) ((u z)⁻¹ • coefficients u) = 1
    rw [map_smul, smul_eq_mul, rowForm_apply, coefficients_pairing, hrEq,
      inv_mul_cancel₀ (ne_of_gt hpos)]

theorem noOpposite_of_pair_sites {n : ℕ}
    (v : Labels (n + 1) → CanonicalModel.Space (n + 1))
    (hsites : ∀ i, ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      (1 - t) • v (Sum.inl i) + t • v (Sum.inr i) ∈ interior (hull v)) :
    PairedHalfspaces.NoOppositeTight (fun i => (rowForm (v i)).toLinearMap) (fun _ => 1) := by
  intro x hx i hboth
  obtain ⟨t, ht, ht1, hsite⟩ := hsites i
  have hx0 : x ≠ 0 := by
    intro he
    have hl := hboth.1
    simp only [he, map_zero] at hl
    norm_num at hl
  have hrow : rowForm x ≠ 0 := by
    intro he
    have hh := congrArg coefficients he
    exact hx0 (by simpa only [coefficients_rowForm, coefficients_zero] using hh)
  have hvalid : ∀ y ∈ hull v, rowForm x y ≤ 1 := by
    intro y hy
    simpa only [rowForm_apply, dot_comm] using (primal_iff_hull v x).mp hx y hy
  have hh := interior_lt_support (hull v) (rowForm x) hrow 1 hvalid hsite
  have hlo : rowForm x (v (Sum.inl i)) = 1 := by
    have hh : rowForm (v (Sum.inl i)) x = 1 := hboth.1
    simpa only [rowForm_apply, dot_comm] using hh
  have hup : rowForm x (v (Sum.inr i)) = 1 := by
    have hh : rowForm (v (Sum.inr i)) x = 1 := hboth.2
    simpa only [rowForm_apply, dot_comm] using hh
  simp only [map_add, map_smul, smul_eq_mul, hlo, hup, mul_one] at hh
  linarith

theorem cube_noOpposite {n : ℕ} (p : RegularData (n + 1) (Labels (n + 1)))
    (hp : (referenceCube n).SameLabelledType (presentation p)) :
    PairedHalfspaces.NoOppositeTight (fun i => (p.data.1 i).toLinearMap) p.data.2 := by
  classical
  let r := cyclicRegular (n := n) (ε := 0) le_rfl zero_lt_one
  let f := fun i => (r.data.1 i).toLinearMap
  let g := fun i => (p.data.1 i).toLinearMap
  obtain ⟨e, he⟩ := sameLabelledType_raw r p hp
  let ev := faceIsoVertexEquiv f g r.data.2 p.data.2 r.compact p.compact e
  intro x hx i hboth
  let F := tightFace g p.data.2 {Sum.inl i, Sum.inr i}
  have hF := tightFace_isExposed g p.data.2 {Sum.inl i, Sum.inr i}
  have hxF : x ∈ F := by
    refine ⟨hx, ?_⟩
    intro j hj
    rcases Set.mem_insert_iff.mp hj with rfl | hj
    · exact hboth.1
    · have heq := Set.mem_singleton_iff.mp hj
      simpa only [heq] using hboth.2
  obtain ⟨y, hy⟩ := (hF.isCompact p.compact).extremePoints_nonempty ⟨x, hxF⟩
  let Y : HalfspaceVertices g p.data.2 :=
    ⟨y, hF.isExtreme.extremePoints_subset_extremePoints hy⟩
  let X := ev.symm Y
  have hinc := faceIsoVertexEquiv_incidence f g r.data.2 p.data.2 r.compact p.compact e he X
  have hXY : ev X = Y := ev.apply_symm_apply Y
  have hl : f (Sum.inl i) X.val = r.data.2 (Sum.inl i) := by
    apply (hinc (Sum.inl i)).mpr
    rw [hXY]
    exact hy.1.2 _ (Set.mem_insert _ _)
  have hr : f (Sum.inr i) X.val = r.data.2 (Sum.inr i) := by
    apply (hinc (Sum.inr i)).mpr
    rw [hXY]
    exact hy.1.2 _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  exact opposite_not_both_tight (n := n) (ε := 0) le_rfl zero_lt_one X.property.1 i ⟨hl, hr⟩

end NormalProjective.NormalHull
end

/- Source: NormalProjective/DiagonalSites.lean -/
section
/-! # Positive relations among the actual open opposite diagonals -/
open Set
open scoped BigOperators
namespace NormalProjective.DiagonalSites
open UnitNormalization CanonicalModel RootedGeometry CyclicCube NormalHull FiniteHullGeometry
variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem midpoint_weight_lt_half
    (v : ι → CanonicalModel.Space d) (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hasum : ∑ i, a i = 1)
    (p q r : ι) (hpq : p ≠ q) (hrp : r ≠ p) (hrq : r ≠ q)
    (havg : ∑ i, a i • v i = (1 / 2 : ℝ) • v p + (1 / 2 : ℝ) • v q)
    (u : CanonicalModel.Space d →L[ℝ] ℝ)
    (huq : u (v q) = 1) (hu : ∀ i, i ≠ q → u (v i) < 1) : a p < 1 / 2 := by
  classical
  let b : ι → ℝ := fun i => a i * (1 - u (v i))
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    by_cases hi : i = q
    · simp [b, hi, huq]
    · exact mul_nonneg (ha i).le (sub_pos.mpr (hu i hi)).le
  have hr : 0 < b r := mul_pos (ha r) (sub_pos.mpr (hu r hrq))
  have hrest : 0 < ∑ i ∈ Finset.univ.erase p, b i :=
    Finset.sum_pos' (fun i _ => hb i) ⟨r, by simp [hrp], hr⟩
  have hpsum : b p < ∑ i, b i := by
    have hh := Finset.sum_erase_add (s := Finset.univ) b (Finset.mem_univ p)
    linarith
  have hsum : ∑ i, b i = (1 - u (v p)) / 2 := by
    have hh := congrArg u havg
    simp only [map_sum, map_smul, map_add, smul_eq_mul, huq] at hh
    simp only [b, mul_sub, mul_one, Finset.sum_sub_distrib, hasum]
    linarith
  rw [hsum] at hpsum
  have hgap : 0 < 1 - u (v p) := sub_pos.mpr (hu p hpq)
  apply lt_of_not_ge
  intro hlarge
  have hh := mul_le_mul_of_nonneg_right hlarge hgap.le
  dsimp only [b] at hpsum
  nlinarith

structure Sites {n : ℕ}
    (v : Labels (n + 1) → CanonicalModel.Space (n + 1)) where
  value : Fin (n + 1) → CanonicalModel.Space (n + 1)
  parameter : Fin (n + 1) → ℝ
  parameter_pos : ∀ i, 0 < parameter i
  parameter_lt_one : ∀ i, parameter i < 1
  value_eq : ∀ i, value i = (1 - parameter i) • v (Sum.inl i) + parameter i • v (Sum.inr i)
  interior : ∀ i, value i ∈ interior (NormalHull.hull v)

structure GroupState {n : ℕ}
    (v : Labels (n + 1) → CanonicalModel.Space (n + 1)) (G : Finset (Fin (n + 1))) where
  sites : Sites v
  common : CanonicalModel.Space (n + 1)
  common_eq : ∀ i ∈ G, sites.value i = common
  weights : Fin (n + 1) → ℝ
  weights_pos : ∀ i ∉ G, 0 < weights i
  weights_sum : ∑ i ∈ Finset.univ \ G, weights i = 1
  positive_average : ∑ i ∈ Finset.univ \ G, weights i • sites.value i = common

theorem initial_group {n : ℕ} (hn : 1 ≤ n)
    (v : Labels (n + 1) → CanonicalModel.Space (n + 1))
    (hz : (0 : CanonicalModel.Space (n + 1)) ∈ interior (NormalHull.hull v))
    (hopp : PairedHalfspaces.NoOppositeTight (fun i => (rowForm (v i)).toLinearMap) (fun _ => 1))
    (hexposed : ∀ l : Labels (n + 1), ∃ u : CanonicalModel.Space (n + 1) →L[ℝ] ℝ,
      u (v l) = 1 ∧ ∀ k, k ≠ l → u (v k) < 1) :
    Nonempty (GroupState v {0}) := by
  classical
  let z : CanonicalModel.Space (n + 1) :=
    (1 / 2 : ℝ) • v (Sum.inl 0) + (1 / 2 : ℝ) • v (Sum.inr 0)
  have hzi : z ∈ interior (NormalHull.hull v) := by
    dsimp only [z]
    convert open_pair_interior v hz hopp 0
      (t := 1 / 2) (by norm_num) (by norm_num) using 1 <;> norm_num
  obtain ⟨a, ha, hasum, havg⟩ := interior_has_positive_weights v hzi
  let j : Fin (n + 1) := ⟨1, by omega⟩
  have hj0 : j ≠ 0 := by intro he; have := congrArg Fin.val he; norm_num [j] at this
  obtain ⟨ulo, hulo, hulos⟩ := hexposed (Sum.inl 0)
  obtain ⟨uhi, huhi, huhis⟩ := hexposed (Sum.inr 0)
  have haLo : a (Sum.inl 0) < 1 / 2 :=
    midpoint_weight_lt_half v a ha hasum (Sum.inl 0) (Sum.inr 0) (Sum.inl j)
      (by simp) (by simpa using hj0) (by simp) havg uhi huhi huhis
  have havg' : ∑ i, a i • v i = (1 / 2 : ℝ) • v (Sum.inr 0) + (1 / 2 : ℝ) • v (Sum.inl 0) := by
    rw [havg]
    exact add_comm _ _
  have haHi : a (Sum.inr 0) < 1 / 2 :=
    midpoint_weight_lt_half v a ha hasum (Sum.inr 0) (Sum.inl 0) (Sum.inr j)
      (by simp) (by simpa using hj0) (by simp) havg' ulo hulo hulos
  let b : Fin (n + 1) → ℝ := fun i => a (Sum.inl i) + a (Sum.inr i)
  have hb : ∀ i, 0 < b i := fun i => add_pos (ha _) (ha _)
  let B : ℝ := 1 - b 0
  have hB : 0 < B := by dsimp [B, b]; linarith
  let t : Fin (n + 1) → ℝ := fun i =>
    if i = 0 then (1 / 2 - a (Sum.inr 0)) / B else a (Sum.inr i) / b i
  have ht : ∀ i, 0 < t i := by
    intro i
    dsimp [t]
    split_ifs
    · exact div_pos (sub_pos.mpr haHi) hB
    · exact div_pos (ha _) (hb i)
  have ht1 : ∀ i, t i < 1 := by
    intro i
    dsimp [t]
    split_ifs
    · apply (div_lt_one hB).mpr
      dsimp [B, b]
      linarith
    · apply (div_lt_one (hb i)).mpr
      dsimp [b]
      linarith [ha (Sum.inl i)]
  let s : Fin (n + 1) → CanonicalModel.Space (n + 1) :=
    fun i => (1 - t i) • v (Sum.inl i) + t i • v (Sum.inr i)
  have hsi : ∀ i, s i ∈ interior (NormalHull.hull v) :=
    fun i => open_pair_interior v hz hopp i (ht i) (ht1 i)
  have hbsum : ∑ i, b i = 1 := by
    simpa only [b, Finset.sum_add_distrib, Fintype.sum_sum_type] using hasum
  let S := Finset.univ.erase (0 : Fin (n + 1))
  have hSsum : ∑ i ∈ S, b i = B := by
    have hh := Finset.sum_erase_add (s := Finset.univ) b (Finset.mem_univ (0 : Fin (n + 1)))
    rw [hbsum] at hh
    dsimp [S, B]
    linarith
  have hterm (i : Fin (n + 1)) (hi : i ≠ 0) :
      b i • s i = a (Sum.inl i) • v (Sum.inl i) + a (Sum.inr i) • v (Sum.inr i) := by
    simp only [s, t, hi, if_false]
    rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ (ne_of_gt (hb i))]
    have hlo : b i * (1 - a (Sum.inr i) / b i) = a (Sum.inl i) := by
      rw [mul_sub, mul_one, mul_div_cancel₀ _ (ne_of_gt (hb i))]
      dsimp [b]
      ring
    rw [hlo]
  have hroot : B • s 0 =
      (1 / 2 - a (Sum.inl 0)) • v (Sum.inl 0) +
        (1 / 2 - a (Sum.inr 0)) • v (Sum.inr 0) := by
    simp only [s, t, if_pos rfl, ite_true]
    rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ (ne_of_gt hB)]
    have hlo : B * (1 - (1 / 2 - a (Sum.inr 0)) / B) = 1 / 2 - a (Sum.inl 0) := by
      rw [mul_sub, mul_one, mul_div_cancel₀ _ (ne_of_gt hB)]
      dsimp [B, b]
      ring
    rw [hlo]
  have hSvec : ∑ i ∈ S, b i • s i = B • s 0 := by
    rw [hroot]
    have hh := Finset.sum_erase_add (s := Finset.univ)
      (fun i : Fin (n + 1) => a (Sum.inl i) • v (Sum.inl i) + a (Sum.inr i) • v (Sum.inr i))
      (Finset.mem_univ (0 : Fin (n + 1)))
    have hsumvec : (∑ i : Fin (n + 1),
        (a (Sum.inl i) • v (Sum.inl i) + a (Sum.inr i) • v (Sum.inr i))) = z := by
      simpa only [Finset.sum_add_distrib, Fintype.sum_sum_type] using havg
    rw [hsumvec] at hh
    have hreplace : (∑ i ∈ S, b i • s i) =
        ∑ i ∈ S, (a (Sum.inl i) • v (Sum.inl i) + a (Sum.inr i) • v (Sum.inr i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hterm i (Finset.mem_erase.mp hi).1
    rw [hreplace]
    ext k
    have hk := congrFun hh k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hk ⊢
    dsimp only [z] at hk
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hk
    linarith
  refine ⟨{
    sites := {
      value := s
      parameter := t
      parameter_pos := ht
      parameter_lt_one := ht1
      value_eq := fun _ => rfl
      interior := hsi }
    common := s 0
    common_eq := by intro i hi; simpa only [Finset.mem_singleton.mp hi]
    weights := fun i => b i / B
    weights_pos := fun i _ => div_pos (hb i) hB
    weights_sum := ?_
    positive_average := ?_ }⟩
  · change (∑ i ∈ Finset.univ \ {0}, b i / B) = 1
    rw [Finset.sdiff_singleton_eq_erase, ← Finset.sum_div, hSsum]
    exact div_self (ne_of_gt hB)
  · change (∑ i ∈ Finset.univ \ {0}, (b i / B) • s i) = s 0
    rw [Finset.sdiff_singleton_eq_erase]
    simp only [div_eq_inv_mul, mul_smul, ← Finset.smul_sum]
    rw [hSvec, smul_smul, inv_mul_cancel₀ (ne_of_gt hB), one_smul]

end NormalProjective.DiagonalSites
end

/- Source: NormalProjective/DiagonalMerge.lean -/
section
/-! # One admissible PN step merges one more opposite diagonal -/
open Set Filter
open scoped BigOperators Topology
namespace NormalProjective.DiagonalSites
open UnitNormalization CanonicalModel RootedGeometry CyclicCube NormalHull FiniteHullGeometry
variable {n : ℕ}
abbrev E (n : ℕ) := CanonicalModel.Space (n + 1)
abbrev L (n : ℕ) := Labels (n + 1)

theorem exists_center_beyond (K : Set (E n)) {z s : E n} (hs : s ∈ interior K) :
    ∃ t : ℝ, 1 < t ∧ z + t • (s - z) ∈ interior K := by
  have hc : Continuous (fun t : ℝ => z + t • (s - z)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hnear : ∀ᶠ t : ℝ in 𝓝 1, z + t • (s - z) ∈ interior K := by
    have htend : Tendsto (fun t : ℝ => z + t • (s - z)) (𝓝 1) (𝓝 s) := by
      simpa only [one_smul, add_sub_cancel] using hc.tendsto 1
    exact htend.eventually (show ∀ᶠ y in 𝓝 s, y ∈ interior K from
      isOpen_interior.mem_nhds hs)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have ht : 1 < 1 + ε / 2 := by linarith
  refine ⟨1 + ε / 2, ht, hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq]
  have habs : |1 + ε / 2 - 1| = ε / 2 := by
    rw [abs_of_pos (by linarith : 0 < 1 + ε / 2 - 1)]
    ring
  rw [habs]
  linarith

theorem hull_translation (v : L n → E n) (O : E n) :
    NormalHull.hull (fun i => v i - O) = (fun x : E n => x - O) '' NormalHull.hull v := by
  let a := AffineEquiv.constVAdd ℝ (E n) (-O)
  have hh := a.toAffineMap.image_convexHull (Set.range v)
  have hr : a.toAffineMap '' Set.range v = Set.range (fun i => v i - O) := by
    rw [← Set.range_comp']
    congr 1
    funext i
    simp [a, sub_eq_add_neg, add_comm]
  rw [hr] at hh
  change convexHull ℝ (Set.range (fun i => v i - O)) =
    (fun x : E n => x - O) '' convexHull ℝ (Set.range v)
  rw [← hh]
  congr 1
  funext x
  simp [a, sub_eq_add_neg, add_comm]

theorem interior_translation (v : L n → E n) (O : E n) {x : E n}
    (hx : x ∈ interior (NormalHull.hull v)) :
    x - O ∈ interior (NormalHull.hull (fun i => v i - O)) := by
  rw [hull_translation]
  let a := AffineEquiv.constVAdd ℝ (E n) (-O)
  have ha := a.toHomeomorphOfFiniteDimensional.image_interior (NormalHull.hull v)
  have hh : a.toHomeomorphOfFiniteDimensional x ∈
      a.toHomeomorphOfFiniteDimensional '' interior (NormalHull.hull v) := ⟨x, hx, rfl⟩
  rw [ha] at hh
  have he : (a : E n → E n) = fun y => y - O := by
    funext y
    simp [a, sub_eq_add_neg, add_comm]
  simpa only [AffineEquiv.coe_toHomeomorphOfFiniteDimensional, he] using hh

theorem merge_algebra {s z sj : E n} {lam t : ℝ}
    (hs : s = (1 - lam) • z + lam • sj)
    (htlam : t - lam ≠ 0) (ht1 : t - 1 ≠ 0) :
    let O := z + t • (sj - z)
    (t / (t - lam)) • (s - O) = z - O ∧
      (t / (t - 1)) • (sj - O) = z - O := by
  dsimp only
  constructor
  · rw [hs]
    ext k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [htlam] <;> ring
  · ext k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [ht1] <;> ring

/-- Splitting a strictly positive finite average isolates one coefficient strictly
between zero and one, and leaves a strictly positive normalized average. -/
theorem split_positive_average
    (G : Finset (Fin (n + 1))) (w : Fin (n + 1) → ℝ) (s : Fin (n + 1) → E n)
    (hw : ∀ i ∉ G, 0 < w i) (hsum : ∑ i ∈ Finset.univ \ G, w i = 1)
    (j : Fin (n + 1)) (hj : j ∉ G) (hk : ∃ k, k ∉ G ∧ k ≠ j) :
    0 < w j ∧ w j < 1 ∧
      (∑ i ∈ Finset.univ \ insert j G, w i) = 1 - w j ∧
      (∑ i ∈ Finset.univ \ G, w i • s i) =
        (1 - w j) • ((1 - w j)⁻¹ • ∑ i ∈ Finset.univ \ insert j G, w i • s i) +
          w j • s j := by
  classical
  let S := Finset.univ \ G
  have hjS : j ∈ S := by simp [S, hj]
  have hrest : S.erase j = Finset.univ \ insert j G := by
    ext i
    simp [S, and_comm, and_left_comm]
  have hrestpos : 0 < ∑ i ∈ S.erase j, w i := by
    obtain ⟨k, hkG, hkj⟩ := hk
    apply Finset.sum_pos'
    · intro i hi
      exact (hw i (by simpa [S] using (Finset.mem_erase.mp hi).2)).le
    · exact ⟨k, by simp [S, hkG, hkj], hw k hkG⟩
  have hscalar := Finset.sum_erase_add (s := S) w hjS
  have hSsum : ∑ i ∈ S, w i = 1 := hsum
  have hwj : w j < 1 := by rw [hSsum] at hscalar; linarith
  refine ⟨hw j hj, hwj, ?_, ?_⟩
  · rw [← hrest]
    linarith
  · rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr hwj)), one_smul,
      ← hrest]
    exact (Finset.sum_erase_add (s := S) (fun i => w i • s i) hjS).symm

theorem weighted_average_interior
    (v : L n → E n) (S : Finset (Fin (n + 1))) (w : Fin (n + 1) → ℝ)
    (s : Fin (n + 1) → E n) (hw : ∀ i ∈ S, 0 ≤ w i)
    (hsum : ∑ i ∈ S, w i = 1)
    (hs : ∀ i ∈ S, s i ∈ interior (NormalHull.hull v)) :
    (∑ i ∈ S, w i • s i) ∈ interior (NormalHull.hull v) :=
  (convex_convexHull ℝ (Set.range v)).interior.sum_mem hw hsum hs

theorem merge_sites
    (v : L n → E n) (G : Finset (Fin (n + 1))) (st : GroupState v G)
    (j : Fin (n + 1)) (hj : j ∉ G) (hk : ∃ k, k ∉ G ∧ k ≠ j) :
    ∃ (O : E n) (γ : Fin (n + 1) → ℝ),
      O ∈ interior (NormalHull.hull v) ∧ (∀ i, 1 ≤ γ i) ∧
      (0 : E n) ∈ interior (NormalHull.hull (fun l => γ (labelCoordinate l) • (v l - O))) ∧
      Nonempty (GroupState (fun l => γ (labelCoordinate l) • (v l - O)) (insert j G)) := by
  classical
  obtain ⟨hlam0, hlam1, hrestSum, hsplit⟩ := split_positive_average G st.weights st.sites.value
    st.weights_pos st.weights_sum j hj hk
  let lam := st.weights j
  let S := Finset.univ \ insert j G
  let z : E n := (1 - lam)⁻¹ • ∑ i ∈ S, st.weights i • st.sites.value i
  have hrempos : 0 < 1 - lam := sub_pos.mpr hlam1
  have hnormalize : ∑ i ∈ S, st.weights i / (1 - lam) = 1 := by
    rw [← Finset.sum_div, hrestSum]
    exact div_self (ne_of_gt hrempos)
  have hzsum : (∑ i ∈ S, (st.weights i / (1 - lam)) • st.sites.value i) = z := by
    simp only [div_eq_inv_mul, mul_smul, ← Finset.smul_sum]
    rfl
  have hzi : z ∈ interior (NormalHull.hull v) := by
    rw [← hzsum]
    apply weighted_average_interior v S (fun i => st.weights i / (1 - lam))
      st.sites.value _ hnormalize (fun i hi => st.sites.interior i)
    intro i hi
    have hiG : i ∉ G := fun hiG =>
      (Finset.mem_sdiff.mp hi).2 (Finset.mem_insert_of_mem hiG)
    exact (div_pos (st.weights_pos i hiG) hrempos).le
  have hcommon : st.common = (1 - lam) • z + lam • st.sites.value j := by
    rw [← st.positive_average]
    exact hsplit
  obtain ⟨t, ht, hOi⟩ := exists_center_beyond (NormalHull.hull v) (z := z) (st.sites.interior j)
  let O : E n := z + t • (st.sites.value j - z)
  let γ : Fin (n + 1) → ℝ := fun i =>
    if i ∈ G then t / (t - lam) else if i = j then t / (t - 1) else 1
  have htlam : 0 < t - lam := by dsimp [lam]; linarith
  have ht1 : 0 < t - 1 := sub_pos.mpr ht
  have hγ : ∀ i, 1 ≤ γ i := by
    intro i
    dsimp only [γ]
    split_ifs
    · apply (le_div_iff₀ htlam).mpr
      dsimp [lam]
      linarith
    · apply (le_div_iff₀ ht1).mpr
      linarith
    · exact le_rfl
  have hγpos : ∀ i, 0 < γ i := fun i => lt_of_lt_of_le zero_lt_one (hγ i)
  let v' : L n → E n := fun l => γ (labelCoordinate l) • (v l - O)
  have hOzero : (0 : E n) ∈ interior (NormalHull.hull (fun l => v l - O)) := by
    simpa using interior_translation v O (x := O) hOi
  have hsub : NormalHull.hull (fun l => v l - O) ⊆ NormalHull.hull v' :=
    hull_subset_radial_hull (fun l => v l - O) (fun l => γ (labelCoordinate l))
      (fun l => hγ _) (interior_subset hOzero)
  have hzero : (0 : E n) ∈ interior (NormalHull.hull v') := interior_mono hsub hOzero
  have hznew : z - O ∈ interior (NormalHull.hull v') :=
    interior_mono hsub (interior_translation v O hzi)
  let s' : Fin (n + 1) → E n := fun i => if i ∈ insert j G then z - O else st.sites.value i - O
  have hmerge := merge_algebra hcommon (ne_of_gt htlam) (ne_of_gt ht1)
  have htransform (i : Fin (n + 1)) : s' i = γ i • (st.sites.value i - O) := by
    by_cases hiG : i ∈ G
    · rw [show s' i = z - O by simp [s', hiG], show γ i = t / (t - lam) by simp [γ, hiG],
        st.common_eq i hiG]
      exact hmerge.1.symm
    · by_cases hij : i = j
      · subst i
        rw [show s' j = z - O by simp [s'], show γ j = t / (t - 1) by simp [γ, hj]]
        exact hmerge.2.symm
      · simp [s', γ, hiG, hij]
  have hs'eq (i : Fin (n + 1)) :
      s' i = (1 - st.sites.parameter i) • v' (Sum.inl i) + st.sites.parameter i • v' (Sum.inr i) := by
    rw [htransform, st.sites.value_eq]
    ext k
    simp only [v', labelCoordinate, Sum.elim_inl, Sum.elim_inr, id_eq,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hs'int (i : Fin (n + 1)) : s' i ∈ interior (NormalHull.hull v') := by
    by_cases hi : i ∈ insert j G
    · simpa only [s', if_pos hi] using hznew
    · simpa only [s', if_neg hi] using
        interior_mono hsub (interior_translation v O (st.sites.interior i))
  refine ⟨O, γ, hOi, hγ, hzero, ⟨{
    sites := {
      value := s'
      parameter := st.sites.parameter
      parameter_pos := st.sites.parameter_pos
      parameter_lt_one := st.sites.parameter_lt_one
      value_eq := hs'eq
      interior := hs'int }
    common := z - O
    common_eq := by intro i hi; simp only [s', if_pos hi]
    weights := fun i => st.weights i / (1 - lam)
    weights_pos := ?_
    weights_sum := hnormalize
    positive_average := ?_ }⟩⟩
  · intro i hi
    exact div_pos (st.weights_pos i (fun hiG => hi (Finset.mem_insert_of_mem hiG))) hrempos
  · change (∑ i ∈ S, (st.weights i / (1 - lam)) • s' i) = z - O
    have heq : (∑ i ∈ S, (st.weights i / (1 - lam)) • s' i) =
        (∑ i ∈ S, (st.weights i / (1 - lam)) • st.sites.value i) -
          (∑ i ∈ S, st.weights i / (1 - lam)) • O := by
      rw [Finset.sum_smul]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i ∉ insert j G := (Finset.mem_sdiff.mp hi).2
      simp only [s', if_neg hi', smul_sub]
    rw [heq, hzsum, hnormalize, one_smul]

end NormalProjective.DiagonalSites
end

/- Source: NormalProjective/NormalizedCubeMoves.lean -/
section
/-! # The diagonal merge is a literal admissible projective move followed by a normal move -/
open Set Matrix
open scoped BigOperators
namespace NormalProjective.NormalizedCubeMoves
open UnitNormalization CanonicalModel CanonicalModel.Realization
open RootedGeometry CyclicCube NormalHull DiagonalSites
variable {n : ℕ}
abbrev E (n : ℕ) := CanonicalModel.Space (n + 1)
abbrev L (n : ℕ) := Labels (n + 1)

def data (v : L n → E n) : MatrixRealization.MatrixData (n + 1) (L n) := (v, fun _ => 1)
abbrev Realizes (v : L n → E n) := MatrixRealization.Realizes (referenceCube n) (data v)
def realization (v : L n → E n) (hv : Realizes v) : Realization (referenceCube n) :=
  MatrixRealization.realization (referenceCube n) (data v) hv

theorem zero_interior_hull (v : L n → E n) (hv : Realizes v) :
    (0 : E n) ∈ interior (NormalHull.hull v) := by
  let p := MatrixRealization.regular (referenceCube n) (data v) hv
  have hp := MatrixRealization.regular_data (referenceCube n) (data v) hv
  apply zero_interior_of_primal_bounded (Nat.succ_pos _) v
  have hc := p.compact
  rw [hp] at hc
  exact hc.isBounded

theorem exposed_normals (v : L n → E n) (hv : Realizes v) (l : L n) :
    ∃ u : E n →L[ℝ] ℝ, u (v l) = 1 ∧ ∀ k, k ≠ l → u (v k) < 1 := by
  let p := MatrixRealization.regular (referenceCube n) (data v) hv
  have hp := MatrixRealization.regular_data (referenceCube n) (data v) hv
  obtain ⟨x, hx, hxl, hxs⟩ := p.strict_facet_point l
  rw [hp] at hxl hxs
  refine ⟨rowForm x, ?_, fun k hkl => ?_⟩
  · simpa only [data, MatrixRealization.asData, rowForm_apply, dot_comm] using hxl
  · simpa only [data, MatrixRealization.asData, rowForm_apply, dot_comm] using hxs k hkl

theorem initial_sites (hn : 1 ≤ n) (v : L n → E n) (hv : Realizes v) :
    Nonempty (GroupState v {0}) := by
  let p := MatrixRealization.regular (referenceCube n) (data v) hv
  have hp := MatrixRealization.regular_data (referenceCube n) (data v) hv
  have htype := hv.choose_spec.2
  have hnopp := cube_noOpposite p htype
  rw [hp] at hnopp
  exact initial_group hn v (zero_interior_hull v hv) hnopp (exposed_normals v hv)

theorem realizes_of_sites (v : L n → E n)
    (hz : (0 : E n) ∈ interior (NormalHull.hull v)) (s : Sites v) : Realizes v := by
  let p := MatrixRealization.asData (data v)
  have hc : IsCompact (dataRegion p) := primal_compact_of_zero_interior v hz
  have hfull : (interior (dataRegion p)).Nonempty := ⟨0, primal_zero_interior v⟩
  have hnopp := noOpposite_of_pair_sites v (fun i =>
    ⟨s.parameter i, s.parameter_pos i, s.parameter_lt_one i,
      by rw [← s.value_eq i]; exact s.interior i⟩)
  exact ⟨PairedHalfspaces.regularOfNoOpposite p hc hfull hnopp, rfl,
    PairedHalfspaces.cube_type_of_noOpposite p hc hfull hnopp⟩

theorem rowForm_sub (x y : E n) : rowForm (x - y) = rowForm x - rowForm y := by
  apply ContinuousLinearMap.ext
  intro z
  simp [rowForm_apply, dot, sub_mul, Finset.sum_sub_distrib]

theorem rowForm_smul (r : ℝ) (x : E n) : rowForm (r • x) = r • rowForm x := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [rowForm_apply, dot, Pi.smul_apply, smul_eq_mul,
    ContinuousLinearMap.smul_apply, Finset.mul_sum, mul_assoc]

theorem realizes_translation (v : L n → E n) (hv : Realizes v) (O : E n)
    (hO : O ∈ interior (NormalHull.hull v)) : Realizes (fun l => v l - O) := by
  let p := MatrixRealization.regular (referenceCube n) (data v) hv
  have hp := MatrixRealization.regular_data (referenceCube n) (data v) hv
  let u := -rowForm O
  have hsupport : ∀ i, 0 < p.data.2 i := by rw [hp]; exact fun _ => zero_lt_one
  have hu : ∀ x ∈ dataRegion p.data, 0 < 1 + u x := by
    intro x hx
    rw [hp] at hx
    simpa only [u, ContinuousLinearMap.neg_apply, rowForm_apply, sub_eq_add_neg] using
      interior_center_denominator v hO hx
  let q := elementaryRegular p u hsupport hu
  have hq : q.data = MatrixRealization.asData (data (fun l => v l - O)) := by
    apply Prod.ext
    · funext l
      change p.data.1 l + p.data.2 l • u = rowForm (v l - O)
      rw [hp]
      change rowForm (v l) + (1 : ℝ) • (-rowForm O) = rowForm (v l - O)
      rw [one_smul, rowForm_sub, sub_eq_add_neg]
    · change p.data.2 = fun _ => 1
      exact congrArg Prod.snd hp
  exact ⟨q, hq, hv.choose_spec.2.trans (elementaryRegular_type p u hsupport hu)⟩

theorem projective_translation (v : L n → E n) (hv : Realizes v) (O : E n)
    (hO : O ∈ interior (NormalHull.hull v))
    (hw : Realizes (fun l => v l - O)) :
    ProjectiveStep (realization v hv) (realization (fun l => v l - O) hw) := by
  apply MatrixRealization.projective_step (referenceCube n) (data v) (data (fun l => v l - O))
    hv hw (-O)
  · intro i j
    simp [data, sub_eq_add_neg]
  · rfl
  · exact fun _ => zero_le_one
  · intro x hx
    have hh := interior_center_denominator v hO hx
    simpa only [rowForm_apply, dot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib,
      sub_eq_add_neg] using hh

theorem normal_radial (v : L n → E n) (hv : Realizes v)
    (γ : Fin (n + 1) → ℝ) (hγ : ∀ i, 0 < γ i)
    (hw : Realizes (fun l => γ (labelCoordinate l) • v l)) :
    NormalStep (realization v hv) (realization (fun l => γ (labelCoordinate l) • v l) hw) := by
  change (fun i => unitRow ((MatrixRealization.regular _ _ hv).data.1 i)) =
    (fun i => unitRow ((MatrixRealization.regular _ _ hw).data.1 i))
  rw [MatrixRealization.regular_data, MatrixRealization.regular_data]
  funext i
  change unitRow (rowForm (v i)) = unitRow (rowForm (γ (labelCoordinate i) • v i))
  rw [rowForm_smul, unitRow_pos_smul _ (hγ _)]

theorem actual_merge
    (v : L n → E n) (hv : Realizes v) (G : Finset (Fin (n + 1)))
    (st : GroupState v G) (j : Fin (n + 1)) (hj : j ∉ G)
    (hk : ∃ k, k ∉ G ∧ k ≠ j) :
    ∃ (w : L n → E n) (hw : Realizes w),
      Nonempty (GroupState w (insert j G)) ∧
      ∃ Y : Realization (referenceCube n),
        ProjectiveStep (realization v hv) Y ∧ NormalStep Y (realization w hw) := by
  obtain ⟨O, γ, hO, hγ, hzero, ⟨st'⟩⟩ := merge_sites v G st j hj hk
  let w : L n → E n := fun l => γ (labelCoordinate l) • (v l - O)
  have hw : Realizes w := realizes_of_sites w hzero st'.sites
  have hmid := realizes_translation v hv O hO
  refine ⟨w, hw, ⟨st'⟩, realization (fun l => v l - O) hmid,
    projective_translation v hv O hO hmid, ?_⟩
  exact normal_radial (fun l => v l - O) hmid γ
    (fun i => lt_of_lt_of_le zero_lt_one (hγ i)) hw

end NormalProjective.NormalizedCubeMoves
end

/- Source: NormalProjective/Parallelotope.lean -/
section
/-! # A cube with parallel opposite facets is actually affinely the unit cube -/
open Set Matrix
open scoped BigOperators
namespace NormalProjective.Parallelotope
open UnitNormalization CanonicalModel CanonicalModel.Realization
open RootedGeometry CyclicCube
variable {n : ℕ}
abbrev E (n : ℕ) := CanonicalModel.Space (n + 1)
abbrev L (n : ℕ) := Labels (n + 1)

def negativeDiagonalEquiv (w : E n) (hw : ∀ i, w i ≠ 0) : E n ≃ₗ[ℝ] E n where
  toFun x := fun i => -(w i)⁻¹ * x i
  invFun y := fun i => -(w i) * y i
  map_add' x y := by ext i; simp only [Pi.add_apply]; ring
  map_smul' c x := by ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
  left_inv x := by ext i; field_simp [hw i]
  right_inv y := by ext i; field_simp [hw i]

theorem reference_facet_lower (i : Fin (n + 1)) :
    (referenceCube n).facet (Sum.inl i) = {x ∈ unitBox n | x i = 0} := by
  rw [referenceCube, presentation_facet]
  change {x ∈ dataRegion (cubeData n 0) | -x i = 0} = _
  have hK : dataRegion (cubeData n 0) = unitBox n := by
    change dataRegion (cyclicRegular (n := n) (ε := 0) le_rfl zero_lt_one).data = _
    exact (presentation_carrier _).symm.trans (referenceCube_carrier n)
  rw [hK]
  ext x
  simp

theorem reference_facet_upper (i : Fin (n + 1)) :
    (referenceCube n).facet (Sum.inr i) = {x ∈ unitBox n | x i = 1} := by
  rw [referenceCube, presentation_facet]
  change {x ∈ dataRegion (cubeData n 0) | rowForm (RankObstruction.cyclicMatrix n 0 i) x = 1} = _
  have hK : dataRegion (cubeData n 0) = unitBox n := by
    change dataRegion (cyclicRegular (n := n) (ε := 0) le_rfl zero_lt_one).data = _
    exact (presentation_carrier _).symm.trans (referenceCube_carrier n)
  rw [hK]
  ext x
  simp only [Set.mem_setOf_eq, rowForm_apply, cyclic_dot, zero_mul, add_zero]

theorem lower_normals_nonsingular (Q : Realization (referenceCube n)) :
    (facetCoefficientMatrix (fun j =>
      (rowForm (Q.val.normal (Sum.inl j))).toLinearMap)).det ≠ 0 := by
  let r := cyclicRegular (n := n) (ε := 0) le_rfl zero_lt_one
  let p := ofCanonical Q.val
  have htype : (presentation r).SameLabelledType (presentation p) := by
    change (referenceCube n).SameLabelledType (presentation (ofCanonical Q.val))
    rw [presentation_ofCanonical]
    exact Q.property
  obtain ⟨e, he⟩ := sameLabelledType_raw r p htype
  let f := fun i => (r.data.1 i).toLinearMap
  let g := fun i => (p.data.1 i).toLinearMap
  let ev := faceIsoVertexEquiv f g r.data.2 p.data.2 r.compact p.compact e
  let z : HalfspaceVertices f r.data.2 := ⟨0, rooted_zero_vertex _⟩
  let x := ev z
  have hinc := faceIsoVertexEquiv_incidence f g r.data.2 p.data.2 r.compact p.compact e he z
  have hI (j : Fin (n + 1)) : g (Sum.inl j) x.val = p.data.2 (Sum.inl j) := by
    apply (hinc (Sum.inl j)).mp
    change (-ContinuousLinearMap.proj j : E n →L[ℝ] ℝ) 0 = 0
    simp
  have hsimple : IsSimpleHalfspace g p.data.2 := by
    apply (simple_iff_raw p).mp
    change (presentation (ofCanonical Q.val)).Simple
    rw [presentation_ofCanonical]
    exact (cyclic_simple (n := n) (ε := 0) le_rfl zero_lt_one).of_sameLabelledType Q.property
  exact (simple_active_minor_spans g p.data.2 hsimple x.property (lowerEmbedding _) hI).2

theorem affine_to_unitCube (Q : Realization (referenceCube n)) (hQ : OppositeNormals Q.val) :
    AffineRelated Q (standardRealization n) := by
  classical
  let f : Fin (n + 1) → E n →L[ℝ] ℝ := fun i => rowForm (Q.val.normal (Sum.inl i))
  let h : E n := fun i => Q.val.support (Sum.inl i)
  let k : E n := fun i => Q.val.support (Sum.inr i)
  let w : E n := fun i => h i + k i
  have hup (i : Fin (n + 1)) (x : E n) : dot (Q.val.normal (Sum.inr i)) x = -f i x := by
    rw [hQ i]
    simp only [dot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, f, rowForm_apply]
  have hw : ∀ i, 0 < w i := by
    obtain ⟨z, hz⟩ := (ofCanonical Q.val).full_dimensional
    have hh := regular_interior_strict (ofCanonical Q.val) hz
    intro i
    have hl := hh (Sum.inl i)
    have hr := hh (Sum.inr i)
    change f i z < h i at hl
    change rowForm (Q.val.normal (Sum.inr i)) z < k i at hr
    rw [rowForm_apply, hup] at hr
    dsimp [w]
    linarith
  let A := facetCoefficientMatrix (fun i => (f i).toLinearMap)
  have hA : A.det ≠ 0 := lower_normals_nonsingular Q
  let LA : E n ≃ₗ[ℝ] E n := LinearEquiv.ofInjectiveEndo (Matrix.mulVecLin A)
    (Matrix.mulVec_injective_of_det_ne_zero hA)
  let D := negativeDiagonalEquiv w (fun i => ne_of_gt (hw i))
  let b : E n := fun i => h i / w i
  let a : E n ≃ᵃ[ℝ] E n := (LA.trans D).toAffineEquiv.trans (AffineEquiv.constVAdd ℝ (E n) b)
  have ha (x : E n) (i : Fin (n + 1)) : a x i = (h i - f i x) / w i := by
    change b i + (-(w i)⁻¹ * (A *ᵥ x) i) = _
    rw [facetCoefficientMatrix_mulVec]
    dsimp [b]
    ring
  have hcarrier (x : E n) : x ∈ Q.carrier ↔ a x ∈ unitBox n := by
    change (∀ l : L n, dot (Q.val.normal l) x ≤ Q.val.support l) ↔
      ((∀ i, 0 ≤ a x i) ∧ ∀ i, a x i ≤ 1)
    constructor
    · intro hx
      constructor <;> intro i
      · rw [ha]
        have hh : f i x ≤ h i := by simpa only [f, h, rowForm_apply] using hx (Sum.inl i)
        exact div_nonneg (sub_nonneg.mpr hh) (hw i).le
      · rw [ha]
        apply (div_le_one (hw i)).mpr
        have hh := hx (Sum.inr i)
        rw [hup] at hh
        dsimp [w]
        linarith
    · rintro ⟨hl, hr⟩ l
      cases l with
      | inl i =>
          have hh := hl i
          rw [ha] at hh
          have hs : 0 ≤ h i - f i x := by
            simpa only [zero_mul] using (le_div_iff₀ (hw i)).mp hh
          simpa only [f, h, rowForm_apply] using sub_nonneg.mp hs
      | inr i =>
          have hh := hr i
          rw [ha] at hh
          have hs := (div_le_one (hw i)).mp hh
          rw [hup]
          dsimp [w] at hs
          linarith
  have hlow (x : E n) (i : Fin (n + 1)) :
      dot (Q.val.normal (Sum.inl i)) x = Q.val.support (Sum.inl i) ↔ a x i = 0 := by
    rw [ha, div_eq_zero_iff]
    simp only [ne_of_gt (hw i), or_false, sub_eq_zero, f, h, rowForm_apply]
    exact eq_comm
  have hhigh (x : E n) (i : Fin (n + 1)) :
      dot (Q.val.normal (Sum.inr i)) x = Q.val.support (Sum.inr i) ↔ a x i = 1 := by
    rw [ha, div_eq_one_iff_eq (ne_of_gt (hw i)), hup]
    dsimp [w]
    constructor <;> intro hh <;> linarith
  refine ⟨a, ?_, fun l => ?_⟩
  · change a '' Q.carrier = (referenceCube n).carrier
    rw [referenceCube_carrier]
    ext y
    obtain ⟨x, rfl⟩ := a.surjective y
    rw [a.injective.mem_set_image]
    exact hcarrier x
  · change a '' Q.facet l = (referenceCube n).facet l
    cases l with
    | inl i =>
        rw [reference_facet_lower]
        ext y
        obtain ⟨x, rfl⟩ := a.surjective y
        rw [a.injective.mem_set_image]
        change (x ∈ Q.carrier ∧ dot (Q.val.normal (Sum.inl i)) x = Q.val.support (Sum.inl i)) ↔ _
        rw [hcarrier, hlow]
        rfl
    | inr i =>
        rw [reference_facet_upper]
        ext y
        obtain ⟨x, rfl⟩ := a.surjective y
        rw [a.injective.mem_set_image]
        change (x ∈ Q.carrier ∧ dot (Q.val.normal (Sum.inr i)) x = Q.val.support (Sum.inr i)) ↔ _
        rw [hcarrier, hhigh]
        rfl

end NormalProjective.Parallelotope
end

/- Source: NormalProjective/CubeUpper.lean -/
section
/-! # The full exact cube bound, with actual admissible moves and all dimensions -/
open Set
open scoped BigOperators
namespace NormalProjective.CanonicalModel.Realization
variable {d : ℕ} {ι : Type*} [Fintype ι] {R : Presentation d ι}

/-- The literal word `(PN)^k P`; its first and last projectivities can absorb
actual affine endpoint normalizations without changing the counts. -/
inductive AlternatingPN : Realization R → Realization R → ℕ → Prop
  | single {P Q} : ProjectiveStep P Q → AlternatingPN P Q 0
  | step {P A B Q k} : ProjectiveStep P A → NormalStep A B →
      AlternatingPN B Q k → AlternatingPN P Q (k + 1)

theorem AlternatingPN.word {P Q : Realization R} {k : ℕ} (h : AlternatingPN P Q k) :
    PNWord P Q (k + 1) k := by
  induction h with
  | single hp => exact PNWord.projective hp (PNWord.nil _)
  | step hp hn h ih => exact PNWord.projective hp (PNWord.normal hn ih)

theorem AlternatingPN.precompose {P Q U : Realization R} {k : ℕ}
    (h : AlternatingPN Q U k) (hp : ProjectiveStep P Q) : AlternatingPN P U k := by
  cases h with
  | single hq => exact .single (hp.trans hq)
  | step hq hn ht => exact .step (hp.trans hq) hn ht

theorem AlternatingPN.postcompose {P Q U : Realization R} {k : ℕ}
    (h : AlternatingPN P Q k) (hp : ProjectiveStep Q U) : AlternatingPN P U k := by
  induction h generalizing U with
  | single hq => exact .single (hq.trans hp)
  | step hq hn ht ih => exact .step hq hn (ih hp)

end NormalProjective.CanonicalModel.Realization

namespace NormalProjective.CubeUpper
open UnitNormalization CanonicalModel CanonicalModel.Realization
open RootedGeometry CyclicCube NormalHull DiagonalSites
variable {n : ℕ}
abbrev E (n : ℕ) := CanonicalModel.Space (n + 1)
abbrev L (n : ℕ) := Labels (n + 1)

theorem concurrent_projective_to_unitCube
    (v : L n → E n) (hv : NormalizedCubeMoves.Realizes v) (s : Sites v)
    (z : E n) (hs : ∀ i, s.value i = z) :
    ProjectiveStep (NormalizedCubeMoves.realization v hv) (standardRealization n) := by
  have hzi : z ∈ interior (NormalHull.hull v) := by
    rw [← hs 0]
    exact s.interior 0
  have hw := NormalizedCubeMoves.realizes_translation v hv z hzi
  let Q := NormalizedCubeMoves.realization (fun l => v l - z) hw
  have hopp : OppositeNormals Q.val := by
    intro i
    let t := s.parameter i
    have ht : 0 < t := s.parameter_pos i
    have ht1 : t < 1 := s.parameter_lt_one i
    have hsite : z = (1 - t) • v (Sum.inl i) + t • v (Sum.inr i) :=
      (hs i).symm.trans (s.value_eq i)
    have hvectors : v (Sum.inr i) - z =
        ((1 - t) / t) • (-(v (Sum.inl i) - z)) := by
      ext k
      have hh := congrFun hsite k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hh
      simp only [Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
      field_simp [ne_of_gt ht]
      nlinarith
    change unitRow ((MatrixRealization.regular _ _ hw).data.1 (Sum.inr i)) =
      -unitRow ((MatrixRealization.regular _ _ hw).data.1 (Sum.inl i))
    rw [MatrixRealization.regular_data]
    change unitRow (rowForm (v (Sum.inr i) - z)) = -unitRow (rowForm (v (Sum.inl i) - z))
    rw [hvectors, NormalizedCubeMoves.rowForm_smul, RootedGeometry.rowForm_neg,
      unitRow_pos_smul _ (div_pos (sub_pos.mpr ht1) ht), unitRow_neg]
  have hp : ProjectiveStep (NormalizedCubeMoves.realization v hv) Q :=
    NormalizedCubeMoves.projective_translation v hv z hzi hw
  exact hp.trans (Parallelotope.affine_to_unitCube Q hopp).projectiveStep

theorem finish_group
    (m : ℕ) (v : L n → E n) (hv : NormalizedCubeMoves.Realizes v)
    (G : Finset (Fin (n + 1))) (st : GroupState v G)
    (hcard : (Finset.univ \ G).card = m + 1) :
    AlternatingPN (NormalizedCubeMoves.realization v hv) (standardRealization n) m := by
  classical
  induction m generalizing v G with
  | zero =>
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
      have hwj : st.weights j = 1 := by
        have hh := st.weights_sum
        rw [hj] at hh
        simpa using hh
      have hsj : st.sites.value j = st.common := by
        have hh := st.positive_average
        rw [hj] at hh
        simpa only [Finset.sum_singleton, hwj, one_smul] using hh
      have hall (i : Fin (n + 1)) : st.sites.value i = st.common := by
        by_cases hi : i ∈ G
        · exact st.common_eq i hi
        · have his : i ∈ Finset.univ \ G := by simp [hi]
          rw [hj] at his
          have hij := Finset.mem_singleton.mp his
          simpa only [hij] using hsj
      exact .single (concurrent_projective_to_unitCube v hv st.sites st.common hall)
  | succ m ih =>
      have htwo : 1 < (Finset.univ \ G).card := by omega
      obtain ⟨j, hjS, k, hkS, hjk⟩ := Finset.one_lt_card.mp htwo
      have hj : j ∉ G := (Finset.mem_sdiff.mp hjS).2
      have hk : k ∉ G := (Finset.mem_sdiff.mp hkS).2
      obtain ⟨w, hw, ⟨st'⟩, Y, hp, hn⟩ :=
        NormalizedCubeMoves.actual_merge v hv G st j hj ⟨k, hk, Ne.symm hjk⟩
      have hrest : Finset.univ \ insert j G = (Finset.univ \ G).erase j := by
        ext i
        simp [and_comm, and_left_comm]
      have hcard' : (Finset.univ \ insert j G).card = m + 1 := by
        rw [hrest, Finset.card_erase_of_mem hjS, hcard]
        omega
      exact .step hp hn (ih w hw (insert j G) st' hcard')

theorem normalized_upper_chain (hn : 1 ≤ n) (v : L n → E n)
    (hv : NormalizedCubeMoves.Realizes v) :
    AlternatingPN (NormalizedCubeMoves.realization v hv) (standardRealization n) (n - 1) := by
  obtain ⟨st⟩ := NormalizedCubeMoves.initial_sites hn v hv
  apply finish_group (n - 1) v hv {0} st
  simp only [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin]
  omega

/-- The upper bound in Theorem 3, with exactly d-1 projective moves and d-2
normal moves, for every actual labelled realization of the d-cube (d=n+1≥2).
The endpoint affine maps are absorbed into genuine first/last projectivities. -/
theorem every_cube_upper_chain (hn : 1 ≤ n) (P : Realization (referenceCube n)) :
    AlternatingPN P (standardRealization n) (n - 1) := by
  obtain ⟨a, hpos, _⟩ := GenericCoordinates.exists_generic_centered_chart (ofCanonical P.val)
  let r := affineRegular a (ofCanonical P.val)
  let p := normalizedRegular r hpos
  let v := normalizedMatrix r
  have hpdata : p.data = MatrixRealization.asData (v, fun _ => 1) := normalizedRegular_data r hpos
  have hpPres : presentation p = (affineAction a P).val := presentation_normalizedRegular r hpos
  have htype : (referenceCube n).SameLabelledType (presentation p) := by
    rw [hpPres]
    exact (affineAction a P).property
  have hv : NormalizedCubeMoves.Realizes v := ⟨p, hpdata, htype⟩
  have heq : NormalizedCubeMoves.realization v hv = affineAction a P := by
    apply Subtype.ext
    change presentation (MatrixRealization.regular _ _ hv) = _
    rw [MatrixRealization.regularData_ext
      ((MatrixRealization.regular_data _ _ hv).trans hpdata.symm), hpPres]
  have hstart : ProjectiveStep P (NormalizedCubeMoves.realization v hv) := by
    rw [heq]
    exact (affineAction_related a P).projectiveStep
  exact (normalized_upper_chain hn v hv).precompose hstart

/-- The paper's literal target is C_d=[-1,1]^d; x↦2x−1 is composed into the
last projective step, so both advertised move counts remain unchanged. -/
theorem every_cube_exact_word (hn : 1 ≤ n) (P : Realization (referenceCube n)) :
    PNWord P (centeredRealization n) n (n - 1) := by
  have hlast : ProjectiveStep (standardRealization n) (centeredRealization n) :=
    (affineAction_related (cubeCentering n) (standardRealization n)).projectiveStep
  have hword := ((every_cube_upper_chain hn P).postcompose hlast).word
  have hcount : n - 1 + 1 = n := by omega
  simpa only [hcount] using hword

def UniformTotalBound (n k : ℕ) : Prop :=
  ∀ P : Realization (referenceCube n), ∃ p q : ℕ,
    PNWord P (centeredRealization n) p q ∧ p + q ≤ k

/-- Exact worst-case complexity: a uniform total bound exists precisely from
2d-3 onward. This formulation states the complete minimax assertion without
silently assuming that a minimum is attained. -/
theorem exact_cube_bound (hn : 1 ≤ n) (k : ℕ) :
    UniformTotalBound n k ↔ 2 * (n + 1) - 3 ≤ k := by
  constructor
  · intro h
    have hε0 : (0 : ℝ) < 1 / 2 := by norm_num
    have hε1 : (1 / 2 : ℝ) < 1 := by norm_num
    obtain ⟨p, q, hw, hk⟩ := h (CyclicCube.realization (n := n) hε0.le hε1)
    exact (cyclic_to_centeredCube_lower_bound hε0 hε1 hn hw).2.2.trans hk
  · intro hk P
    refine ⟨n, n - 1, every_cube_exact_word hn P, ?_⟩
    omega

/-- Actual lengths of geometric PN words to the paper's specified target. -/
theorem exists_total_length (hn : 1 ≤ n) (P : Realization (referenceCube n)) :
    ∃ k : ℕ, ∃ p q : ℕ, PNWord P (centeredRealization n) p q ∧ p + q = k :=
  ⟨n + (n - 1), n, n - 1, every_cube_exact_word hn P, rfl⟩

/-- The minimum total number of actual moves. Existence is supplied by the
unconditional constructive upper theorem, not by an extra assumption. -/
def pnDistance (hn : 1 ≤ n) (P : Realization (referenceCube n)) : ℕ := by
  classical
  exact Nat.find (exists_total_length hn P)

theorem pnDistance_spec (hn : 1 ≤ n) (P : Realization (referenceCube n)) :
    ∃ p q : ℕ, PNWord P (centeredRealization n) p q ∧ p + q = pnDistance hn P := by
  classical
  exact Nat.find_spec (exists_total_length hn P)

theorem pnDistance_le_iff (hn : 1 ≤ n) (P : Realization (referenceCube n)) (k : ℕ) :
    pnDistance hn P ≤ k ↔ ∃ p q : ℕ,
      PNWord P (centeredRealization n) p q ∧ p + q ≤ k := by
  classical
  constructor
  · intro hk
    obtain ⟨p, q, hw, hlen⟩ := pnDistance_spec hn P
    exact ⟨p, q, hw, by simpa only [hlen] using hk⟩
  · rintro ⟨p, q, hw, hlen⟩
    have hmin : pnDistance hn P ≤ p + q :=
      Nat.find_min' (exists_total_length hn P) ⟨p, q, hw, rfl⟩
    exact hmin.trans hlen

theorem pnDistance_upper (hn : 1 ≤ n) (P : Realization (referenceCube n)) :
    pnDistance hn P ≤ 2 * (n + 1) - 3 := by
  apply (pnDistance_le_iff hn P _).mpr
  exact ⟨n, n - 1, every_cube_exact_word hn P, by omega⟩

theorem cyclic_distance_exact (hn : 1 ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    pnDistance hn (CyclicCube.realization (n := n) hε0.le hε1) = 2 * (n + 1) - 3 := by
  apply le_antisymm (pnDistance_upper hn _)
  obtain ⟨p, q, hw, hlen⟩ := pnDistance_spec hn (CyclicCube.realization hε0.le hε1)
  rw [← hlen]
  exact (cyclic_to_centeredCube_lower_bound hε0 hε1 hn hw).2.2

/-- Literally the largest PN-distance in the paper: the range of minimum word
lengths has greatest element 2d-3. The cyclic family attains it for every allowed ε. -/
theorem largest_PN_distance (hn : 1 ≤ n) :
    IsGreatest (Set.range (pnDistance hn)) (2 * (n + 1) - 3) := by
  constructor
  · exact ⟨CyclicCube.realization (n := n) (ε := 1 / 2) (by norm_num) (by norm_num),
      cyclic_distance_exact hn (ε := 1 / 2) (by norm_num) (by norm_num)⟩
  · rintro k ⟨P, rfl⟩
    exact pnDistance_upper hn P

/-- The successor indexing above covers exactly all dimensions in Theorem 3. -/
theorem dimension_parameterization (d : ℕ) (hd : 2 ≤ d) :
    ∃ n : ℕ, 1 ≤ n ∧ n + 1 = d := ⟨d - 1, by omega, by omega⟩

end NormalProjective.CubeUpper
end

/- Source: NormalProjective/CubeTargetLabels.lean -/
section
/-! # The geometric cube target permits every induced facet labelling

The rank lower bound applies to any actual PN word whose final carrier is C_d,
without fixing a facet permutation at the endpoint. This bridge derives opposite
normal pairs from the actual carrier and the labelled cube incidence structure.
-/
open Set
namespace NormalProjective.UnitNormalization
variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem displayed_facet_of_same_carrier
    (p : RegularData d ι) (q : RegularData d κ)
    (hK : dataRegion p.data = dataRegion q.data) (i : ι) :
    ∃ j : κ, (displayedFacet p i).val = (displayedFacet q j).val := by
  let Fp := displayedFacet p i
  have hFp := displayedFacet_isActualFacet p i
  have hexp : IsExposed ℝ (dataRegion q.data) Fp.val := by
    rw [← hK]
    exact Fp.property
  let F : HalfspaceFaces (fun j => (q.data.1 j).toLinearMap) q.data.2 := ⟨Fp.val, hexp⟩
  have hF : IsActualFacet q F := by
    refine ⟨hFp.1, ?_, ?_⟩
    · simpa only [F, hK] using hFp.2.1
    · intro G hFG hGK
      have hGexp : IsExposed ℝ (dataRegion p.data) G.val := by
        rw [hK]
        exact G.property
      let G' : HalfspaceFaces (fun j => (p.data.1 j).toLinearMap) p.data.2 := ⟨G.val, hGexp⟩
      have hG'ne : G'.val ≠ dataRegion p.data := by simpa only [G', hK] using hGK
      have hh := hFp.2.2 G' hFG hG'ne
      apply Subtype.ext
      exact congrArg (fun X : HalfspaceFaces (fun j => (p.data.1 j).toLinearMap) p.data.2 => X.val) hh
  obtain ⟨j, hj⟩ := actualFacet_is_displayed q F hF
  exact ⟨j, congrArg Subtype.val hj⟩

theorem unitRow_eq_of_same_carrier_facet
    (p : RegularData d ι) (q : RegularData d κ)
    (hK : dataRegion p.data = dataRegion q.data) (i : ι) (j : κ)
    (hF : (displayedFacet p i).val = (displayedFacet q j).val) :
    unitRow (p.data.1 i) = unitRow (q.data.1 j) := by
  have hvalid : ∀ x ∈ dataRegion p.data, q.data.1 j x ≤ q.data.2 j := by
    intro x hx
    have hxq : x ∈ dataRegion q.data := hK ▸ hx
    exact hxq j
  have hfacet : {x ∈ dataRegion p.data | p.data.1 i x = p.data.2 i} =
      {x ∈ dataRegion p.data | q.data.1 j x = q.data.2 j} := by
    have hh := hF
    simp only [displayedFacet, tightFace, Set.mem_singleton_iff, forall_eq,
      ContinuousLinearMap.coe_coe] at hh
    change {x ∈ dataRegion p.data | p.data.1 i x = p.data.2 i} =
      {x ∈ dataRegion q.data | q.data.1 j x = q.data.2 j} at hh
    rw [← hK] at hh
    exact hh
  obtain ⟨c, hc, hform, _⟩ := positive_multiple_of_same_facet p i
    (q.data.1 j) (q.normal_ne_zero j) (q.data.2 j) hvalid hfacet
  rw [hform, unitRow_pos_smul _ hc]

end NormalProjective.UnitNormalization

namespace NormalProjective.CubeTargetLabels
open UnitNormalization CanonicalModel CanonicalModel.Realization
open RootedGeometry CyclicCube
variable {n : ℕ}

def partner : Labels (n + 1) → Labels (n + 1) := Sum.swap

theorem chosen_pair_of_not_partner (i j : Labels (n + 1)) (hji : j ≠ partner i) :
    ∃ b : Fin (n + 1) → Bool, Chosen b i ∧ Chosen b j := by
  classical
  cases i with
  | inl i =>
      cases j with
      | inl j => exact ⟨fun _ => false, rfl, rfl⟩
      | inr j =>
          have hij : j ≠ i := fun h => hji (by simpa [partner, h])
          exact ⟨fun k => decide (k ≠ i), by simp [Chosen], by simp [Chosen, hij]⟩
  | inr i =>
      cases j with
      | inl j =>
          have hij : j ≠ i := fun h => hji (by simpa [partner, h])
          exact ⟨fun k => decide (k = i), by simp [Chosen], by simp [Chosen, hij]⟩
      | inr j => exact ⟨fun _ => true, rfl, rfl⟩

theorem reference_normal_partner (i : Labels (n + 1)) :
    (referenceCube n).normal (partner i) = -(referenceCube n).normal i := by
  cases i with
  | inl i => exact referenceCube_oppositeNormals n i
  | inr i =>
      change (referenceCube n).normal (Sum.inl i) = -(referenceCube n).normal (Sum.inr i)
      rw [referenceCube_oppositeNormals n i, neg_neg]

theorem oppositeNormals_of_unitCube_carrier (Q : Realization (referenceCube n))
    (hQ : Q.carrier = unitBox n) : OppositeNormals Q.val := by
  classical
  let p := ofCanonical Q.val
  let r := cyclicRegular (n := n) (ε := 0) le_rfl zero_lt_one
  have hpK : dataRegion p.data = Q.carrier := by
    change dataRegion p.data = Q.val.carrier
    rw [← presentation_carrier, show presentation p = Q.val from presentation_ofCanonical _]
  have hrK : dataRegion r.data = unitBox n := by
    simpa only [r, referenceCube, presentation_carrier] using referenceCube_carrier n
  have hK : dataRegion p.data = dataRegion r.data := hpK.trans (hQ.trans hrK.symm)
  have htype : (referenceCube n).SameLabelledType (presentation p) := by
    simpa only [p, presentation_ofCanonical] using Q.property
  have hnopp := NormalHull.cube_noOpposite p htype
  have hpPres : presentation p = Q.val := presentation_ofCanonical _
  rw [← hpPres]
  intro i
  obtain ⟨j, hj⟩ := displayed_facet_of_same_carrier p r hK (Sum.inl i)
  obtain ⟨k, hk⟩ := displayed_facet_of_same_carrier p r hK (Sum.inr i)
  have hkj : k = partner j := by
    by_contra hne
    obtain ⟨b, hbj, hbk⟩ := chosen_pair_of_not_partner j k hne
    let x := assignedVertex (n := n) (ε := 0) le_rfl zero_lt_one b
    have hxj : x ∈ (displayedFacet r j).val := by
      refine ⟨assignedVertex_mem le_rfl zero_lt_one b, ?_⟩
      intro l hl
      have hlj := Set.mem_singleton_iff.mp hl
      subst l
      exact (assignedVertex_incidence le_rfl zero_lt_one b j).mpr hbj
    have hxk : x ∈ (displayedFacet r k).val := by
      refine ⟨assignedVertex_mem le_rfl zero_lt_one b, ?_⟩
      intro l hl
      have hlk := Set.mem_singleton_iff.mp hl
      subst l
      exact (assignedVertex_incidence le_rfl zero_lt_one b k).mpr hbk
    rw [← hj] at hxj
    rw [← hk] at hxk
    exact hnopp x hxj.1 i ⟨hxj.2 _ (Set.mem_singleton _), hxk.2 _ (Set.mem_singleton _)⟩
  have huj := unitRow_eq_of_same_carrier_facet p r hK (Sum.inl i) j hj
  have huk := unitRow_eq_of_same_carrier_facet p r hK (Sum.inr i) k hk
  change unitRow (p.data.1 (Sum.inr i)) = -unitRow (p.data.1 (Sum.inl i))
  rw [huj, huk, hkj]
  exact reference_normal_partner j

theorem oppositeNormals_of_centeredCube_carrier (Q : Realization (referenceCube n))
    (hQ : Q.carrier = Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ))) :
    OppositeNormals Q.val := by
  let a := cubeCentering n
  let Q' := affineAction a.symm Q
  change Q.val.carrier = Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) at hQ
  have hQ' : Q'.carrier = unitBox n := by
    change (affinePresentation a.symm Q.val).carrier = _
    rw [affinePresentation_carrier, hQ]
    have hcenter : Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) =
        (affinePresentation a (referenceCube n)).carrier := (centeredRealization_carrier n).symm
    rw [hcenter]
    change a.symm '' (affinePresentation a (referenceCube n)).carrier = _
    rw [affinePresentation_carrier, Set.image_image]
    simpa only [AffineEquiv.symm_apply_apply, Set.image_id'] using referenceCube_carrier n
  have hh := oppositeNormals_affine Q'.val (oppositeNormals_of_unitCube_carrier Q' hQ') a
  have heq : affineAction a Q' = Q := by
    have haa : a.symm.symm = a := by ext x; rfl
    simpa only [Q', haa] using affineAction_inverse a.symm Q
  change OppositeNormals (affineAction a Q').val at hh
  simpa only [heq] using hh

/-- The lower bound quantifies over every labelling induced at the geometric
endpoint C_d, not only the chosen standard facet labelling. -/
theorem cyclic_to_geometric_cube_lower_bound {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hn : 1 ≤ n) (Q : Realization (referenceCube n))
    (hQ : Q.carrier = Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)))
    {p q : ℕ} (hword : PNWord (CyclicCube.realization hε0.le hε1) Q p q) :
    n ≤ p ∧ n - 1 ≤ q ∧ 2 * (n + 1) - 3 ≤ p + q :=
  cyclic_geometric_lower_bound hε0 hε1 hn Q
    (oppositeNormals_of_centeredCube_carrier Q hQ) hword

/-- Actual word length to the geometric carrier C_d, with unrestricted induced
facet labels at the endpoint. -/
def GeometricLength (P : Realization (referenceCube n)) (k : ℕ) : Prop :=
  ∃ Q : Realization (referenceCube n), ∃ p q : ℕ,
    Q.carrier = Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) ∧
      PNWord P Q p q ∧ p + q = k

theorem geometricLength_exists (hn : 1 ≤ n) (P : Realization (referenceCube n)) :
    ∃ k : ℕ, GeometricLength P k :=
  ⟨n + (n - 1), centeredRealization n, n, n - 1, centeredRealization_carrier n,
    CubeUpper.every_cube_exact_word hn P, rfl⟩

def geometricPNDistance (hn : 1 ≤ n) (P : Realization (referenceCube n)) : ℕ := by
  classical
  exact Nat.find (geometricLength_exists hn P)

theorem geometricPNDistance_spec (hn : 1 ≤ n) (P : Realization (referenceCube n)) :
    GeometricLength P (geometricPNDistance hn P) := by
  classical
  exact Nat.find_spec (geometricLength_exists hn P)

theorem geometricPNDistance_upper (hn : 1 ≤ n) (P : Realization (referenceCube n)) :
    geometricPNDistance hn P ≤ 2 * (n + 1) - 3 := by
  classical
  have hm : geometricPNDistance hn P ≤ n + (n - 1) :=
    Nat.find_min' (geometricLength_exists hn P)
      ⟨centeredRealization n, n, n - 1, centeredRealization_carrier n,
        CubeUpper.every_cube_exact_word hn P, rfl⟩
  omega

theorem cyclic_geometricPNDistance_exact (hn : 1 ≤ n) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    geometricPNDistance hn (CyclicCube.realization (n := n) hε0.le hε1) =
      2 * (n + 1) - 3 := by
  apply le_antisymm (geometricPNDistance_upper hn _)
  obtain ⟨Q, p, q, hQ, hw, hlen⟩ :=
    geometricPNDistance_spec hn (CyclicCube.realization hε0.le hε1)
  rw [← hlen]
  exact (cyclic_to_geometric_cube_lower_bound hε0 hε1 hn Q hQ hw).2.2

/-- Theorem 3's literal maximum over distances to the geometric cube, including
all allowable endpoint facet permutations. -/
theorem geometric_largest_PN_distance (hn : 1 ≤ n) :
    IsGreatest (Set.range (geometricPNDistance hn)) (2 * (n + 1) - 3) := by
  constructor
  · exact ⟨CyclicCube.realization (n := n) (ε := 1 / 2) (by norm_num) (by norm_num),
      cyclic_geometricPNDistance_exact hn (ε := 1 / 2) (by norm_num) (by norm_num)⟩
  · rintro k ⟨P, rfl⟩
    exact geometricPNDistance_upper hn P

end NormalProjective.CubeTargetLabels
end
