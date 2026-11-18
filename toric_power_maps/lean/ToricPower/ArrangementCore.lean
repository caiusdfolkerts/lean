module

public import ToricPower.ArrangementCells
public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.CWComplex.Classical.Basic
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.CWComplex.Classical.Subcomplex
public import Mathlib.Analysis.Convex.Contractible

attribute [local instance] Classical.propDecidable

/-! The CW structure of the literal integral arrangement and its convex
weight-region subcomplexes.  Elementary cell geometry is proved in
`ArrangementCells`; this file retains recovered source sections 2--4. -/

section ArrangementSource2





/-! # Characteristic charts for genuine arrangement cells

All topology is the subtype topology inherited from the actual linear space.
The relative closed cell is a compact convex body in its active-kernel space.
An ambient homeomorphism of that space identifies the open cell, closed cell,
and boundary with an open ball, closed ball, and sphere of the correct dimension.
No ball-chart or regular-cell hypothesis is postulated.

This source remains a candidate until its ordinary compiler record succeeds.
-/

@[expose] public noncomputable section

open Set Filter Topology Metric

namespace ToricPower.IntegralArrangement

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite ι]

def relativeCell (f : ι → E →ₗ[ℝ] ℝ) (e : ι → ℤ) (I : Set ι)
    (x : E) : Set (cellDirection f I) :=
  {u | x + u.val ∈ cell f e I}

def relativeClosedCell (f : ι → E →ₗ[ℝ] ℝ) (e : ι → ℤ) (I : Set ι)
    (x : E) : Set (cellDirection f I) :=
  {u | x + u.val ∈ closedCell f e I}

theorem relativeCell_eq_strict (f : ι → E →ₗ[ℝ] ℝ) (e : ι → ℤ)
    (I : Set ι) {x : E} (hx : x ∈ cell f e I) :
    relativeCell f e I x =
      ⋂ i, {u : cellDirection f I | i ∉ I →
        (e i : ℝ)-1 < f i (x + u.val) ∧ f i (x + u.val) < (e i : ℝ)} := by
  ext u
  simp only [relativeCell, mem_ofPred_eq, mem_iInter]
  constructor
  · intro hu i hi
    simpa only [ite_eq_right hi] using hu i
  · intro hu i
    by_cases hi : i ∈ I
    · have hxi := hx i
      have hui := (mem_cellDirection f I u.val).mp u.property i hi
      simp only [ite_eq_left hi] at hxi ⊢
      rw [map_add, hxi, hui, add_zero]
    · simpa only [ite_eq_right hi] using hu i hi

theorem relativeCell_isOpen (f : ι → E →ₗ[ℝ] ℝ) (e : ι → ℤ)
    (I : Set ι) {x : E} (hx : x ∈ cell f e I) :
    IsOpen (relativeCell f e I x) := by
  rw [relativeCell_eq_strict f e I hx]
  apply isOpen_iInter_of_finite
  intro i
  by_cases hi : i ∈ I
  · simp only [not_not.mpr hi, false_implies, ofPred_true, isOpen_univ]
  · simp only [hi, not_false_eq_true, true_implies]
    have hf : Continuous (fun u : cellDirection f I => f i (x + u.val)) :=
      (f i).continuous_of_finiteDimensional.comp
        (continuous_const.add continuous_subtype_val)
    exact (isOpen_lt continuous_const hf).inter (isOpen_lt hf continuous_const)

theorem relativeClosedCell_isClosed (f : ι → E →ₗ[ℝ] ℝ)
    (e : ι → ℤ) (I : Set ι) (x : E) :
    IsClosed (relativeClosedCell f e I x) :=
  (closedCell_isClosed f (fun i => (f i).continuous_of_finiteDimensional) e I).preimage
    (continuous_const.add continuous_subtype_val)

theorem relativeCell_subset_relativeClosedCell (f : ι → E →ₗ[ℝ] ℝ)
    (e : ι → ℤ) (I : Set ι) (x : E) :
    relativeCell f e I x ⊆ relativeClosedCell f e I x :=
  fun _ hu => cell_subset_closedCell f e I hu

theorem relativeClosedCell_convex (f : ι → E →ₗ[ℝ] ℝ)
    (e : ι → ℤ) (I : Set ι) (x : E) :
    Convex ℝ (relativeClosedCell f e I x) := by
  intro u hu v hv a b ha hb hab
  have h := closedCell_convex f e I hu hv ha hb hab
  have he : x + (a • u + b • v : cellDirection f I).val =
      a • (x + u.val) + b • (x + v.val) := by
    simp only [Submodule.coe_add, Submodule.coe_smul, smul_add]
    calc
      x + (a • u.val + b • v.val) =
          (a+b) • x + (a • u.val + b • v.val) := by rw [hab, one_smul]
      _ = (a • x + a • u.val) + (b • x + b • v.val) := by
        rw [add_smul]
        abel
  change x + (a • u + b • v : cellDirection f I).val ∈ closedCell f e I
  rw [he]
  exact h

theorem closure_relativeCell (f : ι → E →ₗ[ℝ] ℝ) (e : ι → ℤ)
    (I : Set ι) {x : E} (hx : x ∈ cell f e I) :
    closure (relativeCell f e I x) = relativeClosedCell f e I x := by
  apply Subset.antisymm
  · exact closure_minimal (relativeCell_subset_relativeClosedCell f e I x)
      (relativeClosedCell_isClosed f e I x)
  · intro v hv
    have hmem : ∀ᶠ r : ℝ in 𝓝[<] 1, r • v ∈ relativeCell f e I x := by
      filter_upwards [Ico_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with r hr
      have hh := segment_mem_cell f e I hx hv hr
      change x + (r • v : cellDirection f I).val ∈ cell f e I
      have he : x + (r • v : cellDirection f I).val =
          (1-r) • x + r • (x + v.val) := by
        simp only [Submodule.coe_smul, smul_add, sub_smul, one_smul]
        abel
      exact he.symm ▸ hh
    apply mem_closure_of_tendsto _ hmem
    have ht : Tendsto (fun r : ℝ => r • v) (𝓝 1) (𝓝 v) := by
      have continuousScaling : Continuous (fun r : ℝ => r • v) := by fun_prop
      simpa only [one_smul] using continuousScaling.tendsto (1 : ℝ)
    exact ht.mono_left (nhdsWithin_le_nhds (a := (1 : ℝ)) (s := Iio 1))

theorem relativeCell_convex (f : ι → E →ₗ[ℝ] ℝ)
    (e : ι → ℤ) (I : Set ι) (x : E) : Convex ℝ (relativeCell f e I x) := by
  intro u hu v hv a b ha hb hab i
  have hui := hu i
  have hvi := hv i
  have he : f i (x + (a • u + b • v : cellDirection f I).val) =
      a * f i (x + u.val) + b * f i (x + v.val) := by
    simp only [Submodule.coe_add, Submodule.coe_smul, map_add, map_smul, smul_eq_mul]
    calc
      f i x + (a * f i u.val + b * f i v.val) =
          (a + b) * f i x + (a * f i u.val + b * f i v.val) := by
            rw [hab, one_mul]
      _ = a * (f i x + f i u.val) + b * (f i x + f i v.val) := by ring
  by_cases hi : i ∈ I
  · simp only [ite_eq_left hi] at hui hvi ⊢
    rw [he, hui, hvi, ← add_mul, hab, one_mul]
  · simp only [ite_eq_right hi] at hui hvi ⊢
    rw [he]
    exact (convex_Ioo ((e i : ℝ) - 1) (e i : ℝ)) hui hvi ha hb hab

theorem interior_relativeClosedCell (f : ι → E →ₗ[ℝ] ℝ)
    (e : ι → ℤ) (I : Set ι) {x : E} (hx : x ∈ cell f e I) :
    interior (relativeClosedCell f e I x) = relativeCell f e I x := by
  have hopen := relativeCell_isOpen f e I hx
  have hzero : (0 : cellDirection f I) ∈ relativeCell f e I x := by
    simpa only [relativeCell, mem_ofPred_eq, Submodule.coe_zero, add_zero] using hx
  rw [← closure_relativeCell f e I hx,
    (relativeCell_convex f e I x).interior_closure_eq_interior_of_nonempty_interior
      (by rw [hopen.interior_eq]; exact ⟨0, hzero⟩), hopen.interior_eq]

theorem relativeClosedCell_isCompact (f : ι → E →ₗ[ℝ] ℝ)
    (e : ι → ℤ) (I : Set ι) (x : E) (hc : IsCompact (closedCell f e I)) :
    IsCompact (relativeClosedCell f e I x) := by
  apply Metric.isCompact_of_isClosed_isBounded (relativeClosedCell_isClosed f e I x)
  obtain ⟨R, hR⟩ := hc.isBounded.exists_norm_le
  rw [isBounded_iff_forall_norm_le]
  refine ⟨R + ‖x‖, ?_⟩
  intro u hu
  have h := (norm_sub_le (x + u.val) x).trans (add_le_add (hR _ hu) le_rfl)
  simpa only [add_sub_cancel_left, Submodule.norm_coe] using h

/-- The characteristic chart is a genuine homeomorphism of the relative
direction space, with the exact intrinsic dimension. -/
theorem exists_relativeCell_ball_chart (f : ι → E →ₗ[ℝ] ℝ)
    (e : ι → ℤ) (I : Set ι) {x : E} (hx : x ∈ cell f e I)
    (hc : IsCompact (closedCell f e I)) :
    ∃ h : cellDirection f I ≃ₜ (Fin (Module.finrank ℝ (cellDirection f I)) → ℝ),
      h '' relativeCell f e I x = ball 0 1 ∧
      h '' relativeClosedCell f e I x = closedBall 0 1 ∧
      h '' (relativeClosedCell f e I x \ relativeCell f e I x) = sphere 0 1 := by
  let c := (Module.finBasis ℝ (cellDirection f I)).equivFun.toContinuousLinearEquiv
  let C := c '' relativeClosedCell f e I x
  have hC : IsCompact C := (relativeClosedCell_isCompact f e I x hc).image c.continuous
  have hconv : Convex ℝ C := (relativeClosedCell_convex f e I x).linear_image c.toLinearMap
  have hint : interior C = c '' relativeCell f e I x := by
    change interior (c.toHomeomorph '' relativeClosedCell f e I x) =
      c.toHomeomorph '' relativeCell f e I x
    rw [← c.toHomeomorph.image_interior, interior_relativeClosedCell f e I hx]
  have hne : (interior C).Nonempty := by
    rw [hint]
    exact ⟨c 0, 0, by simpa [relativeCell] using hx, rfl⟩
  obtain ⟨g, hg, hgc, hgf⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconv hne hC.isBounded
  refine ⟨c.toHomeomorph.trans g, ?_, ?_, ?_⟩
  · change (g ∘ c) '' relativeCell f e I x = _
    rw [image_comp, ← hint]
    exact hg
  · change (g ∘ c) '' relativeClosedCell f e I x = _
    rw [image_comp]
    simpa only [hC.isClosed.closure_eq] using hgc
  · change (g ∘ c) '' (relativeClosedCell f e I x \ relativeCell f e I x) = _
    rw [image_comp, image_sdiff c.injective, ← hint]
    have hfront : C \ interior C = frontier C := by rw [frontier, hC.isClosed.closure_eq]
    change g '' (C \ interior C) = _
    rw [hfront]
    exact hgf

end ToricPower.IntegralArrangement

end
end ArrangementSource2

section ArrangementSource3




/-! # The actual CW structure of a bounded-cell hyperplane arrangement

The index of an `n`-cell records a nonempty literal arrangement cell whose
active-kernel space has dimension `n`. The characteristic maps are constructed
from the ball charts, boundary finiteness from integer label bounds, the
dimension drop from a new independent equality, and weak topology from local
finiteness. No cellular exactness or CW structure is assumed.

The compactness hypothesis on closed cells is discharged for the augmented
integral arrangement at the end of the file.

Candidate source: verification requires an ordinary successful compiler run.
-/

@[expose] public noncomputable section

open Set Function Metric Topology

namespace ToricPower.IntegralArrangement

universe u

variable {E ι : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite ι]

abbrev Cell (f : ι → E →ₗ[ℝ] ℝ) (d : ℕ) :=
  {p : (ι → ℤ) × Set ι // (cell f p.1 p.2).Nonempty ∧
    Module.finrank ℝ (cellDirection f p.2) = d}

def cellCenter (f : ι → E →ₗ[ℝ] ℝ) {d : ℕ} (c : Cell f d) : E :=
  c.property.1.choose

theorem cellCenter_mem (f : ι → E →ₗ[ℝ] ℝ) {d : ℕ} (c : Cell f d) :
    cellCenter f c ∈ cell f c.val.1 c.val.2 := c.property.1.choose_spec

variable (f : ι → E →ₗ[ℝ] ℝ)
  (hc : ∀ e I, IsCompact (closedCell f e I))

def cellCoordinateChart {d : ℕ} (c : Cell f d) :
    cellDirection f c.val.2 ≃ₜ (Fin d → ℝ) := by
  rcases c with ⟨⟨e, I⟩, hn, hd⟩
  dsimp only at hd ⊢
  subst d
  exact (exists_relativeCell_ball_chart f e I hn.choose_spec (hc e I)).choose

theorem cellCoordinateChart_spec {d : ℕ} (c : Cell f d) :
    cellCoordinateChart f hc c '' relativeCell f c.val.1 c.val.2 (cellCenter f c) =
        ball 0 1 ∧
    cellCoordinateChart f hc c '' relativeClosedCell f c.val.1 c.val.2 (cellCenter f c) =
        closedBall 0 1 ∧
    cellCoordinateChart f hc c ''
        (relativeClosedCell f c.val.1 c.val.2 (cellCenter f c) \
          relativeCell f c.val.1 c.val.2 (cellCenter f c)) = sphere 0 1 := by
  rcases c with ⟨⟨e, I⟩, hn, hd⟩
  dsimp only at hd ⊢
  subst d
  exact (exists_relativeCell_ball_chart f e I hn.choose_spec (hc e I)).choose_spec

def cellMap {d : ℕ} (c : Cell f d) (z : Fin d → ℝ) : E :=
  cellCenter f c + ((cellCoordinateChart f hc c).symm z).val

theorem cellMap_isEmbedding {d : ℕ} (c : Cell f d) :
    Topology.IsEmbedding (cellMap f hc c) :=
  (Homeomorph.addLeft (cellCenter f c)).isEmbedding.comp
    (Topology.IsEmbedding.subtypeVal.comp (cellCoordinateChart f hc c).symm.isEmbedding)

private theorem translated_relativeCell_image {d : ℕ} (c : Cell f d) :
    (fun v : cellDirection f c.val.2 => cellCenter f c + v.val) ''
      relativeCell f c.val.1 c.val.2 (cellCenter f c) = cell f c.val.1 c.val.2 := by
  apply Subset.antisymm
  · rintro y ⟨v, hv, rfl⟩
    exact hv
  · intro y hy
    let v : cellDirection f c.val.2 := ⟨y - cellCenter f c,
      sub_mem_cellDirection f c.val.1 c.val.2
        (cell_subset_closedCell f _ _ (cellCenter_mem f c))
        (cell_subset_closedCell f _ _ hy)⟩
    refine ⟨v, ?_, ?_⟩
    · simpa [relativeCell, v] using hy
    · simp [v]

private theorem translated_relativeClosedCell_image {d : ℕ} (c : Cell f d) :
    (fun v : cellDirection f c.val.2 => cellCenter f c + v.val) ''
      relativeClosedCell f c.val.1 c.val.2 (cellCenter f c) =
        closedCell f c.val.1 c.val.2 := by
  apply Subset.antisymm
  · rintro y ⟨v, hv, rfl⟩
    exact hv
  · intro y hy
    let v : cellDirection f c.val.2 := ⟨y - cellCenter f c,
      sub_mem_cellDirection f c.val.1 c.val.2
        (cell_subset_closedCell f _ _ (cellCenter_mem f c)) hy⟩
    refine ⟨v, ?_, ?_⟩
    · simpa [relativeClosedCell, v] using hy
    · simp [v]

private theorem cellMap_image_of_chart_image {d : ℕ} (c : Cell f d)
    (P : Set (cellDirection f c.val.2)) (S : Set (Fin d → ℝ))
    (hPS : cellCoordinateChart f hc c '' P = S) :
    cellMap f hc c '' S =
      (fun v : cellDirection f c.val.2 => cellCenter f c + v.val) '' P := by
  rw [← hPS, image_image]
  congr 1
  funext v
  simp only [cellMap, Homeomorph.symm_apply_apply]

theorem cellMap_image_ball {d : ℕ} (c : Cell f d) :
    cellMap f hc c '' ball 0 1 = cell f c.val.1 c.val.2 := by
  rw [cellMap_image_of_chart_image f hc c _ _ (cellCoordinateChart_spec f hc c).1,
    translated_relativeCell_image]

theorem cellMap_image_closedBall {d : ℕ} (c : Cell f d) :
    cellMap f hc c '' closedBall 0 1 = closedCell f c.val.1 c.val.2 := by
  rw [cellMap_image_of_chart_image f hc c _ _ (cellCoordinateChart_spec f hc c).2.1,
    translated_relativeClosedCell_image]

theorem cellMap_image_sphere {d : ℕ} (c : Cell f d) :
    cellMap f hc c '' sphere 0 1 = closedCell f c.val.1 c.val.2 \ cell f c.val.1 c.val.2 := by
  rw [cellMap_image_of_chart_image f hc c _ _ (cellCoordinateChart_spec f hc c).2.2]
  have hi : Function.Injective (fun v : cellDirection f c.val.2 => cellCenter f c + v.val) :=
    fun v w h => Subtype.ext (add_left_cancel h)
  rw [image_sdiff hi, translated_relativeClosedCell_image, translated_relativeCell_image]

def cellPartialEquiv {d : ℕ} (c : Cell f d) : PartialEquiv (Fin d → ℝ) E where
  toFun := cellMap f hc c
  invFun := Function.invFun (cellMap f hc c)
  source := ball 0 1
  target := cellMap f hc c '' ball 0 1
  map_source' z hz := ⟨z, hz, rfl⟩
  map_target' := by
    rintro _ ⟨z, hz, rfl⟩
    simpa only [Function.leftInverse_invFun (cellMap_isEmbedding f hc c).injective z] using hz
  left_inv' z _ := Function.leftInverse_invFun (cellMap_isEmbedding f hc c).injective z
  right_inv' := by
    rintro _ ⟨z, _, rfl⟩
    exact Function.apply_invFun_apply

theorem cellPartialEquiv_continuousOn_symm {d : ℕ} (c : Cell f d) :
    ContinuousOn (cellPartialEquiv f hc c).symm (cellPartialEquiv f hc c).target := by
  change ContinuousOn (Function.invFun (cellMap f hc c)) (cellMap f hc c '' ball 0 1)
  apply (cellMap_isEmbedding f hc c).isInducing.continuousOn_image_iff.mpr
  simpa only [Function.invFun_comp (cellMap_isEmbedding f hc c).injective] using
    (continuous_id.continuousOn : ContinuousOn (id : (Fin d → ℝ) → _) (ball 0 1))

theorem sigmaCell_label_injective :
    Function.Injective (fun c : Σ d, Cell f d => c.2.val) := by
  rintro ⟨d, p, hp, hd⟩ ⟨e, q, hq, he⟩ hpq
  dsimp only at hpq
  subst q
  have hde : d = e := hd.symm.trans he
  cases hde
  rfl

/-- A genuine CW structure on the actual vector space, with no change of
its topology or of its arrangement cells. -/
@[instance_reducible]
def arrangementCWComplex : Topology.CWComplex (Set.univ : Set E) where
  cell := Cell f
  map _ c := cellPartialEquiv f hc c
  source_eq _ _ := rfl
  continuousOn d c := by
    change ContinuousOn (cellMap f hc c) (closedBall (0 : Fin d → ℝ) 1)
    exact (cellMap_isEmbedding f hc c).continuous.continuousOn
  continuousOn_symm d c := by
    change ContinuousOn (Function.invFun (cellMap f hc c))
      (cellMap f hc c '' ball (0 : Fin d → ℝ) 1)
    exact cellPartialEquiv_continuousOn_symm f hc c
  pairwiseDisjoint' := by
    intro a _ b _ hab
    change Disjoint (cellMap f hc a.2 '' ball 0 1) (cellMap f hc b.2 '' ball 0 1)
    rw [Set.disjoint_left]
    intro y hya hyb
    change y ∈ cellMap f hc a.2 '' ball 0 1 at hya
    change y ∈ cellMap f hc b.2 '' ball 0 1 at hyb
    rw [cellMap_image_ball] at hya hyb
    obtain ⟨he, hI⟩ := cell_indices_unique f hya hyb
    exact hab (sigmaCell_label_injective f (Prod.ext he hI))
  mapsTo' d c := by
    let F : (ι → ℤ) × Set ι → Prop := fun p =>
      ∃ y ∈ closedCell f c.val.1 c.val.2, y ∈ cell f p.1 p.2
    have hF : Set.Finite {p | F p} := finite_labels_meeting_closedCell f c.val.1 c.val.2
    have hfinite (m : ℕ) : Set.Finite {q : Cell f m | F q.val} :=
      Set.Finite.preimage (f := Subtype.val) Subtype.val_injective.injOn hF
    refine ⟨fun m => (hfinite m).toFinset, ?_⟩
    intro z hz
    have hy : cellMap f hc c z ∈
        closedCell f c.val.1 c.val.2 \ cell f c.val.1 c.val.2 := by
      rw [← cellMap_image_sphere f hc c]
      exact ⟨z, hz, rfl⟩
    let y := cellMap f hc c z
    let m := Module.finrank ℝ (cellDirection f (integralIndices f y))
    let q : Cell f m := ⟨(ceilingVector f y, integralIndices f y),
      ⟨y, mem_cell_self f y⟩, rfl⟩
    have hm : m < d := by
      rw [← c.property.2]
      exact boundary_finrank_lt f c.val.1 c.val.2 (cellCenter_mem f c) hy.1 hy.2
    refine mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨hm,
      mem_iUnion.mpr ⟨q, mem_iUnion.mpr ⟨?_, ?_⟩⟩⟩⟩
    · exact (hfinite m).mem_toFinset.mpr ⟨y, hy.1, mem_cell_self f y⟩
    · change y ∈ cellMap f hc q '' closedBall 0 1
      rw [cellMap_image_closedBall]
      exact cell_subset_closedCell f _ _ (mem_cell_self f y)
  closed' A _ hA := by
    let C : (Σ d, Cell f d) → Set E := fun c => closedCell f c.2.val.1 c.2.val.2
    have hloc : LocallyFinite C :=
      (closedCells_locallyFinite f (fun i => (f i).continuous_of_finiteDimensional)).comp_injective
        (sigmaCell_label_injective f)
    have hcov : (⋃ c, A ∩ C c) = A := by
      apply Subset.antisymm
      · exact iUnion_subset fun _ => inter_subset_left
      · intro y hy
        let q : Cell f (Module.finrank ℝ (cellDirection f (integralIndices f y))) :=
          ⟨(ceilingVector f y, integralIndices f y), ⟨y, mem_cell_self f y⟩, rfl⟩
        exact mem_iUnion.mpr ⟨⟨_, q⟩, hy, cell_subset_closedCell f _ _ (mem_cell_self f y)⟩
    rw [← hcov]
    apply (hloc.subset (fun _ => inter_subset_right)).isClosed_iUnion
    intro c
    have h := hA c.1 c.2
    change IsClosed (A ∩ cellMap f hc c.2 '' closedBall 0 1) at h
    simpa only [cellMap_image_closedBall, C] using h
  union' := by
    apply Set.eq_univ_of_forall
    intro y
    let q : Cell f (Module.finrank ℝ (cellDirection f (integralIndices f y))) :=
      ⟨(ceilingVector f y, integralIndices f y), ⟨y, mem_cell_self f y⟩, rfl⟩
    refine mem_iUnion.mpr ⟨_, mem_iUnion.mpr ⟨q, ?_⟩⟩
    change y ∈ cellMap f hc q '' closedBall 0 1
    rw [cellMap_image_closedBall]
    exact cell_subset_closedCell f _ _ (mem_cell_self f y)

/-- The integral arrangement augmented by coordinate hyperplanes is a genuine
CW structure in every dimension, including dimension zero. -/
@[instance_reducible]
def augmentedArrangementCWComplex {n s : ℕ} (A : Fin s → Fin n → ℤ) :
    Topology.CWComplex (Set.univ : Set (Fin n → ℝ)) :=
  arrangementCWComplex (augmentedForms A) (closedCell_isCompact A)

end ToricPower.IntegralArrangement

end
end ArrangementSource3

section ArrangementSource4




/-! # Literal monomial-weight subcomplexes

Only the selected forms impose monomial inequalities; extra coordinate
hyperplanes merely subdivide the space. Thus the augmented arrangement works
also when the original ray forms do not span. The subcomplex carrier is proved
to be the actual convex weight polyhedron.

Candidate until an ordinary compiler pass succeeds.
-/

@[expose] public noncomputable section

open Set Topology

namespace ToricPower.IntegralArrangement

universe u

variable {E ι : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite ι]

def weightRegionOn (f : ι → E →ₗ[ℝ] ℝ) (J : Set ι) (l : ι → ℤ) : Set E :=
  {x | ∀ i ∈ J, f i x ≤ (l i : ℝ)}

theorem weightRegionOn_convex (f : ι → E →ₗ[ℝ] ℝ) (J : Set ι) (l : ι → ℤ) :
    Convex ℝ (weightRegionOn f J l) := by
  intro x hx y hy a b ha hb hab i hi
  have hxi := hx i hi
  have hyi := hy i hi
  simp only [map_add, map_smul, smul_eq_mul]
  calc
    a * f i x + b * f i y ≤ a * (l i : ℝ) + b * (l i : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hxi ha) (mul_le_mul_of_nonneg_left hyi hb)
    _ = (l i : ℝ) := by rw [← add_mul, hab, one_mul]

theorem mem_weightRegionOn_iff (f : ι → E →ₗ[ℝ] ℝ) (J : Set ι)
    (l : ι → ℤ) (x : E) :
    x ∈ weightRegionOn f J l ↔ ∀ i ∈ J, 0 ≤ l i - ceilingVector f x i := by
  simp only [weightRegionOn, mem_ofPred_eq, ceilingVector, sub_nonneg, Int.ceil_le]

theorem closedCell_subset_weightRegionOn (f : ι → E →ₗ[ℝ] ℝ)
    (J : Set ι) (l e : ι → ℤ) (I : Set ι) (he : ∀ i ∈ J, e i ≤ l i) :
    closedCell f e I ⊆ weightRegionOn f J l := by
  intro x hx i hi
  have hxi : f i x ≤ (e i : ℝ) := by
    have h := hx i
    by_cases hI : i ∈ I
    · simp only [ite_eq_left hI] at h
      exact h.le
    · exact (show (e i : ℝ)-1 ≤ f i x ∧ f i x ≤ (e i : ℝ) by
        simpa only [ite_eq_right hI] using h).2
  exact hxi.trans (by exact_mod_cast he i hi)

variable (f : ι → E →ₗ[ℝ] ℝ) (hc : ∀ e I, IsCompact (closedCell f e I))

/-- The actual CW subcomplex selected by nonnegative monomial exponents. -/
def weightSubcomplex (J : Set ι) (l : ι → ℤ) :
    letI : CWComplex (univ : Set E) := arrangementCWComplex f hc
    CWComplex.Subcomplex (univ : Set E) := by
  letI : CWComplex (univ : Set E) := arrangementCWComplex f hc
  exact CWComplex.Subcomplex.mk' univ (weightRegionOn f J l)
    (fun _ => {c | ∀ i ∈ J, c.val.1 i ≤ l i})
    (by
      intro d c
      change cellMap f hc c.val '' Metric.closedBall 0 1 ⊆ _
      rw [cellMap_image_closedBall]
      exact closedCell_subset_weightRegionOn f J l c.val.val.1 c.val.val.2 c.property)
    (by
      apply Subset.antisymm
      · intro y hy
        obtain ⟨d, hd⟩ := mem_iUnion.mp hy
        rcases mem_iUnion.mp hd with ⟨c, hy⟩
        change y ∈ cellMap f hc c.val '' Metric.ball 0 1 at hy
        rw [cellMap_image_ball] at hy
        exact closedCell_subset_weightRegionOn f J l c.val.val.1 c.val.val.2
          c.property (cell_subset_closedCell f _ _ hy)
      · intro y hy
        let q : Cell f (Module.finrank ℝ (cellDirection f (integralIndices f y))) :=
          ⟨(ceilingVector f y, integralIndices f y), ⟨y, mem_cell_self f y⟩, rfl⟩
        have hq : ∀ i ∈ J, q.val.1 i ≤ l i := by
          intro i hi
          exact Int.ceil_le.mpr (hy i hi)
        refine mem_iUnion.mpr ⟨_, mem_iUnion.mpr ⟨⟨q, hq⟩, ?_⟩⟩
        change y ∈ cellMap f hc q '' Metric.ball 0 1
        rw [cellMap_image_ball]
        exact mem_cell_self f y)

@[simp]
theorem weightSubcomplex_coe (J : Set ι) (l : ι → ℤ) :
    (weightSubcomplex f hc J l : Set E) = weightRegionOn f J l := rfl

/-- Nonempty weight pieces are contractible as actual topological spaces. -/
theorem weightSubcomplex_contractible (J : Set ι) (l : ι → ℤ)
    (hne : (weightRegionOn f J l).Nonempty) :
    ContractibleSpace (weightSubcomplex f hc J l : Set E) :=
  (weightRegionOn_convex f J l).contractibleSpace hne

/-- For the augmented arrangement only the original integer rows constrain
the weight. The additional coordinate rows are geometrically inert. -/
theorem augmented_weightRegionOn {n s : ℕ} (A : Fin s → Fin n → ℤ)
    (l : Fin s → ℤ) :
    weightRegionOn (augmentedForms A) (Set.range Sum.inl)
      (Sum.elim l (fun _ => 0)) = weightRegion (integralRowForm A) l := by
  ext x
  constructor
  · intro hx i
    simpa only [augmentedForms, Sum.elim_inl] using hx (.inl i) ⟨i, rfl⟩
  · rintro hx _ ⟨i, rfl⟩
    simpa only [augmentedForms, Sum.elim_inl] using hx i

end ToricPower.IntegralArrangement

end
end ArrangementSource4

