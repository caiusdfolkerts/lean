module

public import Projection.RepeatedSegment
public import VolumePapers.WeightedTriangles
public import Mathlib.Data.Fin.VecNotation

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Module
open scoped Pointwise BigOperators Matrix

namespace RankThreeProjection
open VolumePolynomials

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

section Measure
variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

/-- The actual complementary mixed-volume matrix, with the paper's factor
`dim(E) * (dim(E)-1)` when `dim(E)=d+2`. -/
def complementaryMixedMatrix {d : ℕ} (K : ConvexBody E) (U : ι → E) :
    Matrix ι ι ℝ := fun i j =>
  (d + 2 : ℝ) * (d + 1 : ℝ) * mixedVolume volume
    (Fin.cons (centeredSegment (U i))
      (Fin.cons (centeredSegment (U j)) (fun _ : Fin d => K)))

@[simp] theorem complementaryMixedMatrix_diagonal {d : ℕ}
    (K : ConvexBody E) (U : ι → E) (i : ι) :
    complementaryMixedMatrix (d := d) K U i i = 0 := by
  rw [complementaryMixedMatrix, mixedVolume_repeated_segment_zero, mul_zero]

theorem complementaryMixedMatrix_symmetric {d : ℕ}
    (K : ConvexBody E) (U : ι → E) (i j : ι) :
    complementaryMixedMatrix (d := d) K U i j =
      complementaryMixedMatrix (d := d) K U j i := by
  unfold complementaryMixedMatrix
  congr 1
  have he := mixedVolume_reindex volume
    (Fin.cons (centeredSegment (U i))
      (Fin.cons (centeredSegment (U j)) (fun _ : Fin d => K)))
    (Equiv.swap (0 : Fin (d + 2)) 1)
  change mixedVolume volume
    ((Matrix.vecCons (centeredSegment (U i))
      (Matrix.vecCons (centeredSegment (U j)) (fun _ : Fin d => K))) ∘
        Equiv.swap 0 1) = _ at he
  rw [Matrix.cons_cons_comp_swap_zero_one] at he
  exact he.symm

theorem complementaryMixedMatrix_translate {d : ℕ}
    (K : ConvexBody E) (U : ι → E) (v : E) :
    complementaryMixedMatrix (d := d) (translateBody v K) U =
      complementaryMixedMatrix (d := d) K U := by
  funext i j
  unfold complementaryMixedMatrix
  congr 1
  have he := mixedVolume_translate volume
    (Fin.cons (centeredSegment (U i))
      (Fin.cons (centeredSegment (U j)) (fun _ : Fin d => K)))
    (Fin.cons 0 (Fin.cons 0 (fun _ : Fin d => v)))
  convert he using 1
  congr 1
  funext k
  refine Fin.cases ?_ (fun l => ?_) k
  · simp only [Fin.cons_zero, translateBody_zero]
  · refine Fin.cases ?_ (fun m => rfl) l
    simp only [Fin.cons_succ, Fin.cons_zero, translateBody_zero]

section Frame
variable [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F]
  [Measure.IsAddHaarMeasure (volume : Measure F)]

theorem complementaryMixedMatrix_frame {d : ℕ}
    (K : ConvexBody E) (U : ι → E) (T : E ≃L[ℝ] F) (i j : ι) :
    complementaryMixedMatrix (d := d) K U i j =
      (mixedVolumeFrameFactor volume volume T : ℝ) *
        complementaryMixedMatrix (d := d) (mapBody T.toContinuousLinearMap K)
          (fun i => T (U i)) i j := by
  unfold complementaryMixedMatrix
  rw [mixedVolume_eq_frameFactor_mul volume volume T]
  have he :
      (fun k : Fin (d + 2) => mapBody T.toContinuousLinearMap
        ((Fin.cons (centeredSegment (U i))
          (Fin.cons (centeredSegment (U j)) (fun _ : Fin d => K)) :
            Fin (d + 2) → ConvexBody E) k)) =
      (Fin.cons (centeredSegment (T (U i)))
        (Fin.cons (centeredSegment (T (U j)))
          (fun _ : Fin d => mapBody T.toContinuousLinearMap K)) :
            Fin (d + 2) → ConvexBody F) := by
    funext k
    refine Fin.cases ?_ (fun l => ?_) k
    · exact map_centeredSegment _ _
    · refine Fin.cases ?_ (fun m => rfl) l
      exact map_centeredSegment _ _
  rw [he]
  ring

end Frame

/-- A body annihilated by a nonzero functional maps to its actual projection
in the kernel factor. This is set equality, including degenerate bodies. -/
theorem mapBody_frame_eq_embed (K : ConvexBody E)
    (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1)
    (hK : ∀ x ∈ (K : Set E), l x = 0) :
    mapBody (LinearFrame.continuousEquiv l v hv).toContinuousLinearMap K =
      embedHyperplane (mapBody
        ((ContinuousLinearMap.snd ℝ ℝ (LinearMap.ker l.toLinearMap)).comp
          (LinearFrame.continuousEquiv l v hv).toContinuousLinearMap) K) := by
  apply ConvexBody.ext
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(LinearFrame.continuousEquiv l v hv x).2, ⟨x, hx, rfl⟩, ?_⟩
    apply Prod.ext
    · exact (hK x hx).symm
    · rfl
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    apply Prod.ext
    · exact hK x hx
    · rfl

/-- Lemma 5.1's weighted inequalities in every actual hyperplane frame.
The frame's positive Haar factor is retained explicitly during the proof. -/
theorem complementaryMixedMatrix_hyperplane_weighted_triangles
    {d : ℕ} (K : ConvexBody E) (hdim : finrank ℝ E = d + 2)
    (U : ι → E) (l : E →L[ℝ] ℝ) (hl : l ≠ 0)
    (hK : ∀ x ∈ (K : Set E), l x = 0) (i j k : ι) :
    complementaryMixedMatrix (d := d) K U i j * |l (U k)| ≤
      complementaryMixedMatrix (d := d) K U i k * |l (U j)| +
        complementaryMixedMatrix (d := d) K U j k * |l (U i)| := by
  obtain ⟨v, hv⟩ := LinearFrame.exists_unit_value l hl
  let F := LinearMap.ker l.toLinearMap
  letI : MeasureSpace F := ⟨Measure.addHaar⟩
  letI : Measure.IsAddHaarMeasure (volume : Measure F) := by
    change Measure.IsAddHaarMeasure (Measure.addHaar : Measure F)
    infer_instance
  have hF : finrank ℝ F = d + 1 := by
    change finrank ℝ (LinearMap.ker l.toLinearMap) = d + 1
    have he := LinearFrame.finrank_kernel_add_one l v hv
    rw [hdim] at he
    omega
  letI : Nontrivial F := Module.nontrivial_of_finrank_eq_succ hF
  let T : E ≃L[ℝ] ℝ × F := LinearFrame.continuousEquiv l v hv
  let L : ConvexBody F := mapBody
    ((ContinuousLinearMap.snd ℝ ℝ F).comp T.toContinuousLinearMap) K
  let N := segmentMixedVolumeSeminorm volume (fun _ : Fin d => L) hF
  let J : ℝ := mixedVolumeFrameFactor volume volume T
  have hJ : 0 ≤ J := NNReal.coe_nonneg _
  have he (a b : ι) : complementaryMixedMatrix (d := d) K U a b =
      J * N (l (U a) • (T (U b)).2 - l (U b) • (T (U a)).2) := by
    rw [complementaryMixedMatrix_frame K U T,
      mapBody_frame_eq_embed K l v hv hK]
    rw [complementaryMixedMatrix, ← hyperplanePair]
    change J * ((d + 2 : ℝ) * (d + 1 : ℝ) *
      hyperplanePair (d := d) L (T (U a)) (T (U b))) = _
    rw [hyperplanePair_eq_seminorm L hF]
    rfl
  simp_rw [he]
  have ht := seminorm_weighted_triangle N (fun a => l (U a))
    (fun a => (T (U a)).2) i j k
  nlinarith [mul_le_mul_of_nonneg_left ht hJ]

/-- If every mark is tangent to the containing hyperplane, every entry of
the actual complementary mixed-volume matrix vanishes. -/
theorem complementaryMixedMatrix_eq_zero_of_tangent
    {d : ℕ} (K : ConvexBody E) (hdim : finrank ℝ E = d + 2)
    (U : ι → E) (l : E →L[ℝ] ℝ) (hl : l ≠ 0)
    (hK : ∀ x ∈ (K : Set E), l x = 0) (hU : ∀ i, l (U i) = 0) :
    complementaryMixedMatrix (d := d) K U = 0 := by
  obtain ⟨v, hv⟩ := LinearFrame.exists_unit_value l hl
  let F := LinearMap.ker l.toLinearMap
  letI : MeasureSpace F := ⟨Measure.addHaar⟩
  letI : Measure.IsAddHaarMeasure (volume : Measure F) := by
    change Measure.IsAddHaarMeasure (Measure.addHaar : Measure F)
    infer_instance
  let T : E ≃L[ℝ] ℝ × F := LinearFrame.continuousEquiv l v hv
  let L : ConvexBody F := mapBody
    ((ContinuousLinearMap.snd ℝ ℝ F).comp T.toContinuousLinearMap) K
  funext i j
  rw [complementaryMixedMatrix_frame K U T,
    mapBody_frame_eq_embed K l v hv hK]
  unfold complementaryMixedMatrix
  rw [← hyperplanePair]
  have hz : hyperplanePair (d := d) L (T (U i)) (T (U j)) = 0 := by
    have hframe (k : ι) : T (U k) = (l (U k), (T (U k)).2) :=
      Prod.ext (LinearFrame.continuousEquiv_fst l v hv (U k)) rfl
    rw [hframe i, hframe j, hU i, hU j]
    have hf := hyperplanePair_formula (d := d) L
      (l (U i)) (l (U j)) (T (U i)).2 (T (U j)).2
    rw [hU i, hU j, zero_smul, zero_smul, sub_self, centeredSegment_zero,
      mixedVolume_zero_first] at hf
    exact (mul_eq_zero.mp hf).resolve_left (by positivity)
  rw [hz]
  simp

/-- A rank-at-most-three positive hollow matrix on at least five marks cannot
be represented by an actual body in any linear hyperplane. -/
theorem hyperplane_representation_impossible {n d : ℕ} (hn : 5 ≤ n)
    (K : ConvexBody E) (hdim : finrank ℝ E = d + 2) (U : Fin n → E)
    (l : E →L[ℝ] ℝ) (hl : l ≠ 0) (hK : ∀ x ∈ (K : Set E), l x = 0)
    (hpos : ∀ i j, i ≠ j → 0 < complementaryMixedMatrix (d := d) K U i j)
    (hrank : (complementaryMixedMatrix (d := d) K U).rank ≤ 3) : False := by
  let x : Fin n → ℝ := fun i => |l (U i)|
  have hx : ∀ i, 0 ≤ x i := fun i => abs_nonneg _
  have hne : x ≠ 0 := by
    intro hx0
    have hU : ∀ i, l (U i) = 0 := by
      intro i
      exact abs_eq_zero.mp (congrFun hx0 i)
    have hzero := complementaryMixedMatrix_eq_zero_of_tangent K hdim U l hl hK hU
    let i : Fin n := ⟨0, by omega⟩
    let j : Fin n := ⟨1, by omega⟩
    have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i, j] at this
    have hp := hpos i j hij
    rw [hzero] at hp
    exact (lt_irrefl (0 : ℝ)) hp
  apply VolumePapers.RankThree.no_nonnegative_weighted_triangles hn
    (complementaryMixedMatrix (d := d) K U)
    (complementaryMixedMatrix_diagonal K U)
    (complementaryMixedMatrix_symmetric K U) hpos hrank x hx hne
  intro i j k _ _ _
  exact complementaryMixedMatrix_hyperplane_weighted_triangles K hdim U l hl hK i j k

/-- Every lower-dimensional body can be translated into the kernel of an
actual nonzero continuous functional. -/
theorem exists_translate_annihilator (K : ConvexBody E)
    (hdim : finrank ℝ (affineSpan ℝ (K : Set E)).direction < finrank ℝ E) :
    ∃ (p : E) (l : E →L[ℝ] ℝ), l ≠ 0 ∧
      ∀ x ∈ ((translateBody (-p) K : ConvexBody E) : Set E), l x = 0 := by
  let V := (affineSpan ℝ (K : Set E)).direction
  have hV : V < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro he
    have hdim' : finrank ℝ V < finrank ℝ E := hdim
    rw [he, finrank_top] at hdim'
    exact (lt_irrefl _) hdim'
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hV inferInstance
  obtain ⟨p, hp⟩ := K.nonempty
  let l : E →L[ℝ] ℝ := f.toContinuousLinearMap
  refine ⟨p, l, ?_, ?_⟩
  · intro hl
    apply hf
    ext x
    exact congrArg (fun g : E →L[ℝ] ℝ => g x) hl
  · intro x hx
    change x ∈ (translateBody (-p) K : Set E) at hx
    rw [coe_translateBody] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hv : y - p ∈ V := by
      simpa only [vsub_eq_sub] using
        AffineSubspace.vsub_mem_direction
          (subset_affineSpan ℝ (K : Set E) hy)
          (subset_affineSpan ℝ (K : Set E) hp)
    have hz : f (y - p) ∈ V.map f := ⟨y - p, hv, rfl⟩
    rw [hmap, Submodule.mem_bot] at hz
    simpa only [l, LinearMap.coe_toContinuousLinearMap', vadd_eq_add,
      neg_add_eq_sub] using hz

/-- The hyperplane obstruction applies to every non-full-dimensional body,
not just to a chosen coordinate hyperplane or to bodies of codimension one. -/
theorem nonfull_representation_impossible {n d : ℕ} (hn : 5 ≤ n)
    (K : ConvexBody E) (hdim : finrank ℝ E = d + 2) (U : Fin n → E)
    (hK : finrank ℝ (affineSpan ℝ (K : Set E)).direction < finrank ℝ E)
    (hpos : ∀ i j, i ≠ j → 0 < complementaryMixedMatrix (d := d) K U i j)
    (hrank : (complementaryMixedMatrix (d := d) K U).rank ≤ 3) : False := by
  obtain ⟨p, l, hl, hzero⟩ := exists_translate_annihilator K hK
  apply hyperplane_representation_impossible hn (translateBody (-p) K) hdim U l hl hzero
  · simpa only [complementaryMixedMatrix_translate] using hpos
  · simpa only [complementaryMixedMatrix_translate] using hrank

end Measure
end RankThreeProjection
