module

public import ToricPower.ArrangementPeriodicity
public import Mathlib.Tactic.Abel

/-! # Characteristic maps compatible with the literal lattice translations

The normalized representative of a cell determines its characteristic map;
the map of any translate is obtained by translating that map. Consequently
the lattice action preserves the chosen disk parameter, including its
orientation. No invariance of incidence signs is assumed as data.

Candidate until an ordinary successful compiler check.
-/

@[expose] public noncomputable section

open scoped Classical
open Set Function Topology Metric

namespace ToricPower

section ReplaceMaps

variable {E : Type*} [TopologicalSpace E] {C : Set E} [CWComplex C]

/-- Reparametrize an actual CW structure while preserving each open cell,
closed cell and attaching image. The topology and cell indices are unchanged. -/
@[instance_reducible]
def replaceCWMaps
    (q : ∀ d, Topology.RelCWComplex.cell C d → PartialEquiv (Fin d → ℝ) E)
    (hsource : ∀ d c, (q d c).source = ball 0 1)
    (hcont : ∀ d c, ContinuousOn (q d c) (closedBall 0 1))
    (hinv : ∀ d c, ContinuousOn (q d c).symm (q d c).target)
    (hball : ∀ d c, q d c '' ball 0 1 = Topology.RelCWComplex.openCell d c)
    (hclosed : ∀ d c, q d c '' closedBall 0 1 = Topology.RelCWComplex.closedCell d c)
    (hsphere : ∀ d c, q d c '' sphere 0 1 = Topology.RelCWComplex.cellFrontier d c) :
    CWComplex C where
  cell := Topology.RelCWComplex.cell C
  map := q
  source_eq := hsource
  continuousOn := hcont
  continuousOn_symm := hinv
  pairwiseDisjoint' := by
    simpa only [hball] using (CWComplex.pairwiseDisjoint (C := C))
  mapsTo' d c := by
    obtain ⟨I, hI⟩ := CWComplex.cellFrontier_subset_finite_closedCell (C := C) d c
    refine ⟨I, ?_⟩
    intro z hz
    have hmem : q d c z ∈ Topology.RelCWComplex.cellFrontier d c := by
      rw [← hsphere]
      exact ⟨z, hz, rfl⟩
    simpa only [hclosed] using hI hmem
  closed' A hAC hA := by
    apply CWComplex.closed' A hAC
    intro d c
    change IsClosed (A ∩ Topology.RelCWComplex.closedCell (C := C) d c)
    simpa only [hclosed] using hA d c
  union' := by
    simpa only [hclosed] using (CWComplex.union (C := C))

end ReplaceMaps

namespace IntegralArrangement

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E]

theorem add_mem_closedCell_iff (f : ι → E →ₗ[ℝ] ℝ)
    (e k : ι → ℤ) (I : Set ι) (z : E) (hz : ∀ i, f i z = (k i : ℝ)) (x : E) :
    x + z ∈ closedCell f (e + k) I ↔ x ∈ closedCell f e I := by
  constructor <;> intro hx i
  all_goals
    have h := hx i
    simp only [map_add, hz, Pi.add_apply, Int.cast_add] at h ⊢
    by_cases hi : i ∈ I
    · simp only [if_pos hi] at h ⊢
      linarith
    · simp only [if_neg hi] at h ⊢
      constructor <;> linarith [h.1, h.2]

theorem add_image_cell (f : ι → E →ₗ[ℝ] ℝ) (e k : ι → ℤ)
    (I : Set ι) (z : E) (hz : ∀ i, f i z = (k i : ℝ)) :
    (fun x => x + z) '' cell f e I = cell f (e + k) I := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (add_mem_cell_iff f e k I z hz x).mpr hx
  · intro hy
    refine ⟨y-z, ?_, sub_add_cancel y z⟩
    apply (add_mem_cell_iff f e k I z hz (y-z)).mp
    simpa only [sub_add_cancel] using hy

theorem add_image_closedCell (f : ι → E →ₗ[ℝ] ℝ) (e k : ι → ℤ)
    (I : Set ι) (z : E) (hz : ∀ i, f i z = (k i : ℝ)) :
    (fun x => x + z) '' closedCell f e I = closedCell f (e + k) I := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (add_mem_closedCell_iff f e k I z hz x).mpr hx
  · intro hy
    refine ⟨y-z, ?_, sub_add_cancel y z⟩
    apply (add_mem_closedCell_iff f e k I z hz (y-z)).mp
    simpa only [sub_add_cancel] using hy

section IntegralCoordinates

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

@[simp]
theorem latticeLift_add (z w : Fin n → ℤ) :
    latticeLift (z+w) = latticeLift z + latticeLift w := by
  funext j
  simp only [latticeLift, Pi.add_apply, Int.cast_add]

theorem translate_normalizeCell {d : ℕ} (c : Cell (augmentedForms A) d) :
    translateCell A (coordinateCeilings A c) (normalizeCell A c).val = c :=
  (cellOrbitEquiv A d).left_inv c

@[simp]
theorem normalizeCell_translate (z : Fin n → ℤ) {d : ℕ}
    (c : Cell (augmentedForms A) d) :
    normalizeCell A (translateCell A z c) = normalizeCell A c := by
  apply Subtype.ext
  change translateCell A (-coordinateCeilings A (translateCell A z c))
    (translateCell A z c) = translateCell A (-coordinateCeilings A c) c
  rw [coordinateCeilings_translateCell, translateCell_add]
  congr 1
  abel

/-- The characteristic map chosen on a representative is translated to
every other cell in its actual lattice orbit. -/
def periodicCellMap {d : ℕ} (c : Cell (augmentedForms A) d) (v : Fin d → ℝ) :
    Fin n → ℝ :=
  cellMap (augmentedForms A) (closedCell_isCompact A) (normalizeCell A c).val v +
    latticeLift (coordinateCeilings A c)

theorem periodicCellMap_isEmbedding {d : ℕ} (c : Cell (augmentedForms A) d) :
    Topology.IsEmbedding (periodicCellMap A c) :=
  (Homeomorph.addRight (latticeLift (coordinateCeilings A c))).isEmbedding.comp
    (cellMap_isEmbedding (augmentedForms A) (closedCell_isCompact A) (normalizeCell A c).val)

theorem periodicCellMap_image_ball {d : ℕ} (c : Cell (augmentedForms A) d) :
    periodicCellMap A c '' ball 0 1 = cell (augmentedForms A) c.val.1 c.val.2 := by
  change ((fun x => x + latticeLift (coordinateCeilings A c)) ∘
    cellMap (augmentedForms A) (closedCell_isCompact A) (normalizeCell A c).val) '' _ = _
  rw [image_comp, cellMap_image_ball, add_image_cell _ _ _ _ _
    (augmentedForms_latticeLift A (coordinateCeilings A c))]
  exact congrArg (fun q : Cell (augmentedForms A) d => cell (augmentedForms A) q.val.1 q.val.2)
    (translate_normalizeCell A c)

theorem periodicCellMap_image_closedBall {d : ℕ} (c : Cell (augmentedForms A) d) :
    periodicCellMap A c '' closedBall 0 1 = closedCell (augmentedForms A) c.val.1 c.val.2 := by
  change ((fun x => x + latticeLift (coordinateCeilings A c)) ∘
    cellMap (augmentedForms A) (closedCell_isCompact A) (normalizeCell A c).val) '' _ = _
  rw [image_comp, cellMap_image_closedBall, add_image_closedCell _ _ _ _ _
    (augmentedForms_latticeLift A (coordinateCeilings A c))]
  exact congrArg (fun q : Cell (augmentedForms A) d =>
    closedCell (augmentedForms A) q.val.1 q.val.2) (translate_normalizeCell A c)

theorem periodicCellMap_image_sphere {d : ℕ} (c : Cell (augmentedForms A) d) :
    periodicCellMap A c '' sphere 0 1 =
      closedCell (augmentedForms A) c.val.1 c.val.2 \ cell (augmentedForms A) c.val.1 c.val.2 := by
  rw [← closedBall_sdiff_ball, image_sdiff (periodicCellMap_isEmbedding A c).injective,
    periodicCellMap_image_closedBall, periodicCellMap_image_ball]

/-- The parameter of the characteristic disk is unchanged by translating
the cell. This is the orientation compatibility needed by incidence maps. -/
theorem periodicCellMap_translate (z : Fin n → ℤ) {d : ℕ}
    (c : Cell (augmentedForms A) d) (v : Fin d → ℝ) :
    periodicCellMap A (translateCell A z c) v = periodicCellMap A c v + latticeLift z := by
  simp only [periodicCellMap, normalizeCell_translate, coordinateCeilings_translateCell,
    latticeLift_add]
  exact (add_assoc _ _ _).symm

def periodicCellPartialEquiv {d : ℕ} (c : Cell (augmentedForms A) d) :
    PartialEquiv (Fin d → ℝ) (Fin n → ℝ) where
  toFun := periodicCellMap A c
  invFun := Function.invFun (periodicCellMap A c)
  source := ball 0 1
  target := periodicCellMap A c '' ball 0 1
  map_source' z hz := ⟨z, hz, rfl⟩
  map_target' := by
    rintro _ ⟨z, hz, rfl⟩
    simpa only [Function.leftInverse_invFun (periodicCellMap_isEmbedding A c).injective z] using hz
  left_inv' z _ := Function.leftInverse_invFun (periodicCellMap_isEmbedding A c).injective z
  right_inv' := by
    rintro _ ⟨z, _, rfl⟩
    exact Function.apply_invFun_apply

/-- The actual universal-cover carrier. Naming the whole Euclidean space
retains the arrangement matrix in dependent CW structure inference. -/
def arrangementCarrier (_A : Fin s → Fin n → ℤ) : Set (Fin n → ℝ) := Set.univ

@[simp]
theorem arrangementCarrier_eq_univ : arrangementCarrier A = Set.univ := rfl

/-- An actual CW structure with literal lattice-equivariant characteristic
maps. Its cells are the original geometric arrangement cells. -/
@[instance_reducible]
def periodicArrangementCWComplex : CWComplex (univ : Set (Fin n → ℝ)) := by
  letI : CWComplex (univ : Set (Fin n → ℝ)) := augmentedArrangementCWComplex A
  apply replaceCWMaps (fun _ c => periodicCellPartialEquiv A c)
  · intros
    rfl
  · intro d c
    exact (periodicCellMap_isEmbedding A c).continuous.continuousOn
  · intro d c
    change ContinuousOn (Function.invFun (periodicCellMap A c)) (periodicCellMap A c '' ball 0 1)
    apply (periodicCellMap_isEmbedding A c).isInducing.continuousOn_image_iff.mpr
    simpa only [Function.invFun_comp (periodicCellMap_isEmbedding A c).injective] using
      (continuous_id.continuousOn : ContinuousOn (id : (Fin d → ℝ) → _) (ball 0 1))
  · intro d c
    change periodicCellMap A c '' ball 0 1 =
      cellMap (augmentedForms A) (closedCell_isCompact A) c '' ball 0 1
    rw [periodicCellMap_image_ball, cellMap_image_ball]
  · intro d c
    change periodicCellMap A c '' closedBall 0 1 =
      cellMap (augmentedForms A) (closedCell_isCompact A) c '' closedBall 0 1
    rw [periodicCellMap_image_closedBall, cellMap_image_closedBall]
  · intro d c
    change periodicCellMap A c '' sphere 0 1 =
      cellMap (augmentedForms A) (closedCell_isCompact A) c '' sphere 0 1
    rw [periodicCellMap_image_sphere, cellMap_image_sphere]

end IntegralCoordinates

end IntegralArrangement

end ToricPower
