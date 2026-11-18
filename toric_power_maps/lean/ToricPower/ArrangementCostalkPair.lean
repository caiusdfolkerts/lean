module

public import ToricPower.ArrangementCore
public import ToricPower.ArrangementCostalkGeometry
public import ToricPower.CWRelativeSubcomplex

/-!
# The actual relative CW pair for an arrangement costalk

Integral strict inequalities are constant on each open arrangement cell.
Consequently the complement of the literal costalk region is a CW
subcomplex. Placing this complement in the base produces the relative CW
structure whose remaining cells are precisely the cells in the open
costalk region. This keeps the original characteristic maps and incidence
orientations; no new cellular differential is postulated.
-/

@[expose] public noncomputable section

open Set Topology
open scoped Classical

namespace ToricPower.IntegralArrangement

section Linear

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E]

/-- Membership in the set depends only on the actual open arrangement cell. -/
def Cellwise (f : ι → E →ₗ[ℝ] ℝ) (S : Set E) : Prop :=
  ∀ (e : ι → ℤ) (I : Set ι) ⦃x y : E⦄,
    x ∈ cell f e I → y ∈ cell f e I → (x ∈ S ↔ y ∈ S)

theorem Cellwise.compl {f : ι → E →ₗ[ℝ] ℝ} {S : Set E}
    (h : Cellwise f S) : Cellwise f Sᶜ := by
  intro e I x y hx hy
  exact not_congr (h e I hx hy)

theorem Cellwise.inter {f : ι → E →ₗ[ℝ] ℝ} {S T : Set E}
    (hS : Cellwise f S) (hT : Cellwise f T) : Cellwise f (S ∩ T) := by
  intro e I x y hx hy
  exact and_congr (hS e I hx hy) (hT e I hx hy)

private theorem strictBelow_of_sameCell (f : ι → E →ₗ[ℝ] ℝ)
    (e : ι → ℤ) (I : Set ι) {x y : E}
    (hx : x ∈ cell f e I) (hy : y ∈ cell f e I)
    (i : ι) (a : ℤ) (bound : f i x < (a : ℝ)) : f i y < (a : ℝ) := by
  by_cases integral : i ∈ I
  · have hx' := hx i
    have hy' := hy i
    simp only [if_pos integral] at hx' hy'
    rwa [hy', ← hx']
  · have hy' := hy i
    simp only [if_neg integral] at hy'
    have ceiling_bound : e i ≤ a := by
      rw [← ceil_eq_of_mem_cell f e I hx i]
      exact Int.ceil_le.mpr bound.le
    exact hy'.2.trans_le (by exact_mod_cast ceiling_bound)

private theorem strictAbove_of_sameCell (f : ι → E →ₗ[ℝ] ℝ)
    (e : ι → ℤ) (I : Set ι) {x y : E}
    (hx : x ∈ cell f e I) (hy : y ∈ cell f e I)
    (i : ι) (a : ℤ) (bound : (a : ℝ) < f i x) : (a : ℝ) < f i y := by
  by_cases integral : i ∈ I
  · have hx' := hx i
    have hy' := hy i
    simp only [if_pos integral] at hx' hy'
    rwa [hy', ← hx']
  · have hx' := hx i
    have hy' := hy i
    simp only [if_neg integral] at hx' hy'
    have integer_bound : a < e i := by exact_mod_cast bound.trans hx'.2
    have real_bound : (a : ℝ) ≤ (e i : ℝ) - 1 := by
      have : a ≤ e i - 1 := by omega
      exact_mod_cast this
    exact real_bound.trans_lt hy'.1

/-- The original and the extra coordinate hyperplanes are treated uniformly. -/
theorem localStar_cellwise (f : ι → E →ₗ[ℝ] ℝ) (p : E) :
    Cellwise f (localStar f p) := by
  intro e I x y hx hy
  suffices transfer : ∀ ⦃a b : E⦄, a ∈ cell f e I → b ∈ cell f e I →
      a ∈ localStar f p → b ∈ localStar f p from
    ⟨transfer hx hy, transfer hy hx⟩
  intro a b ha hb inStar i
  constructor
  · have lower : ((⌈f i p⌉ - 1 : ℤ) : ℝ) < f i a := by
      simpa only [Int.cast_sub, Int.cast_one] using (inStar i).1
    simpa only [Int.cast_sub, Int.cast_one] using
      strictAbove_of_sameCell f e I ha hb i (⌈f i p⌉ - 1) lower
  · by_cases integral : f i p = (⌈f i p⌉ : ℝ)
    · have upper : ((⌈f i p⌉ + 1 : ℤ) : ℝ) > f i a := by
        simpa only [if_pos integral, Int.cast_add, Int.cast_one] using (inStar i).2
      simpa only [if_pos integral, Int.cast_add, Int.cast_one] using
        strictBelow_of_sameCell f e I ha hb i (⌈f i p⌉ + 1) upper
    · have upper : (⌈f i p⌉ : ℝ) > f i a := by
        simpa only [if_neg integral, add_zero] using (inStar i).2
      simpa only [if_neg integral, add_zero] using
        strictBelow_of_sameCell f e I ha hb i ⌈f i p⌉ upper

theorem openWeightRegion_cellwise (f : ι → E →ₗ[ℝ] ℝ)
    (selected : Set ι) (weight : ι → ℤ) :
    Cellwise f (openWeightRegion f selected weight) := by
  intro e I x y hx hy
  suffices transfer : ∀ ⦃a b : E⦄, a ∈ cell f e I → b ∈ cell f e I →
      a ∈ openWeightRegion f selected weight → b ∈ openWeightRegion f selected weight from
    ⟨transfer hx hy, transfer hy hx⟩
  intro a b ha hb inWeight i selected_i
  have upper : f i a < ((weight i + 1 : ℤ) : ℝ) := by
    simpa only [Int.cast_add, Int.cast_one] using inWeight i selected_i
  simpa only [Int.cast_add, Int.cast_one] using
    strictBelow_of_sameCell f e I ha hb i (weight i + 1) upper

theorem costalkRegion_cellwise (f : ι → E →ₗ[ℝ] ℝ)
    (selected : Set ι) (weight : ι → ℤ) (x : E) :
    Cellwise f (costalkRegion f selected weight x) :=
  (localStar_cellwise f x).inter (openWeightRegion_cellwise f selected weight)

end Linear

section CW

universe u

variable {E ι : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite ι]
  (f : ι → E →ₗ[ℝ] ℝ) (hc : ∀ e I, IsCompact (closedCell f e I))

/-- A closed union of literal arrangement cells, as an actual CW subcomplex. -/
def cellwiseSubcomplex (S : Set E) (closed : IsClosed S) (cellwise : Cellwise f S) :
    letI : CWComplex (univ : Set E) := arrangementCWComplex f hc
    CWComplex.Subcomplex (univ : Set E) := by
  letI : CWComplex (univ : Set E) := arrangementCWComplex f hc
  refine ⟨S, (fun d => {c : Cell f d | cellCenter f c ∈ S}), closed, ?_⟩
  rw [empty_union]
  apply Subset.antisymm
  · intro x hx
    obtain ⟨d, hx⟩ := mem_iUnion.mp hx
    obtain ⟨c, hx⟩ := mem_iUnion.mp hx
    change x ∈ cellMap f hc c.val '' Metric.ball 0 1 at hx
    rw [cellMap_image_ball] at hx
    exact (cellwise c.val.val.1 c.val.val.2 (cellCenter_mem f c.val) hx).mp c.property
  · intro x hx
    let c : Cell f (Module.finrank ℝ (cellDirection f (integralIndices f x))) :=
      ⟨(ceilingVector f x, integralIndices f x), ⟨x, mem_cell_self f x⟩, rfl⟩
    have center_mem : cellCenter f c ∈ S :=
      (cellwise c.val.1 c.val.2 (mem_cell_self f x) (cellCenter_mem f c)).mp hx
    refine mem_iUnion.2 ⟨_, mem_iUnion.2 ⟨⟨c, center_mem⟩, ?_⟩⟩
    change x ∈ cellMap f hc c '' Metric.ball 0 1
    rw [cellMap_image_ball]
    exact mem_cell_self f x

/-- The closed complement of the open costalk region is an actual subcomplex. -/
def costalkComplementSubcomplex (selected : Set ι) (weight : ι → ℤ) (x : E) :
    letI : CWComplex (univ : Set E) := arrangementCWComplex f hc
    CWComplex.Subcomplex (univ : Set E) :=
  cellwiseSubcomplex f hc (costalkRegion f selected weight x)ᶜ
    (costalkRegion_isOpen f selected weight x).isClosed_compl
    (costalkRegion_cellwise f selected weight x).compl

/-- The pair `(E,E \ U)` for the literal costalk region `U`, with the
inherited characteristic maps. -/
@[instance_reducible]
def costalkRelativeCWComplex (selected : Set ι) (weight : ι → ℤ) (x : E) :
    RelCWComplex (univ : Set E) (costalkRegion f selected weight x)ᶜ := by
  letI : CWComplex (univ : Set E) := arrangementCWComplex f hc
  exact ToricPower.relativeToSubcomplex (costalkComplementSubcomplex f hc selected weight x)

end CW
end ToricPower.IntegralArrangement
