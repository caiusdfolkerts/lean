module

public import VolumePolynomials.PlanarExtrusion
public import VolumePolynomials.Definitions
public import Mathlib.Tactic.Abel

@[expose] public section
set_option autoImplicit false

/-! # Removing an actual horizontal segment from a planar convex body

The eroded set is the literal intersection of the body with its translate
by the negative segment endpoint. If the bottom and top support faces each
contain a horizontal segment of length `r`, convexity supplies such a
segment in every nonempty horizontal fiber. Compact interval fibers then
prove the exact Minkowski decomposition, including zero height and `r = 0`.
-/

noncomputable section
open Set
open scoped Pointwise

namespace VolumePolynomials.PlanarErosion

open PlanarExtrusion

def erosion (C : Set (ℝ × ℝ)) (r : ℝ) : Set (ℝ × ℝ) :=
  {p | p ∈ C ∧ p + (r, 0) ∈ C}

theorem erosion_subset (C : Set (ℝ × ℝ)) (r : ℝ) : erosion C r ⊆ C :=
  fun _ hp => hp.1

theorem erosion_compact {C : Set (ℝ × ℝ)} (hC : IsCompact C) (r : ℝ) :
    IsCompact (erosion C r) := by
  first
  | exact hC.inter_right (hC.isClosed.preimage (continuous_id.add continuous_const))

theorem erosion_convex {C : Set (ℝ × ℝ)} (hC : Convex ℝ C) (r : ℝ) :
    Convex ℝ (erosion C r) := by
  first
  | intro x hx y hy a b ha hb hab
    refine ⟨hC hx.1 hy.1 ha hb hab, ?_⟩
    have h := hC hx.2 hy.2 ha hb hab
    have he : a • (x + (r, 0)) + b • (y + (r, 0)) =
        (a • x + b • y) + (r, 0) := by
      rw [smul_add, smul_add]
      calc
        _ = (a • x + b • y) + (a • (r, 0) + b • (r, 0)) := by abel
        _ = _ := by rw [← add_smul, hab, one_smul]
    rwa [he] at h

theorem fiber_erosion (C : Set (ℝ × ℝ)) (r y : ℝ) :
    fiber (erosion C r) y = fiber C y ∩ {x : ℝ | x + r ∈ fiber C y} := by
  first
  | ext x
    change ((x, y) ∈ C ∧ (x, y) + (r, 0) ∈ C) ↔
      ((x, y) ∈ C ∧ (x + r, y) ∈ C)
    simp only [Prod.mk_add_mk, add_zero]

theorem fiber_erosion_eq_interval {C : Set (ℝ × ℝ)} {a b r y : ℝ}
    (hr : 0 ≤ r) (hI : fiber C y = Icc a b) :
    fiber (erosion C r) y = Icc a (b - r) := by
  first
  | rw [fiber_erosion, hI]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨ha, hb⟩, ⟨har, hbr⟩⟩
      exact ⟨ha, by linarith⟩
    · rintro ⟨ha, hb⟩
      exact ⟨⟨ha, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- A segment in each nonempty fiber is sufficient for the exact erosion
identity; compactness and convexity identify all fibers as closed intervals. -/
theorem eq_erosion_add_horizontal_of_fiber_segments
    {C : Set (ℝ × ℝ)} (hC : IsCompact C) (hc : Convex ℝ C) {r : ℝ} (hr : 0 ≤ r)
    (hsegments : ∀ y ∈ projection C, ∃ a : ℝ, (a, y) ∈ C ∧ (a + r, y) ∈ C) :
    C = erosion C r + horizontal r := by
  first
  | ext p
    rcases p with ⟨x, y⟩
    change x ∈ fiber C y ↔ x ∈ fiber (erosion C r + horizontal r) y
    rw [fiber_add_horizontal]
    by_cases hne : (fiber C y).Nonempty
    · have hcompact := fiber_compact hC y
      have hI : fiber C y = Icc (sInf (fiber C y)) (sSup (fiber C y)) :=
        eq_Icc_of_connected_compact
          ⟨hne, Real.convex_iff_isPreconnected.mp (fiber_convex hc y)⟩ hcompact
      obtain ⟨a, ha, har⟩ := hsegments y ((fiber_nonempty_iff C y).mp hne)
      have hlo : sInf (fiber C y) ≤ a := csInf_le hcompact.bddBelow ha
      have hhi : a + r ≤ sSup (fiber C y) := le_csSup hcompact.bddAbove har
      have hwidth : sInf (fiber C y) ≤ sSup (fiber C y) - r := by linarith
      rw [fiber_erosion_eq_interval hr hI, Icc_add_Icc hwidth hr]
      simp only [add_zero, sub_add_cancel]
      exact Iff.mp Set.ext_iff hI x
    · have hI : fiber C y = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have hE : fiber (erosion C r) y = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro z hz
        exact hne ⟨z, hz.1⟩
      simp only [hI, hE, Set.empty_add]

/-- The two extreme horizontal segments interpolate to a segment in every
intermediate horizontal slice. No positive-height hypothesis is needed. -/
theorem fiber_segment_of_extreme_endpoints
    {C : Set (ℝ × ℝ)} (hc : Convex ℝ C)
    {lo hi r a b y : ℝ} (hy : lo ≤ y ∧ y ≤ hi)
    (ha : (a, lo) ∈ C) (har : (a + r, lo) ∈ C)
    (hb : (b, hi) ∈ C) (hbr : (b + r, hi) ∈ C) :
    ∃ z : ℝ, (z, y) ∈ C ∧ (z + r, y) ∈ C := by
  first
  | by_cases heq : lo = hi
    · have hylo : y = lo := by linarith
      subst y
      exact ⟨a, ha, har⟩
    · have hheight : 0 < hi - lo := by
        have hle := hy.1.trans hy.2
        exact sub_pos.mpr (lt_of_le_of_ne hle heq)
      let t : ℝ := (y - lo) / (hi - lo)
      have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hy.1) hheight.le
      have ht1 : t ≤ 1 := (div_le_one hheight).mpr (by linarith)
      have hty : t * (hi - lo) = y - lo := div_mul_cancel₀ _ hheight.ne'
      let z : ℝ := (1 - t) * a + t * b
      have hpoint : ((1 - t) • (a, lo) + t • (b, hi) : ℝ × ℝ) = (z, y) := by
        apply Prod.ext
        · rfl
        · change (1 - t) * lo + t * hi = y
          nlinarith [hty]
      have hpointR : ((1 - t) • (a + r, lo) + t • (b + r, hi) : ℝ × ℝ) = (z + r, y) := by
        apply Prod.ext
        · change (1 - t) * (a + r) + t * (b + r) = z + r
          dsimp only [z]
          ring
        · change (1 - t) * lo + t * hi = y
          nlinarith [hty]
      refine ⟨z, ?_, ?_⟩
      · exact hpoint ▸ hc ha hb (sub_nonneg.mpr ht1) ht0 (by ring)
      · exact hpointR ▸ hc har hbr (sub_nonneg.mpr ht1) ht0 (by ring)

theorem eq_erosion_add_horizontal_of_vertical_bounds
    {C : Set (ℝ × ℝ)} (hC : IsCompact C) (hc : Convex ℝ C)
    {lo hi r : ℝ} (hr : 0 ≤ r)
    (hbound : ∀ p ∈ C, lo ≤ p.2 ∧ p.2 ≤ hi)
    (hlo : ∃ a : ℝ, (a, lo) ∈ C ∧ (a + r, lo) ∈ C)
    (hhi : ∃ b : ℝ, (b, hi) ∈ C ∧ (b + r, hi) ∈ C) :
    C = erosion C r + horizontal r := by
  first
  | apply eq_erosion_add_horizontal_of_fiber_segments hC hc hr
    intro y hy
    obtain ⟨p, hp, hpy⟩ := hy
    obtain ⟨a, ha, har⟩ := hlo
    obtain ⟨b, hb, hbr⟩ := hhi
    exact fiber_segment_of_extreme_endpoints hc (hpy ▸ hbound p hp) ha har hb hbr

/-- The support-face formulation, with the actual minimum and maximum of
the vertical projection. These hypotheses say precisely that both horizontal
support faces contain a translate of the segment being removed. -/
theorem eq_erosion_add_horizontal_of_extreme_fibers
    {C : Set (ℝ × ℝ)} (hC : IsCompact C) (hc : Convex ℝ C) (hne : C.Nonempty)
    {r : ℝ} (hr : 0 ≤ r)
    (hlo : ∃ a : ℝ, (a, sInf (projection C)) ∈ C ∧ (a + r, sInf (projection C)) ∈ C)
    (hhi : ∃ b : ℝ, (b, sSup (projection C)) ∈ C ∧ (b + r, sSup (projection C)) ∈ C) :
    C = erosion C r + horizontal r := by
  first
  | have hprojection : IsCompact (projection C) := hC.image continuous_snd
    apply eq_erosion_add_horizontal_of_vertical_bounds hC hc hr _ hlo hhi
    intro p hp
    have hmem : p.2 ∈ projection C := ⟨p, hp, rfl⟩
    exact ⟨csInf_le hprojection.bddBelow hmem, le_csSup hprojection.bddAbove hmem⟩

def erosionBody (C : ConvexBody (ℝ × ℝ)) (r : ℝ) (hne : (erosion (C : Set _) r).Nonempty) :
    ConvexBody (ℝ × ℝ) where
  carrier := erosion (C : Set _) r
  convex' := erosion_convex C.convex r
  isCompact' := erosion_compact C.isCompact r
  nonempty' := hne

theorem erosion_nonempty_of_bottom_segment
    {C : Set (ℝ × ℝ)} {r : ℝ}
    (hlo : ∃ a : ℝ, (a, sInf (projection C)) ∈ C ∧ (a + r, sInf (projection C)) ∈ C) :
    (erosion C r).Nonempty := by
  first
  | obtain ⟨a, ha, har⟩ := hlo
    refine ⟨(a, sInf (projection C)), ha, ?_⟩
    simpa only [Prod.mk_add_mk, add_zero] using har

end VolumePolynomials.PlanarErosion
