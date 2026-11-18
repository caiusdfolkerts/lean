module

public import VolumePolynomials.PlanarErosion
public import VolumePolynomials.TriangleExtremeFaces

@[expose] public section
set_option autoImplicit false

/-! # Actual removal of the two coordinate segments -/

noncomputable section
open Set MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.PlanarEdges

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarErosion OAI.Paper092

def vertical (h : ℝ) : Set Plane := {0} ×ˢ Icc 0 h

def verticalErosion (C : Set Plane) (h : ℝ) : Set Plane :=
  {p | p ∈ C ∧ p + (0, h) ∈ C}

theorem swap_add_coordinates (p q : Plane) : (p + q).swap = p.swap + q.swap := rfl

theorem verticalErosion_compact {C : Set Plane} (hC : IsCompact C) (h : ℝ) :
    IsCompact (verticalErosion C h) :=
  hC.inter_right (hC.isClosed.preimage (continuous_id.add continuous_const))

theorem verticalErosion_convex {C : Set Plane} (hC : Convex ℝ C) (h : ℝ) :
    Convex ℝ (verticalErosion C h) := by
  first
  | intro x hx y hy a b ha hb hab
    refine ⟨hC hx.1 hy.1 ha hb hab, ?_⟩
    have hp := hC hx.2 hy.2 ha hb hab
    have he : a • (x + (0, h)) + b • (y + (0, h)) =
        (a • x + b • y) + (0, h) := by
      rw [smul_add, smul_add]
      calc
        _ = (a • x + b • y) + (a • (0, h) + b • (0, h)) := by abel
        _ = _ := by rw [← add_smul, hab, one_smul]
    rwa [he] at hp

theorem eq_verticalErosion_add_of_bounds {C : Set Plane}
    (hC : IsCompact C) (hc : Convex ℝ C) {lo hi h : ℝ} (hh : 0 ≤ h)
    (hbound : ∀ p ∈ C, lo ≤ p.1 ∧ p.1 ≤ hi)
    (hlo : ∃ a : ℝ, (lo, a) ∈ C ∧ (lo, a + h) ∈ C)
    (hhi : ∃ b : ℝ, (hi, b) ∈ C ∧ (hi, b + h) ∈ C) :
    C = verticalErosion C h + vertical h := by
  first
  | let D : Set Plane := Prod.swap '' C
    have hDc : IsCompact D := hC.image continuous_swap
    have hDv : Convex ℝ D := hc.linear_image (LinearEquiv.prodComm ℝ ℝ ℝ).toLinearMap
    have hD := eq_erosion_add_horizontal_of_vertical_bounds hDc hDv hh
      (lo := lo) (hi := hi) (by
        rintro p ⟨q, hq, rfl⟩
        exact hbound q hq)
      (by
        obtain ⟨a, ha, har⟩ := hlo
        exact ⟨a, ⟨(lo, a), ha, rfl⟩, ⟨(lo, a + h), har, rfl⟩⟩)
      (by
        obtain ⟨b, hb, hbr⟩ := hhi
        exact ⟨b, ⟨(hi, b), hb, rfl⟩, ⟨(hi, b + h), hbr, rfl⟩⟩)
    have hswap (p : Plane) : p.swap ∈ D ↔ p ∈ C := by
      constructor
      · rintro ⟨q, hq, he⟩
        have hqp : q = p := by simpa only [Prod.swap_swap] using congrArg Prod.swap he
        exact hqp ▸ hq
      · intro hp
        exact ⟨p, hp, rfl⟩
    ext p
    constructor
    · intro hp
      have hs : p.swap ∈ erosion D h + horizontal h := hD ▸ (hswap p).mpr hp
      obtain ⟨q, hq, r, hr, he⟩ := hs
      have hr0 : r.2 = 0 := hr.2
      refine ⟨q.swap, ⟨(hswap q.swap).mp (by simpa using hq.1), ?_⟩,
        r.swap, ⟨hr0, hr.1⟩, ?_⟩
      · apply (hswap (q.swap + (0, h))).mp
        simpa only [swap_add_coordinates, Prod.swap_swap, Prod.swap_prod_mk] using hq.2
      · have h := congrArg Prod.swap he
        simpa only [swap_add_coordinates, Prod.swap_swap] using h
    · rintro ⟨q, hq, r, hr, rfl⟩
      apply (hswap (q + r)).mp
      rw [hD]
      refine ⟨q.swap, ⟨(hswap q).mpr hq.1, ?_⟩, r.swap, ⟨hr.2, hr.1⟩, ?_⟩
      · have h := (hswap (q + (0, h))).mpr hq.2
        simpa only [swap_add_coordinates, Prod.swap_prod_mk] using h
      · simp only [swap_add_coordinates]

/-- Removing a horizontal summand preserves the left supporting face and
translates the right supporting face by its length. -/
theorem erosion_extreme_vertical_endpoints {C : Set Plane} {r lo hi yl yr : ℝ}
    (hbound : ∀ p ∈ C, lo ≤ p.1 ∧ p.1 ≤ hi)
    (hdecomp : C = erosion C r + horizontal r)
    (hl : (lo, yl) ∈ C) (hr : (hi, yr) ∈ C) :
    (lo, yl) ∈ erosion C r ∧ (hi - r, yr) ∈ erosion C r := by
  first
  | constructor
    · have hp : (lo, yl) ∈ erosion C r + horizontal r := hdecomp ▸ hl
      obtain ⟨q, hq, v, hv, he⟩ := hp
      have hb := hbound q hq.1
      have hx := congrArg Prod.fst he
      have hy := congrArg Prod.snd he
      have hv0 : v.2 = 0 := hv.2
      have hfv : v.1 = 0 := by
        change q.1 + v.1 = lo at hx
        linarith [hv.1.1]
      have hqeq : q = (lo, yl) := by
        ext
        · change q.1 + v.1 = lo at hx
          simpa only [hfv, add_zero] using hx
        · change q.2 + v.2 = yl at hy
          simpa only [hv0, add_zero] using hy
      exact hqeq ▸ hq
    · have hp : (hi, yr) ∈ erosion C r + horizontal r := hdecomp ▸ hr
      obtain ⟨q, hq, v, hv, he⟩ := hp
      have hb := hbound (q + (r, 0)) hq.2
      have hx := congrArg Prod.fst he
      have hy := congrArg Prod.snd he
      have hv0 : v.2 = 0 := hv.2
      have hfv : v.1 = r := by
        have hb2 : q.1 + r ≤ hi := hb.2
        change q.1 + v.1 = hi at hx
        linarith [hv.1.2]
      have hqeq : q = (hi - r, yr) := by
        ext
        · change q.1 + v.1 = hi at hx
          linarith
        · change q.2 + v.2 = yr at hy
          simpa only [hv0, add_zero] using hy
      exact hqeq ▸ hq

/-- Two extreme horizontal and two extreme vertical segments yield a literal
rectangle summand, including all degenerate cases. -/
theorem exists_rectangle_remainder (C : ConvexBody Plane)
    {lx ux ly uy w h : ℝ} (hw : 0 ≤ w) (hh : 0 ≤ h)
    (hbound : ∀ p ∈ C, (lx ≤ p.1 ∧ p.1 ≤ ux) ∧ (ly ≤ p.2 ∧ p.2 ≤ uy))
    (hbottom : ∃ a : ℝ, (a, ly) ∈ C ∧ (a + w, ly) ∈ C)
    (htop : ∃ a : ℝ, (a, uy) ∈ C ∧ (a + w, uy) ∈ C)
    (hleft : ∃ a : ℝ, (lx, a) ∈ C ∧ (lx, a + h) ∈ C)
    (hright : ∃ a : ℝ, (ux, a) ∈ C ∧ (ux, a + h) ∈ C) :
    ∃ Q : ConvexBody Plane, (C : Set Plane) =
      ((Q : Set Plane) + vertical h) + horizontal w := by
  first
  | let E := erosion (C : Set Plane) w
    have hE : (C : Set Plane) = E + horizontal w :=
      eq_erosion_add_horizontal_of_vertical_bounds C.isCompact C.convex hw
        (fun p hp => (hbound p hp).2) hbottom htop
    have hEb : ∀ p ∈ E, lx ≤ p.1 ∧ p.1 ≤ ux - w := by
      intro p hp
      have h0 := (hbound p hp.1).1
      have h1 := (hbound (p + (w, 0)) hp.2).1
      have h12 : p.1 + w ≤ ux := h1.2
      exact ⟨h0.1, by linarith⟩
    obtain ⟨a, ha, hah⟩ := hleft
    obtain ⟨b, hb, hbh⟩ := hright
    have hleftE : (lx, a) ∈ E ∧ (lx, a + h) ∈ E := by
      constructor
      · exact (erosion_extreme_vertical_endpoints (fun p hp => (hbound p hp).1) hE ha hb).1
      · exact (erosion_extreme_vertical_endpoints (fun p hp => (hbound p hp).1) hE hah hbh).1
    have hrightE : (ux - w, b) ∈ E ∧ (ux - w, b + h) ∈ E := by
      constructor
      · exact (erosion_extreme_vertical_endpoints (fun p hp => (hbound p hp).1) hE ha hb).2
      · exact (erosion_extreme_vertical_endpoints (fun p hp => (hbound p hp).1) hE hah hbh).2
    have hEc := erosion_compact C.isCompact w
    have hEv := erosion_convex C.convex w
    have hQne : (verticalErosion E h).Nonempty := by
      refine ⟨(lx, a), hleftE.1, ?_⟩
      simpa only [Prod.mk_add_mk, add_zero] using hleftE.2
    let Q : ConvexBody Plane :=
      ⟨verticalErosion E h, verticalErosion_convex hEv h,
        verticalErosion_compact hEc h, hQne⟩
    refine ⟨Q, ?_⟩
    have hV := eq_verticalErosion_add_of_bounds hEc hEv hh hEb
      ⟨a, hleftE.1, hleftE.2⟩ ⟨b, hrightE.1, hrightE.2⟩
    change E = (Q : Set Plane) + vertical h at hV
    rw [hE, hV]

end VolumePolynomials.PlanarEdges
