module

public import VolumePolynomials.HigherLiftSupport
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Product coordinates forced by the lifted slice

The quotient complement is constructed inside the first body's hyperplane.
Consequently its fibers in the three-dimensional factor lie in one fixed
plane. No product structure of the original body is assumed.
-/

open Set Module MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.HigherLift

theorem exists_complement_inside {E : Type*} [AddCommGroup E] [Module ℝ E]
    (H W : Submodule ℝ E) (hHW : H ⊔ W = ⊤) :
    ∃ U : Submodule ℝ E, U ≤ H ∧ IsCompl W U ∧ (H ⊓ W) ⊔ U = H := by
  first
  | obtain ⟨V, hV⟩ := Submodule.exists_isCompl (H ⊓ W)
    let U := H ⊓ V
    have hUH : U ≤ H := inf_le_left
    have hsplit : (H ⊓ W) ⊔ U = H := by
      first
      | apply le_antisymm
        · exact sup_le inf_le_left hUH
        · intro x hx
          obtain ⟨e, v, hev, _⟩ := Submodule.existsUnique_add_of_isCompl hV x
          have hvH : (v : E) ∈ H := by
            have hv : (v : E) = x - (e : E) := by rw [← hev]; abel
            rw [hv]
            exact H.sub_mem hx e.property.1
          exact Submodule.mem_sup.mpr ⟨e, e.property, v, ⟨hvH, v.property⟩, hev⟩
    have hinf : W ⊓ U = ⊥ := by
      first
      | change W ⊓ (H ⊓ V) = ⊥
        rw [← inf_assoc, inf_comm W H]
        exact hV.inf_eq_bot
    have hsup : W ⊔ U = ⊤ := by
      first
      | apply top_unique
        rw [← hHW, ← hsplit]
        exact sup_le (sup_le (inf_le_right.trans le_sup_left) le_sup_right) le_sup_left
    exact ⟨U, hUH, IsCompl.of_le hinf.le hsup.ge, hsplit⟩

theorem lifted_subspaces {k : ℕ} {α s z : ℝ} (hα : 0 < α) (hs : 0 < s)
    {K : Fin 3 → Body (3 + k)} (hK : Realizes K (coefficients k α s z))
    (h0 : ∀ i, (0 : Space (3 + k)) ∈ K i) :
    ∃ U : Submodule ℝ (Space (3 + k)),
      U ≤ linearHull (K 0) ∧
      IsCompl (linearHull (K 1) ⊔ linearHull (K 2)) U ∧
      finrank ℝ U = k ∧
      finrank ℝ ((linearHull (K 0) ⊓ (linearHull (K 1) ⊔ linearHull (K 2))) :
        Submodule ℝ (Space (3 + k))) = 2 ∧
      (linearHull (K 0) ⊓ (linearHull (K 1) ⊔ linearHull (K 2))) ⊔ U = linearHull (K 0) := by
  first
  | obtain ⟨hdH, hdB, hdC, hdW, hHB, hHC⟩ := centered_dimensions hα hs hK h0
    let H := linearHull (K 0)
    let W := linearHull (K 1) ⊔ linearHull (K 2)
    have hHW : H ⊔ W = ⊤ := by
      first
      | change linearHull (K 0) ⊔ (linearHull (K 1) ⊔ linearHull (K 2)) = ⊤
        rw [← sup_assoc, hHB, top_sup_eq]
    have hdE : finrank ℝ ((H ⊓ W) : Submodule ℝ (Space (3 + k))) = 2 := by
      first
      | have h := Submodule.finrank_sup_add_finrank_inf_eq H W
        rw [hHW] at h
        have htop : finrank ℝ (⊤ : Submodule ℝ (Space (3 + k))) = 3 + k := by simp [Space]
        change finrank ℝ H = k + 2 at hdH
        change finrank ℝ W = 3 at hdW
        rw [htop, hdH, hdW] at h
        omega
    obtain ⟨U, hUH, hWU, hsplit⟩ := exists_complement_inside H W hHW
    have hdU : finrank ℝ U = k := by
      first
      | have h := Submodule.finrank_add_eq_of_isCompl hWU
        change finrank ℝ W = 3 at hdW
        rw [hdW] at h
        have hspace : finrank ℝ (Space (3 + k)) = 3 + k := by simp [Space]
        rw [hspace] at h
        omega
    exact ⟨U, hUH, hWU, hdU, hdE, hsplit⟩

variable {k : ℕ}

def threeFrame (W U : Submodule ℝ (Space (3 + k)))
    (hWU : IsCompl W U) (hdW : finrank ℝ W = 3) (hdU : finrank ℝ U = k) :
    Space (3 + k) ≃L[ℝ] (Space 3 × Space k) :=
  ((W.prodEquivOfIsCompl U hWU).symm.trans
    ((LinearEquiv.ofFinrankEq W (Space 3) (by simpa [Space] using hdW)).prodCongr
      (LinearEquiv.ofFinrankEq U (Space k) (by simpa [Space] using hdU)))).toContinuousLinearEquiv

def threeFrameLeft (W : Submodule ℝ (Space (3 + k))) (hdW : finrank ℝ W = 3) :
    W ≃ₗ[ℝ] Space 3 := LinearEquiv.ofFinrankEq W (Space 3) (by simpa [Space] using hdW)

def threeFrameRight (U : Submodule ℝ (Space (3 + k))) (hdU : finrank ℝ U = k) :
    U ≃ₗ[ℝ] Space k := LinearEquiv.ofFinrankEq U (Space k) (by simpa [Space] using hdU)

theorem threeFrame_on_left (W U : Submodule ℝ (Space (3 + k)))
    (hWU : IsCompl W U) (hdW : finrank ℝ W = 3) (hdU : finrank ℝ U = k) (x : W) :
    threeFrame W U hWU hdW hdU (x : Space (3 + k)) = (threeFrameLeft W hdW x, 0) := by
  first
  | change ((threeFrameLeft W hdW) ((W.prodEquivOfIsCompl U hWU).symm (x : Space (3 + k))).1,
      (threeFrameRight U hdU) ((W.prodEquivOfIsCompl U hWU).symm (x : Space (3 + k))).2) = _
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
    simp only [map_zero]

theorem threeFrame_on_right (W U : Submodule ℝ (Space (3 + k)))
    (hWU : IsCompl W U) (hdW : finrank ℝ W = 3) (hdU : finrank ℝ U = k) (x : U) :
    threeFrame W U hWU hdW hdU (x : Space (3 + k)) = (0, threeFrameRight U hdU x) := by
  first
  | change ((threeFrameLeft W hdW) ((W.prodEquivOfIsCompl U hWU).symm (x : Space (3 + k))).1,
      (threeFrameRight U hdU) ((W.prodEquivOfIsCompl U hWU).symm (x : Space (3 + k))).2) = _
    rw [Submodule.prodEquivOfIsCompl_symm_apply_right]
    simp only [map_zero]

def sectionPlane (H W : Submodule ℝ (Space (3 + k))) (hdW : finrank ℝ W = 3) :
    Submodule ℝ (Space 3) :=
  (H.comap W.subtype).map (threeFrameLeft W hdW).toLinearMap

theorem sectionPlane_finrank (H W : Submodule ℝ (Space (3 + k)))
    (hdW : finrank ℝ W = 3)
    (hdE : finrank ℝ ((H ⊓ W) : Submodule ℝ (Space (3 + k))) = 2) :
    finrank ℝ (sectionPlane H W hdW) = 2 := by
  first
  | rw [sectionPlane, LinearEquiv.finrank_map_eq]
    have heq : H.comap W.subtype = (H ⊓ W).comap W.subtype := by
      first
      | ext x
        change (x : Space (3 + k)) ∈ H ↔
          (x : Space (3 + k)) ∈ H ∧ (x : Space (3 + k)) ∈ W
        exact ⟨fun hx => ⟨hx, x.property⟩, fun hx => hx.1⟩
    rw [heq, (Submodule.comapSubtypeEquivOfLe
      (show H ⊓ W ≤ W from inf_le_right)).finrank_eq]
    exact hdE

theorem frame_fiber_subset_plane (H W U : Submodule ℝ (Space (3 + k)))
    (hWU : IsCompl W U) (hUH : U ≤ H)
    (hdW : finrank ℝ W = 3) (hdU : finrank ℝ U = k)
    (C : Body (3 + k)) (hCH : (C : Set (Space (3 + k))) ⊆ H)
    (y : Space k) :
    ConvexFibers.fiberSet (mapBody (threeFrame W U hWU hdW hdU).toContinuousLinearMap C) y ⊆
      sectionPlane H W hdW := by
  first
  | intro x hx
    obtain ⟨p, hp, hxy⟩ := hx
    let q := (W.prodEquivOfIsCompl U hWU).symm p
    have hq : (q.1 : Space (3 + k)) + (q.2 : Space (3 + k)) = p :=
      (W.prodEquivOfIsCompl U hWU).apply_symm_apply p
    have hleftH : (q.1 : Space (3 + k)) ∈ H := by
      first
      | have heq : (q.1 : Space (3 + k)) = p - (q.2 : Space (3 + k)) := by
          rw [← hq]; abel
        rw [heq]
        exact H.sub_mem (hCH hp) (hUH q.2.property)
    refine ⟨q.1, hleftH, ?_⟩
    exact congrArg Prod.fst hxy

theorem frame_body_in_threeSpace (W U : Submodule ℝ (Space (3 + k)))
    (hWU : IsCompl W U) (hdW : finrank ℝ W = 3) (hdU : finrank ℝ U = k)
    (B : Body (3 + k)) (hBW : (B : Set (Space (3 + k))) ⊆ W) :
    mapBody (threeFrame W U hWU hdW hdU).toContinuousLinearMap B =
      FiberVolume.embedBody (mapBody (ContinuousLinearMap.fst ℝ (Space 3) (Space k))
        (mapBody (threeFrame W U hWU hdW hdU).toContinuousLinearMap B)) := by
  first
  | let T := threeFrame W U hWU hdW hdU
    have hz (x : Space (3 + k)) (hx : x ∈ B) : (T x).2 = 0 :=
      congrArg Prod.snd (threeFrame_on_left W U hWU hdW hdU ⟨x, hBW hx⟩)
    apply ConvexBody.ext
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(T x).1, ⟨T x, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
      exact Prod.ext rfl (hz x hx).symm
    · rintro ⟨y, ⟨_, ⟨x, hx, rfl⟩, hxy⟩, rfl⟩
      exact ⟨x, hx, Prod.ext hxy (hz x hx)⟩

end VolumePolynomials.HigherLift
