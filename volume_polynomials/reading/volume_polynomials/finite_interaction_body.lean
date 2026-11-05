module

public import VolumePolynomials.PrismAxisRemainder

@[expose] public section
set_option autoImplicit false

/-! # The genuine three-dimensional interaction identity for finite edge data

Actual Minkowski decompositions reduce arbitrary finite representations to
right-triangle pairs. Their four-axis remainder is eliminated by translation
and the two unit segments. This proves the mixed-volume identity, not merely
the existence of a body with a prescribed Fourier matrix.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators Pointwise

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092

theorem AxisEquivalent.congr {F G F' G' : ConvexBody Plane → ℝ}
    (h : AxisEquivalent F G) (hF : ∀ A, F A = F' A) (hG : ∀ A, G A = G' A) :
    AxisEquivalent F' G' := by
  first
  | apply AxisFunctional.congr h
    intro A
    rw [hF A, hG A]

theorem axisFunctional_triple_middle_rectangle (B C : ConvexBody Plane) :
    AxisFunctional (fun A => 6 * triple A (boundingRectangle B) C) := by
  first
  | have h := (axisFunctional_width.smul (width B * height C)).add
      (axisFunctional_height.smul (height B * width C))
    apply h.congr
    intro A
    rw [boundingRectangle, triple_add_middle,
      triple_smul_middle _ _ _ (show 0 ≤ width B from measureReal_nonneg),
      triple_smul_middle _ _ _ (show 0 ≤ height B from measureReal_nonneg)]
    have hx := congrArg (width B * ·) (triple_middle_unitX A C)
    have hy := congrArg (height B * ·) (triple_middle_unitY A C)
    nlinarith

theorem axisFunctional_triple_last_rectangle (B C : ConvexBody Plane) :
    AxisFunctional (fun A => 6 * triple A B (boundingRectangle C)) := by
  first
  | have h := (axisFunctional_height.smul (width C * height B)).add
      (axisFunctional_width.smul (height C * width B))
    apply h.congr
    intro A
    rw [boundingRectangle, triple_add_last,
      triple_smul_last _ _ _ (show 0 ≤ width C from measureReal_nonneg),
      triple_smul_last _ _ _ (show 0 ≤ height C from measureReal_nonneg)]
    have hx := congrArg (width C * ·) (triple_last_unitX A B)
    have hy := congrArg (height C * ·) (triple_last_unitY A B)
    nlinarith

theorem finite_representation_triple_reduction {ι κ : Type*} [Fintype ι] [Fintype κ]
    {B C : ConvexBody Plane} {b : ι → Plane} {c : κ → Plane}
    (hB : Represents B b) (hC : Represents C c) :
    AxisEquivalent (fun A => 6 * triple A B C)
      (fun A => 6 * triple A (triangleSum b) (triangleSum c)) := by
  first
  | obtain ⟨vB, hvB⟩ := hB.triangleSum_eq_translate
    obtain ⟨vC, hvC⟩ := hC.triangleSum_eq_translate
    have hR := ((axisFunctional_triple_middle_rectangle B C).add
      (axisFunctional_triple_last_rectangle B C)).add
      (axisFunctional_triple_middle_rectangle B (boundingRectangle C))
    apply hR.neg.congr
    intro A
    dsimp only
    rw [hvB, hvC, triple_translate_middle, triple_translate_last,
      triple_add_middle, triple_add_last, triple_add_last]
    ring

theorem finite_representation_product_axis {ι κ : Type*} [Fintype ι] [Fintype κ]
    {B C : ConvexBody Plane} {b : ι → Plane} {c : κ → Plane}
    (hB : Represents B b) (hC : Represents C c) :
    AxisEquivalent (fun A => 6 * triple A B C)
      (fun A => ∑ i, ∑ j, SupportGeometry.support (A : Set Plane) (normal (interactionEdge (b i) (c j)))) := by
  first
  | have hsum := AxisEquivalent.sum (fun i : ι => AxisEquivalent.sum
      (fun j : κ => triangle_pair_axis_equivalent (b i) (c j)))
    have hpair : AxisEquivalent (fun A => 6 * triple A (triangleSum b) (triangleSum c))
        (fun A => ∑ i, ∑ j, SupportGeometry.support (A : Set Plane)
          (normal (interactionEdge (b i) (c j)))) := by
      first
      | apply hsum.congr
        · intro A
          simp only [triangleSum, triple_sum_middle, triple_sum_last, Finset.mul_sum]
          rw [Finset.sum_comm]
        · intro A
          rfl
    exact (finite_representation_triple_reduction hB hC).trans hpair

theorem completed_representation_axis {ι κ : Type*} [Fintype ι] [Fintype κ]
    {Q : ConvexBody Plane} {b : ι → Plane} {c : κ → Plane}
    (hQ : Represents Q (completedEdges (productEdges b c))) :
    AxisEquivalent (fun A => ∑ i, ∑ j,
      SupportGeometry.support (A : Set Plane) (normal (interactionEdge (b i) (c j))))
      (fun A => 2 * mixedArea volume A Q) := by
  first
  | have haxis (k : Fin 4) : AxisFunctional (fun A =>
        SupportGeometry.support (A : Set Plane) (normal (axisCompletion (productEdges b c) k))) := by
      first
      | apply axisFunctional_support_normal
        fin_cases k <;> simp [axisCompletion]
    apply (AxisFunctional.sum haxis).neg.congr
    intro A
    have h := hQ A
    simp only [completedEdges, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      productEdges, Fintype.sum_prod_type] at h
    linarith

/-- Formula (4.8) for every input with an actual finite first-variation
representation. This includes every positive-area polygon and the explicit
finite logarithmic witnesses constructed from balanced vectors. -/
theorem finite_interaction_identity {ι κ : Type*} [Fintype ι] [Fintype κ]
    {B C Q : ConvexBody Plane} {b : ι → Plane} {c : κ → Plane}
    (hB : Represents B b) (hC : Represents C c)
    (hBw : width B = 1) (hBh : height B = 1)
    (hCw : width C = 1) (hCh : height C = 1)
    (hQ : Represents Q (completedEdges (productEdges b c)))
    (hQw : width Q = 1) (hQh : height Q = 1) :
    ∀ A : ConvexBody Plane, 6 * triple A B C = 2 * mixedArea volume A Q := by
  first
  | have haxis := (finite_representation_product_axis hB hC).trans (completed_representation_axis hQ)
    have hpoint (v : Plane) : 6 * triple (pointBody v) B C - 2 * mixedArea volume (pointBody v) Q = 0 := by
      first
      | rw [triple_point, mixedArea_point_left]
        ring
    have hx : 6 * triple unitX B C - 2 * mixedArea volume unitX Q = 0 := by
      first
      | rw [triple_unitX, mixedArea_symm volume unitX Q, twice_mixedArea_unitX, hBw, hCh, hQh]
        norm_num
    have hy : 6 * triple unitY B C - 2 * mixedArea volume unitY Q = 0 := by
      first
      | rw [triple_unitY, mixedArea_symm volume unitY Q, twice_mixedArea_unitY, hBh, hCw, hQw]
        norm_num
    have hzero := AxisFunctional.eq_zero haxis (hpoint (1, 0)) (hpoint (0, 1)) hx hy
    intro A
    exact sub_eq_zero.mp (hzero A)

theorem finite_interaction_body {ι κ : Type*} [Fintype ι] [Fintype κ]
    {B C : ConvexBody Plane} {b : ι → Plane} {c : κ → Plane}
    (hB : Represents B b) (hC : Represents C c)
    (hBw : width B = 1) (hBh : height B = 1)
    (hCw : width C = 1) (hCh : height C = 1) :
    ∃ Q : ConvexBody Plane, width Q = 1 ∧ height Q = 1 ∧
      (∀ A, 6 * triple A B C = 2 * mixedArea volume A Q) ∧
      max (volume.real (B : Set Plane)) (volume.real (C : Set Plane)) ≤ volume.real (Q : Set Plane) ∧
      Represents Q (completedEdges (productEdges b c)) := by
  first
  | obtain ⟨Q, hQ, hQw, hQh⟩ := exists_productEdge_body hB hC hBw hBh hCw hCh
    exact ⟨Q, hQw, hQh, finite_interaction_identity hB hC hBw hBh hCw hCh hQ hQw hQh,
      productEdge_body_area_ge_inputs hB hC hBw hBh hCw hCh hQ hQw hQh, hQ⟩

/-- Proposition 4.3 for arbitrary positive-area polygons, with the literal
mixed-volume functional and ordinary coordinate widths. -/
theorem polygon_interaction_body (B C : ConvexBody Plane)
    (hB : PolytopeGeometry.IsFiniteHull (B : Set Plane))
    (hC : PolytopeGeometry.IsFiniteHull (C : Set Plane))
    (hBa : 0 < volume.real (B : Set Plane)) (hCa : 0 < volume.real (C : Set Plane))
    (hBw : width B = 1) (hBh : height B = 1) (hCw : width C = 1) (hCh : height C = 1) :
    ∃ Q : ConvexBody Plane, width Q = 1 ∧ height Q = 1 ∧
      (∀ A, 6 * triple A B C = 2 * mixedArea volume A Q) ∧
      max (volume.real (B : Set Plane)) (volume.real (C : Set Plane)) ≤ volume.real (Q : Set Plane) := by
  first
  | obtain ⟨m, b, hb⟩ := exists_representation B hB hBa
    obtain ⟨n, c, hc⟩ := exists_representation C hC hCa
    obtain ⟨Q, hQw, hQh, hQV, hQa, _⟩ := finite_interaction_body hb hc hBw hBh hCw hCh
    exact ⟨Q, hQw, hQh, hQV, hQa⟩

end VolumePolynomials.PlanarInteraction
