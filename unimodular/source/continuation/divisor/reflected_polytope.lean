module

public import Unimodular.Geometry

/-!
# Reflection of a smooth reflexive polytope

Reflection negates the actual vertices, facet normals and active integral
bases. Its carrier is exactly the negative of the original convex hull.
The geometric condition of deep monotonicity is invariant under this
reflection, by the proved equivalence with containment of the unit corners.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators

namespace Unimodular

variable {n : ℕ}

@[simp] theorem embed_neg (u : Lattice n) : embed (-u) = -embed u := by
  ext i
  simp [embed]

@[simp] theorem pairing_neg_left (x : Ambient n) (u : Lattice n) :
    pairing (-x) u = -pairing x u := by
  simp [pairing, Finset.sum_neg_distrib]

@[simp] theorem pairing_neg_right (x : Ambient n) (u : Lattice n) :
    pairing x (-u) = -pairing x u := by
  simp [pairing, Finset.sum_neg_distrib]

/-- Negating the normal basis negates its dual-coordinate corner. -/
theorem dualCorner_map_neg (b : Module.Basis (Fin n) ℤ (Lattice n))
    (t : Ambient n) :
    dualCorner (b.map (LinearEquiv.neg ℤ)) t = -dualCorner b t := by
  ext j
  simp [dualCorner, Module.Basis.map_repr, LinearEquiv.trans_apply,
    LinearEquiv.neg_apply, Finset.sum_neg_distrib]

namespace SmoothReflexivePresentation

variable (P : SmoothReflexivePresentation n)

/-- Reflection identifies the listed vertices without making a choice. -/
def reflectedVertexEquiv :
    {v // v ∈ P.vertices.image Neg.neg} ≃ {v // v ∈ P.vertices} where
  toFun v := ⟨-v.val, by
    obtain ⟨w, hw, he⟩ := Finset.mem_image.mp v.property
    simpa only [← he, neg_neg] using hw⟩
  invFun v := ⟨-v.val, Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩⟩
  left_inv v := Subtype.ext (neg_neg v.val)
  right_inv v := Subtype.ext (neg_neg v.val)

@[simp] theorem reflectedVertexEquiv_apply_val
    (v : {v // v ∈ P.vertices.image Neg.neg}) :
    (P.reflectedVertexEquiv v).val = -v.val := rfl

@[simp] theorem reflectedVertexEquiv_symm_apply_val
    (v : {v // v ∈ P.vertices}) :
    (P.reflectedVertexEquiv.symm v).val = -v.val := rfl

/-- The actual convex hull of the negated lattice vertices. -/
theorem reflected_hull :
    convexHull ℝ (embed '' (P.vertices.image Neg.neg : Set (Lattice n))) =
      {x : Ambient n | ∀ u ∈ P.normals.image Neg.neg, pairing x u ≤ 1} := by
  have hvertices :
      embed '' (P.vertices.image Neg.neg : Set (Lattice n)) =
        (fun x : Ambient n => -x) '' (embed '' (P.vertices : Set (Lattice n))) := by
    rw [Finset.coe_image, Set.image_image, Set.image_image]
    congr 1
    funext u
    exact embed_neg u
  have hlinear :
      (fun x : Ambient n => -x) ''
          convexHull ℝ (embed '' (P.vertices : Set (Lattice n))) =
        convexHull ℝ ((fun x : Ambient n => -x) ''
          (embed '' (P.vertices : Set (Lattice n)))) :=
    (LinearEquiv.neg ℝ : Ambient n ≃ₗ[ℝ] Ambient n).toLinearMap.image_convexHull _
  rw [hvertices, ← hlinear, P.hull_eq]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    simpa only [pairing_neg_left, pairing_neg_right, neg_neg] using hy v hv
  · intro hx
    refine ⟨-x, ?_, neg_neg x⟩
    intro u hu
    have h := hx (-u) (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
    simpa only [pairing_neg_left, pairing_neg_right] using h

/-- Reflection preserves the full smooth reflexive presentation, including
the exact set of active facet normals at every actual vertex. -/
def reflected : SmoothReflexivePresentation n where
  vertices := P.vertices.image Neg.neg
  normals := P.normals.image Neg.neg
  vertices_nonempty := P.vertices_nonempty.image _
  basis v := (P.basis (P.reflectedVertexEquiv v)).map (LinearEquiv.neg ℤ)
  basis_mem v i := by
    exact Finset.mem_image.mpr
      ⟨P.basis (P.reflectedVertexEquiv v) i, P.basis_mem _ i, rfl⟩
  basis_active v i := by
    change pairing (embed v.val) (-(P.basis (P.reflectedVertexEquiv v) i)) = 1
    have h := P.basis_active (P.reflectedVertexEquiv v) i
    change pairing (embed (-v.val)) (P.basis (P.reflectedVertexEquiv v) i) = 1 at h
    simpa only [embed_neg, pairing_neg_left, pairing_neg_right] using h
  active_subset v u hu hactive := by
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
    have h : pairing (embed (P.reflectedVertexEquiv v).val) w = 1 := by
      simpa only [reflectedVertexEquiv_apply_val, embed_neg,
        pairing_neg_left, pairing_neg_right] using hactive
    obtain ⟨i, hi⟩ := P.active_subset (P.reflectedVertexEquiv v) w hw h
    refine ⟨i, ?_⟩
    change -(P.basis (P.reflectedVertexEquiv v) i) = -w
    exact congrArg Neg.neg hi
  normals_occur u hu := by
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v, i, hi⟩ := P.normals_occur w hw
    refine ⟨P.reflectedVertexEquiv.symm v, i, ?_⟩
    change -(P.basis (P.reflectedVertexEquiv (P.reflectedVertexEquiv.symm v)) i) = -w
    rw [Equiv.apply_symm_apply, hi]
  hull_eq := P.reflected_hull

@[simp] theorem reflected_vertices : P.reflected.vertices = P.vertices.image Neg.neg := rfl

@[simp] theorem reflected_normals : P.reflected.normals = P.normals.image Neg.neg := rfl

@[simp] theorem reflected_basis (v : {v // v ∈ P.reflected.vertices}) :
    P.reflected.basis v =
      (P.basis (P.reflectedVertexEquiv v)).map (LinearEquiv.neg ℤ) := rfl

/-- Membership in the reflected polytope is exactly reflected membership. -/
@[simp] theorem mem_reflected_carrier (x : Ambient n) :
    x ∈ P.reflected.carrier ↔ -x ∈ P.carrier := by
  rw [P.reflected.mem_carrier_iff, P.mem_carrier_iff]
  constructor
  · intro h u hu
    have hh := h (-u) (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
    simpa only [pairing_neg_left, pairing_neg_right] using hh
  · intro h u hu
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
    simpa only [pairing_neg_left, pairing_neg_right] using h w hw

theorem reflected_carrier :
    P.reflected.carrier = Neg.neg '' P.carrier := by
  ext x
  rw [P.mem_reflected_carrier]
  constructor
  · intro hx
    exact ⟨-x, hx, neg_neg x⟩
  · rintro ⟨y, hy, rfl⟩
    simpa only [neg_neg] using hy

/-- Unit corners are reflected point by point, in their actual dual bases. -/
theorem reflected_unitCorner (v : {v // v ∈ P.reflected.vertices}) (t : Ambient n) :
    -(embed v.val - dualCorner (P.reflected.basis v) t) =
      embed (P.reflectedVertexEquiv v).val -
        dualCorner (P.basis (P.reflectedVertexEquiv v)) t := by
  rw [P.reflected_basis, dualCorner_map_neg, reflectedVertexEquiv_apply_val, embed_neg]
  module

theorem unitCornersContained_reflected_iff :
    P.reflected.UnitCornersContained ↔ P.UnitCornersContained := by
  constructor
  · intro h v t ht
    have hv := (P.mem_reflected_carrier _).mp
      (h (P.reflectedVertexEquiv.symm v) t ht)
    rw [P.reflected_unitCorner, Equiv.apply_symm_apply] at hv
    exact hv
  · intro h v t ht
    apply (P.mem_reflected_carrier _).mpr
    rw [P.reflected_unitCorner]
    exact h (P.reflectedVertexEquiv v) t ht

/-- Deep monotonicity, defined using all actual primitive edge segments,
is unchanged by reflection. No new assumption is needed in either direction. -/
theorem deeplyMonotone_reflected_iff : P.reflected.DeeplyMonotone ↔ P.DeeplyMonotone :=
  P.reflected.deeplyMonotone_iff_unitCornersContained.trans
    (P.unitCornersContained_reflected_iff.trans P.deeplyMonotone_iff_unitCornersContained.symm)

end SmoothReflexivePresentation

#print axioms SmoothReflexivePresentation.reflected
#print axioms SmoothReflexivePresentation.reflected_carrier
#print axioms SmoothReflexivePresentation.deeplyMonotone_reflected_iff

end Unimodular
