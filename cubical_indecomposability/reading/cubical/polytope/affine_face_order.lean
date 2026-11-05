import cubical.polytope.face_order

/-! # Face-poset transport through an affine realization equivalence -/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n m : ℕ}

theorem affine_functional_le_iff (l : E n →L[ℝ] ℝ) (g : E m →ᵃ[ℝ] E n)
    (x y : E m) :
    l (g x) ≤ l (g y) ↔
      (l.comp g.linear.toContinuousLinearMap) x ≤
        (l.comp g.linear.toContinuousLinearMap) y := by
  have hx : g x = g.linear x + g 0 := congrFun g.decomp x
  have hy : g y = g.linear y + g 0 := congrFun g.decomp y
  rw [hx, hy, map_add, map_add, add_le_add_iff_right]
  rfl

theorem isFace_affine_image (P : ConvexPolytope n) (Q : ConvexPolytope m)
    (f : E n →ᵃ[ℝ] E m) (g : E m →ᵃ[ℝ] E n)
    (hinv : ∀ x ∈ P.toSet, g (f x) = x) (hbody : f '' P.toSet = Q.toSet)
    {F : Set (E n)} (hF : P.IsFace F) : Q.IsFace (f '' F) := by
  have hne : (f '' F).Nonempty := hF.2.image f
  refine ⟨?_, hne⟩
  intro _
  obtain ⟨l, hl⟩ := hF.1 hF.2
  refine ⟨l.comp g.linear.toContinuousLinearMap, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hxF, rfl⟩
    have hx : x ∈ P.toSet := face_subset_toSet P hF hxF
    have hxmax : ∀ z ∈ P.toSet, l z ≤ l x := (hl ▸ hxF).2
    refine ⟨hbody ▸ ⟨x, hx, rfl⟩, ?_⟩
    intro z hz
    obtain ⟨u, hu, rfl⟩ := (show z ∈ f '' P.toSet from hbody.symm ▸ hz)
    apply (affine_functional_le_iff l g (f u) (f x)).mp
    rw [hinv u hu, hinv x hx]
    exact hxmax u hu
  · rintro ⟨hy, hymax⟩
    obtain ⟨x, hx, rfl⟩ := (show y ∈ f '' P.toSet from hbody.symm ▸ hy)
    refine ⟨x, ?_, rfl⟩
    rw [hl]
    refine ⟨hx, ?_⟩
    intro z hz
    have h := (affine_functional_le_iff l g (f z) (f x)).mpr
      (hymax (f z) (hbody ▸ ⟨z, hz, rfl⟩))
    simpa only [hinv z hz, hinv x hx] using h

theorem affine_inverse_image_body (P : ConvexPolytope n) (Q : ConvexPolytope m)
    (f : E n →ᵃ[ℝ] E m) (g : E m →ᵃ[ℝ] E n)
    (hinv : ∀ x ∈ P.toSet, g (f x) = x) (hbody : f '' P.toSet = Q.toSet) :
    g '' Q.toSet = P.toSet := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := (show y ∈ f '' P.toSet from hbody.symm ▸ hy)
    simpa only [hinv z hz] using hz
  · intro hx
    exact ⟨f x, hbody ▸ ⟨x, hx, rfl⟩, hinv x hx⟩

theorem affine_inverse_on_image (P : ConvexPolytope n) (Q : ConvexPolytope m)
    (f : E n →ᵃ[ℝ] E m) (g : E m →ᵃ[ℝ] E n)
    (hinv : ∀ x ∈ P.toSet, g (f x) = x) (hbody : f '' P.toSet = Q.toSet) :
    ∀ y ∈ Q.toSet, f (g y) = y := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (show y ∈ f '' P.toSet from hbody.symm ▸ hy)
  rw [hinv x hx]

/-- An affine map with an affine inverse on the two polytope bodies induces
an isomorphism of their ordinary geometric face posets. -/
def affineFaceOrderIso (P : ConvexPolytope n) (Q : ConvexPolytope m)
    (f : E n →ᵃ[ℝ] E m) (g : E m →ᵃ[ℝ] E n)
    (hinv : ∀ x ∈ P.toSet, g (f x) = x) (hbody : f '' P.toSet = Q.toSet) :
    FaceType P ≃o FaceType Q where
  toFun F := ⟨f '' F.val, isFace_affine_image P Q f g hinv hbody F.property⟩
  invFun G := ⟨g '' G.val, isFace_affine_image Q P g f
    (affine_inverse_on_image P Q f g hinv hbody)
    (affine_inverse_image_body P Q f g hinv hbody) G.property⟩
  left_inv F := by
    apply Subtype.ext
    ext x
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      simpa only [hinv z (face_subset_toSet P F.property hz)] using hz
    · intro hx
      exact ⟨f x, ⟨x, hx, rfl⟩, hinv x (face_subset_toSet P F.property hx)⟩
  right_inv G := by
    apply Subtype.ext
    ext y
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      simpa only [affine_inverse_on_image P Q f g hinv hbody z
        (face_subset_toSet Q G.property hz)] using hz
    · intro hy
      exact ⟨g y, ⟨y, hy, rfl⟩, affine_inverse_on_image P Q f g hinv hbody y
        (face_subset_toSet Q G.property hy)⟩
  map_rel_iff' := by
    intro F G
    constructor
    · intro h x hx
      obtain ⟨z, hz, hfzx⟩ := h ⟨x, hx, rfl⟩
      have hzx := congrArg g hfzx
      rw [hinv z (face_subset_toSet P G.property hz),
        hinv x (face_subset_toSet P F.property hx)] at hzx
      exact hzx ▸ hz
    · intro h
      exact Set.image_mono h

end LeanEval.Geometry.PlatonicClassification
