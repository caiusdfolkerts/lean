import cubical.polytope.stacking_cubical

/-!
# Exact stacked cubical f-vectors and sharpness

All increments are derived from the genuine gluing face poset. Equality is
then preserved by every finite stacking sequence of actual convex polytopes.
-/

open Set Classical

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n m : ℕ} {P : ConvexPolytope n} {Q : ConvexPolytope m}

namespace FacetStacking

variable (S : FacetStacking P Q)

include S

theorem gluedFacet_faceNumber (hc : IsCubical P) (hdim : 2 ≤ P.dim) (i : ℕ) :
    faceNumber (facePolytope P S.facet.val.property) i =
      2 ^ (P.dim - 1 - i) * (P.dim - 1).choose i := by
  obtain ⟨φ⟩ := hc S.facet.val.val S.facet.val.property S.facet.property
  exact (faceNumber_eq_of_faceOrderIso φ i).trans
    (standardCube_faceNumber (P.dim - 1) (by omega) i)

/-- A cubical stacking adds exactly `2^(d-1)` vertices. -/
theorem vertices_increment (hc : IsCubical P) (hdim : 2 ≤ P.dim) :
    Q.vertices.card = P.vertices.card + 2 ^ (P.dim - 1) := by
  rw [S.vertices_card hdim,
    ← faceNumber_zero (facePolytope P S.facet.val.property),
    S.gluedFacet_faceNumber hc hdim 0]
  simp

/-- The exact i-face increment from attaching one cube along a facet. -/
theorem face_increment (hc : IsCubical P) (hdim : 3 ≤ P.dim)
    (i : ℕ) (hi : 1 ≤ i) (hid : i ≤ P.dim - 2) :
    faceNumber Q i = faceNumber P i + 2 ^ (P.dim - 1 - i) *
      (P.dim.choose i + (P.dim - 1).choose (i - 1)) := by
  rw [S.faceNumber_positive i hi (by omega),
    S.gluedFacet_faceNumber hc (by omega), S.gluedFacet_faceNumber hc (by omega)]
  have he : P.dim - 1 - (i - 1) = (P.dim - 1 - i) + 1 := by omega
  rw [he, pow_succ]
  have hbin := Nat.choose_eq_choose_pred_add (by omega : 0 < P.dim) (by omega : 0 < i)
  rw [hbin]
  ring

/-- Stacking removes one facet and adds `2d-1` facets, hence increases
the total by `2(d-1)`. -/
theorem facet_increment (hc : IsCubical P) (hdim : 3 ≤ P.dim) :
    faceNumber Q (P.dim - 1) = faceNumber P (P.dim - 1) + 2 * (P.dim - 1) := by
  have htop : faceNumber (facePolytope P S.facet.val.property) (P.dim - 1) = 1 := by
    rw [S.gluedFacet_faceNumber hc (by omega)]
    simp
  have hridge : faceNumber (facePolytope P S.facet.val.property) (P.dim - 2) =
      2 * (P.dim - 1) := by
    rw [S.gluedFacet_faceNumber hc (by omega)]
    have he1 : P.dim - 1 - (P.dim - 2) = 1 := by omega
    have he2 : P.dim - 2 = (P.dim - 1) - 1 := by omega
    rw [he1, pow_one, he2, Nat.choose_symm (by omega : 1 ≤ P.dim - 1), Nat.choose_one_right]
  have h := S.facet_count_balance (by omega)
  rw [htop, hridge] at h
  omega

/-- Every proper-face equality is invariant under a genuine stacking. -/
theorem preserves_face_equality (hc : IsCubical P) (hdim : 3 ≤ P.dim)
    (i : ℕ) (hi : 1 ≤ i) (hid : i ≤ P.dim - 2)
    (heq : (P.dim.choose i + (P.dim - 1).choose (i - 1)) * P.vertices.card =
      2 ^ i * faceNumber P i + 2 ^ P.dim * (P.dim - 1).choose (i - 1)) :
    (Q.dim.choose i + (Q.dim - 1).choose (i - 1)) * Q.vertices.card =
      2 ^ i * faceNumber Q i + 2 ^ Q.dim * (Q.dim - 1).choose (i - 1) := by
  rw [S.dimension, S.vertices_increment hc (by omega), S.face_increment hc hdim i hi hid]
  have hp : 2 ^ i * 2 ^ (P.dim - 1 - i) = 2 ^ (P.dim - 1) := by
    rw [← pow_add, Nat.add_sub_of_le (by omega : i ≤ P.dim - 1)]
  calc
    (P.dim.choose i + (P.dim - 1).choose (i - 1)) * (P.vertices.card + 2 ^ (P.dim - 1)) =
      (P.dim.choose i + (P.dim - 1).choose (i - 1)) * P.vertices.card +
        (P.dim.choose i + (P.dim - 1).choose (i - 1)) * 2 ^ (P.dim - 1) := by ring
    _ = (2 ^ i * faceNumber P i + 2 ^ P.dim * (P.dim - 1).choose (i - 1)) +
        (P.dim.choose i + (P.dim - 1).choose (i - 1)) * 2 ^ (P.dim - 1) := by rw [heq]
    _ = _ := by rw [← hp]; ring

/-- The facet equality is invariant under a genuine stacking. -/
theorem preserves_facet_equality (hc : IsCubical P) (hdim : 3 ≤ P.dim)
    (heq : (P.dim - 1) * P.vertices.card =
      2 ^ (P.dim - 2) * faceNumber P (P.dim - 1) + (P.dim - 2) * 2 ^ (P.dim - 1)) :
    (Q.dim - 1) * Q.vertices.card =
      2 ^ (Q.dim - 2) * faceNumber Q (Q.dim - 1) + (Q.dim - 2) * 2 ^ (Q.dim - 1) := by
  rw [S.dimension, S.vertices_increment hc (by omega), S.facet_increment hc hdim]
  have hp : 2 ^ (P.dim - 1) = 2 * 2 ^ (P.dim - 2) := by
    have h : P.dim - 2 + 1 = P.dim - 1 := by omega
    rw [← h, pow_succ, Nat.mul_comm]
  calc
    (P.dim - 1) * (P.vertices.card + 2 ^ (P.dim - 1)) =
      (P.dim - 1) * P.vertices.card + (P.dim - 1) * 2 ^ (P.dim - 1) := by ring
    _ = (2 ^ (P.dim - 2) * faceNumber P (P.dim - 1) + (P.dim - 2) * 2 ^ (P.dim - 1)) +
        (P.dim - 1) * 2 ^ (P.dim - 1) := by rw [heq]
    _ = _ := by rw [hp]; ring

end FacetStacking

/-- Every stacked cubical polytope attains every proper-face bound in
Corollary 5, with no restriction on its number of stacking operations. -/
theorem IsStackedCubical.face_equality {P : ConvexPolytope n} (hP : IsStackedCubical P) :
    ∀ (hdim : 3 ≤ P.dim) (i : ℕ), 1 ≤ i → i ≤ P.dim - 2 →
      (P.dim.choose i + (P.dim - 1).choose (i - 1)) * P.vertices.card =
        2 ^ i * faceNumber P i + 2 ^ P.dim * (P.dim - 1).choose (i - 1) := by
  induction hP with
  | cube P hd hcube =>
    intro hdim i hi hid
    obtain ⟨φ⟩ := hcube
    have hdP : P.dim = _ := (faceOrderIso_dim φ).symm.trans (ipercubo_isFullDim _ hd)
    have hN := vertices_card_eq_of_faceOrderIso φ
    have hF := faceNumber_eq_of_faceOrderIso φ i
    rw [hdP, hN, hF]
    exact standardCube_face_equality _ (by omega) i hi (by omega)
  | stack hP S ih =>
    intro hdim i hi hid
    have hdP := S.dimension ▸ hdim
    apply S.preserves_face_equality (hP.isCubical hdP) hdP i hi (by rwa [S.dimension] at hid)
    exact ih hdP i hi (by rwa [S.dimension] at hid)

/-- Every stacked cubical polytope attains the facet bound in Corollary 5. -/
theorem IsStackedCubical.facet_equality {P : ConvexPolytope n} (hP : IsStackedCubical P) :
    3 ≤ P.dim → (P.dim - 1) * P.vertices.card =
      2 ^ (P.dim - 2) * faceNumber P (P.dim - 1) + (P.dim - 2) * 2 ^ (P.dim - 1) := by
  induction hP with
  | cube P hd hcube =>
    intro hdim
    obtain ⟨φ⟩ := hcube
    have hdP : P.dim = _ := (faceOrderIso_dim φ).symm.trans (ipercubo_isFullDim _ hd)
    have hN := vertices_card_eq_of_faceOrderIso φ
    rw [hdP, hN, faceNumber_eq_of_faceOrderIso φ]
    exact standardCube_facet_equality _ (by omega)
  | stack hP S ih =>
    intro hdim
    have hdP := S.dimension ▸ hdim
    exact S.preserves_facet_equality (hP.isCubical hdP) hdP (ih hdP)

/-- The edge sharpness assertion in Theorem 1 is the i=1 case. -/
theorem IsStackedCubical.edge_equality {P : ConvexPolytope n}
    (hP : IsStackedCubical P) (hdim : 3 ≤ P.dim) :
    (P.dim + 1) * P.vertices.card = 2 * faceNumber P 1 + 2 ^ P.dim := by
  have h := hP.face_equality hdim 1 (by omega) (by omega)
  simpa using h

end LeanEval.Geometry.PlatonicClassification
