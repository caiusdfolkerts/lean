import cubical.polytope.cube_faces
import cubical.polytope.cube_subfaces
import cubical.cube_face_code_count

/-! # The full geometric cube f-vector and the cube-prism face isomorphism -/

open Set Classical

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n m : ℕ} {P : ConvexPolytope n} {Q : ConvexPolytope m}

def prodOrderIso {α β γ δ : Type*} [Preorder α] [Preorder β] [Preorder γ] [Preorder δ]
    (e : α ≃o β) (f : γ ≃o δ) : α × γ ≃o β × δ where
  __ := Equiv.prodCongr e.toEquiv f.toEquiv
  map_rel_iff' := by intro a b; exact and_congr e.map_rel_iff f.map_rel_iff

theorem faceNumber_eq_of_faceOrderIso (φ : FaceType P ≃o FaceType Q) (i : ℕ) :
    faceNumber P i = faceNumber Q i := by
  let e := φ.toEquiv.subtypeEquiv (p := fun F => faceDim F.val = i)
    (q := fun G => faceDim G.val = i) (fun F => by
      change faceDim F.val = i ↔ faceDim (φ F).val = i
      rw [faceOrderIso_dimension])
  exact (card_dimFaceType P i).symm.trans ((Fintype.card_congr e).trans (card_dimFaceType Q i))

/-- The complete f-vector of an actual geometric cube. -/
theorem standardCube_faceNumber (d : ℕ) (hd : 1 ≤ d) (i : ℕ) :
    faceNumber (standardCube d) i = 2 ^ (d - i) * d.choose i := by
  let φ := cubeFacesOrderIso d hd
  let e := φ.toEquiv.subtypeEquiv (p := fun F => faceDim F.val = i)
    (q := fun p => (Cubical.Cube.freeCoords p).card = i) (fun F => by
      change faceDim F.val = i ↔ (Cubical.Cube.freeCoords (cubeFacesOrderIso d hd F)).card = i
      rw [cubeFacesOrderIso_dim])
  exact (card_dimFaceType _ _).symm.trans
    ((Fintype.card_congr e).trans (Cubical.Cube.card_faceCodes_rank d i))

/-- The interval's two endpoints and whole face are precisely the three
states of one cube face coordinate. -/
def stackingLayerCodeIso : StackingLayer ≃o Cubical.Cube.FaceCoordinate where
  toFun l := match l with
    | .lower => .fixed false
    | .upper => .fixed true
    | .side => .free
  invFun l := match l with
    | .fixed false => .lower
    | .fixed true => .upper
    | .free => .side
  left_inv l := by cases l <;> rfl
  right_inv l := by cases l with
    | free => rfl
    | fixed b => cases b <;> rfl
  map_rel_iff' := by
    intro a b
    cases a <;> cases b <;> simp [StackingLayer.le_iff]

/-- The ordinary face poset of the prism over a geometric cube is that
of a cube of dimension one higher. -/
def cubePrismFaceOrderIso (d : ℕ) (hd : 1 ≤ d) :
    FaceType (standardCube d) × StackingLayer ≃o FaceType (standardCube (d + 1)) :=
  (prodOrderIso (cubeFacesOrderIso d hd) stackingLayerCodeIso).trans
    ((Cubical.Cube.faceCodePrismIso d).trans (cubeFacesOrderIso (d + 1) (by omega)).symm)

/-- Cubes attain every proper-face inequality, with exactly the paper's constants. -/
theorem standardCube_face_equality (d : ℕ) (hd : 3 ≤ d) (i : ℕ)
    (hi : 1 ≤ i) (hid : i ≤ d - 2) :
    (d.choose i + (d - 1).choose (i - 1)) * (standardCube d).vertices.card =
      2 ^ i * faceNumber (standardCube d) i + 2 ^ d * (d - 1).choose (i - 1) := by
  rw [standardCube_vertices_card, standardCube_faceNumber d (by omega)]
  have hp : 2 ^ i * 2 ^ (d - i) = 2 ^ d := by
    rw [← pow_add, Nat.add_sub_of_le (by omega : i ≤ d)]
  rw [← Nat.mul_assoc, hp]
  ring

/-- Cubes attain the facet inequality. -/
theorem standardCube_facet_equality (d : ℕ) (hd : 3 ≤ d) :
    (d - 1) * (standardCube d).vertices.card =
      2 ^ (d - 2) * faceNumber (standardCube d) (d - 1) +
        (d - 2) * 2 ^ (d - 1) := by
  rw [standardCube_vertices_card, standardCube_faceNumber d (by omega)]
  have he : d - (d - 1) = 1 := by omega
  rw [he, pow_one, Nat.choose_symm (show 1 ≤ d by omega), Nat.choose_one_right]
  have hpow1 : 2 ^ (d - 1) = 2 * 2 ^ (d - 2) := by
    have h : d - 2 + 1 = d - 1 := by omega
    rw [← h, pow_succ, Nat.mul_comm]
  have hpow2 : 2 ^ d = 4 * 2 ^ (d - 2) := by
    have h : d - 2 + 2 = d := by omega
    calc
      2 ^ d = 2 ^ (d - 2 + 2) := congrArg (fun k : ℕ => 2 ^ k) h.symm
      _ = _ := by rw [pow_add]; norm_num; ring
  rw [hpow1, hpow2]
  have h1 : d - 1 + 1 = d := by omega
  have h2 : d - 2 + 2 = d := by omega
  have hc : (d - 1) * 4 = 2 * d + (d - 2) * 2 := by omega
  calc
    (d - 1) * (4 * 2 ^ (d - 2)) = ((d - 1) * 4) * 2 ^ (d - 2) := by ring
    _ = (2 * d + (d - 2) * 2) * 2 ^ (d - 2) := by rw [hc]
    _ = _ := by ring

end LeanEval.Geometry.PlatonicClassification
