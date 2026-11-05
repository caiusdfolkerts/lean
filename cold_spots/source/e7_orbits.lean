module
public import paper_verification.lattice007
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

@[expose] public section
noncomputable section
namespace PaperVerification.ColdSpots
open scoped BigOperators

/-- The half-coordinate E7 root attached to a four-element support. -/
def e7OrbitRoot (S : E7FourSubset) : zeroSumSpace := (2 : ℝ) • e7PaperShift S

lemma e7OrbitRoot_apply (S : E7FourSubset) (i : Fin 8) :
    e7OrbitRoot S i = (if i ∈ S.val then (1 : ℝ) else 0) - 1/2 := by
  change 2 * e7PaperShift S i = _
  rw [e7PaperShift_apply]
  split_ifs <;> ring

lemma e7OrbitRoot_mem (S : E7FourSubset) : e7OrbitRoot S ∈ e7Set := by
  let z : Fin 8 → ℤ := fun i => if i ∈ S.val then 0 else -1
  have hz : (∑ i, z i) = -4 := by
    simp [z, Finset.sum_ite, Finset.filter_not, Finset.card_sdiff, S.property]
  refine ⟨z, ?_, Or.inr ?_⟩
  · rw [hz]; decide
  · funext i
    simp only [e7OrbitRoot_apply, intVec, z]
    split_ifs <;> norm_num

lemma e7OrbitRoot_norm (S : E7FourSubset) :
    coordinateInner (e7OrbitRoot S).val (e7OrbitRoot S).val = 2 := by
  have h (i : Fin 8) : e7OrbitRoot S i * e7OrbitRoot S i = (1/4 : ℝ) := by
    rw [e7OrbitRoot_apply]; split_ifs <;> norm_num
  simp only [coordinateInner, h]
  norm_num

lemma coordinateInner_sub_left (x y z : Fin 8 → ℝ) :
    coordinateInner (x-y) z = coordinateInner x z-coordinateInner y z := by
  simp [coordinateInner, sub_mul, Finset.sum_sub_distrib]
lemma coordinateInner_smul_left (c : ℝ) (x y : Fin 8 → ℝ) :
    coordinateInner (c • x) y = c * coordinateInner x y := by
  simp [coordinateInner, mul_assoc, Finset.mul_sum]
lemma coordinateInner_comm (x y : Fin 8 → ℝ) : coordinateInner x y=coordinateInner y x := by
  simp [coordinateInner, mul_comm]

/-- Reflection in the hyperplane perpendicular to a root of squared norm two. -/
def e7RootReflection (a x : zeroSumSpace) : zeroSumSpace :=
  x - coordinateInner x.val a.val • a

lemma e7RootReflection_involutive (a : zeroSumSpace)
    (ha : coordinateInner a.val a.val=2) : Function.Involutive (e7RootReflection a) := by
  intro x
  have h : coordinateInner (e7RootReflection a x).val a.val = -coordinateInner x.val a.val := by
    change coordinateInner (x.val-coordinateInner x.val a.val • a.val) a.val = _
    rw [coordinateInner_sub_left, coordinateInner_smul_left, ha]
    ring
  unfold e7RootReflection at *
  rw [h]
  module

lemma e7RootReflection_lattice (a : zeroSumSpace) (ha : a ∈ e7Set)
    {x : zeroSumSpace} (hx : x ∈ e7ProjectedSet) : e7RootReflection a x ∈ e7ProjectedSet := by
  obtain ⟨k,hk⟩ := e7Projected_mem_dual hx a ha
  have ha' : a ∈ e7ProjectedSet := by
    simpa only [project8_coe] using project8_mem_e7Projected ha
  have ha'' : a ∈ e7ProjectedAddSubgroup := by
    change a ∈ (e7ProjectedAddSubgroup : Set zeroSumSpace)
    rwa [e7ProjectedAddSubgroup_coe]
  have hx' : x ∈ e7ProjectedAddSubgroup := by
    change x ∈ (e7ProjectedAddSubgroup : Set zeroSumSpace)
    rwa [e7ProjectedAddSubgroup_coe]
  rw [e7RootReflection, hk]
  have hsmul : (k : ℝ) • a = k • a := by
    exact Int.cast_smul_eq_zsmul ℝ k a
  rw [hsmul, ← e7ProjectedAddSubgroup_coe]
  exact e7ProjectedAddSubgroup.sub_mem hx' (e7ProjectedAddSubgroup.zsmul_mem ha'' k)

end PaperVerification.ColdSpots

namespace PaperVerification.ColdSpots
open scoped BigOperators
lemma e7RootReflection_sqDist (a : zeroSumSpace)
    (ha : coordinateInner a.val a.val=2) (x y : zeroSumSpace) :
    sqDist (e7RootReflection a x).val (e7RootReflection a y).val = sqDist x.val y.val := by
  let c := coordinateInner x.val a.val-coordinateInner y.val a.val
  have hc : coordinateInner (x.val-y.val) a.val=c := coordinateInner_sub_left _ _ _
  have hexpand (i : Fin 8) :
      (e7RootReflection a x i-e7RootReflection a y i)^2 =
      (x i-y i)^2 - 2*c*((x i-y i)*a i)+c^2*(a i*a i) := by
    change (x i-coordinateInner x.val a.val*a i-
      (y i-coordinateInner y.val a.val*a i))^2 = _
    dsimp [c]; ring
  unfold sqDist
  simp_rw [hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  change _-2*c*coordinateInner (x.val-y.val) a.val+c^2*coordinateInner a.val a.val = _
  rw [hc,ha]
  ring

lemma e7OrbitRoot_witness_inner (S : E7FourSubset) :
    coordinateInner e7Witness.val (e7OrbitRoot S).val =
      if (0 : Fin 8) ∈ S.val then (1/2 : ℝ) else -1/2 := by
  change coordinateInner (project8 e8Axis).val (e7OrbitRoot S).val = _
  rw [coordinateInner_project_left]
  simp only [coordinateInner, e8Axis, intVec]
  simp only [e7OrbitRoot_apply]
  simp
  split_ifs <;> norm_num

lemma e7OrbitRoot_witness (S : E7FourSubset) :
    e7RootReflection (e7OrbitRoot S) e7Witness =
      if (0 : Fin 8) ∈ S.val then e7Witness-e7PaperShift S
      else e7Witness+e7PaperShift S := by
  rw [e7RootReflection,e7OrbitRoot_witness_inner]
  unfold e7OrbitRoot
  split_ifs <;> module

end PaperVerification.ColdSpots

namespace PaperVerification.ColdSpots
open scoped BigOperators

def e7RootReflectionLinear (a : zeroSumSpace) : zeroSumSpace →ₗ[ℝ] zeroSumSpace where
  toFun := e7RootReflection a
  map_add' x y := by
    have h : coordinateInner (x+y).val a.val =
        coordinateInner x.val a.val + coordinateInner y.val a.val := by
      simp [coordinateInner, add_mul, Finset.sum_add_distrib]
    simp only [e7RootReflection, h, add_smul]
    abel
  map_smul' c x := by
    have h : coordinateInner (c • x).val a.val = c * coordinateInner x.val a.val :=
      coordinateInner_smul_left _ _ _
    simp only [e7RootReflection, h, RingHom.id_apply]
    module

def e7RootReflectionEquiv (a : zeroSumSpace) (ha : coordinateInner a.val a.val=2) :
    zeroSumSpace ≃ₗ[ℝ] zeroSumSpace :=
  { e7RootReflectionLinear a with
    invFun := e7RootReflection a
    left_inv := e7RootReflection_involutive a ha
    right_inv := e7RootReflection_involutive a ha }

lemma e7RootReflection_mem_iff (a : zeroSumSpace) (ha : a ∈ e7Set)
    (hn : coordinateInner a.val a.val=2) (x : zeroSumSpace) :
    e7RootReflection a x ∈ e7ProjectedSet ↔ x ∈ e7ProjectedSet := by
  constructor
  · intro h
    simpa only [e7RootReflection_involutive a hn x] using e7RootReflection_lattice a ha h
  · exact e7RootReflection_lattice a ha

end PaperVerification.ColdSpots

namespace PaperVerification.ColdSpots

/-- An affine automorphism preserving the lattice and its genuine Euclidean
squared distance. The default norm on coordinate functions is not used. -/
def IsE7AffineSymmetry (f : zeroSumSpace ≃ᵃ[ℝ] zeroSumSpace) : Prop :=
  (∀ x y, sqDist (f x).val (f y).val = sqDist x.val y.val) ∧
  (∀ x, f x ∈ e7ProjectedSet ↔ x ∈ e7ProjectedSet)

lemma e7AffineSymmetry_refl : IsE7AffineSymmetry (AffineEquiv.refl ℝ zeroSumSpace) := by
  exact ⟨fun _ _ => rfl, fun _ => Iff.rfl⟩

lemma e7AffineSymmetry_trans {f g : zeroSumSpace ≃ᵃ[ℝ] zeroSumSpace}
    (hf : IsE7AffineSymmetry f) (hg : IsE7AffineSymmetry g) :
    IsE7AffineSymmetry (f.trans g) := by
  exact ⟨fun x y => (hg.1 _ _).trans (hf.1 x y), fun x => (hg.2 _).trans (hf.2 x)⟩

lemma e7AffineSymmetry_symm {f : zeroSumSpace ≃ᵃ[ℝ] zeroSumSpace}
    (hf : IsE7AffineSymmetry f) : IsE7AffineSymmetry f.symm := by
  constructor
  · intro x y
    simpa using (hf.1 (f.symm x) (f.symm y)).symm
  · intro x
    simpa using (hf.2 (f.symm x)).symm

lemma e7AffineSymmetry_translation {t : zeroSumSpace} (ht : t ∈ e7ProjectedSet) :
    IsE7AffineSymmetry (AffineEquiv.constVAdd ℝ zeroSumSpace t) := by
  have ht' : t ∈ e7ProjectedAddSubgroup := by
    change t ∈ (e7ProjectedAddSubgroup : Set zeroSumSpace)
    rwa [e7ProjectedAddSubgroup_coe]
  constructor
  · intro x y
    change sqDist (t.val+x.val) (t.val+y.val) = _
    simpa only [add_comm t.val] using sqDist_add_add x.val y.val t.val
  · intro x
    change t+x ∈ e7ProjectedSet ↔ x ∈ e7ProjectedSet
    rw [← e7ProjectedAddSubgroup_coe]
    exact e7ProjectedAddSubgroup.add_mem_cancel_left ht'

lemma e7AffineSymmetry_reflection (a : zeroSumSpace) (ha : a ∈ e7Set)
    (hn : coordinateInner a.val a.val=2) :
    IsE7AffineSymmetry (e7RootReflectionEquiv a hn).toAffineEquiv := by
  exact ⟨e7RootReflection_sqDist a hn, e7RootReflection_mem_iff a ha hn⟩

end PaperVerification.ColdSpots

namespace PaperVerification.ColdSpots

lemma e7PaperPoint_affine_orbit (p : E7PaperIndex) :
    ∃ f : zeroSumSpace ≃ᵃ[ℝ] zeroSumSpace,
      IsE7AffineSymmetry f ∧ f e7Witness = e7PaperPoint p := by
  cases p with
  | none => exact ⟨AffineEquiv.refl ℝ zeroSumSpace, e7AffineSymmetry_refl, rfl⟩
  | some S =>
    let a := e7OrbitRoot S
    have ha : a ∈ e7Set := e7OrbitRoot_mem S
    have hn : coordinateInner a.val a.val = 2 := e7OrbitRoot_norm S
    let f := (e7RootReflectionEquiv a hn).toAffineEquiv
    have hf : IsE7AffineSymmetry f := e7AffineSymmetry_reflection a ha hn
    by_cases h : (0 : Fin 8) ∈ S.val
    · have ha' : a ∈ e7ProjectedSet := by
        simpa only [project8_coe] using project8_mem_e7Projected ha
      refine ⟨f.trans (AffineEquiv.constVAdd ℝ zeroSumSpace a),
        e7AffineSymmetry_trans hf (e7AffineSymmetry_translation ha'), ?_⟩
      change a + e7RootReflection a e7Witness = e7PaperPoint (some S)
      rw [e7PaperPoint_some, show a = e7OrbitRoot S from rfl,
        e7OrbitRoot_witness, if_pos h]
      unfold e7OrbitRoot
      module
    · refine ⟨f, hf, ?_⟩
      change e7RootReflection (e7OrbitRoot S) e7Witness = _
      rw [e7OrbitRoot_witness, if_neg h, e7PaperPoint_some]

/-- Every genuine E7* deep hole lies in the affine-isometry orbit of the
paper's distinguished hole. No genericity or choice of translation class is assumed. -/
theorem e7_deep_hole_affine_orbit (x : zeroSumSpace) (hx : IsE7DeepHole x) :
    ∃ f : zeroSumSpace ≃ᵃ[ℝ] zeroSumSpace,
      IsE7AffineSymmetry f ∧ f e7Witness = x := by
  obtain ⟨p,hp⟩ := (isE7DeepHole_iff_paper x).mp hx
  obtain ⟨f,hf,hfx⟩ := e7PaperPoint_affine_orbit p
  refine ⟨f.trans (AffineEquiv.constVAdd ℝ zeroSumSpace (x-e7PaperPoint p)),
    e7AffineSymmetry_trans hf (e7AffineSymmetry_translation hp), ?_⟩
  change x-e7PaperPoint p+f e7Witness=x
  rw [hfx]
  abel

/-- Transitivity on all actual E7* deep holes, by lattice-preserving affine
maps preserving the genuine Euclidean squared distance. -/
theorem e7_deep_holes_single_affine_orbit (x y : zeroSumSpace)
    (hx : IsE7DeepHole x) (hy : IsE7DeepHole y) :
    ∃ f : zeroSumSpace ≃ᵃ[ℝ] zeroSumSpace,
      IsE7AffineSymmetry f ∧ f x = y := by
  obtain ⟨f,hf,hfx⟩ := e7_deep_hole_affine_orbit x hx
  obtain ⟨g,hg,hgy⟩ := e7_deep_hole_affine_orbit y hy
  refine ⟨f.symm.trans g,e7AffineSymmetry_trans (e7AffineSymmetry_symm hf) hg,?_⟩
  change g (f.symm x)=y
  rw [← hfx, f.symm_apply_apply, hgy]

#print axioms e7_deep_holes_single_affine_orbit
end PaperVerification.ColdSpots

namespace PaperVerification.ColdSpots

/-- Literal Euclidean distance preservation on the seven-dimensional
zero-sum subspace, independent of the coordinate function norm. -/
theorem IsE7AffineSymmetry.euclidean_distance
    {f : zeroSumSpace ≃ᵃ[ℝ] zeroSumSpace} (hf : IsE7AffineSymmetry f) (x y : zeroSumSpace) :
    dist (WithLp.toLp 2 (f x).val : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (f y).val) =
      dist (WithLp.toLp 2 x.val : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 y.val) := by
  have h := hf.1 x y
  rw [sqDist_eq_euclidean_dist_sq,sqDist_eq_euclidean_dist_sq] at h
  have h₁ : 0 ≤ dist (WithLp.toLp 2 (f x).val : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (f y).val) := dist_nonneg
  have h₂ : 0 ≤ dist (WithLp.toLp 2 x.val : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 y.val) := dist_nonneg
  nlinarith

end PaperVerification.ColdSpots
