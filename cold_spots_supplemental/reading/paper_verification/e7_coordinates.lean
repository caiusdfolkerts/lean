module
public import PaperVerification.DnGaussian
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.BigOperators.Fin
@[expose] public section
/-!
# The dual E7 lattice in its genuine seven-dimensional ambient space

All ambient points have coordinate sum zero. The lattice below is the orthogonal
projection of the actual E8 coordinate lattice, and the duality theorem identifies
it with the integral dual of E8 intersected with that hyperplane. Thus no assertion
about a rank-seven lattice quantifies over the larger eight-dimensional space.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def zeroSumSpace : Submodule ℝ (Fin 8 → ℝ) where
  carrier := {x | ∑ i, x i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change (∑ i, x i) = 0 at hx
    change (∑ i, y i) = 0 at hy
    change (∑ i, (x + y) i) = 0
    simp only [Pi.add_apply, Finset.sum_add_distrib, hx, hy, zero_add]
  smul_mem' := by
    intro a x hx
    change (∑ i, x i) = 0 at hx
    change (∑ i, (a • x) i) = 0
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hx, mul_zero]

/-- Evaluation of a vector in the literal zero-sum subspace. -/
instance zeroSumSpaceCoeFun : CoeFun zeroSumSpace (fun _ ↦ Fin 8 → ℝ) where
  coe x := x.val

def project8 (x : Fin 8 → ℝ) : zeroSumSpace :=
  ⟨fun i ↦ x i - (∑ j, x j) / 8, by
    change (∑ i, (x i - (∑ j, x j) / 8)) = 0
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring⟩

@[simp] lemma project8_apply (x : Fin 8 → ℝ) (i : Fin 8) :
    project8 x i = x i - (∑ j, x j) / 8 := rfl

lemma zeroSumSpace_sum (x : zeroSumSpace) : (∑ i, x i) = 0 := x.property

@[simp] lemma project8_coe (x : zeroSumSpace) : project8 x.val = x := by
  apply Subtype.ext
  ext i
  simp only [project8_apply, zeroSumSpace_sum, zero_div, sub_zero]

theorem project8_add_constant (x : Fin 8 → ℝ) (c : ℝ) :
    project8 (fun i ↦ x i + c) = project8 x := by
  apply Subtype.ext
  ext i
  simp only [project8_apply, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

def coordinateInner (x y : Fin 8 → ℝ) : ℝ := ∑ i, x i * y i

theorem coordinateInner_project_left (x : Fin 8 → ℝ) (y : zeroSumSpace) :
    coordinateInner (project8 x).val y.val = coordinateInner x y.val := by
  unfold coordinateInner
  simp only [project8_apply, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum,
    zeroSumSpace_sum, mul_zero, sub_zero]

def e7Set : Set zeroSumSpace := {x | x.val ∈ dPlusSet 8}

def e7DualSet : Set zeroSumSpace :=
  {y | ∀ x ∈ e7Set, ∃ k : ℤ, coordinateInner y.val x.val = (k : ℝ)}

def e7ProjectedSet : Set zeroSumSpace :=
  {y | ∃ z : Fin 8 → ℤ, Even (∑ i, z i) ∧ y = project8 (intVec z)}

theorem project8_mem_e7Projected {v : Fin 8 → ℝ} (hv : v ∈ dPlusSet 8) :
    project8 v ∈ e7ProjectedSet := by
  rcases hv with ⟨z, hz, rfl | rfl⟩
  · exact ⟨z, hz, rfl⟩
  · exact ⟨z, hz, project8_add_constant (intVec z) (1 / 2)⟩

theorem e7Projected_mem_dual {y : zeroSumSpace} (hy : y ∈ e7ProjectedSet) :
    y ∈ e7DualSet := by
  rcases hy with ⟨z, hz, rfl⟩
  intro x hx
  rw [coordinateInner_project_left]
  rcases hx with ⟨w, hw, h | h⟩
  · refine ⟨∑ i, z i * w i, ?_⟩
    rw [h]
    simp [coordinateInner, intVec]
  · obtain ⟨k, hk⟩ := hz
    refine ⟨(∑ i, z i * w i) + k, ?_⟩
    rw [h]
    simp only [coordinateInner, intVec, mul_add, Finset.sum_add_distrib,
      ← Finset.sum_mul, Int.cast_add, Int.cast_sum, Int.cast_mul]
    have hcast : (∑ i, (z i : ℝ)) = (k : ℝ) + k := by exact_mod_cast hk
    rw [hcast]
    ring

def coordinateDifferenceInt (i : Fin 8) : Fin 8 → ℤ :=
  fun j ↦ (if j = i then 1 else 0) - (if j = 0 then 1 else 0)

lemma sum_coordinateDifferenceInt (i : Fin 8) :
    (∑ j, coordinateDifferenceInt i j) = 0 := by
  simp [coordinateDifferenceInt, Finset.sum_sub_distrib]

def coordinateDifference (i : Fin 8) : zeroSumSpace :=
  ⟨intVec (coordinateDifferenceInt i), by
    change (∑ j, (coordinateDifferenceInt i j : ℝ)) = 0
    exact_mod_cast sum_coordinateDifferenceInt i⟩

lemma coordinateDifference_mem_e7 (i : Fin 8) : coordinateDifference i ∈ e7Set := by
  refine ⟨coordinateDifferenceInt i, ?_, Or.inl rfl⟩
  rw [sum_coordinateDifferenceInt]
  exact ⟨0, rfl⟩

lemma inner_coordinateDifference (y : zeroSumSpace) (i : Fin 8) :
    coordinateInner y.val (coordinateDifference i).val = y i - y 0 := by
  simp [coordinateInner, coordinateDifference, coordinateDifferenceInt, intVec,
    mul_sub, Finset.sum_sub_distrib, mul_ite]

def halfRootInt : Fin 8 → ℤ := fun i ↦ if i.val < 4 then 0 else -1

lemma sum_halfRootInt : (∑ i, halfRootInt i) = -4 := by
  norm_num [halfRootInt, Fin.sum_univ_succ]

def balancedHalfRoot : zeroSumSpace :=
  ⟨fun i ↦ (halfRootInt i : ℝ) + 1 / 2, by
    change (∑ i, ((halfRootInt i : ℝ) + 1 / 2)) = 0
    norm_num [halfRootInt, Fin.sum_univ_succ]⟩

lemma balancedHalfRoot_mem_e7 : balancedHalfRoot ∈ e7Set := by
  refine ⟨halfRootInt, ?_, Or.inr rfl⟩
  rw [sum_halfRootInt]
  exact ⟨-2, by norm_num⟩

/-- An explicit coordinate proof of the E7 dual/projection correspondence. -/
theorem e7DualSet_eq_projected : e7DualSet = e7ProjectedSet := by
  apply Set.Subset.antisymm
  · intro y hy
    have hi (i : Fin 8) : ∃ k : ℤ, y i - y 0 = (k : ℝ) := by
      simpa only [inner_coordinateDifference] using
        hy (coordinateDifference i) (coordinateDifference_mem_e7 i)
    choose z hz using hi
    have hsum : (∑ i, (z i : ℝ)) = -8 * y 0 := by
      calc
        _ = ∑ i, (y i - y 0) := Finset.sum_congr rfl (fun i _ ↦ (hz i).symm)
        _ = _ := by
          rw [Finset.sum_sub_distrib, zeroSumSpace_sum]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
    have hproj : y = project8 (intVec z) := by
      apply Subtype.ext
      ext i
      simp only [project8_apply, intVec, hsum]
      linarith [hz i]
    obtain ⟨k, hk⟩ := hy balancedHalfRoot balancedHalfRoot_mem_e7
    rw [hproj, coordinateInner_project_left] at hk
    have hdot : coordinateInner (intVec z) balancedHalfRoot.val =
        ((∑ i, z i * halfRootInt i : ℤ) : ℝ) + (∑ i, (z i : ℝ)) / 2 := by
      simp only [coordinateInner, intVec, balancedHalfRoot, mul_add,
        Finset.sum_add_distrib, ← Finset.sum_mul, Int.cast_sum, Int.cast_mul]
      ring
    rw [hdot] at hk
    push_cast at hk
    have hint : (∑ i, z i) =
        2 * (k - ∑ i, z i * halfRootInt i) := by
      apply Int.cast_injective (α := ℝ)
      push_cast
      linarith
    refine ⟨z, ?_, hproj⟩
    rw [hint]
    exact even_two_mul _
  · intro y hy
    exact e7Projected_mem_dual hy

def e7Lift (y : e7ProjectedSet) : Fin 8 → ℤ := Classical.choose y.property

lemma e7Lift_even (y : e7ProjectedSet) : Even (∑ i, e7Lift y i) :=
  (Classical.choose_spec y.property).1

lemma e7Lift_projects (y : e7ProjectedSet) : project8 (intVec (e7Lift y)) = y.val :=
  (Classical.choose_spec y.property).2.symm

lemma even_sum_add_constant (z : Fin 8 → ℤ) (hz : Even (∑ i, z i)) (q : ℤ) :
    Even (∑ i, (z i + q)) := by
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact hz.add (by exact ⟨4 * q, by ring⟩)

lemma intVec_add_half_multiple_mem (z : Fin 8 → ℤ) (hz : Even (∑ i, z i)) (k : ℤ) :
    (fun i ↦ (z i : ℝ) + (k : ℝ) / 2) ∈ dPlusSet 8 := by
  rcases Int.even_or_odd k with he | ho
  · obtain ⟨q, hq⟩ := he
    refine ⟨fun i ↦ z i + q, even_sum_add_constant z hz q, Or.inl ?_⟩
    ext i
    rw [hq]
    simp only [Int.cast_add, intVec]
    ring
  · obtain ⟨q, hq⟩ := ho
    refine ⟨fun i ↦ z i + q, even_sum_add_constant z hz q, Or.inr ?_⟩
    ext i
    rw [hq]
    push_cast
    ring

def e8FibreMap (yk : e7ProjectedSet × ℤ) : dPlusSet 8 :=
  ⟨fun i ↦ (e7Lift yk.1 i : ℝ) + (yk.2 : ℝ) / 2,
    intVec_add_half_multiple_mem _ (e7Lift_even yk.1) yk.2⟩

lemma e8FibreMap_projects (y : e7ProjectedSet) (k : ℤ) :
    project8 (e8FibreMap (y, k)).val = y.val := by
  change project8 (fun i ↦ (e7Lift y i : ℝ) + (k : ℝ) / 2) = y.val
  rw [project8_add_constant]
  change project8 (intVec (e7Lift y)) = y.val
  exact e7Lift_projects y

/-- Exact infinite-fibre parametrization of E8, with no multiplicity. -/
theorem e8FibreMap_bijective : Function.Bijective e8FibreMap := by
  constructor
  · rintro ⟨y, k⟩ ⟨z, l⟩ h
    have hp := congrArg (fun v : dPlusSet 8 ↦ project8 v.val) h
    simp only [e8FibreMap_projects] at hp
    have hyz : y = z := Subtype.ext hp
    subst z
    have h0 := congrFun (congrArg Subtype.val h) 0
    change (e7Lift y 0 : ℝ) + (k : ℝ) / 2 = (e7Lift y 0 : ℝ) + (l : ℝ) / 2 at h0
    have hkl : k = l := Int.cast_injective (by linarith : (k : ℝ) = (l : ℝ))
    subst l
    rfl
  · intro v
    let y : e7ProjectedSet := ⟨project8 v.val, project8_mem_e7Projected v.property⟩
    have hp : project8 (intVec (e7Lift y)) = project8 v.val := e7Lift_projects y
    have hdiff (i : Fin 8) : v.val i - (e7Lift y i : ℝ) =
        v.val 0 - (e7Lift y 0 : ℝ) := by
      have hi := congrFun (congrArg Subtype.val hp) i
      have h0 := congrFun (congrArg Subtype.val hp) 0
      simp only [project8_apply, intVec] at hi h0
      linarith
    rcases v.property with ⟨w, hw, hv | hv⟩
    · refine ⟨(y, 2 * (w 0 - e7Lift y 0)), ?_⟩
      apply Subtype.ext
      ext i
      change (e7Lift y i : ℝ) + ((2 * (w 0 - e7Lift y 0) : ℤ) : ℝ) / 2 = v.val i
      have hd := hdiff i
      rw [hv] at hd ⊢
      simp only [intVec, Int.cast_mul, Int.cast_ofNat, Int.cast_sub] at hd ⊢
      linarith
    · refine ⟨(y, 2 * (w 0 - e7Lift y 0) + 1), ?_⟩
      apply Subtype.ext
      ext i
      change (e7Lift y i : ℝ) + ((2 * (w 0 - e7Lift y 0) + 1 : ℤ) : ℝ) / 2 = v.val i
      have hd := hdiff i
      rw [hv] at hd ⊢
      push_cast at hd ⊢
      linarith

def e8FibreEquiv : e7ProjectedSet × ℤ ≃ dPlusSet 8 :=
  Equiv.ofBijective e8FibreMap e8FibreMap_bijective

end PaperVerification.ColdSpots
