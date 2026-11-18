module

public import PaperVerification.E8TranslationClasses
public import PaperVerification.E7Transfer


@[expose] public section
/-! # Actual projection classes in E7*

The only extra identification of half-E8 classes under orthogonal projection is
addition of the binary class of the projection root.  This is proved using the
integral E8 basis and the exact kernel of the coordinate projection.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

theorem project8_zero : project8 0 = 0 := by
  apply Subtype.ext
  funext i
  simp [project8]

theorem project8_add (x y : Fin 8 → ℝ) : project8 (x + y) = project8 x + project8 y := by
  apply Subtype.ext
  funext i
  change (project8 (x + y)).val i = (project8 x).val i + (project8 y).val i
  simp only [project8_apply, Pi.add_apply, Finset.sum_add_distrib]
  ring

theorem project8_sub (x y : Fin 8 → ℝ) : project8 (x - y) = project8 x - project8 y := by
  apply Subtype.ext
  funext i
  change (project8 (x - y)).val i = (project8 x).val i - (project8 y).val i
  simp only [project8_apply, Pi.sub_apply, Finset.sum_sub_distrib]
  ring

theorem project8_eq_zero_iff_constant (x : Fin 8 → ℝ) :
    project8 x = 0 ↔ ∃ a : ℝ, x = fun _ => a := by
  constructor
  · intro h
    refine ⟨(∑ i, x i) / 8, ?_⟩
    funext i
    have hi := congrArg (fun y : zeroSumSpace => y i) h
    change x i - (∑ j, x j) / 8 = 0 at hi
    linarith
  · rintro ⟨a, rfl⟩
    apply Subtype.ext
    funext i
    norm_num [project8_apply]

def project8AddHom : (Fin 8 → ℝ) →+ zeroSumSpace where
  toFun := project8
  map_zero' := project8_zero
  map_add' := project8_add

def e7ProjectedAddSubgroup : AddSubgroup zeroSumSpace :=
  (dPlusAddSubgroup 8 (by decide)).map project8AddHom

theorem e7ProjectedAddSubgroup_coe : (e7ProjectedAddSubgroup : Set zeroSumSpace) = e7ProjectedSet := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact project8_mem_e7Projected hx
  · rintro ⟨z, hz, rfl⟩
    exact ⟨intVec z, ⟨z, hz, Or.inl rfl⟩, rfl⟩

theorem e7SquaredDepth_add {g : zeroSumSpace} (hg : g ∈ e7ProjectedSet) (x : zeroSumSpace) :
    e7SquaredDepth (x + g) = e7SquaredDepth x := by
  have hgin : g ∈ e7ProjectedAddSubgroup := by
    change g ∈ (e7ProjectedAddSubgroup : Set zeroSumSpace)
    rwa [e7ProjectedAddSubgroup_coe]
  unfold e7SquaredDepth
  congr 1
  ext r
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hmem : y - g ∈ e7ProjectedSet := by
      rw [← e7ProjectedAddSubgroup_coe] at hy ⊢
      exact e7ProjectedAddSubgroup.sub_mem hy hgin
    refine ⟨y - g, hmem, ?_⟩
    exact (sqDist_add_left x.val y.val g.val).symm
  · rintro ⟨y, hy, rfl⟩
    have hmem : y + g ∈ e7ProjectedSet := by
      rw [← e7ProjectedAddSubgroup_coe] at hy ⊢
      exact e7ProjectedAddSubgroup.add_mem hy hgin
    refine ⟨y + g, hmem, ?_⟩
    exact sqDist_add_add x.val y.val g.val

theorem isE7DeepHole_add_iff {g : zeroSumSpace} (hg : g ∈ e7ProjectedSet) (x : zeroSumSpace) :
    IsE7DeepHole (x + g) ↔ IsE7DeepHole x := by
  rw [isE7DeepHole_iff_depth, isE7DeepHole_iff_depth, e7SquaredDepth_add hg]

theorem e8RootSum_halfCoordinates :
    e8RootSum (fun i => (e8HalfCoordinates i : ℝ)) = fun _ => 1 / 2 := by
  ext i
  fin_cases i <;> norm_num [e8RootSum, e8SimpleRoot, e8HalfCoordinates, Fin.sum_univ_succ]

theorem e8HalfRootSum_halfCoordinates : e8HalfRootSum e8HalfCoordinates = fun _ => 1 / 4 := by
  ext i
  fin_cases i <;> norm_num [e8HalfRootSum, e8RootSum, e8SimpleRoot, e8HalfCoordinates, Fin.sum_univ_succ]

theorem e8_constant_half_integer {a : ℝ} (ha : (fun _ : Fin 8 => a) ∈ dPlusSet 8) :
    ∃ m : ℤ, a = (m : ℝ) / 2 := by
  rcases ha with ⟨z, hz, he | he⟩
  · have h := congrFun he 0
    refine ⟨2 * z 0, ?_⟩
    change a = (z 0 : ℝ) at h
    push_cast
    linarith
  · have h := congrFun he 0
    refine ⟨2 * z 0 + 1, ?_⟩
    push_cast
    linarith

theorem e7Projected_halfRoot_difference_iff (t u : Fin 8 → ℤ) :
    project8 (e8HalfRootSum t) - project8 (e8HalfRootSum u) ∈ e7ProjectedSet ↔
      (fun i => (t i : Binary)) = (fun i => (u i : Binary)) ∨
        (fun i => (t i : Binary)) = (fun i => (u i : Binary)) + e8BinaryRoot := by
  constructor
  · rintro ⟨z, hz, hproj⟩
    obtain ⟨k, hk⟩ := (e8_mem_iff_integer_root_coordinates (intVec z)).mp
      (show intVec z ∈ dPlusSet 8 from ⟨z, hz, Or.inl rfl⟩)
    let w : Fin 8 → ℤ := t - u - fun i => 2 * k i
    have hhalf : e8HalfRootSum w = e8HalfRootSum t - e8HalfRootSum u - intVec z := by
      rw [e8HalfRootSum_sub, e8HalfRootSum_sub, e8HalfRootSum_two, ← hk]
    have hzero : project8 (e8HalfRootSum w) = 0 := by
      rw [hhalf, project8_sub, project8_sub, hproj, sub_self]
    obtain ⟨a, ha⟩ := (project8_eq_zero_iff_constant _).mp hzero
    have hroot : e8RootSum (fun i => (w i : ℝ)) = fun _ => 2 * a := by
      rw [← e8HalfRootSum_double, ha]
    have hmem : (fun _ : Fin 8 => 2 * a) ∈ dPlusSet 8 := hroot ▸ e8RootSum_int_mem w
    obtain ⟨m, hm⟩ := e8_constant_half_integer hmem
    have hmr : e8RootSum (fun i => ((m * e8HalfCoordinates i : ℤ) : ℝ)) = fun _ => (m : ℝ) / 2 := by
      have he : (fun i => ((m * e8HalfCoordinates i : ℤ) : ℝ)) =
          (m : ℝ) • (fun i => (e8HalfCoordinates i : ℝ)) := by funext i; simp
      rw [he, e8RootSum_smul, e8RootSum_halfCoordinates]
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    have hw : ∀ i, w i = m * e8HalfCoordinates i := by
      have he := e8RootSum_injective (hroot.trans (by rw [hm]; exact hmr.symm))
      intro i
      exact_mod_cast congrFun he i
    have hcast (i : Fin 8) : (t i : Binary) - (u i : Binary) = (m : Binary) * e8BinaryRoot i := by
      have h := congrArg (fun v : ℤ => (v : Binary)) (hw i)
      simpa [w, e8BinaryRoot] using h
    rcases binary_eq_zero_or_one (m : Binary) with hm0 | hm1
    · left
      funext i
      have h := hcast i
      simpa only [hm0, zero_mul, sub_eq_zero] using h
    · right
      funext i
      have h := hcast i
      rw [hm1, one_mul] at h
      exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  · rintro (h | h)
    · rw [← project8_sub]
      exact project8_mem_e7Projected ((e8HalfRootSum_sub_mem_iff t u).mpr h)
    · let w : Fin 8 → ℤ := t - u - e8HalfCoordinates
      have hw : e8HalfRootSum w ∈ dPlusSet 8 := by
        apply (e8HalfRootSum_mem_iff w).mpr
        intro i
        apply ZMod.intCast_eq_zero_iff_even.mp
        have hi := congrFun h i
        change (t i : Binary) = (u i : Binary) + e8BinaryRoot i at hi
        simp only [w, Pi.sub_apply, Int.cast_sub, hi, e8BinaryRoot]
        ring
      have hp := project8_mem_e7Projected hw
      have he : project8 (e8HalfRootSum w) = project8 (e8HalfRootSum t) - project8 (e8HalfRootSum u) := by
        rw [e8HalfRootSum_sub, e8HalfRootSum_sub, e8HalfRootSum_halfCoordinates,
          project8_sub, project8_sub]
        have hz : project8 (fun _ : Fin 8 => (1 / 4 : ℝ)) = 0 :=
          (project8_eq_zero_iff_constant _).mpr ⟨1 / 4, rfl⟩
        rw [hz, sub_zero]
      rwa [he] at hp

def e8HalfSumInt (t : Fin 8 → ℤ) : ℤ :=
  e8IntegralQ (t + e8HalfCoordinates) - e8IntegralQ t - e8IntegralQ e8HalfCoordinates

theorem e8HalfRootSum_sum (t : Fin 8 → ℤ) :
    (∑ i, e8HalfRootSum t i) = (e8HalfSumInt t : ℝ) := by
  simp [e8HalfSumInt, e8HalfRootSum, e8IntegralQ, e8RootSum, e8SimpleRoot,
    e8HalfCoordinates, Fin.sum_univ_succ]
  ring

theorem e8HalfSumInt_cast (t : Fin 8 → ℤ) :
    (e8HalfSumInt t : Binary) = e8BinaryPolar (fun i => (t i : Binary)) e8BinaryRoot := by
  simp only [e8HalfSumInt, Int.cast_sub, e8IntegralQ_cast, e8BinaryPolar, e8BinaryRoot,
    Pi.add_apply, Int.cast_add]
  rfl

theorem e7Slice_project8_of_sum_one {x : Fin 8 → ℝ} (hx : (∑ i, x i) = 1) :
    e7Slice (project8 x) = x := by
  funext i
  simp only [e7Slice, project8_apply, hx]
  ring

theorem e7_project_deep_of_odd_sum {x : Fin 8 → ℝ} (hx : IsDeepHole (dPlusSet 8) x)
    {s : ℤ} (hs : (∑ i, x i) = (s : ℝ)) (hodd : Odd s) : IsE7DeepHole (project8 x) := by
  obtain ⟨k, hk⟩ := hodd
  let z : Fin 8 → ℤ := fun i => if i = 0 then 2 * k else 0
  have hzsum : (∑ i, z i) = 2 * k := by simp [z]
  have hz : intVec z ∈ dPlusSet 8 := ⟨z, by rw [hzsum]; exact even_two.mul_right k, Or.inl rfl⟩
  let y := x - intVec z
  have hysum : (∑ i, y i) = 1 := by
    simp only [y, Pi.sub_apply, Finset.sum_sub_distrib, intVec, ← Int.cast_sum, hzsum, hs, hk]
    push_cast
    ring
  have hy : IsDeepHole (dPlusSet 8) y := by
    rw [isDeepHole_dPlus_iff_depth (by decide : 8 ≤ 8) (by decide : Even 8)]
    change squaredDepth (dPlusSet 8) (x - intVec z) = _
    have htrans := squaredDepth_sub_of_subgroup (dPlusAddSubgroup 8 (by decide)) x (intVec z) hz
    change squaredDepth (dPlusSet 8) (x - intVec z) = squaredDepth (dPlusSet 8) x at htrans
    rw [htrans]
    exact (isDeepHole_dPlus_iff_depth (by decide : 8 ≤ 8) (by decide : Even 8) x).mp hx
  have hproj : IsE7DeepHole (project8 y) := by
    apply (isDeepHole_slice_iff _).mp
    rw [e7Slice_project8_of_sum_one hysum]
    exact hy
  have h := (isE7DeepHole_add_iff (project8_mem_e7Projected hz) (project8 y)).mpr hproj
  have he : project8 y + project8 (intVec z) = project8 x := by
    rw [← project8_add]
    congr 1
    dsimp [y]
    abel
  rwa [he] at h

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.e7Projected_halfRoot_difference_iff
