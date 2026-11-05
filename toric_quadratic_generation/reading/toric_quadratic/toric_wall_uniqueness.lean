module

public import PaperVerification.ToricContractionCones
public import PaperVerification.ToricStarPurity
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Uniqueness of the opposite smooth cone at a wall

Two prospective opposite rays with the same negative normal coordinate
produce a common point by adding nonnegative wall coordinates. The fan's
actual common-ray intersection forces the rays to coincide.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- An integral wall in a genuine basis has at most one adjacent fan ray
whose missing coordinate is strictly negative. The two coefficients are
scaled to the same height before applying the genuine fan intersection. -/
theorem opposite_wall_ray_unique_of_negative (b : Module.Basis (Fin n) ℤ (Lattice n))
    (j : Fin n) (w z : Lattice n)
    (hw : insert w ((Finset.univ.erase j).image b) ∈ «Σ».cones)
    (hz : insert z ((Finset.univ.erase j).image b) ∈ «Σ».cones)
    (hjw : b.repr w j < 0) (hjz : b.repr z j < 0) : w = z := by
  let W := (Finset.univ.erase j).image b
  let B := integralBasisReal b
  let α : ℝ := -(b.repr z j : ℝ)
  let β : ℝ := -(b.repr w j : ℝ)
  have hα : 0 < α := neg_pos.mpr (by exact_mod_cast hjz)
  have hβ : 0 < β := neg_pos.mpr (by exact_mod_cast hjw)
  let d : Fin n → ℝ := fun i => B.repr (β • embed n z - α • embed n w) i
  let u : Fin n → ℝ := fun i => |d i| + d i
  let v : Fin n → ℝ := fun i => |d i|
  have hdj : d j = 0 := by
    simp only [d, B, map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply,
      integralBasisReal_repr, smul_eq_mul, α, β]
    ring
  have hu (i : Fin n) : 0 ≤ u i := by
    have h := neg_abs_le (d i)
    dsimp only [u]
    linarith
  have hv (i : Fin n) : 0 ≤ v i := abs_nonneg _
  have huj : u j = 0 := by simp [u, hdj]
  have hvj : v j = 0 := by simp [v, hdj]
  have hwall (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (haj : a j = 0)
      (y : Lattice n) : (∑ i, a i • B i) ∈ latticeRayCone (insert y W) := by
    apply Submodule.sum_mem
    intro i hi
    by_cases hij : i = j
    · subst i
      simp only [haj, zero_smul]
      exact Submodule.zero_mem _
    · rw [integralBasisReal_apply]
      apply PointedCone.smul_mem _ (ha i)
      apply latticeRayCone_generator
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨i, Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩, rfl⟩)
  have hsum : (∑ i, u i • B i) =
      (∑ i, v i • B i) + (β • embed n z - α • embed n w) := by
    simp only [u, add_smul, Finset.sum_add_distrib, v, d, Module.Basis.sum_repr]
  have hbalance : α • embed n w + (∑ i, u i • B i) =
      β • embed n z + (∑ i, v i • B i) := by
    rw [hsum]
    abel
  have hxw : α • embed n w + (∑ i, u i • B i) ∈ latticeRayCone (insert w W) :=
    (latticeRayCone (insert w W)).add_mem
      (PointedCone.smul_mem _ hα.le (latticeRayCone_generator _ (Finset.mem_insert_self _ _)))
      (hwall u hu huj w)
  have hxz : α • embed n w + (∑ i, u i • B i) ∈ latticeRayCone (insert z W) := by
    rw [hbalance]
    exact (latticeRayCone (insert z W)).add_mem
      (PointedCone.smul_mem _ hβ.le (latticeRayCone_generator _ (Finset.mem_insert_self _ _)))
      (hwall v hv hvj z)
  have hxmeet : α • embed n w + (∑ i, u i • B i) ∈
      latticeRayCone ((insert w W) ∩ (insert z W)) := by
    rw [← «Σ».intersection _ hw _ hz]
    exact ⟨hxw, hxz⟩
  have hface := «Σ».cone_subset_isFaceOf hw
    (Finset.inter_subset_left : insert w W ∩ insert z W ⊆ insert w W)
  have hwmeet : embed n w ∈ latticeRayCone ((insert w W) ∩ (insert z W)) :=
    hface.mem_of_smul_add_mem
      (latticeRayCone_generator _ (Finset.mem_insert_self _ _)) (hwall u hu huj w) hα hxmeet
  have hwrays : w ∈ «Σ».rays := («Σ».mem_rays_iff w).mpr
    ⟨insert w W, hw, Finset.mem_insert_self _ _⟩
  have hwz : w ∈ insert z W := («Σ».ray_mem_cone_iff hz hwrays).mp
    (latticeRayCone_mono Finset.inter_subset_right hwmeet)
  rcases Finset.mem_insert.mp hwz with hwz | hwW
  · exact hwz
  · obtain ⟨i, hi, hwi⟩ := Finset.mem_image.mp hwW
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    rw [← hwi] at hjw
    simp only [Module.Basis.repr_self_apply, if_neg hij] at hjw
    norm_num at hjw

/-- The normalized smooth-wall form used by primitive contraction relations. -/
theorem opposite_wall_ray_unique (b : Module.Basis (Fin n) ℤ (Lattice n))
    (j : Fin n) (w z : Lattice n)
    (hw : insert w ((Finset.univ.erase j).image b) ∈ «Σ».cones)
    (hz : insert z ((Finset.univ.erase j).image b) ∈ «Σ».cones)
    (hjw : b.repr w j = -1) (hjz : b.repr z j = -1) : w = z :=
  «Σ».opposite_wall_ray_unique_of_negative b j w z hw hz (by omega) (by omega)

end SmoothCompleteFan

end PaperVerification.ToricGeometry
