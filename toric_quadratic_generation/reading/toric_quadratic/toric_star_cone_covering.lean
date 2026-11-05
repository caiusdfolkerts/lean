module
public import PaperVerification.ToricFanFoundations
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
@[expose] public section
/-!
# The actual support of a finite star subdivision

These lemmas work with ordinary finite nonnegative spans. In particular, the
new ray is the actual sum of the old focus rays, and preservation of support
is proved by subtracting a minimum coefficient.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Intersecting a finitely generated subcone with an actual face keeps
exactly the generators belonging to that face. -/
theorem finiteRayCone_inf_face (C F : PointedCone ℝ E) (hF : F.IsFaceOf C)
    (s : Finset E) (hs : ∀ v ∈ s, v ∈ C) :
    finiteRayCone s ⊓ F = finiteRayCone (s.filter (fun v => v ∈ F)) := by
  apply le_antisymm
  · rintro x ⟨⟨c, hc, hsum⟩, hxF⟩
    have hzero (v : E) (hv : v ∈ s) (hvF : v ∉ F) : c v = 0 := by
      by_contra hne
      have hpos : 0 < c v := lt_of_le_of_ne (hc v hv) (Ne.symm hne)
      apply hvF
      apply hF.mem_of_smul_add_mem (hs v hv)
        (Submodule.sum_mem _ (fun w hw => PointedCone.smul_mem _
          (hc w (Finset.mem_of_mem_erase hw)) (hs w (Finset.mem_of_mem_erase hw)))) hpos
      rw [Finset.add_sum_erase s (fun w => c w • w) hv, hsum]
      exact hxF
    refine ⟨c, fun v hv => hc v ((Finset.mem_filter.mp hv).1), ?_⟩
    calc
      (∑ v ∈ s.filter (fun v => v ∈ F), c v • v) = ∑ v ∈ s, c v • v := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro v hv hvfilter
        have hvF : v ∉ F := fun h => hvfilter (Finset.mem_filter.mpr ⟨hv, h⟩)
        rw [hzero v hv hvF, zero_smul]
      _ = x := hsum
  · rintro x ⟨c, hc, hsum⟩
    refine ⟨finiteRayCone_mono (Finset.filter_subset _ _) ⟨c, hc, hsum⟩, ?_⟩
    rw [← hsum]
    exact Submodule.sum_mem _ (fun v hv =>
      PointedCone.smul_mem _ (hc v hv) (Finset.mem_filter.mp hv).2)

/-- The actual ray set of one cone in the star subdivision of `s` along
the nonempty subset `t`, omitting the selected old ray `v`. -/
def starRaySet (s t : Finset E) (v : E) : Finset E :=
  insert (∑ w ∈ t, w) (s.erase v)

omit [Module ℝ E] in
/-- Membership in the actual star ray set, independent of the implementation
of decidable equality used by its finite-set operations. -/
theorem mem_starRaySet (s t : Finset E) (v w : E) :
    w ∈ starRaySet s t v ↔ w = (∑ z ∈ t, z) ∨ (w ≠ v ∧ w ∈ s) := by
  simp only [starRaySet, Finset.mem_insert, Finset.mem_erase]

/-- Every new cone is contained in its old parent cone. -/
theorem finiteRayCone_starRaySet_le {s t : Finset E} (hts : t ⊆ s) (v : E) :
    finiteRayCone (starRaySet s t v) ≤ finiteRayCone s := by
  rw [finiteRayCone_eq_hull]
  apply Submodule.span_le.mpr
  intro w hw
  rcases Finset.mem_insert.mp hw with rfl | hw
  · exact Submodule.sum_mem _ (fun w hw => finiteRayCone_generator s (hts hw))
  · exact finiteRayCone_generator s (Finset.mem_of_mem_erase hw)

/-- A cone is covered by the actual cones obtained by replacing one focus
ray with the sum of all focus rays. No smoothness or linear independence is
needed for this support assertion. -/
theorem finiteRayCone_star_cover {s t : Finset E} (hts : t ⊆ s)
    (ht : t.Nonempty) {x : E} (hx : x ∈ finiteRayCone s) :
    ∃ v ∈ t, x ∈ finiteRayCone (starRaySet s t v) := by
  obtain ⟨c, hc, hsum⟩ := hx
  obtain ⟨v, hv, hmin⟩ := t.exists_min_image c ht
  have hvs : v ∈ s := hts hv
  let d : E → ℝ := fun w => c w - if w ∈ t then c v else 0
  have hd (w : E) (hw : w ∈ s) : 0 ≤ d w := by
    by_cases hwt : w ∈ t
    · simp only [d, if_pos hwt]
      exact sub_nonneg.mpr (hmin w hwt)
    · simp only [d, if_neg hwt, sub_zero]
      exact hc w hw
  have hdv : d v = 0 := by simp [d, hv]
  have hcond : (∑ w ∈ s, (if w ∈ t then c v else 0) • w) =
      c v • ∑ w ∈ t, w := by
    calc
      (∑ w ∈ s, (if w ∈ t then c v else 0) • w) =
          ∑ w ∈ t, (if w ∈ t then c v else 0) • w := by
        symm
        apply Finset.sum_subset hts
        intro w _ hw
        simp only [if_neg hw, zero_smul]
      _ = ∑ w ∈ t, c v • w := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [if_pos hw]
      _ = c v • ∑ w ∈ t, w := Finset.smul_sum.symm
  have hfull : (∑ w ∈ s, d w • w) = x - c v • ∑ w ∈ t, w := by
    simp only [d, sub_smul, Finset.sum_sub_distrib, hcond, hsum]
  have herase : (∑ w ∈ s.erase v, d w • w) = x - c v • ∑ w ∈ t, w := by
    rw [← Finset.sum_erase_add s (fun w => d w • w) hvs, hdv, zero_smul,
      add_zero] at hfull
    exact hfull
  refine ⟨v, hv, ?_⟩
  have hfirst : c v • (∑ w ∈ t, w) ∈ finiteRayCone (starRaySet s t v) :=
    PointedCone.smul_mem _ (hc v hvs)
      (finiteRayCone_generator _ (Finset.mem_insert_self _ _))
  have hsecond : (∑ w ∈ s.erase v, d w • w) ∈
      finiteRayCone (starRaySet s t v) := by
    apply Submodule.sum_mem
    intro w hw
    exact PointedCone.smul_mem _ (hd w (Finset.mem_of_mem_erase hw))
      (finiteRayCone_generator _ (Finset.mem_insert_of_mem hw))
  have hnew := (finiteRayCone (starRaySet s t v)).add_mem hfirst hsecond
  rw [herase] at hnew
  have hcancel : c v • (∑ w ∈ t, w) +
      (x - c v • (∑ w ∈ t, w)) = x := by abel
  rw [hcancel] at hnew
  exact hnew

/-- Equality of the old cone with the finite union of the new actual cones. -/
theorem finiteRayCone_eq_union_star {s t : Finset E} (hts : t ⊆ s)
    (ht : t.Nonempty) :
    (finiteRayCone s : Set E) =
      {x | ∃ v ∈ t, x ∈ finiteRayCone (starRaySet s t v)} := by
  ext x
  constructor
  · exact finiteRayCone_star_cover hts ht
  · rintro ⟨v, hv, hx⟩
    exact finiteRayCone_starRaySet_le hts v hx

end PaperVerification.ToricGeometry
