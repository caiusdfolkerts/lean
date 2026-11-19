module

public import GaleSevenFrame

@[expose] public section

/-!
# The common Gale obstruction for Appendix B.8, types 31 and 32

This theorem is independent of any finite catalogue. It rules out every
real vector configuration satisfying precisely the four independent
four-sets, three independent triples, distinguished four-plane, and seven
hyperplane incidences used in the paper. Its actual-polytope applications
are supplied separately by complementary-rank witnesses.
-/

noncomputable section
namespace Papers.RationalityTen.GaleSevenFrame

open Matrix Set Module
open scoped BigOperators Classical
open GaleSevenCoordinates

theorem first_six_mem_plane (p : Fin 10 → GaleSevenCoordinates.Vector) (h : Conditions p)
    (i : Fin 6) : p (Fin.castLE (by decide) i) ∈ plane p := by
  fin_cases i
  · exact h.A_mem
  · exact Submodule.subset_span ⟨0, rfl⟩
  · exact Submodule.subset_span ⟨1, rfl⟩
  · exact Submodule.subset_span ⟨2, rfl⟩
  · exact Submodule.subset_span ⟨3, rfl⟩
  · exact h.F_mem

theorem four_with_O_independent (p : Fin 10 → GaleSevenCoordinates.Vector) (h : Conditions p)
    (i : Fin 4) : LinearIndependent ℝ (p ∘ Fin.snoc (fourSets i) 6) := by
  have hmem : ∀ v ∈ Set.range (p ∘ fourSets i), v ∈ plane p := by
    rintro v ⟨j, rfl⟩
    have hb : ∀ i : Fin 4, ∀ j : Fin 4, (fourSets i j).val < 6 := by decide
    exact first_six_mem_plane p h ⟨(fourSets i j).val, hb i j⟩
  have hO : p 6 ∉ Submodule.span ℝ (Set.range (p ∘ fourSets i)) :=
    fun hz => h.outside 0 ((Submodule.span_le.mpr hmem) hz)
  have hi := (h.four_independent i).finSnoc hO
  convert hi using 1
  ext j
  fin_cases j <;> rfl

theorem detRows_ne_zero_of_independent (a b c d e : GaleSevenCoordinates.Vector)
    (h : LinearIndependent ℝ ![a, b, c, d, e]) : detRows a b c d e ≠ 0 := by
  change Matrix.det (Matrix.of ![a, b, c, d, e]) ≠ 0
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
    ← Matrix.linearIndependent_row_iff_isUnit]
  exact h

/-- The seven hyperplanes are incompatible with the paper's independent
sets. This is a universal real-vector theorem, with no finite-instance
evaluation or realizability hypothesis hidden in its definitions. -/
theorem seven_hyperplane_obstruction (p : Fin 10 → GaleSevenCoordinates.Vector) (h : Conditions p) : False := by
  let q := normalized p h
  obtain ⟨hB, hD, hR, hS, hO⟩ := normalized_frame p h
  change q 1 = unitPoint 0 at hB
  change q 2 = unitPoint 1 at hD
  change q 3 = unitPoint 2 at hR
  change q 4 = unitPoint 3 at hS
  change q 6 = unitPoint 4 at hO
  let a : Fin 4 → ℝ := fun i => q 0 i.castSucc
  let f : Fin 4 → ℝ := fun i => q 5 i.castSucc
  let x : Fin 4 → ℝ := fun i => q 7 i.castSucc
  let y : Fin 4 → ℝ := fun i => q 8 i.castSucc
  let z : Fin 4 → ℝ := fun i => q 9 i.castSucc
  have hA : q 0 = point a 0 := by
    ext i
    fin_cases i <;> simp [point, a, q, (normalized_internal p h).1]
  have hF : q 5 = point f 0 := by
    ext i
    fin_cases i <;> simp [point, f, q, (normalized_internal p h).2]
  have hX : q 7 = point x 1 := by
    ext i
    fin_cases i <;> simp [point, x, q, normalized_outside p h 7 (by decide)]
  have hY : q 8 = point y 1 := by
    ext i
    fin_cases i <;> simp [point, y, q, normalized_outside p h 8 (by decide)]
  have hZ : q 9 = point z 1 := by
    ext i
    fin_cases i <;> simp [point, z, q, normalized_outside p h 9 (by decide)]
  have hfour (i : Fin 4) : LinearIndependent ℝ
      ![q (fourSets i 0), q (fourSets i 1), q (fourSets i 2), q (fourSets i 3), q 6] := by
    have hi := (normalized_independent_iff p h (Fin.snoc (fourSets i) 6)).mpr
      (four_with_O_independent p h i)
    convert hi using 1
    ext j
    fin_cases j <;> rfl
  have hthree (i : Fin 3) : LinearIndependent ℝ
      ![q (tripleSets i 0), q (tripleSets i 1), q (tripleSets i 2)] := by
    have hi := (normalized_independent_iff p h (tripleSets i)).mpr (h.three_independent i)
    convert hi using 1
    ext j
    fin_cases j <;> rfl
  have hdet (i : Fin 7) : detRows
      (q (hyperplanes i 0)) (q (hyperplanes i 1)) (q (hyperplanes i 2))
        (q (hyperplanes i 3)) (q (hyperplanes i 4)) = 0 := by
    change Matrix.det (Matrix.of ![q (hyperplanes i 0), q (hyperplanes i 1),
      q (hyperplanes i 2), q (hyperplanes i 3), q (hyperplanes i 4)]) = 0
    apply Matrix.det_eq_zero_of_not_linearIndependent_rows
    intro hi
    apply h.hyperplane_dependent i
    apply (normalized_independent_iff p h (hyperplanes i)).mp
    convert hi using 1
    ext j
    fin_cases j <;> rfl
  have ha : a 3 ≠ 0 := by
    have hi := hfour 0
    change LinearIndependent ℝ ![q 0, q 1, q 2, q 3, q 6] at hi
    rw [hA, hB, hD, hR, hO] at hi
    have hd := detRows_ne_zero_of_independent _ _ _ _ _ hi
    rwa [determinant_ABDRO, neg_ne_zero] at hd
  have hδ : a 2 * f 3 - a 3 * f 2 ≠ 0 := by
    have hi := hfour 2
    change LinearIndependent ℝ ![q 0, q 1, q 2, q 5, q 6] at hi
    rw [hA, hB, hD, hF, hO] at hi
    have hd := detRows_ne_zero_of_independent _ _ _ _ _ hi
    rwa [determinant_ABDFO] at hd
  have hε : a 0 * f 1 - a 1 * f 0 ≠ 0 := by
    have hi := hfour 3
    change LinearIndependent ℝ ![q 0, q 3, q 4, q 5, q 6] at hi
    rw [hA, hR, hS, hF, hO] at hi
    have hd := detRows_ne_zero_of_independent _ _ _ _ _ hi
    rwa [determinant_ARSFO] at hd
  apply normalized_obstruction a f x y z ha hδ hε
  · simpa [tripleSets, hO, hX, hB] using hthree 0
  · simpa [tripleSets, hY, hZ, hD] using hthree 1
  · simpa [tripleSets, hX, hZ, hS] using hthree 2
  · simpa [hyperplanes, hB, hD, hR, hO, hX] using hdet 0
  · simpa [hyperplanes, hA, hB, hF, hO, hX] using hdet 1
  · simpa [hyperplanes, hB, hD, hR, hY, hZ] using hdet 2
  · simpa [hyperplanes, hA, hD, hF, hY, hZ] using hdet 3
  · simpa [hyperplanes, hB, hS, hO, hX, hZ] using hdet 4
  · simpa [hyperplanes, hD, hS, hX, hY, hZ] using hdet 5
  · simpa [hyperplanes, hA, hR, hS, hX, hZ] using hdet 6

end Papers.RationalityTen.GaleSevenFrame
