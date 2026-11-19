module
public import graph_foundation.part014
public import shared_results.part020_integer_filtered_subalgebra_lifting

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.IntegerFilteredGeneration -/
section

/-! # Generation descends through a locally finite homogeneous filtration

Leading-term correction is performed inside one actual finite-dimensional
homogeneous component. The lower bound is proved from separatedness. This avoids
any unrestricted infinite descent in the integer weight index.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.IntegerFiltered.MultiplicativeFiltration

open Classical DirectSum
open scoped BigOperators

variable {K A Γ : Type*} [Field K] [Ring A] [Algebra K A] [DecidableEq Γ]
  (F : MultiplicativeFiltration K A) (D : ParityDifferential K A)

section ComponentDescent

variable (P : Γ → Submodule K A) [DirectSum.Decomposition P]
  [∀ i, FiniteDimensional K (P i)]

theorem homogeneous_cycle_mem_of_approximation
    (hF : ∀ n, SetLike.IsHomogeneous P (F.level n))
    (hD : ∀ i x, x ∈ P i → D.d x ∈ P i)
    (T : Subalgebra K A) (hT : SetLike.IsHomogeneous P T)
    (happrox : ∀ n x, x ∈ F.level n → D.d x = 0 →
      ∃ z, z ∈ T ∧ z ∈ F.level n ∧ D.d z = 0 ∧ x - z ∈ F.level (n - 1))
    (i : Γ) (x : A) (hxP : x ∈ P i) (hdx : D.d x = 0) : x ∈ T := by
  obtain ⟨l, hl⟩ := F.exists_component_lower_bound (P i)
  have hstep : ∀ (N : ℕ) (a : A), a ∈ P i → a ∈ F.level (l + (N : ℤ)) →
      D.d a = 0 → a ∈ T := by
    intro N
    induction N with
    | zero =>
        intro a haP haF _
        have ha : (⟨a, haP⟩ : P i) ∈ (F.level l).comap (P i).subtype := by
          change a ∈ F.level l
          simpa only [Nat.cast_zero, add_zero] using haF
        rw [hl, Submodule.mem_bot] at ha
        have ha0 : a = 0 := congrArg Subtype.val ha
        rw [ha0]
        exact T.zero_mem
    | succ N ih =>
        intro a haP haF hda
        obtain ⟨z, hzT, _, hdz, haz⟩ := happrox (l + ((N + 1 : ℕ) : ℤ)) a haF hda
        let z' : A := (DirectSum.decompose P z i).val
        have hz'T : z' ∈ T := hT i hzT
        have hz'P : z' ∈ P i := (DirectSum.decompose P z i).property
        have hdz' : D.d z' = 0 := by
          dsimp only [z']
          rw [differential_decompose_commutes D P hD, hdz]
          simp
        have herr : a - z' ∈ F.level (l + (N : ℤ)) := by
          have hh := hF (l + ((N + 1 : ℕ) : ℤ) - 1) i haz
          rw [DirectSum.decompose_sub, DFinsupp.sub_apply, Submodule.coe_sub,
            DirectSum.decompose_of_mem_same P haP] at hh
          have he : l + ((N + 1 : ℕ) : ℤ) - 1 = l + (N : ℤ) := by omega
          simpa only [he] using hh
        have herrorT : a - z' ∈ T := ih (a - z') ((P i).sub_mem haP hz'P) herr
          (by rw [map_sub, hda, hdz', sub_self])
        simpa only [sub_add_cancel] using T.add_mem herrorT hz'T
  obtain ⟨n, hn⟩ := F.exhaustive x
  obtain ⟨N, hN⟩ := exists_nat_ge (n - l)
  exact hstep N x hxP (F.mono (by omega) hn) hdx

theorem cycles_le_of_approximation
    (hF : ∀ n, SetLike.IsHomogeneous P (F.level n))
    (hD : ∀ i x, x ∈ P i → D.d x ∈ P i)
    (T : Subalgebra K A) (hT : SetLike.IsHomogeneous P T)
    (happrox : ∀ n x, x ∈ F.level n → D.d x = 0 →
      ∃ z, z ∈ T ∧ z ∈ F.level n ∧ D.d z = 0 ∧ x - z ∈ F.level (n - 1)) :
    D.cycles ≤ T := by
  intro x hx
  have hmem (i : Γ) : (DirectSum.decompose P x i).val ∈ T :=
    F.homogeneous_cycle_mem_of_approximation D P hF hD T hT happrox i
      (DirectSum.decompose P x i).val (DirectSum.decompose P x i).property (by
        rw [differential_decompose_commutes D P hD, show D.d x = 0 from hx]
        simp)
  have hs := T.sum_mem (t := (DirectSum.decompose P x).support) (fun i _ => hmem i)
  simpa only [DirectSum.sum_support_decompose P x] using hs

end ComponentDescent

variable [AddMonoid Γ] (P : Γ → Submodule K A) [GradedAlgebra P]
  [∀ i, FiniteDimensional K (P i)]
  (hd : ∀ n x, x ∈ F.level n → D.d x ∈ F.level n)
  (hp : ∀ n x, x ∈ F.level n → D.parity x ∈ F.level n)

/-- The full generation assertion of multiplicative degeneration, for an
actual filtered differential algebra with finite homogeneous components. -/
theorem homology_generated_of_relative_generators
    (hF : ∀ n, SetLike.IsHomogeneous P (F.level n))
    (hD : ∀ i x, x ∈ P i → D.d x ∈ P i)
    (W : Submodule K A) (hW : SetLike.IsHomogeneous P W)
    (hlift : F.RelativeLiftsCycles D W)
    (hgen : Algebra.adjoin K (F.specialClasses D hd hp W) = ⊤) :
    Algebra.adjoin K (selectedHomologyClasses D W) = ⊤ := by
  let T := cycleGeneratedAlgebra D W
  have hTc : T ≤ D.cycles := cycleGeneratedAlgebra_le_cycles D W
  have hTh : SetLike.IsHomogeneous P T := cycleGeneratedAlgebra_homogeneous D W P hW hD
  have hsurj := F.goodSpecialMap_surjective_of_generators D hd hp W hlift hgen T hTc
    (fun x hx hdx => selected_cycle_mem_cycleGeneratedAlgebra D W hx hdx)
  have happrox := F.cycle_approximation_in_subalgebra D hd hp T hTc
    (boundary_mem_cycleGeneratedAlgebra D W) hsurj
  apply homology_generated_of_cycles_le_cycleGeneratedAlgebra D W
  exact F.cycles_le_of_approximation D P hF hD T hTh happrox

end FourPapers.IntegerFiltered.MultiplicativeFiltration

end
end
end


end
