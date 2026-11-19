module
public import graph_foundation.part014
public import shared_results.part020_integer_filtered_dimension

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.IntegerFilteredBounds -/
section

/-! # Finite-dimensional filtration bounds

Exhaustiveness and separatedness imply that the induced integer filtration on
every finite-dimensional subspace has both a zero step and a full step. These
bounds are proved, rather than supplied as extra hypotheses on the algebra.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section

namespace FourPapers.IntegerFiltered.MultiplicativeFiltration

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]
  (F : MultiplicativeFiltration K A) (W : Submodule K A) [FiniteDimensional K W]

theorem exists_component_lower_bound :
    ∃ n : ℤ, (F.level n).comap W.subtype = ⊥ := by
  classical
  let P : ℕ → Prop := fun r => ∃ n : ℤ,
    Module.finrank K ((F.level n).comap W.subtype) = r
  have hex : ∃ r, P r := ⟨_, 0, rfl⟩
  obtain ⟨n, hn⟩ := Nat.find_spec hex
  have hmin (m : ℤ) : Module.finrank K ((F.level n).comap W.subtype) ≤
      Module.finrank K ((F.level m).comap W.subtype) := by
    rw [hn]
    exact Nat.find_min' hex ⟨m, rfl⟩
  refine ⟨n, bot_unique ?_⟩
  intro x hx
  apply (Submodule.mem_bot K).mpr
  apply Subtype.ext
  apply F.separated x.val
  intro m
  by_cases hm : m ≤ n
  · have he : (F.level m).comap W.subtype = (F.level n).comap W.subtype :=
      Submodule.eq_of_le_of_finrank_le (Submodule.comap_mono (F.mono hm)) (hmin m)
    rw [← he] at hx
    exact hx
  · exact F.mono (by omega) hx

theorem exists_component_upper_bound :
    ∃ n : ℤ, (F.level n).comap W.subtype = ⊤ := by
  classical
  let P : ℕ → Prop := fun r => ∃ n : ℤ,
    Module.finrank K W - Module.finrank K ((F.level n).comap W.subtype) = r
  have hex : ∃ r, P r := ⟨_, 0, rfl⟩
  obtain ⟨n, hn⟩ := Nat.find_spec hex
  have hmax (m : ℤ) : Module.finrank K ((F.level m).comap W.subtype) ≤
      Module.finrank K ((F.level n).comap W.subtype) := by
    have hmin := Nat.find_min' hex (show P
      (Module.finrank K W - Module.finrank K ((F.level m).comap W.subtype)) from ⟨m, rfl⟩)
    have hnle := ((F.level n).comap W.subtype).finrank_le
    have hmle := ((F.level m).comap W.subtype).finrank_le
    omega
  refine ⟨n, top_unique ?_⟩
  intro x _
  obtain ⟨m, hm⟩ := F.exhaustive x.val
  have he : (F.level n).comap W.subtype = (F.level (max n m)).comap W.subtype :=
    Submodule.eq_of_le_of_finrank_le
      (Submodule.comap_mono (F.mono (le_max_left n m))) (hmax (max n m))
  rw [he]
  exact F.mono (le_max_right n m) hm

theorem exists_component_bounds :
    ∃ (L : ℤ) (hL : (F.level (L - 1)).comap W.subtype = ⊥) (N : ℕ),
      (F.componentFiltration W L hL).level N = ⊤ := by
  obtain ⟨l, hl⟩ := F.exists_component_lower_bound W
  obtain ⟨u, hu⟩ := F.exists_component_upper_bound W
  let L : ℤ := l + 1
  have hL : (F.level (L - 1)).comap W.subtype = ⊥ := by
    simpa only [L, add_sub_cancel_right] using hl
  obtain ⟨N, hN⟩ := exists_nat_ge (u - L + 1)
  refine ⟨L, hL, N, top_unique ?_⟩
  intro x _
  have hx : x ∈ (F.level u).comap W.subtype := by rw [hu]; trivial
  exact F.mono (by omega) hx

end FourPapers.IntegerFiltered.MultiplicativeFiltration

end
end
end


end
