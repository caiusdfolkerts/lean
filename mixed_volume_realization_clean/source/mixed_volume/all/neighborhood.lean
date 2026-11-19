module

public import mixed_volume.all
public meta import Lean.Util.CollectAxioms

/-! Topological correspondence for the numbered statement of Theorem 6.1.
The original main proof remains frozen. The topology here is the standard
product topology on three real coordinates; no choice of norm occurs in the
conclusions below. -/

@[expose] public section

open Set Filter
open scoped Topology

namespace MixedVolume.ScalarSection

/-- Every neighbourhood of zero contains a nonempty relatively open piece of
each specified supporting plane lying in the actual frontier of the cone. -/
theorem boundary_plane_patch_in_neighborhood (k : ℕ)
    (U : Set (Fin 3 → ℝ)) (hU : U ∈ 𝓝 (0 : Fin 3 → ℝ)) :
    ∃ a : Fin 3 → ℝ, ∃ W : Set (Fin 3 → ℝ),
      IsOpen W ∧ a ∈ W ∩ DyadicCone.plane k ∧
      W ∩ DyadicCone.plane k ⊆ frontier DyadicCone.cone ∩ U := by
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨a, δ, hδ, ha, hpatch⟩ := DyadicCone.boundary_plane_patch_local k R hR
  refine ⟨a, Metric.ball a δ, Metric.isOpen_ball,
    ⟨Metric.mem_ball_self hδ, ha.1⟩, ?_⟩
  rintro b ⟨hb, hplane⟩
  have h := hpatch b hb hplane
  exact ⟨h.1, hRU h.2⟩

/-- The global section theorem restricts to every neighbourhood of the interior
parameter point zero, and each plane contributes a relatively open boundary
piece there. This is the norm-free form of the paper's local assertion. -/
theorem theorem_6_1_neighborhoods :
    (0 : Fin 3 → ℝ) ∈ interior (Set.univ : Set (Fin 3 → ℝ)) ∧
      ∀ U : Set (Fin 3 → ℝ), U ∈ 𝓝 (0 : Fin 3 → ℝ) →
        (coefficientMap ⁻¹' VolumePolynomials.VolumeLocus 12 3) ∩ U =
          DyadicCone.cone ∩ U ∧
        ∀ k : ℕ, ∃ a : Fin 3 → ℝ, ∃ W : Set (Fin 3 → ℝ),
          IsOpen W ∧ a ∈ W ∩ DyadicCone.plane k ∧
          W ∩ DyadicCone.plane k ⊆ frontier DyadicCone.cone ∩ U := by
  refine ⟨by simp, ?_⟩
  intro U hU
  refine ⟨congrArg (fun S => S ∩ U) rational_quadratic_section.2, ?_⟩
  intro k
  exact boundary_plane_patch_in_neighborhood k U hU

end MixedVolume.ScalarSection

open Lean Elab Command in
run_cmd do
  for name in #[``MixedVolume.ScalarSection.boundary_plane_patch_in_neighborhood,
      ``MixedVolume.ScalarSection.theorem_6_1_neighborhoods] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unapproved axiom {ax} in {name}"
    logInfo m!"{name}: {axioms}"
