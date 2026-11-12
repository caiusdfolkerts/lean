module

public import ToricPower.CechSingular.NerveCongruence
public import ToricPower.CechSingular.StarConvexNerve
public import ToricPower.CechSingular.ReducedCochainAcyclicity

/-! # Contractibility of the actual face-intersection incidence nerve -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set
open ToricPower.NegativeSupportCech
open BondalThomsen.ConvexNerveReducedCochainAcyclicity
open BondalThomsen.ConvexNerveRealizationEquivalence
open BondalThomsen.ClosedConvexNerveComparison

attribute [local instance] Classical.decEq

namespace ToricPower.FaceNerve

variable {B : Type} [SemilatticeInf B] {E : Type*}
  (cells : InfHom B (Set E)) (cut : Set E)

def retained (b : B) : Prop := (cells b ∩ cut).Nonempty

theorem retained_upward : Monotone (retained cells cut) := by
  intro b c below
  rintro ⟨x,inside,selected⟩
  exact ⟨x,OrderHomClass.mono cells below inside,selected⟩

theorem coverNerve_eq_incidence :
    coverNerve (fun b => cells b ∩ cut) =
      coverNerve (incidencePatches (fun b c : B => b ≤ c) (retained cells cut)) := by
  apply SetLike.ext
  intro face
  rw [incidencePatches_coverNerve,mem_coverNerve_iff]
  change (face.Nonempty ∧ ∃ x, ∀ b ∈ face, x ∈ cells b ∩ cut) ↔
    face.Nonempty ∧ ∃ b, retained cells cut b ∧ ∀ c ∈ face, b ≤ c
  constructor
  · rintro ⟨nonempty,x,contains⟩
    refine ⟨nonempty,face.inf' nonempty id,?_,?_⟩
    · refine ⟨x,?_,(contains nonempty.choose nonempty.choose_spec).2⟩
      rw [map_finset_inf']
      change x ∈ face.inf' nonempty (fun c => cells c)
      have singleton : ({x} : Set E) ≤ face.inf' nonempty (fun c => cells c) :=
        (Finset.le_inf'_iff nonempty (fun c => cells c)).mpr
          (fun c hc => Set.singleton_subset_iff.mpr (contains c hc).1)
      exact singleton (Set.mem_singleton x)
    · exact fun b hb => Finset.inf'_le _ hb
  · rintro ⟨nonempty,b,⟨x,hx,selected⟩,below⟩
    exact ⟨nonempty,x,fun c hc => ⟨OrderHomClass.mono cells (below c hc) hx,selected⟩⟩

variable [Finite B] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- This concerns the literal incidence realization, including the
closed-complement case whose union is star-convex rather than convex. -/
theorem incidence_contractible_of_starConvex (region : Set E) (center : E)
    (star : StarConvex ℝ center region) (nonempty : region.Nonempty)
    (convex : ∀ b, Convex ℝ (cells b ∩ cut))
    (closed : ∀ b, IsClosed {x : region | x.val ∈ cells b ∩ cut})
    (cover : (⋃ b, cells b ∩ cut) = region) :
    ContractibleSpace (incidenceRealization (fun b c : B => b ≤ c) (retained cells cut)) := by
  letI := CompactCarrierNerve.entireNerve_contractible_of_starConvex
    (fun b => cells b ∩ cut) region center star nonempty convex closed cover
  exact (NerveCongruence.activeNerve_contractible_congr _ _
    (coverNerve_eq_incidence cells cut)).mp inferInstance

end ToricPower.FaceNerve

end
