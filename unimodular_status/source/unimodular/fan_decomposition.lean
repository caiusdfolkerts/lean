module

public import Unimodular.FanProducts

@[expose] public section

open scoped BigOperators
open TauCeti.Toric

namespace Unimodular.FanProducts

variable {J : Type*} [Fintype J] [DecidableEq J]
variable {N V : J → Type*} [∀ j, AddCommGroup (N j)]
  [∀ j, AddCommGroup (V j)] [∀ j, Module ℝ (V j)]

/-- The real inclusion of the finite direct sum of lattices. -/
def piEmbedding (i : ∀ j, N j →+ V j) : (∀ j, N j) →+ (∀ j, V j) where
  toFun x j := i j (x j)
  map_zero' := by ext j; exact (i j).map_zero
  map_add' x y := by ext j; exact (i j).map_add _ _

def integralProj (j : J) : (∀ j, N j) →+ N j where
  toFun x := x j
  map_zero' := rfl
  map_add' _ _ := rfl

variable (i : ∀ j, N j →+ V j) (hi : ∀ j, IsIntegralLattice (i j))
variable (Φ : Fan (piEmbedding i))

/-- All rays of the fan lie in the prescribed direct summands. The condition quantifies
over all actual one-dimensional faces of its cones. -/
def HasSummandRays : Prop := ∀ C ∈ Φ.cones, RaysInSummands C

variable {i hi Φ}

theorem cone_splits (h : HasSummandRays i Φ) {C} (hC : C ∈ Φ.cones) : Splits C :=
  splits_of_raysInSummands (Φ.isToricCone hC).fg (Φ.isToricCone hC).salient (h C hC)

theorem section_isToricCone (h : HasSummandRays i Φ) {C} (hC : C ∈ Φ.cones) (j : J) :
    IsToricCone (i j) (sectionCone C j) := by
  refine ⟨?_, sectionCone_salient (Φ.isToricCone hC).salient j⟩
  rw [(cone_splits h hC).section_eq_map j]
  exact (Φ.isToricCone hC).rational.map (f := integralProj j)
    (g := LinearMap.proj j) (fun _ => rfl)

variable (i hi Φ)

/-- The canonical factor fan consists of the coordinate sections of all original cones. -/
def factorFan (h : HasSummandRays i Φ) (j : J) : Fan (i j) where
  lattice := hi j
  cones := (fun C => sectionCone C j) '' Φ.cones
  finite_cones := Φ.finite_cones.image _
  isToricCone := by
    rintro _ ⟨C, hC, rfl⟩
    exact section_isToricCone h hC j
  mem_of_isFaceOf := by
    rintro _ D ⟨C, hC, rfl⟩ hD
    refine ⟨D.map (LinearMap.single ℝ V j), ?_, sectionCone_map_single D⟩
    exact Φ.mem_of_isFaceOf hC ((hD.map _ (single_injective j)).trans
      ((cone_splits h hC).map_section_isFaceOf (Φ.isToricCone hC).salient j))
  inf_isFaceOf_left := by
    rintro _ _ ⟨C, hC, rfl⟩ ⟨D, hD, rfl⟩
    exact (Φ.inf_isFaceOf_left hC hD).comap (LinearMap.single ℝ V j)

@[simp] theorem mem_factorFan_cones (h : HasSummandRays i Φ) (j : J)
    (C : PointedCone ℝ (V j)) :
    C ∈ (factorFan i hi Φ h j).cones ↔ ∃ D ∈ Φ.cones, sectionCone D j = C := Iff.rfl

theorem section_mem_factorFan (h : HasSummandRays i Φ) (j : J) {C}
    (hC : C ∈ Φ.cones) : sectionCone C j ∈ (factorFan i hi Φ h j).cones :=
  ⟨C, hC, rfl⟩

/-- The factors retain precisely the cones of the original fan lying in their summands.
In particular this identifies their ray systems, without discarding either orientation. -/
theorem map_single_mem_iff (h : HasSummandRays i Φ) (j : J)
    (C : PointedCone ℝ (V j)) :
    C.map (LinearMap.single ℝ V j) ∈ Φ.cones ↔ C ∈ (factorFan i hi Φ h j).cones := by
  constructor
  · intro hC
    exact ⟨C.map (LinearMap.single ℝ V j), hC, sectionCone_map_single C⟩
  · rintro ⟨D, hD, rfl⟩
    exact Φ.mem_of_isFaceOf hD
      ((cone_splits h hD).map_section_isFaceOf (Φ.isToricCone hD).salient j)

theorem factorFan_complete (h : HasSummandRays i Φ) (hc : Φ.IsComplete) (j : J) :
    (factorFan i hi Φ h j).IsComplete := by
  apply (Fan.isComplete_iff _).2
  intro x
  obtain ⟨C, hC, hx⟩ := Φ.isComplete_iff.1 hc (Pi.single j x)
  exact ⟨sectionCone C j, section_mem_factorFan i hi Φ h j hC, hx⟩

/-- Any choice of one cone from each canonical factor occurs in the original fan.
The proof works for every finite number of factors, including zero-dimensional factors. -/
theorem conePi_mem (h : HasSummandRays i Φ) (hc : Φ.IsComplete)
    (C : ∀ j, PointedCone ℝ (V j))
    (hC : ∀ j, C j ∈ (factorFan i hi Φ h j).cones) : conePi C ∈ Φ.cones := by
  classical
  choose x hx hdetect using fun j =>
    exists_face_detecting_point (C j) ((factorFan i hi Φ h j).isToricCone (hC j)).fg
  obtain ⟨D, hD, hxD⟩ := Φ.isComplete_iff.1 hc x
  have hs : Splits D := cone_splits h hD
  have hDj : ∀ j, sectionCone D j ∈ (factorFan i hi Φ h j).cones :=
    fun j => section_mem_factorFan i hi Φ h j hD
  have hle : ∀ j, C j ≤ sectionCone D j := by
    intro j
    have hface := (factorFan i hi Φ h j).inf_isFaceOf_left (hC j) (hDj j)
    have hm : x j ∈ C j ⊓ sectionCone D j := ⟨hx j, hs x hxD j⟩
    exact (hdetect j _ hface hm).trans inf_le_right
  have hfaces : ∀ j, (C j).IsFaceOf (sectionCone D j) :=
    fun j => (factorFan i hi Φ h j).isFaceOf_of_le (hDj j) (hC j) (hle j)
  apply Φ.mem_of_isFaceOf hD
  rw [hs.eq_conePi]
  exact conePi_isFaceOf hfaces

/-- Exact product decomposition, for an arbitrary finite direct sum of ambient lattices. -/
theorem proposition_4_1_cones (h : HasSummandRays i Φ) (hc : Φ.IsComplete)
    (C : PointedCone ℝ (∀ j, V j)) :
    C ∈ Φ.cones ↔ ∃ D : ∀ j, PointedCone ℝ (V j),
      (∀ j, D j ∈ (factorFan i hi Φ h j).cones) ∧ C = conePi D := by
  constructor
  · intro hC
    exact ⟨sectionCone C, fun j => section_mem_factorFan i hi Φ h j hC,
      (cone_splits h hC).eq_conePi⟩
  · rintro ⟨D, hD, rfl⟩
    exact conePi_mem i hi Φ h hc D hD

@[simp] theorem sectionCone_conePi (C : ∀ j, PointedCone ℝ (V j)) (j : J) :
    sectionCone (conePi C) j = C j := by
  ext x
  simp only [mem_sectionCone, mem_conePi]
  constructor
  · intro h
    simpa using h j
  · intro hx k
    by_cases hk : k = j
    · subst k
      simpa using hx
    · simp [Pi.single_eq_of_ne hk]

/-- Product factors are unique. This is uniqueness as actual fans in the specified
summands, not only up to a combinatorial isomorphism. -/
theorem factorFan_unique (h : HasSummandRays i Φ)
    (Ψ : ∀ j, Fan (i j)) (hΨc : ∀ j, (Ψ j).IsComplete)
    (hprod : ∀ C : PointedCone ℝ (∀ j, V j),
      C ∈ Φ.cones ↔ ∃ D : ∀ j, PointedCone ℝ (V j),
        (∀ j, D j ∈ (Ψ j).cones) ∧ C = conePi D) :
    ∀ j, factorFan i hi Φ h j = Ψ j := by
  classical
  intro j
  apply Fan.ext
  ext C
  constructor
  · rintro ⟨D, hD, rfl⟩
    obtain ⟨E, hE, rfl⟩ := (hprod D).1 hD
    simpa using hE j
  · intro hC
    have hbot : ∀ k, (⊥ : PointedCone ℝ (V k)) ∈ (Ψ k).cones := by
      intro k
      obtain ⟨D, hD, _⟩ := (Ψ k).isComplete_iff.1 (hΨc k) 0
      exact (Ψ k).bot_mem hD
    let D : ∀ k, PointedCone ℝ (V k) := Function.update (fun k => ⊥) j C
    have hD : ∀ k, D k ∈ (Ψ k).cones := by
      intro k
      by_cases hk : k = j
      · subst k
        simpa [D] using hC
      · simpa [D, Function.update_of_ne hk] using hbot k
    have hmem : conePi D ∈ Φ.cones := (hprod _).2 ⟨D, hD, rfl⟩
    exact ⟨conePi D, hmem, by simp [D]⟩

include hi in
/-- Complete formulation of the geometric product assertion of Proposition 4.1, including
existence, completeness, exact cone and ray retention, and uniqueness of every factor. -/
theorem proposition_4_1 (h : HasSummandRays i Φ) (hc : Φ.IsComplete) :
    ∃ Ψ : ∀ j, Fan (i j),
      (∀ j, (Ψ j).IsComplete) ∧
      (∀ C : PointedCone ℝ (∀ j, V j),
        C ∈ Φ.cones ↔ ∃ D : ∀ j, PointedCone ℝ (V j),
          (∀ j, D j ∈ (Ψ j).cones) ∧ C = conePi D) ∧
      (∀ j (C : PointedCone ℝ (V j)),
        C.map (LinearMap.single ℝ V j) ∈ Φ.cones ↔ C ∈ (Ψ j).cones) ∧
      (∀ Ω : ∀ j, Fan (i j), (∀ j, (Ω j).IsComplete) →
        (∀ C : PointedCone ℝ (∀ j, V j),
          C ∈ Φ.cones ↔ ∃ D : ∀ j, PointedCone ℝ (V j),
            (∀ j, D j ∈ (Ω j).cones) ∧ C = conePi D) → Ψ = Ω) := by
  refine ⟨factorFan i hi Φ h, fun j => factorFan_complete i hi Φ h hc j,
    proposition_4_1_cones i hi Φ h hc, map_single_mem_iff i hi Φ h, ?_⟩
  intro Ω hΩc hΩ
  exact funext (factorFan_unique i hi Φ h Ω hΩc hΩ)

end Unimodular.FanProducts
