module

public import Unimodular.CycleTopology

@[expose] public section

open scoped Pointwise Topology BigOperators
open Set

namespace Unimodular.FanMaximalCones

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {i : N →+ V} (Φ : TauCeti.Toric.Fan i)

/-- In a finite complete fan, its full-dimensional cones already cover every point. -/
theorem full_cones_cover (hΦ : Φ.IsComplete) (x : V) :
    ∃ C ∈ Φ.cones, Submodule.span ℝ (C : Set V) = ⊤ ∧ x ∈ C := by
  classical
  let P := {C : Φ.cones // Submodule.span ℝ (C.1 : Set V) ≠ ⊤}
  letI : Fintype P := Fintype.ofFinite P
  let Q := {C : Φ.cones // Submodule.span ℝ (C.1 : Set V) = ⊤}
  let T : Set V := ⋃ C : Q, (C.1.1 : Set V)
  have hTc : IsClosed T := isClosed_iUnion_of_finite
    (fun C : Q => ConeInterior.isClosed_of_fg (Φ.isToricCone C.1.2).fg)
  have hdense := FiniteSubspacePaths.dense_complement
    (fun C : P => Submodule.span ℝ (C.1.1 : Set V)) (fun C => C.2)
  have hsubset : {z | ∀ C : P, z ∉ Submodule.span ℝ (C.1.1 : Set V)} ⊆ T := by
    intro z hz
    obtain ⟨C, hC, hzC⟩ := Φ.isComplete_iff.1 hΦ z
    have hfull : Submodule.span ℝ (C : Set V) = ⊤ := by
      by_contra hn
      exact hz ⟨⟨C, hC⟩, hn⟩ (Submodule.subset_span hzC)
    exact Set.mem_iUnion.2 ⟨⟨⟨C, hC⟩, hfull⟩, hzC⟩
  have hTu : T = Set.univ := hTc.closure_eq.symm.trans (hdense.mono hsubset).closure_eq
  have hx : x ∈ T := by rw [hTu]; trivial
  obtain ⟨C, hxC⟩ := Set.mem_iUnion.1 hx
  exact ⟨C.1.1, C.1.2, C.2, hxC⟩

/-- Every cone of a complete fan is a face of one of its full-dimensional cones. -/
theorem exists_full_supercone (hΦ : Φ.IsComplete) {C : PointedCone ℝ V} (hC : C ∈ Φ.cones) :
    ∃ D ∈ Φ.cones, Submodule.span ℝ (D : Set V) = ⊤ ∧ C.IsFaceOf D := by
  obtain ⟨x, hxC, hdetect⟩ := FanProducts.exists_face_detecting_point C (Φ.isToricCone hC).fg
  obtain ⟨D, hD, hfull, hxD⟩ := full_cones_cover Φ hΦ x
  have hCD : C ≤ D :=
    (hdetect _ (Φ.inf_isFaceOf_left hC hD) ⟨hxC, hxD⟩).trans inf_le_right
  exact ⟨D, hD, hfull, Φ.isFaceOf_of_le hD hC hCD⟩

theorem mem_iff_face_of_full (hΦ : Φ.IsComplete) (C : PointedCone ℝ V) :
    C ∈ Φ.cones ↔ ∃ D ∈ Φ.cones,
      Submodule.span ℝ (D : Set V) = ⊤ ∧ C.IsFaceOf D := by
  exact ⟨exists_full_supercone Φ hΦ, fun ⟨D, hD, _, hCD⟩ => Φ.mem_of_isFaceOf hD hCD⟩

/-- Full-dimensional cones are exactly the maximal cones of a finite complete fan. -/
theorem full_iff_maximal (hΦ : Φ.IsComplete) {C : PointedCone ℝ V} (hC : C ∈ Φ.cones) :
    Submodule.span ℝ (C : Set V) = ⊤ ↔
      ∀ D ∈ Φ.cones, C ≤ D → C = D := by
  constructor
  · intro hfull D hD hCD
    by_contra hn
    exact ConeInterior.span_ne_top_of_proper_face (Φ.isFaceOf_of_le hD hC hCD) hn hfull
  · intro hmax
    obtain ⟨D, hD, hfull, hCD⟩ := exists_full_supercone Φ hΦ hC
    rw [hmax D hD hCD.le]
    exact hfull

end Unimodular.FanMaximalCones
