import bier.complex
import bier.cone_neighborhood
import bier.realization_image

/-! The coordinate cone is precisely the standard realization of the abstract cone. -/

noncomputable section

namespace Bier

open Set Geometry
open DifferentialGeometry.Topology.Engulfing
open DifferentialGeometry.Topology.PiecewiseLinear

namespace Complex

variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem eraseNone_insert_none (s : Finset (Option V)) :
    (insert none s).eraseNone = s.eraseNone := by
  ext v
  simp

def cone (K : Complex V) : Complex (Option V) where
  face s := K.face s.eraseNone
  empty := by simpa using K.empty
  downward hst ht := K.downward (Finset.eraseNone.monotone hst) ht

@[simp] theorem cone_face (K : Complex V) (s : Finset (Option V)) :
    K.cone.face s ↔ K.face s.eraseNone := Iff.rfl

theorem bier_cone_coordinates (K : Complex V) (hK : K.Proper)
    (w : Option (V ⊕ V) → ℝ) :
    w ∈ (standardRealization (K.bier hK).cone.toAbstract).space ↔
      ConeCoordinates K.face w := by
  classical
  rw [mem_standardRealization_iff]
  have hleft : (positiveSupport w).eraseNone.toLeft =
      Finset.univ.filter (fun v => 0 < w (some (.inl v))) := by
    ext v
    simp [positiveSupport]
  have hright : (positiveSupport w).eraseNone.toRight =
      Finset.univ.filter (fun v => 0 < w (some (.inr v))) := by
    ext v
    simp [positiveSupport]
  constructor
  · rintro ⟨hnonneg, htotal, hne, hface⟩
    obtain ⟨hpos, hneg, hdis⟩ := hface
    rw [hleft] at hpos
    have hcomp : (positiveSupport w).eraseNone.toRightᶜ =
        Finset.univ.filter (fun v => w (some (.inr v)) = 0) := by
      rw [hright]
      ext v
      simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
      exact ⟨fun h => le_antisymm h (hnonneg _), fun h => h.le⟩
    rw [hcomp] at hneg
    refine ⟨hnonneg, htotal, hpos, hneg, fun v => ?_⟩
    by_cases hl : w (some (.inl v)) = 0
    · exact Or.inl hl
    · refine Or.inr (le_antisymm ?_ (hnonneg _))
      apply not_lt.mp
      intro hr
      apply Finset.disjoint_left.mp hdis
      · simpa [positiveSupport] using (hnonneg (some (.inl v))).lt_of_ne' hl
      · simpa [positiveSupport] using hr
  · intro hw
    refine ⟨hw.nonneg, hw.total, ?_, ?_⟩
    · by_contra hn
      have hz : ∀ a, w a = 0 := by
        intro a
        apply le_antisymm _ (hw.nonneg a)
        exact not_lt.mp (fun h => hn ⟨a, (mem_positiveSupport w a).mpr h⟩)
      have hh := hw.total
      simp [hz] at hh
    · change K.face _ ∧ ¬ K.face _ ∧ Disjoint _ _
      refine ⟨by rw [hleft]; exact hw.positive, ?_, ?_⟩
      · have hcomp : (positiveSupport w).eraseNone.toRightᶜ =
            Finset.univ.filter (fun v => w (some (.inr v)) = 0) := by
          rw [hright]
          ext v
          simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
          exact ⟨fun h => le_antisymm h (hw.nonneg _), fun h => h.le⟩
        rw [hcomp]
        exact hw.negative
      · apply Finset.disjoint_left.mpr
        intro v hl hr
        have hl' : 0 < w (some (.inl v)) := by simpa [positiveSupport] using hl
        have hr' : 0 < w (some (.inr v)) := by simpa [positiveSupport] using hr
        rcases hw.disjoint v with h | h <;> linarith

theorem cone_apex_face (K : Complex V) :
    {Pi.single (none : Option V) (1 : ℝ)} ∈ (standardRealization K.cone.toAbstract).faces := by
  refine ⟨{none}, ⟨Finset.singleton_nonempty _, ?_⟩, ?_⟩
  · simpa using K.empty
  · simp

theorem cone_link_abstract (K : Complex V) :
    DifferentialGeometry.Topology.SimplicialComplex.link K.cone.toAbstract {none} =
      K.toAbstract.map some := by
  classical
  ext s
  constructor
  · rintro ⟨hsne, hdis, hface⟩
    have hnone : none ∉ s := Finset.disjoint_singleton_left.mp hdis
    have hks : K.face s.eraseNone := by simpa using hface.2
    have heq : s.eraseNone.image some = s := by
      rw [Finset.image_some_eraseNone, Finset.erase_eq_of_notMem hnone]
    refine ⟨s.eraseNone, ⟨?_, hks⟩, heq⟩
    exact Finset.image_nonempty.mp (heq.symm ▸ hsne)
  · rintro ⟨t, ⟨htne, ht⟩, rfl⟩
    refine ⟨htne.image some, ?_, ?_⟩
    · simp
    · refine ⟨Finset.union_nonempty.mpr (Or.inl (Finset.singleton_nonempty _)), ?_⟩
      simpa using ht

end Complex

end Bier
