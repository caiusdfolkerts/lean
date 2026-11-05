import cubical.pl_abstract
import Mathlib.Data.Finset.Sum

/-!
# Finite simplicial complexes, Alexander duality, and the Bier construction

The empty face is included.  A ground-set label need not be a vertex: this is
essential for the ghost label in the explicit constructions.
-/

noncomputable section

namespace Bier

structure Complex (V : Type*) where
  face : Finset V → Prop
  empty : face ∅
  downward : ∀ {s t}, s ⊆ t → face t → face s

namespace Complex

variable {V : Type*} [Fintype V] [DecidableEq V]

def Proper (K : Complex V) : Prop := ¬ K.face Finset.univ

def vertices (K : Complex V) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => K.face {v})

@[simp] theorem mem_vertices (K : Complex V) (v : V) :
    v ∈ K.vertices ↔ K.face {v} := by
  classical
  simp [vertices]

def maxFaceCard (K : Complex V) : ℕ := by
  classical
  exact (Finset.univ.filter K.face).sup Finset.card

def dimension (K : Complex V) : ℤ := (K.maxFaceCard : ℤ) - 1

theorem card_le_maxFaceCard (K : Complex V) {s : Finset V} (hs : K.face s) :
    s.card ≤ K.maxFaceCard := by
  classical
  exact Finset.le_sup (f := Finset.card) (by simp [hs])

theorem maxFaceCard_le (K : Complex V) {n : ℕ}
    (h : ∀ s, K.face s → s.card ≤ n) : K.maxFaceCard ≤ n := by
  classical
  exact Finset.sup_le fun s hs => h s (Finset.mem_filter.mp hs).2

open DifferentialGeometry.Topology.Engulfing in
def toAbstract (K : Complex V) : PreAbstractSimplicialComplex V where
  faces := {s | s.Nonempty ∧ K.face s}
  isRelLowerSet_faces := by
    rintro s ⟨hs, hK⟩
    exact ⟨hs, fun t hts ht => ⟨ht, K.downward hts hK⟩⟩

@[simp] theorem mem_toAbstract (K : Complex V) (s : Finset V) :
    s ∈ K.toAbstract.faces ↔ s.Nonempty ∧ K.face s := Iff.rfl

def dual (K : Complex V) (hK : K.Proper) : Complex V where
  face s := ¬ K.face sᶜ
  empty := by simpa [Proper] using hK
  downward := by
    intro s t hst ht hs
    exact ht (K.downward (Finset.compl_subset_compl.mpr hst) hs)

@[simp] theorem dual_face_iff (K : Complex V) (hK : K.Proper) (s : Finset V) :
    (K.dual hK).face s ↔ ¬ K.face sᶜ := Iff.rfl

theorem dual_proper (K : Complex V) (hK : K.Proper) : (K.dual hK).Proper := by
  simpa [Proper, dual] using K.empty

@[simp] theorem dual_dual_face (K : Complex V) (hK : K.Proper) (s : Finset V) :
    ((K.dual hK).dual (K.dual_proper hK)).face s ↔ K.face s := by
  classical
  simp [dual]

def bier (K : Complex V) (hK : K.Proper) : Complex (V ⊕ V) where
  face s := K.face s.toLeft ∧ ¬ K.face s.toRightᶜ ∧ Disjoint s.toLeft s.toRight
  empty := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [Finset.toLeft] using K.empty
    · simpa [Proper, Finset.toRight] using hK
    · simp [Finset.toLeft, Finset.toRight]
  downward := by
    intro s t hst ht
    refine ⟨K.downward (Finset.toLeft_subset_toLeft hst) ht.1, ?_, ?_⟩
    · intro hs
      exact ht.2.1 (K.downward
        (Finset.compl_subset_compl.mpr (Finset.toRight_subset_toRight hst)) hs)
    · exact ht.2.2.mono (Finset.toLeft_subset_toLeft hst)
        (Finset.toRight_subset_toRight hst)

@[simp] theorem bier_face_iff (K : Complex V) (hK : K.Proper)
    (s : Finset (V ⊕ V)) :
    (K.bier hK).face s ↔
      K.face s.toLeft ∧ ¬ K.face s.toRightᶜ ∧ Disjoint s.toLeft s.toRight := Iff.rfl

end Complex
end Bier
