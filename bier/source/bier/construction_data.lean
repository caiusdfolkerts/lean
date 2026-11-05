import bier.explicit_ordering
import bier.all_signs
import bier.facets
import bier.sphere

/-! # Exact dimensions and actual vertex counts of the explicit constructions -/

noncomputable section

namespace Bier

namespace Complex

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem ghost_maxFaceCard (K : Complex V) : K.ghost.maxFaceCard = K.maxFaceCard := by
  apply Nat.le_antisymm
  · apply K.ghost.maxFaceCard_le
    intro s hs
    have h := K.card_le_maxFaceCard hs.2
    simpa only [Finset.card_eraseNone_of_notMem hs.1] using h
  · apply K.maxFaceCard_le
    intro s hs
    have h := K.ghost.card_le_maxFaceCard ((ghost_map_some K s).mpr hs)
    simpa using h

@[simp] theorem ghost_dimension (K : Complex V) : K.ghost.dimension = K.dimension := by
  simp [dimension, ghost_maxFaceCard]

end Complex

def principalSphere : Complex
    (Option (Fin 20 ⊕ Fin 145162) ⊕ Option (Fin 20 ⊕ Fin 145162)) :=
  principalInput.bier principalCore.ghost_proper

theorem principalInput_dimension : principalInput.dimension = 9 := by
  simpa [principalInput] using principalCore_dimension

theorem principalSphere_vertex_count : principalSphere.vertices.card = 290365 := by
  have hv : ∀ v, principalCore.face {v} := by
    intro v
    rw [← Complex.mem_vertices, principalCore_vertices]
    exact Finset.mem_univ _
  simpa [principalSphere, principalInput, Fintype.card_sum] using
    Complex.ghost_bier_vertex_count principalCore principalCore_proper hv

theorem principalSphere_dimension : principalSphere.dimension = 145181 := by
  simpa [principalSphere, principalInput, Fintype.card_sum] using
    Complex.ghost_bier_dimension principalCore

theorem principalSphere_isSphere : principalSphere.IsSphere 145181 := by
  have h := Complex.bier_isSphere principalInput principalCore.ghost_proper
    (by simp [Fintype.card_option, Fintype.card_sum] :
      2 ≤ Fintype.card (Option (Fin 20 ⊕ Fin 145162)))
  simpa [principalSphere, Fintype.card_option, Fintype.card_sum] using h

def patternRows (m k r : ℕ) (h : r + 1 ≤ m.choose k)
    (i : Option (Fin r)) : Finset (Fin m) :=
  firstSubsets m k (r + 1) h ((finSuccEquiv r).symm i)

theorem patternRows_card (m k r : ℕ) (h : r + 1 ≤ m.choose k) (i : Option (Fin r)) :
    (patternRows m k r h i).card = k := firstSubsets_card _ _ _ _ _

theorem patternRows_injective (m k r : ℕ) (h : r + 1 ≤ m.choose k) :
    Function.Injective (patternRows m k r h) :=
  (firstSubsets_injective _ _ _ _).comp (finSuccEquiv r).symm.injective

def patternCore (m k r : ℕ) (h : r + 1 ≤ m.choose k) :
    Complex (Fin m ⊕ (Fin r → Fin 2)) :=
  signComplex k (patternRows m k r h) (patternRows_card m k r h) (allColumnSigns (Fin r))

theorem patternCore_proper (m k r : ℕ) (h : r + 1 ≤ m.choose k) (hk : k < m) :
    (patternCore m k r h).Proper :=
  signComplex_proper k (by simpa using hk) _ _ _

theorem patternCore_vertices (m k r : ℕ) (h : r + 1 ≤ m.choose k) (hk : 1 ≤ k) :
    (patternCore m k r h).vertices = Finset.univ :=
  signComplex_all_vertices k hk _ _ _

theorem patternCore_dimension (m k r : ℕ) (h : r + 1 ≤ m.choose k) :
    (patternCore m k r h).dimension = k :=
  signComplex_dimension _ _ _ _ (allColumnSigns_positive (Fin r))

def patternInput (m k r : ℕ) (h : r + 1 ≤ m.choose k) := (patternCore m k r h).ghost

def patternSphere (m k r : ℕ) (h : r + 1 ≤ m.choose k) :=
  (patternInput m k r h).bier (patternCore m k r h).ghost_proper

theorem patternInput_dimension (m k r : ℕ) (h : r + 1 ≤ m.choose k) :
    (patternInput m k r h).dimension = k := by
  simpa [patternInput] using patternCore_dimension m k r h

theorem patternSphere_vertex_count (m k r : ℕ) (h : r + 1 ≤ m.choose k)
    (hk : 1 ≤ k) (hkm : k < m) :
    (patternSphere m k r h).vertices.card = 2 * (m + 2 ^ r) + 1 := by
  have hv : ∀ v, (patternCore m k r h).face {v} := by
    intro v
    rw [← Complex.mem_vertices, patternCore_vertices m k r h hk]
    exact Finset.mem_univ _
  simpa [patternSphere, patternInput, Fintype.card_sum] using
    Complex.ghost_bier_vertex_count (patternCore m k r h)
      (patternCore_proper m k r h hkm) hv

theorem patternSphere_dimension (m k r : ℕ) (h : r + 1 ≤ m.choose k) :
    (patternSphere m k r h).dimension = (m : ℤ) + 2 ^ r - 1 := by
  simpa [patternSphere, patternInput, Fintype.card_sum] using
    Complex.ghost_bier_dimension (patternCore m k r h)

theorem patternSphere_isSphere (m k r : ℕ) (h : r + 1 ≤ m.choose k) :
    (patternSphere m k r h).IsSphere (m + 2 ^ r - 1) := by
  have hn : 0 < 2 ^ r := pow_pos (by norm_num) _
  have hc : 2 ≤ Fintype.card (Option (Fin m ⊕ (Fin r → Fin 2))) := by
    simp only [Fintype.card_option, Fintype.card_sum, Fintype.card_fun, Fintype.card_fin]
    omega
  have hb := Complex.bier_isSphere (patternInput m k r h)
    (patternCore m k r h).ghost_proper hc
  convert hb using 1 <;> simp [patternSphere, Fintype.card_option, Fintype.card_sum]

theorem enough_triples : 74 ≤ Nat.choose 9 3 := by decide

def threeDimensionalInput := patternInput 9 3 73 enough_triples
def threeDimensionalSphere := patternSphere 9 3 73 enough_triples

theorem threeDimensionalInput_dimension : threeDimensionalInput.dimension = 3 :=
  patternInput_dimension _ _ _ _

theorem threeDimensionalSphere_vertex_count :
    threeDimensionalSphere.vertices.card = 2 ^ 74 + 19 := by
  simpa [threeDimensionalSphere] using patternSphere_vertex_count 9 3 73 enough_triples
    (by norm_num) (by norm_num)

theorem threeDimensionalSphere_dimension : threeDimensionalSphere.dimension = 2 ^ 73 + 8 := by
  simpa [threeDimensionalSphere] using patternSphere_dimension 9 3 73 enough_triples

theorem threeDimensionalSphere_isSphere : threeDimensionalSphere.IsSphere (2 ^ 73 + 8) := by
  simpa [threeDimensionalSphere] using patternSphere_isSphere 9 3 73 enough_triples

end Bier
