import CommAlg.Polymatroid.Exponents
import CommAlg.Simplicial.Chains
/-! # Upper Koszul faces as actual divisibility conditions -/

noncomputable section
namespace CommAlg.Koszul
open Classical CommAlg.Polymatroid
universe u
variable {V : Type u} [Fintype V] [LinearOrder V]

/-- The squarefree exponent vector associated with an exterior basis wedge. -/
def faceExponent (s : Finset V) : Exponent V := ∑ j ∈ s, Finsupp.single j 1

@[simp] lemma faceExponent_apply (s : Finset V) (j : V) :
    faceExponent s j = if j ∈ s then 1 else 0 := by
  classical
  simp [faceExponent, Finsupp.single_apply]

@[simp] lemma faceExponent_empty : faceExponent (∅ : Finset V) = 0 := by
  simp [faceExponent]

lemma faceExponent_mono {s t : Finset V} (h : s ⊆ t) : faceExponent s ≤ faceExponent t := by
  intro j
  by_cases hs : j ∈ s
  · simp [faceExponent_apply, hs, h hs]
  · simp [faceExponent_apply, hs]

lemma faceExponent_erase_add {s : Finset V} {j : V} (hj : j ∈ s) :
    faceExponent (s.erase j) + Finsupp.single j 1 = faceExponent s := by
  ext a
  by_cases h : a = j
  · subst a; simp [hj]
  · simp [faceExponent_apply, Finsupp.single_apply, h, Ne.symm h]

/-- A face exactly when its exterior monomial divides `a` and the residual monomial lies in the ideal. -/
def koszulFaces (B : Family V) (a : Exponent V) (s : Finset V) : Prop :=
  faceExponent s ≤ a ∧ Contains B (a - faceExponent s)

lemma koszulFaces_downward (B : Family V) (a : Exponent V) :
    Simplicial.Downward (koszulFaces B a) := by
  intro s t hts hs
  refine ⟨(faceExponent_mono hts).trans hs.1, ?_⟩
  obtain ⟨b, hb, hba⟩ := hs.2
  exact ⟨b, hb, hba.trans (tsub_le_tsub_left (faceExponent_mono hts) a)⟩


end CommAlg.Koszul
end
