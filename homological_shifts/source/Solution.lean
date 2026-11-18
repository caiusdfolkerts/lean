module
public import four_papers.homological.complete

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace PalomarHomological
open CommAlg CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]
/-- Homological shift via actual Koszul homology. The Solution identifies this
with the genuine derived-Tor definition; no rank formula defines the support. -/
def homologicalShiftIdeal (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I)
    (i : ℕ) : Ideal (MvPolynomial V k) :=
  Ideal.span ((fun a : Exponent V => MvPolynomial.monomial a (1 : k)) ''
    {a | Simplicial.NonzeroHomology (k := k) (Koszul.koszulFaces (idealGenerators I hI) a) i})

private theorem agrees_with_derivedTor
    (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I) (i : ℕ) :
    homologicalShiftIdeal I hI i = CommAlg.Polymatroid.homologicalShiftIdeal I hI i := by
  unfold homologicalShiftIdeal CommAlg.Polymatroid.homologicalShiftIdeal CommAlg.Koszul.homologicalShift
  apply congrArg (fun S : Set (MvPolynomial V k) => Ideal.span S)
  apply congrArg (fun S : Set (Exponent V) =>
    (fun a : Exponent V => MvPolynomial.monomial a (1 : k)) '' S)
  ext a
  exact (CommAlg.Koszul.gradedBettiNonzero_iff_faces (k := k) (idealGenerators I hI) a i).symm

/-- Theorem 1.1's uniform stabilization equality for every i>0 and s>=i. -/
theorem stabilization (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I)
    (i s : ℕ) (_hi : 0 < i) (hs : i ≤ s) :
    homologicalShiftIdeal (I ^ (s + 1)) (hI.pow (s + 1)) i =
      I * homologicalShiftIdeal (I ^ s) (hI.pow s) i := by
  simpa only [agrees_with_derivedTor] using
    (FourPapers.Homological.theorem_1_1 I hI i s _hi hs)
/-- The fixed-polymatroidal-twist clause, on the identical uniform range. -/
theorem twistedStabilization (I J : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (hJ : IsPolymatroidalIdeal J)
    (i s : ℕ) (_hi : 0 < i) (hs : i ≤ s) :
    homologicalShiftIdeal (J * I ^ (s + 1)) (hJ.mul (hI.pow (s + 1))) i =
      I * homologicalShiftIdeal (J * I ^ s) (hJ.mul (hI.pow s)) i := by
  simpa only [agrees_with_derivedTor] using
    (FourPapers.Homological.theorem_1_1_twisted I J hI hJ i s _hi hs)
/-- Theorem 1.2's exact rank formula for the actual homological shift. -/
theorem exactRankFormula (g : RankFunction V) (hg : g.Active) (i : ℕ) :
    homologicalShiftIdeal (rankIdeal k g) (isPolymatroidalIdeal_rankIdeal g) i =
      if homologicalRank g hg i Finset.univ = g Finset.univ + i then
        rankIdeal k (homologicalRank g hg i) else ⊥ := by
  simpa only [agrees_with_derivedTor] using
    (FourPapers.Homological.theorem_1_2 (k := k) g hg i)
/-- The canonical upper-rank clause in the nonzero case, on the actual
minimal monomial generator family of the homological shift. -/
theorem canonicalRank (g : RankFunction V) (hg : g.Active) (i : ℕ)
    (hne : homologicalShiftIdeal (rankIdeal k g) (isPolymatroidalIdeal_rankIdeal g) i ≠ ⊥) :
    ∃ hH : IsPolymatroidalIdeal
        (homologicalShiftIdeal (rankIdeal k g) (isPolymatroidalIdeal_rankIdeal g) i),
      ∀ A : Finset V, upperRank (idealGenerators
        (homologicalShiftIdeal (rankIdeal k g) (isPolymatroidalIdeal_rankIdeal g) i) hH) A =
        homologicalRank g hg i A := by
  rw [agrees_with_derivedTor] at hne ⊢
  refine ⟨CommAlg.Polymatroid.homologicalShiftIdeal_polymatroidal _ _ i, ?_⟩
  intro A
  exact FourPapers.Homological.theorem_1_2_canonical g hg i hne A
end PalomarHomological
