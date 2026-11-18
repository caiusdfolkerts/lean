module
public import four_papers.homological.complete

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace PalomarHomological
open CommAlg CommAlg.Polymatroid
/-- The paper's explicit predicted rank value, including its normalized empty case. -/
def rankValue {V : Type*} [Fintype V] [DecidableEq V]
    (g : RankFunction V) (i : ℕ) (A : Finset V) : ℕ :=
  if A = ∅ then 0 else min (g A + i) (A.card + partitionRank g A)
private theorem rankValue_eq_source {V : Type*} [Fintype V] [DecidableEq V]
    (g : RankFunction V) (hg : g.Active) (i : ℕ) :
    rankValue g i = (CommAlg.Polymatroid.homologicalRank g hg i).toFun := by
  funext A
  by_cases hA : A = ∅
  · subst A
    simp [rankValue, CommAlg.Polymatroid.homologicalRank_empty]
  · simpa [rankValue, hA] using
      (CommAlg.Polymatroid.homologicalRank_apply g hg i
        (Finset.nonempty_iff_ne_empty.mpr hA)).symm

/-- Normalization of the explicit numerical rank formula. -/
theorem rankValue_empty {V : Type*} [Fintype V] [DecidableEq V]
    (g : RankFunction V) (i : ℕ) : rankValue g i ∅ = 0 := by simp [rankValue]
/-- Monotonicity of the explicit numerical formula for an active rank. -/
theorem rankValue_mono {V : Type*} [Fintype V] [DecidableEq V]
    (g : RankFunction V) (hg : g.Active) (i : ℕ) : Monotone (rankValue g i) := by
  rw [rankValue_eq_source g hg i]
  exact (CommAlg.Polymatroid.homologicalRank g hg i).monotone
/-- Submodularity of the explicit numerical formula for an active rank. -/
theorem rankValue_submodular {V : Type*} [Fintype V] [DecidableEq V]
    (g : RankFunction V) (hg : g.Active) (i : ℕ) (A B : Finset V) :
    rankValue g i (A ∪ B) + rankValue g i (A ∩ B) ≤
      rankValue g i A + rankValue g i B := by
  simp only [rankValue_eq_source g hg i]
  exact (CommAlg.Polymatroid.homologicalRank g hg i).submodular A B
/-- The same explicit paper rank, with its proved rank-function properties. -/
def rankFunction {V : Type*} [Fintype V] [DecidableEq V]
    (g : RankFunction V) (hg : g.Active) (i : ℕ) : RankFunction V where
  toFun := rankValue g i
  empty := rankValue_empty g i
  monotone := rankValue_mono g hg i
  submodular := rankValue_submodular g hg i

private theorem rank_ext {V : Type*} [DecidableEq V] {a b : RankFunction V}
    (h : a.toFun = b.toFun) : a = b := by
  cases a
  cases b
  dsimp at h
  cases h
  rfl
private theorem rankFunction_eq_source {V : Type*} [Fintype V] [DecidableEq V]
    (g : RankFunction V) (hg : g.Active) (i : ℕ) :
    rankFunction g hg i = CommAlg.Polymatroid.homologicalRank g hg i := by
  exact rank_ext (rankValue_eq_source g hg i)

universe u
/-- The product closure certificate with every original ambient hypothesis explicit. -/
theorem mulPolymatroidal {V k : Type u} [Fintype V] [LinearOrder V]
    [CommRing k] [Nontrivial k] {I J : Ideal (MvPolynomial V k)}
    (hI : IsPolymatroidalIdeal I) (hJ : IsPolymatroidalIdeal J) :
    IsPolymatroidalIdeal (I * J) := hI.mul hJ
/-- The power closure certificate with every original ambient hypothesis explicit. -/
theorem powPolymatroidal {V k : Type u} [Fintype V] [LinearOrder V]
    [CommRing k] [Nontrivial k] {I : Ideal (MvPolynomial V k)}
    (hI : IsPolymatroidalIdeal I) (s : ℕ) : IsPolymatroidalIdeal (I ^ s) := hI.pow s
/-- Every integral rank-base ideal is polymatroidal, with ambient hypotheses explicit. -/
theorem rankIdealPolymatroidal {V k : Type u} [Fintype V] [LinearOrder V]
    [CommRing k] [Nontrivial k] (g : RankFunction V) :
    IsPolymatroidalIdeal (rankIdeal k g) := isPolymatroidalIdeal_rankIdeal g

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
    homologicalShiftIdeal (I ^ (s + 1)) (powPolymatroidal hI (s + 1)) i =
      I * homologicalShiftIdeal (I ^ s) (powPolymatroidal hI s) i := by
  simpa only [agrees_with_derivedTor, rankFunction_eq_source] using
    (FourPapers.Homological.theorem_1_1 I hI i s _hi hs)
/-- The fixed-polymatroidal-twist clause, on the identical uniform range. -/
theorem twistedStabilization (I J : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (hJ : IsPolymatroidalIdeal J)
    (i s : ℕ) (_hi : 0 < i) (hs : i ≤ s) :
    homologicalShiftIdeal (J * I ^ (s + 1)) (mulPolymatroidal hJ (powPolymatroidal hI (s + 1))) i =
      I * homologicalShiftIdeal (J * I ^ s) (mulPolymatroidal hJ (powPolymatroidal hI s)) i := by
  simpa only [agrees_with_derivedTor, rankFunction_eq_source] using
    (FourPapers.Homological.theorem_1_1_twisted I J hI hJ i s _hi hs)
/-- Theorem 1.2's exact rank formula for the actual homological shift. -/
theorem exactRankFormula (g : RankFunction V) (hg : g.Active) (i : ℕ) :
    homologicalShiftIdeal (rankIdeal k g) (rankIdealPolymatroidal g) i =
      if rankFunction g hg i Finset.univ = g Finset.univ + i then
        rankIdeal k (rankFunction g hg i) else ⊥ := by
  simpa only [agrees_with_derivedTor, rankFunction_eq_source] using
    (FourPapers.Homological.theorem_1_2 (k := k) g hg i)
/-- The canonical upper-rank clause in the nonzero case, on the actual
minimal monomial generator family of the homological shift. -/
theorem canonicalRank (g : RankFunction V) (hg : g.Active) (i : ℕ)
    (hne : homologicalShiftIdeal (rankIdeal k g) (rankIdealPolymatroidal g) i ≠ ⊥) :
    ∃ hH : IsPolymatroidalIdeal
        (homologicalShiftIdeal (rankIdeal k g) (rankIdealPolymatroidal g) i),
      ∀ A : Finset V, upperRank (idealGenerators
        (homologicalShiftIdeal (rankIdeal k g) (rankIdealPolymatroidal g) i) hH) A =
        rankFunction g hg i A := by
  rw [agrees_with_derivedTor] at hne ⊢
  refine ⟨CommAlg.Polymatroid.homologicalShiftIdeal_polymatroidal _ _ i, ?_⟩
  intro A
  simpa only [rankFunction_eq_source] using
    (FourPapers.Homological.theorem_1_2_canonical g hg i hne A)
end PalomarHomological
