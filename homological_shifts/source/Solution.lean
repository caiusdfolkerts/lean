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
    {a | Simplicial.literalNonzeroHomology (k := k) (Koszul.koszulFaces (idealGenerators I hI) a) i})

private theorem agrees_with_derivedTor
    (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I) (i : ℕ) :
    homologicalShiftIdeal I hI i = CommAlg.Polymatroid.homologicalShiftIdeal I hI i := by
  unfold homologicalShiftIdeal CommAlg.Polymatroid.homologicalShiftIdeal CommAlg.Koszul.homologicalShift
  apply congrArg (fun S : Set (MvPolynomial V k) => Ideal.span S)
  apply congrArg (fun S : Set (Exponent V) =>
    (fun a : Exponent V => MvPolynomial.monomial a (1 : k)) '' S)
  ext a
  change Simplicial.literalNonzeroHomology (k := k)
      (Koszul.koszulFaces (idealGenerators I hI) a) i ↔
    Koszul.GradedBettiNonzero (k := k) (idealGenerators I hI) a i
  rw [CommAlg.Simplicial.literalNonzeroHomology_iff]
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

namespace PalomarHomological
open CommAlg CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]
/-- Positive-power pieces of the actual homological-shift module; degree zero is zero. -/
def powerPiece (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I)
    (i s : ℕ) : Ideal (MvPolynomial V k) :=
  if s = 0 then ⊥ else homologicalShiftIdeal (I ^ s) (powPolymatroidal hI s) i

private theorem powerPiece_eq_source (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i s : ℕ) :
    powerPiece I hI i s = CommAlg.homologicalPowerPiece I hI i s := by
  simp only [powerPiece, CommAlg.homologicalPowerPiece, agrees_with_derivedTor]

/-- Literal zero closure of the coefficientwise Rees ideal. -/
theorem powerZero {V k : Type u} [Fintype V] [LinearOrder V] [Field k]
    (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I) (i : ℕ) :
    ∀ s, (0 : reesAlgebra I).val.coeff s ∈ powerPiece I hI i s := by
  intro s
  simpa only [Subalgebra.coe_zero, Polynomial.coeff_zero] using (powerPiece I hI i s).zero_mem
/-- Literal addition closure of the coefficientwise Rees ideal. -/
theorem powerAdd {V k : Type u} [Fintype V] [LinearOrder V] [Field k]
    (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I) (i : ℕ)
    {p q : reesAlgebra I}
    (hp : ∀ s, p.val.coeff s ∈ powerPiece I hI i s)
    (hq : ∀ s, q.val.coeff s ∈ powerPiece I hI i s) :
    ∀ s, (p + q).val.coeff s ∈ powerPiece I hI i s := by
  intro s
  simpa only [Subalgebra.coe_add, Polynomial.coeff_add] using
    (powerPiece I hI i s).add_mem (hp s) (hq s)
/-- Literal multiplication closure, proved from the genuine homological-shift action. -/
theorem powerMul {V k : Type u} [Fintype V] [LinearOrder V] [Field k]
    (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I) (i : ℕ)
    (r p : reesAlgebra I) (hp : ∀ s, p.val.coeff s ∈ powerPiece I hI i s) :
    ∀ s, (r * p).val.coeff s ∈ powerPiece I hI i s := by
  intro s
  change (r.val * p.val).coeff s ∈ powerPiece I hI i s
  rw [Polynomial.coeff_mul]
  apply Ideal.sum_mem
  rintro ⟨n, t⟩ hnt
  rw [← Finset.mem_antidiagonal.mp hnt]
  have hpt : p.val.coeff t ∈ CommAlg.homologicalPowerPiece I hI i t := by
    simpa only [powerPiece_eq_source] using hp t
  rw [powerPiece_eq_source]
  exact CommAlg.homologicalPowerPiece_action I hI i n t
    (Ideal.mul_mem_mul (r.property n) hpt)
/-- The ordinary Rees ideal whose coefficients are the actual positive-power homological shifts. -/
def powerIdeal (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I)
    (i : ℕ) : Ideal (reesAlgebra I) where
  carrier := {p | ∀ s, p.val.coeff s ∈ powerPiece I hI i s}
  zero_mem' := powerZero I hI i
  add_mem' := powerAdd I hI i
  smul_mem' := powerMul I hI i
/-- All homogeneous elements in Rees degrees at most i, including polynomial factors. -/
def powerBoxGenerators (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) : Set (reesAlgebra I) :=
  {p | ∃ s r, s ≤ i ∧ r ∈ powerPiece I hI i s ∧ p.val = Polynomial.monomial s r}
/-- The ordinary monic-equation definition of integrality over an ideal. -/
def IntegralOverIdeal {R : Type*} [CommRing R] (I : Ideal R) (x : R) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ c : ℕ → R,
    (∀ i < n, c i ∈ I ^ (n - i)) ∧ x ^ n + ∑ i ∈ Finset.range n, c i * x ^ i = 0
/-- An ideal contains every element integral over it in its actual ambient ring. -/
def IsIntegrallyClosedIdeal {R : Type*} [CommRing R] (I : Ideal R) : Prop :=
  ∀ x : R, IntegralOverIdeal I x → x ∈ I

private theorem powerIdeal_eq_source (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) :
    powerIdeal I hI i = CommAlg.homologicalPowerIdeal I hI i := by
  ext p
  change (∀ s, p.val.coeff s ∈ powerPiece I hI i s) ↔
    ∀ s, p.val.coeff s ∈ CommAlg.homologicalPowerPiece I hI i s
  simp only [powerPiece_eq_source]

/-- Theorem 1.1's actual ordinary Rees-module generation assertion. -/
theorem reesGeneration (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) (hi : 0 < i) :
    powerIdeal I hI i = Ideal.span (powerBoxGenerators I hI i) := by
  simpa only [powerIdeal_eq_source, powerBoxGenerators, powerPiece_eq_source,
    CommAlg.homologicalPowerBoxGenerators] using
      (FourPapers.Homological.theorem_1_1_generation I hI i hi)
/-- Theorem 6.1: integral closure in the actual ordinary Rees algebra. -/
theorem reesIntegralClosure (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) (hi : 0 < i) :
    IsIntegrallyClosedIdeal (powerIdeal I hI i) := by
  rw [powerIdeal_eq_source]
  change CommAlg.IsIntegrallyClosedIdeal (CommAlg.homologicalPowerIdeal I hI i)
  exact FourPapers.Homological.theorem_6_1 I hI i hi
/-- Theorem 5.1's field independence on every genuine nonzero Koszul multidegree. -/
theorem fieldIndependence {l : Type u} [Field l]
    (g : RankFunction V) (a : Exponent V) (i : ℕ) :
    Simplicial.literalNonzeroHomology (k := k) (Koszul.koszulFaces (rankBases g) a) i ↔
      Simplicial.literalNonzeroHomology (k := l) (Koszul.koszulFaces (rankBases g) a) i := by
  simp only [CommAlg.Simplicial.literalNonzeroHomology_iff]
  rw [← CommAlg.Koszul.gradedBettiNonzero_iff_faces (k := k),
    ← CommAlg.Koszul.gradedBettiNonzero_iff_faces (k := l)]
  exact FourPapers.Homological.theorem_5_1_field_independent g a i
end PalomarHomological

namespace PalomarHomological
open CommAlg CommAlg.Polymatroid
universe uSharp
/-- Normalization of the literal uniform rank function. -/
theorem sharpUniform_empty {V : Type uSharp} [DecidableEq V] (d : ℕ) :
    min (∅ : Finset V).card d = 0 := by exact (CommAlg.Polymatroid.uniformRank V d).empty
/-- Monotonicity of the literal truncated cardinality rank. -/
theorem sharpUniform_mono {V : Type uSharp} [DecidableEq V] (d : ℕ) :
    Monotone (fun A : Finset V => min A.card d) := by exact (CommAlg.Polymatroid.uniformRank V d).monotone
/-- Submodularity of the actual uniform rank function. -/
theorem sharpUniform_submodular {V : Type uSharp} [DecidableEq V] (d : ℕ)
    (A B : Finset V) :
    min (A ∪ B).card d + min (A ∩ B).card d ≤ min A.card d + min B.card d := by exact (CommAlg.Polymatroid.uniformRank V d).submodular A B
/-- The exact rank function A ↦ min(card A,d), with its semantic rank axioms. -/
def sharpUniformRank (V : Type uSharp) [DecidableEq V] (d : ℕ) : RankFunction V where
  toFun A := min A.card d
  empty := sharpUniform_empty d
  monotone := sharpUniform_mono d
  submodular := sharpUniform_submodular d
variable {V k : Type uSharp} [Fintype V] [LinearOrder V] [Field k]
/-- The actual squarefree-Veronese ideal, written as its uniform-rank ideal. -/
def sharpIdeal (d : ℕ) : Ideal (MvPolynomial V k) := rankIdeal k (sharpUniformRank V d)
/-- Polymatroidality of the actual sharpness ideal. -/
theorem sharpIdealPolymatroidal (d : ℕ) :
    IsPolymatroidalIdeal (sharpIdeal (V := V) (k := k) d) := by exact rankIdealPolymatroidal _
/-- Proposition4.2: all positive below-threshold shifts vanish, while the threshold
shift is the nonzero principal ideal generated by the displayed coordinate product. -/
theorem universalSharpness (i : ℕ) (hi : 1 ≤ i) (hcard : Fintype.card V = i+1) :
    (∀ s : ℕ, 1 ≤ s → s < i →
      homologicalShiftIdeal ((sharpIdeal (V := V) (k := k) i) ^ s)
        (powPolymatroidal (sharpIdealPolymatroidal i) s) i = ⊥) ∧
    homologicalShiftIdeal ((sharpIdeal (V := V) (k := k) i) ^ i)
      (powPolymatroidal (sharpIdealPolymatroidal i) i) i =
        Ideal.span {(∏ j : V, (MvPolynomial.X j : MvPolynomial V k)) ^ i} ∧
    homologicalShiftIdeal ((sharpIdeal (V := V) (k := k) i) ^ i)
      (powPolymatroidal (sharpIdealPolymatroidal i) i) i ≠ ⊥ := by
  have h := FourPapers.Homological.proposition_4_2 (V := V) (k := k) i hi hcard
  have he : sharpUniformRank V i = CommAlg.Polymatroid.uniformRank V i := by
    apply RankFunction.ext_fun
    intro A
    rfl
  simpa only [agrees_with_derivedTor, sharpIdeal, he,
    CommAlg.Polymatroid.squarefreeVeroneseIdeal] using h
end PalomarHomological
