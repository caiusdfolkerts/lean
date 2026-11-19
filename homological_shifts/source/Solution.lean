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

namespace PalomarHomological
open CommAlg CommAlg.Polymatroid
open scoped BigOperators
universe uInterval
variable {V k : Type uInterval} [Fintype V] [LinearOrder V] [Field k]
/-- Exact clamped integer ceiling threshold over every partition of A.
Zero-defect partitions contribute zero; the empty set is included. -/
def intervalThreshold (ρ : RankFunction V) (i : ℕ) (A : Finset V) : ℕ :=
  Finset.univ.sup (fun P : Finpartition A =>
    if partitionDefect ρ P = 0 then 0 else
      (min i (eventualOffset ρ A) - partitionSlack P) ⌈/⌉ partitionDefect ρ P)
/-- Maximum of the actual thresholds over every subset, including the empty set. -/
def intervalGlobalThreshold (ρ : RankFunction V) (i : ℕ) : ℕ :=
  Finset.univ.sup (intervalThreshold ρ i)
/-- Actual minimality under Rees monomial divisibility, including degree-zero
polynomial factors; the module pieces use genuine nonzero Koszul homology. -/
def intervalMinimal (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i s : ℕ) (a : Exponent V) : Prop :=
  MvPolynomial.monomial a (1 : k) ∈ powerPiece I hI i s ∧
    ∀ r b, r ≤ s → b ≤ a →
      MvPolynomial.monomial b (1 : k) ∈ powerPiece I hI i r →
      MvPolynomial.monomial (a - b) (1 : k) ∈ I ^ (s - r) →
      r = s ∧ b = a
/-- All actual module monomials through Rees degree q, in the actual ordinary Rees algebra. -/
def intervalBoundedMonomials (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i q : ℕ) : Set (reesAlgebra I) :=
  {p | ∃ s a, MvPolynomial.monomial a (1 : k) ∈ powerPiece I hI i s ∧
    s ≤ q ∧ p.val = Polynomial.monomial s (MvPolynomial.monomial a 1)}

private theorem intervalThreshold_eq_source (ρ : RankFunction V) (i : ℕ) (A : Finset V) :
    intervalThreshold ρ i A = CommAlg.Polymatroid.powerThreshold ρ i A := by rfl
private theorem intervalGlobalThreshold_eq_source (ρ : RankFunction V) (i : ℕ) :
    intervalGlobalThreshold ρ i = CommAlg.Polymatroid.globalPowerThreshold ρ i := by rfl
private theorem intervalMinimal_iff_source (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i s : ℕ) (a : Exponent V) :
    intervalMinimal I hI i s a ↔ CommAlg.IsMinimalHomologicalPowerMonomial I hI i s a := by
  simp only [intervalMinimal, CommAlg.IsMinimalHomologicalPowerMonomial, powerPiece_eq_source]
private theorem intervalBoundedMonomials_eq_source (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i q : ℕ) :
    intervalBoundedMonomials I hI i q = CommAlg.boundedHomologicalPowerMonomials I hI i q := by
  ext a
  simp only [intervalBoundedMonomials, CommAlg.boundedHomologicalPowerMonomials, powerPiece_eq_source]
/-- The complete zero-Rees-module case of Theorem4.4. -/
theorem zeroPowerModule (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi : eventualOffset ρ Finset.univ < i) :
    powerIdeal (rankIdeal k ρ) (rankIdealPolymatroidal ρ) i = ⊥ := by
  simpa only [powerIdeal_eq_source] using
    (FourPapers.Homological.theorem_4_4_zero (k := k) ρ hρ i hi)

/-- Full Theorem4.4: endpoints, first nonzero piece, every actual minimal
monomial Rees-generator degree and the exact least ideal-span generation bound. -/
theorem exactGeneratorInterval (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ Finset.univ) :
    (1 ≤ intervalThreshold ρ i Finset.univ ∧
      intervalThreshold ρ i Finset.univ ≤ intervalGlobalThreshold ρ i ∧
      intervalGlobalThreshold ρ i ≤ i) ∧
    (∀ s : ℕ, 1 ≤ s →
      (homologicalShiftIdeal (rankIdeal k ρ ^ s)
        (powPolymatroidal (rankIdealPolymatroidal ρ) s) i ≠ ⊥ ↔
          intervalThreshold ρ i Finset.univ ≤ s)) ∧
    (∀ s : ℕ,
      (∃ a, intervalMinimal (rankIdeal k ρ)
        (rankIdealPolymatroidal ρ) i s a) ↔
          intervalThreshold ρ i Finset.univ ≤ s ∧ s ≤ intervalGlobalThreshold ρ i) ∧
    (∀ q : ℕ,
      powerIdeal (rankIdeal k ρ) (rankIdealPolymatroidal ρ) i =
        Ideal.span (intervalBoundedMonomials (rankIdeal k ρ)
          (rankIdealPolymatroidal ρ) i q) ↔
            intervalGlobalThreshold ρ i ≤ q) := by
  simpa only [agrees_with_derivedTor, intervalThreshold_eq_source,
    intervalGlobalThreshold_eq_source, intervalMinimal_iff_source,
    powerIdeal_eq_source, intervalBoundedMonomials_eq_source] using
      (FourPapers.Homological.theorem_4_4 (k := k) ρ hρ i hi0 hi)

/-- The signed rational-ceiling formula, with negative numerators and all
empty index collections handled by the literal sup/toNat conventions. -/
theorem thresholdRationalCeiling (ρ : RankFunction V) (i : ℕ) (A : Finset V) :
    intervalThreshold ρ i A = Finset.univ.sup (fun P : Finpartition A =>
      if 0 < partitionDefect ρ P then
        (Int.ceil (((((min i (eventualOffset ρ A)) : ℕ) : ℚ) - partitionSlack P) /
          (partitionDefect ρ P : ℚ))).toNat else 0) := by
  simpa only [intervalThreshold_eq_source, CommAlg.Polymatroid.eventualCorrection] using
    (FourPapers.Homological.theorem_4_4_threshold_formula ρ i A)

end PalomarHomological

namespace PalomarHomological
open CommAlg CommAlg.Polymatroid
open scoped BigOperators
universe uTotal
variable {V k : Type uTotal} [Fintype V] [LinearOrder V] [Field k]
/-- The loop-compatible partition rank of g+cardinality, with all coordinates retained. -/
def totalAugmentedValue (g : RankFunction V) (A : Finset V) : ℕ :=
  partitionRank (fun B => g B + B.card) A
/-- The exact degree excess, later identified with genuine projective dimension. -/
def totalShiftLength (g : RankFunction V) : ℕ := totalAugmentedValue g Finset.univ - g Finset.univ
/-- Both branches of the canonical rank on the actual added coordinate `none`. -/
def totalHomogenizedValue (g : RankFunction V) (A : Finset (Option V)) : ℕ :=
  if none ∈ A then totalShiftLength g + g A.eraseNone else totalAugmentedValue g A.eraseNone
/-- Literal homogenized sum of genuine homological-shift ideals, in the polynomial
ring with one new coordinate. Every degree from0 throughp is included. -/
def totalHomogenizedIdeal (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (p : ℕ) : Ideal (MvPolynomial (Option V) k) :=
  ∑ i ∈ Finset.range (p + 1),
    Ideal.span {MvPolynomial.X (R := k) none ^ (p - i)} *
      Ideal.map (MvPolynomial.rename some).toRingHom (homologicalShiftIdeal I hI i)


private theorem totalAugmentedValue_eq_source (g : RankFunction V) (A : Finset V) :
    totalAugmentedValue g A = universalAugmentedRank g A := by
  rw [universalAugmentedRank_apply]
  apply congrArg (fun f : Finset V → ℕ => partitionRank f A)
  funext B
  exact (cardinalLift_apply g B).symm
private theorem totalShiftLength_eq_source (g : RankFunction V) :
    totalShiftLength g = shiftLength g := by
  have h := shiftLength_add_degree g
  rw [← totalAugmentedValue_eq_source g Finset.univ] at h
  unfold totalShiftLength
  omega
private theorem totalHomogenizedValue_eq_source (g : RankFunction V)
    (A : Finset (Option V)) :
    totalHomogenizedValue g A = homogenizedShiftRank g A := by
  simp only [totalHomogenizedValue, totalShiftLength_eq_source, totalAugmentedValue_eq_source,
    homogenizedShiftRank, RankFunction.homogenize_apply, homogenizedRankValue, shiftLength, rankGap]
private theorem totalHomogenizedIdeal_eq_source (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (p : ℕ) :
    totalHomogenizedIdeal I hI p = homogenizedHomologicalIdeal I hI p := by
  simp only [totalHomogenizedIdeal, homogenizedHomologicalIdeal, agrees_with_derivedTor]

/-- Complete Theorem5.1: actual homogenized ideal, genuine projective dimension,
equigeneration, canonical rank on every subset and every actual nonzero Tor multidegree.
No positivity assumption on the rank and no inactive coordinate is discarded. -/
theorem totalSupportHomogenization (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g) :
    ∃ p : ℕ, p = totalShiftLength g ∧
      CategoryTheory.projectiveDimension (ModuleCat.of (MvPolynomial V k) I) =
        (p : WithBot ℕ∞) ∧
      ∃ hH : IsPolymatroidalIdeal (totalHomogenizedIdeal I hI p),
        Equigenerated (idealGenerators (totalHomogenizedIdeal I hI p) hH) (g Finset.univ + p) ∧
        (∀ A : Finset (Option V),
          upperRank (idealGenerators (totalHomogenizedIdeal I hI p) hH) A =
            totalHomogenizedValue g A) ∧
        (∀ e : Exponent (Option V),
          e ∈ idealGenerators (totalHomogenizedIdeal I hI p) hH ↔
            ∃ i ≤ p, ∃ a : Exponent V,
              Simplicial.literalNonzeroHomology (k := k)
                (Koszul.koszulFaces (idealGenerators I hI) a) i ∧
              e = a.optionElim (p - i)) := by
  simpa only [totalShiftLength_eq_source, totalHomogenizedIdeal_eq_source,
    totalHomogenizedValue_eq_source, Simplicial.literalNonzeroHomology_iff,
    Koszul.gradedBettiNonzero_iff_faces] using
      (FourPapers.Homological.theorem_5_1 I hI g he)

/-- Both displayed canonical rank formulas of Theorem5.1 on every original subset. -/
theorem totalCanonicalRankFormulas (g : RankFunction V) (hg : g.Active) (A : Finset V) :
    totalHomogenizedValue g (A.image some) = A.card + partitionRank g A ∧
      totalHomogenizedValue g A.insertNone = totalShiftLength g + g A := by
  simpa only [totalHomogenizedValue_eq_source, totalShiftLength_eq_source] using
    (FourPapers.Homological.theorem_5_1_rank g hg A)

end PalomarHomological

namespace PalomarHomological
open CommAlg CommAlg.Polymatroid
open scoped BigOperators
universe uMixed uMixedColor
variable {V k : Type uMixed} [Fintype V] [LinearOrder V] [Field k]
variable {C : Type uMixedColor} [Fintype C] [DecidableEq C]


/-- Polymatroidality of the exact finite product of color powers. -/
theorem mixedProductPolymatroidal (I : C → Ideal (MvPolynomial V k))
    (hI : ∀ c, IsPolymatroidalIdeal (I c)) (s : C →₀ ℕ) :
    IsPolymatroidalIdeal (powerProduct I s) := by exact CommAlg.polymatroidal_powerProduct I hI s

/-- Actual homological-shift coefficient ideal at each color multidegree;
no positive-coordinate restriction and no replacement by a predicted rank. -/
def mixedPiece (J : Ideal (MvPolynomial V k)) (I : C → Ideal (MvPolynomial V k))
    (hJ : IsPolymatroidalIdeal J) (hI : ∀ c, IsPolymatroidalIdeal (I c))
    (i : ℕ) (s : C →₀ ℕ) : Ideal (MvPolynomial V k) :=
  homologicalShiftIdeal (J * powerProduct I s)
    (mulPolymatroidal hJ (mixedProductPolymatroidal I hI s)) i

private theorem mixedPiece_eq_source (J : Ideal (MvPolynomial V k))
    (I : C → Ideal (MvPolynomial V k)) (hJ : IsPolymatroidalIdeal J)
    (hI : ∀ c, IsPolymatroidalIdeal (I c)) (i : ℕ) (s : C →₀ ℕ) :
    mixedPiece J I hJ hI i s = CommAlg.homologicalMultiPiece J I hJ hI i s := by
  simp only [mixedPiece, CommAlg.homologicalMultiPiece, agrees_with_derivedTor]

/-- Zero closure of the literal coefficientwise homological multi-Rees ideal. -/
theorem mixedZero (J : Ideal (MvPolynomial V k)) (I : C → Ideal (MvPolynomial V k))
    (hJ : IsPolymatroidalIdeal J) (hI : ∀ c, IsPolymatroidalIdeal (I c)) (i : ℕ) :
    ∀ s, (0 : multiReesAlgebra I).val.coeff s ∈ mixedPiece J I hJ hI i s := by
  intro s
  simpa only [Subalgebra.coe_zero, MvPolynomial.coeff_zero] using
    (mixedPiece J I hJ hI i s).zero_mem

/-- Addition closure of the exact actual coefficient ideals. -/
theorem mixedAdd (J : Ideal (MvPolynomial V k)) (I : C → Ideal (MvPolynomial V k))
    (hJ : IsPolymatroidalIdeal J) (hI : ∀ c, IsPolymatroidalIdeal (I c)) (i : ℕ)
    {p q : multiReesAlgebra I}
    (hp : ∀ s, p.val.coeff s ∈ mixedPiece J I hJ hI i s)
    (hq : ∀ s, q.val.coeff s ∈ mixedPiece J I hJ hI i s) :
    ∀ s, (p + q).val.coeff s ∈ mixedPiece J I hJ hI i s := by
  intro s
  simpa only [Subalgebra.coe_add, MvPolynomial.coeff_add] using
    (mixedPiece J I hJ hI i s).add_mem (hp s) (hq s)

/-- Closure under actual multi-Rees multiplication, from the genuine shift action. -/
theorem mixedMul (J : Ideal (MvPolynomial V k)) (I : C → Ideal (MvPolynomial V k))
    (hJ : IsPolymatroidalIdeal J) (hI : ∀ c, IsPolymatroidalIdeal (I c)) (i : ℕ)
    (r p : multiReesAlgebra I) (hp : ∀ s, p.val.coeff s ∈ mixedPiece J I hJ hI i s) :
    ∀ s, (r * p).val.coeff s ∈ mixedPiece J I hJ hI i s := by
  intro s
  change (r.val * p.val).coeff s ∈ mixedPiece J I hJ hI i s
  rw [MvPolynomial.coeff_mul]
  apply Ideal.sum_mem
  intro uv huv
  have he : uv.1 + uv.2 = s := Finset.mem_antidiagonal.mp huv
  have hpv : p.val.coeff uv.2 ∈ CommAlg.homologicalMultiPiece J I hJ hI i uv.2 := by
    simpa only [mixedPiece_eq_source] using hp uv.2
  rw [← he, mixedPiece_eq_source]
  exact CommAlg.homologicalMultiPiece_action J I hJ hI i uv.1 uv.2
    (Ideal.mul_mem_mul (r.property uv.1) hpv)

/-- Literal ideal in the actual multi-Rees algebra, containing precisely the
polynomials whose coefficients lie in the actual homological-shift pieces. -/
def mixedIdeal (J : Ideal (MvPolynomial V k)) (I : C → Ideal (MvPolynomial V k))
    (hJ : IsPolymatroidalIdeal J) (hI : ∀ c, IsPolymatroidalIdeal (I c))
    (i : ℕ) : Ideal (multiReesAlgebra I) where
  carrier := {p | ∀ s, p.val.coeff s ∈ mixedPiece J I hJ hI i s}
  zero_mem' := mixedZero J I hJ hI i
  add_mem' := mixedAdd J I hJ hI i
  smul_mem' := mixedMul J I hJ hI i
/-- Every actual homogeneous module element in the closed coordinate box;
its polynomial coefficient is unrestricted inside the corresponding shift ideal. -/
def mixedBoxGenerators (J : Ideal (MvPolynomial V k)) (I : C → Ideal (MvPolynomial V k))
    (hJ : IsPolymatroidalIdeal J) (hI : ∀ c, IsPolymatroidalIdeal (I c))
    (i : ℕ) : Set (multiReesAlgebra I) :=
  {p | ∃ s r, (∀ c, s c ≤ i) ∧ r ∈ mixedPiece J I hJ hI i s ∧
    p.val = MvPolynomial.monomial s r}

private theorem mixedIdeal_eq_source (J : Ideal (MvPolynomial V k))
    (I : C → Ideal (MvPolynomial V k)) (hJ : IsPolymatroidalIdeal J)
    (hI : ∀ c, IsPolymatroidalIdeal (I c)) (i : ℕ) :
    mixedIdeal J I hJ hI i = CommAlg.homologicalMultiIdeal J I hJ hI i := by
  ext p
  change (∀ s, p.val.coeff s ∈ mixedPiece J I hJ hI i s) ↔
    ∀ s, p.val.coeff s ∈ CommAlg.homologicalMultiPiece J I hJ hI i s
  simp only [mixedPiece_eq_source]
private theorem mixedBoxGenerators_eq_source (J : Ideal (MvPolynomial V k))
    (I : C → Ideal (MvPolynomial V k)) (hJ : IsPolymatroidalIdeal J)
    (hI : ∀ c, IsPolymatroidalIdeal (I c)) (i : ℕ) :
    mixedBoxGenerators J I hJ hI i =
      CommAlg.reesBoxGenerators I (CommAlg.homologicalMultiPiece J I hJ hI i) i := by
  ext p
  simp only [mixedBoxGenerators, CommAlg.reesBoxGenerators, mixedPiece_eq_source]

/-- Full Corollary4.1 coordinatewise stabilization with arbitrary fixed twist,
all finite color sets and all untouched zero coordinates. -/
theorem mixedStabilization (I : C → Ideal (MvPolynomial V k))
    (J : Ideal (MvPolynomial V k)) (hI : ∀ c, IsPolymatroidalIdeal (I c))
    (hJ : IsPolymatroidalIdeal J) (s : C →₀ ℕ) (i : ℕ) (c : C)
    (hi : 0 < i) (hs : i ≤ s c) :
    mixedPiece J I hJ hI i (s + Finsupp.single c 1) = I c * mixedPiece J I hJ hI i s := by
  simpa only [mixedPiece, agrees_with_derivedTor] using
    (FourPapers.Homological.corollary_4_1 I J hI hJ s i c hi hs)

/-- The complete actual multi-Rees module generation clause of Corollary4.1. -/
theorem mixedGeneration (I : C → Ideal (MvPolynomial V k))
    (J : Ideal (MvPolynomial V k)) (hI : ∀ c, IsPolymatroidalIdeal (I c))
    (hJ : IsPolymatroidalIdeal J) (i : ℕ) :
    mixedIdeal J I hJ hI i = Ideal.span (mixedBoxGenerators J I hJ hI i) := by
  simpa only [mixedIdeal_eq_source, mixedBoxGenerators_eq_source] using
    (FourPapers.Homological.corollary_4_1_generation I J hI hJ i)

/-- Full Corollary6.2: actual multi-Rees integral closure for arbitrary finite
colors, all fixed polymatroidal twists and all multidegrees including zero coordinates. -/
theorem mixedIntegralClosure (I : C → Ideal (MvPolynomial V k))
    (J : Ideal (MvPolynomial V k)) (hI : ∀ c, IsPolymatroidalIdeal (I c))
    (hJ : IsPolymatroidalIdeal J) (hIne : ∀ c, I c ≠ ⊥) (i : ℕ) :
    IsIntegrallyClosedIdeal (mixedIdeal J I hJ hI i) := by
  rw [mixedIdeal_eq_source]
  change CommAlg.IsIntegrallyClosedIdeal (CommAlg.homologicalMultiIdeal J I hJ hI i)
  exact FourPapers.Homological.corollary_6_2 I J hI hJ hIne i

end PalomarHomological
