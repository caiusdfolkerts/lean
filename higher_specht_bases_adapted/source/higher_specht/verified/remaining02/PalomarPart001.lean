module

public import higher_specht.verified.remaining02.PalomarPart000
import all higher_specht.verified.remaining02.PalomarPart000
public import higher_specht.verified.remaining01
public import tau_ceti.combinatorics.enumerative.partition.box_move
public import Mathlib.Data.Multiset.Pairwise
public import Mathlib.Data.Complex.Basic

/- Generated ordinary source-preserving proof stage. See audit/staged_specht_remaining/Remaining02/manifest.json. -/

@[expose] public section

section CanonicalSource56
/- Source: HigherSpecht/FiniteCommonSpechtCopies.lean -/



/-!
# The genuine finite common cyclic Specht copies

The multiplicity vectors are the exact maximal-prefix vectors defined for
Theorem 5.2.  Their ambient representation is the actual annihilator of the
empty-partition Griffin ideal.  The map from the ordinary Young ideal is
constructed from the actual Young-image vector, and its range is proved to be
the specified cyclic polynomial span.  Spanning the nonempty-partition
harmonic spaces is a separate remaining assertion.
-/

noncomputable section

open TauCeti TauCeti.YoungTableau MvPolynomial Module
open scoped Classical

namespace HigherSpecht

theorem adjointYoungApply_smul {mu : YoungDiagram} (T : YoungTableau mu)
    (c : ℂ) (p : PolynomialRing mu.card ℂ) :
    adjointYoungApply T (c • p) = c • adjointYoungApply T p := by
  simp only [adjointYoungApply, rowSymmetrize, columnAlternate, map_sum, map_smul,
    Finset.smul_sum, smul_comm c]

def fixedFiniteToHarmonic {n s : ℕ} (part : n.Partition)
    (i : FixedFiniteHarmonicIndex (YoungDiagram.ofPartition part) s) : FiniteHarmonicIndex n s where
  part := part
  left := i.left
  multiplier := i.multiplier
  multiplier_length := by
    simpa [YoungDiagram.card_ofPartition, YoungDiagram.card] using i.multiplier_length
  descents_lt := i.descents_lt
  multiplier_width := i.multiplier_width

def finiteHarmonicToFixed {n s : ℕ} (i : FiniteHarmonicIndex n s) :
    FixedFiniteHarmonicIndex (YoungDiagram.ofPartition i.part) s where
  left := i.left
  multiplier := i.multiplier
  eligible := prefixEligible_bot
    ⟨YoungDiagram.ofPartition i.part, rfl, i.left,
      StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition i.part)⟩
  descents_lt := i.descents_lt
  multiplier_length := by
    simpa [YoungDiagram.card_ofPartition, YoungDiagram.card] using i.multiplier_length
  multiplier_width := i.multiplier_width

def finiteHarmonicIndexEquiv (n s : ℕ) :
    FiniteHarmonicIndex n s ≃ Σ part : n.Partition,
      FixedFiniteHarmonicIndex (YoungDiagram.ofPartition part) s where
  toFun i := ⟨i.part, finiteHarmonicToFixed i⟩
  invFun z := fixedFiniteToHarmonic z.1 z.2
  left_inv i := by cases i; rfl
  right_inv z := by rcases z with ⟨part, i⟩; cases i; rfl

theorem fixedCommonCut_toFinite {n s : ℕ} (part : n.Partition)
    (i : FixedFiniteHarmonicIndex (YoungDiagram.ofPartition part) s) :
    fixedCommonCut i = maximalFinitePrefix (fixedFiniteToHarmonic part i) := by
  simp only [fixedCommonCut, maximalFinitePrefix, fixedFiniteToHarmonic,
    YoungDiagram.card_ofPartition]

theorem finiteCommonHarmonicVector_toFixed {n s : ℕ} (part : n.Partition)
    (i : FixedFiniteHarmonicIndex (YoungDiagram.ofPartition part) s) :
    finiteCommonHarmonicVector (fixedFiniteToHarmonic part i) =
      MvPolynomial.rename (finCongr (YoungDiagram.card_ofPartition part))
        (fixedCommonHarmonicVector (StandardYoungTableau.rowSuperstandard _) i) := by
  simp only [finiteCommonHarmonicVector, fixedCommonHarmonicVector, fixedFiniteToHarmonic,
    normalizedOrdinaryDerivative, adjointYoungApply_smul, fixedCommonCut_toFinite] <;> rfl

theorem finiteHarmonicIndex_eligible_bot {n s : ℕ} (i : FiniteHarmonicIndex n s) :
    i.toUnboundedHarmonicIndex.eligible ⊥ (by simp [YoungDiagram.card]) := by
  refine ⟨?_, ?_⟩
  · simpa [YoungDiagram.card] using i.multiplier_length
  · exact prefixEligible_bot
      ⟨YoungDiagram.ofPartition i.part, rfl, i.left,
        StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition i.part)⟩

def finiteCommonAmbient (n s : ℕ) : Subrepresentation (polynomialRepresentation ℂ n) :=
  ordinaryHarmonicRepresentation (griffinIdeal ℂ n ⊥ s) (permutationStable_griffinIdeal ⊥ s)

theorem finiteCommonAmbient_finiteDimensional (n s : ℕ) (hs : 0 < s) :
    FiniteDimensional ℂ (finiteCommonAmbient n s).toSubmodule :=
  finiteDimensional_ordinaryGriffinHarmonics n s ⊥ hs

def subrepresentationInclusion {K G M : Type*} [CommSemiring K] [Monoid G]
    [AddCommMonoid M] [Module K M] {rho : Representation K G M} (V : Subrepresentation rho) :
    V.toRepresentation.IntertwiningMap rho where
  toLinearMap := V.toSubmodule.subtype
  isIntertwining' g := by ext v; rfl

theorem polynomial_asAlgebraHom_domCongr_rename {n m : ℕ} (e : Fin n ≃ Fin m)
    (a : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) (p : PolynomialRing n ℂ) :
    (polynomialRepresentation ℂ m).asAlgebraHom
      (MonoidAlgebra.domCongr ℂ ℂ e.permCongrHom a) (MvPolynomial.rename e p) =
        MvPolynomial.rename e ((polynomialRepresentation ℂ n).asAlgebraHom a p) := by
  apply MonoidAlgebra.induction_on a
  · intro g
    simp only [MonoidAlgebra.of_apply, MonoidAlgebra.domCongr_single,
      Representation.asAlgebraHom_single, one_smul, polynomialRepresentation_apply,
      MvPolynomial.rename_rename]
    apply congrArg (fun f : Fin n → Fin m => MvPolynomial.rename (R := ℂ) f p)
    funext i
    simp only [Function.comp_apply, Equiv.permCongrHom_coe, Equiv.permCongr_apply,
      Equiv.symm_apply_apply]
  · intro a b ha hb
    simp only [map_add, LinearMap.add_apply, ha, hb]
  · intro c a ha
    simp only [map_smul, LinearMap.smul_apply, ha]

def finiteCommonPreVector {n s : ℕ} (i : FiniteHarmonicIndex n s) : PolynomialRing n ℂ :=
  let T := (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition i.part)).toTableau
  let r := griffinWitnessRejection i.left T i.multiplier (maximalFinitePrefix i)
    (maximalFinitePrefix_le i) s
  let G := griffinApolarWitness i.left T (maximalFinitePrefix i) (maximalFinitePrefix_le i) s
  MvPolynomial.rename (finCongr (YoungDiagram.card_ofPartition i.part))
    (normalizedOrdinaryDerivative r G)

theorem finiteCommonPreVector_mem {n s : ℕ} (i : FiniteHarmonicIndex n s) (hs : 0 < s) :
    finiteCommonPreVector i ∈ (finiteCommonAmbient n s).toSubmodule := by
  apply ordinaryHarmonics_rename_finCongr (YoungDiagram.card_ofPartition i.part) ⊥ s
  apply (ordinaryHarmonics _).smul_mem
  exact ordinaryAction_mem_harmonics
    (finiteCommonApolarWitness_mem_ordinaryHarmonics i hs ⊥
      (by simp [YoungDiagram.card]) (by simp) (finiteHarmonicIndex_eligible_bot i)) _

theorem finiteCommonHarmonicVector_mem_ambient {n s : ℕ} (i : FiniteHarmonicIndex n s)
    (hs : 0 < s) : finiteCommonHarmonicVector i ∈ (finiteCommonAmbient n s).toSubmodule :=
  finiteCommonHarmonicVector_mem i hs ⊥ (by simp [YoungDiagram.card]) (by simp)
    (finiteHarmonicIndex_eligible_bot i)

theorem finiteCommonHarmonicVector_youngImage {n s : ℕ} (i : FiniteHarmonicIndex n s) :
    (polynomialRepresentation ℂ n).asAlgebraHom (i.part.youngSymmetrizer ℂ)
      (finiteCommonPreVector i) = finiteCommonHarmonicVector i := by
  rw [Nat.Partition.youngSymmetrizer_def]
  simp only [finiteCommonPreVector, polynomial_asAlgebraHom_domCongr_rename,
    asAlgebraHom_youngSymmetrizer_adjoint, normalizedOrdinaryDerivative,
    adjointYoungApply_smul, finiteCommonHarmonicVector]

def finiteCommonYoungImage {n s : ℕ} (i : FiniteHarmonicIndex n s) (hs : 0 < s) :
    YoungImage (finiteCommonAmbient n s).toRepresentation i.part :=
  ⟨⟨finiteCommonHarmonicVector i, finiteCommonHarmonicVector_mem_ambient i hs⟩,
    ⟨⟨finiteCommonPreVector i, finiteCommonPreVector_mem i hs⟩, by
      apply Subtype.ext
      exact ((subrepresentationInclusion (finiteCommonAmbient n s)).apply_asAlgebraHom
        (i.part.youngSymmetrizer ℂ) ⟨finiteCommonPreVector i, finiteCommonPreVector_mem i hs⟩).trans
        (finiteCommonHarmonicVector_youngImage i)⟩⟩

theorem finiteCommonYoungImage_linearIndependent {n s : ℕ} (part : n.Partition) (hs : 0 < s) :
    LinearIndependent (M := YoungImage (finiteCommonAmbient n s).toRepresentation part) ℂ
      (fun i : FixedFiniteHarmonicIndex (YoungDiagram.ofPartition part) s =>
      (finiteCommonYoungImage (fixedFiniteToHarmonic part i) hs :
        YoungImage (finiteCommonAmbient n s).toRepresentation part)) := by
  let e := finCongr (YoungDiagram.card_ofPartition part)
  have h : LinearIndependent ℂ
      (fun i : FixedFiniteHarmonicIndex (YoungDiagram.ofPartition part) s =>
        MvPolynomial.rename e
          (fixedCommonHarmonicVector
            (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition part)) i)) := by
    simpa only [Function.comp_def, AlgHom.coe_toLinearMap, AlgHom.toLinearMap_apply] using
      (fixedCommonHarmonicVector_linearIndependent (s := s)
        (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition part))).map'
          (MvPolynomial.rename e).toLinearMap
            (LinearMap.ker_eq_bot.mpr (MvPolynomial.rename_injective e e.injective))
  apply LinearIndependent.of_comp ((finiteCommonAmbient n s).toSubmodule.subtype.comp
    (YoungImage (finiteCommonAmbient n s).toRepresentation part).subtype)
  change LinearIndependent ℂ
    (fun i : FixedFiniteHarmonicIndex (YoungDiagram.ofPartition part) s =>
      finiteCommonHarmonicVector (fixedFiniteToHarmonic part i))
  have hfamily :
      (fun i : FixedFiniteHarmonicIndex (YoungDiagram.ofPartition part) s =>
        finiteCommonHarmonicVector (fixedFiniteToHarmonic part i)) =
      (fun i : FixedFiniteHarmonicIndex (YoungDiagram.ofPartition part) s =>
        MvPolynomial.rename e
          (fixedCommonHarmonicVector
            (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition part)) i)) := by
    funext i
    exact finiteCommonHarmonicVector_toFixed part i
  rw [hfamily]
  exact h

theorem finiteCommonYoungImage_ne_zero {n s : ℕ} (i : FiniteHarmonicIndex n s) (hs : 0 < s) :
    finiteCommonYoungImage i hs ≠ 0 := by
  have h := (finiteCommonYoungImage_linearIndependent i.part hs).ne_zero (finiteHarmonicToFixed i)
  cases i
  exact h

theorem finiteCommonHarmonicCopy_eq_map_cyclic {n s : ℕ}
    (i : FiniteHarmonicIndex n s) (hs : 0 < s) :
    finiteCommonHarmonicCopy i =
      (cyclicRepresentationSpan (finiteCommonAmbient n s).toRepresentation
        (finiteCommonYoungImage i hs)).map (finiteCommonAmbient n s).toSubmodule.subtype := by
  rw [cyclicRepresentationSpan, Submodule.map_span, ← Set.range_comp]
  rfl

/-- Each exact manuscript vector generates a full ordinary Specht copy. -/
theorem finiteCommonHarmonicCopy_isSpecht {n s : ℕ} (i : FiniteHarmonicIndex n s) (hs : 0 < s) :
    IsSpechtPolynomialCopy i.part (finiteCommonHarmonicCopy i) := by
  letI := finiteCommonAmbient_finiteDimensional n s hs
  let f := intertwinerOfYoungImage (finiteCommonAmbient n s).toRepresentation i.part
    (finiteCommonYoungImage i hs)
  let e := subrepresentationInclusion (finiteCommonAmbient n s)
  refine ⟨e.comp f, Subtype.val_injective.comp
    (intertwinerOfYoungImage_injective _ _ _ (finiteCommonYoungImage_ne_zero i hs)), ?_⟩
  rw [finiteCommonHarmonicCopy_eq_map_cyclic i hs, ← range_intertwinerOfYoungImage]
  exact LinearMap.range_comp f.toLinearMap e.toLinearMap

/-- The literal cyclic copies are independent simultaneously across all
standard tableaux, boosts, and shapes, without a dimension-count premise. -/
theorem finiteCommonHarmonicCopies_iSupIndep {n s : ℕ} (hs : 0 < s) :
    iSupIndep (finiteCommonHarmonicCopy (n := n) (s := s)) := by
  letI := finiteCommonAmbient_finiteDimensional n s hs
  have h := intertwinerOfYoungImage_copies_iSupIndep
    (finiteCommonAmbient n s).toRepresentation
    (fun part (i : FixedFiniteHarmonicIndex (YoungDiagram.ofPartition part) s) =>
      (finiteCommonYoungImage (fixedFiniteToHarmonic part i) hs :
        YoungImage (finiteCommonAmbient n s).toRepresentation part))
    (fun part => finiteCommonYoungImage_linearIndependent part hs)
  have hm := LinearMap.iSupIndep_map (finiteCommonAmbient n s).toSubmodule.subtype
    Subtype.val_injective h
  have hc := hm.comp (finiteHarmonicIndexEquiv n s).injective
  convert hc using 1
  funext i
  change finiteCommonHarmonicCopy i =
    (cyclicRepresentationSpan (finiteCommonAmbient n s).toRepresentation
      (finiteCommonYoungImage
        (fixedFiniteToHarmonic (finiteHarmonicIndexEquiv n s i).1
          (finiteHarmonicIndexEquiv n s i).2) hs)).map
            (finiteCommonAmbient n s).toSubmodule.subtype
  rw [← finiteCommonHarmonicCopy_eq_map_cyclic]
  congr 1

end HigherSpecht
end
end CanonicalSource56

section CanonicalSource57
/- Source: HigherSpecht/CommonHarmonicDegrees.lean -/



/-!
# The actual degrees of the common harmonic copies

The degree is computed from the real support of the witness and the genuine
ordinary differential operator.  The rejection-vector identity is supplied by
the rearrangement construction; no external grading label is attached to a
polynomial independently of its coefficients.
-/

noncomputable section

open TauCeti TauCeti.YoungTableau MvPolynomial Finset
open scoped Classical

namespace HigherSpecht

theorem degree_permutedExponent {n : ℕ} (a : Fin n →₀ ℕ) (e : Equiv.Perm (Fin n)) :
    (permutedExponent a e).degree = a.degree := by
  simp only [Finsupp.degree_eq_sum, permutedExponent_apply]
  exact Equiv.sum_comp e a

theorem coefficientWitness_isHomogeneous {n : ℕ}
    (G : Subgroup (Equiv.Perm (Fin n))) (a : Fin n →₀ ℕ) :
    (coefficientWitness (R := ℂ) G a).IsHomogeneous a.degree := by
  apply MvPolynomial.IsHomogeneous.sum
  intro e he
  exact MvPolynomial.isHomogeneous_monomial _ (degree_permutedExponent a e.val)

theorem ordinaryAction_monomial_isHomogeneous {n d : ℕ} (r : Fin n →₀ ℕ)
    {p : PolynomialRing n ℂ} (hp : p.IsHomogeneous (d + r.degree)) :
    (ordinaryAction (MvPolynomial.monomial r (1 : ℂ)) p).IsHomogeneous d := by
  intro a ha
  have hcoeff : p.coeff (a + r) ≠ 0 := by
    intro hz
    rw [ordinaryAction_monomial_coeff, hz, zero_mul, zero_div] at ha
    exact ha rfl
  have hdeg : (a + r).degree = d + r.degree := by
    by_contra h
    exact hcoeff (hp.coeff_eq_zero h)
  rw [map_add] at hdeg
  have ha' : a.degree = d := Nat.add_right_cancel hdeg
  simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using ha'

theorem normalizedOrdinaryDerivative_isHomogeneous {n d : ℕ}
    (r : Fin n →₀ ℕ) {p : PolynomialRing n ℂ} (hp : p.IsHomogeneous (d + r.degree)) :
    (normalizedOrdinaryDerivative r p).IsHomogeneous d :=
  (MvPolynomial.homogeneousSubmodule (Fin n) ℂ d).smul_mem _
    (ordinaryAction_monomial_isHomogeneous r hp)

theorem adjointYoungApply_isHomogeneous {mu : YoungDiagram} (T : YoungTableau mu)
    {p : PolynomialRing mu.card ℂ} {d : ℕ} (hp : p.IsHomogeneous d) :
    (adjointYoungApply T p).IsHomogeneous d :=
  rowSymmetrize_isHomogeneous _ (columnAlternate_isHomogeneous _ hp)

theorem degree_transportedBoosted {mu : YoungDiagram} (S T : StandardYoungTableau mu)
    (eta : YoungDiagram) (heta : eta.colLen 0 ≤ mu.card) :
    (transportedBoosted S T.toTableau eta).degree = cochargeDegree S + eta.card := by
  have hp : (higherSpechtPolynomial (R := ℂ) S T *
      elementaryMultiplier mu.card mu.card eta.rowLen).IsHomogeneous
        (cochargeDegree S + eta.card) :=
    (higherSpechtPolynomial_isHomogeneous S T).mul
      (elementaryMultiplier_isHomogeneous mu.card mu.card eta heta)
  have hc : (higherSpechtPolynomial (R := ℂ) S T *
      elementaryMultiplier mu.card mu.card eta.rowLen).coeff
        (transportedBoosted S T.toTableau eta) ≠ 0 := by
    rw [lemma_4_2_distinguishedCoefficient S T le_rfl eta heta]
    exact_mod_cast (Finset.card_pos.mpr
      (rowFillingStabilizers_nonempty T.toTableau (transportedCocharge S T.toTableau))).ne'
  by_contra hd
  exact hc (hp.coeff_eq_zero hd)

theorem fixedCommonHarmonicVector_isHomogeneous {mu : YoungDiagram} {s : ℕ}
    (T : StandardYoungTableau mu) (i : FixedFiniteHarmonicIndex mu s) :
    (fixedCommonHarmonicVector T i).IsHomogeneous
      (cochargeDegree i.left + i.multiplier.card) := by
  let a := griffinWitnessAlpha i.left T.toTableau (fixedCommonCut i) (fixedCommonCut_le i) s
  let r := griffinWitnessRejection i.left T.toTableau i.multiplier
    (fixedCommonCut i) (fixedCommonCut_le i) s
  let b := transportedBoosted i.left T.toTableau i.multiplier
  have hgeom := griffinWitness_rearrangement i.left T.toTableau i.multiplier
    (fixedCommonCut i) (fixedCommonCut_le i) s
    (fixedCommonCut_multiplier_length i) i.descents_lt i.multiplier_width
  have harb : a = r + b := by
    ext j
    have h := hgeom.subtraction j
    change (b j : ℤ) = (a j : ℤ) - (r j : ℤ) at h
    simp only [Finsupp.add_apply]
    omega
  have hlen : i.multiplier.colLen 0 ≤ mu.card := by
    simpa [YoungDiagram.card] using i.multiplier_length
  have had : a.degree = cochargeDegree i.left + i.multiplier.card + r.degree := by
    rw [harb, map_add, show b.degree = cochargeDegree i.left + i.multiplier.card from
      degree_transportedBoosted i.left T i.multiplier hlen]
    exact Nat.add_comm _ _
  apply adjointYoungApply_isHomogeneous
  apply normalizedOrdinaryDerivative_isHomogeneous
  rw [griffinApolarWitness_eq_coefficientWitness, ← had]
  exact coefficientWitness_isHomogeneous _ _

theorem finiteCommonHarmonicVector_isHomogeneous {n s : ℕ} (i : FiniteHarmonicIndex n s) :
    (finiteCommonHarmonicVector i).IsHomogeneous i.toUnboundedHarmonicIndex.degree := by
  have h := (fixedCommonHarmonicVector_isHomogeneous
    (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition i.part))
    (finiteHarmonicToFixed i)).rename_isHomogeneous
      (f := finCongr (YoungDiagram.card_ofPartition i.part))
  rw [← finiteCommonHarmonicVector_toFixed] at h
  have hi : fixedFiniteToHarmonic i.part (finiteHarmonicToFixed i) = i :=
    (finiteHarmonicIndexEquiv n s).left_inv i
  rw [hi] at h
  simpa only [finiteHarmonicToFixed, UnboundedHarmonicIndex.degree] using h

theorem cyclicPolynomialCopy_le_homogeneous {n d : ℕ} {p : PolynomialRing n ℂ}
    (hp : p.IsHomogeneous d) :
    cyclicPolynomialCopy p ≤ MvPolynomial.homogeneousSubmodule (Fin n) ℂ d := by
  apply Submodule.span_le.mpr
  rintro _ ⟨e, rfl⟩
  exact hp.rename_isHomogeneous

/-- The full cyclic span has the precise cocharge-plus-partition degree. -/
theorem finiteCommonHarmonicCopy_le_homogeneous {n s : ℕ} (i : FiniteHarmonicIndex n s) :
    finiteCommonHarmonicCopy i ≤
      MvPolynomial.homogeneousSubmodule (Fin n) ℂ i.toUnboundedHarmonicIndex.degree :=
  cyclicPolynomialCopy_le_homogeneous (finiteCommonHarmonicVector_isHomogeneous i)

end HigherSpecht
end
end CanonicalSource57

section CanonicalSource58
/- Source: HigherSpecht/OrdinaryHarmonicDuality.lean -/



/-!
# Exact quotient duality for ordinary harmonic polynomials

The inverse map is a finite sum of actual factorial-normalized monomials.
Coordinate-power relations bound its support.  Thus this proves the genuine
duality, including surjectivity, without assuming a dimension theorem or
replacing the annihilator by an abstract vector space of the desired size.
-/

noncomputable section

open MvPolynomial Finset Module
open scoped Classical

namespace HigherSpecht

theorem ordinaryApolar_monomial {n : ℕ} (p : PolynomialRing n ℂ) (a : Fin n →₀ ℕ) :
    ordinaryApolarFunctional p (MvPolynomial.monomial a 1) =
      p.coeff a * (exponentFactorial a : ℂ) := by
  rw [ordinaryApolarFunctional_apply, ordinaryAction_monomial_coeff]
  simp [exponentFactorial]

theorem ordinaryApolarRepresenter_injective (n : ℕ) :
    Function.Injective (ordinaryApolarRepresenter n) := by
  intro p q hpq
  ext a
  have h := DFunLike.congr_fun hpq (MvPolynomial.monomial a 1)
  change ordinaryApolarFunctional p (MvPolynomial.monomial a 1) =
    ordinaryApolarFunctional q (MvPolynomial.monomial a 1) at h
  rw [ordinaryApolar_monomial, ordinaryApolar_monomial] at h
  exact (mul_right_cancel₀ (exponentFactorial_ne_zero a)) h

theorem mem_ordinaryHarmonics_iff_apolar {n : ℕ} (I : Ideal (PolynomialRing n ℂ))
    (p : PolynomialRing n ℂ) :
    p ∈ ordinaryHarmonics I ↔ ∀ f ∈ I, ordinaryApolarFunctional p f = 0 := by
  constructor
  · intro hp f hf
    rw [ordinaryApolarFunctional_apply, hp f hf, MvPolynomial.coeff_zero, Finsupp.zero_apply]
  · intro hp f hf
    apply MvPolynomial.ext
    intro a
    have h := hp (MvPolynomial.monomial a 1 * f) (I.mul_mem_left _ hf)
    rw [ordinaryApolarFunctional_apply, ordinaryAction_mul_apply] at h
    change ordinaryApolarFunctional (ordinaryAction f p) (MvPolynomial.monomial a 1) = 0 at h
    rw [ordinaryApolar_monomial] at h
    exact (mul_eq_zero.mp h).resolve_right (exponentFactorial_ne_zero a)

def ordinaryHarmonicQuotientDual {n : ℕ} (I : Ideal (PolynomialRing n ℂ)) :
    ordinaryHarmonics I →ₗ[ℂ] Module.Dual ℂ (PolynomialRing n ℂ ⧸ I) where
  toFun p := (I.restrictScalars ℂ).liftQ (ordinaryApolarFunctional p.val)
    (fun f hf => (mem_ordinaryHarmonics_iff_apolar I p.val).mp p.property f hf)
  map_add' p q := by
    apply LinearMap.ext
    intro z
    refine Submodule.Quotient.induction_on _ z ?_
    intro f
    change ordinaryApolarFunctional (p.val + q.val) f =
      ordinaryApolarFunctional p.val f + ordinaryApolarFunctional q.val f
    simp only [ordinaryApolarFunctional_apply, map_add, MvPolynomial.coeff_add]
  map_smul' c p := by
    apply LinearMap.ext
    intro z
    refine Submodule.Quotient.induction_on _ z ?_
    intro f
    change ordinaryApolarFunctional (c • p.val) f = c • ordinaryApolarFunctional p.val f
    simp only [ordinaryApolarFunctional_apply, map_smul, MvPolynomial.coeff_smul]

@[simp] theorem ordinaryHarmonicQuotientDual_mk {n : ℕ}
    (I : Ideal (PolynomialRing n ℂ)) (p : ordinaryHarmonics I) (f : PolynomialRing n ℂ) :
    ordinaryHarmonicQuotientDual I p (Ideal.Quotient.mk I f) = ordinaryApolarFunctional p.val f := rfl

theorem ordinaryHarmonicQuotientDual_injective {n : ℕ} (I : Ideal (PolynomialRing n ℂ)) :
    Function.Injective (ordinaryHarmonicQuotientDual I) := by
  intro p q hpq
  apply Subtype.ext
  apply ordinaryApolarRepresenter_injective n
  apply LinearMap.ext
  intro f
  exact DFunLike.congr_fun hpq (Ideal.Quotient.mk I f)

abbrev BoxExponent (n s : ℕ) := {a : Fin n →₀ ℕ // ∀ i, a i < s}

instance finiteBoxExponent (n s : ℕ) : Finite (BoxExponent n s) := by
  apply Finite.of_injective (fun a : BoxExponent n s => fun i => (⟨a.val i, a.property i⟩ : Fin s))
  intro a b h
  apply Subtype.ext
  ext i
  exact congrArg Fin.val (congrFun h i)

noncomputable instance fintypeBoxExponent (n s : ℕ) : Fintype (BoxExponent n s) := Fintype.ofFinite _

def boundedApolarRepresentative {n : ℕ} (s : ℕ) (L : Module.Dual ℂ (PolynomialRing n ℂ)) :
    PolynomialRing n ℂ :=
  ∑ a : BoxExponent n s,
    MvPolynomial.monomial a.val (L (MvPolynomial.monomial a.val 1) / exponentFactorial a.val)

theorem boundedApolarRepresentative_coeff {n : ℕ} (s : ℕ)
    (L : Module.Dual ℂ (PolynomialRing n ℂ)) (a : Fin n →₀ ℕ) :
    (boundedApolarRepresentative s L).coeff a =
      if ∀ i, a i < s then L (MvPolynomial.monomial a 1) / exponentFactorial a else 0 := by
  rw [boundedApolarRepresentative, MvPolynomial.coeff_sum]
  split_ifs with ha
  · rw [Finset.sum_eq_single (⟨a, ha⟩ : BoxExponent n s)]
    · simp
    · intro b hb hba
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro h
      exact hba (Subtype.ext h)
    · simp
  · apply Finset.sum_eq_zero
    intro b hb
    rw [MvPolynomial.coeff_monomial, if_neg]
    intro h
    exact ha (h ▸ b.property)

theorem monomial_mem_of_large_coordinate {n s : ℕ} (I : Ideal (PolynomialRing n ℂ))
    (hpower : powerIdeal ℂ n s ≤ I) (a : Fin n →₀ ℕ) (i : Fin n) (hi : s ≤ a i) :
    MvPolynomial.monomial a (1 : ℂ) ∈ I := by
  have hle : Finsupp.single i s ≤ a := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Finsupp.single_eq_same] using hi
    · simp only [Finsupp.single_eq_of_ne hji, Nat.zero_le]
  have hx : (MvPolynomial.X i : PolynomialRing n ℂ) ^ s ∈ I :=
    hpower (Ideal.subset_span ⟨i, rfl⟩)
  have h := I.mul_mem_left (MvPolynomial.monomial (a - Finsupp.single i s) 1) hx
  simpa only [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul,
    one_mul, tsub_add_cancel_of_le hle] using h

theorem boundedApolarRepresentative_pairing {n s : ℕ} (I : Ideal (PolynomialRing n ℂ))
    (hpower : powerIdeal ℂ n s ≤ I) (L : Module.Dual ℂ (PolynomialRing n ℂ))
    (hL : ∀ f ∈ I, L f = 0) (f : PolynomialRing n ℂ) :
    ordinaryApolarFunctional (boundedApolarRepresentative s L) f = L f := by
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => rw [map_add, map_add, hf, hg]
  | monomial a c =>
    have hm : (MvPolynomial.monomial a c : PolynomialRing n ℂ) = c • MvPolynomial.monomial a 1 := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [hm, map_smul, map_smul, ordinaryApolar_monomial, boundedApolarRepresentative_coeff]
    congr 1
    split_ifs with ha
    · exact div_mul_cancel₀ _ (exponentFactorial_ne_zero a)
    · obtain ⟨i, hi⟩ := not_forall.mp ha
      rw [hL _ (monomial_mem_of_large_coordinate I hpower a i (le_of_not_gt hi)), zero_mul]

theorem ordinaryHarmonicQuotientDual_surjective {n s : ℕ} (I : Ideal (PolynomialRing n ℂ))
    (hpower : powerIdeal ℂ n s ≤ I) :
    Function.Surjective (ordinaryHarmonicQuotientDual I) := by
  intro L
  let Lp := L.comp (Ideal.Quotient.mkₐ ℂ I).toLinearMap
  have hLp : ∀ f ∈ I, Lp f = 0 := by
    intro f hf
    change L (Ideal.Quotient.mk I f) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]
  let p := boundedApolarRepresentative s Lp
  have hp : p ∈ ordinaryHarmonics I := by
    apply (mem_ordinaryHarmonics_iff_apolar I p).mpr
    intro f hf
    rw [boundedApolarRepresentative_pairing I hpower Lp hLp, hLp f hf]
  refine ⟨⟨p, hp⟩, ?_⟩
  apply LinearMap.ext
  intro z
  refine Submodule.Quotient.induction_on _ z ?_
  intro f
  exact boundedApolarRepresentative_pairing I hpower Lp hLp f

/-- Genuine ordinary-apolar duality for every ideal containing the displayed
coordinate powers.  The bound is used only to make the explicit inverse finite. -/
def ordinaryHarmonicQuotientDualEquiv {n s : ℕ} (I : Ideal (PolynomialRing n ℂ))
    (hpower : powerIdeal ℂ n s ≤ I) :
    ordinaryHarmonics I ≃ₗ[ℂ] Module.Dual ℂ (PolynomialRing n ℂ ⧸ I) :=
  LinearEquiv.ofBijective (ordinaryHarmonicQuotientDual I)
    ⟨ordinaryHarmonicQuotientDual_injective I, ordinaryHarmonicQuotientDual_surjective I hpower⟩

theorem finrank_ordinaryGriffinHarmonics (n s : ℕ) (lam : YoungDiagram) :
    Module.finrank ℂ (ordinaryHarmonics (griffinIdeal ℂ n lam s)) =
      Module.finrank ℂ (GriffinRing ℂ n lam s) := by
  rw [(ordinaryHarmonicQuotientDualEquiv (griffinIdeal ℂ n lam s) le_sup_right).finrank_eq,
    Subspace.dual_finrank_eq]

end HigherSpecht
end
end CanonicalSource58

section CanonicalSource59
/- Source: HigherSpecht/CommonHarmonicAssembly.lean -/



/-!
# Exact assembly and the remaining nonempty counting obligation

The dimension of the actual eligible sum is proved to equal the cardinality
of the manuscript's full Griffin index, including all right tableaux.
Consequently a genuine specified quotient basis gives the full harmonic
equality.  That transfer is deliberately named `of_specifiedBasis`: the
nonempty count is not asserted by it.  The empty-partition equality below
instantiates the transfer with the actual bounded-word basis.
-/

noncomputable section

open TauCeti TauCeti.YoungTableau Module
open scoped Classical

namespace HigherSpecht

instance finiteFiniteHarmonicIndex (n s : ℕ) : Finite (FiniteHarmonicIndex n s) :=
  Finite.of_injective (finiteHarmonicIndexEquiv n s) (finiteHarmonicIndexEquiv n s).injective

noncomputable instance fintypeFiniteHarmonicIndex (n s : ℕ) : Fintype (FiniteHarmonicIndex n s) :=
  Fintype.ofFinite _

abbrev EligibleFiniteHarmonicIndex (n s : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :=
  {i : FiniteHarmonicIndex n s // i.toUnboundedHarmonicIndex.eligible lam hk}

abbrev EligibleHarmonicTableauIndex (n s : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :=
  Σ i : EligibleFiniteHarmonicIndex n s lam hk,
    StandardYoungTableau (YoungDiagram.ofPartition i.val.part)

def eligibleHarmonicTableauPartitionEquiv (n s : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    EligibleHarmonicTableauIndex n s lam hk ≃ PartitionGriffinVectorIndex n lam hk s where
  toFun z :=
    ⟨z.1.val.part, z.2,
      { left := z.1.val.left
        multiplier := z.1.val.multiplier
        eligible := z.1.property.2
        descents_lt := z.1.val.descents_lt
        multiplier_length := by
          simpa only [YoungDiagram.card_ofPartition] using z.1.property.1
        multiplier_width := z.1.val.multiplier_width }⟩
  invFun z := by
    let i : FiniteHarmonicIndex n s :=
      { part := z.1
        left := z.2.2.left
        multiplier := z.2.2.multiplier
        multiplier_length := by
          have h := z.2.2.multiplier_length.trans (Nat.sub_le _ _)
          simpa only [YoungDiagram.card_ofPartition] using h
        descents_lt := z.2.2.descents_lt
        multiplier_width := z.2.2.multiplier_width }
    exact ⟨⟨i,
      ⟨by simpa only [YoungDiagram.card_ofPartition] using z.2.2.multiplier_length,
        z.2.2.eligible⟩⟩, z.2.1⟩
  left_inv z := by rcases z with ⟨⟨i, hi⟩, T⟩; cases i; rfl
  right_inv z := by rcases z with ⟨part, T, i⟩; cases i; rfl

def eligibleHarmonicTableauEquiv (n s : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    EligibleHarmonicTableauIndex n s lam hk ≃ GriffinIndex n lam hk s :=
  (eligibleHarmonicTableauPartitionEquiv n s lam hk).trans
    (partitionGriffinIndexEquiv n lam hk s)

theorem sum_standardCount_eligible_eq_card_griffin (n s : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) :
    (∑ i : EligibleFiniteHarmonicIndex n s lam hk,
      standardCount (YoungDiagram.ofPartition i.val.part)) = Nat.card (GriffinIndex n lam hk s) := by
  rw [← Nat.card_congr (eligibleHarmonicTableauEquiv n s lam hk),
    Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [standardCount_def]

theorem finrank_finiteCommonHarmonicCopy {n s : ℕ} (i : FiniteHarmonicIndex n s) (hs : 0 < s) :
    Module.finrank ℂ (finiteCommonHarmonicCopy i) =
      standardCount (YoungDiagram.ofPartition i.part) := by
  obtain ⟨f, hf, hr⟩ := finiteCommonHarmonicCopy_isSpecht i hs
  rw [← hr, LinearMap.finrank_range_of_inj hf,
    Nat.Partition.finrank_span_youngSymmetrizer, TauCeti.finrank_spechtModule]

theorem finite_finiteCommonHarmonicCopy {n s : ℕ} (i : FiniteHarmonicIndex n s) (hs : 0 < s) :
    Module.Finite ℂ (finiteCommonHarmonicCopy i) := by
  letI : Module.Finite ℂ (ordinaryHarmonics (griffinIdeal ℂ n ⊥ s)) :=
    finiteDimensional_ordinaryGriffinHarmonics n s ⊥ hs
  exact Module.Finite.of_injective
    (Submodule.inclusion (finiteCommonHarmonicCopy_le i hs ⊥
      (by simp [YoungDiagram.card]) (by simp) (finiteHarmonicIndex_eligible_bot i)))
    (Submodule.inclusion_injective _)

theorem finrank_iSup_of_independent {I : Type*} [Fintype I]
    {M : Type*} [AddCommGroup M] [Module ℂ M] (p : I → Submodule ℂ M)
    [∀ i, Module.Finite ℂ (p i)] (hp : iSupIndep p) :
    Module.finrank ℂ ↥(⨆ i, p i) = ∑ i, Module.finrank ℂ (p i) := by
  rw [Submodule.iSup_eq_range_dfinsupp_lsum,
    LinearMap.finrank_range_of_inj hp.dfinsupp_lsum_injective]
  change Module.finrank ℂ (DirectSum I (fun i => p i)) = _
  exact Module.finrank_directSum (R := ℂ) (fun i : I => p i)

def eligibleCommonHarmonicSum (n s : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Submodule ℂ (PolynomialRing n ℂ) :=
  ⨆ i : EligibleFiniteHarmonicIndex n s lam hk, finiteCommonHarmonicCopy i.val

theorem eligibleCommonHarmonicSum_le (n s : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    eligibleCommonHarmonicSum n s lam hk ≤ ordinaryHarmonics (griffinIdeal ℂ n lam s) := by
  apply iSup_le
  intro i
  exact finiteCommonHarmonicCopy_le i.val hs lam hk hheight i.property

theorem finrank_eligibleCommonHarmonicSum (n s : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hs : 0 < s) :
    Module.finrank ℂ (eligibleCommonHarmonicSum n s lam hk) = Nat.card (GriffinIndex n lam hk s) := by
  letI : ∀ i : EligibleFiniteHarmonicIndex n s lam hk,
      Module.Finite ℂ (finiteCommonHarmonicCopy i.val) :=
    fun i => finite_finiteCommonHarmonicCopy i.val hs
  have hi := (finiteCommonHarmonicCopies_iSupIndep hs).comp
    (show Function.Injective (fun i : EligibleFiniteHarmonicIndex n s lam hk => i.val) from
      Subtype.val_injective)
  change iSupIndep (fun i : EligibleFiniteHarmonicIndex n s lam hk =>
    finiteCommonHarmonicCopy i.val) at hi
  rw [eligibleCommonHarmonicSum, finrank_iSup_of_independent _ hi]
  simp_rw [finrank_finiteCommonHarmonicCopy _ hs]
  exact sum_standardCount_eligible_eq_card_griffin n s lam hk

/-- Auxiliary assembly only: its displayed basis input is the genuine
remaining nonempty-partition spanning obligation. -/
theorem finiteCommonHarmonic_decomposition_of_specifiedBasis
    (n s : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hs : 0 < s) (hheight : lam.colLen 0 ≤ s)
    (hb : IsSpecifiedBasis (R := ℂ) (griffinFamily ℂ n lam hk s)) :
    ordinaryHarmonics (griffinIdeal ℂ n lam s) = eligibleCommonHarmonicSum n s lam hk := by
  letI := finiteDimensional_ordinaryGriffinHarmonics n s lam hs
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_eq (eligibleCommonHarmonicSum_le n s lam hk hs hheight)
  rw [finrank_eligibleCommonHarmonicSum n s lam hk hs, finrank_ordinaryGriffinHarmonics]
  obtain ⟨b, hb⟩ := hb
  rw [Module.finrank_eq_card_basis b, Nat.card_eq_fintype_card]

/-- The empty-partition case uses the actual bounded-word basis.  No count or
basis hypothesis remains here; it is still a specified special case of 5.2. -/
theorem finiteCommonHarmonic_decomposition_empty (n s : ℕ) (hs : 0 < s) :
    ordinaryHarmonics (griffinIdeal ℂ n ⊥ s) =
      eligibleCommonHarmonicSum n s ⊥ (by simp [YoungDiagram.card]) :=
  finiteCommonHarmonic_decomposition_of_specifiedBasis n s ⊥
    (by simp [YoungDiagram.card]) hs (by simp) (griffin_empty_specifiedBasis ℂ n s hs)

/-- All structural and membership assertions, with the still-unproved general
spanning equality deliberately absent from this auxiliary conjunction. -/
theorem finiteCommonHarmonic_structure (n s : ℕ) (hs : 0 < s) :
    (∀ i : FiniteHarmonicIndex n s,
      IsSpechtPolynomialCopy i.part (finiteCommonHarmonicCopy i) ∧
      finiteCommonHarmonicCopy i ≤ MvPolynomial.homogeneousSubmodule (Fin n) ℂ
        i.toUnboundedHarmonicIndex.degree) ∧
    iSupIndep (finiteCommonHarmonicCopy (n := n) (s := s)) ∧
    ∀ (lam : YoungDiagram) (hk : lam.card ≤ n), lam.colLen 0 ≤ s →
      eligibleCommonHarmonicSum n s lam hk ≤ ordinaryHarmonics (griffinIdeal ℂ n lam s) :=
  ⟨fun i => ⟨finiteCommonHarmonicCopy_isSpecht i hs, finiteCommonHarmonicCopy_le_homogeneous i⟩,
    finiteCommonHarmonicCopies_iSupIndep hs,
    fun lam hk hheight => eligibleCommonHarmonicSum_le n s lam hk hs hheight⟩

end HigherSpecht
end
end CanonicalSource59

section CanonicalSource60
/- Source: HigherSpecht/CommonCopyStabilization.lean -/



/-!
# Stabilization of the manuscript's named common harmonic copies

Once the finite power bound contains the entire insertion diagram, its
maximal prefix is exactly the untruncated maximal prefix.  The two literal
vectors differ by the explicit nonzero factorial scalar already proved for
the exterior powers.  Thus their genuine cyclic polynomial submodules are
equal.  This also establishes all structural assertions of the untruncated
family without using a nonempty-partition spanning theorem.
-/

noncomputable section
open TauCeti TauCeti.YoungTableau Module MvPolynomial Finset
open scoped Classical

namespace HigherSpecht

theorem columnInsertion_height_le_card {mu : YoungDiagram} (S : StandardYoungTableau mu) :
    (columnInsertion S).state.shape.colLen 0 ≤ mu.card := by
  exact (colLen_zero_le_card _).trans_eq (columnInsertion S).shape_card

theorem maximalFinitePrefix_eq_untruncated {n s : ℕ} (i : FiniteHarmonicIndex n s)
    (hheight : (columnInsertion i.left).state.shape.colLen 0 ≤ s) :
    maximalFinitePrefix i = maximalUntruncatedPrefix i.toUnboundedHarmonicIndex := by
  rw [maximalFinitePrefix, ← YoungDiagram.card_eq_sum_range_rowLen _ hheight,
    (columnInsertion i.left).shape_card, YoungDiagram.card_ofPartition]
  exact min_eq_left (Nat.sub_le _ _)

theorem finiteCommonHarmonicVector_eq_normalized {n s : ℕ} (i : FiniteHarmonicIndex n s) :
    finiteCommonHarmonicVector i =
      MvPolynomial.rename (finCongr (YoungDiagram.card_ofPartition i.part))
        (adjointYoungApply (StandardYoungTableau.rowSuperstandard _).toTableau
          (normalizedOrdinaryDerivative
            (griffinWitnessRejection i.left (StandardYoungTableau.rowSuperstandard _).toTableau
              i.multiplier (maximalFinitePrefix i) (maximalFinitePrefix_le i) s)
            (griffinApolarWitness i.left (StandardYoungTableau.rowSuperstandard _).toTableau
              (maximalFinitePrefix i) (maximalFinitePrefix_le i) s))) := by
  simp only [finiteCommonHarmonicVector, normalizedOrdinaryDerivative, adjointYoungApply_smul]

theorem untruncatedCommonHarmonicVector_eq_normalized {n : ℕ} (i : UnboundedHarmonicIndex n) :
    untruncatedCommonHarmonicVector i =
      MvPolynomial.rename (finCongr (YoungDiagram.card_ofPartition i.part))
        (adjointYoungApply (StandardYoungTableau.rowSuperstandard _).toTableau
          (normalizedOrdinaryDerivative
            (untruncatedWitnessRejection i.left (StandardYoungTableau.rowSuperstandard _).toTableau
              i.multiplier (maximalUntruncatedPrefix i) (maximalUntruncatedPrefix_le i))
            (untruncatedApolarWitness i.left (StandardYoungTableau.rowSuperstandard _).toTableau
              i.multiplier (maximalUntruncatedPrefix i) (maximalUntruncatedPrefix_le i)))) := by
  simp only [untruncatedCommonHarmonicVector, untruncatedCommonData,
    normalizedOrdinaryDerivative, adjointYoungApply_smul, untruncatedApolarWitness_eq,
    untruncatedWitnessRejection, untruncatedWitnessAlpha, exteriorPart]

def commonWitnessComparisonScalar {n s : ℕ} (i : FiniteHarmonicIndex n s) : ℂ :=
  let T := (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition i.part)).toTableau
  let k := maximalUntruncatedPrefix i.toUnboundedHarmonicIndex
  let hk := maximalUntruncatedPrefix_le i.toUnboundedHarmonicIndex
  outsideWitnessComparisonScalar (griffinWitnessAlpha i.left T k hk s)
    (untruncatedWitnessRejection i.left T i.multiplier k hk)
    (witnessExteriorDifference i.left T i.multiplier k hk s)

theorem commonWitnessComparisonScalar_ne_zero {n s : ℕ} (i : FiniteHarmonicIndex n s) :
    commonWitnessComparisonScalar i ≠ 0 := outsideWitnessComparisonScalar_ne_zero _ _ _

theorem finiteCommonHarmonicVector_eq_untruncated_smul {n s : ℕ}
    (i : FiniteHarmonicIndex n s)
    (hheight : (columnInsertion i.left).state.shape.colLen 0 ≤ s) :
    finiteCommonHarmonicVector i = commonWitnessComparisonScalar i •
      untruncatedCommonHarmonicVector i.toUnboundedHarmonicIndex := by
  rw [finiteCommonHarmonicVector_eq_normalized, untruncatedCommonHarmonicVector_eq_normalized]
  have hprefix := maximalFinitePrefix_eq_untruncated i hheight
  simp_rw [hprefix]
  have hlen : i.multiplier.colLen 0 ≤ (YoungDiagram.ofPartition i.part).card -
      maximalUntruncatedPrefix i.toUnboundedHarmonicIndex := by
    have h := i.multiplier_length
    simp only [YoungDiagram.card_ofPartition, maximalUntruncatedPrefix]
    omega
  rw [normalized_finiteWitness_eq_untruncated _ _ _ _ _ s hlen i.descents_lt i.multiplier_width,
    adjointYoungApply_smul, map_smul]
  rfl

theorem finiteCommonHarmonicCopy_eq_untruncated {n s : ℕ}
    (i : FiniteHarmonicIndex n s)
    (hheight : (columnInsertion i.left).state.shape.colLen 0 ≤ s) :
    finiteCommonHarmonicCopy i = untruncatedCommonHarmonicCopy i.toUnboundedHarmonicIndex := by
  rw [finiteCommonHarmonicCopy, finiteCommonHarmonicVector_eq_untruncated_smul i hheight,
    cyclicPolynomialCopy_smul (commonWitnessComparisonScalar_ne_zero i)]
  rfl

def commonCopyBound {n : ℕ} (i : UnboundedHarmonicIndex n) : ℕ :=
  n + descentNumber i.left + i.multiplier.rowLen 0 + 1

theorem commonCopyBound_pos {n : ℕ} (i : UnboundedHarmonicIndex n) : 0 < commonCopyBound i := by
  dsimp [commonCopyBound]
  omega

theorem commonCopyBound_conditions {n s : ℕ} (i : UnboundedHarmonicIndex n)
    (h : commonCopyBound i ≤ s) :
    n ≤ s ∧ descentNumber i.left < s ∧
      i.multiplier.rowLen 0 ≤ s - descentNumber i.left - 1 := by
  dsimp [commonCopyBound] at h
  omega

def UnboundedHarmonicIndex.finiteAt {n : ℕ} (i : UnboundedHarmonicIndex n)
    (s : ℕ) (h : commonCopyBound i ≤ s) : FiniteHarmonicIndex n s where
  toUnboundedHarmonicIndex := i
  descents_lt := (commonCopyBound_conditions i h).2.1
  multiplier_width := (commonCopyBound_conditions i h).2.2

@[simp] theorem UnboundedHarmonicIndex.finiteAt_forget {n : ℕ}
    (i : UnboundedHarmonicIndex n) (s : ℕ) (h : commonCopyBound i ≤ s) :
    (i.finiteAt s h).toUnboundedHarmonicIndex = i := rfl

theorem UnboundedHarmonicIndex.finiteAt_copy {n : ℕ}
    (i : UnboundedHarmonicIndex n) (s : ℕ) (h : commonCopyBound i ≤ s) :
    finiteCommonHarmonicCopy (i.finiteAt s h) = untruncatedCommonHarmonicCopy i := by
  apply finiteCommonHarmonicCopy_eq_untruncated
  have hc : (columnInsertion i.left).state.shape.colLen 0 ≤ n :=
    (columnInsertion_height_le_card i.left).trans_eq (YoungDiagram.card_ofPartition i.part)
  exact hc.trans (commonCopyBound_conditions i h).1

set_option maxHeartbeats 800000 in
theorem untruncatedCommonHarmonicCopy_isSpecht {n : ℕ} (i : UnboundedHarmonicIndex n) :
    IsSpechtPolynomialCopy i.part (untruncatedCommonHarmonicCopy i) := by
  have h := finiteCommonHarmonicCopy_isSpecht
    (i.finiteAt (commonCopyBound i) le_rfl) (commonCopyBound_pos i)
  rw [show (i.finiteAt (commonCopyBound i) le_rfl).part = i.part from rfl,
    i.finiteAt_copy (commonCopyBound i) le_rfl] at h
  exact h

theorem untruncatedCommonHarmonicCopy_le_homogeneous {n : ℕ}
    (i : UnboundedHarmonicIndex n) :
    untruncatedCommonHarmonicCopy i ≤ homogeneousSubmodule (Fin n) ℂ i.degree := by
  rw [← i.finiteAt_copy (commonCopyBound i) le_rfl]
  exact finiteCommonHarmonicCopy_le_homogeneous _

theorem untruncatedCommonHarmonicCopies_iSupIndep {n : ℕ} :
    iSupIndep (untruncatedCommonHarmonicCopy (n := n)) := by
  rw [iSupIndep_iff_supIndep]
  intro t
  let s := t.sup commonCopyBound + 1
  have hs : 0 < s := by dsimp [s]; omega
  have hb (i : t) : commonCopyBound i.val ≤ s :=
    (Finset.le_sup (f := commonCopyBound) i.property).trans (Nat.le_succ _)
  let f : t → FiniteHarmonicIndex n s := fun i => i.val.finiteAt s (hb i)
  have hf : Function.Injective f := by
    intro i j h
    apply Subtype.ext
    exact congrArg FiniteHarmonicIndex.toUnboundedHarmonicIndex h
  have hi := (finiteCommonHarmonicCopies_iSupIndep (n := n) hs).comp hf
  have heq : (fun i : t => finiteCommonHarmonicCopy (f i)) =
      (fun i : t => untruncatedCommonHarmonicCopy i.val) := by
    funext i
    exact i.val.finiteAt_copy s (hb i)
  change iSupIndep (fun i : t => finiteCommonHarmonicCopy (f i)) at hi
  rw [heq] at hi
  exact hi.supIndep

theorem descentNumber_le_card {mu : YoungDiagram} (S : StandardYoungTableau mu) :
    descentNumber S ≤ mu.card :=
  (ascentCount_le _ _).trans (Nat.sub_le _ _)

def unboundedDegreeFiniteCode {n d : ℕ}
    (i : {i : UnboundedHarmonicIndex n // i.degree = d}) : FiniteHarmonicIndex n (n + d + 1) where
  toUnboundedHarmonicIndex := i.val
  descents_lt := by
    have h := descentNumber_le_card i.val.left
    rw [YoungDiagram.card_ofPartition] at h
    omega
  multiplier_width := by
    have hdes := descentNumber_le_card i.val.left
    rw [YoungDiagram.card_ofPartition] at hdes
    have hw := rowLen_zero_le_card i.val.multiplier
    have hd := i.property
    dsimp only [UnboundedHarmonicIndex.degree] at hd
    omega

theorem unboundedDegreeFiniteCode_injective (n d : ℕ) :
    Function.Injective (unboundedDegreeFiniteCode (n := n) (d := d)) := by
  intro i j h
  apply Subtype.ext
  exact congrArg FiniteHarmonicIndex.toUnboundedHarmonicIndex h

theorem finite_unboundedHarmonic_degree (n d : ℕ) :
    Set.Finite {i : UnboundedHarmonicIndex n | i.degree = d} := by
  letI : Finite {i : UnboundedHarmonicIndex n // i.degree = d} :=
    Finite.of_injective unboundedDegreeFiniteCode (unboundedDegreeFiniteCode_injective n d)
  exact Set.toFinite _

theorem untruncatedCommonHarmonicCopy_le {n : ℕ} (i : UnboundedHarmonicIndex n)
    (lam : YoungDiagram) (hk : lam.card ≤ n) (he : i.eligible lam hk) :
    untruncatedCommonHarmonicCopy i ≤ ordinaryHarmonics (untruncatedIdeal ℂ n lam) := by
  let s := max (commonCopyBound i) (lam.colLen 0) + 1
  have hb : commonCopyBound i ≤ s := (le_max_left _ _).trans (Nat.le_succ _)
  have hs : 0 < s := by dsimp [s]; omega
  have hheight : lam.colLen 0 ≤ s := (le_max_right _ _).trans (Nat.le_succ _)
  rw [← i.finiteAt_copy s hb]
  exact (finiteCommonHarmonicCopy_le (i.finiteAt s hb) hs lam hk hheight he).trans
    (ordinaryHarmonics_antitone le_sup_left)

end HigherSpecht
end
end CanonicalSource60

section CanonicalSource61
/- Source: HigherSpecht/UntruncatedCommonAssembly.lean -/



/-!
# Exact simultaneous harmonic assembly at arbitrary degree

Every polynomial lies in a genuine finite coordinate-power harmonic space.
At a sufficiently large power bound all named finite cyclic copies have
stabilized to the named untruncated copies.  This proves the untruncated
spanning equality from the actual finite prescribed bases, while retaining
the precise witnesses and all degrees.  The final assembly remains explicitly
conditional until the independent nonempty-index count supplies those bases.
-/

noncomputable section
open TauCeti Module MvPolynomial
open scoped Classical

namespace HigherSpecht

theorem ordinaryHarmonics_sup {n : ℕ} (I J : Ideal (PolynomialRing n ℂ)) :
    ordinaryHarmonics (I ⊔ J) = ordinaryHarmonics I ⊓ ordinaryHarmonics J := by
  ext p
  constructor
  · intro hp
    exact ⟨ordinaryHarmonics_antitone le_sup_left hp,
      ordinaryHarmonics_antitone le_sup_right hp⟩
  · rintro ⟨hI, hJ⟩ f hf
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hf
    rw [map_add, LinearMap.add_apply, hI u hu, hJ v hv, add_zero]

theorem mem_ordinaryGriffinHarmonics_of_totalDegree {n s : ℕ} {lam : YoungDiagram}
    {p : PolynomialRing n ℂ} (hp : p ∈ ordinaryHarmonics (untruncatedIdeal ℂ n lam))
    (hd : p.totalDegree < s) : p ∈ ordinaryHarmonics (griffinIdeal ℂ n lam s) := by
  have hs : 0 < s := (Nat.zero_le p.totalDegree).trans_lt hd
  rw [griffinIdeal, ordinaryHarmonics_sup]
  refine ⟨hp, ?_⟩
  rw [ordinaryHarmonics_powerIdeal_eq_restrictDegree n s hs]
  apply MvPolynomial.restrictTotalDegree_le_restrictDegree (Fin n) ℂ (s - 1)
  exact (MvPolynomial.mem_restrictTotalDegree (Fin n) (s - 1) p).mpr (by omega)

def eligibleUntruncatedCommonHarmonicSum (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Submodule ℂ (PolynomialRing n ℂ) :=
  ⨆ i : {i : UnboundedHarmonicIndex n // i.eligible lam hk}, untruncatedCommonHarmonicCopy i.val

theorem eligibleUntruncatedCommonHarmonicSum_le (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) :
    eligibleUntruncatedCommonHarmonicSum n lam hk ≤ ordinaryHarmonics (untruncatedIdeal ℂ n lam) := by
  apply iSup_le
  intro i
  exact untruncatedCommonHarmonicCopy_le i.val lam hk i.property

theorem finiteEligibleSum_le_untruncated {n s : ℕ} (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hns : n ≤ s) :
    eligibleCommonHarmonicSum n s lam hk ≤ eligibleUntruncatedCommonHarmonicSum n lam hk := by
  apply iSup_le
  intro i
  have hheight : (columnInsertion i.val.left).state.shape.colLen 0 ≤ s := by
    have h : (columnInsertion i.val.left).state.shape.colLen 0 ≤ n :=
      (columnInsertion_height_le_card i.val.left).trans_eq
        (YoungDiagram.card_ofPartition i.val.part)
    exact h.trans hns
  rw [finiteCommonHarmonicCopy_eq_untruncated i.val hheight]
  exact le_iSup (fun j : {j : UnboundedHarmonicIndex n // j.eligible lam hk} =>
    untruncatedCommonHarmonicCopy j.val) ⟨i.val.toUnboundedHarmonicIndex, i.property⟩

/-- Exact transfer, with its remaining finite-basis dependency displayed. -/
theorem untruncatedCommonHarmonic_decomposition_of_finite_bases
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hb : ∀ s : ℕ, 0 < s → lam.colLen 0 ≤ s →
      IsSpecifiedBasis (R := ℂ) (griffinFamily ℂ n lam hk s)) :
    ordinaryHarmonics (untruncatedIdeal ℂ n lam) =
      eligibleUntruncatedCommonHarmonicSum n lam hk := by
  apply le_antisymm
  · intro p hp
    let s := p.totalDegree + n + lam.colLen 0 + 1
    have hs : 0 < s := by dsimp [s]; omega
    have hheight : lam.colLen 0 ≤ s := by dsimp [s]; omega
    have hns : n ≤ s := by dsimp [s]; omega
    have hds : p.totalDegree < s := by dsimp [s]; omega
    have hfinite := mem_ordinaryGriffinHarmonics_of_totalDegree hp hds
    rw [finiteCommonHarmonic_decomposition_of_specifiedBasis n s lam hk hs hheight
      (hb s hs hheight)] at hfinite
    exact finiteEligibleSum_le_untruncated lam hk hns hfinite
  · exact eligibleUntruncatedCommonHarmonicSum_le n lam hk

theorem untruncatedCommonHarmonic_decomposition_empty (n : ℕ) :
    ordinaryHarmonics (untruncatedIdeal ℂ n ⊥) =
      eligibleUntruncatedCommonHarmonicSum n ⊥ (by simp [YoungDiagram.card]) :=
  untruncatedCommonHarmonic_decomposition_of_finite_bases n ⊥
    (by simp [YoungDiagram.card])
    (fun s hs _ => griffin_empty_specifiedBasis ℂ n s hs)

theorem untruncatedCommonHarmonic_structure (n : ℕ) :
    (∀ i : UnboundedHarmonicIndex n,
      IsSpechtPolynomialCopy i.part (untruncatedCommonHarmonicCopy i) ∧
      untruncatedCommonHarmonicCopy i ≤ homogeneousSubmodule (Fin n) ℂ i.degree) ∧
    iSupIndep (untruncatedCommonHarmonicCopy (n := n)) ∧
    (∀ d : ℕ, Set.Finite {i : UnboundedHarmonicIndex n | i.degree = d}) ∧
    ∀ (lam : YoungDiagram) (hk : lam.card ≤ n),
      eligibleUntruncatedCommonHarmonicSum n lam hk ≤
        ordinaryHarmonics (untruncatedIdeal ℂ n lam) :=
  ⟨fun i => ⟨untruncatedCommonHarmonicCopy_isSpecht i,
    untruncatedCommonHarmonicCopy_le_homogeneous i⟩,
    untruncatedCommonHarmonicCopies_iSupIndep, finite_unboundedHarmonic_degree n,
    fun lam hk => eligibleUntruncatedCommonHarmonicSum_le n lam hk⟩

theorem finite_simultaneous_target_of_specified_bases
    (hb : ∀ (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ),
      0 < s → lam.colLen 0 ≤ s → IsSpecifiedBasis (R := ℂ) (griffinFamily ℂ n lam hk s)) :
    FiniteSimultaneousHarmonicTarget := by
  intro n s hn hs
  obtain ⟨hshape, hind, hmem⟩ := finiteCommonHarmonic_structure n s hs
  refine ⟨hshape, hind, ?_⟩
  intro lam hk hheight
  exact finiteCommonHarmonic_decomposition_of_specifiedBasis n s lam hk hs hheight
    (hb n lam hk s hs hheight)

theorem untruncated_simultaneous_target_of_specified_bases
    (hb : ∀ (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ),
      0 < s → lam.colLen 0 ≤ s → IsSpecifiedBasis (R := ℂ) (griffinFamily ℂ n lam hk s)) :
    UntruncatedSimultaneousHarmonicTarget := by
  intro n
  obtain ⟨hshape, hind, hfinite, hmem⟩ := untruncatedCommonHarmonic_structure n
  refine ⟨hshape, hind, hfinite, ?_⟩
  intro lam hk
  exact untruncatedCommonHarmonic_decomposition_of_finite_bases n lam hk (hb n lam hk)

end HigherSpecht
end
end CanonicalSource61

section CanonicalSource62
/- Source: HigherSpecht/PrincipalBases.lean -/



/-!
# The prescribed bases and simultaneous harmonic endpoints

The finite count is supplied by the actual battery injection.  The general
degreewise and parameter-ring assemblies are instantiated with that result;
no counting or spanning premise is retained in these endpoints.  At full
prefix length, the literal prefix tableau is the original tableau.  The
Springer specialization therefore uses exactly the manuscript's index and
polynomial family, including the empty diagram.

These declarations remain source candidates until the complete dependency
closure passes compilation and the independent statement and axiom audits.
The numerical rank, Frobenius series, and commutative-algebra conclusions of
Theorem 6.1 are separate statements, not consequences asserted by a name here.
-/

noncomputable section

open TauCeti Module MvPolynomial

namespace HigherSpecht

theorem standardTableau_heq_of_shape_eq {mu nu : YoungDiagram}
    (hshape : mu = nu) (S : StandardYoungTableau mu) (T : StandardYoungTableau nu)
    (hentry : ∀ c : ↥mu.cells, (S c).val =
      (T ⟨c.val, by simpa only [hshape] using c.property⟩).val) : HEq S T := by
  subst nu
  apply heq_of_eq
  apply StandardYoungTableau.ext
  intro c
  exact Fin.ext (hentry c)

theorem catDominates_of_heq {mu nu : YoungDiagram}
    {S : StandardYoungTableau mu} {T : StandardYoungTableau nu}
    (hshape : mu = nu) (h : HEq S T) (lam : YoungDiagram) :
    CatDominates S lam ↔ CatDominates T lam := by
  subst nu
  cases eq_of_heq h
  rfl

theorem prefixTableau_full_heq {mu : YoungDiagram} (S : StandardYoungTableau mu) :
    HEq (prefixTableau S mu.card le_rfl) S := by
  apply standardTableau_heq_of_shape_eq (prefixShape_full S)
  intro c
  exact prefixTableau_apply_val S mu.card le_rfl c

@[simp] theorem catDominates_prefixTableau_full {mu : YoungDiagram}
    (S : StandardYoungTableau mu) (lam : YoungDiagram) :
    CatDominates (prefixTableau S mu.card le_rfl) lam ↔ CatDominates S lam :=
  catDominates_of_heq (prefixShape_full S) (prefixTableau_full_heq S) lam

@[simp] theorem prefixEligible_full (lam : YoungDiagram) (P : StandardPair lam.card) :
    prefixEligible lam le_rfl P ↔ CatDominates P.left lam := by
  have transport (k : ℕ) (hk : k ≤ P.shape.card) (he : k = P.shape.card) :
      CatDominates (prefixTableau P.left k hk) lam ↔ CatDominates P.left lam := by
    subst k
    exact catDominates_prefixTableau_full P.left lam
  exact transport lam.card P.card_eq.symm.le P.card_eq.symm

/-- The exact quantified basis assertion of Theorem 4.1. -/
theorem theorem_4_1 (K : Type*) [Field K] [CharZero K] : GriffinBasisTarget K := by
  intro n lam hk s hlam hheight
  exact griffin_specifiedBasis K n lam hk s
    ((height_pos_of_card_pos lam hlam).trans_le hheight) hheight

def untruncatedPrescribedVectorBasis (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Basis (UntruncatedVectorIndex n lam hk) K (UntruncatedRing K n lam) :=
  untruncatedVectorBasisOfFiniteBases K n lam hk
    (fun s hs hheight => griffin_specifiedBasis K n lam hk s hs hheight)

@[simp] theorem untruncatedPrescribedVectorBasis_apply
    (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (i : UntruncatedVectorIndex n lam hk) :
    untruncatedPrescribedVectorBasis K n lam hk i =
      untruncatedVectorFamily K n lam hk i :=
  untruncatedVectorBasisOfFiniteBases_apply K n lam hk _ i

theorem untruncated_vector_basis_target (K : Type*) [Field K] [CharZero K] :
    UntruncatedVectorBasisTarget K := by
  intro n lam hk
  exact ⟨untruncatedPrescribedVectorBasis K n lam hk,
    untruncatedPrescribedVectorBasis_apply K n lam hk⟩

theorem diagram_eq_bot_of_height_zero {eta : YoungDiagram} (h : eta.colLen 0 = 0) :
    eta = ⊥ := by
  apply le_antisymm
  · intro c hc
    have hc' := YoungDiagram.lt_colLen_zero_of_mem hc
    rw [h] at hc'
    exact (Nat.not_lt_zero _ hc').elim
  · exact bot_le

def springerUntruncatedVectorIndexEquiv (lam : YoungDiagram) :
    SpringerIndex lam ≃ UntruncatedVectorIndex lam.card lam le_rfl where
  toFun i :=
    { base := ⟨i.val, (prefixEligible_full lam i.val).mpr i.property⟩
      multiplier := ⊥
      multiplier_length := by simp }
  invFun i := ⟨i.base.val, (prefixEligible_full lam i.base.val).mp i.base.property⟩
  left_inv i := Subtype.ext rfl
  right_inv i := by
    apply untruncatedVectorIndex_ext
    · rfl
    · exact (diagram_eq_bot_of_height_zero (by
        have h := i.multiplier_length
        simpa only [Nat.sub_self, Nat.le_zero] using h)).symm

@[simp] theorem springerUntruncatedVectorIndexEquiv_family
    (K : Type*) [CommRing K] (lam : YoungDiagram) (i : SpringerIndex lam) :
    untruncatedVectorFamily K lam.card lam le_rfl
        (springerUntruncatedVectorIndexEquiv lam i) = springerFamily K lam i := by
  simp only [untruncatedVectorFamily, springerUntruncatedVectorIndexEquiv,
    Nat.sub_self, elementaryMultiplier, Finset.range_zero, Finset.prod_empty,
    mul_one, springerFamily, springerIdeal] <;> rfl

def springerPrescribedBasis (K : Type*) [Field K] [CharZero K] (lam : YoungDiagram) :
    Basis (SpringerIndex lam) K (SpringerRing K lam) :=
  (untruncatedPrescribedVectorBasis K lam.card lam le_rfl).reindex
    (springerUntruncatedVectorIndexEquiv lam).symm

@[simp] theorem springerPrescribedBasis_apply (K : Type*) [Field K] [CharZero K]
    (lam : YoungDiagram) (i : SpringerIndex lam) :
    springerPrescribedBasis K lam i = springerFamily K lam i := by
  change ((untruncatedPrescribedVectorBasis K lam.card lam le_rfl).reindex
    (springerUntruncatedVectorIndexEquiv lam).symm) i =
      (springerFamily K lam i : UntruncatedRing K lam.card lam)
  rw [Basis.reindex_apply, untruncatedPrescribedVectorBasis_apply]
  exact springerUntruncatedVectorIndexEquiv_family K lam i

/-- The original prescribed Springer family, with no prefix reformulation
left in its statement. -/
theorem springer_basis_target (K : Type*) [Field K] [CharZero K] :
    SpringerBasisTarget K := by
  intro lam
  exact ⟨springerPrescribedBasis K lam, springerPrescribedBasis_apply K lam⟩

def untruncatedPrescribedParameterBasis (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Basis (UntruncatedIndex n lam hk) (ElementaryParameterRing K n lam)
      (UntruncatedRing K n lam) :=
  untruncatedParameterBasisOfFiniteBases K n lam hk
    (fun s hs hheight => griffin_specifiedBasis K n lam hk s hs hheight)

@[simp] theorem untruncatedPrescribedParameterBasis_apply
    (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (i : UntruncatedIndex n lam hk) :
    untruncatedPrescribedParameterBasis K n lam hk i =
      untruncatedFamily K n lam hk i :=
  untruncatedParameterBasisOfFiniteBases_apply K n lam hk _ i

/-- The free-basis part of Theorem 6.1 over the actual elementary-parameter
action, not an arbitrary polynomial-ring module structure. -/
theorem untruncated_specified_parameter_basis
    (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    IsSpecifiedBasis (R := ElementaryParameterRing K n lam)
      (untruncatedFamily K n lam hk) :=
  ⟨untruncatedPrescribedParameterBasis K n lam hk,
    untruncatedPrescribedParameterBasis_apply K n lam hk⟩

theorem untruncated_finite_parameters (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Module.Finite (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) := by
  classical
  letI : Fintype (UntruncatedIndex n lam hk) := Fintype.ofFinite _
  exact Module.Finite.of_basis (untruncatedPrescribedParameterBasis K n lam hk)

theorem untruncated_parameter_rank_eq_index (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Module.finrank (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) =
      Nat.card (UntruncatedIndex n lam hk) := by
  classical
  letI : Fintype (UntruncatedIndex n lam hk) := Fintype.ofFinite _
  rw [Module.finrank_eq_card_basis (untruncatedPrescribedParameterBasis K n lam hk)]
  exact Nat.card_eq_fintype_card.symm

/-- All the named common finite harmonic copies simultaneously, with their
actual adjoint-Young vectors, factorial factors, and full ideal equalities. -/
theorem theorem_5_2 : FiniteSimultaneousHarmonicTarget :=
  finite_simultaneous_target_of_specified_bases
    (fun n lam hk s hs hheight => griffin_specifiedBasis ℂ n lam hk s hs hheight)

/-- The exact locally finite untruncated common-copy decomposition. -/
theorem theorem_6_6 : UntruncatedSimultaneousHarmonicTarget :=
  untruncated_simultaneous_target_of_specified_bases
    (fun n lam hk s hs hheight => griffin_specifiedBasis ℂ n lam hk s hs hheight)

end HigherSpecht
end
end CanonicalSource62
