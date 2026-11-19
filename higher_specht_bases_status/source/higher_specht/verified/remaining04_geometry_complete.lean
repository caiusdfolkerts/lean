module

public import higher_specht.verified.remaining03_complete
public import Mathlib.Data.Prod.Lex
public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.RingTheory.Polynomial.HilbertPoly
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Descent
public import tau_ceti.ring_theory.etale.discriminant
public import Mathlib.RingTheory.Binomial
public import tau_ceti.representation_theory.symmetric.relabel
public import Mathlib.Data.Finsupp.Order
public import tau_ceti.representation_theory.irreducible
public import tau_ceti.representation_theory.symmetric.specht.complex
public import tau_ceti.representation_theory.symmetric.specht.decomposition
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import tau_ceti.representation_theory.subrepresentation

/- Generated ordinary source-preserving proof stage. See audit/staged_specht_remaining/Remaining04GeometryComplete/manifest.json. -/

@[expose] public section

section CanonicalSource0
/- Source: HigherSpecht/GriffinExpressionCharacters.lean -/



/-!
# The actual graded Frobenius character of every ideal expression

The graded piece is the image of genuinely homogeneous polynomials in the
literal quotient.  Its original prescribed basis is grouped into actual
Specht intertwiners.  Taking traces and applying the existing Frobenius
characteristic gives the Schur sum, without defining the character from the
desired index set.
-/

noncomputable section
open TauCeti TauCeti.YoungTableau Module MvPolynomial
open scoped Classical TensorProduct

namespace HigherSpecht

def polynomialComplexBaseChangeEquiv (n : ℕ) :
    (Representation.baseChange ℂ (polynomialRepresentation ℚ n)).Equiv
      (polynomialRepresentation ℂ n) := by
  refine Representation.Equiv.mk (MvPolynomial.algebraTensorAlgEquiv ℚ ℂ).toLinearEquiv ?_
  intro g
  apply TensorProduct.AlgebraTensorModule.ext (R := ℚ)
  intro c p
  simp only [LinearMap.comp_apply, Representation.baseChange_apply,
    LinearMap.baseChange_tmul, AlgEquiv.toLinearEquiv_toLinearMap,
    AlgEquiv.toLinearMap_apply, LinearEquiv.coe_coe, AlgEquiv.coe_toLinearEquiv,
    AlgEquiv.toLinearEquiv_apply,
    MvPolynomial.algebraTensorAlgEquiv_tmul, polynomialRepresentation_apply,
    MvPolynomial.map_rename, map_smul]

def finiteMasterRationalIntertwiner {n s : ℕ} (i : FiniteHarmonicIndex n s) :
    Representation.IntertwiningMap (spechtModule i.part).ρ (polynomialRepresentation ℚ n) :=
  (symmetricMultiplicationIntertwiner (elementaryMultiplier n n i.multiplier.rowLen)
    (elementaryMultiplier_isSymmetric n n i.multiplier.rowLen)).comp
    (partitionHigherSpechtIntertwiner i.part i.left)

theorem finiteMasterRationalIntertwiner_standard {n s : ℕ}
    (i : FiniteHarmonicIndex n s)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) :
    finiteMasterRationalIntertwiner i (spechtModuleStandardBasis i.part T) =
      finiteMasterPolynomial (R := ℚ) i T := by
  change partitionHigherSpechtIntertwiner i.part i.left (spechtModuleStandardBasis i.part T) *
      elementaryMultiplier n n i.multiplier.rowLen =
    rename (finCongr (YoungDiagram.card_ofPartition i.part))
      (higherSpechtPolynomial i.left T) * elementaryMultiplier n n i.multiplier.rowLen
  rw [partitionHigherSpechtIntertwiner_standardBasis]

private theorem finiteMaster_cast_intertwiner_basis_apply
    {G ι M : Type*} [Monoid G] [AddCommGroup M] [Module ℂ M]
    (rho : Representation ℂ G M) {A B : FDRep ℂ G} (h : A = B)
    (f : Representation.IntertwiningMap A.ρ rho) (b : Basis ι ℂ A) (i : ι) :
    (cast (congrArg (fun V : FDRep ℂ G => Representation.IntertwiningMap V.ρ rho) h) f)
      ((cast (congrArg (fun V : FDRep ℂ G => Basis ι ℂ V) h) b) i) = f (b i) := by
  cases h
  rfl

def finiteMasterComplexIntertwiner {n s : ℕ} (i : FiniteHarmonicIndex n s) :
    Representation.IntertwiningMap (spechtModuleℂ i.part).ρ (polynomialRepresentation ℂ n) :=
  cast (congrArg (fun V : FDRep ℂ (Equiv.Perm (Fin n)) =>
    Representation.IntertwiningMap V.ρ (polynomialRepresentation ℂ n))
    (spechtModuleℂ_def i.part).symm)
    ((polynomialComplexBaseChangeEquiv n).toIntertwiningMap.comp
      ((finiteMasterRationalIntertwiner i).baseChange ℂ))

theorem finiteMasterComplexIntertwiner_standard {n s : ℕ}
    (i : FiniteHarmonicIndex n s)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) :
    finiteMasterComplexIntertwiner i (complexSpechtStandardBasis i.part T) =
      finiteMasterPolynomial (R := ℂ) i T := by
  unfold finiteMasterComplexIntertwiner complexSpechtStandardBasis
  rw [finiteMaster_cast_intertwiner_basis_apply (polynomialRepresentation ℂ n)
    (spechtModuleℂ_def i.part).symm]
  change MvPolynomial.algebraTensorAlgEquiv ℚ ℂ
    ((finiteMasterRationalIntertwiner i).baseChange ℂ
      ((spechtModuleStandardBasis i.part).baseChange ℂ T)) = _
  rw [Basis.baseChange_apply, Representation.IntertwiningMap.baseChange_tmul]
  refine (congrArg (fun p : PolynomialRing n ℚ =>
    MvPolynomial.algebraTensorAlgEquiv ℚ ℂ ((1 : ℂ) ⊗ₜ[ℚ] p))
      (finiteMasterRationalIntertwiner_standard i T)).trans ?_
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul]
  simp only [one_smul, finiteMasterPolynomial, map_mul, MvPolynomial.map_rename,
    map_higherSpechtPolynomial, map_elementaryMultiplier]

namespace GriffinIdealExpression

variable {n s : ℕ} (e : GriffinIdealExpression n s)

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ideal_isHomogeneous (R : Type*) [CommRing R] :
    (e.ideal R).IsHomogeneous (homogeneousSubmodule (Fin n) R) := by
  induction e with
  | atom a =>
      apply (untruncatedIdeal_isHomogeneous a.card_le).sup
      apply Ideal.homogeneous_span
      rintro p ⟨j, rfl⟩
      exact ⟨s, by simpa only [MvPolynomial.mem_homogeneousSubmodule, one_mul] using (MvPolynomial.isHomogeneous_X R j).pow s⟩
  | sum e f he hf => exact he.sup hf
  | intersection e f he hf => exact he.inf hf

def gradedPiece (d : ℕ) : Subrepresentation (quotientRepresentation (e.ideal ℂ)
    (e.permutationStable ℂ)) :=
  homogeneousQuotientSubrepresentation (e.ideal ℂ) (e.permutationStable ℂ) d

abbrev DegreeCopyIndex (d : ℕ) :=
  {i : FiniteHarmonicIndex n s // i ∈ e.eligible ∧ i.toUnboundedHarmonicIndex.degree = d}

def degreeVectorEquiv (d : ℕ) :
    (Σ i : e.DegreeCopyIndex d, StandardYoungTableau (YoungDiagram.ofPartition i.val.part)) ≃
      {z : e.VectorIndex // z.1.val.toUnboundedHarmonicIndex.degree = d} where
  toFun z := ⟨⟨⟨z.1.val, z.1.property.1⟩, z.2⟩, z.1.property.2⟩
  invFun z := ⟨⟨z.val.1.val, z.val.1.property, z.property⟩, z.val.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def degreeCopyBasis (hs : 0 < s) (d : ℕ) :
    Basis (Σ i : e.DegreeCopyIndex d, StandardYoungTableau (YoungDiagram.ofPartition i.val.part))
      ℂ (e.gradedPiece d).toSubmodule :=
  (homogeneousQuotientBasis (e.ideal ℂ) (e.ideal_isHomogeneous ℂ)
    (e.prescribedBasis hs) (e.polynomial ℂ)
    (fun z => z.1.val.toUnboundedHarmonicIndex.degree)
    (fun z => finiteMasterPolynomial_isHomogeneous z.1.val z.2)
    (e.prescribedBasis_apply hs) d).reindex (e.degreeVectorEquiv d).symm

theorem degreeCopyBasis_apply (hs : 0 < s) (d : ℕ)
    (i : e.DegreeCopyIndex d) (T : StandardYoungTableau (YoungDiagram.ofPartition i.val.part)) :
    (e.degreeCopyBasis hs d ⟨i, T⟩ : PolynomialRing n ℂ ⧸ e.ideal ℂ) =
      Ideal.Quotient.mk (e.ideal ℂ) (finiteMasterPolynomial i.val T) := by
  let b := homogeneousQuotientBasis (e.ideal ℂ) (e.ideal_isHomogeneous ℂ)
    (e.prescribedBasis hs) (e.polynomial ℂ) (fun z => z.1.val.toUnboundedHarmonicIndex.degree)
    (fun z => finiteMasterPolynomial_isHomogeneous z.1.val z.2)
    (e.prescribedBasis_apply hs) d
  let E := e.degreeVectorEquiv d
  have h := b.reindex_apply E.symm ⟨i, T⟩
  exact (congrArg
    (fun z : homogeneousQuotientPiece (e.ideal ℂ) d =>
      (z : PolynomialRing n ℂ ⧸ e.ideal ℂ)) h).trans
    ((homogeneousQuotientBasis_apply (e.ideal ℂ) (e.ideal_isHomogeneous ℂ)
      (e.prescribedBasis hs) (e.polynomial ℂ) (fun z => z.1.val.toUnboundedHarmonicIndex.degree)
      (fun z => finiteMasterPolynomial_isHomogeneous z.1.val z.2)
      (e.prescribedBasis_apply hs) d (E ⟨i, T⟩)).trans
        (e.prescribedBasis_apply hs (E ⟨i, T⟩).val))

def complexIntertwiner (i : FiniteHarmonicIndex n s) :
    Representation.IntertwiningMap (spechtModuleℂ i.part).ρ
      (quotientRepresentation (e.ideal ℂ) (e.permutationStable ℂ)) :=
  (quotientProjectionIntertwiner (e.ideal ℂ) (e.permutationStable ℂ)).comp
    (finiteMasterComplexIntertwiner i)

theorem complexIntertwiner_standard (i : FiniteHarmonicIndex n s)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) :
    e.complexIntertwiner i (complexSpechtStandardBasis i.part T) =
      Ideal.Quotient.mk (e.ideal ℂ) (finiteMasterPolynomial i T) := by
  change Ideal.Quotient.mk (e.ideal ℂ)
    (finiteMasterComplexIntertwiner i (complexSpechtStandardBasis i.part T)) = _
  rw [finiteMasterComplexIntertwiner_standard]

theorem complexIntertwiner_mem_degree (hs : 0 < s) (d : ℕ)
    (i : e.DegreeCopyIndex d) (v : spechtModuleℂ i.val.part) :
    e.complexIntertwiner i.val v ∈ (e.gradedPiece d).toSubmodule := by
  rw [← (complexSpechtStandardBasis i.val.part).sum_repr v, map_sum]
  apply Submodule.sum_mem
  intro T _
  rw [map_smul, e.complexIntertwiner_standard]
  apply Submodule.smul_mem
  rw [← e.degreeCopyBasis_apply hs d i T]
  exact (e.degreeCopyBasis hs d ⟨i, T⟩).property

def degreeSpechtMap (hs : 0 < s) (d : ℕ) (i : e.DegreeCopyIndex d) :
    Representation.IntertwiningMap (spechtModuleℂ i.val.part).ρ (e.gradedPiece d).toRepresentation :=
  (e.complexIntertwiner i.val).codRestrict (e.gradedPiece d)
    (e.complexIntertwiner_mem_degree hs d i)

theorem degreeSpechtMap_standard (hs : 0 < s) (d : ℕ)
    (i : e.DegreeCopyIndex d) (T : StandardYoungTableau (YoungDiagram.ofPartition i.val.part)) :
    e.degreeSpechtMap hs d i (complexSpechtStandardBasis i.val.part T) =
      e.degreeCopyBasis hs d ⟨i, T⟩ := by
  apply Subtype.ext
  rw [e.degreeCopyBasis_apply, degreeSpechtMap,
    Representation.IntertwiningMap.codRestrict_apply_coe]
  exact e.complexIntertwiner_standard i.val T

theorem character_gradedPiece (hs : 0 < s) (d : ℕ) (g : Equiv.Perm (Fin n)) :
    (e.gradedPiece d).toRepresentation.character g =
      ∑ i : e.DegreeCopyIndex d, Representation.character (spechtModuleℂ i.val.part).ρ g :=
  character_eq_sum_of_intertwining_basis
    (fun i : e.DegreeCopyIndex d => (spechtModuleℂ i.val.part).ρ)
    (e.gradedPiece d).toRepresentation (fun i => complexSpechtStandardBasis i.val.part)
    (e.degreeCopyBasis hs d) (e.degreeSpechtMap hs d) (e.degreeSpechtMap_standard hs d) g

def frobeniusCoefficient (hs : 0 < s) (d : ℕ) : MvPolynomial (Fin n) ℂ :=
  letI := Module.Finite.of_basis (e.degreeCopyBasis hs d)
  (frobeniusCharacteristic n n le_rfl
    (ClassFunction.ofCharacter (e.gradedPiece d).toRepresentation) :
      symmetricHomogeneousSubmodule (Fin n) ℂ n)

theorem frobeniusCoefficient_eq (hs : 0 < s) (d : ℕ) :
    e.frobeniusCoefficient hs d =
      ∑ i : e.DegreeCopyIndex d, schurPoly (Fin n) ℂ i.val.part := by
  letI := Module.Finite.of_basis (e.degreeCopyBasis hs d)
  have hc : ClassFunction.ofCharacter (e.gradedPiece d).toRepresentation =
      ∑ i : e.DegreeCopyIndex d, ClassFunction.ofCharacter (spechtModuleℂ i.val.part).ρ := by
    apply Subtype.ext
    funext g
    simp only [Submodule.coe_sum, ClassFunction.ofCharacter_apply, Finset.sum_apply]
    exact e.character_gradedPiece hs d g
  simp only [frobeniusCoefficient, hc, map_sum, Submodule.coe_sum,
    frobeniusCharacteristic_spechtCharacter]

def frobeniusSeries (hs : 0 < s) : PowerSeries (MvPolynomial (Fin n) ℂ) :=
  PowerSeries.mk (e.frobeniusCoefficient hs)

theorem corollary_5_3_frobenius (hs : 0 < s) :
    e.frobeniusSeries hs =
      ∑ i : {i : FiniteHarmonicIndex n s // i ∈ e.eligible},
        PowerSeries.monomial i.val.toUnboundedHarmonicIndex.degree
          (schurPoly (Fin n) ℂ i.val.part) := by
  apply PowerSeries.ext
  intro d
  rw [frobeniusSeries, PowerSeries.coeff_mk, e.frobeniusCoefficient_eq]
  simp only [map_sum, PowerSeries.coeff_monomial]
  let he : e.DegreeCopyIndex d ≃
      {i : {i : FiniteHarmonicIndex n s // i ∈ e.eligible} //
        i.val.toUnboundedHarmonicIndex.degree = d} :=
    { toFun i := ⟨⟨i.val, i.property.1⟩, i.property.2⟩
      invFun i := ⟨i.val.val, i.val.property, i.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [← Equiv.sum_comp he.symm
    (fun i : e.DegreeCopyIndex d => schurPoly (Fin n) ℂ i.val.part)]
  simp only [he]
  have hfilter :
      (∑ i : {i : FiniteHarmonicIndex n s // i ∈ e.eligible},
        if d = i.val.toUnboundedHarmonicIndex.degree then schurPoly (Fin n) ℂ i.val.part else 0) =
      ∑ i ∈ Finset.univ.filter
          (fun i : {i : FiniteHarmonicIndex n s // i ∈ e.eligible} =>
            i.val.toUnboundedHarmonicIndex.degree = d), schurPoly (Fin n) ℂ i.val.part := by
    simp only [Finset.sum_filter, eq_comm]
  rw [hfilter]
  exact (Finset.sum_subtype
    (p := fun i : {i : FiniteHarmonicIndex n s // i ∈ e.eligible} =>
      i.val.toUnboundedHarmonicIndex.degree = d)
    (Finset.univ.filter (fun i : {i : FiniteHarmonicIndex n s // i ∈ e.eligible} =>
      i.val.toUnboundedHarmonicIndex.degree = d)) (by simp)
    (fun i : {i : FiniteHarmonicIndex n s // i ∈ e.eligible} =>
      schurPoly (Fin n) ℂ i.val.part)).symm

end GriffinIdealExpression
end HigherSpecht
end
end CanonicalSource0

section CanonicalSource1
/- Source: HigherSpecht/UntruncatedIdealExpressions.lean -/



/-!
# Literal finite expressions in untruncated Griffin ideals

Truncation is performed at every leaf of the expression.  Its compatibility
with sums and intersections below the truncation degree is proved using
homogeneous components.  No distributivity of arbitrary ideals is assumed.
-/

noncomputable section
open TauCeti Module MvPolynomial
open scoped Classical

namespace HigherSpecht

structure BoundedUntruncatedShape (n : ℕ) where
  diagram : YoungDiagram
  card_le : diagram.card ≤ n

inductive UntruncatedIdealExpression (n : ℕ) where
  | atom : BoundedUntruncatedShape n → UntruncatedIdealExpression n
  | sum : UntruncatedIdealExpression n → UntruncatedIdealExpression n →
      UntruncatedIdealExpression n
  | intersection : UntruncatedIdealExpression n → UntruncatedIdealExpression n →
      UntruncatedIdealExpression n

namespace UntruncatedIdealExpression

variable {n : ℕ}

def ideal (R : Type*) [CommRing R] : UntruncatedIdealExpression n →
    Ideal (PolynomialRing n R)
  | .atom a => untruncatedIdeal R n a.diagram
  | .sum e f => e.ideal R ⊔ f.ideal R
  | .intersection e f => e.ideal R ⊓ f.ideal R

def eligible : UntruncatedIdealExpression n → Set (UnboundedHarmonicIndex n)
  | .atom a => {i | i.eligible a.diagram a.card_le}
  | .sum e f => e.eligible ∩ f.eligible
  | .intersection e f => e.eligible ∪ f.eligible

def truncate (e : UntruncatedIdealExpression n) (s : ℕ) (hns : n ≤ s) :
    GriffinIdealExpression n s :=
  match e with
  | .atom a => .atom ⟨a.diagram, a.card_le,
      (colLen_zero_le_card a.diagram).trans (a.card_le.trans hns)⟩
  | .sum e f => .sum (e.truncate s hns) (f.truncate s hns)
  | .intersection e f => .intersection (e.truncate s hns) (f.truncate s hns)

@[simp] theorem truncate_eligible (e : UntruncatedIdealExpression n)
    (s : ℕ) (hns : n ≤ s) (i : FiniteHarmonicIndex n s) :
    i ∈ (e.truncate s hns).eligible ↔ i.toUnboundedHarmonicIndex ∈ e.eligible := by
  induction e with
  | atom a => rfl
  | sum e f he hf => exact and_congr he hf
  | intersection e f he hf => exact or_congr he hf

theorem ideal_le_truncate (R : Type*) [CommRing R]
    (e : UntruncatedIdealExpression n) (s : ℕ) (hns : n ≤ s) :
    e.ideal R ≤ (e.truncate s hns).ideal R := by
  induction e with
  | atom a => exact le_sup_left
  | sum e f he hf => exact sup_le_sup he hf
  | intersection e f he hf => exact inf_le_inf he hf

theorem permutationStable (R : Type*) [CommRing R]
    (e : UntruncatedIdealExpression n) : PermutationStable (e.ideal R) := by
  induction e with
  | atom a => exact permutationStable_untruncatedIdeal a.diagram
  | sum e f he hf => exact he.sup hf
  | intersection e f he hf => exact he.inf hf

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ideal_isHomogeneous (R : Type*) [CommRing R]
    (e : UntruncatedIdealExpression n) :
    (e.ideal R).IsHomogeneous (homogeneousSubmodule (Fin n) R) := by
  induction e with
  | atom a => exact untruncatedIdeal_isHomogeneous a.card_le
  | sum e f he hf => exact he.sup hf
  | intersection e f he hf => exact he.inf hf

theorem homogeneousComponent_truncate_mem (R : Type*) [CommRing R]
    (e : UntruncatedIdealExpression n) (s d : ℕ) (hns : n ≤ s) (hd : d < s)
    {p : PolynomialRing n R} (hp : p ∈ (e.truncate s hns).ideal R) :
    homogeneousComponent d p ∈ e.ideal R := by
  induction e generalizing p with
  | atom a => exact homogeneousComponent_griffin_mem_untruncated a.card_le hp hd
  | sum e f he hf =>
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hp
      rw [map_add]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (he hu))
        (Submodule.mem_sup_right (hf hv))
  | intersection e f he hf => exact ⟨he hp.1, hf hp.2⟩

theorem homogeneous_mem_truncate_iff (R : Type*) [CommRing R]
    (e : UntruncatedIdealExpression n) (s d : ℕ) (hns : n ≤ s) (hd : d < s)
    {p : PolynomialRing n R} (hp : p.IsHomogeneous d) :
    p ∈ (e.truncate s hns).ideal R ↔ p ∈ e.ideal R := by
  constructor
  · intro h
    simpa only [homogeneousComponent_eq_self hp] using
      e.homogeneousComponent_truncate_mem R s d hns hd h
  · intro hp
    exact e.ideal_le_truncate R s hns hp

theorem ideal_eq_of_eligible_eq (e f : UntruncatedIdealExpression n)
    (h : e.eligible = f.eligible) : e.ideal ℂ = f.ideal ℂ := by
  have hfinite (s : ℕ) (hns : n ≤ s) (hs : 0 < s) :
      (e.truncate s hns).ideal ℂ = (f.truncate s hns).ideal ℂ := by
    apply GriffinIdealExpression.ideal_eq_of_eligible_eq _ _ hs
    ext i
    rw [e.truncate_eligible, f.truncate_eligible, h]
  ext p
  rw [MvPolynomial.mem_iff_homogeneousComponent_mem (e.ideal_isHomogeneous ℂ),
    MvPolynomial.mem_iff_homogeneousComponent_mem (f.ideal_isHomogeneous ℂ)]
  apply forall_congr'
  intro d
  let s := n + d + 1
  have hns : n ≤ s := by dsimp [s]; omega
  have hd : d < s := by dsimp [s]; omega
  have hs : 0 < s := by dsimp [s]; omega
  rw [← e.homogeneous_mem_truncate_iff ℂ s d hns hd (homogeneousComponent_isHomogeneous _ _),
    ← f.homogeneous_mem_truncate_iff ℂ s d hns hd (homogeneousComponent_isHomogeneous _ _),
    hfinite s hns hs]

theorem sum_intersection_distributive (a b c : UntruncatedIdealExpression n) :
    a.ideal ℂ ⊔ (b.ideal ℂ ⊓ c.ideal ℂ) =
      (a.ideal ℂ ⊔ b.ideal ℂ) ⊓ (a.ideal ℂ ⊔ c.ideal ℂ) := by
  apply ideal_eq_of_eligible_eq (.sum a (.intersection b c))
    (.intersection (.sum a b) (.sum a c))
  ext i
  simp only [eligible, Set.mem_inter_iff, Set.mem_union]
  tauto

theorem intersection_sum_distributive (a b c : UntruncatedIdealExpression n) :
    a.ideal ℂ ⊓ (b.ideal ℂ ⊔ c.ideal ℂ) =
      (a.ideal ℂ ⊓ b.ideal ℂ) ⊔ (a.ideal ℂ ⊓ c.ideal ℂ) := by
  apply ideal_eq_of_eligible_eq (.intersection a (.sum b c))
    (.sum (.intersection a b) (.intersection a c))
  ext i
  simp only [eligible, Set.mem_inter_iff, Set.mem_union]
  tauto

end UntruncatedIdealExpression

def generatedUntruncatedIdealLattice (n : ℕ) : Set (Ideal (PolynomialRing n ℂ)) :=
  Set.range (UntruncatedIdealExpression.ideal ℂ (n := n))

theorem corollary_6_7_distributive {n : ℕ}
    {A B C : Ideal (PolynomialRing n ℂ)}
    (hA : A ∈ generatedUntruncatedIdealLattice n)
    (hB : B ∈ generatedUntruncatedIdealLattice n)
    (hC : C ∈ generatedUntruncatedIdealLattice n) :
    A ⊔ (B ⊓ C) = (A ⊔ B) ⊓ (A ⊔ C) ∧
      A ⊓ (B ⊔ C) = (A ⊓ B) ⊔ (A ⊓ C) := by
  obtain ⟨a, rfl⟩ := hA
  obtain ⟨b, rfl⟩ := hB
  obtain ⟨c, rfl⟩ := hC
  exact ⟨a.sum_intersection_distributive b c, a.intersection_sum_distributive b c⟩

end HigherSpecht
end
end CanonicalSource1

section CanonicalSource2
/- Source: HigherSpecht/UntruncatedExpressionBases.lean -/



/-!
# The prescribed vector basis for untruncated ideal expressions

Every finite subfamily embeds in one sufficiently large finite truncation.
Its linear independence therefore follows by the actual quotient map.
Spanning uses homogeneous projection of an actual finite-basis expansion;
the low-degree ideal comparison is proved in UntruncatedIdealExpressions.
-/

noncomputable section
open TauCeti Module MvPolynomial
open scoped Classical

namespace HigherSpecht

def unboundedMasterPolynomial {R : Type*} [CommRing R] {n : ℕ}
    (i : UnboundedHarmonicIndex n)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) : PolynomialRing n R :=
  rename (finCongr (YoungDiagram.card_ofPartition i.part)) (higherSpechtPolynomial i.left T) *
    elementaryMultiplier n n i.multiplier.rowLen

theorem unboundedMasterPolynomial_isHomogeneous {R : Type*} [CommRing R] {n : ℕ}
    (i : UnboundedHarmonicIndex n)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) :
    (unboundedMasterPolynomial (R := R) i T).IsHomogeneous i.degree :=
  (higherSpechtPolynomial_isHomogeneous i.left T).rename_isHomogeneous.mul
    (elementaryMultiplier_isHomogeneous n n i.multiplier i.multiplier_length)

namespace UntruncatedIdealExpression

variable {n : ℕ} (e : UntruncatedIdealExpression n)

abbrev VectorIndex :=
  Σ i : {i : UnboundedHarmonicIndex n // i ∈ e.eligible},
    StandardYoungTableau (YoungDiagram.ofPartition i.val.part)

def polynomial (R : Type*) [CommRing R] (z : e.VectorIndex) : PolynomialRing n R :=
  unboundedMasterPolynomial z.1.val z.2

def family (R : Type*) [CommRing R] (z : e.VectorIndex) : PolynomialRing n R ⧸ e.ideal R :=
  Ideal.Quotient.mk (e.ideal R) (e.polynomial R z)

def forgetTruncation (s : ℕ) (hns : n ≤ s)
    (z : (e.truncate s hns).VectorIndex) : e.VectorIndex :=
  ⟨⟨z.1.val.toUnboundedHarmonicIndex,
    (e.truncate_eligible s hns z.1.val).mp z.1.property⟩, z.2⟩

def finiteVector (s : ℕ) (hns : n ≤ s) (z : e.VectorIndex)
    (hz : commonCopyBound z.1.val ≤ s) : (e.truncate s hns).VectorIndex :=
  ⟨⟨z.1.val.finiteAt s hz,
    (e.truncate_eligible s hns (z.1.val.finiteAt s hz)).mpr z.1.property⟩, z.2⟩

@[simp] theorem forgetTruncation_finiteVector (s : ℕ) (hns : n ≤ s)
    (z : e.VectorIndex) (hz : commonCopyBound z.1.val ≤ s) :
    e.forgetTruncation s hns (e.finiteVector s hns z hz) = z := by
  rcases z with ⟨⟨i, hi⟩, T⟩
  rfl

@[simp] theorem forgetTruncation_polynomial (R : Type*) [CommRing R]
    (s : ℕ) (hns : n ≤ s) (z : (e.truncate s hns).VectorIndex) :
    e.polynomial R (e.forgetTruncation s hns z) = (e.truncate s hns).polynomial R z := rfl

@[simp] theorem finiteVector_polynomial (R : Type*) [CommRing R]
    (s : ℕ) (hns : n ≤ s) (z : e.VectorIndex) (hz : commonCopyBound z.1.val ≤ s) :
    (e.truncate s hns).polynomial R (e.finiteVector s hns z hz) = e.polynomial R z := rfl

def truncateQuotient (R : Type*) [CommRing R] (s : ℕ) (hns : n ≤ s) :
    (PolynomialRing n R ⧸ e.ideal R) →ₐ[R]
      (PolynomialRing n R ⧸ (e.truncate s hns).ideal R) :=
  Ideal.Quotient.factorₐ R (e.ideal_le_truncate R s hns)

@[simp] theorem truncateQuotient_family (R : Type*) [CommRing R]
    (s : ℕ) (hns : n ≤ s) (z : e.VectorIndex) (hz : commonCopyBound z.1.val ≤ s) :
    e.truncateQuotient R s hns (e.family R z) =
      (e.truncate s hns).family R (e.finiteVector s hns z hz) := rfl

theorem family_linearIndependent : LinearIndependent ℂ (e.family ℂ) := by
  rw [linearIndependent_iff_finset_linearIndependent]
  intro t
  let s := n + t.sup (fun z : e.VectorIndex => commonCopyBound z.1.val) + 1
  have hns : n ≤ s := by dsimp [s]; omega
  have hs : 0 < s := by dsimp [s]; omega
  have hb (z : t) : commonCopyBound z.val.1.val ≤ s := by
    have h := Finset.le_sup (f := fun z : e.VectorIndex => commonCopyBound z.1.val) z.property
    dsimp [s]
    omega
  let f : t → (e.truncate s hns).VectorIndex :=
    fun z => e.finiteVector s hns z.val (hb z)
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have h' := congrArg (e.forgetTruncation s hns) h
    simpa only [f, e.forgetTruncation_finiteVector] using h'
  have hli := ((e.truncate s hns).family_linearIndependent hs).comp f hf
  apply LinearIndependent.of_comp (e.truncateQuotient ℂ s hns).toLinearMap
  change LinearIndependent ℂ
    (fun z : t => e.truncateQuotient ℂ s hns (e.family ℂ z.val))
  have hmap : (fun z : t => e.truncateQuotient ℂ s hns (e.family ℂ z.val)) =
      (fun z : t => (e.truncate s hns).family ℂ (f z)) := by
    funext z
    exact e.truncateQuotient_family ℂ s hns z.val (hb z)
  rw [hmap]
  exact hli

theorem homogeneous_class_mem_span {d : ℕ} {p : PolynomialRing n ℂ}
    (hp : p.IsHomogeneous d) :
    Ideal.Quotient.mk (e.ideal ℂ) p ∈ Submodule.span ℂ (Set.range (e.family ℂ)) := by
  let s := n + d + 1
  have hns : n ≤ s := by dsimp [s]; omega
  have hs : 0 < s := by dsimp [s]; omega
  have hd : d < s := by dsimp [s]; omega
  let b := (e.truncate s hns).prescribedBasis hs
  let q := Ideal.Quotient.mkₐ ℂ (e.ideal ℂ)
  let qf := Ideal.Quotient.mkₐ ℂ ((e.truncate s hns).ideal ℂ)
  let c := b.repr (qf p)
  let g : PolynomialRing n ℂ := c.sum fun i a => a • (e.truncate s hns).polynomial ℂ i
  have hg : qf g = qf p := by
    change qf (∑ i ∈ c.support, c i • (e.truncate s hns).polynomial ℂ i) = qf p
    simp only [map_sum, map_smul]
    have hrep (i) : qf ((e.truncate s hns).polynomial ℂ i) = b i :=
      ((e.truncate s hns).prescribedBasis_apply hs i).symm
    simp only [hrep]
    exact b.linearCombination_repr (qf p)
  have hmem : p - g ∈ (e.truncate s hns).ideal ℂ := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change qf (p - g) = 0
    rw [map_sub, hg, sub_self]
  have hlow := e.homogeneousComponent_truncate_mem ℂ s d hns hd hmem
  have hquot : q p = q (homogeneousComponent d g) := by
    apply sub_eq_zero.mp
    rw [← map_sub, ← homogeneousComponent_eq_self hp, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hlow
  change q p ∈ _
  rw [hquot]
  change q (homogeneousComponent d
    (∑ i ∈ c.support, c i • (e.truncate s hns).polynomial ℂ i)) ∈ _
  simp only [map_sum, map_smul]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  change q (homogeneousComponent d (finiteMasterPolynomial i.1.val i.2)) ∈ _
  rw [homogeneousComponent_of_mem (finiteMasterPolynomial_isHomogeneous i.1.val i.2)]
  split_ifs with hdeg
  · exact Submodule.subset_span ⟨e.forgetTruncation s hns i, rfl⟩
  · simpa only [map_zero] using
      (Submodule.zero_mem (Submodule.span ℂ (Set.range (e.family ℂ))))

theorem family_spans : ⊤ ≤ Submodule.span ℂ (Set.range (e.family ℂ)) := by
  intro x hx
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [MvPolynomial.as_sum p, map_sum]
  apply Submodule.sum_mem
  intro a ha
  exact e.homogeneous_class_mem_span (MvPolynomial.isHomogeneous_monomial (p.coeff a) rfl)

def prescribedBasis : Basis e.VectorIndex ℂ (PolynomialRing n ℂ ⧸ e.ideal ℂ) :=
  Basis.mk e.family_linearIndependent e.family_spans

@[simp] theorem prescribedBasis_apply (z : e.VectorIndex) :
    e.prescribedBasis z = e.family ℂ z := Basis.mk_apply _ _ _

/-- The original unbounded higher Specht representatives for the actual
quotient of every finite sum/intersection expression, with no degree bound. -/
theorem corollary_6_7_basis : IsSpecifiedBasis (R := ℂ) (e.family ℂ) :=
  ⟨e.prescribedBasis, e.prescribedBasis_apply⟩

end UntruncatedIdealExpression
end HigherSpecht
end
end CanonicalSource2

section CanonicalSource3
/- Source: HigherSpecht/UntruncatedExpressionCharacters.lean -/



/-!
# The actual graded Frobenius series of untruncated expressions

The degree piece is the image of homogeneous polynomials under the literal
quotient map.  Restricting the prescribed basis and its actual Specht
intertwiners computes its character.  The infinite series is specified
coefficient by coefficient; each coefficient is a finite sum by the actual
degree bound on the tableau/multiplier indices.
-/

noncomputable section
open TauCeti TauCeti.YoungTableau Module MvPolynomial
open scoped Classical

namespace HigherSpecht

def unboundedMasterComplexIntertwiner {n : ℕ} (i : UnboundedHarmonicIndex n) :
    Representation.IntertwiningMap (spechtModuleℂ i.part).ρ (polynomialRepresentation ℂ n) :=
  finiteMasterComplexIntertwiner (i.finiteAt (commonCopyBound i) le_rfl)

theorem unboundedMasterComplexIntertwiner_standard {n : ℕ}
    (i : UnboundedHarmonicIndex n)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) :
    unboundedMasterComplexIntertwiner i (complexSpechtStandardBasis i.part T) =
      unboundedMasterPolynomial (R := ℂ) i T :=
  finiteMasterComplexIntertwiner_standard (i.finiteAt (commonCopyBound i) le_rfl) T

namespace UntruncatedIdealExpression

variable {n : ℕ} (e : UntruncatedIdealExpression n)

def gradedPiece (d : ℕ) : Subrepresentation
    (quotientRepresentation (e.ideal ℂ) (e.permutationStable ℂ)) :=
  homogeneousQuotientSubrepresentation (e.ideal ℂ) (e.permutationStable ℂ) d

abbrev DegreeCopyIndex (d : ℕ) :=
  {i : UnboundedHarmonicIndex n // i ∈ e.eligible ∧ i.degree = d}

instance finiteDegreeCopyIndex (d : ℕ) : Finite (e.DegreeCopyIndex d) := by
  letI := (finite_unboundedHarmonic_degree n d).fintype
  exact Finite.of_injective
    (fun i : e.DegreeCopyIndex d =>
      (⟨i.val, i.property.2⟩ : {i : UnboundedHarmonicIndex n // i.degree = d}))
    (fun i j h => Subtype.ext (congrArg
      (fun z : {i : UnboundedHarmonicIndex n // i.degree = d} => z.val) h))

instance fintypeDegreeCopyIndex (d : ℕ) : Fintype (e.DegreeCopyIndex d) :=
  Fintype.ofFinite _

def degreeVectorEquiv (d : ℕ) :
    (Σ i : e.DegreeCopyIndex d, StandardYoungTableau (YoungDiagram.ofPartition i.val.part)) ≃
      {z : e.VectorIndex // z.1.val.degree = d} where
  toFun z := ⟨⟨⟨z.1.val, z.1.property.1⟩, z.2⟩, z.1.property.2⟩
  invFun z := ⟨⟨z.val.1.val, z.val.1.property, z.property⟩, z.val.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def degreeCopyBasis (d : ℕ) :
    Basis (Σ i : e.DegreeCopyIndex d, StandardYoungTableau (YoungDiagram.ofPartition i.val.part))
      ℂ (e.gradedPiece d).toSubmodule :=
  (homogeneousQuotientBasis (e.ideal ℂ) (e.ideal_isHomogeneous ℂ)
    e.prescribedBasis (e.polynomial ℂ) (fun z => z.1.val.degree)
    (fun z => unboundedMasterPolynomial_isHomogeneous z.1.val z.2)
    e.prescribedBasis_apply d).reindex (e.degreeVectorEquiv d).symm

theorem degreeCopyBasis_apply (d : ℕ)
    (i : e.DegreeCopyIndex d) (T : StandardYoungTableau (YoungDiagram.ofPartition i.val.part)) :
    (e.degreeCopyBasis d ⟨i, T⟩ : PolynomialRing n ℂ ⧸ e.ideal ℂ) =
      Ideal.Quotient.mk (e.ideal ℂ) (unboundedMasterPolynomial i.val T) := by
  let b := homogeneousQuotientBasis (e.ideal ℂ) (e.ideal_isHomogeneous ℂ)
    (e.prescribedBasis) (e.polynomial ℂ) (fun z => z.1.val.degree)
    (fun z => unboundedMasterPolynomial_isHomogeneous z.1.val z.2)
    (e.prescribedBasis_apply) d
  let E := e.degreeVectorEquiv d
  have h := b.reindex_apply E.symm ⟨i, T⟩
  exact (congrArg
    (fun z : homogeneousQuotientPiece (e.ideal ℂ) d =>
      (z : PolynomialRing n ℂ ⧸ e.ideal ℂ)) h).trans
    ((homogeneousQuotientBasis_apply (e.ideal ℂ) (e.ideal_isHomogeneous ℂ)
      (e.prescribedBasis) (e.polynomial ℂ) (fun z => z.1.val.degree)
      (fun z => unboundedMasterPolynomial_isHomogeneous z.1.val z.2)
      (e.prescribedBasis_apply) d (E ⟨i, T⟩)).trans
        (e.prescribedBasis_apply (E ⟨i, T⟩).val))

def complexIntertwiner (i : UnboundedHarmonicIndex n) :
    Representation.IntertwiningMap (spechtModuleℂ i.part).ρ
      (quotientRepresentation (e.ideal ℂ) (e.permutationStable ℂ)) :=
  (quotientProjectionIntertwiner (e.ideal ℂ) (e.permutationStable ℂ)).comp
    (unboundedMasterComplexIntertwiner i)

theorem complexIntertwiner_standard (i : UnboundedHarmonicIndex n)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) :
    e.complexIntertwiner i (complexSpechtStandardBasis i.part T) =
      Ideal.Quotient.mk (e.ideal ℂ) (unboundedMasterPolynomial i T) := by
  change Ideal.Quotient.mk (e.ideal ℂ)
    (unboundedMasterComplexIntertwiner i (complexSpechtStandardBasis i.part T)) = _
  rw [unboundedMasterComplexIntertwiner_standard]

theorem complexIntertwiner_mem_degree (d : ℕ) (i : e.DegreeCopyIndex d)
    (v : spechtModuleℂ i.val.part) :
    e.complexIntertwiner i.val v ∈ (e.gradedPiece d).toSubmodule := by
  rw [← (complexSpechtStandardBasis i.val.part).sum_repr v, map_sum]
  apply Submodule.sum_mem
  intro T hT
  rw [map_smul, e.complexIntertwiner_standard]
  apply Submodule.smul_mem
  rw [← e.degreeCopyBasis_apply d i T]
  exact (e.degreeCopyBasis d ⟨i, T⟩).property

def degreeSpechtMap (d : ℕ) (i : e.DegreeCopyIndex d) :
    Representation.IntertwiningMap (spechtModuleℂ i.val.part).ρ (e.gradedPiece d).toRepresentation :=
  (e.complexIntertwiner i.val).codRestrict (e.gradedPiece d)
    (e.complexIntertwiner_mem_degree d i)

theorem degreeSpechtMap_standard (d : ℕ) (i : e.DegreeCopyIndex d)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.val.part)) :
    e.degreeSpechtMap d i (complexSpechtStandardBasis i.val.part T) =
      e.degreeCopyBasis d ⟨i, T⟩ := by
  apply Subtype.ext
  rw [e.degreeCopyBasis_apply, degreeSpechtMap,
    Representation.IntertwiningMap.codRestrict_apply_coe]
  exact e.complexIntertwiner_standard i.val T

theorem character_gradedPiece (d : ℕ) (g : Equiv.Perm (Fin n)) :
    (e.gradedPiece d).toRepresentation.character g =
      ∑ i : e.DegreeCopyIndex d, Representation.character (spechtModuleℂ i.val.part).ρ g :=
  character_eq_sum_of_intertwining_basis
    (fun i : e.DegreeCopyIndex d => (spechtModuleℂ i.val.part).ρ)
    (e.gradedPiece d).toRepresentation (fun i => complexSpechtStandardBasis i.val.part)
    (e.degreeCopyBasis d) (e.degreeSpechtMap d) (e.degreeSpechtMap_standard d) g

def frobeniusCoefficient (d : ℕ) : MvPolynomial (Fin n) ℂ :=
  letI := Module.Finite.of_basis (e.degreeCopyBasis d)
  (frobeniusCharacteristic n n le_rfl
    (ClassFunction.ofCharacter (e.gradedPiece d).toRepresentation) :
      symmetricHomogeneousSubmodule (Fin n) ℂ n)

theorem frobeniusCoefficient_eq (d : ℕ) :
    e.frobeniusCoefficient d =
      ∑ i : e.DegreeCopyIndex d, schurPoly (Fin n) ℂ i.val.part := by
  letI := Module.Finite.of_basis (e.degreeCopyBasis d)
  have hc : ClassFunction.ofCharacter (e.gradedPiece d).toRepresentation =
      ∑ i : e.DegreeCopyIndex d, ClassFunction.ofCharacter (spechtModuleℂ i.val.part).ρ := by
    apply Subtype.ext
    funext g
    simp only [Submodule.coe_sum, ClassFunction.ofCharacter_apply, Finset.sum_apply]
    exact e.character_gradedPiece d g
  simp only [frobeniusCoefficient, hc, map_sum, Submodule.coe_sum,
    frobeniusCharacteristic_spechtCharacter]

def frobeniusSeries : PowerSeries (MvPolynomial (Fin n) ℂ) :=
  PowerSeries.mk e.frobeniusCoefficient

/-- The coefficientwise form of the locally finite Schur series in
Corollary 6.7.  The left side is the Frobenius characteristic of the actual
quotient representation, not an index-set definition. -/
theorem corollary_6_7_frobenius :
    e.frobeniusSeries = PowerSeries.mk
      (fun d => ∑ i : e.DegreeCopyIndex d, schurPoly (Fin n) ℂ i.val.part) := by
  ext d
  simp only [frobeniusSeries, PowerSeries.coeff_mk, e.frobeniusCoefficient_eq]

end UntruncatedIdealExpression
end HigherSpecht
end
end CanonicalSource3

section CanonicalSource4
/- Source: HigherSpecht/UntruncatedExpressionParameters.lean -/



/-!
# The actual elementary-parameter basis for a common-size expression

The common-size condition is the literal equality of the sizes of every
leaf partition.  It factors the recursively defined eligibility predicate
into a tableau condition and an unrestricted partition of length at most
`n-k`.  Partition differences turn that multiplier into an actual monomial
in the elementary parameters.  Thus the previously proved vector basis
gives freeness over their actual evaluation algebra.
-/

noncomputable section
open TauCeti Module MvPolynomial
open scoped Classical

namespace HigherSpecht

theorem elementaryMultiplier_extend {R : Type*} [CommRing R]
    (n m l : ℕ) (hml : m ≤ l) (eta : YoungDiagram) (heta : eta.colLen 0 ≤ m) :
    elementaryMultiplier (R := R) n m eta.rowLen =
      elementaryMultiplier n l eta.rowLen := by
  unfold elementaryMultiplier
  apply Finset.prod_subset (Finset.range_mono hml)
  intro j hj hjm
  have hmj : m ≤ j := by simpa only [Finset.mem_range, not_lt] using hjm
  rw [YoungDiagram.rowLen_eq_zero_of_colLen_le (heta.trans hmj),
    Nat.zero_sub, pow_zero]

abbrev UntruncatedBaseCopyIndex (n : ℕ) :=
  Σ part : n.Partition, StandardYoungTableau (YoungDiagram.ofPartition part)

namespace UntruncatedIdealExpression

variable {n : ℕ} (e : UntruncatedIdealExpression n)

def allSize (e : UntruncatedIdealExpression n) (k : ℕ) : Prop :=
  match e with
  | .atom a => a.diagram.card = k
  | .sum e f => e.allSize k ∧ f.allSize k
  | .intersection e f => e.allSize k ∧ f.allSize k

theorem commonSize_le {k : ℕ} (he : e.allSize k) : k ≤ n := by
  induction e with
  | atom a => exact he ▸ a.card_le
  | sum e f h₁ h₂ => exact h₁ he.1
  | intersection e f h₁ h₂ => exact h₁ he.1

def baseEligible : UntruncatedIdealExpression n → Set (UntruncatedBaseCopyIndex n)
  | .atom a => {i | CatDominates (prefixTableau i.2 a.diagram.card
      (by simpa only [YoungDiagram.card_ofPartition] using a.card_le)) a.diagram}
  | .sum e f => e.baseEligible ∩ f.baseEligible
  | .intersection e f => e.baseEligible ∪ f.baseEligible

theorem eligible_iff_commonSize {k : ℕ} (he : e.allSize k)
    (i : UnboundedHarmonicIndex n) :
    i ∈ e.eligible ↔ i.multiplier.colLen 0 ≤ n - k ∧ ⟨i.part, i.left⟩ ∈ e.baseEligible := by
  induction e with
  | atom a =>
      have hcard : a.diagram.card = k := he
      simp only [eligible, UnboundedHarmonicIndex.eligible, baseEligible,
        Set.mem_setOf_eq, hcard]
  | sum e f h₁ h₂ =>
      rw [eligible, Set.mem_inter_iff, h₁ he.1, h₂ he.2]
      change (_ ∧ _) ∧ (_ ∧ _) ↔ _ ∧ (_ ∧ _)
      tauto
  | intersection e f h₁ h₂ =>
      rw [eligible, Set.mem_union, h₁ he.1, h₂ he.2]
      change (_ ∧ _) ∨ (_ ∧ _) ↔ _ ∧ (_ ∨ _)
      tauto

abbrev BaseVectorIndex :=
  Σ i : {i : UntruncatedBaseCopyIndex n // i ∈ e.baseEligible},
    StandardYoungTableau (YoungDiagram.ofPartition i.val.1)

instance finiteBaseVectorIndex : Finite e.BaseVectorIndex := by
  unfold BaseVectorIndex
  infer_instance

instance fintypeBaseVectorIndex : Fintype e.BaseVectorIndex := Fintype.ofFinite _

def basePolynomial (R : Type*) [CommRing R] (z : e.BaseVectorIndex) : PolynomialRing n R :=
  rename (finCongr (YoungDiagram.card_ofPartition z.1.val.1))
    (higherSpechtPolynomial z.1.val.2 z.2)

def baseFamily (z : e.BaseVectorIndex) : PolynomialRing n ℂ ⧸ e.ideal ℂ :=
  Ideal.Quotient.mk (e.ideal ℂ) (e.basePolynomial ℂ z)

def parameterVectorIndex {k : ℕ} (he : e.allSize k)
    (z : e.BaseVectorIndex × (Fin (n - k) →₀ ℕ)) : e.VectorIndex :=
  let i : UnboundedHarmonicIndex n :=
    { part := z.1.1.val.1
      left := z.1.1.val.2
      multiplier := partitionFromDifferences z.2
      multiplier_length := (partitionFromDifferences_height z.2).trans (Nat.sub_le n k) }
  ⟨⟨i, (e.eligible_iff_commonSize he i).mpr
    ⟨partitionFromDifferences_height z.2, z.1.1.property⟩⟩, z.1.2⟩

def parameterVectorInverse {k : ℕ} (he : e.allSize k)
    (z : e.VectorIndex) : e.BaseVectorIndex × (Fin (n - k) →₀ ℕ) :=
  (⟨⟨⟨z.1.val.part, z.1.val.left⟩, ((e.eligible_iff_commonSize he z.1.val).mp z.1.property).2⟩,
    z.2⟩, partitionDifferences (n - k) z.1.val.multiplier)

theorem parameterVectorInverse_left {k : ℕ} (he : e.allSize k)
    (z : e.BaseVectorIndex × (Fin (n - k) →₀ ℕ)) :
    e.parameterVectorInverse he (e.parameterVectorIndex he z) = z := by
  rcases z with ⟨⟨⟨⟨part, S⟩, hS⟩, T⟩, a⟩
  apply Prod.ext
  · rfl
  · ext j
    simp only [parameterVectorInverse, parameterVectorIndex,
      partitionDifferences_apply, partitionFromDifferences_difference]

theorem parameterVectorInverse_right {k : ℕ} (he : e.allSize k) (z : e.VectorIndex) :
    e.parameterVectorIndex he (e.parameterVectorInverse he z) = z := by
  have hlen := ((e.eligible_iff_commonSize he z.1.val).mp z.1.property).1
  have hpart := partitionFromDifferences_partitionDifferences (n - k) z.1.val.multiplier hlen
  rcases z with ⟨⟨⟨part, S, eta, hlength⟩, heligible⟩, T⟩
  dsimp only at hpart
  have sameMultiplier (eta' : YoungDiagram) (h : eta' = eta)
      (hlength' : eta'.colLen 0 ≤ n)
      (heligible' : (⟨part, S, eta', hlength'⟩ : UnboundedHarmonicIndex n) ∈ e.eligible) :
      (⟨⟨⟨part, S, eta', hlength'⟩, heligible'⟩, T⟩ : e.VectorIndex) =
        ⟨⟨⟨part, S, eta, hlength⟩, heligible⟩, T⟩ := by
    cases h
    rfl
  exact sameMultiplier _ hpart _ _

def parameterVectorEquiv {k : ℕ} (he : e.allSize k) :
    (e.BaseVectorIndex × (Fin (n - k) →₀ ℕ)) ≃ e.VectorIndex where
  toFun := e.parameterVectorIndex he
  invFun := e.parameterVectorInverse he
  left_inv := e.parameterVectorInverse_left he
  right_inv := e.parameterVectorInverse_right he

abbrev ParameterRing (_e : UntruncatedIdealExpression n) (k : ℕ) :=
  MvPolynomial (Fin (n - k)) ℂ

def parameterClasses (k : ℕ) : Fin (n - k) → PolynomialRing n ℂ ⧸ e.ideal ℂ :=
  fun j => Ideal.Quotient.mk (e.ideal ℂ) (esymm (Fin n) ℂ (j.val + 1))

instance parameterAlgebra (k : ℕ) :
    Algebra (e.ParameterRing k) (PolynomialRing n ℂ ⧸ e.ideal ℂ) :=
  (MvPolynomial.aeval (e.parameterClasses k)).toRingHom.toAlgebra

instance parameterScalarTower (k : ℕ) :
    IsScalarTower ℂ (e.ParameterRing k) (PolynomialRing n ℂ ⧸ e.ideal ℂ) :=
  IsScalarTower.of_algHom (MvPolynomial.aeval (e.parameterClasses k))

theorem parameter_monomial_smul {k : ℕ} (he : e.allSize k)
    (i : e.BaseVectorIndex) (a : Fin (n - k) →₀ ℕ) :
    (MvPolynomial.monomial a (1 : ℂ) : e.ParameterRing k) • e.baseFamily i =
      e.family ℂ (e.parameterVectorIndex he (i, a)) := by
  rw [Algebra.smul_def]
  change MvPolynomial.aeval (e.parameterClasses k) (MvPolynomial.monomial a 1) *
    e.baseFamily i = _
  rw [MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod_pow]
  change (∏ j : Fin (n - k), Ideal.Quotient.mk (e.ideal ℂ)
      (esymm (Fin n) ℂ (j.val + 1)) ^ a j) *
    Ideal.Quotient.mk (e.ideal ℂ) (e.basePolynomial ℂ i) = _
  simp only [family, polynomial, parameterVectorIndex, unboundedMasterPolynomial]
  rw [← elementaryMultiplier_extend n (n - k) n (Nat.sub_le n k)
      (partitionFromDifferences a) (partitionFromDifferences_height a),
    elementaryMultiplier_partitionFromDifferences]
  simp only [map_mul, map_prod, map_pow, basePolynomial, mul_comm]
  rfl

theorem baseFamily_linearIndependent {k : ℕ} (he : e.allSize k) :
    LinearIndependent (e.ParameterRing k) e.baseFamily := by
  apply linearIndependent_scalarRing_of_expansion
    (MvPolynomial.basisMonomials (Fin (n - k)) ℂ)
  have h : LinearIndependent ℂ
      (fun z : e.BaseVectorIndex × (Fin (n - k) →₀ ℕ) =>
        e.family ℂ (e.parameterVectorIndex he z)) :=
    e.family_linearIndependent.comp (e.parameterVectorEquiv he)
      (e.parameterVectorEquiv he).injective
  have hfamily :
      (fun z : e.BaseVectorIndex × (Fin (n - k) →₀ ℕ) =>
        MvPolynomial.basisMonomials (Fin (n - k)) ℂ z.2 • e.baseFamily z.1) =
      (fun z : e.BaseVectorIndex × (Fin (n - k) →₀ ℕ) =>
        e.family ℂ (e.parameterVectorIndex he z)) := by
    funext z
    exact e.parameter_monomial_smul he z.1 z.2
  exact Eq.mpr (congrArg
    (fun v : e.BaseVectorIndex × (Fin (n - k) →₀ ℕ) →
      PolynomialRing n ℂ ⧸ e.ideal ℂ => LinearIndependent ℂ v) hfamily) h

theorem baseFamily_spans {k : ℕ} (he : e.allSize k) :
    ⊤ ≤ Submodule.span (e.ParameterRing k) (Set.range e.baseFamily) := by
  let M := Submodule.span (e.ParameterRing k) (Set.range e.baseFamily)
  have hle : Submodule.span ℂ (Set.range (e.family ℂ)) ≤ M.restrictScalars ℂ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    obtain ⟨⟨i, a⟩, rfl⟩ := (e.parameterVectorEquiv he).surjective z
    change e.family ℂ (e.parameterVectorIndex he (i, a)) ∈ M
    rw [← e.parameter_monomial_smul he]
    exact M.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  intro x hx
  exact hle (e.family_spans hx)

def parameterBasis {k : ℕ} (he : e.allSize k) :
    Basis e.BaseVectorIndex (e.ParameterRing k) (PolynomialRing n ℂ ⧸ e.ideal ℂ) :=
  Basis.mk (e.baseFamily_linearIndependent he) (e.baseFamily_spans he)

@[simp] theorem parameterBasis_apply {k : ℕ} (he : e.allSize k) (i : e.BaseVectorIndex) :
    e.parameterBasis he i = e.baseFamily i := Basis.mk_apply _ _ _

theorem baseEligible_oneRow :
    (⟨(standardPairPartitionEquiv n (oneRowPair n)).1,
      (standardPairPartitionEquiv n (oneRowPair n)).2.1⟩ : UntruncatedBaseCopyIndex n)
      ∈ e.baseEligible := by
  induction e with
  | atom a =>
      change prefixEligible a.diagram a.card_le
        ((standardPairPartitionEquiv n).symm (standardPairPartitionEquiv n (oneRowPair n)))
      rw [Equiv.symm_apply_apply]
      exact (oneRowGriffinIndex n a.diagram a.card_le 1 (by omega)).eligible
  | sum e f he hf => exact ⟨he, hf⟩
  | intersection e f he hf => exact Or.inl he

def oneRowBaseVector : e.BaseVectorIndex :=
  ⟨⟨⟨(standardPairPartitionEquiv n (oneRowPair n)).1,
    (standardPairPartitionEquiv n (oneRowPair n)).2.1⟩, e.baseEligible_oneRow⟩,
    (standardPairPartitionEquiv n (oneRowPair n)).2.2⟩

theorem quotient_nontrivial {k : ℕ} (he : e.allSize k) :
    Nontrivial (PolynomialRing n ℂ ⧸ e.ideal ℂ) :=
  nontrivial_of_ne _ _ ((e.parameterBasis he).ne_zero e.oneRowBaseVector)

theorem parameter_finite {k : ℕ} (he : e.allSize k) :
    Module.Finite (e.ParameterRing k) (PolynomialRing n ℂ ⧸ e.ideal ℂ) :=
  Module.Finite.of_basis (e.parameterBasis he)

theorem parameter_free {k : ℕ} (he : e.allSize k) :
    Module.Free (e.ParameterRing k) (PolynomialRing n ℂ ⧸ e.ideal ℂ) :=
  Module.Free.of_basis (e.parameterBasis he)

theorem parameter_faithful {k : ℕ} (he : e.allSize k) :
    FaithfulSMul (e.ParameterRing k) (PolynomialRing n ℂ ⧸ e.ideal ℂ) := by
  letI := e.quotient_nontrivial he
  letI := e.parameter_free he
  infer_instance

theorem parameter_algebraicIndependent {k : ℕ} (he : e.allSize k) :
    AlgebraicIndependent ℂ (e.parameterClasses k) := by
  letI := e.parameter_faithful he
  change Function.Injective (algebraMap (e.ParameterRing k) (PolynomialRing n ℂ ⧸ e.ideal ℂ))
  exact FaithfulSMul.algebraMap_injective (e.ParameterRing k) (PolynomialRing n ℂ ⧸ e.ideal ℂ)

theorem krullDimension {k : ℕ} (he : e.allSize k) :
    ringKrullDim (PolynomialRing n ℂ ⧸ e.ideal ℂ) = (n - k : ℕ) := by
  letI := e.parameter_finite he
  letI := e.parameter_faithful he
  rw [TauCeti.ringKrullDim_eq_of_isIntegral_of_faithfulSMul (R := e.ParameterRing k)]
  change ringKrullDim (MvPolynomial (Fin (n - k)) ℂ) = _
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field, zero_add, Nat.card_fin]

theorem isCohenMacaulay_atPrime {k : ℕ} (he : e.allSize k)
    (P : Ideal (PolynomialRing n ℂ ⧸ e.ideal ℂ)) [P.IsPrime] :
    Module.IsCohenMacaulay (Localization.AtPrime P) (Localization.AtPrime P) := by
  letI := e.parameter_finite he
  letI := e.parameter_free he
  letI : Module.Flat (e.ParameterRing k) (PolynomialRing n ℂ ⧸ e.ideal ℂ) := inferInstance
  exact finiteFlat_isCohenMacaulay_atPrime (e.ParameterRing k) _ P

/-- The common-size finite-free and Cohen--Macaulay clauses of Corollary 6.7,
with the actual elementary parameter action and original unmultiplied
higher Specht representatives. -/
theorem corollary_6_7_parameters {k : ℕ} (he : e.allSize k) :
    IsSpecifiedBasis (R := e.ParameterRing k) e.baseFamily ∧
      Module.Finite (e.ParameterRing k) (PolynomialRing n ℂ ⧸ e.ideal ℂ) ∧
      ringKrullDim (PolynomialRing n ℂ ⧸ e.ideal ℂ) = (n - k : ℕ) ∧
      ∀ (P : Ideal (PolynomialRing n ℂ ⧸ e.ideal ℂ)) [P.IsPrime],
        Module.IsCohenMacaulay (Localization.AtPrime P) (Localization.AtPrime P) :=
  ⟨⟨e.parameterBasis he, e.parameterBasis_apply he⟩, e.parameter_finite he,
    e.krullDimension he, e.isCohenMacaulay_atPrime he⟩

end UntruncatedIdealExpression
end HigherSpecht
end
end CanonicalSource4

section CanonicalSource5
/- Source: HigherSpecht/FiniteIdealFamilies.lean -/



/-!
# Literal finite nonempty families of ideals

An arbitrary finite nonempty index type is enumerated only to build an
atomic/binary expression.  The terminal leaf is repeated; the proved
interpretation identities remove that repetition by the logical
idempotence of conjunction/disjunction and the lattice laws for ideals.
Thus neither a nullary operation nor an extra Fintype hypothesis enters
the statements.  The displayed families use the original polynomials in
the literal finite supremum or infimum quotient.

This file was reconstructed after the v21 runtime recovery.  It preserves
the required finiteSum/finiteIntersection APIs and mathematical scope;
it does not claim byte identity with the lost pre-outage source.
-/

noncomputable section
open TauCeti TauCeti.YoungTableau Module MvPolynomial
open scoped Classical

universe u v

namespace HigherSpecht

def finiteExpressionEnumeration (ι : Type*) [Finite ι] : List ι := by
  classical
  letI := Fintype.ofFinite ι
  exact Finset.univ.toList

private theorem mem_finiteExpressionEnumeration {ι : Type*} [Finite ι] (i : ι) :
    i ∈ finiteExpressionEnumeration ι := by
  classical
  simp [finiteExpressionEnumeration]

def finiteExpressionFold {ι : Type u} {α : Type v} [Finite ι] [Nonempty ι]
    (op : α → α → α) (f : ι → α) : α :=
  (finiteExpressionEnumeration ι).foldr (fun i a => op (f i) a)
    (f (Classical.choice (inferInstance : Nonempty ι)))

private theorem finiteExpressionFold_all {ι : Type u} {α : Type v} [Finite ι] [Nonempty ι]
    (op : α → α → α) (f : ι → α) (P : α → Prop)
    (hop : ∀ a b, P (op a b) ↔ P a ∧ P b) :
    P (finiteExpressionFold op f) ↔ ∀ i, P (f i) := by
  classical
  let i₀ : ι := Classical.choice (inferInstance : Nonempty ι)
  have hlist (l : List ι) :
      P (l.foldr (fun i a => op (f i) a) (f i₀)) ↔
        P (f i₀) ∧ ∀ i ∈ l, P (f i) := by
    induction l with
    | nil => simp
    | cons j l ih =>
        rw [List.foldr_cons, hop, ih]
        constructor
        · rintro ⟨hj, h₀, hl⟩
          refine ⟨h₀, ?_⟩
          intro i hi
          rcases List.mem_cons.mp hi with h | h
          · subst i
            exact hj
          · exact hl i h
        · rintro ⟨h₀, hl⟩
          exact ⟨hl j (by simp), h₀, fun i hi => hl i (List.mem_cons_of_mem j hi)⟩
  change P ((finiteExpressionEnumeration ι).foldr (fun i a => op (f i) a) (f i₀)) ↔ _
  rw [hlist]
  constructor
  · intro h i
    exact h.2 i (mem_finiteExpressionEnumeration i)
  · intro h
    exact ⟨h i₀, fun i _ => h i⟩

private theorem finiteExpressionFold_exists {ι : Type u} {α : Type v} [Finite ι] [Nonempty ι]
    (op : α → α → α) (f : ι → α) (P : α → Prop)
    (hop : ∀ a b, P (op a b) ↔ P a ∨ P b) :
    P (finiteExpressionFold op f) ↔ ∃ i, P (f i) := by
  classical
  let i₀ : ι := Classical.choice (inferInstance : Nonempty ι)
  have hlist (l : List ι) :
      P (l.foldr (fun i a => op (f i) a) (f i₀)) ↔
        P (f i₀) ∨ ∃ i ∈ l, P (f i) := by
    induction l with
    | nil => simp
    | cons j l ih =>
        rw [List.foldr_cons, hop, ih]
        constructor
        · rintro (hj | h₀ | ⟨i, hi, hPi⟩)
          · exact Or.inr ⟨j, by simp, hj⟩
          · exact Or.inl h₀
          · exact Or.inr ⟨i, List.mem_cons_of_mem j hi, hPi⟩
        · rintro (h₀ | ⟨i, hi, hPi⟩)
          · exact Or.inr (Or.inl h₀)
          · rcases List.mem_cons.mp hi with h | h
            · subst i
              exact Or.inl hPi
            · exact Or.inr (Or.inr ⟨i, h, hPi⟩)
  change P ((finiteExpressionEnumeration ι).foldr (fun i a => op (f i) a) (f i₀)) ↔ _
  rw [hlist]
  constructor
  · rintro (h₀ | ⟨i, _, hi⟩)
    · exact ⟨i₀, h₀⟩
    · exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    exact Or.inr ⟨i, mem_finiteExpressionEnumeration i, hi⟩

namespace GriffinIdealExpression

variable {ι : Type*} [Finite ι] [Nonempty ι] {n s : ℕ}

def finiteSum (E : ι → GriffinIdealExpression n s) : GriffinIdealExpression n s :=
  finiteExpressionFold .sum E

def finiteIntersection (E : ι → GriffinIdealExpression n s) :
    GriffinIdealExpression n s :=
  finiteExpressionFold .intersection E

theorem finiteSum_ideal_le_iff (R : Type*) [CommRing R]
    (E : ι → GriffinIdealExpression n s) (I : Ideal (PolynomialRing n R)) :
    (finiteSum E).ideal R ≤ I ↔ ∀ j, (E j).ideal R ≤ I :=
  finiteExpressionFold_all GriffinIdealExpression.sum E (fun e => e.ideal R ≤ I)
    (fun _ _ => sup_le_iff)

theorem le_finiteIntersection_ideal_iff (R : Type*) [CommRing R]
    (E : ι → GriffinIdealExpression n s) (I : Ideal (PolynomialRing n R)) :
    I ≤ (finiteIntersection E).ideal R ↔ ∀ j, I ≤ (E j).ideal R :=
  finiteExpressionFold_all GriffinIdealExpression.intersection E (fun e => I ≤ e.ideal R)
    (fun _ _ => le_inf_iff)

theorem finiteSum_ideal (R : Type*) [CommRing R]
    (E : ι → GriffinIdealExpression n s) :
    (finiteSum E).ideal R = ⨆ j, (E j).ideal R := by
  apply le_antisymm
  · exact (finiteSum_ideal_le_iff R E _).mpr (fun j => le_iSup (fun j => (E j).ideal R) j)
  · exact iSup_le ((finiteSum_ideal_le_iff R E _).mp le_rfl)

theorem finiteIntersection_ideal (R : Type*) [CommRing R]
    (E : ι → GriffinIdealExpression n s) :
    (finiteIntersection E).ideal R = ⨅ j, (E j).ideal R := by
  apply le_antisymm
  · exact le_iInf ((le_finiteIntersection_ideal_iff R E _).mp le_rfl)
  · exact (le_finiteIntersection_ideal_iff R E _).mpr
      (fun j => iInf_le (fun j => (E j).ideal R) j)

theorem mem_finiteSum_eligible (E : ι → GriffinIdealExpression n s)
    (i : FiniteHarmonicIndex n s) :
    i ∈ (finiteSum E).eligible ↔ ∀ j, i ∈ (E j).eligible :=
  finiteExpressionFold_all GriffinIdealExpression.sum E (fun e => i ∈ e.eligible) (fun _ _ => Iff.rfl)

theorem mem_finiteIntersection_eligible (E : ι → GriffinIdealExpression n s)
    (i : FiniteHarmonicIndex n s) :
    i ∈ (finiteIntersection E).eligible ↔ ∃ j, i ∈ (E j).eligible :=
  finiteExpressionFold_exists GriffinIdealExpression.intersection E (fun e => i ∈ e.eligible)
    (fun _ _ => Iff.rfl)

abbrev FiniteFamilySumIndex (E : ι → GriffinIdealExpression n s) :=
  Σ i : {i : FiniteHarmonicIndex n s // ∀ j, i ∈ (E j).eligible},
    StandardYoungTableau (YoungDiagram.ofPartition i.val.part)

abbrev FiniteFamilyIntersectionIndex (E : ι → GriffinIdealExpression n s) :=
  Σ i : {i : FiniteHarmonicIndex n s // ∃ j, i ∈ (E j).eligible},
    StandardYoungTableau (YoungDiagram.ofPartition i.val.part)

def finiteSumVectorEquiv (E : ι → GriffinIdealExpression n s) :
    (finiteSum E).VectorIndex ≃ FiniteFamilySumIndex E where
  toFun z := ⟨⟨z.1.val, (mem_finiteSum_eligible E z.1.val).mp z.1.property⟩, z.2⟩
  invFun z := ⟨⟨z.1.val, (mem_finiteSum_eligible E z.1.val).mpr z.1.property⟩, z.2⟩
  left_inv z := by rcases z with ⟨⟨i, hi⟩, T⟩; rfl
  right_inv z := by rcases z with ⟨⟨i, hi⟩, T⟩; rfl

def finiteIntersectionVectorEquiv (E : ι → GriffinIdealExpression n s) :
    (finiteIntersection E).VectorIndex ≃ FiniteFamilyIntersectionIndex E where
  toFun z := ⟨⟨z.1.val, (mem_finiteIntersection_eligible E z.1.val).mp z.1.property⟩, z.2⟩
  invFun z := ⟨⟨z.1.val, (mem_finiteIntersection_eligible E z.1.val).mpr z.1.property⟩, z.2⟩
  left_inv z := by rcases z with ⟨⟨i, hi⟩, T⟩; rfl
  right_inv z := by rcases z with ⟨⟨i, hi⟩, T⟩; rfl

def finiteFamilySum (E : ι → GriffinIdealExpression n s) (z : FiniteFamilySumIndex E) :
    PolynomialRing n ℂ ⧸ (⨆ j, (E j).ideal ℂ) :=
  Ideal.Quotient.mk _ (finiteMasterPolynomial z.1.val z.2)

def finiteFamilyIntersection (E : ι → GriffinIdealExpression n s)
    (z : FiniteFamilyIntersectionIndex E) :
    PolynomialRing n ℂ ⧸ (⨅ j, (E j).ideal ℂ) :=
  Ideal.Quotient.mk _ (finiteMasterPolynomial z.1.val z.2)

theorem corollary_5_3_finiteSum_basis (E : ι → GriffinIdealExpression n s) (hs : 0 < s) :
    IsSpecifiedBasis (R := ℂ) (finiteFamilySum E) := by
  have H := (finiteSum E).corollary_5_3_basis hs
  change IsSpecifiedBasis (R := ℂ) (fun z : (finiteSum E).VectorIndex =>
    Ideal.Quotient.mk ((finiteSum E).ideal ℂ) (finiteMasterPolynomial z.1.val z.2)) at H
  rw [finiteSum_ideal ℂ E] at H
  obtain ⟨b, hb⟩ := H
  refine ⟨b.reindex (finiteSumVectorEquiv E), ?_⟩
  intro z
  rw [Basis.reindex_apply, hb]
  rfl

theorem corollary_5_3_finiteIntersection_basis (E : ι → GriffinIdealExpression n s)
    (hs : 0 < s) :
    IsSpecifiedBasis (R := ℂ) (finiteFamilyIntersection E) := by
  have H := (finiteIntersection E).corollary_5_3_basis hs
  change IsSpecifiedBasis (R := ℂ) (fun z : (finiteIntersection E).VectorIndex =>
    Ideal.Quotient.mk ((finiteIntersection E).ideal ℂ)
      (finiteMasterPolynomial z.1.val z.2)) at H
  rw [finiteIntersection_ideal ℂ E] at H
  obtain ⟨b, hb⟩ := H
  refine ⟨b.reindex (finiteIntersectionVectorEquiv E), ?_⟩
  intro z
  rw [Basis.reindex_apply, hb]
  rfl

end GriffinIdealExpression

namespace UntruncatedIdealExpression

variable {ι : Type*} [Finite ι] [Nonempty ι] {n : ℕ}

def finiteSum (E : ι → UntruncatedIdealExpression n) : UntruncatedIdealExpression n :=
  finiteExpressionFold .sum E

def finiteIntersection (E : ι → UntruncatedIdealExpression n) :
    UntruncatedIdealExpression n :=
  finiteExpressionFold .intersection E

theorem finiteSum_ideal_le_iff (R : Type*) [CommRing R]
    (E : ι → UntruncatedIdealExpression n) (I : Ideal (PolynomialRing n R)) :
    (finiteSum E).ideal R ≤ I ↔ ∀ j, (E j).ideal R ≤ I :=
  finiteExpressionFold_all UntruncatedIdealExpression.sum E (fun e => e.ideal R ≤ I)
    (fun _ _ => sup_le_iff)

theorem le_finiteIntersection_ideal_iff (R : Type*) [CommRing R]
    (E : ι → UntruncatedIdealExpression n) (I : Ideal (PolynomialRing n R)) :
    I ≤ (finiteIntersection E).ideal R ↔ ∀ j, I ≤ (E j).ideal R :=
  finiteExpressionFold_all UntruncatedIdealExpression.intersection E (fun e => I ≤ e.ideal R)
    (fun _ _ => le_inf_iff)

theorem finiteSum_ideal (R : Type*) [CommRing R]
    (E : ι → UntruncatedIdealExpression n) :
    (finiteSum E).ideal R = ⨆ j, (E j).ideal R := by
  apply le_antisymm
  · exact (finiteSum_ideal_le_iff R E _).mpr (fun j => le_iSup (fun j => (E j).ideal R) j)
  · exact iSup_le ((finiteSum_ideal_le_iff R E _).mp le_rfl)

theorem finiteIntersection_ideal (R : Type*) [CommRing R]
    (E : ι → UntruncatedIdealExpression n) :
    (finiteIntersection E).ideal R = ⨅ j, (E j).ideal R := by
  apply le_antisymm
  · exact le_iInf ((le_finiteIntersection_ideal_iff R E _).mp le_rfl)
  · exact (le_finiteIntersection_ideal_iff R E _).mpr
      (fun j => iInf_le (fun j => (E j).ideal R) j)

theorem mem_finiteSum_eligible (E : ι → UntruncatedIdealExpression n)
    (i : UnboundedHarmonicIndex n) :
    i ∈ (finiteSum E).eligible ↔ ∀ j, i ∈ (E j).eligible :=
  finiteExpressionFold_all UntruncatedIdealExpression.sum E (fun e => i ∈ e.eligible) (fun _ _ => Iff.rfl)

theorem mem_finiteIntersection_eligible (E : ι → UntruncatedIdealExpression n)
    (i : UnboundedHarmonicIndex n) :
    i ∈ (finiteIntersection E).eligible ↔ ∃ j, i ∈ (E j).eligible :=
  finiteExpressionFold_exists UntruncatedIdealExpression.intersection E (fun e => i ∈ e.eligible)
    (fun _ _ => Iff.rfl)

theorem finiteSum_allSize_iff (E : ι → UntruncatedIdealExpression n) (k : ℕ) :
    (finiteSum E).allSize k ↔ ∀ j, (E j).allSize k :=
  finiteExpressionFold_all UntruncatedIdealExpression.sum E (fun e => e.allSize k) (fun _ _ => Iff.rfl)

theorem finiteIntersection_allSize_iff (E : ι → UntruncatedIdealExpression n) (k : ℕ) :
    (finiteIntersection E).allSize k ↔ ∀ j, (E j).allSize k :=
  finiteExpressionFold_all UntruncatedIdealExpression.intersection E (fun e => e.allSize k) (fun _ _ => Iff.rfl)

/-- The actual common-size premise needed by the parameter/CM theorem is
proved for the constructed finite sum, not assumed as an extra premise. -/
theorem finiteSum_allSize (E : ι → UntruncatedIdealExpression n) {k : ℕ}
    (hE : ∀ j, (E j).allSize k) : (finiteSum E).allSize k :=
  (finiteSum_allSize_iff E k).mpr hE

theorem finiteIntersection_allSize (E : ι → UntruncatedIdealExpression n) {k : ℕ}
    (hE : ∀ j, (E j).allSize k) : (finiteIntersection E).allSize k :=
  (finiteIntersection_allSize_iff E k).mpr hE

abbrev FiniteFamilySumIndex (E : ι → UntruncatedIdealExpression n) :=
  Σ i : {i : UnboundedHarmonicIndex n // ∀ j, i ∈ (E j).eligible},
    StandardYoungTableau (YoungDiagram.ofPartition i.val.part)

abbrev FiniteFamilyIntersectionIndex (E : ι → UntruncatedIdealExpression n) :=
  Σ i : {i : UnboundedHarmonicIndex n // ∃ j, i ∈ (E j).eligible},
    StandardYoungTableau (YoungDiagram.ofPartition i.val.part)

def finiteSumVectorEquiv (E : ι → UntruncatedIdealExpression n) :
    (finiteSum E).VectorIndex ≃ FiniteFamilySumIndex E where
  toFun z := ⟨⟨z.1.val, (mem_finiteSum_eligible E z.1.val).mp z.1.property⟩, z.2⟩
  invFun z := ⟨⟨z.1.val, (mem_finiteSum_eligible E z.1.val).mpr z.1.property⟩, z.2⟩
  left_inv z := by rcases z with ⟨⟨i, hi⟩, T⟩; rfl
  right_inv z := by rcases z with ⟨⟨i, hi⟩, T⟩; rfl

def finiteIntersectionVectorEquiv (E : ι → UntruncatedIdealExpression n) :
    (finiteIntersection E).VectorIndex ≃ FiniteFamilyIntersectionIndex E where
  toFun z := ⟨⟨z.1.val, (mem_finiteIntersection_eligible E z.1.val).mp z.1.property⟩, z.2⟩
  invFun z := ⟨⟨z.1.val, (mem_finiteIntersection_eligible E z.1.val).mpr z.1.property⟩, z.2⟩
  left_inv z := by rcases z with ⟨⟨i, hi⟩, T⟩; rfl
  right_inv z := by rcases z with ⟨⟨i, hi⟩, T⟩; rfl

def finiteFamilySum (E : ι → UntruncatedIdealExpression n) (z : FiniteFamilySumIndex E) :
    PolynomialRing n ℂ ⧸ (⨆ j, (E j).ideal ℂ) :=
  Ideal.Quotient.mk _ (unboundedMasterPolynomial z.1.val z.2)

def finiteFamilyIntersection (E : ι → UntruncatedIdealExpression n)
    (z : FiniteFamilyIntersectionIndex E) :
    PolynomialRing n ℂ ⧸ (⨅ j, (E j).ideal ℂ) :=
  Ideal.Quotient.mk _ (unboundedMasterPolynomial z.1.val z.2)

theorem corollary_6_7_finiteSum_basis (E : ι → UntruncatedIdealExpression n) :
    IsSpecifiedBasis (R := ℂ) (finiteFamilySum E) := by
  have H := (finiteSum E).corollary_6_7_basis
  change IsSpecifiedBasis (R := ℂ) (fun z : (finiteSum E).VectorIndex =>
    Ideal.Quotient.mk ((finiteSum E).ideal ℂ) (unboundedMasterPolynomial z.1.val z.2)) at H
  rw [finiteSum_ideal ℂ E] at H
  obtain ⟨b, hb⟩ := H
  refine ⟨b.reindex (finiteSumVectorEquiv E), ?_⟩
  intro z
  rw [Basis.reindex_apply, hb]
  rfl

theorem corollary_6_7_finiteIntersection_basis (E : ι → UntruncatedIdealExpression n) :
    IsSpecifiedBasis (R := ℂ) (finiteFamilyIntersection E) := by
  have H := (finiteIntersection E).corollary_6_7_basis
  change IsSpecifiedBasis (R := ℂ) (fun z : (finiteIntersection E).VectorIndex =>
    Ideal.Quotient.mk ((finiteIntersection E).ideal ℂ)
      (unboundedMasterPolynomial z.1.val z.2)) at H
  rw [finiteIntersection_ideal ℂ E] at H
  obtain ⟨b, hb⟩ := H
  refine ⟨b.reindex (finiteIntersectionVectorEquiv E), ?_⟩
  intro z
  rw [Basis.reindex_apply, hb]
  rfl

end UntruncatedIdealExpression
end HigherSpecht
end
end CanonicalSource5

section CanonicalSource6
/- Source: HigherSpecht/ExpressionSpechtCopies.lean -/



/-!
# The literal Specht copies in ideal-expression quotients

For each actual eligible left tableau and multiplier, the already constructed
complex intertwiner sends the standard Specht basis to the original quotient
polynomials.  Its range is both their full right-tableau span and the cyclic
span of any one of those polynomials.  The prescribed-basis independence
proves injectivity, so the actual subrepresentation is equivalent to the
ordinary complex Specht module and is irreducible.

These statements retain the exact finite-expression eligibility sets.
No character identity, dimension assertion, or representation comparison is
assumed.
-/

noncomputable section

open TauCeti TauCeti.YoungTableau Module MvPolynomial
open scoped Classical

namespace HigherSpecht

theorem expression_linearMap_range_eq_span_basis
    {R V W I : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (b : Basis I R V) (f : V →ₗ[R] W) :
    LinearMap.range f = Submodule.span R (Set.range (fun i => f (b i))) := by
  rw [← Submodule.map_top, ← b.span_eq, Submodule.map_span, ← Set.range_comp']

/-- A nonzero vector in the irreducible source generates the entire image
under the actual group action.  The target need not be finite dimensional. -/
theorem expression_intertwiner_range_eq_span_orbit
    {K G V W : Type*} [Field K] [Group G]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {rho : Representation K G V} {sigma : Representation K G W}
    [rho.IsIrreducible] (f : rho.IntertwiningMap sigma) {v : V} (hv : v ≠ 0) :
    LinearMap.range f.toLinearMap =
      Submodule.span K (Set.range (fun g : G => sigma g (f v))) := by
  let S : Subrepresentation rho :=
    { toSubmodule := Submodule.span K (Set.range (fun g : G => rho g v))
      apply_mem_toSubmodule := by
        intro g w hw
        induction hw using Submodule.span_induction with
        | mem w hw =>
            obtain ⟨h, rfl⟩ := hw
            apply Submodule.subset_span
            refine ⟨g * h, ?_⟩
            change rho (g * h) v = rho g (rho h v)
            rw [map_mul]
            rfl
        | zero => simpa only [map_zero] using (Submodule.zero_mem _)
        | add x y hx hy ihx ihy =>
            simpa only [map_add] using (Submodule.add_mem _ ihx ihy)
        | smul c x hx ih =>
            simpa only [map_smul] using (Submodule.smul_mem _ c ih) }
  have hvS : v ∈ S.toSubmodule := by
    change v ∈ Submodule.span K (Set.range (fun g : G => rho g v))
    exact Submodule.subset_span ⟨1, by simp⟩
  have hS : S = ⊤ := (eq_bot_or_eq_top S).resolve_left (by
    intro h
    have hz : v ∈ (⊥ : Submodule K V) := by
      change v ∈ (⊥ : Subrepresentation rho).toSubmodule
      rw [← h]
      exact hvS
    exact hv (by simpa only [Submodule.mem_bot] using hz))
  have hspan : Submodule.span K (Set.range (fun g : G => rho g v)) = ⊤ :=
    congrArg Subrepresentation.toSubmodule hS
  rw [← Submodule.map_top, ← hspan, Submodule.map_span, ← Set.range_comp']
  exact congrArg (fun z : G → W => Submodule.span K (Set.range z))
    (funext (fun g => Representation.IntertwiningMap.isIntertwining rho sigma f g v))

namespace GriffinIdealExpression

variable {n s : ℕ} (e : GriffinIdealExpression n s)

/-- The actual range of the existing fixed-left-tableau polynomial map. -/
def fixedSpechtCopy (i : FiniteHarmonicIndex n s) :
    Subrepresentation (quotientRepresentation (e.ideal ℂ) (e.permutationStable ℂ)) :=
  (e.complexIntertwiner i).range

theorem fixedSpechtCopy_span (i : FiniteHarmonicIndex n s) :
    (e.fixedSpechtCopy i).toSubmodule =
      Submodule.span ℂ (Set.range
        (fun T : StandardYoungTableau (YoungDiagram.ofPartition i.part) =>
          Ideal.Quotient.mk (e.ideal ℂ) (finiteMasterPolynomial i T))) := by
  change LinearMap.range (e.complexIntertwiner i).toLinearMap = _
  rw [expression_linearMap_range_eq_span_basis (complexSpechtStandardBasis i.part)]
  simp only [Representation.IntertwiningMap.toLinearMap_apply, e.complexIntertwiner_standard]

theorem complexIntertwiner_ne_zero (hs : 0 < s)
    (i : FiniteHarmonicIndex n s) (hi : i ∈ e.eligible) :
    e.complexIntertwiner i ≠ 0 := by
  let T := StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition i.part)
  intro hz
  apply (e.family_linearIndependent hs).ne_zero (⟨⟨i, hi⟩, T⟩ : e.VectorIndex)
  calc
    e.family ℂ ⟨⟨i, hi⟩, T⟩ =
        e.complexIntertwiner i (complexSpechtStandardBasis i.part T) :=
      (e.complexIntertwiner_standard i T).symm
    _ = 0 := by rw [hz]; rfl

def fixedSpechtCopyEquiv (hs : 0 < s)
    (i : FiniteHarmonicIndex n s) (hi : i ∈ e.eligible) :
    Representation.Equiv (spechtModuleℂ i.part).ρ (e.fixedSpechtCopy i).toRepresentation := by
  letI : Representation.IsIrreducible (spechtModuleℂ i.part).ρ :=
    (FDRep.simple_iff_isIrreducible (spechtModuleℂ i.part)).mp inferInstance
  have hf : Function.Injective (e.complexIntertwiner i) :=
    (Representation.IsIrreducible.injective_or_eq_zero _).resolve_right
      (e.complexIntertwiner_ne_zero hs i hi)
  exact (e.complexIntertwiner i).equivOfRange hf rfl

theorem fixedSpechtCopy_cyclic (i : FiniteHarmonicIndex n s)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) :
    (e.fixedSpechtCopy i).toSubmodule =
      Submodule.span ℂ (Set.range (fun g : Equiv.Perm (Fin n) =>
        quotientRepresentation (e.ideal ℂ) (e.permutationStable ℂ) g
          (Ideal.Quotient.mk (e.ideal ℂ) (finiteMasterPolynomial i T)))) := by
  letI : Representation.IsIrreducible (spechtModuleℂ i.part).ρ :=
    (FDRep.simple_iff_isIrreducible (spechtModuleℂ i.part)).mp inferInstance
  change LinearMap.range (e.complexIntertwiner i).toLinearMap = _
  have h := expression_intertwiner_range_eq_span_orbit (e.complexIntertwiner i)
    ((complexSpechtStandardBasis i.part).linearIndependent.ne_zero T)
  simpa only [e.complexIntertwiner_standard] using h

/-- The higher-Specht assertion in Corollary 5.3 for every actual eligible
copy in an arbitrary finite sum/intersection expression. -/
theorem corollary_5_3_specht_copy (hs : 0 < s)
    (i : FiniteHarmonicIndex n s) (hi : i ∈ e.eligible) :
    (e.fixedSpechtCopy i).toSubmodule =
        Submodule.span ℂ (Set.range
          (fun T : StandardYoungTableau (YoungDiagram.ofPartition i.part) =>
            Ideal.Quotient.mk (e.ideal ℂ) (finiteMasterPolynomial i T))) ∧
      (∀ T : StandardYoungTableau (YoungDiagram.ofPartition i.part),
        (e.fixedSpechtCopy i).toSubmodule =
          Submodule.span ℂ (Set.range (fun g : Equiv.Perm (Fin n) =>
            quotientRepresentation (e.ideal ℂ) (e.permutationStable ℂ) g
              (Ideal.Quotient.mk (e.ideal ℂ) (finiteMasterPolynomial i T))))) ∧
      (e.fixedSpechtCopy i).toRepresentation.IsIrreducible ∧
      Nonempty (Representation.Equiv (spechtModuleℂ i.part).ρ (e.fixedSpechtCopy i).toRepresentation) := by
  letI : Representation.IsIrreducible (spechtModuleℂ i.part).ρ :=
    (FDRep.simple_iff_isIrreducible (spechtModuleℂ i.part)).mp inferInstance
  exact ⟨e.fixedSpechtCopy_span i, e.fixedSpechtCopy_cyclic i,
    irreducible_of_representation_equiv (e.fixedSpechtCopyEquiv hs i hi),
    ⟨e.fixedSpechtCopyEquiv hs i hi⟩⟩

end GriffinIdealExpression

namespace UntruncatedIdealExpression

variable {n : ℕ} (e : UntruncatedIdealExpression n)

/-- The actual range of the existing unbounded polynomial map. -/
def fixedSpechtCopy (i : UnboundedHarmonicIndex n) :
    Subrepresentation (quotientRepresentation (e.ideal ℂ) (e.permutationStable ℂ)) :=
  (e.complexIntertwiner i).range

theorem fixedSpechtCopy_span (i : UnboundedHarmonicIndex n) :
    (e.fixedSpechtCopy i).toSubmodule =
      Submodule.span ℂ (Set.range
        (fun T : StandardYoungTableau (YoungDiagram.ofPartition i.part) =>
          Ideal.Quotient.mk (e.ideal ℂ) (unboundedMasterPolynomial i T))) := by
  change LinearMap.range (e.complexIntertwiner i).toLinearMap = _
  rw [expression_linearMap_range_eq_span_basis (complexSpechtStandardBasis i.part)]
  simp only [Representation.IntertwiningMap.toLinearMap_apply, e.complexIntertwiner_standard]

theorem complexIntertwiner_ne_zero (i : UnboundedHarmonicIndex n) (hi : i ∈ e.eligible) :
    e.complexIntertwiner i ≠ 0 := by
  let T := StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition i.part)
  intro hz
  apply e.family_linearIndependent.ne_zero (⟨⟨i, hi⟩, T⟩ : e.VectorIndex)
  calc
    e.family ℂ ⟨⟨i, hi⟩, T⟩ =
        e.complexIntertwiner i (complexSpechtStandardBasis i.part T) :=
      (e.complexIntertwiner_standard i T).symm
    _ = 0 := by rw [hz]; rfl

def fixedSpechtCopyEquiv (i : UnboundedHarmonicIndex n) (hi : i ∈ e.eligible) :
    Representation.Equiv (spechtModuleℂ i.part).ρ (e.fixedSpechtCopy i).toRepresentation := by
  letI : Representation.IsIrreducible (spechtModuleℂ i.part).ρ :=
    (FDRep.simple_iff_isIrreducible (spechtModuleℂ i.part)).mp inferInstance
  have hf : Function.Injective (e.complexIntertwiner i) :=
    (Representation.IsIrreducible.injective_or_eq_zero _).resolve_right
      (e.complexIntertwiner_ne_zero i hi)
  exact (e.complexIntertwiner i).equivOfRange hf rfl

theorem fixedSpechtCopy_cyclic (i : UnboundedHarmonicIndex n)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) :
    (e.fixedSpechtCopy i).toSubmodule =
      Submodule.span ℂ (Set.range (fun g : Equiv.Perm (Fin n) =>
        quotientRepresentation (e.ideal ℂ) (e.permutationStable ℂ) g
          (Ideal.Quotient.mk (e.ideal ℂ) (unboundedMasterPolynomial i T)))) := by
  letI : Representation.IsIrreducible (spechtModuleℂ i.part).ρ :=
    (FDRep.simple_iff_isIrreducible (spechtModuleℂ i.part)).mp inferInstance
  change LinearMap.range (e.complexIntertwiner i).toLinearMap = _
  have h := expression_intertwiner_range_eq_span_orbit (e.complexIntertwiner i)
    ((complexSpechtStandardBasis i.part).linearIndependent.ne_zero T)
  simpa only [e.complexIntertwiner_standard] using h

/-- The higher-Specht assertion in Corollary 6.7, without a truncation,
degree bound, or common partition-size hypothesis. -/
theorem corollary_6_7_specht_copy
    (i : UnboundedHarmonicIndex n) (hi : i ∈ e.eligible) :
    (e.fixedSpechtCopy i).toSubmodule =
        Submodule.span ℂ (Set.range
          (fun T : StandardYoungTableau (YoungDiagram.ofPartition i.part) =>
            Ideal.Quotient.mk (e.ideal ℂ) (unboundedMasterPolynomial i T))) ∧
      (∀ T : StandardYoungTableau (YoungDiagram.ofPartition i.part),
        (e.fixedSpechtCopy i).toSubmodule =
          Submodule.span ℂ (Set.range (fun g : Equiv.Perm (Fin n) =>
            quotientRepresentation (e.ideal ℂ) (e.permutationStable ℂ) g
              (Ideal.Quotient.mk (e.ideal ℂ) (unboundedMasterPolynomial i T))))) ∧
      (e.fixedSpechtCopy i).toRepresentation.IsIrreducible ∧
      Nonempty (Representation.Equiv (spechtModuleℂ i.part).ρ (e.fixedSpechtCopy i).toRepresentation) := by
  letI : Representation.IsIrreducible (spechtModuleℂ i.part).ρ :=
    (FDRep.simple_iff_isIrreducible (spechtModuleℂ i.part)).mp inferInstance
  exact ⟨e.fixedSpechtCopy_span i, e.fixedSpechtCopy_cyclic i,
    irreducible_of_representation_equiv (e.fixedSpechtCopyEquiv i hi),
    ⟨e.fixedSpechtCopyEquiv i hi⟩⟩

end UntruncatedIdealExpression
end HigherSpecht
end
end CanonicalSource6

section CanonicalSource7
/- Source: HigherSpecht/FiniteFamilySpechtCopies.lean -/



/-!
# Actual Specht copies for arbitrary finite families of defining ideals

The predicate below spells out the literal quotient span, the actual
permutation orbit, and an equivalence with the ordinary complex Specht
module.  Its permutation-stability proof is part of the conclusion.
The two final theorems obtain these conclusions from the actual finite-family
fold and its proved ideal/eligibility equalities; they add no input
representation hypothesis.
-/

noncomputable section

open TauCeti TauCeti.YoungTableau Module MvPolynomial
open scoped Classical

namespace HigherSpecht

/-- The literal fixed-left polynomial span is an irreducible Specht copy,
and any one of its prescribed right-tableau vectors generates it. -/
def IsLiteralQuotientSpechtCopy {n : ℕ}
    (J : Ideal (PolynomialRing n ℂ)) (part : n.Partition)
    (p : StandardYoungTableau (YoungDiagram.ofPartition part) → PolynomialRing n ℂ) : Prop :=
  ∃ hJ : PermutationStable J,
    ∃ V : Subrepresentation (quotientRepresentation J hJ),
      V.toSubmodule =
        Submodule.span ℂ (Set.range (fun T => Ideal.Quotient.mk J (p T))) ∧
      (∀ T : StandardYoungTableau (YoungDiagram.ofPartition part),
        V.toSubmodule = Submodule.span ℂ
          (Set.range (fun g : Equiv.Perm (Fin n) =>
            quotientRepresentation J hJ g (Ideal.Quotient.mk J (p T))))) ∧
      V.toRepresentation.IsIrreducible ∧
      Nonempty (Representation.Equiv (spechtModuleℂ part).ρ V.toRepresentation)

theorem griffin_specht_copy_of_expression_eq {n s : ℕ}
    (e : GriffinIdealExpression n s) (hs : 0 < s)
    (J : Ideal (PolynomialRing n ℂ)) (hJ : e.ideal ℂ = J)
    (i : FiniteHarmonicIndex n s) (hi : i ∈ e.eligible) :
    IsLiteralQuotientSpechtCopy J i.part (finiteMasterPolynomial i) := by
  subst J
  exact ⟨e.permutationStable ℂ, e.fixedSpechtCopy i,
    e.corollary_5_3_specht_copy hs i hi⟩

theorem untruncated_specht_copy_of_expression_eq {n : ℕ}
    (e : UntruncatedIdealExpression n)
    (J : Ideal (PolynomialRing n ℂ)) (hJ : e.ideal ℂ = J)
    (i : UnboundedHarmonicIndex n) (hi : i ∈ e.eligible) :
    IsLiteralQuotientSpechtCopy J i.part (unboundedMasterPolynomial i) := by
  subst J
  exact ⟨e.permutationStable ℂ, e.fixedSpechtCopy i,
    e.corollary_6_7_specht_copy i hi⟩

/-- The actual higher-Specht copies for the literal finite intersections
and sums in Corollary 5.3.  Intersections retain the union of eligibility;
sums retain its intersection. -/
theorem corollary_5_3_finite_family_specht_copies
    {ι : Type*} [Finite ι] [Nonempty ι] {n s : ℕ} (hs : 0 < s)
    (A : ι → BoundedGriffinShape n s) :
    (∀ i : FiniteHarmonicIndex n s,
      (∃ j, i.toUnboundedHarmonicIndex.eligible (A j).diagram (A j).card_le) →
        IsLiteralQuotientSpechtCopy
          (⨅ j, griffinIdeal ℂ n (A j).diagram s) i.part (finiteMasterPolynomial i)) ∧
    (∀ i : FiniteHarmonicIndex n s,
      (∀ j, i.toUnboundedHarmonicIndex.eligible (A j).diagram (A j).card_le) →
        IsLiteralQuotientSpechtCopy
          (⨆ j, griffinIdeal ℂ n (A j).diagram s) i.part (finiteMasterPolynomial i)) := by
  constructor
  · intro i hi
    apply griffin_specht_copy_of_expression_eq
      (GriffinIdealExpression.finiteIntersection (fun j => .atom (A j))) hs
      (⨅ j, griffinIdeal ℂ n (A j).diagram s)
      (GriffinIdealExpression.finiteIntersection_ideal ℂ (fun j => .atom (A j))) i
    exact (GriffinIdealExpression.mem_finiteIntersection_eligible
      (fun j => .atom (A j)) i).mpr hi
  · intro i hi
    apply griffin_specht_copy_of_expression_eq
      (GriffinIdealExpression.finiteSum (fun j => .atom (A j))) hs
      (⨆ j, griffinIdeal ℂ n (A j).diagram s)
      (GriffinIdealExpression.finiteSum_ideal ℂ (fun j => .atom (A j))) i
    exact (GriffinIdealExpression.mem_finiteSum_eligible
      (fun j => .atom (A j)) i).mpr hi

/-- The corresponding literal finite-family assertion in Corollary 6.7
has no truncation, degree bound, or common partition-size hypothesis. -/
theorem corollary_6_7_finite_family_specht_copies
    {ι : Type*} [Finite ι] [Nonempty ι] {n : ℕ}
    (A : ι → BoundedUntruncatedShape n) :
    (∀ i : UnboundedHarmonicIndex n,
      (∃ j, i.eligible (A j).diagram (A j).card_le) →
        IsLiteralQuotientSpechtCopy
          (⨅ j, untruncatedIdeal ℂ n (A j).diagram) i.part (unboundedMasterPolynomial i)) ∧
    (∀ i : UnboundedHarmonicIndex n,
      (∀ j, i.eligible (A j).diagram (A j).card_le) →
        IsLiteralQuotientSpechtCopy
          (⨆ j, untruncatedIdeal ℂ n (A j).diagram) i.part (unboundedMasterPolynomial i)) := by
  constructor
  · intro i hi
    apply untruncated_specht_copy_of_expression_eq
      (UntruncatedIdealExpression.finiteIntersection (fun j => .atom (A j)))
      (⨅ j, untruncatedIdeal ℂ n (A j).diagram)
      (UntruncatedIdealExpression.finiteIntersection_ideal ℂ (fun j => .atom (A j))) i
    exact (UntruncatedIdealExpression.mem_finiteIntersection_eligible
      (fun j => .atom (A j)) i).mpr hi
  · intro i hi
    apply untruncated_specht_copy_of_expression_eq
      (UntruncatedIdealExpression.finiteSum (fun j => .atom (A j)))
      (⨆ j, untruncatedIdeal ℂ n (A j).diagram)
      (UntruncatedIdealExpression.finiteSum_ideal ℂ (fun j => .atom (A j))) i
    exact (UntruncatedIdealExpression.mem_finiteSum_eligible
      (fun j => .atom (A j)) i).mpr hi

end HigherSpecht
end
end CanonicalSource7

section CanonicalSource8
/- Source: HigherSpecht/DividedHarmonicDuality.lean -/



/-!
# Quotient duality for the actual divided-power inverse system

The coefficient pairing is perfect for an ideal containing coordinate
powers. Its inverse is the finite sum of ordinary monomial symbols with the
specified dual coefficients. No factorial or characteristic hypothesis
occurs: these monomials represent divided-power symbols, acted on by the
explicit contraction operators defined in `Apolar`.
-/

noncomputable section
open MvPolynomial Finset Module
open scoped Classical

namespace HigherSpecht

variable {R : Type*} [CommRing R]

def dividedApolarFunctional {n : ℕ} (w : PolynomialRing n R) :
    Module.Dual R (PolynomialRing n R) := contractionCoefficient w 0

@[simp] theorem dividedApolarFunctional_apply {n : ℕ} (w f : PolynomialRing n R) :
    dividedApolarFunctional w f = (dividedAction f w).coeff 0 := rfl

@[simp] theorem dividedApolarFunctional_monomial {n : ℕ}
    (w : PolynomialRing n R) (a : Fin n →₀ ℕ) (c : R) :
    dividedApolarFunctional w (MvPolynomial.monomial a c) = c * w.coeff a := by
  simp only [dividedApolarFunctional_apply, dividedAction_monomial,
    LinearMap.smul_apply, MvPolynomial.coeff_smul, coeff_contractMonomial,
    zero_add, smul_eq_mul]

def dividedApolarRepresenter (n : ℕ) :
    PolynomialRing n R →ₗ[R] Module.Dual R (PolynomialRing n R) where
  toFun := dividedApolarFunctional
  map_add' p q := contractionCoefficient_add p q 0
  map_smul' c p := contractionCoefficient_smul c p 0

theorem dividedApolarRepresenter_injective (n : ℕ) :
    Function.Injective (dividedApolarRepresenter (R := R) n) := by
  intro p q hpq
  apply MvPolynomial.ext
  intro a
  have h := DFunLike.congr_fun hpq (MvPolynomial.monomial a 1)
  change dividedApolarFunctional p (MvPolynomial.monomial a 1) =
    dividedApolarFunctional q (MvPolynomial.monomial a 1) at h
  simpa only [dividedApolarFunctional_monomial, one_mul] using h

theorem mem_dividedHarmonics_iff_apolar {n : ℕ} (I : Ideal (PolynomialRing n R))
    (p : PolynomialRing n R) :
    p ∈ dividedHarmonics I ↔ ∀ f ∈ I, dividedApolarFunctional p f = 0 := by
  constructor
  · intro hp f hf
    rw [dividedApolarFunctional_apply, hp f hf, MvPolynomial.coeff_zero, Finsupp.zero_apply]
  · intro hp f hf
    apply MvPolynomial.ext
    intro a
    have h := hp (MvPolynomial.monomial a 1 * f) (I.mul_mem_left _ hf)
    rw [dividedApolarFunctional_apply, dividedAction_mul] at h
    simpa only [dividedAction_monomial, one_smul, coeff_contractMonomial,
      zero_add, MvPolynomial.coeff_zero, Finsupp.zero_apply] using h

def dividedHarmonicQuotientDual {n : ℕ} (I : Ideal (PolynomialRing n R)) :
    dividedHarmonics I →ₗ[R] Module.Dual R (PolynomialRing n R ⧸ I) where
  toFun p := (I.restrictScalars R).liftQ (dividedApolarFunctional p.val)
    (fun f hf => (mem_dividedHarmonics_iff_apolar I p.val).mp p.property f hf)
  map_add' p q := by
    apply LinearMap.ext
    intro z
    refine Submodule.Quotient.induction_on (I.restrictScalars R) z ?_
    intro f
    change dividedApolarFunctional (p.val + q.val) f =
      dividedApolarFunctional p.val f + dividedApolarFunctional q.val f
    exact DFunLike.congr_fun (contractionCoefficient_add p.val q.val 0) f
  map_smul' c p := by
    apply LinearMap.ext
    intro z
    refine Submodule.Quotient.induction_on (I.restrictScalars R) z ?_
    intro f
    change dividedApolarFunctional (c • p.val) f = c • dividedApolarFunctional p.val f
    exact DFunLike.congr_fun (contractionCoefficient_smul c p.val 0) f

@[simp] theorem dividedHarmonicQuotientDual_mk {n : ℕ}
    (I : Ideal (PolynomialRing n R)) (p : dividedHarmonics I) (f : PolynomialRing n R) :
    dividedHarmonicQuotientDual I p (Ideal.Quotient.mk I f) = dividedApolarFunctional p.val f := rfl

theorem dividedHarmonicQuotientDual_injective {n : ℕ} (I : Ideal (PolynomialRing n R)) :
    Function.Injective (dividedHarmonicQuotientDual I) := by
  intro p q hpq
  apply Subtype.ext
  apply dividedApolarRepresenter_injective n
  apply LinearMap.ext
  intro f
  exact DFunLike.congr_fun hpq (Ideal.Quotient.mk I f)

abbrev DividedSupportBox (n s : ℕ) := {a : Fin n →₀ ℕ // ∀ i, a i < s}

instance finiteDividedSupportBox (n s : ℕ) : Finite (DividedSupportBox n s) := by
  apply Finite.of_injective
    (fun a : DividedSupportBox n s => fun i => (⟨a.val i, a.property i⟩ : Fin s))
  intro a b h
  apply Subtype.ext
  ext i
  exact congrArg Fin.val (congrFun h i)

noncomputable instance fintypeDividedSupportBox (n s : ℕ) :
    Fintype (DividedSupportBox n s) := Fintype.ofFinite _

def boundedDividedRepresentative {n : ℕ} (s : ℕ)
    (L : Module.Dual R (PolynomialRing n R)) : PolynomialRing n R :=
  ∑ a : DividedSupportBox n s, MvPolynomial.monomial a.val (L (MvPolynomial.monomial a.val 1))

theorem boundedDividedRepresentative_coeff {n : ℕ} (s : ℕ)
    (L : Module.Dual R (PolynomialRing n R)) (a : Fin n →₀ ℕ) :
    (boundedDividedRepresentative s L).coeff a =
      if ∀ i, a i < s then L (MvPolynomial.monomial a 1) else 0 := by
  rw [boundedDividedRepresentative, MvPolynomial.coeff_sum]
  split_ifs with ha
  · rw [Finset.sum_eq_single (⟨a, ha⟩ : DividedSupportBox n s)]
    · simp
    · intro b hb hba
      rw [MvPolynomial.coeff_monomial, if_neg]
      exact fun h => hba (Subtype.ext h)
    · simp
  · apply Finset.sum_eq_zero
    intro b hb
    rw [MvPolynomial.coeff_monomial, if_neg]
    exact fun h => ha (h ▸ b.property)

theorem monomial_mem_of_coordinate_power_bound {n s : ℕ}
    (I : Ideal (PolynomialRing n R)) (hpower : powerIdeal R n s ≤ I)
    (a : Fin n →₀ ℕ) (i : Fin n) (hi : s ≤ a i) :
    MvPolynomial.monomial a (1 : R) ∈ I := by
  have hle : Finsupp.single i s ≤ a := Finsupp.single_le_iff.mpr hi
  have hx : (MvPolynomial.X i : PolynomialRing n R) ^ s ∈ I :=
    hpower (Ideal.subset_span ⟨i, rfl⟩)
  have h := I.mul_mem_left (MvPolynomial.monomial (a - Finsupp.single i s) 1) hx
  simpa only [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul,
    one_mul, tsub_add_cancel_of_le hle] using h

theorem boundedDividedRepresentative_pairing {n s : ℕ}
    (I : Ideal (PolynomialRing n R)) (hpower : powerIdeal R n s ≤ I)
    (L : Module.Dual R (PolynomialRing n R)) (hL : ∀ f ∈ I, L f = 0)
    (f : PolynomialRing n R) :
    dividedApolarFunctional (boundedDividedRepresentative s L) f = L f := by
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => rw [map_add, map_add, hf, hg]
  | monomial a c =>
      have hm : (MvPolynomial.monomial a c : PolynomialRing n R) =
          c • MvPolynomial.monomial a 1 := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [hm, map_smul, map_smul, dividedApolarFunctional_monomial,
        one_mul, boundedDividedRepresentative_coeff]
      congr 1
      split_ifs with ha
      · rfl
      · obtain ⟨i, hi⟩ := not_forall.mp ha
        exact (hL _ (monomial_mem_of_coordinate_power_bound I hpower a i
          (le_of_not_gt hi))).symm

theorem dividedHarmonicQuotientDual_surjective {n s : ℕ}
    (I : Ideal (PolynomialRing n R)) (hpower : powerIdeal R n s ≤ I) :
    Function.Surjective (dividedHarmonicQuotientDual I) := by
  intro L
  let Lp := L.comp (Ideal.Quotient.mkₐ R I).toLinearMap
  have hLp : ∀ f ∈ I, Lp f = 0 := by
    intro f hf
    change L (Ideal.Quotient.mk I f) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]
  let p := boundedDividedRepresentative s Lp
  have hp : p ∈ dividedHarmonics I := by
    apply (mem_dividedHarmonics_iff_apolar I p).mpr
    intro f hf
    rw [boundedDividedRepresentative_pairing I hpower Lp hLp, hLp f hf]
  refine ⟨⟨p, hp⟩, ?_⟩
  apply LinearMap.ext
  intro z
  refine Submodule.Quotient.induction_on (I.restrictScalars R) z ?_
  intro f
  exact boundedDividedRepresentative_pairing I hpower Lp hLp f

def dividedHarmonicQuotientDualEquiv {n s : ℕ}
    (I : Ideal (PolynomialRing n R)) (hpower : powerIdeal R n s ≤ I) :
    dividedHarmonics I ≃ₗ[R] Module.Dual R (PolynomialRing n R ⧸ I) :=
  LinearEquiv.ofBijective (dividedHarmonicQuotientDual I)
    ⟨dividedHarmonicQuotientDual_injective I, dividedHarmonicQuotientDual_surjective I hpower⟩

theorem dividedApolarFunctional_mul {n : ℕ} (w f g : PolynomialRing n R) :
    dividedApolarFunctional w (f * g) = dividedApolarFunctional (dividedAction f w) g := by
  simp only [dividedApolarFunctional_apply, dividedAction_mul, dividedAction_comm f g]

end HigherSpecht
end
end CanonicalSource8

section CanonicalSource9
/- Source: HigherSpecht/SpringerInverseSystem.lean -/



/-!
# The Springer inverse system is generated by its actual top alternants

For a full filling there are no outside variables. Thus the complete
column-contraction theorem specializes to contractions of the degree
`n(mu)` alternants, with no exponent parameter remaining.  Coordinate
nilpotence is derived from the literal global elementary relations and
the coordinate characteristic polynomial; it supplies the finite duality
bound in every characteristic, including the empty diagram.
-/

noncomputable section
open TauCeti TauCeti.YoungTableau MvPolynomial Finset Module
open scoped Classical

namespace HigherSpecht

variable {R : Type*} [CommRing R]

def springerTopDegree (mu : YoungDiagram) : ℕ := ∑ c ∈ mu.cells, c.1

theorem springerTopDegree_eq_sum_rows (mu : YoungDiagram) :
    springerTopDegree mu = ∑ r ∈ Finset.range (mu.colLen 0), r * mu.rowLen r := by
  unfold springerTopDegree
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun c : ℕ × ℕ => c.1)
    (t := Finset.range (mu.colLen 0))
    (fun c hc => Finset.mem_range.mpr (YoungDiagram.lt_colLen_zero_of_mem hc))
    (fun c : ℕ × ℕ => c.1)]
  apply Finset.sum_congr rfl
  intro r hr
  have hrow : (mu.cells.filter (fun c => c.1 = r)).card = mu.rowLen r :=
    by rw [YoungDiagram.rowLen_eq_card, YoungDiagram.row]
  rw [show (∑ c ∈ mu.cells with c.1 = r, c.1) =
      ∑ _c ∈ mu.cells with _c.1 = r, r from
      Finset.sum_congr rfl (fun c hc => (Finset.mem_filter.mp hc).2)]
  simp only [Finset.sum_const, smul_eq_mul, hrow, Nat.mul_comm]

theorem springerCoordinate_characteristic (mu : YoungDiagram) :
    coordinateCharacteristic Finset.univ
        (fun i : Fin mu.card => Ideal.Quotient.mk (springerIdeal R mu) (MvPolynomial.X i)) =
      Polynomial.X ^ mu.card := by
  simpa only [Finset.card_univ, Fintype.card_fin] using
    coordinateCharacteristic_eq_X_pow_of_elementary Finset.univ
      (fun i : Fin mu.card => Ideal.Quotient.mk (springerIdeal R mu) (MvPolynomial.X i))
      (fun d hd => by
        have hm : elementaryOn (R := R) (Finset.univ : Finset (Fin mu.card)) d ∈
            springerIdeal R mu :=
          elementaryOn_univ_mem_untruncated_of_parameter_lt (m := 0) (by omega) hd
        simpa only [elementaryValue, elementaryOn, map_sum, map_prod] using
          Ideal.Quotient.eq_zero_iff_mem.mpr hm)

theorem springer_coordinate_pow_card_eq_zero (mu : YoungDiagram) (i : Fin mu.card) :
    (Ideal.Quotient.mk (springerIdeal R mu) (MvPolynomial.X i)) ^ mu.card = 0 := by
  have h := coordinateCharacteristic_eval_root Finset.univ
    (fun j : Fin mu.card => Ideal.Quotient.mk (springerIdeal R mu) (MvPolynomial.X j))
    (Finset.mem_univ i)
  rw [springerCoordinate_characteristic, Polynomial.eval_pow, Polynomial.eval_X] at h
  exact h

theorem powerIdeal_le_springerIdeal (mu : YoungDiagram) :
    powerIdeal R mu.card (mu.card + 1) ≤ springerIdeal R mu := by
  apply Ideal.span_le.mpr
  rintro p ⟨i, rfl⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_pow, pow_succ, springer_coordinate_pow_card_eq_zero, zero_mul]

def springerDividedDualEquiv (K : Type*) [Field K] (mu : YoungDiagram) :
    dividedHarmonics (springerIdeal K mu) ≃ₗ[K] Module.Dual K (SpringerRing K mu) :=
  dividedHarmonicQuotientDualEquiv (springerIdeal K mu) (powerIdeal_le_springerIdeal mu)

def topColumnAlternant {mu : YoungDiagram} (U : YoungTableau mu) : PolynomialRing mu.card R :=
  columnWitness U.toEmbedding 1

theorem columnWitness_full_eq_top {mu : YoungDiagram}
    (U : ↥mu.cells ↪ Fin mu.card) (s : ℕ) :
    ∃ T : YoungTableau mu, columnWitness (R := R) U s = topColumnAlternant T := by
  have hbij : Function.Bijective U :=
    (Fintype.bijective_iff_injective_and_card U).mpr ⟨U.injective, by
      simp only [Fintype.card_coe, Fintype.card_fin, YoungDiagram.card]⟩
  let T : YoungTableau mu := Equiv.ofBijective U hbij
  refine ⟨T, ?_⟩
  change columnWitness (R := R) T.toEmbedding s = columnWitness T.toEmbedding 1
  simp only [columnWitness, outsidePower_equiv, mul_one]

theorem fullFillingExponent_degree {mu : YoungDiagram} (T : YoungTableau mu) :
    (fullFillingExponent T).degree = springerTopDegree mu := by
  rw [Finsupp.degree_eq_sum]
  change (∑ i : Fin mu.card, (T.symm i).val.1) = _
  calc
    (∑ i : Fin mu.card, (T.symm i).val.1) =
        ∑ c : ↥mu.cells, c.val.1 := Equiv.sum_comp T.symm (fun c : ↥mu.cells => c.val.1)
    _ = springerTopDegree mu := by
      simpa only [springerTopDegree] using
        (Finset.sum_coe_sort mu.cells (fun c : ℕ × ℕ => c.1))

theorem topColumnAlternant_isHomogeneous {mu : YoungDiagram} (T : YoungTableau mu) :
    (topColumnAlternant (R := R) T).IsHomogeneous (springerTopDegree mu) := by
  rw [topColumnAlternant, ← coefficientWitness_fullFilling_eq_columnWitness T 1,
    coefficientWitness_eq_columnAlternate]
  apply columnAlternate_isHomogeneous
  exact MvPolynomial.isHomogeneous_monomial 1 (fullFillingExponent_degree T)

theorem topColumnAlternant_mem_harmonics {mu : YoungDiagram} (T : YoungTableau mu) :
    topColumnAlternant (R := R) T ∈ dividedHarmonics (springerIdeal R mu) :=
  columnWitness_mem_untruncatedHarmonics T.toEmbedding 1

def topColumnContractionSpan (R : Type*) [CommRing R] (mu : YoungDiagram) :
    Submodule R (PolynomialRing mu.card R) :=
  Submodule.span R {w | ∃ (T : YoungTableau mu) (d : Fin mu.card →₀ ℕ),
    w = contractMonomial d (topColumnAlternant T)}

theorem springerHarmonics_eq_topColumnContractions
    (R : Type*) [CommRing R] [Nontrivial R] (mu : YoungDiagram) :
    dividedHarmonics (springerIdeal R mu) = topColumnContractionSpan R mu := by
  rw [springerIdeal, untruncatedHarmonics_eq_columnContractionSpan (R := R) le_rfl]
  apply congrArg (Submodule.span R)
  ext w
  constructor
  · rintro ⟨s, U, d, rfl⟩
    obtain ⟨T, hT⟩ := columnWitness_full_eq_top (R := R) U s
    exact ⟨T, d, by rw [hT]⟩
  · rintro ⟨T, d, rfl⟩
    exact ⟨1, T.toEmbedding, d, rfl⟩

theorem contractMonomial_isHomogeneous {n D : ℕ}
    {w : PolynomialRing n R} (hw : w.IsHomogeneous D) (d : Fin n →₀ ℕ) :
    (contractMonomial d w).IsHomogeneous (D - d.degree) := by
  intro a ha
  have hwd : w.coeff (a + d) ≠ 0 := by simpa only [coeff_contractMonomial] using ha
  have hdegree := hw hwd
  change Finsupp.weight (fun _ : Fin n => (1 : ℕ)) (a + d) = D at hdegree
  rw [← Finsupp.degree_eq_weight_one, map_add] at hdegree
  change Finsupp.weight (fun _ : Fin n => (1 : ℕ)) a = D - d.degree
  rw [← Finsupp.degree_eq_weight_one]
  omega

theorem contractMonomial_eq_zero_of_degree_lt {n D : ℕ}
    {w : PolynomialRing n R} (hw : w.IsHomogeneous D)
    {d : Fin n →₀ ℕ} (hd : D < d.degree) : contractMonomial d w = 0 := by
  apply MvPolynomial.ext
  intro a
  rw [coeff_contractMonomial, MvPolynomial.coeff_zero, Finsupp.zero_apply]
  by_contra hne
  have h := hw hne
  change Finsupp.weight (fun _ : Fin n => (1 : ℕ)) (a + d) = D at h
  rw [← Finsupp.degree_eq_weight_one, map_add] at h
  omega

end HigherSpecht
end
end CanonicalSource9

section CanonicalSource10
/- Source: HigherSpecht/SpringerCommonDecompositions.lean -/



/-!
# Corollary 5.5: the same actual harmonic copies for every Springer ideal

The common vector is the full-prefix, empty-multiplier specialization of
the literal normalized derivative.  The coordinate characteristic identity
proves that the n-th power relations already belong to every Springer ideal.
Eligibility therefore becomes exactly the original catabolizability
dominance condition, with no auxiliary partition remaining.
-/

noncomputable section
open TauCeti TauCeti.YoungTableau Module MvPolynomial Finset
open scoped Classical

namespace HigherSpecht

abbrev SpringerCommonIndex (n : ℕ) :=
  Σ part : n.Partition, StandardYoungTableau (YoungDiagram.ofPartition part)

theorem descentNumber_lt_card {mu : YoungDiagram}
    (S : StandardYoungTableau mu) (hmu : 0 < mu.card) : descentNumber S < mu.card := by
  have h := ascentCount_le (tableauRows S) (mu.card - 1)
  change ascentCount (tableauRows S) (mu.card - 1) < mu.card
  omega

def springerCommonFiniteIndex {n : ℕ} (hn : 0 < n) (z : SpringerCommonIndex n) :
    FiniteHarmonicIndex n n where
  part := z.1
  left := z.2
  multiplier := ⊥
  multiplier_length := by simp
  descents_lt := by
    simpa only [YoungDiagram.card_ofPartition] using
      descentNumber_lt_card z.2 (by simpa only [YoungDiagram.card_ofPartition] using hn)
  multiplier_width := by simp

theorem springerCommonFiniteIndex_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (springerCommonFiniteIndex hn) := by
  intro z w h
  exact congrArg (fun i : FiniteHarmonicIndex n n =>
    (⟨i.part, i.left⟩ : SpringerCommonIndex n)) h

def springerCommonHarmonicVector {n : ℕ} (hn : 0 < n)
    (z : SpringerCommonIndex n) : PolynomialRing n ℂ :=
  finiteCommonHarmonicVector (springerCommonFiniteIndex hn z)

def springerCommonHarmonicCopy {n : ℕ} (hn : 0 < n)
    (z : SpringerCommonIndex n) : Submodule ℂ (PolynomialRing n ℂ) :=
  cyclicPolynomialCopy (springerCommonHarmonicVector hn z)

theorem springerCommonPrefix_full {n : ℕ} (hn : 0 < n) (z : SpringerCommonIndex n) :
    maximalFinitePrefix (springerCommonFiniteIndex hn z) = n := by
  rw [maximalFinitePrefix_eq_untruncated _ (by
    change (columnInsertion z.2).state.shape.colLen 0 ≤ n
    simpa only [YoungDiagram.card_ofPartition] using columnInsertion_height_le_card z.2)]
  simp only [maximalUntruncatedPrefix, springerCommonFiniteIndex,
    YoungDiagram.colLen_bot, Nat.sub_zero]

/-- The exact normalized full-prefix formula (5.1). -/
theorem springerCommonHarmonicVector_formula {n : ℕ} (hn : 0 < n)
    (z : SpringerCommonIndex n) :
    springerCommonHarmonicVector hn z =
      rename (finCongr (YoungDiagram.card_ofPartition z.1))
        (adjointYoungApply (StandardYoungTableau.rowSuperstandard _).toTableau
          (normalizedOrdinaryDerivative
            (griffinWitnessRejection z.2 (StandardYoungTableau.rowSuperstandard _).toTableau
              ⊥ n (YoungDiagram.card_ofPartition z.1).symm.le n)
            (griffinApolarWitness z.2 (StandardYoungTableau.rowSuperstandard _).toTableau
              n (YoungDiagram.card_ofPartition z.1).symm.le n))) := by
  rw [springerCommonHarmonicVector, finiteCommonHarmonicVector_eq_normalized]
  simp only [springerCommonPrefix_full]
  rfl

/-- Transport a full prefix together with its literal cell inclusion. -/
private theorem fullPrefix_transport {μ : YoungDiagram} (S : StandardYoungTableau μ)
    (P : (ν : YoungDiagram) → StandardYoungTableau ν → (↥ν.cells ↪ ↥μ.cells) → Prop)
    (hP : P μ S (Function.Embedding.refl _)) :
    P (prefixShape S μ.card) (prefixTableau S μ.card le_rfl)
      (prefixCellsEmbedding S μ.card) := by
  have transport {ν : YoungDiagram} (Q : StandardYoungTableau ν)
      (e : ↥ν.cells ↪ ↥μ.cells) (hshape : ν = μ) (hQ : HEq Q S)
      (he : ∀ c, (e c).val = c.val) : P ν Q e := by
    subst ν
    cases eq_of_heq hQ
    have heq : e = Function.Embedding.refl _ :=
      Function.Embedding.ext (fun c => Subtype.ext (he c))
    simpa only [heq] using hP
  exact transport _ _ (prefixShape_full S) (prefixTableau_full_heq S) (fun _ => rfl)

/-- At full prefix length the extended witness is exactly the original
column-reading witness. The exterior exponent is irrelevant because every
ambient label belongs to the filling. -/
theorem griffinApolarWitness_full {R : Type*} [CommRing R] {μ : YoungDiagram}
    (S : StandardYoungTableau μ) (T : YoungTableau μ) (s : ℕ) :
    griffinApolarWitness (R := R) S T μ.card le_rfl s = higherSpechtWitness S T := by
  unfold griffinApolarWitness prefixAmbientEmbedding
  refine fullPrefix_transport S
    (fun ν Q e =>
      columnWitness (R := R)
        ((insertionFilling Q Q.toTableau).toEmbedding.trans
          (Q.toTableau.symm.toEmbedding.trans (e.trans T.toEmbedding))) s =
        higherSpechtWitness S T) ?_
  have hf :
      (insertionFilling S S.toTableau).toEmbedding.trans
          (S.toTableau.symm.toEmbedding.trans
            ((Function.Embedding.refl _).trans T.toEmbedding)) =
        (insertionFilling S T).toEmbedding := by
    apply Function.Embedding.ext
    intro c
    change T (S.toTableau.symm
      (S.toTableau (columnScanEquiv μ ((columnInsertion S).filling c)))) =
      T (columnScanEquiv μ ((columnInsertion S).filling c))
    exact congrArg T (S.toTableau.symm_apply_apply _)
  rw [hf]
  exact (coefficientWitness_fullFilling_eq_columnWitness
    (R := R) (insertionFilling S T) s).symm

/-- The full-prefix distinguished exponent is the actual insertion row. -/
theorem griffinWitnessAlpha_full {μ : YoungDiagram}
    (S : StandardYoungTableau μ) (T : YoungTableau μ) (s : ℕ) :
    griffinWitnessAlpha S T μ.card le_rfl s = insertionAlpha S T := by
  unfold griffinWitnessAlpha prefixAmbientEmbedding
  refine fullPrefix_transport S
    (fun ν Q e =>
      embeddedWitnessAlpha
        (Q.toTableau.symm.toEmbedding.trans (e.trans T.toEmbedding))
        (insertionAlpha Q Q.toTableau) s = insertionAlpha S T) ?_
  ext i
  let e := S.toTableau.symm.toEmbedding.trans
    ((Function.Embedding.refl _).trans T.toEmbedding)
  have he : e (S (T.symm i)) = i := by simp [e]
  have ha : insertionAlpha S S.toTableau (S (T.symm i)) = insertionAlpha S T i := by
    simp [insertionAlpha, insertionRow, scanLabelEquiv]
  have h := embeddedWitnessAlpha_inside e (insertionAlpha S S.toTableau) s
    (S (T.symm i))
  rw [he, ha] at h
  exact h

/-- With the empty multiplier, the full-prefix derivative order is exactly
the rejection-count vector of the original column-reading run. -/
theorem griffinWitnessRejection_full {μ : YoungDiagram}
    (S : StandardYoungTableau μ) (T : YoungTableau μ) (s : ℕ) :
    griffinWitnessRejection S T ⊥ μ.card le_rfl s = insertionRejectionExponent S T := by
  rw [griffinWitnessRejection, griffinWitnessAlpha_full]
  ext i
  simp only [Finsupp.tsub_apply, insertionAlpha, insertionRejectionExponent,
    Finsupp.equivFunOnFinite_symm_apply_apply]
  have hb : transportedBoosted S T ⊥ i = transportedCocharge S T i := by
    simp [transportedBoosted, transportedCocharge, boostedFilling,
      boostedLabel, boostLabel, cochargeFilling]
  rw [hb, insertion_row_eq_input_add_rejections]
  omega

/-- Formula (5.1) in the original full-tableau notation: the witness and
derivative order are those of the deterministic column-reading algorithm,
with precisely the factorial normalization used in the manuscript. -/
theorem springerCommonHarmonicVector_literal_formula {n : ℕ} (hn : 0 < n)
    (z : SpringerCommonIndex n) :
    springerCommonHarmonicVector hn z =
      rename (finCongr (YoungDiagram.card_ofPartition z.1))
        (adjointYoungApply (StandardYoungTableau.rowSuperstandard _).toTableau
          (normalizedOrdinaryDerivative
            (insertionRejectionExponent z.2
              (StandardYoungTableau.rowSuperstandard _).toTableau)
            (higherSpechtWitness z.2
              (StandardYoungTableau.rowSuperstandard _).toTableau))) := by
  let T := (StandardYoungTableau.rowSuperstandard
    (YoungDiagram.ofPartition z.1)).toTableau
  have full (k : ℕ) (hk : k ≤ (YoungDiagram.ofPartition z.1).card)
      (hfull : k = (YoungDiagram.ofPartition z.1).card) :
      griffinWitnessRejection z.2 T ⊥ k hk n = insertionRejectionExponent z.2 T ∧
        griffinApolarWitness (R := ℂ) z.2 T k hk n = higherSpechtWitness z.2 T := by
    subst k
    exact ⟨griffinWitnessRejection_full z.2 T n, griffinApolarWitness_full z.2 T n⟩
  obtain ⟨hr, hG⟩ := full n (YoungDiagram.card_ofPartition z.1).symm.le
    (YoungDiagram.card_ofPartition z.1).symm
  rw [springerCommonHarmonicVector_formula, hr, hG]


theorem powerIdeal_card_le_springerIdeal {R : Type*} [CommRing R] (mu : YoungDiagram) :
    powerIdeal R mu.card mu.card ≤ springerIdeal R mu := by
  apply Ideal.span_le.mpr
  rintro p ⟨j, rfl⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_pow, springer_coordinate_pow_card_eq_zero]

theorem griffinIdeal_full_eq_untruncated {R : Type*} [CommRing R]
    {n : ℕ} (mu : YoungDiagram) (hmu : mu.card = n) :
    griffinIdeal R n mu n = untruncatedIdeal R n mu := by
  subst n
  exact sup_eq_left.mpr (powerIdeal_card_le_springerIdeal mu)

theorem catDominates_prefix_of_full_card {mu : YoungDiagram}
    (S : StandardYoungTableau mu) {n : ℕ} (hn : mu.card = n)
    (lam : YoungDiagram) (h : n ≤ mu.card) :
    CatDominates (prefixTableau S n h) lam ↔ CatDominates S lam := by
  subst n
  exact catDominates_prefixTableau_full S lam

theorem finiteEligible_full_card_iff {n : ℕ} (mu : YoungDiagram) (hmu : mu.card = n)
    (i : FiniteHarmonicIndex n n) :
    i.toUnboundedHarmonicIndex.eligible mu hmu.le ↔
      i.multiplier = ⊥ ∧ CatDominates i.left mu := by
  subst n
  rw [UnboundedHarmonicIndex.eligible, Nat.sub_self,
    catDominates_prefix_of_full_card i.left (YoungDiagram.card_ofPartition i.part)]
  constructor
  · rintro ⟨h, hc⟩
    exact ⟨diagram_eq_bot_of_height_zero (Nat.eq_zero_of_le_zero h), hc⟩
  · rintro ⟨h, hc⟩
    exact ⟨by simp [h], hc⟩

def springerEligibleFiniteEquiv {n : ℕ} (hn : 0 < n)
    (mu : YoungDiagram) (hmu : mu.card = n) :
    EligibleFiniteHarmonicIndex n n mu hmu.le ≃
      {z : SpringerCommonIndex n // CatDominates z.2 mu} where
  toFun i := ⟨⟨i.val.part, i.val.left⟩,
    ((finiteEligible_full_card_iff mu hmu i.val).mp i.property).2⟩
  invFun z := ⟨springerCommonFiniteIndex hn z.val,
    (finiteEligible_full_card_iff mu hmu _).mpr ⟨rfl, z.property⟩⟩
  left_inv i := by
    apply Subtype.ext
    have hm := ((finiteEligible_full_card_iff mu hmu i.val).mp i.property).1
    rcases i with ⟨⟨⟨part, S, eta, he⟩, hd, hw⟩, hi⟩
    dsimp only at hm
    subst eta
    rfl
  right_inv z := by cases z; rfl

theorem springerCommonHarmonicCopy_isSpecht {n : ℕ} (hn : 0 < n)
    (z : SpringerCommonIndex n) :
    IsSpechtPolynomialCopy z.1 (springerCommonHarmonicCopy hn z) :=
  finiteCommonHarmonicCopy_isSpecht (springerCommonFiniteIndex hn z) hn

theorem springerCommonHarmonicCopy_degree {n : ℕ} (hn : 0 < n)
    (z : SpringerCommonIndex n) :
    springerCommonHarmonicCopy hn z ≤ homogeneousSubmodule (Fin n) ℂ (cochargeDegree z.2) := by
  simpa only [finiteCommonHarmonicCopy, springerCommonHarmonicCopy, springerCommonHarmonicVector,
    UnboundedHarmonicIndex.degree, springerCommonFiniteIndex, YoungDiagram.card,
    YoungDiagram.cells_bot, Finset.card_empty, Nat.add_zero] using
    finiteCommonHarmonicCopy_le_homogeneous (springerCommonFiniteIndex hn z)

theorem springerCommonHarmonicCopies_iSupIndep {n : ℕ} (hn : 0 < n) :
    iSupIndep (springerCommonHarmonicCopy hn) :=
  (finiteCommonHarmonicCopies_iSupIndep hn).comp (springerCommonFiniteIndex_injective hn)

theorem corollary_5_5_decomposition {n : ℕ} (hn : 0 < n)
    (mu : YoungDiagram) (hmu : mu.card = n) :
    ordinaryHarmonics (untruncatedIdeal ℂ n mu) =
      ⨆ z : {z : SpringerCommonIndex n // CatDominates z.2 mu},
        springerCommonHarmonicCopy hn z.val := by
  have hheight : mu.colLen 0 ≤ n := (colLen_zero_le_card mu).trans_eq hmu
  rw [← griffinIdeal_full_eq_untruncated mu hmu,
    finiteCommonHarmonic_decomposition_of_specifiedBasis n n mu hmu.le hn hheight
      (griffin_specifiedBasis ℂ n mu hmu.le n hn hheight), eligibleCommonHarmonicSum]
  rw [← Equiv.iSup_comp (springerEligibleFiniteEquiv hn mu hmu).symm]
  rfl

theorem min_card_le_rowPrefixSum (mu : YoungDiagram) (r : ℕ) :
    min mu.card r ≤ rowPrefixSum mu r := by
  by_cases hr : r ≤ mu.colLen 0
  · apply (min_le_right _ _).trans
    change r ≤ ∑ j ∈ range r, mu.rowLen j
    calc
      r = ∑ _j ∈ range r, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun j hj => by
        have hjh : j < mu.colLen 0 := (mem_range.mp hj).trans_le hr
        exact YoungDiagram.mem_iff_lt_rowLen.mp
          (YoungDiagram.mem_iff_lt_colLen.mpr hjh)
  · have hsum := YoungDiagram.card_eq_sum_range_rowLen mu (Nat.le_of_not_ge hr)
    change min mu.card r ≤ ∑ j ∈ range r, mu.rowLen j
    rw [← hsum]
    exact min_le_left _ _

theorem dominates_column_of_card {mu : YoungDiagram} {n : ℕ} (hmu : mu.card = n) :
    Dominates mu (columnPartition n) := by
  intro r
  change rowPrefixSum (columnPartition n) r ≤ rowPrefixSum mu r
  have hleft : rowPrefixSum (columnPartition n) r ≤ min n r := by
    apply le_min
    · exact (rowPrefixSum_le_card _ r).trans_eq (columnPartition_card n)
    · change (∑ j ∈ range r, (columnPartition n).rowLen j) ≤ r
      calc
        _ ≤ ∑ _j ∈ range r, 1 := by
          apply Finset.sum_le_sum
          intro j hj
          by_contra h
          have hc : (j, 1) ∈ (columnPartition n).cells :=
            YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.lt_of_not_ge h)
          rw [columnPartition_cells] at hc
          simp only [Finset.mem_product, Finset.mem_singleton] at hc
          omega
        _ = r := by simp
  exact hleft.trans (by simpa only [hmu] using min_card_le_rowPrefixSum mu r)

theorem catDominates_column (n : ℕ) (z : SpringerCommonIndex n) :
    CatDominates z.2 (columnPartition n) := by
  rw [← columnInsertion_dominates_iff]
  exact dominates_column_of_card
    ((columnInsertion z.2).shape_card.trans (YoungDiagram.card_ofPartition z.1))

theorem corollary_5_5_master {n : ℕ} (hn : 0 < n) :
    ordinaryHarmonics (untruncatedIdeal ℂ n (columnPartition n)) =
      ⨆ z : SpringerCommonIndex n, springerCommonHarmonicCopy hn z := by
  rw [corollary_5_5_decomposition hn _ (columnPartition_card n)]
  apply le_antisymm
  · exact iSup_le fun z => le_iSup (springerCommonHarmonicCopy hn) z.val
  · exact iSup_le fun z => le_iSup
      (fun w : {w : SpringerCommonIndex n // CatDominates w.2 (columnPartition n)} =>
        springerCommonHarmonicCopy hn w.val) ⟨z, catDominates_column n z⟩

end HigherSpecht
end
end CanonicalSource10

section CanonicalSource11
/- Source: HigherSpecht/SpringerIntersections.lean -/



/-!
# Corollary 5.6 for every nonempty finite family

The ideal below is the literal intersection of the Springer ideals.  A
finite expression, with an explicitly redundant chosen leaf, identifies it
with the general ideal-expression construction.  Removing the forced empty
multiplier gives exactly the original `F_T^S` family and its graded Schur sum.
-/

noncomputable section
open TauCeti TauCeti.YoungTableau Module MvPolynomial Finset
open scoped Classical

namespace HigherSpecht

def fullSpringerAtom {n : ℕ} (part : n.Partition) : GriffinIdealExpression n n :=
  .atom ⟨YoungDiagram.ofPartition part, (YoungDiagram.card_ofPartition part).le,
    (colLen_zero_le_card _).trans_eq (YoungDiagram.card_ofPartition part)⟩

theorem fullSpringerAtom_ideal {R : Type*} [CommRing R] {n : ℕ} (part : n.Partition) :
    (fullSpringerAtom part).ideal R = untruncatedIdeal R n (YoungDiagram.ofPartition part) :=
  griffinIdeal_full_eq_untruncated _ (YoungDiagram.card_ofPartition part)

theorem fullSpringerAtom_eligible {n : ℕ} (part : n.Partition)
    (i : FiniteHarmonicIndex n n) :
    i ∈ (fullSpringerAtom part).eligible ↔ i.multiplier = ⊥ ∧
      CatDominates i.left (YoungDiagram.ofPartition part) :=
  finiteEligible_full_card_iff _ (YoungDiagram.card_ofPartition part) i

def springerIntersectionIdeal (R : Type*) [CommRing R] {n : ℕ}
    (A : Finset n.Partition) : Ideal (PolynomialRing n R) :=
  ⨅ part ∈ A, untruncatedIdeal R n (YoungDiagram.ofPartition part)

def springerIntersectionExpression {n : ℕ} (A : Finset n.Partition) (hA : A.Nonempty) :
    GriffinIdealExpression n n :=
  A.toList.foldr (fun part e => .intersection (fullSpringerAtom part) e)
    (fullSpringerAtom (Classical.choose hA))

theorem mem_springerFold_ideal {R : Type*} [CommRing R] {n : ℕ}
    (L : List n.Partition) (e : GriffinIdealExpression n n) (p : PolynomialRing n R) :
    p ∈ (L.foldr (fun part e => .intersection (fullSpringerAtom part) e) e).ideal R ↔
      p ∈ e.ideal R ∧ ∀ part ∈ L, p ∈ untruncatedIdeal R n (YoungDiagram.ofPartition part) := by
  induction L with
  | nil => simp
  | cons part L ih =>
      simp only [List.foldr_cons, GriffinIdealExpression.ideal, Ideal.mem_inf,
        fullSpringerAtom_ideal, ih, List.mem_cons, forall_eq_or_imp]
      tauto

theorem springerIntersectionExpression_ideal {R : Type*} [CommRing R] {n : ℕ}
    (A : Finset n.Partition) (hA : A.Nonempty) :
    (springerIntersectionExpression A hA).ideal R = springerIntersectionIdeal R A := by
  ext p
  rw [springerIntersectionExpression, mem_springerFold_ideal,
    fullSpringerAtom_ideal, springerIntersectionIdeal]
  simp only [Ideal.mem_iInf, Finset.mem_toList]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨h _ (Classical.choose_spec hA), h⟩

theorem mem_springerFold_eligible {n : ℕ}
    (L : List n.Partition) (e : GriffinIdealExpression n n) (i : FiniteHarmonicIndex n n) :
    i ∈ (L.foldr (fun part e => .intersection (fullSpringerAtom part) e) e).eligible ↔
      i ∈ e.eligible ∨ ∃ part ∈ L, i ∈ (fullSpringerAtom part).eligible := by
  induction L with
  | nil => simp
  | cons part L ih =>
      simp only [List.foldr_cons, GriffinIdealExpression.eligible, Set.mem_union,
        ih, List.mem_cons, exists_eq_or_imp]
      tauto

theorem springerIntersectionExpression_eligible {n : ℕ}
    (A : Finset n.Partition) (hA : A.Nonempty) (i : FiniteHarmonicIndex n n) :
    i ∈ (springerIntersectionExpression A hA).eligible ↔
      i.multiplier = ⊥ ∧ ∃ part ∈ A, CatDominates i.left (YoungDiagram.ofPartition part) := by
  rw [springerIntersectionExpression, mem_springerFold_eligible]
  simp only [fullSpringerAtom_eligible, Finset.mem_toList]
  constructor
  · rintro (⟨hm, hc⟩ | ⟨part, hp, hm, hc⟩)
    · exact ⟨hm, Classical.choose hA, Classical.choose_spec hA, hc⟩
    · exact ⟨hm, part, hp, hc⟩
  · rintro ⟨hm, part, hp, hc⟩
    exact Or.inr ⟨part, hp, hm, hc⟩

abbrev SpringerIntersectionLeftIndex {n : ℕ} (A : Finset n.Partition) :=
  {z : SpringerCommonIndex n // ∃ part ∈ A, CatDominates z.2 (YoungDiagram.ofPartition part)}

abbrev SpringerIntersectionVectorIndex {n : ℕ} (A : Finset n.Partition) :=
  Σ z : SpringerIntersectionLeftIndex A,
    StandardYoungTableau (YoungDiagram.ofPartition z.val.1)

def springerIntersectionVectorEquiv {n : ℕ} (hn : 0 < n)
    (A : Finset n.Partition) (hA : A.Nonempty) :
    SpringerIntersectionVectorIndex A ≃ (springerIntersectionExpression A hA).VectorIndex where
  toFun z := ⟨⟨springerCommonFiniteIndex hn z.1.val,
    (springerIntersectionExpression_eligible A hA _).mpr ⟨rfl, z.1.property⟩⟩, z.2⟩
  invFun z := ⟨⟨⟨z.1.val.part, z.1.val.left⟩,
    ((springerIntersectionExpression_eligible A hA z.1.val).mp z.1.property).2⟩, z.2⟩
  left_inv _ := rfl
  right_inv z := by
    have hm := ((springerIntersectionExpression_eligible A hA z.1.val).mp z.1.property).1
    rcases z with ⟨⟨⟨⟨part, S, eta, he⟩, hd, hw⟩, hi⟩, T⟩
    dsimp only at hm
    subst eta
    rfl

def springerIntersectionPolynomial {R : Type*} [CommRing R] {n : ℕ}
    (A : Finset n.Partition) (z : SpringerIntersectionVectorIndex A) : PolynomialRing n R :=
  rename (finCongr (YoungDiagram.card_ofPartition z.1.val.1))
    (higherSpechtPolynomial z.1.val.2 z.2)

def springerIntersectionFamily (R : Type*) [CommRing R] {n : ℕ}
    (A : Finset n.Partition) (z : SpringerIntersectionVectorIndex A) :
    PolynomialRing n R ⧸ springerIntersectionIdeal R A :=
  Ideal.Quotient.mk _ (springerIntersectionPolynomial A z)

theorem springerIntersection_polynomial_correspondence {R : Type*} [CommRing R]
    {n : ℕ} (hn : 0 < n) (A : Finset n.Partition) (hA : A.Nonempty)
    (z : SpringerIntersectionVectorIndex A) :
    (springerIntersectionExpression A hA).polynomial R
        (springerIntersectionVectorEquiv hn A hA z) = springerIntersectionPolynomial A z := by
  change rename (finCongr (YoungDiagram.card_ofPartition z.1.val.1))
      (higherSpechtPolynomial z.1.val.2 z.2) *
      elementaryMultiplier n n (⊥ : YoungDiagram).rowLen =
    rename (finCongr (YoungDiagram.card_ofPartition z.1.val.1))
      (higherSpechtPolynomial z.1.val.2 z.2)
  simp only [elementaryMultiplier, YoungDiagram.rowLen_bot, Nat.sub_self,
    pow_zero, Finset.prod_const_one, mul_one]

def springerIntersectionBasis {n : ℕ} (hn : 0 < n)
    (A : Finset n.Partition) (hA : A.Nonempty) :
    Basis (SpringerIntersectionVectorIndex A) ℂ
      (PolynomialRing n ℂ ⧸ springerIntersectionIdeal ℂ A) :=
  (((springerIntersectionExpression A hA).prescribedBasis hn).reindex
    (springerIntersectionVectorEquiv hn A hA).symm).map
      (Ideal.quotientEquivAlgOfEq ℂ (springerIntersectionExpression_ideal A hA)).toLinearEquiv

theorem springerIntersectionBasis_apply {n : ℕ} (hn : 0 < n)
    (A : Finset n.Partition) (hA : A.Nonempty) (z : SpringerIntersectionVectorIndex A) :
    springerIntersectionBasis hn A hA z = springerIntersectionFamily ℂ A z := by
  rw [springerIntersectionBasis, Basis.map_apply, Basis.reindex_apply,
    GriffinIdealExpression.prescribedBasis_apply]
  simp only [GriffinIdealExpression.family, AlgEquiv.toLinearEquiv_apply,
    Ideal.quotientEquivAlgOfEq_mk, Equiv.symm_symm,
    springerIntersection_polynomial_correspondence, springerIntersectionFamily]

theorem corollary_5_6_basis {n : ℕ} (hn : 0 < n)
    (A : Finset n.Partition) (hA : A.Nonempty) :
    IsSpecifiedBasis (R := ℂ) (springerIntersectionFamily ℂ A) :=
  ⟨springerIntersectionBasis hn A hA, springerIntersectionBasis_apply hn A hA⟩

def springerIntersectionFrobeniusSeries {n : ℕ} (hn : 0 < n)
    (A : Finset n.Partition) (hA : A.Nonempty) : PowerSeries (MvPolynomial (Fin n) ℂ) :=
  (springerIntersectionExpression A hA).frobeniusSeries hn

theorem corollary_5_6_frobenius {n : ℕ} (hn : 0 < n)
    (A : Finset n.Partition) (hA : A.Nonempty) :
    springerIntersectionFrobeniusSeries hn A hA =
      ∑ z : SpringerIntersectionLeftIndex A,
        PowerSeries.monomial (cochargeDegree z.val.2) (schurPoly (Fin n) ℂ z.val.1) := by
  rw [springerIntersectionFrobeniusSeries, GriffinIdealExpression.corollary_5_3_frobenius]
  let e : {i : FiniteHarmonicIndex n n //
      i ∈ (springerIntersectionExpression A hA).eligible} ≃ SpringerIntersectionLeftIndex A :=
    { toFun i := ⟨⟨i.val.part, i.val.left⟩,
        ((springerIntersectionExpression_eligible A hA i.val).mp i.property).2⟩
      invFun z := ⟨springerCommonFiniteIndex hn z.val,
        (springerIntersectionExpression_eligible A hA _).mpr ⟨rfl, z.property⟩⟩
      left_inv i := by
        apply Subtype.ext
        have hm := ((springerIntersectionExpression_eligible A hA i.val).mp i.property).1
        rcases i with ⟨⟨⟨part, S, eta, he⟩, hd, hw⟩, hi⟩
        dsimp only at hm
        subst eta
        rfl
      right_inv _ := rfl }
  rw [← Equiv.sum_comp e.symm]
  apply Finset.sum_congr rfl
  intro z hz
  change PowerSeries.monomial (cochargeDegree z.val.2 + (⊥ : YoungDiagram).card)
      (schurPoly (Fin n) ℂ z.val.1) =
    PowerSeries.monomial (cochargeDegree z.val.2) (schurPoly (Fin n) ℂ z.val.1)
  simp only [YoungDiagram.card, YoungDiagram.cells_bot, Finset.card_empty, Nat.add_zero]

end HigherSpecht
end
end CanonicalSource11

section CanonicalSource12
/- Source: HigherSpecht/WeakDominanceJoin.lean -/



/-!
# The actual partition join in Remark 5.4

The partition is constructed from the successive differences of the maximum
of the two literal conjugate tails.  Discrete convexity makes these genuine
conjugate parts.  The result has exactly the advertised tails and is the
least weak-dominance upper bound; the sum identity then follows from the
original elementary generators over every commutative coefficient ring.
-/

noncomputable section
open Finset TauCeti MvPolynomial
open scoped Classical

namespace HigherSpecht

def maximumColumnTail (lam mu : YoungDiagram) (t : ℕ) : ℕ :=
  max (columnTail lam t) (columnTail mu t)

theorem maximumColumnTail_antitone (lam mu : YoungDiagram) :
    Antitone (maximumColumnTail lam mu) :=
  fun _ _ hij => max_le_max (columnTail_antitone lam hij) (columnTail_antitone mu hij)

theorem maximumColumnTail_discreteConvex (lam mu : YoungDiagram) (t : ℕ) :
    2 * maximumColumnTail lam mu (t + 1) ≤
      maximumColumnTail lam mu t + maximumColumnTail lam mu (t + 2) := by
  by_cases h : columnTail lam (t + 1) ≤ columnTail mu (t + 1)
  · rw [maximumColumnTail, max_eq_right h]
    exact (columnTail_discreteConvex mu t).trans
      (Nat.add_le_add (le_max_right _ _) (le_max_right _ _))
  · rw [maximumColumnTail, max_eq_left (le_of_not_ge h)]
    exact (columnTail_discreteConvex lam t).trans
      (Nat.add_le_add (le_max_left _ _) (le_max_left _ _))

def maximumTailDifference (lam mu : YoungDiagram) (t : ℕ) : ℕ :=
  maximumColumnTail lam mu t - maximumColumnTail lam mu (t + 1)

theorem maximumTailDifference_antitone (lam mu : YoungDiagram) :
    Antitone (maximumTailDifference lam mu) := by
  apply antitone_nat_of_succ_le
  intro t
  have h0 : maximumColumnTail lam mu (t + 1) ≤ maximumColumnTail lam mu t :=
    maximumColumnTail_antitone lam mu (by omega)
  have h1 : maximumColumnTail lam mu (t + 2) ≤ maximumColumnTail lam mu (t + 1) :=
    maximumColumnTail_antitone lam mu (by omega)
  have hc := maximumColumnTail_discreteConvex lam mu t
  change maximumColumnTail lam mu (t + 1) - maximumColumnTail lam mu (t + 2) ≤
    maximumColumnTail lam mu t - maximumColumnTail lam mu (t + 1)
  omega

def weakJoinWidth (lam mu : YoungDiagram) : ℕ := max (lam.rowLen 0) (mu.rowLen 0)

theorem maximumColumnTail_zero_of_width_le (lam mu : YoungDiagram) {t : ℕ}
    (ht : weakJoinWidth lam mu ≤ t) : maximumColumnTail lam mu t = 0 := by
  rw [maximumColumnTail,
    columnTail_eq_zero_of_width_le lam ((le_max_left _ _).trans ht),
    columnTail_eq_zero_of_width_le mu ((le_max_right _ _).trans ht), max_self]

def weakDominanceJoin (lam mu : YoungDiagram) : YoungDiagram :=
  (YoungDiagram.ofRowLensFin
    (fun i : Fin (weakJoinWidth lam mu) => maximumTailDifference lam mu i.val)
    (fun _ _ hij => maximumTailDifference_antitone lam mu hij)).transpose

theorem weakDominanceJoin_width_le (lam mu : YoungDiagram) :
    (weakDominanceJoin lam mu).rowLen 0 ≤ weakJoinWidth lam mu := by
  rw [weakDominanceJoin, YoungDiagram.rowLen_transpose]
  exact YoungDiagram.colLen_zero_ofRowLensFin_le _ _

theorem weakDominanceJoin_colLen (lam mu : YoungDiagram) (t : ℕ) :
    (weakDominanceJoin lam mu).colLen t = maximumTailDifference lam mu t := by
  rw [weakDominanceJoin, YoungDiagram.colLen_transpose]
  by_cases ht : t < weakJoinWidth lam mu
  · exact YoungDiagram.rowLen_ofRowLensFin _ _ ⟨t, ht⟩
  · have hz : maximumTailDifference lam mu t = 0 := by
      rw [maximumTailDifference,
        maximumColumnTail_zero_of_width_le lam mu (Nat.le_of_not_gt ht), Nat.zero_sub]
    exact (YoungDiagram.rowLen_ofRowLensFin_eq_zero_of_le _ _
      (Nat.le_of_not_gt ht)).trans hz.symm

/-- The construction realizes the pointwise maximum, not merely an upper
bound or a convex relaxation of it. -/
theorem columnTail_weakDominanceJoin (lam mu : YoungDiagram) (t : ℕ) :
    columnTail (weakDominanceJoin lam mu) t = maximumColumnTail lam mu t := by
  let N := weakJoinWidth lam mu
  by_cases ht : t ≤ N
  · induction ht using Nat.decreasingInduction with
    | self =>
        rw [columnTail_eq_zero_of_width_le _ (weakDominanceJoin_width_le lam mu),
          maximumColumnTail_zero_of_width_le lam mu le_rfl]
    | of_succ k hk ih =>
        rw [columnTail_succ, weakDominanceJoin_colLen, ih, maximumTailDifference]
        exact Nat.sub_add_cancel (maximumColumnTail_antitone lam mu (Nat.le_succ k))
  · rw [columnTail_eq_zero_of_width_le _
        ((weakDominanceJoin_width_le lam mu).trans (le_of_not_ge ht)),
      maximumColumnTail_zero_of_width_le lam mu (le_of_not_ge ht)]

theorem weakDominanceJoin_card (lam mu : YoungDiagram) :
    (weakDominanceJoin lam mu).card = max lam.card mu.card := by
  simpa only [columnTail_zero, maximumColumnTail] using columnTail_weakDominanceJoin lam mu 0

theorem weakDominanceJoin_height_le (lam mu : YoungDiagram) :
    (weakDominanceJoin lam mu).colLen 0 ≤ max (lam.colLen 0) (mu.colLen 0) := by
  rw [weakDominanceJoin_colLen, maximumTailDifference, maximumColumnTail, maximumColumnTail]
  have hl := columnTail_succ lam 0
  have hm := columnTail_succ mu 0
  omega

theorem weakDominanceJoin_dominates_left (lam mu : YoungDiagram) :
    Dominates (weakDominanceJoin lam mu) lam := by
  apply (dominates_iff_columnTail_le _ _).mpr
  intro t
  rw [columnTail_weakDominanceJoin]
  exact le_max_left _ _

theorem weakDominanceJoin_dominates_right (lam mu : YoungDiagram) :
    Dominates (weakDominanceJoin lam mu) mu := by
  apply (dominates_iff_columnTail_le _ _).mpr
  intro t
  rw [columnTail_weakDominanceJoin]
  exact le_max_right _ _

theorem dominates_weakDominanceJoin_iff (nu lam mu : YoungDiagram) :
    Dominates nu (weakDominanceJoin lam mu) ↔ Dominates nu lam ∧ Dominates nu mu := by
  simp only [dominates_iff_columnTail_le, columnTail_weakDominanceJoin,
    maximumColumnTail, max_le_iff, forall_and]

theorem untruncatedIdeal_weakDominanceJoin {R : Type*} [CommRing R] {n : ℕ}
    (lam mu : YoungDiagram) (hlam : lam.card ≤ n) (hmu : mu.card ≤ n) :
    untruncatedIdeal R n (weakDominanceJoin lam mu) =
      untruncatedIdeal R n lam ⊔ untruncatedIdeal R n mu := by
  have hjoin : (weakDominanceJoin lam mu).card ≤ n := by
    rw [weakDominanceJoin_card]
    exact max_le hlam hmu
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro p ⟨Y, d, hd, hY, hthreshold, rfl⟩
    rw [← columnTail_eq_conjugateTail _ hjoin, columnTail_weakDominanceJoin,
      maximumColumnTail] at hthreshold
    by_cases h : columnTail lam (n - Y.card) ≤ columnTail mu (n - Y.card)
    · rw [max_eq_right h, columnTail_eq_conjugateTail mu hmu] at hthreshold
      exact Ideal.mem_sup_right (elementaryOn_mem_untruncatedIdeal Y hd hY hthreshold)
    · rw [max_eq_left (le_of_not_ge h), columnTail_eq_conjugateTail lam hlam] at hthreshold
      exact Ideal.mem_sup_left (elementaryOn_mem_untruncatedIdeal Y hd hY hthreshold)
  · exact sup_le
      (untruncatedIdeal_le_of_dominates hlam hjoin (weakDominanceJoin_dominates_left lam mu))
      (untruncatedIdeal_le_of_dominates hmu hjoin (weakDominanceJoin_dominates_right lam mu))

/-- Remark 5.4's exact ideal-sum identity holds over every coefficient
ring directly from the defining thresholds. -/
theorem remark_5_4_griffin_sum {R : Type*} [CommRing R] {n s : ℕ}
    (lam mu : YoungDiagram) (hlam : lam.card ≤ n) (hmu : mu.card ≤ n) :
    griffinIdeal R n lam s ⊔ griffinIdeal R n mu s =
      griffinIdeal R n (weakDominanceJoin lam mu) s := by
  rw [griffinIdeal, griffinIdeal, griffinIdeal,
    untruncatedIdeal_weakDominanceJoin lam mu hlam hmu]
  calc
    _ = (untruncatedIdeal R n lam ⊔ untruncatedIdeal R n mu) ⊔
        (powerIdeal R n s ⊔ powerIdeal R n s) := sup_sup_sup_comm _ _ _ _
    _ = _ := by rw [sup_idem]

end HigherSpecht
end
end CanonicalSource12

section CanonicalSource13
/- Source: HigherSpecht/CommonShapeEligibility.lean -/



/-!
# One actual partition records all finite eligibility conditions

The common prefix is the original maximal prefix, with both its boost cutoff
and the first-`s`-rows cutoff.  Restriction of the literal catabolism output
proves the converse eligibility direction as well as the already established
forward direction.  The constructed join therefore records simultaneous
eligibility without changing the original index set.
-/

noncomputable section
open TauCeti Finset

namespace HigherSpecht

theorem remark_5_4_eligibility {n s : ℕ} (i : FiniteHarmonicIndex n s)
    (lam : YoungDiagram) (hk : lam.card ≤ n) (hheight : lam.colLen 0 ≤ s) :
    i.toUnboundedHarmonicIndex.eligible lam hk ↔
      Dominates (finiteCommonPrefixShape i) lam := by
  refine ⟨finiteCommonPrefixShape_dominates i lam hk hheight, ?_⟩
  intro hdom
  have hcard := dominates_card_le hdom
  rw [finiteCommonPrefixShape_card] at hcard
  have hcut : lam.card ≤ n - i.multiplier.colLen 0 :=
    hcard.trans (min_le_left _ _)
  refine ⟨by have := i.multiplier_length; omega, ?_⟩
  apply (catDominates_prefix_iff i.left lam
    (by simpa only [YoungDiagram.card_ofPartition] using hk)).mpr
  intro r
  have hr := hdom r
  change rowPrefixSum lam r ≤ rowPrefixSum (finiteCommonPrefixShape i) r at hr
  rw [finiteCommonPrefixShape, catabolizability_prefix_rowSums] at hr
  exact hr.trans (min_le_right _ _)

theorem finiteEligibility_weakDominanceJoin {n s : ℕ}
    (i : FiniteHarmonicIndex n s) (lam mu : YoungDiagram)
    (hlam : lam.card ≤ n) (hmu : mu.card ≤ n)
    (hls : lam.colLen 0 ≤ s) (hms : mu.colLen 0 ≤ s) :
    i.toUnboundedHarmonicIndex.eligible (weakDominanceJoin lam mu)
        (by rw [weakDominanceJoin_card]; exact max_le hlam hmu) ↔
      i.toUnboundedHarmonicIndex.eligible lam hlam ∧
        i.toUnboundedHarmonicIndex.eligible mu hmu := by
  rw [remark_5_4_eligibility i _ _
      ((weakDominanceJoin_height_le lam mu).trans (max_le hls hms)),
    remark_5_4_eligibility i lam hlam hls,
    remark_5_4_eligibility i mu hmu hms,
    dominates_weakDominanceJoin_iff]

end HigherSpecht
end
end CanonicalSource13

section CanonicalSource14
/- Source: HigherSpecht/TriangularMultiplicityChange.lean -/



/-!
# The literal inverse of a finite triangular pairing matrix

A numerical key may have ties.  A finite enumeration refines it to a true
linear order; the assumed zero entries at distinct tied keys make the
pairing upper triangular for this refinement.  Its unit diagonal supplies
the actual inverse over the coefficient ring, not a rational inverse
whose denominators have been left uncontrolled.
-/

noncomputable section
open Matrix Module
open scoped Classical

namespace HigherSpecht

def pairingKeyOrder {ι κ : Type*} [Fintype ι] [LinearOrder κ] (key : ι → κ) : LinearOrder ι :=
  LinearOrder.lift' (fun i => (toLex (key i, Fintype.equivFin ι i) : κ ×ₗ Fin (Fintype.card ι)))
    (fun i j h => (Fintype.equivFin ι).injective (congrArg (fun z => (ofLex z).2) h))

theorem key_le_of_pairingKeyOrder_le {ι κ : Type*} [Fintype ι] [LinearOrder κ]
    (key : ι → κ) {i j : ι} (h : @LE.le ι (pairingKeyOrder key).toLE i j) : key i ≤ key j := by
  change (toLex (key i, Fintype.equivFin ι i) : κ ×ₗ Fin (Fintype.card ι)) ≤
    toLex (key j, Fintype.equivFin ι j) at h
  rcases lt_or_eq_of_le h with hlt | heq
  · rcases Prod.lex_iff.mp hlt with hkey | ⟨hkey, _⟩
    · exact hkey.le
    · exact hkey.le
  · exact (congrArg (fun z => (ofLex z).1) heq).le

theorem matrix_upperTriangular_of_key
    {R ι κ : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [LinearOrder κ]
    (key : ι → κ) (M : Matrix ι ι R)
    (hzero : ∀ i j, i ≠ j → key j ≤ key i → M i j = 0) :
    letI := pairingKeyOrder key
    M.IsUpperTriangular := by
  letI := pairingKeyOrder key
  intro i j hji
  exact hzero i j (ne_of_gt hji) (key_le_of_pairingKeyOrder_le key hji.le)

theorem matrix_isUnit_det_of_key
    {R ι κ : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [LinearOrder κ]
    (key : ι → κ) (M : Matrix ι ι R)
    (hzero : ∀ i j, i ≠ j → key j ≤ key i → M i j = 0)
    (hdiag : ∀ i, IsUnit (M i i)) : IsUnit M.det := by
  letI := pairingKeyOrder key
  rw [Matrix.det_of_isUpperTriangular (matrix_upperTriangular_of_key key M hzero)]
  exact IsUnit.prod_univ_iff.mpr hdiag

theorem matrix_inverse_upperTriangular_of_key
    {R ι κ : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [LinearOrder κ]
    (key : ι → κ) (M : Matrix ι ι R)
    (hzero : ∀ i j, i ≠ j → key j ≤ key i → M i j = 0)
    (hdiag : ∀ i, IsUnit (M i i)) :
    letI := pairingKeyOrder key
    M⁻¹.IsUpperTriangular := by
  letI := pairingKeyOrder key
  obtain ⟨_⟩ := ((Matrix.isUnit_iff_isUnit_det M).mpr
    (matrix_isUnit_det_of_key key M hzero hdiag)).nonempty_invertible
  exact Matrix.blockTriangular_inv_of_blockTriangular
    (matrix_upperTriangular_of_key key M hzero)

def inversePairingFamily {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) (v : ι → V) (j : ι) : V :=
  ∑ i, M⁻¹ i j • v i

theorem pairing_inversePairingFamily
    {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [Fintype ι] [DecidableEq ι] (L : ι → Module.Dual R V) (v : ι → V)
    (hunit : IsUnit (Matrix.of (fun i j => L i (v j))).det) (i j : ι) :
    L i (inversePairingFamily (Matrix.of (fun i j => L i (v j))) v j) =
      if i = j then 1 else 0 := by
  let M : Matrix ι ι R := Matrix.of fun i j => L i (v j)
  have h := congrArg (fun A : Matrix ι ι R => A i j) (Matrix.mul_nonsing_inv M hunit)
  simpa only [inversePairingFamily, map_sum, map_smul, smul_eq_mul,
    Matrix.mul_apply, Matrix.one_apply, Matrix.of_apply, M, mul_comm] using h

theorem map_matrix_inverse_of_isUnit
    {R S ι : Type*} [CommRing R] [CommRing S] [Fintype ι] [DecidableEq ι]
    (f : R →+* S) (M : Matrix ι ι R) (hM : IsUnit M.det) :
    (M⁻¹).map f = (M.map f)⁻¹ := by
  apply Eq.symm
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul M hM]
  exact Matrix.map_one f (map_zero f) (map_one f)

theorem originalFamily_eq_sum_inverseFamily
    {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) (hM : IsUnit M.det)
    (v : ι → V) (i : ι) :
    v i = ∑ j, M j i • inversePairingFamily M v j := by
  simp only [inversePairingFamily, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, mul_comm (M _ i)]
  have hentry (k : ι) : (∑ j, M⁻¹ k j * M j i) = if k = i then 1 else 0 := by
    exact congrArg (fun A : Matrix ι ι R => A k i) (Matrix.nonsing_inv_mul M hM)
  simp_rw [hentry]
  simp

theorem specifiedBasis_of_spanning_same_index
    {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [Fintype ι] [DecidableEq ι] (B : Basis ι R V) (v : ι → V)
    (hspan : Submodule.span R (Set.range v) = ⊤) :
    ∃ b : Basis ι R V, ∀ i, b i = v i := by
  let A := B.toMatrix v
  have hsurj : Function.Surjective A.mulVec := by
    intro y
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp
      (show B.equivFun.symm y ∈ Submodule.span R (Set.range v) by rw [hspan]; trivial)
    refine ⟨c, ?_⟩
    funext i
    have h := congrArg (fun z => B.repr z i) hc
    have hy := congrFun (B.equivFun.apply_symm_apply y) i
    rw [Basis.equivFun_apply] at hy
    rw [hy] at h
    simpa only [A, Basis.toMatrix_apply, Matrix.mulVec, dotProduct, map_sum, map_smul,
      Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, mul_comm] using h
  have hunit : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det A).mp (Matrix.mulVec_surjective_iff_isUnit.mp hsurj)
  obtain ⟨hind, hsp⟩ := B.is_basis_iff_det.mpr hunit
  exact ⟨Basis.mk hind hsp.ge, fun i => Basis.mk_apply _ _ i⟩

end HigherSpecht
end
end CanonicalSource14

section CanonicalSource15
/- Source: HigherSpecht/IntegralCommonPairing.lean -/



/-!
# The integral common pairing and its actual inverse

Every entry is the literal divided-power coefficient pairing.  Its diagonal
is a product of subgroup orders dividing n!, so the inverse exists over
Z[1/n!] and every ring in which n! is a unit.  The same coefficient matrix
is used for every right tableau of a fixed shape and degree.
-/

noncomputable section
open TauCeti TauCeti.YoungTableau Module MvPolynomial Matrix
open scoped Classical

namespace HigherSpecht

variable {R : Type*} [CommRing R]

def fixedCommonCoefficientOver {mu : YoungDiagram} {s : ℕ}
    (T : StandardYoungTableau mu) (i : FixedFiniteHarmonicIndex mu s) :
    Module.Dual R (PolynomialRing mu.card R) :=
  griffinCoefficientFunctional i.left T.toTableau i.multiplier
    (fixedCommonCut i) (fixedCommonCut_le i) s

theorem fixedCommonCoefficientOver_offDiagonal {mu : YoungDiagram} {s : ℕ}
    (T : StandardYoungTableau mu) (i j : FixedFiniteHarmonicIndex mu s)
    (hne : i ≠ j) (hkey : fixedGriffinKey T j ≤ fixedGriffinKey T i) :
    fixedCommonCoefficientOver (R := R) T i (fixedGriffinPolynomial T j) = 0 := by
  rw [fixedCommonCoefficientOver, griffinCoefficientFunctional_eq]
  apply witnessCoefficient_eq_zero_of_key_finiteRange
    (row := fun i => (rowIndex T.toTableau i : ℤ))
    (griffinWitness_rearrangement i.left T.toTableau i.multiplier
      (fixedCommonCut i) (fixedCommonCut_le i) s
      (fixedCommonCut_multiplier_length i) i.descents_lt i.multiplier_width)
    (griffinWitnessGroup i.left T.toTableau (fixedCommonCut i) (fixedCommonCut_le i))
    (griffinWitnessGroup_preserves i.left T.toTableau (fixedCommonCut i) (fixedCommonCut_le i))
    (fixedGriffinPolynomial T j)
    (boosted_higherSpecht_triangularSupport j.left T (Nat.sub_le _ _)
      j.multiplier j.multiplier_length)
    hkey (fun h => hne (fixedGriffinBoost_injective T h))
    (rowIndex_injective_on_intColumn T.toTableau)
    (transportedBoosted_intColumnMonovary i.left T.toTableau i.multiplier)
    (transportedBoosted_intColumnMonovary j.left T.toTableau j.multiplier)

theorem fixedCommonCoefficientOver_diagonal {mu : YoungDiagram} {s : ℕ}
    (T : StandardYoungTableau mu) (i : FixedFiniteHarmonicIndex mu s) :
    fixedCommonCoefficientOver T i (fixedGriffinPolynomial T i) =
      ((rowFillingStabilizers T.toTableau (transportedCocharge i.left T.toTableau)).card : R) *
      ((fixedWitnessPermutations
        (griffinWitnessGroup i.left T.toTableau (fixedCommonCut i) (fixedCommonCut_le i))
        (griffinWitnessRejection i.left T.toTableau i.multiplier
          (fixedCommonCut i) (fixedCommonCut_le i) s)
        (fun j => (colIndex T.toTableau j : ℤ))).card : R) := by
  rw [fixedCommonCoefficientOver, griffinCoefficientFunctional_eq]
  rw [witnessCoefficient_diagonal_finiteRange
    (griffinWitness_rearrangement i.left T.toTableau i.multiplier
      (fixedCommonCut i) (fixedCommonCut_le i) s
      (fixedCommonCut_multiplier_length i) i.descents_lt i.multiplier_width)
    (griffinWitnessGroup i.left T.toTableau (fixedCommonCut i) (fixedCommonCut_le i))
    (griffinWitnessGroup_preserves i.left T.toTableau (fixedCommonCut i) (fixedCommonCut_le i))
    (fixedGriffinPolynomial T i)
    (boosted_higherSpecht_triangularSupport i.left T (Nat.sub_le _ _)
      i.multiplier i.multiplier_length)]
  · rw [fixedGriffinPolynomial, lemma_4_2_distinguishedCoefficient i.left T
      (Nat.sub_le _ _) i.multiplier i.multiplier_length]
  · intro e he
    rw [← coeff_rename_perm, fixedGriffinPolynomial,
      boostedPolynomial_columnAlternating i.left T _ i.multiplier e
        (fun j => Int.ofNat_inj.mp (congrFun he j)), MvPolynomial.coeff_smul, smul_eq_mul]


theorem fixedCommonCoefficientOver_diagonal_isUnit {mu : YoungDiagram} {s : ℕ}
    (hfac : IsUnit (mu.card.factorial : R))
    (T : StandardYoungTableau mu) (i : FixedFiniteHarmonicIndex mu s) :
    IsUnit (fixedCommonCoefficientOver (R := R) T i (fixedGriffinPolynomial T i)) := by
  rw [fixedCommonCoefficientOver_diagonal]
  exact (rowFillingStabilizers_card_isUnit hfac T.toTableau
    (transportedCocharge i.left T.toTableau)).mul
    (fixedWitnessPermutations_card_isUnit hfac
      (griffinWitnessGroup i.left T.toTableau (fixedCommonCut i) (fixedCommonCut_le i))
      (griffinWitnessRejection i.left T.toTableau i.multiplier
        (fixedCommonCut i) (fixedCommonCut_le i) s)
      (fun j => (colIndex T.toTableau j : ℤ)))

theorem map_witnessCoefficient {S : Type*} [CommRing S] (f : R →+* S)
    {n : ℕ} (G : Subgroup (Equiv.Perm (Fin n))) (a r : Fin n →₀ ℕ)
    (p : PolynomialRing n R) :
    f (witnessCoefficient G a r p) =
      witnessCoefficient G a r (MvPolynomial.map f p) := by
  simp only [witnessCoefficient_apply, map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs <;> simp only [map_mul, map_zero, coefficientSign, map_intCast,
    MvPolynomial.coeff_map]

theorem map_fixedCommonCoefficientOver {S : Type*} [CommRing S] (f : R →+* S)
    {mu : YoungDiagram} {s : ℕ} (T : StandardYoungTableau mu)
    (i j : FixedFiniteHarmonicIndex mu s) :
    f (fixedCommonCoefficientOver T i (fixedGriffinPolynomial (R := R) T j)) =
      fixedCommonCoefficientOver T i (fixedGriffinPolynomial (R := S) T j) := by
  simp only [fixedCommonCoefficientOver, griffinCoefficientFunctional_eq]
  rw [map_witnessCoefficient]
  simp only [fixedGriffinPolynomial, map_mul, map_higherSpechtPolynomial,
    map_elementaryMultiplier]

abbrev FixedFiniteDegreeIndex (mu : YoungDiagram) (s d : ℕ) :=
  {i : FixedFiniteHarmonicIndex mu s // cochargeDegree i.left + i.multiplier.card = d}

def commonPairingMatrix (R : Type*) [CommRing R] (mu : YoungDiagram) (s d : ℕ) :
    Matrix (FixedFiniteDegreeIndex mu s d) (FixedFiniteDegreeIndex mu s d) R :=
  Matrix.of fun i j => fixedCommonCoefficientOver
    (StandardYoungTableau.rowSuperstandard mu) i.val
    (fixedGriffinPolynomial (StandardYoungTableau.rowSuperstandard mu) j.val)

def commonPairingKey {mu : YoungDiagram} {s d : ℕ} (i : FixedFiniteDegreeIndex mu s d) :
    ℤ ×ₗ ℤ := fixedGriffinKey (StandardYoungTableau.rowSuperstandard mu) i.val

theorem commonPairingMatrix_offDiagonal (R : Type*) [CommRing R]
    {mu : YoungDiagram} {s d : ℕ} (i j : FixedFiniteDegreeIndex mu s d)
    (hne : i ≠ j) (hkey : commonPairingKey j ≤ commonPairingKey i) :
    commonPairingMatrix R mu s d i j = 0 :=
  fixedCommonCoefficientOver_offDiagonal _ i.val j.val
    (fun h => hne (Subtype.ext h)) hkey

theorem commonPairingMatrix_det_isUnit (R : Type*) [CommRing R]
    (mu : YoungDiagram) (s d : ℕ) (hfac : IsUnit (mu.card.factorial : R)) :
    IsUnit (commonPairingMatrix R mu s d).det :=
  matrix_isUnit_det_of_key commonPairingKey _
    (commonPairingMatrix_offDiagonal R)
    (fun i => fixedCommonCoefficientOver_diagonal_isUnit hfac _ i.val)

theorem commonPairingMatrix_inverse_triangular (R : Type*) [CommRing R]
    (mu : YoungDiagram) (s d : ℕ) (hfac : IsUnit (mu.card.factorial : R)) :
    letI := pairingKeyOrder (commonPairingKey (mu := mu) (s := s) (d := d))
    (commonPairingMatrix R mu s d)⁻¹.IsUpperTriangular :=
  matrix_inverse_upperTriangular_of_key commonPairingKey _
    (commonPairingMatrix_offDiagonal R)
    (fun i => fixedCommonCoefficientOver_diagonal_isUnit hfac _ i.val)

theorem commonPairingMatrix_map {S : Type*} [CommRing S] (f : R →+* S)
    (mu : YoungDiagram) (s d : ℕ) :
    (commonPairingMatrix R mu s d).map f = commonPairingMatrix S mu s d := by
  ext i j
  exact map_fixedCommonCoefficientOver f _ i.val j.val

def adaptedFixedPolynomial (R : Type*) [CommRing R] {mu : YoungDiagram} {s d : ℕ}
    (i : FixedFiniteDegreeIndex mu s d) (T : StandardYoungTableau mu) : PolynomialRing mu.card R :=
  ∑ j, (commonPairingMatrix R mu s d)⁻¹ j i • fixedGriffinPolynomial T j.val

theorem adaptedFixedPolynomial_isHomogeneous (R : Type*) [CommRing R]
    {mu : YoungDiagram} {s d : ℕ} (i : FixedFiniteDegreeIndex mu s d)
    (T : StandardYoungTableau mu) : (adaptedFixedPolynomial R i T).IsHomogeneous d := by
  apply MvPolynomial.IsHomogeneous.sum
  intro j hj
  apply (MvPolynomial.homogeneousSubmodule (Fin mu.card) R d).smul_mem
  have hhom := (higherSpechtPolynomial_isHomogeneous (R := R) j.val.left T).mul
    (elementaryMultiplier_isHomogeneous mu.card (mu.card - (⊥ : YoungDiagram).card)
      j.val.multiplier j.val.multiplier_length)
  exact Eq.mp (congrArg
    (fun e => (fixedGriffinPolynomial (R := R) T j.val).IsHomogeneous e) j.property) hhom

theorem fixedCommonCoefficientOver_adapted (R : Type*) [CommRing R]
    {mu : YoungDiagram} {s d : ℕ} (hfac : IsUnit (mu.card.factorial : R))
    (i j : FixedFiniteDegreeIndex mu s d) :
    fixedCommonCoefficientOver (StandardYoungTableau.rowSuperstandard mu) i.val
      (adaptedFixedPolynomial R j (StandardYoungTableau.rowSuperstandard mu)) =
        if i = j then 1 else 0 :=
  pairing_inversePairingFamily _ _ (commonPairingMatrix_det_isUnit R mu s d hfac) i j

theorem map_adaptedFixedPolynomial {S : Type*} [CommRing S] (f : R →+* S)
    {mu : YoungDiagram} {s d : ℕ} (hfac : IsUnit (mu.card.factorial : R))
    (i : FixedFiniteDegreeIndex mu s d) (T : StandardYoungTableau mu) :
    MvPolynomial.map f (adaptedFixedPolynomial R i T) = adaptedFixedPolynomial S i T := by
  have hinv := map_matrix_inverse_of_isUnit f (commonPairingMatrix R mu s d)
    (commonPairingMatrix_det_isUnit R mu s d hfac)
  rw [commonPairingMatrix_map f] at hinv
  simp only [adaptedFixedPolynomial, map_sum, MvPolynomial.smul_eq_C_mul, map_mul,
    MvPolynomial.map_C, fixedGriffinPolynomial, map_higherSpechtPolynomial,
    map_elementaryMultiplier]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← congrArg (fun A => A j i) hinv]
  rfl

def finiteHarmonicToDegree {n s : ℕ} (i : FiniteHarmonicIndex n s) :
    FixedFiniteDegreeIndex (YoungDiagram.ofPartition i.part) s
      i.toUnboundedHarmonicIndex.degree :=
  ⟨finiteHarmonicToFixed i, rfl⟩

def adaptedMasterPolynomial (R : Type*) [CommRing R] {n s : ℕ}
    (i : FiniteHarmonicIndex n s)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) : PolynomialRing n R :=
  rename (finCongr (YoungDiagram.card_ofPartition i.part))
    (adaptedFixedPolynomial R (finiteHarmonicToDegree i) T)

theorem adaptedMasterPolynomial_isHomogeneous (R : Type*) [CommRing R]
    {n s : ℕ} (i : FiniteHarmonicIndex n s)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) :
    (adaptedMasterPolynomial R i T).IsHomogeneous i.toUnboundedHarmonicIndex.degree :=
  (adaptedFixedPolynomial_isHomogeneous R (finiteHarmonicToDegree i) T).rename_isHomogeneous

end HigherSpecht
end
end CanonicalSource15

section CanonicalSource16
/- Source: HigherSpecht/YoungCornerPairing.lean -/



/-!
# Whole-copy orthogonality from the opposite primitive lines

Right multiplication between actual Young left ideals proves that a
cross-shape corner of the group algebra is zero.  The same-shape corner is
one dimensional by the verified Young sandwich lemma.  Inverting group
elements gives the opposite corner used by the manuscript's symmetrizer.
These group-algebra identities prove the required apolar orthogonality of
entire cyclic copies; a single matrix entry is never silently substituted
for that assertion.
-/

noncomputable section
open TauCeti TauCeti.YoungTableau Module MvPolynomial
open scoped Classical

namespace HigherSpecht

def youngRightMultiplication {n : ℕ} (mu nu : n.Partition)
    (a : MonoidAlgebra ℚ (Equiv.Perm (Fin n))) :
    Representation.IntertwiningMap (YoungIdealRepresentation (K := ℚ) mu)
      (YoungIdealRepresentation (K := ℚ) nu) where
  toLinearMap :=
    { toFun := fun x => ⟨x.val * a * nu.youngSymmetrizer ℚ,
        Ideal.mem_span_singleton'.mpr ⟨x.val * a, rfl⟩⟩
      map_add' := fun x y => Subtype.ext (by simp only [Submodule.coe_add, add_mul])
      map_smul' := fun c x => Subtype.ext (by simp only [Submodule.coe_smul_of_tower, smul_mul_assoc, RingHom.id_apply]) }
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      YoungIdealRepresentation, TauCeti.Representation.ofModule'_apply,
      Submodule.coe_smul, smul_eq_mul]
    simp only [mul_assoc]

theorem partitionYoungCorner_eq_zero {n : ℕ} {mu nu : n.Partition}
    (hne : mu ≠ nu) (a : MonoidAlgebra ℚ (Equiv.Perm (Fin n))) :
    mu.youngSymmetrizer ℚ * a * nu.youngSymmetrizer ℚ = 0 := by
  let f := youngRightMultiplication mu nu a
  let em := canonicalYoungIdealSpechtEquiv mu
  let en := canonicalYoungIdealSpechtEquiv nu
  let g := en.toIntertwiningMap.comp (f.comp em.symm.toIntertwiningMap)
  letI : Representation.IsIrreducible (spechtModule mu).ρ := isIrreducible_spechtModule mu
  letI : Representation.IsIrreducible (spechtModule nu).ρ := isIrreducible_spechtModule nu
  have hg : g = 0 := by
    rcases Representation.IsIrreducible.bijective_or_eq_zero g with hb | hz
    · exfalso
      apply hne
      apply (spechtModule_iso_iff mu nu).mp
      exact nonempty_fdRepIso_iff.mpr ⟨g.ofBijective hb⟩
    · exact hz
  have hf : f = 0 := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change f x = 0
    apply en.injective
    change en (f x) = en 0
    rw [map_zero]
    have h := DFunLike.congr_fun hg (em x)
    simpa only [g, Representation.IntertwiningMap.comp_apply,
      Representation.Equiv.coe_toIntertwiningMap, Representation.Equiv.symm_apply_apply,
      Representation.IntertwiningMap.coe_zero, Pi.zero_apply, map_zero] using h
  have h := DFunLike.congr_fun hf (spanSingletonGenerator (mu.youngSymmetrizer ℚ))
  have hv := congrArg Subtype.val h
  change (spanSingletonGenerator (mu.youngSymmetrizer ℚ) :
      MonoidAlgebra ℚ (Equiv.Perm (Fin n))) * a * nu.youngSymmetrizer ℚ = 0 at hv
  simpa only [coe_spanSingletonGenerator] using hv

theorem partitionYoungCorner_scalar {n : ℕ} (mu : n.Partition)
    (a : MonoidAlgebra ℚ (Equiv.Perm (Fin n))) :
    ∃ c : ℚ, mu.youngSymmetrizer ℚ * a * mu.youngSymmetrizer ℚ =
      c • mu.youngSymmetrizer ℚ := by
  let T := (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition mu)).toTableau
  obtain ⟨c, hc⟩ := exists_eq_smul_youngSymmetrizer_mul_mul T
    ((partitionLabelAlgebraEquiv mu).symm a)
  refine ⟨c, ?_⟩
  have h := congrArg (partitionLabelAlgebraEquiv mu) hc
  simpa only [map_mul, map_smul, AlgEquiv.apply_symm_apply,
    partitionLabelAlgebraEquiv_generator, T] using h

def partitionPaperSymmetrizer (K : Type*) [CommRing K] [Algebra ℚ K]
    {n : ℕ} (mu : n.Partition) : MonoidAlgebra K (Equiv.Perm (Fin n)) :=
  inverseGroupAlgebra (mu.youngSymmetrizer K)

theorem partitionPaperCorner_eq_zero_rat {n : ℕ} {mu nu : n.Partition}
    (hne : mu ≠ nu) (a : MonoidAlgebra ℚ (Equiv.Perm (Fin n))) :
    partitionPaperSymmetrizer ℚ mu * a * partitionPaperSymmetrizer ℚ nu = 0 := by
  have h := congrArg inverseGroupAlgebra
    (partitionYoungCorner_eq_zero hne.symm (inverseGroupAlgebra a))
  simpa only [inverseGroupAlgebra_mul, inverseGroupAlgebra_involutive,
    map_zero, partitionPaperSymmetrizer, mul_assoc] using h

theorem partitionPaperCorner_scalar_rat {n : ℕ} (mu : n.Partition)
    (a : MonoidAlgebra ℚ (Equiv.Perm (Fin n))) :
    ∃ c : ℚ, partitionPaperSymmetrizer ℚ mu * a * partitionPaperSymmetrizer ℚ mu =
      c • partitionPaperSymmetrizer ℚ mu := by
  obtain ⟨c, hc⟩ := partitionYoungCorner_scalar mu (inverseGroupAlgebra a)
  refine ⟨c, ?_⟩
  have h := congrArg inverseGroupAlgebra hc
  simpa only [inverseGroupAlgebra_mul, inverseGroupAlgebra_involutive,
    map_smul, partitionPaperSymmetrizer, mul_assoc] using h

theorem map_partitionPaperSymmetrizer {K : Type*} [CommRing K] [Algebra ℚ K]
    {n : ℕ} (mu : n.Partition) :
    MonoidAlgebra.mapAlgHom _ (Algebra.ofId ℚ K) (partitionPaperSymmetrizer ℚ mu) =
      partitionPaperSymmetrizer K mu := by
  ext g
  simp only [MonoidAlgebra.coeff_mapAlgHom, partitionPaperSymmetrizer,
    inverseGroupAlgebra_coeff, Nat.Partition.youngSymmetrizer_def,
    MonoidAlgebra.coeff_domCongr, youngSymmetrizerOver_coeff,
    Algebra.ofId_apply, Algebra.algebraMap_self, RingHom.id_apply]

theorem partitionPaperCorner_eq_zero {n : ℕ} {mu nu : n.Partition}
    (hne : mu ≠ nu) (g : Equiv.Perm (Fin n)) :
    partitionPaperSymmetrizer ℂ mu * MonoidAlgebra.single g 1 *
      partitionPaperSymmetrizer ℂ nu = 0 := by
  have h := congrArg (MonoidAlgebra.mapAlgHom _ (Algebra.ofId ℚ ℂ))
    (partitionPaperCorner_eq_zero_rat hne (MonoidAlgebra.single g 1))
  simpa only [map_mul, map_zero, map_partitionPaperSymmetrizer,
    MonoidAlgebra.mapAlgHom_single, map_one] using h

theorem partitionPaperCorner_scalar {n : ℕ} (mu : n.Partition)
    (g : Equiv.Perm (Fin n)) :
    ∃ c : ℂ, partitionPaperSymmetrizer ℂ mu * MonoidAlgebra.single g 1 *
      partitionPaperSymmetrizer ℂ mu = c • partitionPaperSymmetrizer ℂ mu := by
  obtain ⟨c, hc⟩ := partitionPaperCorner_scalar_rat mu (MonoidAlgebra.single g 1)
  refine ⟨algebraMap ℚ ℂ c, ?_⟩
  have h := congrArg (MonoidAlgebra.mapAlgHom _ (Algebra.ofId ℚ ℂ)) hc
  simpa only [map_mul, map_smul, map_partitionPaperSymmetrizer,
    MonoidAlgebra.mapAlgHom_single, map_one, algebraMap_smul] using h

theorem partitionPaperSymmetrizer_sq {n : ℕ} (mu : n.Partition) :
    partitionPaperSymmetrizer ℂ mu * partitionPaperSymmetrizer ℂ mu =
      youngQuasiScalar (K := ℂ) mu • partitionPaperSymmetrizer ℂ mu := by
  have h := congrArg inverseGroupAlgebra (mu.youngSymmetrizer_mul_self ℂ)
  simpa only [inverseGroupAlgebra_mul, map_smul, partitionPaperSymmetrizer,
    youngQuasiScalar] using h

theorem ordinaryApolar_primitive_shift_eq_zero {n : ℕ} (mu nu : n.Partition)
    (a b : PolynomialRing n ℂ)
    (hzero : mu = nu → ordinaryApolarFunctional
      ((polynomialRepresentation ℂ n).asAlgebraHom (mu.youngSymmetrizer ℂ) a)
      ((polynomialRepresentation ℂ n).asAlgebraHom (partitionPaperSymmetrizer ℂ nu) b) = 0)
    (g : Equiv.Perm (Fin n)) :
    ordinaryApolarFunctional
      ((polynomialRepresentation ℂ n).asAlgebraHom (mu.youngSymmetrizer ℂ) a)
      (rename g ((polynomialRepresentation ℂ n).asAlgebraHom
        (partitionPaperSymmetrizer ℂ nu) b)) = 0 := by
  let rho := polynomialRepresentation ℂ n
  have hcorner (u : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) :
      ordinaryApolarFunctional (rho.asAlgebraHom (mu.youngSymmetrizer ℂ) a)
        (rho.asAlgebraHom u (rho.asAlgebraHom (partitionPaperSymmetrizer ℂ nu) b)) =
      ordinaryApolarFunctional a (rho.asAlgebraHom
        (partitionPaperSymmetrizer ℂ mu * u * partitionPaperSymmetrizer ℂ nu) b) := by
    rw [ordinaryApolar_groupAlgebra_adjoint]
    simp only [partitionPaperSymmetrizer, map_mul, Module.End.mul_apply, rho]
  have hmain := hcorner (MonoidAlgebra.single g 1)
  simp only [Representation.asAlgebraHom_single, one_smul,
    polynomialRepresentation_apply, rho] at hmain
  rw [hmain]
  by_cases heq : mu = nu
  · subst nu
    have hz := hzero rfl
    rw [ordinaryApolar_groupAlgebra_adjoint] at hz
    change ordinaryApolarFunctional a (rho.asAlgebraHom
      (partitionPaperSymmetrizer ℂ mu)
        (rho.asAlgebraHom (partitionPaperSymmetrizer ℂ mu) b)) = 0 at hz
    rw [← Module.End.mul_apply, ← map_mul] at hz
    rw [partitionPaperSymmetrizer_sq, map_smul, LinearMap.smul_apply, map_smul,
      smul_eq_mul] at hz
    have hbase : ordinaryApolarFunctional a
        (rho.asAlgebraHom (partitionPaperSymmetrizer ℂ mu) b) = 0 :=
      (mul_eq_zero.mp hz).resolve_left (youngQuasiScalar_ne_zero mu)
    obtain ⟨c, hc⟩ := partitionPaperCorner_scalar mu g
    rw [hc, map_smul, LinearMap.smul_apply, map_smul, hbase, smul_zero]
  · rw [partitionPaperCorner_eq_zero heq, map_zero, LinearMap.zero_apply, map_zero]

end HigherSpecht
end
end CanonicalSource16

section CanonicalSource17
/- Source: HigherSpecht/AdaptedPrimitiveCopies.lean -/



/-!
# The actual primitive lines of the simultaneous polynomial family

The inverse pairing matrix is applied to literal polynomial representatives.
Their reference-tableau values are in the image of the opposite Young
operator, and every other right-tableau value is its genuine permutation
translate.  These are the hypotheses needed by the whole-copy corner
argument, rather than a scalar pairing standing in for that argument.
-/

noncomputable section
open TauCeti TauCeti.YoungTableau Module MvPolynomial Matrix
open scoped Classical

namespace HigherSpecht

def standardTableauRelabel {mu : YoungDiagram}
    (T U : StandardYoungTableau mu) : Equiv.Perm (Fin mu.card) :=
  Classical.choose (exists_relabel_eq T.toTableau U.toTableau)

theorem standardTableauRelabel_spec {mu : YoungDiagram}
    (T U : StandardYoungTableau mu) :
    relabel (standardTableauRelabel T U) T.toTableau = U.toTableau :=
  Classical.choose_spec (exists_relabel_eq T.toTableau U.toTableau)

theorem higherSpechtPolynomial_right_relabel {R : Type*} [CommRing R]
    {mu : YoungDiagram} (S T U : StandardYoungTableau mu) :
    rename (standardTableauRelabel T U) (higherSpechtPolynomial (R := R) S T) =
      higherSpechtPolynomial S U := by
  let g := standardTableauRelabel T U
  have hT : (spechtSubrepresentationOver R mu).toRepresentation g
      (standardPolytabloidOver T) = standardPolytabloidOver U := by
    apply Subtype.ext
    change tabloidRepresentationOver R mu g (polytabloidOver R T.toTableau) =
      polytabloidOver R U.toTableau
    rw [← polytabloidOver_relabel, standardTableauRelabel_spec]
  have h := DFunLike.congr_fun ((higherSpechtIntertwinerOver (R := R) S).isIntertwining' g)
    (standardPolytabloidOver T)
  simp only [LinearMap.comp_apply, Representation.IntertwiningMap.coe_toLinearMap] at h
  rw [hT] at h
  simpa only [higherSpechtIntertwinerOver_standard, polynomialRepresentation_apply, g]
    using h.symm

theorem fixedGriffinPolynomial_right_relabel {R : Type*} [CommRing R]
    {mu : YoungDiagram} {s : ℕ} (i : FixedFiniteHarmonicIndex mu s)
    (T U : StandardYoungTableau mu) :
    rename (standardTableauRelabel T U) (fixedGriffinPolynomial (R := R) T i) =
      fixedGriffinPolynomial U i := by
  simp only [fixedGriffinPolynomial, map_mul, higherSpechtPolynomial_right_relabel]
  rw [elementaryMultiplier_isSymmetric _ _ _ (standardTableauRelabel T U)]

theorem adaptedFixedPolynomial_right_relabel {R : Type*} [CommRing R]
    {mu : YoungDiagram} {s d : ℕ} (i : FixedFiniteDegreeIndex mu s d)
    (T U : StandardYoungTableau mu) :
    rename (standardTableauRelabel T U) (adaptedFixedPolynomial R i T) =
      adaptedFixedPolynomial R i U := by
  simp only [adaptedFixedPolynomial, map_sum, map_smul, fixedGriffinPolynomial_right_relabel]

def fixedMasterPrePolynomial {mu : YoungDiagram} {s : ℕ}
    (i : FixedFiniteHarmonicIndex mu s) : PolynomialRing mu.card ℂ :=
  monomial (transportedCocharge i.left
    (StandardYoungTableau.rowSuperstandard mu).toTableau) 1 *
      elementaryMultiplier mu.card mu.card i.multiplier.rowLen

theorem fixedMasterPrePolynomial_paperImage {mu : YoungDiagram} {s : ℕ}
    (i : FixedFiniteHarmonicIndex mu s) :
    (polynomialRepresentation ℂ mu.card).asAlgebraHom
      (paperYoungSymmetrizerOver ℂ (StandardYoungTableau.rowSuperstandard mu).toTableau)
      (fixedMasterPrePolynomial i) =
        fixedGriffinPolynomial (StandardYoungTableau.rowSuperstandard mu) i := by
  rw [asAlgebraHom_paperYoungSymmetrizer, fixedMasterPrePolynomial,
    youngApply_mul_elementaryMultiplier]
  simp only [fixedGriffinPolynomial, higherSpechtPolynomial, YoungDiagram.card,
    YoungDiagram.cells_bot, Finset.card_empty, Nat.sub_zero]

def adaptedFixedPrePolynomial {mu : YoungDiagram} {s d : ℕ}
    (i : FixedFiniteDegreeIndex mu s d) : PolynomialRing mu.card ℂ :=
  ∑ j, (commonPairingMatrix ℂ mu s d)⁻¹ j i • fixedMasterPrePolynomial j.val

theorem adaptedFixedPrePolynomial_paperImage {mu : YoungDiagram} {s d : ℕ}
    (i : FixedFiniteDegreeIndex mu s d) :
    (polynomialRepresentation ℂ mu.card).asAlgebraHom
      (paperYoungSymmetrizerOver ℂ (StandardYoungTableau.rowSuperstandard mu).toTableau)
      (adaptedFixedPrePolynomial i) =
        adaptedFixedPolynomial ℂ i (StandardYoungTableau.rowSuperstandard mu) := by
  simp only [adaptedFixedPrePolynomial, map_sum, map_smul,
    fixedMasterPrePolynomial_paperImage, adaptedFixedPolynomial]

theorem inverseGroupAlgebra_domCongr {n m : ℕ} (e : Fin n ≃ Fin m)
    (a : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) :
    inverseGroupAlgebra (MonoidAlgebra.domCongr ℂ ℂ e.permCongrHom a) =
      MonoidAlgebra.domCongr ℂ ℂ e.permCongrHom (inverseGroupAlgebra a) := by
  induction a using MonoidAlgebra.induction_on with
  | of g =>
    simp only [MonoidAlgebra.of_apply, MonoidAlgebra.domCongr_single,
      inverseGroupAlgebra_single, map_inv]
  | add a b ha hb => simp only [map_add, ha, hb]
  | smul c a ha => simp only [map_smul, ha]

theorem partitionPaperSymmetrizer_def {n : ℕ} (part : n.Partition) :
    partitionPaperSymmetrizer ℂ part =
      MonoidAlgebra.domCongr ℂ ℂ
        (finCongr (YoungDiagram.card_ofPartition part)).permCongrHom
        (paperYoungSymmetrizerOver ℂ
          (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition part)).toTableau) := by
  rw [partitionPaperSymmetrizer, Nat.Partition.youngSymmetrizer_def,
    inverseGroupAlgebra_domCongr, inverseGroupAlgebra_youngSymmetrizerOver]

def adaptedMasterPrePolynomial {n s : ℕ} (i : FiniteHarmonicIndex n s) : PolynomialRing n ℂ :=
  rename (finCongr (YoungDiagram.card_ofPartition i.part))
    (adaptedFixedPrePolynomial (finiteHarmonicToDegree i))

theorem adaptedMasterPrePolynomial_paperImage {n s : ℕ} (i : FiniteHarmonicIndex n s) :
    (polynomialRepresentation ℂ n).asAlgebraHom (partitionPaperSymmetrizer ℂ i.part)
      (adaptedMasterPrePolynomial i) =
        adaptedMasterPolynomial ℂ i (StandardYoungTableau.rowSuperstandard _) := by
  rw [partitionPaperSymmetrizer_def]
  simp only [adaptedMasterPrePolynomial, polynomial_asAlgebraHom_domCongr_rename,
    adaptedFixedPrePolynomial_paperImage, adaptedMasterPolynomial]

def masterTableauRelabel {n s : ℕ} (i : FiniteHarmonicIndex n s)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) : Equiv.Perm (Fin n) :=
  (finCongr (YoungDiagram.card_ofPartition i.part)).permCongr
    (standardTableauRelabel (StandardYoungTableau.rowSuperstandard _) T)

theorem adaptedMasterPolynomial_right_relabel {R : Type*} [CommRing R]
    {n s : ℕ} (i : FiniteHarmonicIndex n s)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) :
    rename (masterTableauRelabel i T)
      (adaptedMasterPolynomial R i (StandardYoungTableau.rowSuperstandard _)) =
        adaptedMasterPolynomial R i T := by
  unfold adaptedMasterPolynomial masterTableauRelabel
  rw [rename_rename]
  have hfun : (finCongr (YoungDiagram.card_ofPartition i.part)).permCongr
        (standardTableauRelabel (StandardYoungTableau.rowSuperstandard _) T) ∘
        finCongr (YoungDiagram.card_ofPartition i.part) =
      finCongr (YoungDiagram.card_ofPartition i.part) ∘
        standardTableauRelabel (StandardYoungTableau.rowSuperstandard _) T := by
    funext j
    simp only [Function.comp_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rw [hfun, ← rename_rename, adaptedFixedPolynomial_right_relabel]

theorem ordinaryApolar_homogeneous_eq_zero {n d e : ℕ}
    {p q : PolynomialRing n ℂ} (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous e)
    (hde : d ≠ e) : ordinaryApolarFunctional p q = 0 := by
  rw [q.as_sum, map_sum]
  apply Finset.sum_eq_zero
  intro a ha
  have hqa : q.coeff a ≠ 0 := mem_support_iff.mp ha
  have hae : a.degree = e := by
    by_contra he
    exact hqa (hq.coeff_eq_zero he)
  have hpa : p.coeff a = 0 := hp.coeff_eq_zero (by omega)
  have hm : monomial a (q.coeff a) = q.coeff a • monomial a (1 : ℂ) := by
    simp only [smul_monomial, smul_eq_mul, mul_one]
  rw [hm, map_smul, ordinaryApolar_monomial, hpa, zero_mul, smul_zero]

theorem ordinaryApolar_fixedCommon_adapted {mu : YoungDiagram} {s d : ℕ}
    (i j : FixedFiniteDegreeIndex mu s d) :
    ordinaryApolarFunctional
      (fixedCommonHarmonicVector (StandardYoungTableau.rowSuperstandard mu) i.val)
      (adaptedFixedPolynomial ℂ j (StandardYoungTableau.rowSuperstandard mu)) =
        fixedCommonPairingScalar (StandardYoungTableau.rowSuperstandard mu) i.val *
          if i = j then 1 else 0 := by
  have hfac : IsUnit (mu.card.factorial : ℂ) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr mu.card.factorial_ne_zero)
  calc
    _ = fixedCommonPairingScalar (StandardYoungTableau.rowSuperstandard mu) i.val *
        fixedCommonCoefficientOver (StandardYoungTableau.rowSuperstandard mu) i.val
          (adaptedFixedPolynomial ℂ j (StandardYoungTableau.rowSuperstandard mu)) := by
      simp only [adaptedFixedPolynomial, map_sum, map_smul, smul_eq_mul,
        ordinaryApolar_fixedCommonHarmonicVector, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      rw [show fixedCommonWitnessFunctional (StandardYoungTableau.rowSuperstandard mu) i.val =
        fixedCommonCoefficientOver (R := ℂ) (StandardYoungTableau.rowSuperstandard mu) i.val by
          unfold fixedCommonWitnessFunctional fixedCommonCoefficientOver
          rfl]
      ring
    _ = _ := by rw [fixedCommonCoefficientOver_adapted ℂ hfac]

end HigherSpecht
end
end CanonicalSource17

section CanonicalSource18
/- Source: HigherSpecht/AdaptedIdealMembership.lean -/



/-!
# Ineligible modified polynomials lie in the actual ideals

The fixed-line inverse pairing is combined with the true Young corner
calculation.  This proves orthogonality against every permutation translate
of every other common harmonic vector.  Finite apolar double annihilation
then proves membership in the literal ideal, for every finite ideal
expression.  This is stronger than vanishing of a reference-tableau scalar.
-/

noncomputable section
open TauCeti TauCeti.YoungTableau Module MvPolynomial
open scoped Classical

namespace HigherSpecht

theorem ordinaryApolar_fixedCommon_adapted_ne {mu : YoungDiagram} {s : ℕ}
    (j i : FixedFiniteHarmonicIndex mu s) (hne : j ≠ i) :
    ordinaryApolarFunctional
      (fixedCommonHarmonicVector (StandardYoungTableau.rowSuperstandard mu) j)
      (adaptedFixedPolynomial ℂ
        (⟨i, rfl⟩ : FixedFiniteDegreeIndex mu s (cochargeDegree i.left + i.multiplier.card))
        (StandardYoungTableau.rowSuperstandard mu)) = 0 := by
  by_cases hd : cochargeDegree j.left + j.multiplier.card =
      cochargeDegree i.left + i.multiplier.card
  · let j' : FixedFiniteDegreeIndex mu s (cochargeDegree i.left + i.multiplier.card) := ⟨j, hd⟩
    let i' : FixedFiniteDegreeIndex mu s (cochargeDegree i.left + i.multiplier.card) := ⟨i, rfl⟩
    have hji : j' ≠ i' := fun h => hne (congrArg Subtype.val h)
    have h := ordinaryApolar_fixedCommon_adapted j' i'
    simpa only [if_neg hji, mul_zero, j', i'] using h
  · exact ordinaryApolar_homogeneous_eq_zero
      (fixedCommonHarmonicVector_isHomogeneous _ j)
      (adaptedFixedPolynomial_isHomogeneous ℂ _ _) hd

theorem ordinaryApolar_common_adapted_samePart_ne {n s : ℕ}
    (j i : FiniteHarmonicIndex n s) (hne : j ≠ i) (hpart : j.part = i.part) :
    ordinaryApolarFunctional (finiteCommonHarmonicVector j)
      (adaptedMasterPolynomial ℂ i (StandardYoungTableau.rowSuperstandard _)) = 0 := by
  obtain ⟨⟨partj, j'⟩, rfl⟩ := (finiteHarmonicIndexEquiv n s).symm.surjective j
  obtain ⟨⟨parti, i'⟩, rfl⟩ := (finiteHarmonicIndexEquiv n s).symm.surjective i
  change partj = parti at hpart
  subst partj
  have hji : j' ≠ i' := fun h => hne (by cases h; rfl)
  change ordinaryApolarFunctional (finiteCommonHarmonicVector (fixedFiniteToHarmonic parti j'))
    (adaptedMasterPolynomial ℂ (fixedFiniteToHarmonic parti i')
      (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition parti))) = 0
  have hadapted : adaptedMasterPolynomial ℂ (fixedFiniteToHarmonic parti i')
      (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition parti)) =
    rename (finCongr (YoungDiagram.card_ofPartition parti))
      (adaptedFixedPolynomial ℂ
        (⟨i', rfl⟩ : FixedFiniteDegreeIndex (YoungDiagram.ofPartition parti) s
          (cochargeDegree i'.left + i'.multiplier.card))
        (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition parti))) := by
    rfl
  rw [finiteCommonHarmonicVector_toFixed, hadapted, ordinaryApolar_rename_finCongr]
  exact ordinaryApolar_fixedCommon_adapted_ne j' i' hji

theorem ordinaryApolar_common_adapted_shift_ne {n s : ℕ}
    (j i : FiniteHarmonicIndex n s) (hne : j ≠ i) (g : Equiv.Perm (Fin n)) :
    ordinaryApolarFunctional (finiteCommonHarmonicVector j)
      (rename g (adaptedMasterPolynomial ℂ i
        (StandardYoungTableau.rowSuperstandard _))) = 0 := by
  rw [← finiteCommonHarmonicVector_youngImage,
    ← adaptedMasterPrePolynomial_paperImage]
  apply ordinaryApolar_primitive_shift_eq_zero j.part i.part
    (finiteCommonPreVector j) (adaptedMasterPrePolynomial i)
  intro hpart
  rw [finiteCommonHarmonicVector_youngImage, adaptedMasterPrePolynomial_paperImage]
  exact ordinaryApolar_common_adapted_samePart_ne j i hne hpart

theorem ordinaryApolar_common_translate_adapted_ne {n s : ℕ}
    (j i : FiniteHarmonicIndex n s) (hne : j ≠ i)
    (g : Equiv.Perm (Fin n))
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) :
    ordinaryApolarFunctional (rename g (finiteCommonHarmonicVector j))
      (adaptedMasterPolynomial ℂ i T) = 0 := by
  rw [ordinaryApolar_rename_adjoint, ← adaptedMasterPolynomial_right_relabel i T,
    rename_rename]
  simpa only [Equiv.Perm.coe_mul, Equiv.symm_apply_apply] using
    ordinaryApolar_common_adapted_shift_ne j i hne (g.symm * masterTableauRelabel i T)

theorem ordinaryApolar_commonCopy_adapted_ne {n s : ℕ}
    (j i : FiniteHarmonicIndex n s) (hne : j ≠ i)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part))
    (p : PolynomialRing n ℂ) (hp : p ∈ finiteCommonHarmonicCopy j) :
    ordinaryApolarFunctional p (adaptedMasterPolynomial ℂ i T) = 0 := by
  let L : Module.Dual ℂ (PolynomialRing n ℂ) :=
    (LinearMap.applyₗ (adaptedMasterPolynomial ℂ i T)).comp (ordinaryApolarRepresenter n)
  have hle : finiteCommonHarmonicCopy j ≤ LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact ordinaryApolar_common_translate_adapted_ne j i hne g T
  exact hle hp

namespace GriffinIdealExpression

theorem adaptedPolynomial_mem_of_ineligible {n s : ℕ}
    (e : GriffinIdealExpression n s) (hs : 0 < s)
    (i : FiniteHarmonicIndex n s) (hi : i ∉ e.eligible)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) :
    adaptedMasterPolynomial ℂ i T ∈ e.ideal ℂ := by
  apply (mem_ideal_iff_all_harmonic_pairings_zero (e.ideal ℂ) (e.powerIdeal_le ℂ) _).mpr
  let L : Module.Dual ℂ (PolynomialRing n ℂ) :=
    (LinearMap.applyₗ (adaptedMasterPolynomial ℂ i T)).comp (ordinaryApolarRepresenter n)
  have hle : ordinaryHarmonics (e.ideal ℂ) ≤ LinearMap.ker L := by
    rw [e.harmonic_decomposition hs, independentSubsum]
    apply iSup_le
    intro j
    apply iSup_le
    intro hj p hp
    exact ordinaryApolar_commonCopy_adapted_ne j i (fun h => hi (h ▸ hj)) T p hp
  intro p hp
  exact hle hp

end GriffinIdealExpression

/-- The ideal-membership assertion of Corollary 5.7 for the original
Griffin ideal, without a new orthogonality or basis premise. -/
theorem corollary_5_7_ineligible_mem_complex {n s : ℕ}
    (lam : YoungDiagram) (hk : lam.card ≤ n) (hs : 0 < s)
    (hheight : lam.colLen 0 ≤ s) (i : FiniteHarmonicIndex n s)
    (hi : ¬ i.toUnboundedHarmonicIndex.eligible lam hk)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) :
    adaptedMasterPolynomial ℂ i T ∈ griffinIdeal ℂ n lam s :=
  (GriffinIdealExpression.atom ⟨lam, hk, hheight⟩).adaptedPolynomial_mem_of_ineligible hs i hi T

end HigherSpecht
end
end CanonicalSource18

section CanonicalSource19
/- Source: HigherSpecht/AdaptedComplexBases.lean -/



/-!
# The simultaneous modified basis over the complex numbers

The inverse change of the actual pairing matrix expresses every original
basis vector as a finite combination of modified vectors of the same shape
and degree.  The ineligible terms vanish by actual ideal membership.  A
finite square change-of-generators argument supplies the basis, including
nonvanishing of every eligible vector.
-/

noncomputable section
open TauCeti TauCeti.YoungTableau Module MvPolynomial
open scoped Classical

namespace HigherSpecht

theorem adaptedMasterPolynomial_fixedDegree {R : Type*} [CommRing R]
    {n s d : ℕ} (part : n.Partition)
    (i : FixedFiniteDegreeIndex (YoungDiagram.ofPartition part) s d)
    (T : StandardYoungTableau (YoungDiagram.ofPartition part)) :
    adaptedMasterPolynomial R (fixedFiniteToHarmonic part i.val) T =
      rename (finCongr (YoungDiagram.card_ofPartition part)) (adaptedFixedPolynomial R i T) := by
  rcases i with ⟨i, rfl⟩
  rfl

theorem finiteMaster_eq_sum_adapted {R : Type*} [CommRing R]
    {n s : ℕ} (hfac : IsUnit (n.factorial : R)) (i : FiniteHarmonicIndex n s)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) :
    finiteMasterPolynomial (R := R) i T =
      ∑ j : FixedFiniteDegreeIndex (YoungDiagram.ofPartition i.part) s
          i.toUnboundedHarmonicIndex.degree,
        commonPairingMatrix R (YoungDiagram.ofPartition i.part) s
            i.toUnboundedHarmonicIndex.degree j (finiteHarmonicToDegree i) •
          adaptedMasterPolynomial R (fixedFiniteToHarmonic i.part j.val) T := by
  have hfac' : IsUnit ((YoungDiagram.ofPartition i.part).card.factorial : R) := by
    simpa only [YoungDiagram.card_ofPartition] using hfac
  have h := originalFamily_eq_sum_inverseFamily
    (commonPairingMatrix R (YoungDiagram.ofPartition i.part) s i.toUnboundedHarmonicIndex.degree)
    (commonPairingMatrix_det_isUnit R _ _ _ hfac')
    (fun j : FixedFiniteDegreeIndex (YoungDiagram.ofPartition i.part) s
        i.toUnboundedHarmonicIndex.degree => fixedGriffinPolynomial (R := R) T j.val)
    (finiteHarmonicToDegree i)
  have hr := congrArg (rename (R := R) (finCongr (YoungDiagram.card_ofPartition i.part))) h
  have hadapted (j : FixedFiniteDegreeIndex (YoungDiagram.ofPartition i.part) s
      i.toUnboundedHarmonicIndex.degree) :
      inversePairingFamily
          (commonPairingMatrix R (YoungDiagram.ofPartition i.part) s
            i.toUnboundedHarmonicIndex.degree)
          (fun k => fixedGriffinPolynomial (R := R) T k.val) j = adaptedFixedPolynomial R j T := rfl
  simp only [map_sum, map_smul, hadapted, ← adaptedMasterPolynomial_fixedDegree] at hr
  have hpoly :
      rename (finCongr (YoungDiagram.card_ofPartition i.part))
        (fixedGriffinPolynomial (R := R) T (finiteHarmonicToDegree i).val) =
      finiteMasterPolynomial (R := R) i T := by
    exact (finiteMasterPolynomial_toFixed (R := R) i.part
      (finiteHarmonicToDegree i).val T).symm.trans (by rfl)
  exact hpoly.symm.trans hr

namespace GriffinIdealExpression

def adaptedFamily {n s : ℕ} (e : GriffinIdealExpression n s)
    (R : Type*) [CommRing R] (z : e.VectorIndex) : PolynomialRing n R ⧸ e.ideal R :=
  Ideal.Quotient.mk (e.ideal R) (adaptedMasterPolynomial R z.1.val z.2)

theorem adaptedFamily_span_complex {n s : ℕ}
    (e : GriffinIdealExpression n s) (hs : 0 < s) :
    Submodule.span ℂ (Set.range (e.adaptedFamily ℂ)) = ⊤ := by
  apply top_unique
  rw [← (e.prescribedBasis hs).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨z, rfl⟩
  rw [e.prescribedBasis_apply]
  change Ideal.Quotient.mk (e.ideal ℂ) (finiteMasterPolynomial z.1.val z.2) ∈ _
  rw [finiteMaster_eq_sum_adapted
    (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr n.factorial_ne_zero)), map_sum]
  apply Submodule.sum_mem
  intro j hj
  rw [← Ideal.Quotient.mkₐ_eq_mk ℂ (e.ideal ℂ), map_smul]
  apply Submodule.smul_mem
  by_cases he : fixedFiniteToHarmonic z.1.val.part j.val ∈ e.eligible
  · exact Submodule.subset_span
      ⟨⟨⟨fixedFiniteToHarmonic z.1.val.part j.val, he⟩, z.2⟩, rfl⟩
  · simp only [Ideal.Quotient.mkₐ_eq_mk]
    have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr
      (e.adaptedPolynomial_mem_of_ineligible hs _ he z.2)
    exact hz.symm ▸ Submodule.zero_mem _

def adaptedBasisComplex {n s : ℕ} (e : GriffinIdealExpression n s) (hs : 0 < s) :
    Basis e.VectorIndex ℂ (PolynomialRing n ℂ ⧸ e.ideal ℂ) :=
  Classical.choose (specifiedBasis_of_spanning_same_index (e.prescribedBasis hs)
    (e.adaptedFamily ℂ) (e.adaptedFamily_span_complex hs))

theorem adaptedBasisComplex_apply {n s : ℕ} (e : GriffinIdealExpression n s)
    (hs : 0 < s) (z : e.VectorIndex) : e.adaptedBasisComplex hs z = e.adaptedFamily ℂ z :=
  Classical.choose_spec (specifiedBasis_of_spanning_same_index (e.prescribedBasis hs)
    (e.adaptedFamily ℂ) (e.adaptedFamily_span_complex hs)) z

theorem adaptedFamily_specifiedBasis_complex {n s : ℕ}
    (e : GriffinIdealExpression n s) (hs : 0 < s) :
    IsSpecifiedBasis (R := ℂ) (e.adaptedFamily ℂ) :=
  ⟨e.adaptedBasisComplex hs, e.adaptedBasisComplex_apply hs⟩

theorem adaptedPolynomial_not_mem_of_eligible {n s : ℕ}
    (e : GriffinIdealExpression n s) (hs : 0 < s)
    (i : FiniteHarmonicIndex n s) (hi : i ∈ e.eligible)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) :
    adaptedMasterPolynomial ℂ i T ∉ e.ideal ℂ := by
  intro h
  have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr h
  have hn := (e.adaptedBasisComplex hs).ne_zero ⟨⟨i, hi⟩, T⟩
  apply hn
  rw [e.adaptedBasisComplex_apply]
  exact hz

end GriffinIdealExpression

theorem corollary_5_7_complex {n s : ℕ}
    (lam : YoungDiagram) (hk : lam.card ≤ n) (hs : 0 < s)
    (hheight : lam.colLen 0 ≤ s) :
    let e : GriffinIdealExpression n s := .atom ⟨lam, hk, hheight⟩
    IsSpecifiedBasis (R := ℂ) (e.adaptedFamily ℂ) ∧
      ∀ (i : FiniteHarmonicIndex n s)
        (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)),
        adaptedMasterPolynomial ℂ i T ∈ griffinIdeal ℂ n lam s ↔
          ¬ i.toUnboundedHarmonicIndex.eligible lam hk := by
  let e : GriffinIdealExpression n s := .atom ⟨lam, hk, hheight⟩
  refine ⟨e.adaptedFamily_specifiedBasis_complex hs, ?_⟩
  intro i T
  constructor
  · intro hm he
    exact e.adaptedPolynomial_not_mem_of_eligible hs i he T hm
  · intro hi
    exact e.adaptedPolynomial_mem_of_ineligible hs i hi T

end HigherSpecht
end
end CanonicalSource19

section CanonicalSource20
/- Source: HigherSpecht/GriffinCoefficientReflection.lean -/



/-!
# Coefficient reflection in the actual Griffin quotient

The integral staircase representatives are a basis over every nontrivial
coefficient ring.  Consequently an injective coefficient homomorphism
remains injective on the literal quotient.  This is the torsion-free
descent needed to carry complex orthogonality back to Z[1/n!].
-/

noncomputable section
open TauCeti Module MvPolynomial
open scoped Classical

namespace HigherSpecht

def griffinCoefficientMap {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) (lam : YoungDiagram) (s : ℕ) :
    GriffinRing R n lam s →+* GriffinRing S n lam s :=
  Ideal.quotientMap (griffinIdeal S n lam s) (MvPolynomial.map f)
    (Ideal.map_le_iff_le_comap.mp (map_griffinIdeal f n lam s).le)

@[simp] theorem griffinCoefficientMap_mk {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) (lam : YoungDiagram) (s : ℕ) (p : PolynomialRing n R) :
    griffinCoefficientMap f n lam s (Ideal.Quotient.mk (griffinIdeal R n lam s) p) =
      Ideal.Quotient.mk (griffinIdeal S n lam s) (MvPolynomial.map f p) := rfl

theorem griffinCoefficientMap_smul {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) (lam : YoungDiagram) (s : ℕ)
    (c : R) (x : GriffinRing R n lam s) :
    griffinCoefficientMap f n lam s (c • x) = f c • griffinCoefficientMap f n lam s x := by
  refine Quotient.inductionOn' x ?_
  intro p
  change griffinCoefficientMap f n lam s
    (Ideal.Quotient.mk (griffinIdeal R n lam s) (c • p)) =
      f c • griffinCoefficientMap f n lam s
        (Ideal.Quotient.mk (griffinIdeal R n lam s) p)
  rw [griffinCoefficientMap_mk, griffinCoefficientMap_mk]
  have hmap : MvPolynomial.map f (c • p) = f c • MvPolynomial.map f p := by
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]
  rw [hmap]
  exact map_smul (Ideal.Quotient.mkₐ S (griffinIdeal S n lam s)) (f c) _

theorem griffinCoefficientMap_standardBasis {R S : Type*} [CommRing R] [Nontrivial R]
    [CommRing S] [Nontrivial S] (f : R →+* S)
    {n s : ℕ} (lam : YoungDiagram) (hk : lam.card ≤ n) (hs : 0 < s)
    (hheight : lam.colLen 0 ≤ s) (a : GriffinStaircaseExponents n lam s) :
    griffinCoefficientMap f n lam s (griffinStandardMonomialBasis (R := R) hk s hs hheight a) =
      griffinStandardMonomialBasis (R := S) hk s hs hheight a := by
  simp only [griffinStandardMonomialBasis_apply, griffinCoefficientMap_mk,
    MvPolynomial.map_monomial, map_one]

theorem griffinCoefficientMap_injective {R S : Type*} [CommRing R] [Nontrivial R]
    [CommRing S] [Nontrivial S] (f : R →+* S) (hf : Function.Injective f)
    {n s : ℕ} (lam : YoungDiagram) (hk : lam.card ≤ n) (hs : 0 < s)
    (hheight : lam.colLen 0 ≤ s) : Function.Injective (griffinCoefficientMap f n lam s) := by
  letI := (finite_griffinStaircaseExponents (n := n) (μ := lam) s hs hheight).fintype
  let B := griffinStandardMonomialBasis (R := R) hk s hs hheight
  let C := griffinStandardMonomialBasis (R := S) hk s hs hheight
  apply (injective_iff_map_eq_zero (griffinCoefficientMap f n lam s)).mpr
  intro x hx
  have h := congrArg (griffinCoefficientMap f n lam s) (B.sum_repr x)
  simp only [map_sum, griffinCoefficientMap_smul,
    griffinCoefficientMap_standardBasis, B, hx] at h
  apply B.repr.injective
  ext a
  have ha := congrArg (fun y => C.repr y a) h
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    Basis.repr_self, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, map_zero, Finsupp.zero_apply, C] at ha
  apply hf
  simpa only [map_zero, Finsupp.zero_apply, B] using ha

theorem griffinIdeal_mem_iff_coefficientMap {R S : Type*}
    [CommRing R] [Nontrivial R] [CommRing S] [Nontrivial S]
    (f : R →+* S) (hf : Function.Injective f)
    {n s : ℕ} (lam : YoungDiagram) (hk : lam.card ≤ n) (hs : 0 < s)
    (hheight : lam.colLen 0 ≤ s) (p : PolynomialRing n R) :
    p ∈ griffinIdeal R n lam s ↔ MvPolynomial.map f p ∈ griffinIdeal S n lam s := by
  constructor
  · intro hp
    rw [← map_griffinIdeal f n lam s]
    exact Ideal.mem_map_of_mem _ hp
  · intro hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply griffinCoefficientMap_injective f hf lam hk hs hheight
    rw [map_zero, griffinCoefficientMap_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hp

def factorialLocalizationMap (R : Type*) [CommRing R] (n : ℕ)
    (hfac : IsUnit (n.factorial : R)) : FactorialLocalization n →+* R :=
  IsLocalization.Away.lift (n.factorial : ℤ)
    (show IsUnit ((Int.castRingHom R) (n.factorial : ℤ)) by simpa using hfac)

/-- The actual localization is nontrivial: its canonical map to the rationals
preserves zero and one, and the rational factorial is nonzero. -/
instance factorialLocalization_nontrivial (n : ℕ) : Nontrivial (FactorialLocalization n) :=
  (factorialLocalizationMap ℚ n
    (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr n.factorial_ne_zero))).domain_nontrivial

@[simp] theorem factorialLocalizationMap_int (R : Type*) [CommRing R] (n : ℕ)
    (hfac : IsUnit (n.factorial : R)) (z : ℤ) :
    factorialLocalizationMap R n hfac (algebraMap ℤ (FactorialLocalization n) z) = (z : R) :=
  IsLocalization.Away.lift_eq _ _ z

theorem factorialLocalizationMap_complex_injective (n : ℕ) :
    Function.Injective (factorialLocalizationMap ℂ n
      (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr n.factorial_ne_zero))) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (n.factorial : ℤ)) _).mpr
  intro a b
  rw [factorialLocalizationMap_int, factorialLocalizationMap_int]
  have hfac : (n.factorial : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hinj : Function.Injective (algebraMap ℤ (FactorialLocalization n)) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hfac)
  rw [hinj.eq_iff]
  exact Int.cast_inj.symm

end HigherSpecht
end
end CanonicalSource20

section CanonicalSource21
/- Source: HigherSpecht/AdaptedCoefficientDescent.lean -/



/-!
# Descent of simultaneous ideal membership to Z[1/n!]

The modified polynomials are defined by the same integral pairing matrix in
each coefficient ring.  Naturality of its actual inverse gives coefficient
compatibility.  The staircase basis reflects ideal membership from complex
coefficients to the localization, after which ordinary coefficient extension
proves it over every ring where n! is a unit.
-/

noncomputable section
open TauCeti TauCeti.YoungTableau Module MvPolynomial
open scoped Classical

namespace HigherSpecht

theorem map_adaptedMasterPolynomial {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {n s : ℕ} (hfac : IsUnit (n.factorial : R))
    (i : FiniteHarmonicIndex n s)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) :
    MvPolynomial.map f (adaptedMasterPolynomial R i T) = adaptedMasterPolynomial S i T := by
  rw [adaptedMasterPolynomial, MvPolynomial.map_rename,
    map_adaptedFixedPolynomial f (by simpa only [YoungDiagram.card_ofPartition] using hfac)]
  rfl

theorem adaptedPolynomial_mem_localization {n s : ℕ}
    (lam : YoungDiagram) (hk : lam.card ≤ n) (hs : 0 < s)
    (hheight : lam.colLen 0 ≤ s) (i : FiniteHarmonicIndex n s)
    (hi : ¬ i.toUnboundedHarmonicIndex.eligible lam hk)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) :
    adaptedMasterPolynomial (FactorialLocalization n) i T ∈
      griffinIdeal (FactorialLocalization n) n lam s := by
  let f := factorialLocalizationMap ℂ n
    (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr n.factorial_ne_zero))
  apply (griffinIdeal_mem_iff_coefficientMap f
    (factorialLocalizationMap_complex_injective n) lam hk hs hheight _).mpr
  rw [map_adaptedMasterPolynomial f (factorial_isUnit_localization n)]
  exact corollary_5_7_ineligible_mem_complex lam hk hs hheight i hi T

theorem adaptedPolynomial_mem_of_ineligible {R : Type*} [CommRing R]
    {n s : ℕ} (hfac : IsUnit (n.factorial : R))
    (lam : YoungDiagram) (hk : lam.card ≤ n) (hs : 0 < s)
    (hheight : lam.colLen 0 ≤ s) (i : FiniteHarmonicIndex n s)
    (hi : ¬ i.toUnboundedHarmonicIndex.eligible lam hk)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) :
    adaptedMasterPolynomial R i T ∈ griffinIdeal R n lam s := by
  let f := factorialLocalizationMap R n hfac
  have hm := Ideal.mem_map_of_mem (MvPolynomial.map f)
    (adaptedPolynomial_mem_localization lam hk hs hheight i hi T)
  rw [map_griffinIdeal, map_adaptedMasterPolynomial f (factorial_isUnit_localization n)] at hm
  exact hm

theorem elementaryMultiplier_truncate {R : Type*} [CommRing R]
    (n : ℕ) {m l : ℕ} (hml : m ≤ l) (eta : YoungDiagram) (heta : eta.colLen 0 ≤ m) :
    elementaryMultiplier (R := R) n l eta.rowLen = elementaryMultiplier n m eta.rowLen := by
  symm
  apply Finset.prod_subset (Finset.range_mono hml)
  intro j hj hnj
  have hmj : m ≤ j := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hnj)
  rw [YoungDiagram.rowLen_eq_zero_of_colLen_le (heta.trans hmj), Nat.zero_sub, pow_zero]

theorem eligibleHarmonicTableauEquiv_polynomial {R : Type*} [CommRing R]
    {n s : ℕ} (lam : YoungDiagram) (hk : lam.card ≤ n)
    (z : EligibleHarmonicTableauIndex n s lam hk) :
    griffinPolynomial (R := R) (eligibleHarmonicTableauEquiv n s lam hk z) =
      finiteMasterPolynomial z.1.val z.2 := by
  change rename (finCongr (YoungDiagram.card_ofPartition z.1.val.part))
      (higherSpechtPolynomial z.1.val.left z.2) *
        elementaryMultiplier n (n - lam.card) z.1.val.multiplier.rowLen = _
  rw [finiteMasterPolynomial,
    elementaryMultiplier_truncate n (Nat.sub_le n lam.card) _ z.1.property.1]

end HigherSpecht
end
end CanonicalSource21

section CanonicalSource22
/- Source: HigherSpecht/AdaptedLocalizedBases.lean -/



/-!
# Corollary 5.7 over the actual localization and admissible fields

The same inverse matrix defines the polynomial family over every ring in
which n! is a unit.  The old prescribed basis and the literal inverse change
prove spanning; actual ineligible ideal membership removes exactly the
unwanted summands.  Thus all eligible right tableaux form a basis over the
localization itself, not only after extending scalars to a field.
-/

noncomputable section
open TauCeti TauCeti.YoungTableau Module MvPolynomial
open scoped Classical

namespace HigherSpecht

def adaptedGriffinFamily (R : Type*) [CommRing R] {n s : ℕ}
    (lam : YoungDiagram) (hk : lam.card ≤ n)
    (z : EligibleHarmonicTableauIndex n s lam hk) : GriffinRing R n lam s :=
  Ideal.Quotient.mk (griffinIdeal R n lam s) (adaptedMasterPolynomial R z.1.val z.2)

def originalMasterGriffinBasis (R : Type*) [CommRing R] [Nontrivial R]
    {n s : ℕ} (hfac : IsUnit (n.factorial : R))
    (lam : YoungDiagram) (hk : lam.card ≤ n) (hs : 0 < s)
    (hheight : lam.colLen 0 ≤ s) :
    Basis (EligibleHarmonicTableauIndex n s lam hk) R (GriffinRing R n lam s) :=
  (Classical.choose (griffin_specifiedBasis_of_factorial_isUnit R n lam hk s hs hheight hfac)).reindex
    (eligibleHarmonicTableauEquiv n s lam hk).symm

theorem originalMasterGriffinBasis_apply (R : Type*) [CommRing R] [Nontrivial R]
    {n s : ℕ} (hfac : IsUnit (n.factorial : R))
    (lam : YoungDiagram) (hk : lam.card ≤ n) (hs : 0 < s)
    (hheight : lam.colLen 0 ≤ s) (z : EligibleHarmonicTableauIndex n s lam hk) :
    originalMasterGriffinBasis R hfac lam hk hs hheight z =
      Ideal.Quotient.mk (griffinIdeal R n lam s) (finiteMasterPolynomial z.1.val z.2) := by
  rw [originalMasterGriffinBasis, Basis.reindex_apply,
    Classical.choose_spec (griffin_specifiedBasis_of_factorial_isUnit R n lam hk s hs hheight hfac)]
  rw [griffinFamily, Equiv.symm_symm, eligibleHarmonicTableauEquiv_polynomial]

theorem adaptedGriffinFamily_span (R : Type*) [CommRing R] [Nontrivial R]
    {n s : ℕ} (hfac : IsUnit (n.factorial : R))
    (lam : YoungDiagram) (hk : lam.card ≤ n) (hs : 0 < s)
    (hheight : lam.colLen 0 ≤ s) :
    Submodule.span R (Set.range (adaptedGriffinFamily (n := n) (s := s) R lam hk)) = ⊤ := by
  apply top_unique
  rw [← (originalMasterGriffinBasis R hfac lam hk hs hheight).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨z, rfl⟩
  rw [originalMasterGriffinBasis_apply, finiteMaster_eq_sum_adapted hfac, map_sum]
  apply Submodule.sum_mem
  intro j hj
  rw [← Ideal.Quotient.mkₐ_eq_mk R (griffinIdeal R n lam s), map_smul]
  apply Submodule.smul_mem
  by_cases he : (fixedFiniteToHarmonic z.1.val.part j.val).toUnboundedHarmonicIndex.eligible lam hk
  · exact Submodule.subset_span
      ⟨⟨⟨fixedFiniteToHarmonic z.1.val.part j.val, he⟩, z.2⟩, rfl⟩
  · simp only [Ideal.Quotient.mkₐ_eq_mk]
    have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr
      (adaptedPolynomial_mem_of_ineligible hfac lam hk hs hheight _ he z.2)
    exact hz.symm ▸ Submodule.zero_mem _

def adaptedGriffinBasis (R : Type*) [CommRing R] [Nontrivial R]
    {n s : ℕ} (hfac : IsUnit (n.factorial : R))
    (lam : YoungDiagram) (hk : lam.card ≤ n) (hs : 0 < s)
    (hheight : lam.colLen 0 ≤ s) :
    Basis (EligibleHarmonicTableauIndex n s lam hk) R (GriffinRing R n lam s) :=
  Classical.choose (specifiedBasis_of_spanning_same_index
    (originalMasterGriffinBasis R hfac lam hk hs hheight)
    (adaptedGriffinFamily R lam hk) (adaptedGriffinFamily_span R hfac lam hk hs hheight))

theorem adaptedGriffinBasis_apply (R : Type*) [CommRing R] [Nontrivial R]
    {n s : ℕ} (hfac : IsUnit (n.factorial : R))
    (lam : YoungDiagram) (hk : lam.card ≤ n) (hs : 0 < s)
    (hheight : lam.colLen 0 ≤ s) (z : EligibleHarmonicTableauIndex n s lam hk) :
    adaptedGriffinBasis R hfac lam hk hs hheight z = adaptedGriffinFamily R lam hk z :=
  Classical.choose_spec (specifiedBasis_of_spanning_same_index
    (originalMasterGriffinBasis R hfac lam hk hs hheight)
    (adaptedGriffinFamily R lam hk) (adaptedGriffinFamily_span R hfac lam hk hs hheight)) z

/-- Full simultaneous basis and exact zero/nonzero test, with the same
polynomial construction for every allowed partition. -/
theorem corollary_5_7_of_factorial_isUnit (R : Type*) [CommRing R] [Nontrivial R]
    {n s : ℕ} (hfac : IsUnit (n.factorial : R))
    (lam : YoungDiagram) (hk : lam.card ≤ n) (hs : 0 < s)
    (hheight : lam.colLen 0 ≤ s) :
    IsSpecifiedBasis (R := R) (adaptedGriffinFamily (n := n) (s := s) R lam hk) ∧
      ∀ (i : FiniteHarmonicIndex n s)
        (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)),
        adaptedMasterPolynomial R i T ∈ griffinIdeal R n lam s ↔
          ¬ i.toUnboundedHarmonicIndex.eligible lam hk := by
  refine ⟨⟨adaptedGriffinBasis R hfac lam hk hs hheight,
    adaptedGriffinBasis_apply R hfac lam hk hs hheight⟩, ?_⟩
  intro i T
  constructor
  · intro hm he
    have hn := (adaptedGriffinBasis R hfac lam hk hs hheight).ne_zero ⟨⟨i, he⟩, T⟩
    apply hn
    rw [adaptedGriffinBasis_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hm
  · intro hi
    exact adaptedPolynomial_mem_of_ineligible hfac lam hk hs hheight i hi T

theorem corollary_5_7_localized {n s : ℕ}
    (lam : YoungDiagram) (hk : lam.card ≤ n) (hs : 0 < s)
    (hheight : lam.colLen 0 ≤ s) :
    IsSpecifiedBasis (R := FactorialLocalization n)
      (adaptedGriffinFamily (n := n) (s := s) (FactorialLocalization n) lam hk) ∧
      ∀ (i : FiniteHarmonicIndex n s)
        (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)),
        adaptedMasterPolynomial (FactorialLocalization n) i T ∈
            griffinIdeal (FactorialLocalization n) n lam s ↔
          ¬ i.toUnboundedHarmonicIndex.eligible lam hk :=
  corollary_5_7_of_factorial_isUnit (FactorialLocalization n)
    (factorial_isUnit_localization n) lam hk hs hheight

theorem corollary_5_7_field (K : Type*) [Field K] {n s : ℕ}
    (hchar : ringChar K = 0 ∨ n < ringChar K)
    (lam : YoungDiagram) (hk : lam.card ≤ n) (hs : 0 < s)
    (hheight : lam.colLen 0 ≤ s) :
    IsSpecifiedBasis (R := K) (adaptedGriffinFamily (n := n) (s := s) K lam hk) ∧
      ∀ (i : FiniteHarmonicIndex n s)
        (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)),
        adaptedMasterPolynomial K i T ∈ griffinIdeal K n lam s ↔
          ¬ i.toUnboundedHarmonicIndex.eligible lam hk :=
  corollary_5_7_of_factorial_isUnit K
    (isUnit_iff_ne_zero.mpr ((factorial_ne_zero_iff_characteristic_range K n).mpr hchar))
    lam hk hs hheight

end HigherSpecht
end
end CanonicalSource22

section CanonicalSource23
/- Source: HigherSpecht/AdaptedSpechtCopies.lean -/



/-!
# The actual Specht action on the modified copies

The same scalar matrix is used for every standard right tableau, so it is
an actual linear combination of intertwiners.  The complete modified basis
proves that each eligible map is injective.  Its range is therefore the
ordinary standard-polytabloid module over the coefficient ring, including
the Specht lattice over Z[1/n!].
-/

noncomputable section
open TauCeti TauCeti.YoungTableau Module MvPolynomial
open scoped Classical

namespace HigherSpecht

theorem linearMap_injective_of_basis_family
    {R V W ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (B : Basis ι R V) (f : V →ₗ[R] W)
    (h : LinearIndependent R (fun i => f (B i))) : Function.Injective f := by
  intro x y hxy
  apply B.repr.injective
  apply h.finsuppLinearCombination_injective
  change Finsupp.linearCombination R (f ∘ B) (B.repr x) =
    Finsupp.linearCombination R (f ∘ B) (B.repr y)
  rw [Finsupp.linearCombination_linear_comp, LinearMap.comp_apply,
    LinearMap.comp_apply, B.linearCombination_repr, B.linearCombination_repr]
  exact hxy

def adaptedMasterIntertwiner {R : Type*} [CommRing R] {n s : ℕ}
    (i : FiniteHarmonicIndex n s) :
    Representation.IntertwiningMap (partitionSpechtRepresentationOver R i.part)
      (polynomialRepresentation R n) :=
  ∑ j : FixedFiniteDegreeIndex (YoungDiagram.ofPartition i.part) s
      i.toUnboundedHarmonicIndex.degree,
    (commonPairingMatrix R (YoungDiagram.ofPartition i.part) s
        i.toUnboundedHarmonicIndex.degree)⁻¹ j (finiteHarmonicToDegree i) •
      finiteMasterIntertwiner (fixedFiniteToHarmonic i.part j.val)

theorem adaptedMasterIntertwiner_standard {R : Type*} [CommRing R] {n s : ℕ}
    (i : FiniteHarmonicIndex n s)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) :
    adaptedMasterIntertwiner (R := R) i (standardPolytabloidOver T) =
      adaptedMasterPolynomial R i T := by
  simp only [adaptedMasterIntertwiner, Representation.IntertwiningMap.sum_apply,
    adaptedMasterPolynomial, adaptedFixedPolynomial, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro j hj
  let c : R := (commonPairingMatrix R (YoungDiagram.ofPartition i.part) s
    i.toUnboundedHarmonicIndex.degree)⁻¹ j (finiteHarmonicToDegree i)
  let f : Representation.IntertwiningMap (partitionSpechtRepresentationOver R i.part)
      (polynomialRepresentation R n) :=
    finiteMasterIntertwiner (fixedFiniteToHarmonic i.part j.val)
  have hsmul : (c • f) (standardPolytabloidOver T) = c • f (standardPolytabloidOver T) :=
    Representation.IntertwiningMap.smul_apply
      (ρ := partitionSpechtRepresentationOver R i.part) (σ := polynomialRepresentation R n)
      c f (standardPolytabloidOver T)
  have hf : f (standardPolytabloidOver T) =
      rename (finCongr (YoungDiagram.card_ofPartition i.part)) (fixedGriffinPolynomial T j.val) :=
    (finiteMasterIntertwiner_standard (R := R) (fixedFiniteToHarmonic i.part j.val) T).trans
      (finiteMasterPolynomial_toFixed (R := R) i.part j.val T)
  exact hsmul.trans (congrArg (fun p : PolynomialRing n R => c • p) hf)

def adaptedGriffinIntertwiner {R : Type*} [CommRing R] {n s : ℕ}
    (lam : YoungDiagram) (i : FiniteHarmonicIndex n s) :
    Representation.IntertwiningMap (partitionSpechtRepresentationOver R i.part)
      (griffinRepresentation R n lam s) :=
  (quotientProjectionIntertwiner (griffinIdeal R n lam s)
    (permutationStable_griffinIdeal lam s)).comp (adaptedMasterIntertwiner i)

@[simp] theorem adaptedGriffinIntertwiner_standard {R : Type*} [CommRing R]
    {n s : ℕ} (lam : YoungDiagram) (hk : lam.card ≤ n)
    (i : EligibleFiniteHarmonicIndex n s lam hk)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.val.part)) :
    adaptedGriffinIntertwiner (R := R) lam i.val (standardPolytabloidOver T) =
      adaptedGriffinFamily R lam hk ⟨i, T⟩ := by
  change Ideal.Quotient.mk (griffinIdeal R n lam s)
      (adaptedMasterIntertwiner (R := R) i.val (standardPolytabloidOver T)) =
    Ideal.Quotient.mk (griffinIdeal R n lam s) (adaptedMasterPolynomial R i.val T)
  rw [adaptedMasterIntertwiner_standard]

def adaptedGriffinCopy {R : Type*} [CommRing R] {n s : ℕ}
    (lam : YoungDiagram) (i : FiniteHarmonicIndex n s) :
    Subrepresentation (griffinRepresentation R n lam s) :=
  (adaptedGriffinIntertwiner lam i).range

theorem adaptedGriffinCopy_eq_span {R : Type*} [CommRing R] {n s : ℕ}
    (lam : YoungDiagram) (i : FiniteHarmonicIndex n s) :
    (adaptedGriffinCopy (R := R) lam i).toSubmodule =
      Submodule.span R (Set.range (fun T : StandardYoungTableau (YoungDiagram.ofPartition i.part) =>
        Ideal.Quotient.mk (griffinIdeal R n lam s) (adaptedMasterPolynomial R i T))) := by
  change LinearMap.range (adaptedGriffinIntertwiner (R := R) lam i).toLinearMap = _
  rw [linearMap_range_eq_span_standard]
  simp only [Representation.IntertwiningMap.coe_toLinearMap, adaptedGriffinIntertwiner, Representation.IntertwiningMap.comp_apply,
    adaptedMasterIntertwiner_standard, quotientProjectionIntertwiner,
    Representation.IntertwiningMap.coe_mk, AlgHom.coe_toLinearMap,
    Ideal.Quotient.mkₐ_eq_mk]

theorem adaptedGriffinIntertwiner_injective
    {R : Type*} [CommRing R] [Nontrivial R] {n s : ℕ}
    (hfac : IsUnit (n.factorial : R))
    (lam : YoungDiagram) (hk : lam.card ≤ n) (hs : 0 < s)
    (hheight : lam.colLen 0 ≤ s) (i : EligibleFiniteHarmonicIndex n s lam hk) :
    Function.Injective (adaptedGriffinIntertwiner (R := R) lam i.val) := by
  apply linearMap_injective_of_basis_family (standardPolytabloidBasisOver R _)
  have h := (adaptedGriffinBasis R hfac lam hk hs hheight).linearIndependent.comp
    (fun T : StandardYoungTableau (YoungDiagram.ofPartition i.val.part) =>
      (⟨i, T⟩ : EligibleHarmonicTableauIndex n s lam hk))
    (fun T U h => eq_of_heq (Sigma.mk.inj_iff.mp h).2)
  have hfam :
      (fun T : StandardYoungTableau (YoungDiagram.ofPartition i.val.part) =>
        adaptedGriffinBasis R hfac lam hk hs hheight ⟨i, T⟩) =
      (fun T => (adaptedGriffinIntertwiner (R := R) lam i.val).toLinearMap
        (standardPolytabloidBasisOver R _ T)) := by
    funext T
    rw [adaptedGriffinBasis_apply, standardPolytabloidBasisOver_apply]
    exact (adaptedGriffinIntertwiner_standard (R := R) lam hk i T).symm
  exact Eq.mp (congrArg
    (fun v : StandardYoungTableau (YoungDiagram.ofPartition i.val.part) → GriffinRing R n lam s =>
      (LinearIndependent R v : Prop)) hfam) h

def adaptedGriffinSpechtEquiv {R : Type*} [CommRing R] [Nontrivial R] {n s : ℕ}
    (hfac : IsUnit (n.factorial : R))
    (lam : YoungDiagram) (hk : lam.card ≤ n) (hs : 0 < s)
    (hheight : lam.colLen 0 ≤ s) (i : EligibleFiniteHarmonicIndex n s lam hk) :
    Representation.Equiv (partitionSpechtRepresentationOver R i.val.part)
      (adaptedGriffinCopy (R := R) lam i.val).toRepresentation :=
  (adaptedGriffinIntertwiner lam i.val).equivOfRange
    (adaptedGriffinIntertwiner_injective hfac lam hk hs hheight i) rfl

theorem corollary_5_7_localized_copy {n s : ℕ}
    (lam : YoungDiagram) (hk : lam.card ≤ n) (hs : 0 < s)
    (hheight : lam.colLen 0 ≤ s) (i : EligibleFiniteHarmonicIndex n s lam hk) :
    Nonempty (Representation.Equiv (partitionSpechtRepresentationOver (FactorialLocalization n) i.val.part)
      (adaptedGriffinCopy (R := FactorialLocalization n) lam i.val).toRepresentation) :=
  ⟨adaptedGriffinSpechtEquiv (factorial_isUnit_localization n) lam hk hs hheight i⟩

theorem corollary_5_7_field_copy (K : Type*) [Field K] {n s : ℕ}
    (hchar : ringChar K = 0 ∨ n < ringChar K)
    (lam : YoungDiagram) (hk : lam.card ≤ n) (hs : 0 < s)
    (hheight : lam.colLen 0 ≤ s) (i : EligibleFiniteHarmonicIndex n s lam hk) :
    (adaptedGriffinCopy (R := K) lam i.val).toRepresentation.IsIrreducible ∧
      Nonempty (Representation.Equiv (partitionSpechtRepresentationOver K i.val.part)
        (adaptedGriffinCopy (R := K) lam i.val).toRepresentation) := by
  have hfac := (factorial_ne_zero_iff_characteristic_range K n).mpr hchar
  letI := partitionSpechtRepresentationOver_isIrreducible hfac i.val.part
  let e := adaptedGriffinSpechtEquiv (isUnit_iff_ne_zero.mpr hfac) lam hk hs hheight i
  exact ⟨irreducible_of_representation_equiv e, ⟨e⟩⟩

end HigherSpecht
end
end CanonicalSource23

section CanonicalSource24
/- Source: HigherSpecht/BlockPolynomialQuotient.lean -/



/-!
# The actual quotient of an embedded Springer component

An explicit coordinate permutation first places the outside variables before
an enumeration of the Springer block.  The sum-variable polynomial
equivalence then identifies the extended ideal with the coefficient ideal.
The standard quotient equivalence produces the polynomial algebra over the
genuine Springer quotient.  This is the literal tensor/polynomial structure
used by the primary-component calculation.
-/

noncomputable section

open Finset MvPolynomial TauCeti

namespace HigherSpecht

variable {R : Type*} [CommRing R] {n : ℕ} {mu : YoungDiagram}

abbrev OutsideCoordinates (A : Finset (Fin n)) := {i : Fin n // i ∉ A}

def blockEnumeration (A : Finset (Fin n)) (hA : A.card = mu.card) :
    Fin mu.card ↪ Fin n where
  toFun i := ((Finset.equivFinOfCardEq hA).symm i).val
  inj' i j h := (Finset.equivFinOfCardEq hA).symm.injective (Subtype.ext h)

theorem blockEnumeration_range (A : Finset (Fin n)) (hA : A.card = mu.card) :
    (Finset.univ : Finset (Fin mu.card)).map (blockEnumeration A hA) = A := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    exact ((Finset.equivFinOfCardEq hA).symm j).property
  · intro hi
    refine Finset.mem_map.mpr ⟨Finset.equivFinOfCardEq hA ⟨i, hi⟩,
      Finset.mem_univ _, ?_⟩
    change (((Finset.equivFinOfCardEq hA).symm
      ((Finset.equivFinOfCardEq hA) ⟨i, hi⟩)) : ↥A).val = i
    exact congrArg Subtype.val ((Finset.equivFinOfCardEq hA).symm_apply_apply ⟨i, hi⟩)

def blockSplitEquiv (A : Finset (Fin n)) (hA : A.card = mu.card) :
    Fin n ≃ (OutsideCoordinates A ⊕ Fin mu.card) :=
  ((Equiv.sumCompl fun i : Fin n => i ∈ A).symm.trans
    (Equiv.sumComm ↥A (OutsideCoordinates A))).trans
      (Equiv.sumCongr (Equiv.refl _) (Finset.equivFinOfCardEq hA))

@[simp] theorem blockSplitEquiv_enumeration (A : Finset (Fin n))
    (hA : A.card = mu.card) (i : Fin mu.card) :
    blockSplitEquiv A hA (blockEnumeration A hA i) = Sum.inr i := by
  change Sum.map (fun x : OutsideCoordinates A => x) (Finset.equivFinOfCardEq hA)
    ((Equiv.sumCompl fun i : Fin n => i ∈ A).symm
      (((Finset.equivFinOfCardEq hA).symm i).val)).swap = Sum.inr i
  rw [Equiv.sumCompl_symm_apply_pos, Sum.swap_inl, Sum.map_inr, Equiv.apply_symm_apply]

@[simp] theorem blockSplitEquiv_outside (A : Finset (Fin n))
    (hA : A.card = mu.card) (i : OutsideCoordinates A) :
    blockSplitEquiv A hA i.val = Sum.inl i := by
  change Sum.map (fun x : OutsideCoordinates A => x) (Finset.equivFinOfCardEq hA)
    ((Equiv.sumCompl fun j : Fin n => j ∈ A).symm i.val).swap = Sum.inl i
  rw [Equiv.sumCompl_symm_apply_neg, Sum.swap_inr, Sum.map_inl]

def blockPolynomialSplit (A : Finset (Fin n)) (hA : A.card = mu.card) :
    PolynomialRing n R ≃ₐ[R] MvPolynomial (OutsideCoordinates A) (PolynomialRing mu.card R) :=
  (MvPolynomial.renameEquiv R (blockSplitEquiv A hA)).trans
    (MvPolynomial.sumAlgEquiv R (OutsideCoordinates A) (Fin mu.card))

@[simp] theorem blockPolynomialSplit_X_inside (A : Finset (Fin n))
    (hA : A.card = mu.card) (i : Fin mu.card) :
    blockPolynomialSplit (R := R) A hA (MvPolynomial.X (blockEnumeration A hA i)) =
      MvPolynomial.C (MvPolynomial.X i) := by
  simp only [blockPolynomialSplit, AlgEquiv.trans_apply,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
    blockSplitEquiv_enumeration, MvPolynomial.sumAlgEquiv_X_inr]

@[simp] theorem blockPolynomialSplit_X_outside (A : Finset (Fin n))
    (hA : A.card = mu.card) (i : OutsideCoordinates A) :
    blockPolynomialSplit (R := R) A hA (MvPolynomial.X i.val) = MvPolynomial.X i := by
  simp only [blockPolynomialSplit, AlgEquiv.trans_apply,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
    blockSplitEquiv_outside, MvPolynomial.sumAlgEquiv_X_inl]

theorem blockPolynomialSplit_comp_rename (A : Finset (Fin n))
    (hA : A.card = mu.card) :
    (blockPolynomialSplit (R := R) A hA).toRingHom.comp
      (MvPolynomial.rename (blockEnumeration A hA)).toRingHom =
      (MvPolynomial.C : PolynomialRing mu.card R →+*
        MvPolynomial (OutsideCoordinates A) (PolynomialRing mu.card R)) := by
  have h : (blockPolynomialSplit (R := R) A hA).toAlgHom.comp
      (MvPolynomial.rename (blockEnumeration A hA)) =
      IsScalarTower.toAlgHom R (PolynomialRing mu.card R)
        (MvPolynomial (OutsideCoordinates A) (PolynomialRing mu.card R)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_algHom, MvPolynomial.rename_X,
      IsScalarTower.toAlgHom_apply, MvPolynomial.algebraMap_eq] using
      (blockPolynomialSplit_X_inside (R := R) A hA i)
  exact congrArg AlgHom.toRingHom h

theorem map_blockSpringerIdeal_polynomialSplit (A : Finset (Fin n))
    (hA : A.card = mu.card) :
    (blockSpringerIdeal R A mu).map (blockPolynomialSplit A hA).toRingHom =
      (springerIdeal R mu).map (MvPolynomial.C : PolynomialRing mu.card R →+*
        MvPolynomial (OutsideCoordinates A) (PolynomialRing mu.card R)) := by
  have hblock := blockSpringerIdeal_eq_map (R := R) mu (blockEnumeration A hA)
  rw [blockEnumeration_range A hA] at hblock
  rw [hblock]
  change ((springerIdeal R mu).map
    (MvPolynomial.rename (blockEnumeration A hA)).toRingHom).map
      (blockPolynomialSplit (R := R) A hA).toRingHom = _
  rw [Ideal.map_map, blockPolynomialSplit_comp_rename]

/-- The component quotient is the polynomial ring on the actual outside
coordinates with coefficients in the original Springer quotient. -/
def blockSpringerQuotientEquiv (A : Finset (Fin n)) (hA : A.card = mu.card) :
    (PolynomialRing n R ⧸ blockSpringerIdeal R A mu) ≃ₐ[R]
      MvPolynomial (OutsideCoordinates A) (SpringerRing R mu) :=
  (Ideal.quotientEquivAlg _ _ (blockPolynomialSplit A hA)
    (map_blockSpringerIdeal_polynomialSplit A hA).symm).trans
      ((MvPolynomial.quotientEquivQuotientMvPolynomial (σ := OutsideCoordinates A)
        (springerIdeal R mu)).symm.restrictScalars R)

end HigherSpecht
end
end CanonicalSource24

section CanonicalSource25
/- Source: HigherSpecht/PolynomialPrimaryExtension.lean -/



/-!
# Primary zero ideals under finite polynomial extension

McCoy's theorem reduces a polynomial zero divisor to a nonzero scalar
annihilating every coefficient. Primaryness in the coefficient ring then
makes those coefficients nilpotent, hence makes the polynomial nilpotent.
Finite multivariable extension follows through the actual empty-variable,
renaming, and one-extra-variable ring equivalences.
-/

namespace HigherSpecht

open scoped Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

theorem nontrivial_of_bot_primary (h : (⊥ : Ideal R).IsPrimary) : Nontrivial R := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro hzero
  apply (Ideal.isPrimary_iff.mp h).1
  apply (Ideal.eq_top_iff_one _).mpr
  exact (Ideal.mem_bot).mpr hzero.symm

/-- An injective ring homomorphism reflects primaryness of the zero ideal. -/
theorem bot_primary_of_injective_hom (f : R →+* S) (hf : Function.Injective f)
    (h : (⊥ : Ideal S).IsPrimary) : (⊥ : Ideal R).IsPrimary := by
  have hcomap := h.comap f
  have heq : Ideal.comap f (⊥ : Ideal S) = (⊥ : Ideal R) := by
    ext x
    change f x = 0 ↔ x = 0
    constructor
    · intro hx
      apply hf
      exact hx.trans (map_zero f).symm
    · rintro rfl
      exact map_zero f
  rwa [heq] at hcomap

/-- No noetherianity or coefficient-field hypothesis is needed. -/
theorem polynomial_bot_primary (hR : (⊥ : Ideal R).IsPrimary) :
    (⊥ : Ideal R[X]).IsPrimary := by
  letI : Nontrivial R := nontrivial_of_bot_primary hR
  apply Ideal.isPrimary_iff.mpr
  refine ⟨bot_ne_top, ?_⟩
  intro f g hfg
  change f * g = 0 at hfg
  by_cases hf : f = 0
  · exact Or.inl ((Ideal.mem_bot).mpr hf)
  · apply Or.inr
    have hg : g ∉ nonZeroDivisors (R[X]) := by
      intro hregular
      exact hf (hregular.2 f hfg)
    obtain ⟨a, ha, hag⟩ := Polynomial.notMem_nonZeroDivisors_iff.mp hg
    have hcoeff : ∀ k, IsNilpotent (g.coeff k) := by
      intro k
      have hmul : a * g.coeff k = 0 := by
        have hc := congrArg (fun p : R[X] => p.coeff k) hag
        simpa only [Polynomial.coeff_smul, Polynomial.coeff_zero, smul_eq_mul] using hc
      have hprimary := (Ideal.isPrimary_iff.mp hR).2
        (x := a) (y := g.coeff k) ((Ideal.mem_bot).mpr hmul)
      have hrad : g.coeff k ∈ (⊥ : Ideal R).radical :=
        hprimary.resolve_left (by simpa only [Ideal.mem_bot] using ha)
      obtain ⟨e, he⟩ := Ideal.mem_radical_iff.mp hrad
      exact ⟨e, (Ideal.mem_bot).mp he⟩
    obtain ⟨e, he⟩ := Polynomial.isNilpotent_iff.mpr hcoeff
    exact Ideal.mem_radical_iff.mpr ⟨e, (Ideal.mem_bot).mpr he⟩

/-- Polynomial extension by every finite variable type preserves the
primary zero ideal. The equivalences retain the actual polynomial rings. -/
theorem mvPolynomial_bot_primary (hR : (⊥ : Ideal R).IsPrimary)
    (σ : Type*) [Finite σ] : (⊥ : Ideal (MvPolynomial σ R)).IsPrimary := by
  apply Finite.induction_empty_option
    (P := fun τ => (⊥ : Ideal (MvPolynomial τ R)).IsPrimary) ?_ ?_ ?_ σ
  · intro α β e hα
    let E := MvPolynomial.renameEquiv R e
    exact bot_primary_of_injective_hom E.symm.toRingEquiv.toRingHom E.symm.injective hα
  · exact bot_primary_of_injective_hom
      (MvPolynomial.isEmptyRingEquiv R PEmpty).toRingHom
      (MvPolynomial.isEmptyRingEquiv R PEmpty).injective hR
  · intro α inst hα
    let E := MvPolynomial.optionEquivLeft R α
    exact bot_primary_of_injective_hom E.toRingEquiv.toRingHom E.injective
      (polynomial_bot_primary hα)

end HigherSpecht
end CanonicalSource25

section CanonicalSource26
/- Source: HigherSpecht/PrimaryComponents.lean -/



/-!
# The primary components of the untruncated Springer ideal

The component quotient is the genuine polynomial algebra over the Springer
quotient.  Its zero ideal is primary by the scalar regularity argument and
McCoy's theorem.  Distinct coordinate blocks have incomparable radicals;
an explicit product of powers of outside coordinates witnesses that none
of the components can be removed from the intersection.
-/

noncomputable section

open Finset MvPolynomial TauCeti

namespace HigherSpecht

variable {R : Type*} [CommRing R] {n : ℕ} {mu : YoungDiagram}

/-- Every actual extended Springer ideal is primary over every coefficient
domain, including the integers. -/
theorem blockSpringerIdeal_isPrimary [IsDomain R]
    (A : Finset (Fin n)) (hA : A.card = mu.card) :
    (blockSpringerIdeal R A mu).IsPrimary := by
  let E := blockSpringerQuotientEquiv (R := R) A hA
  have hpoly : (⊥ : Ideal
      (MvPolynomial (OutsideCoordinates A) (SpringerRing R mu))).IsPrimary :=
    mvPolynomial_bot_primary (springerRing_bot_isPrimary (R := R) mu) _
  have hquot : (⊥ : Ideal
      (PolynomialRing n R ⧸ blockSpringerIdeal R A mu)).IsPrimary :=
    bot_primary_of_injective_hom
      (R := PolynomialRing n R ⧸ blockSpringerIdeal R A mu)
      (S := MvPolynomial (OutsideCoordinates A) (SpringerRing R mu))
      E.toRingHom E.injective hpoly
  have hcomap := hquot.comap (Ideal.Quotient.mk (blockSpringerIdeal R A mu))
  have heq : Ideal.comap (Ideal.Quotient.mk (blockSpringerIdeal R A mu))
      (⊥ : Ideal (PolynomialRing n R ⧸ blockSpringerIdeal R A mu)) =
      blockSpringerIdeal R A mu := by
    ext p
    change Ideal.Quotient.mk (blockSpringerIdeal R A mu) p = 0 ↔
      p ∈ blockSpringerIdeal R A mu
    exact Ideal.Quotient.eq_zero_iff_mem
  rwa [heq] at hcomap

theorem X_mem_coordinateIdeal_iff [Nontrivial R]
    (A : Finset (Fin n)) (i : Fin n) :
    (MvPolynomial.X i : PolynomialRing n R) ∈ coordinateIdeal R A ↔ i ∈ A := by
  classical
  constructor
  · intro hi
    by_contra hnot
    let v : Fin n → R := fun j => if j = i then 1 else 0
    let f : PolynomialRing n R →+* R := MvPolynomial.eval₂Hom (RingHom.id R) v
    have hker : coordinateIdeal R A ≤ RingHom.ker f := by
      apply Ideal.span_le.mpr
      rintro p ⟨j, hj, rfl⟩
      have hji : j ≠ i := by rintro rfl; exact hnot hj
      change f (MvPolynomial.X j) = 0
      simp [f, v, hji]
    have hzero := hker hi
    change f (MvPolynomial.X i) = 0 at hzero
    simpa [f, v] using hzero
  · intro hi
    exact Ideal.subset_span ⟨i, hi, rfl⟩

theorem coordinateIdeal_le_iff [Nontrivial R]
    (A B : Finset (Fin n)) : coordinateIdeal R A ≤ coordinateIdeal R B ↔ A ⊆ B := by
  constructor
  · intro h i hi
    exact (X_mem_coordinateIdeal_iff (R := R) B i).mp
      (h ((X_mem_coordinateIdeal_iff (R := R) A i).mpr hi))
  · intro h
    exact Ideal.span_mono (Set.image_mono h)

theorem coordinateIdeal_incomparable [Nontrivial R]
    (A B : SpringerCoordinateBlocks n mu) (hAB : A ≠ B) :
    ¬ coordinateIdeal R A.val ≤ coordinateIdeal R B.val := by
  intro h
  have hsub := (coordinateIdeal_le_iff (R := R) A.val B.val).mp h
  apply hAB
  apply Subtype.ext
  exact Finset.eq_of_subset_of_card_le hsub (by rw [A.property, B.property])

theorem exists_coordinate_outside_of_block_ne
    (A B : SpringerCoordinateBlocks n mu) (hBA : B ≠ A) :
    ∃ i : Fin n, i ∈ B.val ∧ i ∉ A.val := by
  classical
  by_contra h
  have hsub : B.val ⊆ A.val := by
    intro i hi
    by_contra hnot
    exact h ⟨i, hi, hnot⟩
  apply hBA
  apply Subtype.ext
  exact Finset.eq_of_subset_of_card_le hsub (by rw [A.property, B.property])

/-- A literal polynomial witnesses irredundance.  This also covers the
single-component and empty-partition cases, where the empty product is one. -/
theorem springerComponentIntersection_irredundant [Nontrivial R]
    (A : SpringerCoordinateBlocks n mu) :
    ∃ p : PolynomialRing n R,
      (∀ B : SpringerCoordinateBlocks n mu, B ≠ A →
        p ∈ blockSpringerIdeal R B.val mu) ∧
      p ∉ blockSpringerIdeal R A.val mu := by
  classical
  let Other := {B : SpringerCoordinateBlocks n mu // B ≠ A}
  let j : Other → Fin n := fun B =>
    Classical.choose (exists_coordinate_outside_of_block_ne A B.val B.property)
  have hj (B : Other) : j B ∈ B.val.val ∧ j B ∉ A.val :=
    Classical.choose_spec (exists_coordinate_outside_of_block_ne A B.val B.property)
  let p : PolynomialRing n R := ∏ B : Other, MvPolynomial.X (j B) ^ mu.card
  refine ⟨p, ?_, ?_⟩
  · intro B hB
    apply (blockSpringerIdeal R B.val mu).prod_mem
      (Finset.mem_univ (⟨B, hB⟩ : Other))
    have hpow := X_pow_card_mem_blockSpringerIdeal (R := R)
      B.val mu B.property (hj (⟨B, hB⟩ : Other)).1
    simpa only [B.property] using hpow
  · intro hp
    let v : Fin n → R := fun i => if i ∈ A.val then 0 else 1
    let f : PolynomialRing n R →+* R := MvPolynomial.eval₂Hom (RingHom.id R) v
    have hker : coordinateIdeal R A.val ≤ RingHom.ker f := by
      apply Ideal.span_le.mpr
      rintro q ⟨i, hi, rfl⟩
      change i ∈ A.val at hi
      change f (MvPolynomial.X i) = 0
      simp [f, v, hi]
    have hz := hker ((blockSpringerIdeal_le_coordinateIdeal
      A.val mu A.property) hp)
    change f p = 0 at hz
    have hone : f p = 1 := by
      simp only [p, map_prod, map_pow]
      apply Finset.prod_eq_one
      intro B hB
      simp [f, v, (hj B).2]
    rw [hone] at hz
    exact one_ne_zero hz

/-- The ideal identity and complete primary-component assertions of
Proposition 7.3.  The separate numerical multiplicity formula is not part
of this declaration. -/
theorem proposition_7_3_primary_decomposition [IsDomain R]
    (hn : mu.card ≤ n) :
    untruncatedIdeal R n mu = springerComponentIntersection R n mu ∧
      (∀ A : SpringerCoordinateBlocks n mu,
        (blockSpringerIdeal R A.val mu).IsPrimary ∧
        (blockSpringerIdeal R A.val mu).radical = coordinateIdeal R A.val) ∧
      (∀ A : SpringerCoordinateBlocks n mu,
        ∃ p : PolynomialRing n R,
          (∀ B : SpringerCoordinateBlocks n mu, B ≠ A →
            p ∈ blockSpringerIdeal R B.val mu) ∧
          p ∉ blockSpringerIdeal R A.val mu) := by
  refine ⟨untruncatedIdeal_eq_componentIntersection hn, ?_, ?_⟩
  · intro A
    exact ⟨blockSpringerIdeal_isPrimary A.val A.property,
      blockSpringerIdeal_radical A.val mu A.property⟩
  · exact springerComponentIntersection_irredundant

end HigherSpecht
end
end CanonicalSource26

section CanonicalSource27
/- Source: HigherSpecht/NilpotentAugmentationLength.lean -/



/-!
# Length of an augmented algebra with nilpotent augmentation kernel

The augmentation identifies the residue field with the original coefficient
field.  The local scalar-restriction length theorem then identifies the
composition length of the algebra with its actual vector-space dimension.
This is the length calculation needed at a generic Springer component.
-/

noncomputable section

open Module IsLocalRing TauCeti

namespace HigherSpecht

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

theorem isUnit_iff_augmentation_ne_zero
    (eps : A →ₐ[K] K) (hnil : ∀ a : A, eps a = 0 → IsNilpotent a) (a : A) :
    IsUnit a ↔ eps a ≠ 0 := by
  constructor
  · intro ha
    exact isUnit_iff_ne_zero.mp (ha.map eps.toRingHom)
  · intro ha
    have hn : IsNilpotent (a - algebraMap K A (eps a)) :=
      hnil _ (by simp only [map_sub, eps.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self])
    have hu : IsUnit (algebraMap K A (eps a)) :=
      (isUnit_iff_ne_zero.mpr ha).map (algebraMap K A)
    convert hn.isUnit_add_left_of_commute hu (Commute.all _ _) using 1 <;> ring

theorem isLocalRing_of_nilpotent_augmentation
    (eps : A →ₐ[K] K) (hnil : ∀ a : A, eps a = 0 → IsNilpotent a) : IsLocalRing A := by
  letI : Nontrivial A := ⟨⟨0, 1, by
    intro h
    have h' := congrArg eps h
    exact zero_ne_one (by simpa only [map_zero, map_one] using h')⟩⟩
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  by_cases ha : eps a = 0
  · right
    apply (isUnit_iff_augmentation_ne_zero eps hnil (1 - a)).mpr
    simpa only [map_sub, map_one, ha, sub_zero] using (one_ne_zero : (1 : K) ≠ 0)
  · exact Or.inl ((isUnit_iff_augmentation_ne_zero eps hnil a).mpr ha)

theorem residue_algebraMap_surjective_of_nilpotent_augmentation
    [IsLocalRing A] (eps : A →ₐ[K] K)
    (hnil : ∀ a : A, eps a = 0 → IsNilpotent a) :
    Function.Surjective (algebraMap K (ResidueField A)) := by
  intro z
  obtain ⟨a, rfl⟩ := residue_surjective z
  refine ⟨eps a, ?_⟩
  rw [IsScalarTower.algebraMap_apply K A (ResidueField A), ResidueField.algebraMap_eq]
  apply sub_eq_zero.mp
  rw [← map_sub, residue_eq_zero_iff]
  change ¬ IsUnit (algebraMap K A (eps a) - a)
  apply (hnil _ ?_).not_isUnit
  simp only [map_sub, eps.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]

theorem length_self_eq_finrank_of_nilpotent_augmentation
    [Module.Finite K A] (eps : A →ₐ[K] K)
    (hnil : ∀ a : A, eps a = 0 → IsNilpotent a) :
    Module.length A A = (Module.finrank K A : ℕ∞) := by
  letI := isLocalRing_of_nilpotent_augmentation eps hnil
  have hres : Module.length (ResidueField K) (ResidueField A) = 1 := by
    rw [← Module.length_eq_of_surjective (M := ResidueField A)
      (residue_surjective (R := K)),
      Module.length_eq_of_surjective (M := ResidueField A)
        (residue_algebraMap_surjective_of_nilpotent_augmentation eps hnil),
      Module.length_eq_one]
  have h := IsLocalRing.length_restrictScalars K A A
  rw [Module.length_eq_finrank, hres, mul_one] at h
  exact h.symm

theorem springerRing_isLocalRing (K : Type*) [Field K] (lam : YoungDiagram) :
    IsLocalRing (SpringerRing K lam) :=
  isLocalRing_of_nilpotent_augmentation (springerAugmentation lam)
    (fun _ h => springer_isNilpotent_of_augmentation_eq_zero lam h)

theorem springerRing_finiteDimensional (K : Type*) [Field K] (lam : YoungDiagram) :
    FiniteDimensional K (SpringerRing K lam) := by
  letI := finite_fullSizeStaircase lam rfl
  letI : Fintype (UntruncatedStaircaseExponents lam.card lam) := Fintype.ofFinite _
  exact Module.Finite.of_basis (untruncatedStandardMonomialBasis (R := K) (μ := lam) le_rfl)

/-- The actual composition length, over its own local algebra, of the
Springer factor.  This holds in every coefficient characteristic. -/
theorem length_springerRing (K : Type*) [Field K] (lam : YoungDiagram) :
    Module.length (SpringerRing K lam) (SpringerRing K lam) =
      (lam.card.factorial / rowFactorialProduct lam : ℕ) := by
  letI := springerRing_finiteDimensional K lam
  rw [length_self_eq_finrank_of_nilpotent_augmentation
    (springerAugmentation (R := K) lam)
    (fun _ h => springer_isNilpotent_of_augmentation_eq_zero lam h),
    finrank_springer K lam]

end HigherSpecht
end
end CanonicalSource27

section CanonicalSource28
/- Source: HigherSpecht/NilpotentAugmentationLocalization.lean -/



/-!
# Generic length of a finite free algebra with nilpotent augmentation kernel

We construct the generic local algebra as the actual tensor product with the
fraction field.  Its augmentation has nilpotent kernel, so every element
outside that kernel is a unit.  This proves the localization universal
property at the augmentation prime, rather than assuming a local algebra
description.  Its composition length is therefore the original free rank.
-/

noncomputable section

open scoped TensorProduct nonZeroDivisors
open Module TensorProduct

namespace HigherSpecht

theorem length_self_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : Module.length R R = Module.length S S := by
  letI : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
  let f : R →ₛₗ[e.toRingHom] S :=
    { e.toAddHom with map_smul' := fun r x => e.map_mul r x }
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso
      (Submodule.orderIsoMapComapOfBijective f e.bijective)]

theorem isLocalization_of_enlarged_denominators
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M N : Submonoid R} [IsLocalization M S]
    (hMN : M ≤ N) (hunit : ∀ y : N, IsUnit (algebraMap R S y)) :
    IsLocalization N S := by
  refine ⟨⟨hunit, ?_, ?_⟩⟩
  · intro z
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj M z
    exact ⟨(x, ⟨s.val, hMN s.property⟩), hs⟩
  · intro x y hxy
    obtain ⟨s, hs⟩ := IsLocalization.exists_of_eq (M := M) hxy
    exact ⟨⟨s.val, hMN s.property⟩, hs⟩

section FractionAugmentation

variable {C A : Type*} [CommRing C] [IsDomain C] [CommRing A] [Algebra C A]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The literal augmentation kernel is prime because its codomain is a domain. -/
instance augmentation_ker_isPrime (eps : A →ₐ[C] C) :
    (RingHom.ker eps).IsPrime := RingHom.ker_isPrime eps

/-- The base change of the literal augmentation to the fraction field. -/
def fractionAugmentation (eps : A →ₐ[C] C) :
    FractionRing C ⊗[C] A →ₐ[FractionRing C] FractionRing C :=
  AlgHom.liftEquiv C (FractionRing C) A (FractionRing C)
    ((Algebra.ofId C (FractionRing C)).comp eps)

@[simp] theorem fractionAugmentation_tmul
    (eps : A →ₐ[C] C) (s : FractionRing C) (a : A) :
    fractionAugmentation eps (s ⊗ₜ[C] a) =
      s * algebraMap C (FractionRing C) (eps a) := rfl

@[simp] theorem fractionAugmentation_algebraMap
    (eps : A →ₐ[C] C) (a : A) :
    fractionAugmentation eps
      (algebraMap A (FractionRing C ⊗[C] A) a) =
      algebraMap C (FractionRing C) (eps a) := by
  change 1 * algebraMap C (FractionRing C) (eps a) = _
  exact one_mul _

theorem fractionAugmentation_ker_nilpotent
    (eps : A →ₐ[C] C) (hnil : ∀ a : A, eps a = 0 → IsNilpotent a)
    (z : FractionRing C ⊗[C] A) (hz : fractionAugmentation eps z = 0) :
    IsNilpotent z := by
  let M : Submonoid A := Algebra.algebraMapSubmonoid A C⁰
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj M z
  have ha : eps a = 0 := by
    apply IsFractionRing.injective C (FractionRing C)
    have he := congrArg (fractionAugmentation eps) hs
    simpa only [map_mul, hz, zero_mul, fractionAugmentation_algebraMap, map_zero]
      using he.symm
  have hprod : IsNilpotent
      (z * algebraMap A (FractionRing C ⊗[C] A) s.val) := by
    rw [hs]
    exact (hnil a ha).map (algebraMap A (FractionRing C ⊗[C] A))
  exact (IsUnit.isNilpotent_mul_unit_of_commute_iff
    (IsLocalization.map_units (FractionRing C ⊗[C] A) s) (Commute.all _ _)).mp hprod

theorem algebraMap_denominators_le_augmentation_prime
    (eps : A →ₐ[C] C) :
    Algebra.algebraMapSubmonoid A C⁰ ≤ (RingHom.ker eps).primeCompl := by
  intro a ha
  obtain ⟨c, hc, rfl⟩ := ha
  change eps (algebraMap C A c) ≠ 0
  simpa only [eps.commutes, Algebra.algebraMap_self, RingHom.id_apply] using
    (mem_nonZeroDivisors_iff_ne_zero.mp hc)

/-- The fraction-field tensor algebra satisfies the localization property
at the actual augmentation prime. -/
theorem fractionTensor_isLocalization_at_augmentation
    (eps : A →ₐ[C] C) (hnil : ∀ a : A, eps a = 0 → IsNilpotent a) :
    IsLocalization (RingHom.ker eps).primeCompl (FractionRing C ⊗[C] A) := by
  apply isLocalization_of_enlarged_denominators
    (M := Algebra.algebraMapSubmonoid A C⁰)
    (algebraMap_denominators_le_augmentation_prime eps)
  intro a
  apply (isUnit_iff_augmentation_ne_zero (fractionAugmentation eps)
    (fractionAugmentation_ker_nilpotent eps hnil) _).mpr
  rw [fractionAugmentation_algebraMap]
  exact fun h => a.property ((IsFractionRing.injective C (FractionRing C))
    (by simpa only [map_zero] using h))

def augmentationPrimeLocalizationEquiv
    (eps : A →ₐ[C] C) (hnil : ∀ a : A, eps a = 0 → IsNilpotent a) :
    Localization.AtPrime (RingHom.ker eps) ≃ₐ[A]
      FractionRing C ⊗[C] A := by
  letI := fractionTensor_isLocalization_at_augmentation eps hnil
  exact IsLocalization.algEquiv (RingHom.ker eps).primeCompl
    (Localization.AtPrime (RingHom.ker eps)) (FractionRing C ⊗[C] A)

/-- Actual generic composition length of the augmented algebra.  There
is no length, dimension, localization, or freeness conclusion hidden in
the nilpotence hypothesis. -/
theorem length_augmentationPrimeLocalization
    [Module.Free C A] [Module.Finite C A]
    (eps : A →ₐ[C] C) (hnil : ∀ a : A, eps a = 0 → IsNilpotent a) :
    Module.length (Localization.AtPrime (RingHom.ker eps))
        (Localization.AtPrime (RingHom.ker eps)) =
      (Module.finrank C A : ℕ∞) := by
  rw [length_self_eq_of_ringEquiv
    (augmentationPrimeLocalizationEquiv eps hnil).toRingEquiv,
    length_self_eq_finrank_of_nilpotent_augmentation
      (fractionAugmentation eps) (fractionAugmentation_ker_nilpotent eps hnil),
    Module.finrank_baseChange]

end FractionAugmentation

end HigherSpecht
end
end CanonicalSource28

section CanonicalSource29
/- Source: HigherSpecht/PolynomialAugmentation.lean -/



/-! Polynomial extension of an actual augmented finite algebra. -/

noncomputable section

open scoped TensorProduct
open Module TensorProduct MvPolynomial

namespace HigherSpecht

variable {K B : Type*} [Field K] [CommRing B] [Algebra K B] (σ : Type*)

attribute [local instance] MvPolynomial.algebraMvPolynomial

def polynomialAugmentation (eps : B →ₐ[K] K) :
    MvPolynomial σ B →ₐ[MvPolynomial σ K] MvPolynomial σ K where
  toRingHom := MvPolynomial.map eps.toRingHom
  commutes' p := by
    change MvPolynomial.map eps.toRingHom
      (MvPolynomial.map (algebraMap K B) p) = p
    rw [MvPolynomial.map_map]
    have h : eps.toRingHom.comp (algebraMap K B) = RingHom.id K := by
      ext x
      exact eps.commutes x
    rw [h, MvPolynomial.map_id]

theorem polynomialAugmentation_nilpotent
    (eps : B →ₐ[K] K) (hnil : ∀ b : B, eps b = 0 → IsNilpotent b)
    (p : MvPolynomial σ B) (hp : polynomialAugmentation σ eps p = 0) :
    IsNilpotent p := by
  apply MvPolynomial.isNilpotent_iff.mpr
  intro a
  apply hnil
  have hc := congrArg (fun q : MvPolynomial σ K => q.coeff a) hp
  change (MvPolynomial.map eps.toRingHom p).coeff a = (0 : MvPolynomial σ K).coeff a at hc
  simpa only [MvPolynomial.coeff_map, MvPolynomial.coeff_zero, Finsupp.zero_apply,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hc

/-- The ordinary polynomial coefficient extension, with its actual
polynomial-ring scalar action. -/
def polynomialCoefficientTensorEquiv :
    MvPolynomial σ K ⊗[K] B ≃ₐ[MvPolynomial σ K] MvPolynomial σ B :=
  { ((Algebra.TensorProduct.comm K (MvPolynomial σ K) B).trans
      ((MvPolynomial.algebraTensorAlgEquiv K B).restrictScalars K)).toRingEquiv with
    commutes' p := by
      change MvPolynomial.algebraTensorAlgEquiv K B (1 ⊗ₜ[K] p) =
        MvPolynomial.map (algebraMap K B) p
      simp only [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul] }

theorem polynomialCoefficient_free [Module.Free K B] :
    Module.Free (MvPolynomial σ K) (MvPolynomial σ B) := by
  exact Module.Free.of_basis
    (((Module.Free.chooseBasis K B).baseChange (MvPolynomial σ K)).map
      (polynomialCoefficientTensorEquiv (K := K) (B := B) σ).toLinearEquiv)

theorem polynomialCoefficient_finite [Module.Free K B] [Module.Finite K B] :
    Module.Finite (MvPolynomial σ K) (MvPolynomial σ B) := by
  exact Module.Finite.of_basis
    (((Module.Free.chooseBasis K B).baseChange (MvPolynomial σ K)).map
      (polynomialCoefficientTensorEquiv (K := K) (B := B) σ).toLinearEquiv)

theorem polynomialCoefficient_finrank [Module.Free K B] :
    Module.finrank (MvPolynomial σ K) (MvPolynomial σ B) = Module.finrank K B := by
  rw [← (polynomialCoefficientTensorEquiv (K := K) (B := B) σ).toLinearEquiv.finrank_eq,
    Module.finrank_baseChange]

theorem length_polynomialAugmentationPrime
    [Module.Free K B] [Module.Finite K B]
    (eps : B →ₐ[K] K) (hnil : ∀ b : B, eps b = 0 → IsNilpotent b) :
    Module.length
        (Localization.AtPrime (RingHom.ker (polynomialAugmentation σ eps)))
        (Localization.AtPrime (RingHom.ker (polynomialAugmentation σ eps))) =
      (Module.finrank K B : ℕ∞) := by
  letI := polynomialCoefficient_free (K := K) (B := B) σ
  letI := polynomialCoefficient_finite (K := K) (B := B) σ
  rw [length_augmentationPrimeLocalization (polynomialAugmentation σ eps)
      (polynomialAugmentation_nilpotent σ eps hnil),
    polynomialCoefficient_finrank]

end HigherSpecht
end
end CanonicalSource29

section CanonicalSource30
/- Source: HigherSpecht/QuotientLocalizationLength.lean -/



/-!
# Transport of actual local quotient length

The quotient/localization commutation is the existing localization universal
property.  The prime used below is the literal pullback of the augmentation
kernel through the supplied quotient isomorphism.
-/

noncomputable section

namespace HigherSpecht

variable {R C A : Type*} [CommRing R] [CommRing C] [IsDomain C]
  [CommRing A] [Algebra C A]

def quotientAugmentationPrime (I : Ideal R) (E : R ⧸ I ≃+* A)
    (eps : A →ₐ[C] C) : Ideal R :=
  RingHom.ker (eps.toRingHom.comp (E.toRingHom.comp (Ideal.Quotient.mk I)))

instance quotientAugmentationPrime_isPrime (I : Ideal R) (E : R ⧸ I ≃+* A)
    (eps : A →ₐ[C] C) : (quotientAugmentationPrime I E eps).IsPrime :=
  RingHom.ker_isPrime _

theorem quotientAugmentationPrime_eq_radical
    (I : Ideal R) (E : R ⧸ I ≃+* A) (eps : A →ₐ[C] C)
    (hnil : ∀ a : A, eps a = 0 → IsNilpotent a) :
    quotientAugmentationPrime I E eps = I.radical := by
  apply le_antisymm
  · intro p hp
    obtain ⟨k, hk⟩ := hnil (E (Ideal.Quotient.mk I p)) hp
    apply Ideal.mem_radical_iff.mpr
    refine ⟨k, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
    apply E.injective
    simpa only [map_pow, map_zero] using hk
  · apply (inferInstance : (quotientAugmentationPrime I E eps).IsPrime).radical_le_iff.mpr
    intro p hp
    change eps (E (Ideal.Quotient.mk I p)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero, map_zero]

def quotientLocalizationAugmentationEquiv
    (I : Ideal R) (E : R ⧸ I ≃+* A) (eps : A →ₐ[C] C) :
    (Localization.AtPrime (quotientAugmentationPrime I E eps) ⧸
      I.map (algebraMap R (Localization.AtPrime (quotientAugmentationPrime I E eps))))
      ≃+* Localization.AtPrime (RingHom.ker eps) := by
  let P := quotientAugmentationPrime I E eps
  let M := Algebra.algebraMapSubmonoid (R ⧸ I) P.primeCompl
  have hM : M.map E.toMonoidHom = (RingHom.ker eps).primeCompl := by
    change (P.primeCompl.map (Ideal.Quotient.mk I).toMonoidHom).map E.toMonoidHom = _
    rw [Submonoid.map_map]
    exact Ideal.map_primeCompl_comap_of_surjective
      (E.toRingHom.comp (Ideal.Quotient.mk I))
      (E.surjective.comp Ideal.Quotient.mk_surjective) (RingHom.ker eps)
  exact IsLocalization.ringEquivOfRingEquiv
    (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P)))
    (Localization.AtPrime (RingHom.ker eps)) E hM

/-- Equality of the actual primes transports the local quotient and its length.
The prime instances are propositions and introduce no choice of localization. -/
theorem length_localized_quotient_congr_prime
    {R : Type*} [CommRing R] (I P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (h : P = Q) :
    Module.length (Localization.AtPrime P)
        (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P))) =
      Module.length (Localization.AtPrime Q)
        (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q))) := by
  subst Q
  rfl

theorem length_localized_quotient_eq_augmentation_length
    (I : Ideal R) (E : R ⧸ I ≃+* A) (eps : A →ₐ[C] C) :
    Module.length (Localization.AtPrime (quotientAugmentationPrime I E eps))
        (Localization.AtPrime (quotientAugmentationPrime I E eps) ⧸
          I.map (algebraMap R
            (Localization.AtPrime (quotientAugmentationPrime I E eps)))) =
      Module.length (Localization.AtPrime (RingHom.ker eps))
        (Localization.AtPrime (RingHom.ker eps)) := by
  let S := Localization.AtPrime (quotientAugmentationPrime I E eps)
  let J := I.map (algebraMap R S)
  have hsurj : Function.Surjective (algebraMap S (S ⧸ J)) :=
    Ideal.Quotient.mk_surjective
  rw [Module.length_eq_of_surjective (M := S ⧸ J) hsurj]
  exact length_self_eq_of_ringEquiv (quotientLocalizationAugmentationEquiv I E eps)

theorem length_localized_quotient_of_augmented_model
    [Module.Free C A] [Module.Finite C A]
    (I : Ideal R) (E : R ⧸ I ≃+* A) (eps : A →ₐ[C] C)
    (hnil : ∀ a : A, eps a = 0 → IsNilpotent a) :
    Module.length (Localization.AtPrime (quotientAugmentationPrime I E eps))
        (Localization.AtPrime (quotientAugmentationPrime I E eps) ⧸
          I.map (algebraMap R
            (Localization.AtPrime (quotientAugmentationPrime I E eps)))) =
      (Module.finrank C A : ℕ∞) := by
  rw [length_localized_quotient_eq_augmentation_length,
    length_augmentationPrimeLocalization eps hnil]

end HigherSpecht
end
end CanonicalSource30

section CanonicalSource31
/- Source: HigherSpecht/PrimaryComponentLengths.lean -/



/-!
# The actual generic lengths in Proposition 7.3

At the coordinate prime belonging to a selected block, every other primary
component becomes the unit ideal: an outside coordinate is invertible there
and a power of it belongs to that component.  The remaining quotient is the
polynomial extension of the actual Springer algebra.  Its nilpotent
augmentation and fraction-field localization compute its composition length.
-/

noncomputable section

open Module Finset MvPolynomial TauCeti

namespace HigherSpecht

theorem localization_map_iInf_finite
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S]
    {ι : Type*} [Fintype ι] (I : ι → Ideal R) :
    (⨅ i, I i).map (algebraMap R S) = ⨅ i, (I i).map (algebraMap R S) := by
  classical
  simpa only [Finset.inf_eq_iInf, Finset.mem_univ, iInf_true,
    Function.comp_apply, IsLocalization.mapFrameHom_apply] using
    map_finset_inf (IsLocalization.mapFrameHom M S) Finset.univ I

variable {K : Type*} [Field K] {n : ℕ} {lam : YoungDiagram}

instance coordinateIdeal_isPrime (A : Finset (Fin n)) :
    (coordinateIdeal K A).IsPrime :=
  MvPolynomial.span_X_image_isPrime (R := K) (A : Set (Fin n))

theorem map_other_component_at_coordinatePrime
    (A B : SpringerCoordinateBlocks n lam) (hBA : B ≠ A) :
    (blockSpringerIdeal K B.val lam).map
      (algebraMap (PolynomialRing n K) (Localization.AtPrime (coordinateIdeal K A.val))) = ⊤ := by
  obtain ⟨i, hiB, hiA⟩ := exists_coordinate_outside_of_block_ne A B hBA
  let S := Localization.AtPrime (coordinateIdeal K A.val)
  have hi : (MvPolynomial.X i : PolynomialRing n K) ∈
      (coordinateIdeal K A.val).primeCompl := by
    exact fun h => hiA ((X_mem_coordinateIdeal_iff (R := K) A.val i).mp h)
  have hu : IsUnit (algebraMap (PolynomialRing n K) S (MvPolynomial.X i)) :=
    IsLocalization.map_units S ⟨MvPolynomial.X i, hi⟩
  apply Ideal.eq_top_of_isUnit_mem
  · exact Ideal.mem_map_of_mem (algebraMap (PolynomialRing n K) S)
      (X_pow_card_mem_blockSpringerIdeal (R := K) B.val lam B.property hiB)
  · simpa only [map_pow] using hu.pow B.val.card

/-- The exact primary component which survives the actual localization. -/
theorem untruncatedIdeal_map_at_coordinatePrime
    (hn : lam.card ≤ n) (A : SpringerCoordinateBlocks n lam) :
    (untruncatedIdeal K n lam).map
        (algebraMap (PolynomialRing n K) (Localization.AtPrime (coordinateIdeal K A.val))) =
      (blockSpringerIdeal K A.val lam).map
        (algebraMap (PolynomialRing n K) (Localization.AtPrime (coordinateIdeal K A.val))) := by
  classical
  rw [untruncatedIdeal_eq_componentIntersection hn, springerComponentIntersection,
    localization_map_iInf_finite (coordinateIdeal K A.val).primeCompl]
  apply le_antisymm (iInf_le _ A)
  apply le_iInf
  intro B
  by_cases hBA : B = A
  · subst B
    exact le_rfl
  · rw [map_other_component_at_coordinatePrime A B hBA]
    exact le_top

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem length_blockSpringerIdeal_at_coordinatePrime
    (A : SpringerCoordinateBlocks n lam) :
    Module.length (Localization.AtPrime (coordinateIdeal K A.val))
        (Localization.AtPrime (coordinateIdeal K A.val) ⧸
          (blockSpringerIdeal K A.val lam).map
            (algebraMap (PolynomialRing n K) (Localization.AtPrime (coordinateIdeal K A.val)))) =
      (lam.card.factorial / rowFactorialProduct lam : ℕ) := by
  letI := springerRing_finiteDimensional K lam
  letI := springerRing_free (R := K) lam
  let C := MvPolynomial (OutsideCoordinates A.val) K
  let B := MvPolynomial (OutsideCoordinates A.val) (SpringerRing K lam)
  let eps : B →ₐ[C] C :=
    polynomialAugmentation (OutsideCoordinates A.val) (springerAugmentation lam)
  have hnil : ∀ p : B, eps p = 0 → IsNilpotent p :=
    polynomialAugmentation_nilpotent (OutsideCoordinates A.val)
      (springerAugmentation lam)
      (fun _ h => springer_isNilpotent_of_augmentation_eq_zero lam h)
  letI : Module.Free C B := polynomialCoefficient_free (OutsideCoordinates A.val)
  letI : Module.Finite C B := polynomialCoefficient_finite (OutsideCoordinates A.val)
  let E := (blockSpringerQuotientEquiv (R := K) A.val A.property).toRingEquiv
  have hprime : quotientAugmentationPrime (C := C) (A := B) (blockSpringerIdeal K A.val lam) E eps =
      coordinateIdeal K A.val := by
    rw [quotientAugmentationPrime_eq_radical (C := C) (A := B) _ E eps hnil,
      blockSpringerIdeal_radical A.val lam A.property]
  have hlength := length_localized_quotient_of_augmented_model (C := C) (A := B)
    (blockSpringerIdeal K A.val lam) E eps hnil
  rw [length_localized_quotient_congr_prime
    (blockSpringerIdeal K A.val lam) _ _ hprime] at hlength
  rw [show Module.finrank C B = Module.finrank K (SpringerRing K lam) from
    polynomialCoefficient_finrank (OutsideCoordinates A.val), finrank_springer K lam] at hlength
  exact hlength

/-- Generic component multiplicity is the genuine local module length,
not a number assigned from a proposed formula. -/
def genericComponentLength (K : Type*) [Field K]
    (A : SpringerCoordinateBlocks n lam) : ℕ∞ :=
  Module.length (Localization.AtPrime (coordinateIdeal K A.val))
    (Localization.AtPrime (coordinateIdeal K A.val) ⧸
      (untruncatedIdeal K n lam).map
        (algebraMap (PolynomialRing n K) (Localization.AtPrime (coordinateIdeal K A.val))))

/-- The generic length of every component in Proposition 7.3, in every
field characteristic.  The ambient dimension and every selected block
are unrestricted subject to the paper's actual cardinality condition. -/
theorem proposition_7_3_generic_component_length
    (hn : lam.card ≤ n) (A : SpringerCoordinateBlocks n lam) :
    genericComponentLength K A = (lam.card.factorial / rowFactorialProduct lam : ℕ) := by
  unfold genericComponentLength
  rw [untruncatedIdeal_map_at_coordinatePrime hn A]
  exact length_blockSpringerIdeal_at_coordinatePrime A

end HigherSpecht
end
end CanonicalSource31

section CanonicalSource32
/- Source: HigherSpecht/StaircaseOrthants.lean -/



/-!
# A finite disjoint orthant decomposition of the actual standard exponents

Clip every exponent at the height of the diagram.  Entries below that height
are fixed; entries at the cap may have arbitrary nonnegative excess.  The
shuffle condition is unchanged by clipping because every diagram row lies
strictly below the cap.  Thus this is a literal bijection of exponent sets,
not a Hilbert-series ansatz.  Its free-coordinate count is at most n-|lambda|.
-/

noncomputable section

open Finset TauCeti
open scoped Classical

namespace HigherSpecht

abbrev ExponentCap (n h : ℕ) := Fin n → Fin (h + 1)

def capExponent {n : ℕ} (h : ℕ) (a : Fin n →₀ ℕ) : ExponentCap n h :=
  fun i => ⟨min (a i) h, Nat.lt_succ_of_le (min_le_right _ _)⟩

def capBase {n h : ℕ} (b : ExponentCap n h) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (b i).val)

abbrev CapFreeCoordinates {n h : ℕ} (b : ExponentCap n h) :=
  {i : Fin n // (b i).val = h}

def liftCapExponent {n h : ℕ} (b : ExponentCap n h)
    (u : CapFreeCoordinates b →₀ ℕ) : Fin n →₀ ℕ :=
  capBase b + Finsupp.embDomain (Function.Embedding.subtype _) u

def capExcess {n : ℕ} (h : ℕ) (a : Fin n →₀ ℕ) :
    CapFreeCoordinates (capExponent h a) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => a i.val - h)

@[simp] theorem capBase_apply {n h : ℕ} (b : ExponentCap n h) (i : Fin n) :
    capBase b i = (b i).val := rfl

theorem liftCapExponent_apply_free {n h : ℕ} (b : ExponentCap n h)
    (u : CapFreeCoordinates b →₀ ℕ) (i : CapFreeCoordinates b) :
    liftCapExponent b u i.val = h + u i := by
  change (b i.val).val +
    Finsupp.embDomain (Function.Embedding.subtype _) u i.val = h + u i
  exact congrArg₂ Nat.add i.property
    (Finsupp.embDomain_apply_self (Function.Embedding.subtype _) u i)

theorem liftCapExponent_apply_fixed {n h : ℕ} (b : ExponentCap n h)
    (u : CapFreeCoordinates b →₀ ℕ) (i : Fin n) (hi : (b i).val ≠ h) :
    liftCapExponent b u i = (b i).val := by
  rw [liftCapExponent, Finsupp.add_apply, capBase_apply,
    Finsupp.embDomain_of_notMem_range, add_zero]
  rintro ⟨j, hj⟩
  exact hi (hj ▸ j.property)

@[simp] theorem capExponent_lift {n h : ℕ} (b : ExponentCap n h)
    (u : CapFreeCoordinates b →₀ ℕ) : capExponent h (liftCapExponent b u) = b := by
  funext i
  apply Fin.ext
  change min (liftCapExponent b u i) h = (b i).val
  by_cases hi : (b i).val = h
  · rw [liftCapExponent_apply_free b u ⟨i, hi⟩,
      Nat.min_eq_right (Nat.le_add_right _ _), hi]
  · rw [liftCapExponent_apply_fixed b u i hi,
      Nat.min_eq_left (Nat.le_of_lt_succ (b i).isLt)]

@[simp] theorem liftCapExponent_capExcess {n : ℕ} (h : ℕ) (a : Fin n →₀ ℕ) :
    liftCapExponent (capExponent h a) (capExcess h a) = a := by
  ext i
  by_cases hi : (capExponent h a i).val = h
  · rw [liftCapExponent_apply_free _ _ ⟨i, hi⟩]
    change h + (a i - h) = a i
    have hh : h ≤ a i := by
      change min (a i) h = h at hi
      omega
    exact Nat.add_sub_of_le hh
  · rw [liftCapExponent_apply_fixed _ _ i hi]
    change min (a i) h = a i
    change min (a i) h ≠ h at hi
    omega

theorem capExcess_lift_apply {n h : ℕ} (b : ExponentCap n h)
    (u : CapFreeCoordinates b →₀ ℕ) (i : CapFreeCoordinates b) :
    liftCapExponent b u i.val - h = u i := by
  rw [liftCapExponent_apply_free, Nat.add_sub_cancel_left]

theorem degree_liftCapExponent {n h : ℕ} (b : ExponentCap n h)
    (u : CapFreeCoordinates b →₀ ℕ) :
    (liftCapExponent b u).degree = (capBase b).degree + u.degree := by
  rw [liftCapExponent, map_add, Finsupp.embDomain_eq_mapDomain, Finsupp.degree_mapDomain]

theorem shuffleBound_cap_iff {n : ℕ} (lam : YoungDiagram) (a : Fin n →₀ ℕ) :
    ShuffleBound n lam (capBase (capExponent (lam.colLen 0) a)) ↔
      ShuffleBound n lam a := by
  constructor
  · rintro ⟨U, hU, ha⟩
    refine ⟨U, hU, fun c => ?_⟩
    have hb := ha c
    have hr : c.val.1 < lam.colLen 0 :=
      YoungDiagram.lt_colLen_zero_of_mem c.property
    change min (a (U c)) (lam.colLen 0) ≤ c.val.1 at hb
    omega
  · rintro ⟨U, hU, ha⟩
    exact ⟨U, hU, fun c => (min_le_left _ _).trans (ha c)⟩

abbrev StaircaseCap (n : ℕ) (lam : YoungDiagram) :=
  {b : ExponentCap n (lam.colLen 0) // ShuffleBound n lam (capBase b)}

instance finite_staircaseCap (n : ℕ) (lam : YoungDiagram) : Finite (StaircaseCap n lam) :=
  inferInstanceAs (Finite {b : ExponentCap n (lam.colLen 0) // _})

instance fintype_staircaseCap (n : ℕ) (lam : YoungDiagram) : Fintype (StaircaseCap n lam) :=
  Fintype.ofFinite _

def staircaseOrthantLift (n : ℕ) (lam : YoungDiagram)
    (z : Σ b : StaircaseCap n lam, CapFreeCoordinates b.val →₀ ℕ) :
    UntruncatedStaircaseExponents n lam :=
  ⟨liftCapExponent z.1.val z.2,
    (mem_untruncatedStaircaseExponents_iff _).mpr
      ((shuffleBound_cap_iff lam _).mp (by rw [capExponent_lift]; exact z.1.property))⟩

theorem staircaseOrthantLift_injective (n : ℕ) (lam : YoungDiagram) :
    Function.Injective (staircaseOrthantLift n lam) := by
  rintro ⟨b, u⟩ ⟨c, v⟩ h
  have hb : b = c := by
    apply Subtype.ext
    have hc := congrArg (fun a : UntruncatedStaircaseExponents n lam =>
      capExponent (lam.colLen 0) a.val) h
    simpa only [staircaseOrthantLift, capExponent_lift] using hc
  cases hb
  have huv : u = v := by
    ext i
    have hi := congrArg (fun a : UntruncatedStaircaseExponents n lam => a.val i.val) h
    change liftCapExponent b.val u i.val = liftCapExponent b.val v i.val at hi
    rw [liftCapExponent_apply_free, liftCapExponent_apply_free] at hi
    exact Nat.add_left_cancel hi
  exact congrArg (Sigma.mk b) huv

theorem staircaseOrthantLift_surjective (n : ℕ) (lam : YoungDiagram) :
    Function.Surjective (staircaseOrthantLift n lam) := by
  intro a
  refine ⟨⟨⟨capExponent (lam.colLen 0) a.val,
    (shuffleBound_cap_iff lam a.val).mpr
      ((mem_untruncatedStaircaseExponents_iff a.val).mp a.property)⟩,
    capExcess (lam.colLen 0) a.val⟩, ?_⟩
  exact Subtype.ext (liftCapExponent_capExcess _ _)

def staircaseOrthantEquiv (n : ℕ) (lam : YoungDiagram) :
    UntruncatedStaircaseExponents n lam ≃
      Σ b : StaircaseCap n lam, CapFreeCoordinates b.val →₀ ℕ :=
  (Equiv.ofBijective (staircaseOrthantLift n lam)
    ⟨staircaseOrthantLift_injective n lam, staircaseOrthantLift_surjective n lam⟩).symm

theorem staircaseCap_freeCard_le {n : ℕ} {lam : YoungDiagram}
    (b : StaircaseCap n lam) : Fintype.card (CapFreeCoordinates b.val) ≤ n - lam.card := by
  obtain ⟨U, hU, hb⟩ := b.property
  let f : ↥lam.cells → {i : Fin n // (b.val i).val ≠ lam.colLen 0} := fun c =>
    ⟨U c, by
      have h := hb c
      have hr : c.val.1 < lam.colLen 0 :=
        YoungDiagram.lt_colLen_zero_of_mem c.property
      change (b.val (U c)).val ≤ c.val.1 at h
      omega⟩
  have hcard := Fintype.card_le_of_injective f (by
    intro c d h
    exact U.injective (congrArg Subtype.val h))
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe] at hcard
  change lam.card ≤ n - Fintype.card (CapFreeCoordinates b.val) at hcard
  have hfree : Fintype.card (CapFreeCoordinates b.val) ≤ n := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective (fun i : CapFreeCoordinates b.val => i.val)
        Subtype.val_injective
  omega

end HigherSpecht
end
end CanonicalSource32

section CanonicalSource33
/- Source: HigherSpecht/OrthantHilbertSeries.lean -/



/-!
# Hilbert series from the actual disjoint orthants

Every coefficient is the dimension of the image of homogeneous polynomials
in the genuine quotient.  The integral standard-monomial basis identifies
that coefficient with the degree fiber of the clipped-exponent bijection.
Consequently its Hilbert series has denominator `(1-X)^(n-|lambda|)` over
the rationals, independently of the coefficient field's characteristic.
-/

noncomputable section

open Module MvPolynomial TauCeti Finset
open scoped Classical PowerSeries

namespace HigherSpecht

abbrev FiniteDegreeExponents (σ : Type*) (d : ℕ) := {a : σ →₀ ℕ // a.degree = d}

instance finite_finiteDegreeExponents (σ : Type*) [Fintype σ] (d : ℕ) :
    Finite (FiniteDegreeExponents σ d) :=
  Finite.of_injective
    (fun a : FiniteDegreeExponents σ d => fun i : σ =>
      (⟨a.val i, Nat.lt_succ_of_le ((Finsupp.le_degree i a.val).trans_eq a.property)⟩ : Fin (d + 1)))
    (by intro a b h; apply Subtype.ext; ext i; exact congrArg Fin.val (congrFun h i))

instance fintype_finiteDegreeExponents (σ : Type*) [Fintype σ] (d : ℕ) :
    Fintype (FiniteDegreeExponents σ d) := Fintype.ofFinite _

def degreeAntidiagonalEquiv (σ : Type*) [Fintype σ] (d : ℕ) :
    FiniteDegreeExponents σ d ≃ ↥(Finset.finsuppAntidiag (Finset.univ : Finset σ) d) where
  toFun a := ⟨a.val, by
    rw [Finset.mem_finsuppAntidiag]
    exact ⟨(Finsupp.degree_eq_sum a.val).symm.trans a.property, Finset.subset_univ _⟩⟩
  invFun a := ⟨a.val, (Finsupp.degree_eq_sum a.val).trans
    (Finset.mem_finsuppAntidiag.mp a.property).1⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem invOneSubPow_val_eq_geometric_pow (R : Type*) [CommRing R] (r : ℕ) :
    (PowerSeries.invOneSubPow R r).val = (PowerSeries.mk (fun _ => (1 : R))) ^ r := by
  cases r with
  | zero => simp only [PowerSeries.invOneSubPow_zero, Units.val_one, pow_zero]
  | succ r =>
    exact (PowerSeries.mk_one_pow_eq_mk_choose_add R r).symm

theorem coeff_invOneSubPow_card (R : Type*) [CommRing R]
    (σ : Type*) [Fintype σ] (d : ℕ) :
    PowerSeries.coeff d (PowerSeries.invOneSubPow R (Fintype.card σ)).val =
      (Nat.card (FiniteDegreeExponents σ d) : R) := by
  rw [invOneSubPow_val_eq_geometric_pow,
    show (PowerSeries.mk (fun _ => (1 : R))) ^ Fintype.card σ =
      ∏ _i : σ, PowerSeries.mk (fun _ => (1 : R)) by simp only [Finset.prod_const, Finset.card_univ]]
  rw [PowerSeries.coeff_prod]
  simp only [PowerSeries.coeff_mk, Finset.prod_const_one, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  congr 1
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (degreeAntidiagonalEquiv σ d).symm

abbrev ShiftedDegreeExponents (σ : Type*) (s d : ℕ) :=
  {a : σ →₀ ℕ // s + a.degree = d}

instance finite_shiftedDegreeExponents (σ : Type*) [Fintype σ] (s d : ℕ) :
    Finite (ShiftedDegreeExponents σ s d) := by
  exact Finite.of_injective
    (fun a : ShiftedDegreeExponents σ s d =>
      (⟨a.val, by have h := a.property; omega⟩ : FiniteDegreeExponents σ (d - s)))
    (by
      intro a b h
      exact Subtype.ext (congrArg
        (fun z : FiniteDegreeExponents σ (d - s) => z.val) h))

instance fintype_shiftedDegreeExponents (σ : Type*) [Fintype σ] (s d : ℕ) :
    Fintype (ShiftedDegreeExponents σ s d) := Fintype.ofFinite _

theorem card_shiftedDegreeExponents (σ : Type*) [Fintype σ] (s d : ℕ) :
    Nat.card (ShiftedDegreeExponents σ s d) =
      if s ≤ d then Nat.card (FiniteDegreeExponents σ (d - s)) else 0 := by
  by_cases hs : s ≤ d
  · rw [if_pos hs]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun a => by omega)
  · rw [if_neg hs]
    letI : IsEmpty (ShiftedDegreeExponents σ s d) := ⟨by
      rintro ⟨a, ha⟩
      omega⟩
    exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

theorem coeff_shifted_orthant (R : Type*) [CommRing R]
    (σ : Type*) [Fintype σ] (s d : ℕ) :
    PowerSeries.coeff d
        ((PowerSeries.X : PowerSeries R) ^ s *
          (PowerSeries.invOneSubPow R (Fintype.card σ)).val) =
      (Nat.card (ShiftedDegreeExponents σ s d) : R) := by
  rw [PowerSeries.coeff_X_pow_mul', coeff_invOneSubPow_card, card_shiftedDegreeExponents]
  split_ifs <;> simp only [Nat.cast_zero]

def subtypeSigmaRightEquiv {ι : Type*} {A : ι → Type*} (P : ∀ i, A i → Prop) :
    {z : Σ i, A i // P z.1 z.2} ≃ Σ i, {a : A i // P i a} where
  toFun z := ⟨z.val.1, ⟨z.val.2, z.property⟩⟩
  invFun z := ⟨⟨z.1, z.2.val⟩, z.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

abbrev UntruncatedMonomialDegreeIndex (n : ℕ) (lam : YoungDiagram) (d : ℕ) :=
  {a : UntruncatedStaircaseExponents n lam // a.val.degree = d}

instance finite_untruncatedMonomialDegreeIndex (n : ℕ) (lam : YoungDiagram) (d : ℕ) :
    Finite (UntruncatedMonomialDegreeIndex n lam d) :=
  Finite.of_injective
    (fun a : UntruncatedMonomialDegreeIndex n lam d =>
      (⟨a.val.val, a.property⟩ : FiniteDegreeExponents (Fin n) d))
    (by
      intro a b h
      exact Subtype.ext (Subtype.ext (congrArg
        (fun z : FiniteDegreeExponents (Fin n) d => z.val) h)))

instance fintype_untruncatedMonomialDegreeIndex (n : ℕ) (lam : YoungDiagram) (d : ℕ) :
    Fintype (UntruncatedMonomialDegreeIndex n lam d) := Fintype.ofFinite _

def untruncatedMonomialDegreeBasis (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (d : ℕ) :
    Basis (UntruncatedMonomialDegreeIndex n lam d) K
      (homogeneousQuotientPiece (untruncatedIdeal K n lam) d) :=
  homogeneousQuotientBasis (untruncatedIdeal K n lam)
    (untruncatedIdeal_isHomogeneous hk) (untruncatedStandardMonomialBasis hk)
    (fun a => MvPolynomial.monomial a.val 1) (fun a => a.val.degree)
    (fun _ => MvPolynomial.isHomogeneous_monomial 1 rfl)
    (untruncatedStandardMonomialBasis_apply hk) d

def untruncatedHilbertFunction (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (d : ℕ) : ℕ :=
  Module.finrank K (homogeneousQuotientPiece (untruncatedIdeal K n lam) d)

theorem untruncatedHilbertFunction_eq_card (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (d : ℕ) :
    untruncatedHilbertFunction K n lam d = Nat.card (UntruncatedMonomialDegreeIndex n lam d) := by
  rw [untruncatedHilbertFunction, Module.finrank_eq_card_basis
    (untruncatedMonomialDegreeBasis K n lam hk d), Nat.card_eq_fintype_card]

theorem untruncatedHilbertFunction_independent_field (K L : Type*) [Field K] [Field L]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (d : ℕ) :
    untruncatedHilbertFunction K n lam d = untruncatedHilbertFunction L n lam d := by
  rw [untruncatedHilbertFunction_eq_card K n lam hk,
    untruncatedHilbertFunction_eq_card L n lam hk]

def staircaseDegreeOrthantEquiv (n : ℕ) (lam : YoungDiagram) (d : ℕ) :
    UntruncatedMonomialDegreeIndex n lam d ≃
      Σ b : StaircaseCap n lam,
        ShiftedDegreeExponents (CapFreeCoordinates b.val) (capBase b.val).degree d :=
  ((staircaseOrthantEquiv n lam).subtypeEquiv (fun a => by
    have h := congrArg (fun b : UntruncatedStaircaseExponents n lam => b.val.degree)
      ((staircaseOrthantEquiv n lam).symm_apply_apply a)
    rw [show ((staircaseOrthantEquiv n lam).symm
      ((staircaseOrthantEquiv n lam) a)).val =
      liftCapExponent ((staircaseOrthantEquiv n lam) a).1.val
        ((staircaseOrthantEquiv n lam) a).2 from rfl,
      degree_liftCapExponent] at h
    rw [h])).trans (subtypeSigmaRightEquiv _)

def untruncatedHilbertSeries (K : Type*) [Field K] (n : ℕ) (lam : YoungDiagram) :
    PowerSeries ℚ := PowerSeries.mk (fun d => (untruncatedHilbertFunction K n lam d : ℚ))

theorem untruncatedHilbertSeries_orthants (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    untruncatedHilbertSeries K n lam =
      ∑ b : StaircaseCap n lam, (PowerSeries.X : PowerSeries ℚ) ^ (capBase b.val).degree *
        (PowerSeries.invOneSubPow ℚ (Fintype.card (CapFreeCoordinates b.val))).val := by
  apply PowerSeries.ext
  intro d
  rw [untruncatedHilbertSeries, PowerSeries.coeff_mk,
    untruncatedHilbertFunction_eq_card K n lam hk,
    Nat.card_congr (staircaseDegreeOrthantEquiv n lam d), Nat.card_sigma,
    Nat.cast_sum, map_sum]
  apply Finset.sum_congr rfl
  intro b _
  exact (coeff_shifted_orthant ℚ (CapFreeCoordinates b.val) (capBase b.val).degree d).symm

/-- The actual standard-degree Hilbert numerator furnished by the finite
orthants.  Its value is not prescribed by the claimed multiplicity. -/
def untruncatedOrthantNumerator (n : ℕ) (lam : YoungDiagram) : Polynomial ℚ :=
  ∑ b : StaircaseCap n lam,
    Polynomial.X ^ (capBase b.val).degree *
      (1 - Polynomial.X) ^ (n - lam.card - Fintype.card (CapFreeCoordinates b.val))

theorem polynomial_powerSeries_sum {R : Type*} [CommRing R] {ι : Type*}
    (s : Finset ι) (p : ι → Polynomial R) :
    ((∑ i ∈ s, p i : Polynomial R) : PowerSeries R) = ∑ i ∈ s, (p i : PowerSeries R) :=
  map_sum (Polynomial.coeToPowerSeries.ringHom) p s

theorem untruncatedHilbertSeries_eq_orthantNumerator (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    untruncatedHilbertSeries K n lam =
      (untruncatedOrthantNumerator n lam : PowerSeries ℚ) *
        (PowerSeries.invOneSubPow ℚ (n - lam.card)).val := by
  rw [untruncatedHilbertSeries_orthants K n lam hk, untruncatedOrthantNumerator,
    polynomial_powerSeries_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  simp only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_sub,
    Polynomial.coe_one, Polynomial.coe_X, mul_assoc]
  have h := PowerSeries.one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val
    ℚ (Fintype.card (CapFreeCoordinates b.val))
    (n - lam.card - Fintype.card (CapFreeCoordinates b.val))
  rw [Nat.add_sub_of_le (staircaseCap_freeCard_le b)] at h
  rw [h]

end HigherSpecht
end
end CanonicalSource33

section CanonicalSource34
/- Source: HigherSpecht/WeightedHilbertSeries.lean -/



/-!
# Comparison of standard and elementary-parameter Hilbert numerators

The actual homogeneous higher Specht basis supplies the weighted-parameter
series.  Its numerator evaluates to the actual basis cardinality.  Comparing
it to the independently obtained standard-degree orthant series proves the
factorial conversion between parameter rank and standard multiplicity.
-/

noncomputable section

open Module MvPolynomial TauCeti Finset
open scoped Classical PowerSeries

namespace HigherSpecht

instance fintype_untruncatedIndexHilbert (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) : Fintype (UntruncatedIndex n lam hk) := Fintype.ofFinite _

def untruncatedDegreeVectorPartitionEquiv (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (d : ℕ) :
    UntruncatedDegreeVectorIndex n lam hk d ≃
      Σ b : {b : UntruncatedIndex n lam hk // cochargeDegree b.val.left ≤ d},
        BoundedLengthPartitionDegree (n - lam.card) (d - cochargeDegree b.val.val.left) where
  toFun i :=
    ⟨⟨i.val.base, by
        have h : cochargeDegree i.val.base.val.left + i.val.multiplier.card = d :=
          i.property
        omega⟩,
      ⟨i.val.multiplier, i.val.multiplier_length, by
        change i.val.multiplier.card = d - cochargeDegree i.val.base.val.left
        have h : cochargeDegree i.val.base.val.left + i.val.multiplier.card = d :=
          i.property
        omega⟩⟩
  invFun z :=
    ⟨⟨z.1.val, z.2.val, z.2.property.1⟩, by
      change cochargeDegree z.1.val.val.left + z.2.val.card = d
      rw [z.2.property.2, Nat.add_sub_of_le z.1.property]⟩
  left_inv i := by cases i; rfl
  right_inv z := by cases z; rfl

theorem untruncatedHilbertFunction_by_parameter (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (d : ℕ) :
    untruncatedHilbertFunction ℚ n lam d =
      ∑ b : UntruncatedIndex n lam hk,
        if cochargeDegree b.val.left ≤ d then
          Nat.card (BoundedLengthPartitionDegree (n - lam.card) (d - cochargeDegree b.val.left))
        else 0 := by
  change Module.finrank ℚ (untruncatedGradedPiece ℚ n lam d).toSubmodule = _
  rw [Module.finrank_eq_nat_card_basis (untruncatedDegreeBasis ℚ n lam hk d),
    Nat.card_congr
      (untruncatedDegreeVectorPartitionEquiv n lam hk d), Nat.card_sigma]
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp)
    (fun b : UntruncatedIndex n lam hk =>
      Nat.card (BoundedLengthPartitionDegree (n - lam.card)
        (d - cochargeDegree b.val.left)))).symm

def untruncatedParameterNumerator (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) : Polynomial ℚ :=
  ∑ b : UntruncatedIndex n lam hk, Polynomial.X ^ cochargeDegree b.val.left

theorem untruncatedParameterNumerator_eval_one (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) :
    (untruncatedParameterNumerator n lam hk).eval 1 =
      (n.factorial / rowFactorialProduct lam : ℕ) := by
  simp only [untruncatedParameterNumerator, Polynomial.eval_finsetSum,
    Polynomial.eval_pow, Polynomial.eval_X, one_pow, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [← Nat.card_eq_fintype_card, card_untruncatedIndex_exact]

theorem untruncatedHilbertSeries_eq_parameterNumerator (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    untruncatedHilbertSeries K n lam =
      (untruncatedParameterNumerator n lam hk : PowerSeries ℚ) *
        (elementaryParameterSeriesUnit ℚ (n - lam.card)).val := by
  apply PowerSeries.ext
  intro d
  rw [untruncatedHilbertSeries, PowerSeries.coeff_mk,
    untruncatedHilbertFunction_independent_field K ℚ n lam hk,
    untruncatedHilbertFunction_by_parameter n lam hk, Nat.cast_sum,
    untruncatedParameterNumerator, polynomial_powerSeries_sum, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Polynomial.coe_pow, Polynomial.coe_X, PowerSeries.coeff_X_pow_mul',
    coeff_elementaryParameterSeriesUnit_partitions]
  split_ifs <;> simp only [Nat.cast_zero]

def elementaryGeometricFactor (m : ℕ) : Polynomial ℚ :=
  ∏ i : Fin m, ∑ j ∈ Finset.range (i.val + 1), Polynomial.X ^ j

def elementaryHilbertDenominator (m : ℕ) : Polynomial ℚ :=
  ∏ i : Fin m, (1 - Polynomial.X ^ (i.val + 1))

theorem elementaryHilbertDenominator_factor (m : ℕ) :
    elementaryHilbertDenominator m =
      (1 - Polynomial.X) ^ m * elementaryGeometricFactor m := by
  unfold elementaryHilbertDenominator elementaryGeometricFactor
  rw [show (1 - (Polynomial.X : Polynomial ℚ)) ^ m =
    ∏ _i : Fin m, (1 - Polynomial.X) by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin],
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact (mul_neg_geom_sum (Polynomial.X : Polynomial ℚ) (i.val + 1)).symm

theorem elementaryGeometricFactor_eval_one (m : ℕ) :
    (elementaryGeometricFactor m).eval 1 = (m.factorial : ℚ) := by
  unfold elementaryGeometricFactor
  simp only [Polynomial.eval_prod, Polynomial.eval_finsetSum, Polynomial.eval_pow,
    Polynomial.eval_X, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [← Nat.cast_prod]
  congr 1
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, Nat.factorial_succ, Nat.mul_comm]

theorem parameter_series_inverse_eq_denominator (m : ℕ) :
    ((elementaryParameterSeriesUnit ℚ m)⁻¹).val =
      (elementaryHilbertDenominator m : PowerSeries ℚ) := by
  rw [elementaryParameterSeriesUnit_inv]
  change _ = Polynomial.coeToPowerSeries.ringHom (∏ i : Fin m,
    (1 - Polynomial.X ^ (i.val + 1) : Polynomial ℚ))
  rw [map_prod]
  simp only [map_sub, map_one, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_X]

/-- Equality of actual polynomial numerators.  Cancellation takes place
only after both Hilbert-series identities have been proved coefficientwise. -/
theorem untruncatedHilbert_numerators_relation
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    untruncatedOrthantNumerator n lam * elementaryGeometricFactor (n - lam.card) =
      untruncatedParameterNumerator n lam hk := by
  apply Polynomial.coe_injective ℚ
  have h := untruncatedHilbertSeries_eq_parameterNumerator ℚ n lam hk
  rw [untruncatedHilbertSeries_eq_orthantNumerator ℚ n lam hk] at h
  have he := congrArg (fun f : PowerSeries ℚ =>
    f * ((elementaryParameterSeriesUnit ℚ (n - lam.card))⁻¹).val) h
  have hunit : (elementaryParameterSeriesUnit ℚ (n - lam.card)).val *
      ((elementaryParameterSeriesUnit ℚ (n - lam.card))⁻¹).val = 1 :=
    (elementaryParameterSeriesUnit ℚ (n - lam.card)).val_inv
  have hright :
      ((untruncatedParameterNumerator n lam hk : PowerSeries ℚ) *
        (elementaryParameterSeriesUnit ℚ (n - lam.card)).val) *
          ((elementaryParameterSeriesUnit ℚ (n - lam.card))⁻¹).val =
            (untruncatedParameterNumerator n lam hk : PowerSeries ℚ) := by
    rw [mul_assoc, hunit, mul_one]
  rw [hright] at he
  rw [parameter_series_inverse_eq_denominator, elementaryHilbertDenominator_factor,
    Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_sub,
    Polynomial.coe_one, Polynomial.coe_X] at he
  have hcancel : (PowerSeries.invOneSubPow ℚ (n - lam.card)).val *
      (1 - PowerSeries.X) ^ (n - lam.card) = 1 := by
    rw [← PowerSeries.invOneSubPow_inv_eq_one_sub_pow]
    exact (PowerSeries.invOneSubPow ℚ (n - lam.card)).val_inv
  simpa only [Polynomial.coe_mul, mul_assoc, ← mul_assoc
    (PowerSeries.invOneSubPow ℚ (n - lam.card)).val, hcancel, one_mul] using he

theorem untruncatedOrthantNumerator_eval_one
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    (untruncatedOrthantNumerator n lam).eval 1 * (n - lam.card).factorial =
      (n.factorial / rowFactorialProduct lam : ℕ) := by
  have h := congrArg (Polynomial.eval (1 : ℚ))
    (untruncatedHilbert_numerators_relation n lam hk)
  simpa only [Polynomial.eval_mul, elementaryGeometricFactor_eval_one,
    untruncatedParameterNumerator_eval_one] using h

end HigherSpecht
end
end CanonicalSource34

section CanonicalSource35
/- Source: HigherSpecht/StandardGradedMultiplicity.lean -/



/-!
# Standard graded multiplicity in Proposition 7.3

The Hilbert polynomial is proved to be the unique rational polynomial which
eventually equals the dimensions of the actual homogeneous quotient pieces.
In positive dimension multiplicity is its leading coefficient times the
factorial of degree; in dimension zero it is the actual vector-space length.
The factorial formula is derived from these invariants.  In particular the
printed value is never used as the definition of multiplicity.
-/

noncomputable section

open Module TauCeti Finset
open scoped Classical PowerSeries

namespace HigherSpecht

def untruncatedHilbertPolynomial (n : ℕ) (lam : YoungDiagram) : Polynomial ℚ :=
  Polynomial.hilbertPoly (untruncatedOrthantNumerator n lam) (n - lam.card)

theorem untruncatedHilbertPolynomial_eventual (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    ∃ N : ℕ, ∀ d > N,
      (untruncatedHilbertFunction K n lam d : ℚ) =
        (untruncatedHilbertPolynomial n lam).eval (d : ℚ) := by
  refine ⟨(untruncatedOrthantNumerator n lam).natDegree, fun d hd => ?_⟩
  have h := Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval
    (p := untruncatedOrthantNumerator n lam) (n - lam.card) hd
  rw [← untruncatedHilbertSeries_eq_orthantNumerator K n lam hk,
    untruncatedHilbertSeries, PowerSeries.coeff_mk] at h
  exact h

/-- A correspondence with the conventional Hilbert polynomial, not only
an identity for a chosen generating function. -/
theorem untruncatedHilbertPolynomial_unique (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (H : Polynomial ℚ)
    (hH : ∃ N : ℕ, ∀ d > N,
      (untruncatedHilbertFunction K n lam d : ℚ) = H.eval (d : ℚ)) :
    H = untruncatedHilbertPolynomial n lam := by
  obtain ⟨N, hN⟩ := hH
  apply Polynomial.eq_hilbertPoly_of_forall_coeff_eq_eval N
  intro d hd
  rw [← untruncatedHilbertSeries_eq_orthantNumerator K n lam hk,
    untruncatedHilbertSeries, PowerSeries.coeff_mk]
  exact hN d hd

theorem hilbertPoly_coeff_top (P : Polynomial ℚ) (d : ℕ) :
    (Polynomial.hilbertPoly P (d + 1)).coeff d = P.eval 1 / (d.factorial : ℚ) := by
  rw [Polynomial.hilbertPoly_succ]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_smul,
    Polynomial.coeff_preHilbertPoly_self, smul_eq_mul, ← Finset.sum_mul, div_eq_mul_inv]
  congr 1
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  simp only [one_pow, mul_one]

theorem hilbertPoly_natDegree_le (P : Polynomial ℚ) (d : ℕ) :
    (Polynomial.hilbertPoly P (d + 1)).natDegree ≤ d := by
  rw [Polynomial.hilbertPoly_succ]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact (Polynomial.natDegree_smul_le _ _).trans
    (Polynomial.natDegree_preHilbertPoly ℚ d i).le

theorem hilbertPoly_leadingCoeff_of_eval_one_ne_zero
    (P : Polynomial ℚ) (d : ℕ) (hP : P.eval 1 ≠ 0) :
    (Polynomial.hilbertPoly P (d + 1)).natDegree = d ∧
      (Polynomial.hilbertPoly P (d + 1)).leadingCoeff = P.eval 1 / (d.factorial : ℚ) := by
  have hcoeff : (Polynomial.hilbertPoly P (d + 1)).coeff d ≠ 0 := by
    rw [hilbertPoly_coeff_top]
    exact div_ne_zero hP (by exact_mod_cast Nat.factorial_ne_zero d)
  have hdeg := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (hilbertPoly_natDegree_le P d) hcoeff
  exact ⟨hdeg, by rw [Polynomial.leadingCoeff, hdeg, hilbertPoly_coeff_top]⟩

theorem rowFactorialProduct_pos (lam : YoungDiagram) : 0 < rowFactorialProduct lam :=
  Nat.prod_factorial_pos _ _

theorem rowFactorialProduct_dvd_factorial (lam : YoungDiagram) :
    rowFactorialProduct lam ∣ lam.card.factorial := by
  have h := Nat.prod_factorial_dvd_factorial_sum
    (Finset.range (lam.colLen 0)) lam.rowLen
  rwa [← YoungDiagram.card_eq_sum_range_rowLen lam le_rfl] at h

theorem rowFactorialProduct_dvd_ambient_factorial
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    rowFactorialProduct lam ∣ n.factorial :=
  (rowFactorialProduct_dvd_factorial lam).trans (Nat.factorial_dvd_factorial hk)

theorem componentFactorialProduct_dvd_factorial
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    (n - lam.card).factorial * rowFactorialProduct lam ∣ n.factorial := by
  have h := (Nat.mul_dvd_mul_right (rowFactorialProduct_dvd_factorial lam)
    (n - lam.card).factorial).trans
      (Nat.factorial_mul_factorial_dvd_factorial hk)
  simpa only [Nat.mul_comm] using h

theorem untruncatedOrthantNumerator_eval_one_pos
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    0 < (untruncatedOrthantNumerator n lam).eval 1 := by
  have h := untruncatedOrthantNumerator_eval_one n lam hk
  have hN : 0 < n.factorial / rowFactorialProduct lam :=
    Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos _)
      (rowFactorialProduct_dvd_ambient_factorial n lam hk))
      (rowFactorialProduct_pos lam)
  have hm : (0 : ℚ) < (n - lam.card).factorial := by positivity
  have hN' : (0 : ℚ) < (n.factorial / rowFactorialProduct lam : ℕ) := by exact_mod_cast hN
  nlinarith

theorem untruncatedHilbertPolynomial_degree_and_leadingCoeff
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (hm : 0 < n - lam.card) :
    (untruncatedHilbertPolynomial n lam).natDegree = n - lam.card - 1 ∧
      (untruncatedHilbertPolynomial n lam).leadingCoeff =
        (untruncatedOrthantNumerator n lam).eval 1 /
          ((n - lam.card - 1).factorial : ℚ) := by
  have h := hilbertPoly_leadingCoeff_of_eval_one_ne_zero
    (untruncatedOrthantNumerator n lam) (n - lam.card - 1)
    (ne_of_gt (untruncatedOrthantNumerator_eval_one_pos n lam hk))
  rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hm)] at h
  exact h

/-- Conventional standard graded multiplicity: the leading Hilbert
coefficient times the factorial of dimension minus one, with length in
dimension zero.  The dimension is the actual Krull dimension by
`untruncated_krullDimension_allFields`. -/
def standardGradedMultiplicity (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) : ℚ :=
  if n - lam.card = 0 then
    (Module.finrank K (UntruncatedRing K n lam) : ℚ)
  else ((n - lam.card - 1).factorial : ℚ) *
    (untruncatedHilbertPolynomial n lam).leadingCoeff

theorem standardGradedMultiplicity_eq_orthant_eval
    (K : Type*) [Field K] (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (hm : 0 < n - lam.card) :
    standardGradedMultiplicity K n lam = (untruncatedOrthantNumerator n lam).eval 1 := by
  rw [standardGradedMultiplicity, if_neg (Nat.ne_of_gt hm),
    (untruncatedHilbertPolynomial_degree_and_leadingCoeff n lam hk hm).2]
  have hf : (((n - lam.card - 1).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp

theorem untruncatedOrthantNumerator_eval_one_exact
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    (untruncatedOrthantNumerator n lam).eval 1 =
      (n.factorial / ((n - lam.card).factorial * rowFactorialProduct lam) : ℕ) := by
  have hm : (((n - lam.card).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  apply (mul_left_inj' hm).mp
  rw [untruncatedOrthantNumerator_eval_one n lam hk,
    Nat.cast_div_charZero (rowFactorialProduct_dvd_ambient_factorial n lam hk),
    Nat.cast_div_charZero (componentFactorialProduct_dvd_factorial n lam hk), Nat.cast_mul]
  have hr : ((rowFactorialProduct lam : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (rowFactorialProduct_pos lam))
  field_simp

/-- The standard graded multiplicity assertion of Proposition 7.3,
with the conventional Hilbert-polynomial invariant and every field
characteristic retained. -/
theorem proposition_7_3_standard_graded_multiplicity
    (K : Type*) [Field K] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    standardGradedMultiplicity K n lam =
      (n.factorial / ((n - lam.card).factorial * rowFactorialProduct lam) : ℕ) := by
  by_cases hm : n - lam.card = 0
  · have hn : lam.card = n := by omega
    rw [standardGradedMultiplicity, if_pos hm,
      finrank_fullSize_untruncated K lam hn, hm, Nat.factorial_zero, one_mul]
  · rw [standardGradedMultiplicity_eq_orthant_eval K n lam hk (Nat.pos_of_ne_zero hm),
      untruncatedOrthantNumerator_eval_one_exact n lam hk]

theorem proposition_7_3_multiplicities
    (K : Type*) [Field K] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    (∀ A : SpringerCoordinateBlocks n lam,
      genericComponentLength K A = (lam.card.factorial / rowFactorialProduct lam : ℕ)) ∧
      standardGradedMultiplicity K n lam =
        (n.factorial / ((n - lam.card).factorial * rowFactorialProduct lam) : ℕ) :=
  ⟨proposition_7_3_generic_component_length hk,
    proposition_7_3_standard_graded_multiplicity K n lam hk⟩

end HigherSpecht
end
end CanonicalSource35

section CanonicalSource36
/- Source: HigherSpecht/UntruncatedReducedness.lean -/



/-!
# Reducedness of every untruncated Springer algebra

For a diagram with at least two rows, an explicit squarefree monomial is
nonzero in the staircase basis and belongs to the radical of the actual
ideal. Its support consists of every unused coordinate and the label of
one cell in row one. Every coordinate component meets this support. This
gives a genuine nonzero nilpotent over every coefficient domain, with no
dimension, localization-length, or characteristic-zero premise.
-/

noncomputable section
open TauCeti Finset MvPolynomial
open scoped Classical BigOperators

namespace HigherSpecht

variable {R : Type*} [CommRing R] {n : ℕ} {mu : YoungDiagram}

def descendingStandardFilling (hn : mu.card ≤ n) : ↥mu.cells ↪ Fin n :=
  (StandardYoungTableau.rowSuperstandard mu).toTableau.toEmbedding.trans
    (Fin.revPerm.toEmbedding.trans (Fin.castLEEmb hn))

 theorem descendingStandardFilling_columnDescending (hn : mu.card ≤ n) :
    ColumnDescending (descendingStandardFilling hn) := by
  intro j r t hrt
  change Fin.castLE hn (Fin.rev ((StandardYoungTableau.rowSuperstandard mu)
      ⟨(t.val, j), YoungDiagram.mem_iff_lt_colLen.mpr t.isLt⟩)) <
    Fin.castLE hn (Fin.rev ((StandardYoungTableau.rowSuperstandard mu)
      ⟨(r.val, j), YoungDiagram.mem_iff_lt_colLen.mpr r.isLt⟩))
  apply Fin.rev_lt_rev.mpr
  exact (StandardYoungTableau.rowSuperstandard mu).col_strict hrt
    (YoungDiagram.mem_iff_lt_colLen.mpr t.isLt)

/-- The exponent of the actual squarefree monomial on a finite support. -/
def squarefreeSupportExponent (S : Finset (Fin n)) : Fin n →₀ ℕ :=
  ∑ i ∈ S, Finsupp.single i 1

@[simp] theorem squarefreeSupportExponent_apply (S : Finset (Fin n)) (i : Fin n) :
    squarefreeSupportExponent S i = if i ∈ S then 1 else 0 := by
  simp [squarefreeSupportExponent, Finsupp.sum_apply, Finsupp.single_apply, eq_comm]

 theorem monomial_squarefreeSupportExponent (S : Finset (Fin n)) :
    (MvPolynomial.monomial (squarefreeSupportExponent S) 1 : PolynomialRing n R) =
      ∏ i ∈ S, MvPolynomial.X i := by
  rw [squarefreeSupportExponent, MvPolynomial.monomial_sum_one]
  rfl

 theorem blockSpringerIdeal_eq_coordinate_of_one_row
    (A : Finset (Fin n)) (hA : A.card = mu.card) (hrow : mu.colLen 0 ≤ 1) :
    blockSpringerIdeal R A mu = coordinateIdeal R A := by
  apply le_antisymm (blockSpringerIdeal_le_coordinateIdeal (R := R) A mu hA)
  apply Ideal.span_le.mpr
  rintro p ⟨i, hi, rfl⟩
  change (MvPolynomial.X i : PolynomialRing n R) ∈ blockSpringerIdeal R A mu
  have hk : 0 < mu.card := by rw [← hA]; exact card_pos.mpr ⟨i, hi⟩
  have hlast : (0, mu.card - 1) ∈ mu := by
    rw [YoungDiagram.mem_iff_lt_rowLen,
      ← YoungDiagram.card_eq_rowLen_of_colLen_le_one hrow]
    omega
  have htail : 0 < columnTail mu (mu.card - 1) := by
    apply card_pos.mpr
    exact ⟨(0, mu.card - 1), mem_filter.mpr ⟨hlast, le_rfl⟩⟩
  have he := elementaryOn_mem_blockSpringerIdeal (R := R) A mu
    (Y := {i}) (singleton_subset_iff.mpr hi) 1 (by
      simp only [card_singleton, hA]
      have hh : (0 : ℤ) < (columnTail mu (mu.card - 1) : ℤ) := by exact_mod_cast htail
      omega)
  simpa only [elementaryOn, Finset.powersetCard_one, Finset.map_singleton,
    Finset.sum_singleton, Function.Embedding.coeFn_mk, Finset.prod_singleton] using he

 theorem untruncated_isReduced_of_one_row [IsDomain R]
    (hn : mu.card ≤ n) (hrow : mu.colLen 0 ≤ 1) :
    IsReduced (UntruncatedRing R n mu) := by
  apply (Ideal.isRadical_iff_quotient_reduced (untruncatedIdeal R n mu)).mp
  have he : (untruncatedIdeal R n mu).radical = untruncatedIdeal R n mu := by
    rw [untruncatedIdeal_radical_eq_coordinate_intersection hn,
      untruncatedIdeal_eq_componentIntersection hn, springerComponentIntersection]
    apply iInf_congr
    intro A
    exact (blockSpringerIdeal_eq_coordinate_of_one_row A.val A.property hrow).symm
  exact le_of_eq he

private theorem filling_supported_exponent_is_standard
    (U : ↥mu.cells ↪ Fin n) (hU : ColumnDescending (μ := mu) U)
    (c0 : ↥mu.cells) (hc0row : c0.val.1 = 1) :
    squarefreeSupportExponent (insert (U c0) (fillingLabels U)ᶜ) ∈
      UntruncatedStaircaseExponents n mu := by
  apply (mem_untruncatedStaircaseExponents_iff (n := n) (μ := mu) _).mpr
  change ∃ V : ↥mu.cells ↪ Fin n, ColumnDescending V ∧
    ∀ c : ↥mu.cells,
      squarefreeSupportExponent (insert (U c0) (fillingLabels U)ᶜ) (V c) ≤ c.val.1
  refine ⟨U, hU, ?_⟩
  intro c
  rw [squarefreeSupportExponent_apply]
  by_cases hc : U c ∈ insert (U c0) (fillingLabels U)ᶜ
  · rw [if_pos hc]
    have hmem : U c ∈ fillingLabels U := (mem_fillingLabels_iff U _).mpr ⟨c, rfl⟩
    have heq : U c = U c0 := by
      rcases mem_insert.mp hc with heq | hout
      · exact heq
      · exact (mem_compl.mp hout hmem).elim
    have hcell : c = c0 := U.injective heq
    subst c
    exact hc0row.symm.le
  · rw [if_neg hc]
    exact Nat.zero_le _

private theorem filling_support_meets_block
    (U : ↥mu.cells ↪ Fin n) (c0 : ↥mu.cells)
    (B : SpringerCoordinateBlocks n mu) :
    ∃ i, i ∈ B.val ∧ i ∈ insert (U c0) (fillingLabels U)ᶜ := by
  let A := fillingLabels U
  have hi0 : U c0 ∈ A := (mem_fillingLabels_iff U _).mpr ⟨c0, rfl⟩
  have hA : A.card = mu.card := by
    simp only [A, fillingLabels, card_map, card_univ, Fintype.card_coe, YoungDiagram.card]
  by_contra hnoint
  have hsub : B.val ⊆ A.erase (U c0) := by
    intro i hiB
    have hiS : i ∉ insert (U c0) Aᶜ := fun hh => hnoint ⟨i, hiB, hh⟩
    apply mem_erase.mpr
    constructor
    · intro he
      subst i
      exact hiS (mem_insert_self _ _)
    · by_contra hiA
      exact hiS (mem_insert_of_mem (mem_compl.mpr hiA))
  have hc := card_le_card hsub
  rw [card_erase_of_mem hi0, hA, B.property] at hc
  have hp : 0 < mu.card := by rw [← hA]; exact card_pos.mpr ⟨U c0, hi0⟩
  omega

private theorem quotient_exists_nonzero_nilpotent_of_radical
    {A : Type*} [CommRing A] (I : Ideal A) (p : A)
    (hp : Ideal.Quotient.mk I p ≠ 0) (hrad : p ∈ I.radical) :
    ∃ x : A ⧸ I, x ≠ 0 ∧ IsNilpotent x := by
  obtain ⟨N, hN⟩ := Ideal.mem_radical_iff.mp hrad
  refine ⟨Ideal.Quotient.mk I p, hp, N, ?_⟩
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hN

private theorem exists_nonzero_nilpotent_of_filling [IsDomain R]
    (hn : mu.card ≤ n) (U : ↥mu.cells ↪ Fin n) (hU : ColumnDescending (μ := mu) U)
    (c0 : ↥mu.cells) (hc0row : c0.val.1 = 1) :
    ∃ x : UntruncatedRing R n mu, x ≠ 0 ∧ IsNilpotent x := by
  let S := insert (U c0) (fillingLabels U)ᶜ
  let a := squarefreeSupportExponent S
  have ha : a ∈ UntruncatedStaircaseExponents n mu :=
    filling_supported_exponent_is_standard (n := n) (mu := mu) U hU c0 hc0row
  let p : PolynomialRing n R := MvPolynomial.monomial a 1
  have hLI : LinearIndependent R
      (fun c : UntruncatedStaircaseExponents n mu =>
        Ideal.Quotient.mk (untruncatedIdeal R n mu) (MvPolynomial.monomial c.val (1 : R))) :=
    untruncated_staircase_monomials_linearIndependent (R := R) (n := n) (μ := mu)
  have hp : Ideal.Quotient.mk (untruncatedIdeal R n mu) p ≠ 0 :=
    hLI.ne_zero (⟨a, ha⟩ : UntruncatedStaircaseExponents n mu)
  have hrad : p ∈ (untruncatedIdeal R n mu).radical := by
    rw [untruncatedIdeal_radical_eq_coordinate_intersection (R := R) hn]
    apply Ideal.mem_iInf.mpr
    intro B
    obtain ⟨i, hiB, hiS⟩ := filling_support_meets_block U c0 B
    change MvPolynomial.monomial (squarefreeSupportExponent S) 1 ∈ coordinateIdeal R B.val
    rw [monomial_squarefreeSupportExponent]
    exact (coordinateIdeal R B.val).prod_mem hiS (Ideal.subset_span ⟨i, hiB, rfl⟩)
  exact quotient_exists_nonzero_nilpotent_of_radical (untruncatedIdeal R n mu) p hp hrad

/-- An explicit nonzero nilpotent in every multi-row untruncated algebra.
The assertion includes all ambient dimensions in the paper's range. -/
theorem exists_nonzero_nilpotent_untruncated [IsDomain R]
    (hn : mu.card ≤ n) (hrow : 1 < mu.colLen 0) :
    ∃ x : UntruncatedRing R n mu, x ≠ 0 ∧ IsNilpotent x := by
  exact exists_nonzero_nilpotent_of_filling hn (descendingStandardFilling hn)
    (descendingStandardFilling_columnDescending hn)
    ⟨(1, 0), YoungDiagram.mem_iff_lt_colLen.mpr hrow⟩ rfl

/-- The first assertion of Corollary 7.4, for every coefficient field (and
in fact every coefficient domain), including the empty partition. -/
theorem untruncated_isReduced_iff [IsDomain R] (hn : mu.card ≤ n) :
    IsReduced (UntruncatedRing R n mu) ↔ mu.colLen 0 ≤ 1 := by
  constructor
  · intro hred
    letI := hred
    by_contra hrow
    obtain ⟨x, hx, hnil⟩ := exists_nonzero_nilpotent_untruncated
      (R := R) hn (Nat.lt_of_not_ge hrow)
    exact hx hnil.eq_zero
  · exact untruncated_isReduced_of_one_row hn

 theorem springer_isReduced_iff [IsDomain R] :
    IsReduced (SpringerRing R mu) ↔ mu.colLen 0 ≤ 1 :=
  untruncated_isReduced_iff le_rfl

end HigherSpecht
end
end CanonicalSource36

section CanonicalSource37
/- Source: HigherSpecht/SpringerTensorReducedness.lean -/



/-!
# Reducedness of the actual finite Springer tensor factors

Every factor embeds by a map with an explicit augmentation retraction.
A one-row factor is identified with its coefficient ring by its actual
augmentation. No dimension or geometric reducedness premise is used.
-/

noncomputable section

open TauCeti MvPolynomial Finset
open scoped Classical BigOperators TensorProduct

namespace HigherSpecht

variable {R : Type*} [CommRing R]

 theorem springer_X_mem_of_one_row (mu : YoungDiagram) (hrow : mu.colLen 0 ≤ 1)
    (i : Fin mu.card) :
    (MvPolynomial.X i : PolynomialRing mu.card R) ∈ springerIdeal R mu := by
  have h := blockSpringerIdeal_eq_coordinate_of_one_row
    (R := R) (Finset.univ : Finset (Fin mu.card)) (by simp) hrow
  rw [blockSpringerIdeal_univ mu le_rfl] at h
  change (MvPolynomial.X i : PolynomialRing mu.card R) ∈
    untruncatedIdeal R mu.card mu
  rw [h]
  exact Ideal.subset_span ⟨i, Finset.mem_univ i, rfl⟩

/-- For a one-row or empty shape, augmentation and coefficient inclusion
are mutually inverse on the literal Springer quotient. -/
def springerOneRowEquiv (mu : YoungDiagram) (hrow : mu.colLen 0 ≤ 1) :
    SpringerRing R mu ≃ₐ[R] R :=
  AlgEquiv.ofAlgHom (springerAugmentation mu)
    (Algebra.ofId R (SpringerRing R mu))
    (by ext)
    (by
      apply Ideal.Quotient.algHom_ext
      ext i
      have hi : Ideal.Quotient.mk (springerIdeal R mu) (MvPolynomial.X i) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (springer_X_mem_of_one_row mu hrow i)
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
        springerAugmentation_mk, MvPolynomial.constantCoeff_X, map_zero,
        AlgHom.id_apply, hi])

 theorem springer_algebraMap_augmentation_of_one_row
    (mu : YoungDiagram) (hrow : mu.colLen 0 ≤ 1) (x : SpringerRing R mu) :
    algebraMap R (SpringerRing R mu) (springerAugmentation mu x) = x :=
  (springerOneRowEquiv mu hrow).symm_apply_apply x

variable {ι : Type*} [Fintype ι]

/-- Keep one factor and augment every other factor. -/
def springerTensorFactorMap (mu : ι → YoungDiagram) (i j : ι) :
    SpringerRing R (mu j) →ₐ[R] SpringerRing R (mu i) :=
  if h : j = i then by subst j; exact AlgHom.id R _
  else (Algebra.ofId R (SpringerRing R (mu i))).comp (springerAugmentation (mu j))

@[simp] theorem springerTensorFactorMap_self (mu : ι → YoungDiagram) (i : ι) :
    springerTensorFactorMap (R := R) mu i i = AlgHom.id R _ := by
  simp [springerTensorFactorMap]

 def springerTensorRetraction (mu : ι → YoungDiagram) (i : ι) :
    (⨂[R] j, SpringerRing R (mu j)) →ₐ[R] SpringerRing R (mu i) :=
  piTensorAlgLift (springerTensorFactorMap mu i)

@[simp] theorem springerTensorRetraction_single
    (mu : ι → YoungDiagram) (i : ι) (x : SpringerRing R (mu i)) :
    springerTensorRetraction mu i (PiTensorProduct.singleAlgHom i x) = x := by
  simp only [springerTensorRetraction, piTensorAlgLift_single,
    springerTensorFactorMap_self, AlgHom.id_apply]

 theorem springerTensor_single_injective (mu : ι → YoungDiagram) (i : ι) :
    Function.Injective (PiTensorProduct.singleAlgHom (R := R)
      (A := fun j => SpringerRing R (mu j)) i) :=
  by
    intro x y h
    have he := congrArg (springerTensorRetraction (R := R) mu i) h
    exact (springerTensorRetraction_single (R := R) mu i x).symm.trans
      (he.trans (springerTensorRetraction_single (R := R) mu i y))

/-- If every factor is a row, the finite tensor product is the coefficient
ring, including the tensor product over an empty index type. -/
def springerTensorOneRowEquiv (mu : ι → YoungDiagram)
    (hrow : ∀ i, (mu i).colLen 0 ≤ 1) :
    (⨂[R] i, SpringerRing R (mu i)) ≃ₐ[R] R :=
  AlgEquiv.ofAlgHom (piTensorAlgLift fun i => springerAugmentation (mu i))
    (Algebra.ofId R (⨂[R] i, SpringerRing R (mu i)))
    (by ext)
    (by
      apply PiTensorProduct.algHom_ext
      intro i
      ext x
      simp only [AlgHom.comp_apply, piTensorAlgLift_single,
        Algebra.ofId_apply, AlgHom.id_apply]
      rw [← (PiTensorProduct.singleAlgHom (R := R)
        (A := fun j => SpringerRing R (mu j)) i).commutes,
        springer_algebraMap_augmentation_of_one_row (mu i) (hrow i)])

/-- Exact reducedness criterion for the tensor factor in every split fiber. -/
theorem springerTensor_isReduced_iff [IsDomain R] (mu : ι → YoungDiagram) :
    IsReduced (⨂[R] i, SpringerRing R (mu i)) ↔
      ∀ i, (mu i).colLen 0 ≤ 1 := by
  constructor
  · intro h i
    letI := h
    have hi : IsReduced (SpringerRing R (mu i)) :=
      isReduced_of_injective (PiTensorProduct.singleAlgHom (R := R)
        (A := fun j => SpringerRing R (mu j)) i) (springerTensor_single_injective mu i)
    exact springer_isReduced_iff.mp hi
  · intro hrow
    exact isReduced_of_injective (springerTensorOneRowEquiv (R := R) mu hrow)
      (springerTensorOneRowEquiv mu hrow).injective

/-- A nonempty product of the same ring is reduced exactly when the ring is. -/
theorem isReduced_pi_const_iff {J S : Type*} [Nonempty J] [CommRing S] :
    IsReduced (J → S) ↔ IsReduced S := by
  constructor
  · intro h
    letI := h
    exact isReduced_of_injective (RingHom.pi fun _ : J => RingHom.id S)
      (fun x y hxy => congrFun hxy (Classical.choice ‹Nonempty J›))
  · intro h
    letI := h
    infer_instance

 theorem isReduced_iff_of_algEquiv {A B : Type*} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (E : A ≃ₐ[R] B) : IsReduced A ↔ IsReduced B :=
  ⟨fun h => by
      letI := h
      exact isReduced_of_injective E.symm E.symm.injective,
    fun h => by
      letI := h
      exact isReduced_of_injective E E.injective⟩

end HigherSpecht
end
end CanonicalSource37

section CanonicalSource38
/- Source: HigherSpecht/SplitFiberReducedness.lean -/



/-!
# Reducedness and etaleness of the actual parameter fibers

The displayed root factorization determines the literal tensor factors.
Their augmentation retractions detect nilpotents, while the reduced case
is explicitly a product of coefficient fields. The algebraic-closure
statement uses actual scalar extension of the defining quotient.
-/

noncomputable section

open TauCeti Polynomial Finset
open scoped Classical BigOperators TensorProduct

namespace HigherSpecht

variable {K : Type*} [Field K] {n m : ℕ} {ι : Type*} [Fintype ι]

 theorem prescribedRootAssignments_nonempty (r : ι → ℕ)
    (hsum : (∑ i, r i) = n) : Nonempty (PrescribedRootAssignments n r) := by
  apply Fintype.card_pos_iff.mp
  rw [card_prescribedRootAssignments r hsum, ← hsum]
  exact Nat.multinomial_pos Finset.univ r

 theorem split_fiber_assignment_nonempty (lam : YoungDiagram) (a : Fin m → K)
    (hsize : lam.card + m = n) (r0 : ℕ) (c : ι → K) (r : ι → ℕ)
    (hfactor : parameterPolynomial a = splitRootParameter r0 c r) :
    Nonempty (PrescribedRootAssignments n (splitRootMultiplicities lam r0 r)) := by
  have hdeg := congrArg Polynomial.natDegree hfactor
  rw [parameterPolynomial_natDegree, splitRootParameter_natDegree] at hdeg
  apply prescribedRootAssignments_nonempty
  simpa only [splitRootMultiplicities, Fintype.sum_option,
    Option.elim_none, Option.elim_some, add_assoc, ← hdeg] using hsize

 theorem split_root_shape_one_row_iff (lam : YoungDiagram) (r0 : ℕ)
    (r : ι → ℕ) (hr : ∀ i, 0 < r i) :
    (∀ i : Option ι,
      (i.elim (adjoinOnes lam r0) (fun j => columnPartition (r j))).colLen 0 ≤ 1) ↔
      lam.colLen 0 + r0 ≤ 1 ∧ ∀ i, r i = 1 := by
  constructor
  · intro h
    refine ⟨by simpa using h none, fun i => ?_⟩
    have hi := h (some i)
    simp only [Option.elim_some, columnPartition, adjoinOnes_colLen_zero,
      YoungDiagram.colLen_bot, zero_add] at hi
    exact le_antisymm hi (hr i)
  · rintro ⟨h0, h⟩ (_ | i)
    · simpa only [Option.elim_none, adjoinOnes_colLen_zero] using h0
    · simp [columnPartition, h i]

/-- The exact split parameter-fiber reducedness criterion, in arbitrary
characteristic and including the empty partition and constant polynomial. -/
theorem parameterFiber_isReduced_iff
    (lam : YoungDiagram) (a : Fin m → K) (hsize : lam.card + m = n)
    (r0 : ℕ) (c : ι → K) (hc : Function.Injective c) (hcz : ∀ i, c i ≠ 0)
    (r : ι → ℕ) (hr : ∀ i, 0 < r i)
    (hfactor : parameterPolynomial a = splitRootParameter r0 c r) :
    IsReduced (ParameterFiber K n lam m a) ↔
      lam.colLen 0 + r0 ≤ 1 ∧ ∀ i, r i = 1 := by
  letI := split_fiber_assignment_nonempty lam a hsize r0 c r hfactor
  rw [isReduced_iff_of_algEquiv (R := K)
      (A := ParameterFiber K n lam m a)
      (B := PrescribedRootAssignments n (splitRootMultiplicities lam r0 r) →
        ⨂[K] i : Option ι,
          SpringerRing K (i.elim (adjoinOnes lam r0) (fun j => columnPartition (r j))))
      (theorem_7_1_parameter_fiber K lam a hsize r0 c hc hcz r hr hfactor),
    isReduced_pi_const_iff
      (J := PrescribedRootAssignments n (splitRootMultiplicities lam r0 r))
      (S := ⨂[K] i : Option ι,
        SpringerRing K (i.elim (adjoinOnes lam r0) (fun j => columnPartition (r j)))),
    springerTensor_isReduced_iff (R := K)
      (fun i : Option ι => i.elim (adjoinOnes lam r0) (fun j => columnPartition (r j))),
    split_root_shape_one_row_iff lam r0 r hr]

/-- In the reduced case, all tensor factors collapse through their actual
augmentation maps, giving a product of copies of the coefficient field. -/
def parameterFiberReducedEquiv
    (lam : YoungDiagram) (a : Fin m → K) (hsize : lam.card + m = n)
    (r0 : ℕ) (c : ι → K) (hc : Function.Injective c) (hcz : ∀ i, c i ≠ 0)
    (r : ι → ℕ) (hr : ∀ i, 0 < r i)
    (hfactor : parameterPolynomial a = splitRootParameter r0 c r)
    (hrow : lam.colLen 0 + r0 ≤ 1) (hmult : ∀ i, r i = 1) :
    ParameterFiber K n lam m a ≃ₐ[K]
      (PrescribedRootAssignments n (splitRootMultiplicities lam r0 r) → K) :=
  (theorem_7_1_parameter_fiber K lam a hsize r0 c hc hcz r hr hfactor).trans
    (AlgEquiv.piCongrRight fun _ => springerTensorOneRowEquiv
      (fun i : Option ι => i.elim (adjoinOnes lam r0) (fun j => columnPartition (r j)))
      ((split_root_shape_one_row_iff lam r0 r hr).mpr ⟨hrow, hmult⟩))

/-- The split fiber is etale exactly under the same root-multiplicity
condition. This direction requires no perfection assumption on the field. -/
theorem parameterFiber_etale_iff
    (lam : YoungDiagram) (a : Fin m → K) (hsize : lam.card + m = n)
    (r0 : ℕ) (c : ι → K) (hc : Function.Injective c) (hcz : ∀ i, c i ≠ 0)
    (r : ι → ℕ) (hr : ∀ i, 0 < r i)
    (hfactor : parameterPolynomial a = splitRootParameter r0 c r) :
    Algebra.Etale K (ParameterFiber K n lam m a) ↔
      lam.colLen 0 + r0 ≤ 1 ∧ ∀ i, r i = 1 := by
  constructor
  · intro h
    letI := h
    exact (parameterFiber_isReduced_iff lam a hsize r0 c hc hcz r hr hfactor).mp
      (Algebra.FormallyUnramified.isReduced_of_field K _)
  · rintro ⟨h0, hm⟩
    exact Algebra.Etale.of_equiv
      (parameterFiberReducedEquiv lam a hsize r0 c hc hcz r hr hfactor h0 hm).symm

/-- Corollary 7.4's geometric fiber assertion. The roots and multiplicities
are those of the parameter polynomial over the actual algebraic closure. -/
theorem parameterFiber_geometricallyReduced_iff
    (lam : YoungDiagram) (a : Fin m → K) (hsize : lam.card + m = n)
    (r0 : ℕ) (c : ι → AlgebraicClosure K)
    (hc : Function.Injective c) (hcz : ∀ i, c i ≠ 0)
    (r : ι → ℕ) (hr : ∀ i, 0 < r i)
    (hfactor : parameterPolynomial (fun i => algebraMap K (AlgebraicClosure K) (a i)) =
      splitRootParameter r0 c r) :
    Algebra.IsGeometricallyReduced K (ParameterFiber K n lam m a) ↔
      lam.colLen 0 + r0 ≤ 1 ∧ ∀ i, r i = 1 := by
  rw [Algebra.isGeometricallyReduced_field_iff,
    isReduced_iff_of_algEquiv (R := AlgebraicClosure K)
      (A := AlgebraicClosure K ⊗[K] ParameterFiber K n lam m a)
      (B := ParameterFiber (AlgebraicClosure K) n lam m
        (fun i => algebraMap K (AlgebraicClosure K) (a i)))
      (parameterFiberBaseChangeEquiv (S := AlgebraicClosure K) n lam m a)]
  exact parameterFiber_isReduced_iff lam _ hsize r0 c hc hcz r hr hfactor

end HigherSpecht
end
end CanonicalSource38

section CanonicalSource39
/- Source: HigherSpecht/ParameterRootConditions.lean -/



/-!
# The squarefree and nonzero-constant conditions on parameter polynomials

Squarefree is checked after algebraic closure, so it means distinct geometric
roots even over imperfect coefficient fields. Separability gives the same
condition over the original field. The empty parameter tuple is included.
-/

noncomputable section

open TauCeti Polynomial Finset
open scoped Classical BigOperators TensorProduct

namespace HigherSpecht

variable {K : Type*} [Field K] {n m : ℕ} {ι : Type*} [Fintype ι]

 theorem map_parameterPolynomial {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (a : Fin m → R) :
    (parameterPolynomial a).map phi = parameterPolynomial (fun i => phi (a i)) := by
  simp only [parameterPolynomial, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_neg, Polynomial.map_one,
    map_mul, map_pow, map_neg, map_one]

 theorem splitRootParameter_eval_zero_ne_zero_iff (r0 : ℕ) (c : ι → K)
    (hcz : ∀ i, c i ≠ 0) (r : ι → ℕ) :
    (splitRootParameter r0 c r).eval 0 ≠ 0 ↔ r0 = 0 := by
  have hprod : (∏ i, (-c i) ^ r i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (neg_ne_zero.mpr (hcz i)))
  simp only [splitRootParameter, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_C,
    zero_sub, ne_eq, mul_eq_zero, not_or]
  constructor
  · rintro ⟨h0, _⟩
    by_contra hr0
    exact h0 (zero_pow hr0)
  · rintro rfl
    exact ⟨by simp, hprod⟩

 theorem splitRootValue_injective (c : ι → K) (hc : Function.Injective c)
    (hcz : ∀ i, c i ≠ 0) : Function.Injective (splitRootValue c) := by
  intro i j h
  by_contra hij
  have hu := splitRootValue_unitDifferences c
    (fun i => isUnit_iff_ne_zero.mpr (hcz i))
    (fun i j hij => isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (hc.ne hij))) hij
  change IsUnit (splitRootValue c i - splitRootValue c j) at hu
  rw [h, sub_self] at hu
  exact not_isUnit_zero hu

/-- Separability of the displayed split polynomial is exactly the
multiplicity-one condition, including zero and constant polynomials. -/
theorem splitRootParameter_separable_iff (r0 : ℕ) (c : ι → K)
    (hc : Function.Injective c) (hcz : ∀ i, c i ≠ 0)
    (r : ι → ℕ) (hr : ∀ i, 0 < r i) :
    (splitRootParameter r0 c r).Separable ↔ r0 ≤ 1 ∧ ∀ i, r i = 1 := by
  constructor
  · intro h
    have h0 : (Polynomial.X ^ r0 : K[X]).Separable := h.of_mul_left
    have h0le : r0 ≤ 1 := by
      by_cases hz : r0 = 0
      · omega
      · have hX : ¬IsUnit (Polynomial.X : K[X]) := by
          simpa using Polynomial.not_isUnit_X_sub_C (0 : K)
        have h1 := (Polynomial.Separable.of_pow hX hz h0).2
        omega
    refine ⟨h0le, fun i => ?_⟩
    have hi : ((Polynomial.X - Polynomial.C (c i)) ^ r i).Separable :=
      h.of_mul_right.of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
    exact (Polynomial.Separable.of_pow (Polynomial.not_isUnit_X_sub_C (c i))
      (Nat.ne_of_gt (hr i)) hi).2
  · rintro ⟨h0, hm⟩
    have hprod : (∏ i, (Polynomial.X - Polynomial.C (c i))).Separable :=
      Polynomial.separable_prod_X_sub_C_iff.mpr hc
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h0 with h0 | h0
    · simpa only [splitRootParameter, h0, hm, pow_zero, pow_one, one_mul] using hprod
    · have hh := Polynomial.separable_prod_X_sub_C_iff.mpr
        (splitRootValue_injective c hc hcz)
      simpa only [splitRootParameter, Fintype.prod_option, splitRootValue,
        Option.elim_none, Option.elim_some, map_zero, sub_zero, h0, hm, pow_one] using hh

/-- Etaleness of a parameter fiber descends from its literal algebraic
closure tensor product. No ordinary-reducedness claim is made over an
imperfect field. -/
theorem parameterFiber_etale_iff_geometric_root_condition
    (lam : YoungDiagram) (a : Fin m → K) (hsize : lam.card + m = n)
    (r0 : ℕ) (c : ι → AlgebraicClosure K)
    (hc : Function.Injective c) (hcz : ∀ i, c i ≠ 0)
    (r : ι → ℕ) (hr : ∀ i, 0 < r i)
    (hfactor : parameterPolynomial (fun i => algebraMap K (AlgebraicClosure K) (a i)) =
      splitRootParameter r0 c r) :
    Algebra.Etale K (ParameterFiber K n lam m a) ↔
      lam.colLen 0 + r0 ≤ 1 ∧ ∀ i, r i = 1 := by
  let E := parameterFiberBaseChangeEquiv (S := AlgebraicClosure K) n lam m a
  constructor
  · intro h
    letI := h
    letI : Algebra.Etale (AlgebraicClosure K)
        (ParameterFiber (AlgebraicClosure K) n lam m
          (fun i => algebraMap K (AlgebraicClosure K) (a i))) :=
      Algebra.Etale.of_equiv
        (R := AlgebraicClosure K)
        (A := AlgebraicClosure K ⊗[K] ParameterFiber K n lam m a)
        (B := ParameterFiber (AlgebraicClosure K) n lam m
          (fun i => algebraMap K (AlgebraicClosure K) (a i))) E
    exact (parameterFiber_etale_iff lam _ hsize r0 c hc hcz r hr hfactor).mp inferInstance
  · intro h
    letI := (parameterFiber_etale_iff lam _ hsize r0 c hc hcz r hr hfactor).mpr h
    letI : Algebra.Etale (AlgebraicClosure K)
        (AlgebraicClosure K ⊗[K] ParameterFiber K n lam m a) :=
      Algebra.Etale.of_equiv
        (R := AlgebraicClosure K)
        (A := ParameterFiber (AlgebraicClosure K) n lam m
          (fun i => algebraMap K (AlgebraicClosure K) (a i)))
        (B := AlgebraicClosure K ⊗[K] ParameterFiber K n lam m a) E.symm
    exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat (AlgebraicClosure K)

/-- Exact polynomial form of the geometric criterion. The optional
nonzero-constant condition is present exactly for a nonempty shape. -/
theorem parameterFiber_etale_polynomial_iff
    (lam : YoungDiagram) (a : Fin m → K) (hsize : lam.card + m = n)
    (r0 : ℕ) (c : ι → AlgebraicClosure K)
    (hc : Function.Injective c) (hcz : ∀ i, c i ≠ 0)
    (r : ι → ℕ) (hr : ∀ i, 0 < r i)
    (hfactor : parameterPolynomial (fun i => algebraMap K (AlgebraicClosure K) (a i)) =
      splitRootParameter r0 c r) :
    Algebra.Etale K (ParameterFiber K n lam m a) ↔
      lam.colLen 0 ≤ 1 ∧ (parameterPolynomial a).Separable ∧
        (lam.colLen 0 ≠ 0 → (parameterPolynomial a).eval 0 ≠ 0) := by
  rw [parameterFiber_etale_iff_geometric_root_condition lam a hsize r0 c hc hcz r hr hfactor]
  have hsep : (parameterPolynomial a).Separable ↔ r0 ≤ 1 ∧ ∀ i, r i = 1 := by
    rw [← Polynomial.separable_map (algebraMap K (AlgebraicClosure K)),
      map_parameterPolynomial, hfactor, splitRootParameter_separable_iff r0 c hc hcz r hr]
  have hzero : (parameterPolynomial a).eval 0 ≠ 0 ↔ r0 = 0 := by
    have heval : (splitRootParameter r0 c r).eval 0 =
        algebraMap K (AlgebraicClosure K) ((parameterPolynomial a).eval 0) := by
      rw [← hfactor, ← map_parameterPolynomial]
      simpa only [map_zero] using
        (Polynomial.eval_map_apply (algebraMap K (AlgebraicClosure K))
          (p := parameterPolynomial a) (0 : K))
    have hz : algebraMap K (AlgebraicClosure K) ((parameterPolynomial a).eval 0) ≠ 0 ↔
        (parameterPolynomial a).eval 0 ≠ 0 := by
      constructor
      · intro h h0
        exact h (by rw [h0, map_zero])
      · intro h h0
        apply h
        apply RingHom.injective (algebraMap K (AlgebraicClosure K))
        simpa only [map_zero] using h0
    rw [← hz, ← heval, splitRootParameter_eval_zero_ne_zero_iff r0 c hcz r]
  rw [hsep, hzero]
  constructor
  · rintro ⟨h0, hm⟩
    exact ⟨by omega, ⟨by omega, hm⟩, fun h => by omega⟩
  · rintro ⟨h0, ⟨hr0, hm⟩, hz⟩
    refine ⟨?_, hm⟩
    by_cases h : lam.colLen 0 = 0
    · omega
    · have := hz h
      omega

end HigherSpecht
end
end CanonicalSource39

section CanonicalSource40
/- Source: HigherSpecht/CanonicalRootFactorization.lean -/



/-!
# Canonical geometric root factorization

Every monic polynomial over an algebraically closed field is factored using
its actual root multiset. The nonzero-root index is the finite set of its
distinct nonzero roots, and multiplicities are actual multiset counts.
This removes every displayed-factorization premise from the fiber criterion.
-/

noncomputable section

open TauCeti Polynomial Finset
open scoped Classical BigOperators

namespace HigherSpecht

variable {K : Type*} [Field K] {n m : ℕ}

/-- The actual parameter-fiber etale criterion, with no root factorization
premise. Separability is equivalent to squarefreeness after algebraic closure. -/
theorem parameterFiber_etale_iff_polynomial
    (lam : YoungDiagram) (a : Fin m → K) (hsize : lam.card + m = n) :
    Algebra.Etale K (ParameterFiber K n lam m a) ↔
      lam.colLen 0 ≤ 1 ∧ (parameterPolynomial a).Separable ∧
        (lam.colLen 0 ≠ 0 → (parameterPolynomial a).eval 0 ≠ 0) := by
  let Q := parameterPolynomial (fun i => algebraMap K (AlgebraicClosure K) (a i))
  exact parameterFiber_etale_polynomial_iff lam a hsize (Q.roots.count 0)
    (canonicalNonzeroRoot Q) (canonicalNonzeroRoot_injective Q)
    (canonicalNonzeroRoot_ne_zero Q) (canonicalRootMultiplicity Q)
    (canonicalRootMultiplicity_pos Q) (canonical_splitRootParameter Q (parameterPolynomial_monic _))

/-- The complete geometric reducedness criterion without a chosen splitting
or multiplicity hypothesis, for every coefficient field. -/
theorem parameterFiber_geometricallyReduced_iff_polynomial
    (lam : YoungDiagram) (a : Fin m → K) (hsize : lam.card + m = n) :
    Algebra.IsGeometricallyReduced K (ParameterFiber K n lam m a) ↔
      lam.colLen 0 ≤ 1 ∧ (parameterPolynomial a).Separable ∧
        (lam.colLen 0 ≠ 0 → (parameterPolynomial a).eval 0 ≠ 0) := by
  let Q := parameterPolynomial (fun i => algebraMap K (AlgebraicClosure K) (a i))
  rw [← parameterFiber_etale_iff_polynomial lam a hsize]
  exact (parameterFiber_geometricallyReduced_iff lam a hsize (Q.roots.count 0)
    (canonicalNonzeroRoot Q) (canonicalNonzeroRoot_injective Q)
    (canonicalNonzeroRoot_ne_zero Q) (canonicalRootMultiplicity Q)
    (canonicalRootMultiplicity_pos Q) (canonical_splitRootParameter Q (parameterPolynomial_monic _))).trans
      (parameterFiber_etale_iff_geometric_root_condition lam a hsize (Q.roots.count 0)
        (canonicalNonzeroRoot Q) (canonicalNonzeroRoot_injective Q)
        (canonicalNonzeroRoot_ne_zero Q) (canonicalRootMultiplicity Q)
        (canonicalRootMultiplicity_pos Q)
        (canonical_splitRootParameter Q (parameterPolynomial_monic _))).symm

 theorem parameterPolynomial_separable_iff_geometric_squarefree (a : Fin m → K) :
    (parameterPolynomial a).Separable ↔
      Squarefree ((parameterPolynomial a).map (algebraMap K (AlgebraicClosure K))) := by
  rw [← PerfectField.separable_iff_squarefree,
    Polynomial.separable_map (algebraMap K (AlgebraicClosure K))]

/-- The manuscript's squarefree formulation refers to geometric roots;
this is its exact algebraic-closure polynomial statement. -/
theorem parameterFiber_geometricallyReduced_iff_squarefree
    (lam : YoungDiagram) (a : Fin m → K) (hsize : lam.card + m = n) :
    Algebra.IsGeometricallyReduced K (ParameterFiber K n lam m a) ↔
      lam.colLen 0 ≤ 1 ∧
        Squarefree ((parameterPolynomial a).map (algebraMap K (AlgebraicClosure K))) ∧
        (lam.colLen 0 ≠ 0 → (parameterPolynomial a).eval 0 ≠ 0) := by
  rw [parameterFiber_geometricallyReduced_iff_polynomial lam a hsize,
    parameterPolynomial_separable_iff_geometric_squarefree]

end HigherSpecht
end
end CanonicalSource40

section CanonicalSource41
/- Source: HigherSpecht/FiniteFreeEtaleFiber.lean -/



/-! The base-local etale criterion for an actual finite free algebra follows
from the discriminant and residue-field maps. -/

noncomputable section
open scoped TensorProduct

namespace HigherSpecht

variable {A B J : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [Fintype J] [DecidableEq J]

/-- A finite free algebra is etale over the localization of its base at p
exactly when its actual residue-field fiber is etale. -/
theorem finiteFree_etale_atPrime_iff_residueFiber
    (b : Module.Basis J A B) (p : Ideal A) [p.IsPrime] :
    Algebra.Etale (Localization.AtPrime p) (Localization.AtPrime p ⊗[A] B) ↔
      Algebra.Etale p.ResidueField (p.ResidueField ⊗[A] B) := by
  rw [← TauCeti.Algebra.isUnit_discr_localization_iff b p,
    IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p) p,
    ← TauCeti.Algebra.algebraMap_discr_ne_zero_iff_etale_baseChange b p.ResidueField]
  change Algebra.discr A b ∉ p ↔ algebraMap A p.ResidueField (Algebra.discr A b) ≠ 0
  exact not_congr Ideal.algebraMap_residueField_eq_zero.symm

end HigherSpecht
end
end CanonicalSource41

section CanonicalSource42
/- Source: HigherSpecht/ParameterEtaleLocus.lean -/



/-!
# The etale locus on the actual elementary-parameter base

The criterion below is first stated for a supplied finite basis; the final
principal wrapper instantiates the independently constructed integral basis.
The conclusion concerns the actual base localization and actual algebra,
not a set defined by the desired polynomial condition.
-/

noncomputable section

open TauCeti MvPolynomial
open scoped Classical TensorProduct

namespace HigherSpecht

variable {K : Type*} [Field K] {n : ℕ} {lam : YoungDiagram}

 theorem etale_iff_of_algEquiv {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (E : A ≃ₐ[R] B) :
    Algebra.Etale R A ↔ Algebra.Etale R B :=
  ⟨fun h => by letI := h; exact Algebra.Etale.of_equiv E,
    fun h => by letI := h; exact Algebra.Etale.of_equiv E.symm⟩

/-- The exact base-local etale criterion before instantiating the actual
finite parameter basis. All primes, including nonclosed points, occur. -/
theorem parameter_etale_atPrime_iff_polynomial_of_basis
    (hn : lam.card ≤ n) {J : Type*} [Fintype J] [DecidableEq J]
    (b : Module.Basis J (ElementaryParameterRing K n lam) (UntruncatedRing K n lam))
    (p : Ideal (ElementaryParameterRing K n lam)) [p.IsPrime] :
    Algebra.Etale (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[ElementaryParameterRing K n lam] UntruncatedRing K n lam) ↔
      lam.colLen 0 ≤ 1 ∧
        (parameterPolynomial (fun i =>
          algebraMap (ElementaryParameterRing K n lam) p.ResidueField (MvPolynomial.X i))).Separable ∧
        (lam.colLen 0 ≠ 0 →
          (parameterPolynomial (fun i =>
            algebraMap (ElementaryParameterRing K n lam) p.ResidueField
              (MvPolynomial.X i))).eval 0 ≠ 0) := by
  rw [finiteFree_etale_atPrime_iff_residueFiber b p,
    etale_iff_of_algEquiv (elementaryParameterBaseChangeEquiv (R := K) n lam p.ResidueField)]
  exact parameterFiber_etale_iff_polynomial lam _ (Nat.add_sub_of_le hn)

/-- The full base-local assertion of Corollary 7.4, for every prime of the
actual elementary-parameter ring.  Its finite basis is constructed from the
integral Springer monomials and is not a hypothesis of this theorem. -/
theorem parameter_etale_atPrime_iff_polynomial
    (hn : lam.card ≤ n)
    (p : Ideal (ElementaryParameterRing K n lam)) [p.IsPrime] :
    Algebra.Etale (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[ElementaryParameterRing K n lam] UntruncatedRing K n lam) ↔
      lam.colLen 0 ≤ 1 ∧
        (parameterPolynomial (fun i =>
          algebraMap (ElementaryParameterRing K n lam) p.ResidueField (MvPolynomial.X i))).Separable ∧
        (lam.colLen 0 ≠ 0 →
          (parameterPolynomial (fun i =>
            algebraMap (ElementaryParameterRing K n lam) p.ResidueField
              (MvPolynomial.X i))).eval 0 ≠ 0) := by
  letI := finite_specialFiberMonomialIndex n lam hn
  letI : Fintype (SpecialFiberMonomialIndex n lam) := Fintype.ofFinite _
  exact parameter_etale_atPrime_iff_polynomial_of_basis hn
    (untruncatedMonomialParameterBasis K n lam hn) p

end HigherSpecht
end
end CanonicalSource42

section CanonicalSource43
/- Source: TauCeti/LinearAlgebra/Graded/LinearMap.lean -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Homogeneous linear maps

This file records the degree of a linear map between modules equipped with families of graded
subobjects. A linear map has degree `q` when it maps everything in the degree-`p` piece of the
source into the degree-`p + q` piece of the target. This is a containment condition, so no
direct-sum hypothesis is imposed and a map can be homogeneous of several degrees at once. The
families are indexed by an arbitrary `SetLike` type, so the homogeneity predicate and the additive
closure lemmas cover gradings by submodules, additive subgroups and additive submonoids alike.
`LinearMap.IsHomogeneous.smul` additionally needs the target pieces to be closed under a
distributive scalar action, and `LinearMap.homogeneousSubmodule` needs them to be additive
submonoids closed under a module action, i.e. a submodule-valued grading.

The multilinear counterpart, and the degree calculus for substitution, are in
`TauCeti.LinearAlgebra.Graded.Multilinear`.

## Main definitions

* `LinearMap.IsHomogeneous`: a linear map shifts homogeneous degree by a fixed amount.
* `LinearMap.homogeneousSubmodule`: the submodule of linear maps of a fixed degree.

## Main results

* `LinearMap.IsHomogeneous.comp`: degrees add under composition of linear maps.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/


namespace TauCeti

universe uR uι uM uN uP

namespace LinearMap

section Semiring

variable {R : Type uR} {ι : Type uι} {M : Type uM} {N : Type uN} {σM : Type*} {σN : Type*}
  [Semiring R] [AddMonoid ι] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] [SetLike σM M] [SetLike σN N]

/-- A linear map is homogeneous of degree `q` if it maps the degree-`p` piece of `𝒜` into the
degree-`p + q` piece of `ℬ`. No direct-sum hypothesis on the families is needed. -/
def IsHomogeneous (f : M →ₗ[R] N) (𝒜 : ι → σM) (ℬ : ι → σN) (q : ι) : Prop :=
  ∀ ⦃p : ι⦄ ⦃x : M⦄, x ∈ 𝒜 p → f x ∈ ℬ (p + q)

/-- Homogeneity of degree `q` is exactly the mapping condition on homogeneous elements. This is a
convenient introduction rule, and `IsHomogeneous.map_mem` is the corresponding elimination rule. -/
theorem isHomogeneous_def {f : M →ₗ[R] N} {𝒜 : ι → σM} {ℬ : ι → σN} {q : ι} :
    IsHomogeneous f 𝒜 ℬ q ↔ ∀ (p : ι) (x : M), x ∈ 𝒜 p → f x ∈ ℬ (p + q) :=
  ⟨fun hf _ _ hx ↦ hf hx, fun hf _ _ hx ↦ hf _ _ hx⟩

/-- Apply a homogeneous linear map to a homogeneous element. -/
theorem IsHomogeneous.map_mem {f : M →ₗ[R] N} {𝒜 : ι → σM}
    {ℬ : ι → σN} {q p : ι} (hf : IsHomogeneous f 𝒜 ℬ q) {x : M} (hx : x ∈ 𝒜 p) :
    f x ∈ ℬ (p + q) :=
  hf hx

/-- The zero linear map is homogeneous of every degree. -/
@[simp]
theorem isHomogeneous_zero [ZeroMemClass σN N] (𝒜 : ι → σM) (ℬ : ι → σN) (q : ι) :
    IsHomogeneous (0 : M →ₗ[R] N) 𝒜 ℬ q := by
  intro p x _
  simp

/-- A sum of linear maps of the same degree has that degree. -/
@[grind ←]
theorem IsHomogeneous.add [AddMemClass σN N] {f g : M →ₗ[R] N} {𝒜 : ι → σM}
    {ℬ : ι → σN} {q : ι} (hf : IsHomogeneous f 𝒜 ℬ q) (hg : IsHomogeneous g 𝒜 ℬ q) :
    IsHomogeneous (f + g) 𝒜 ℬ q := by
  intro p x hx
  simpa using add_mem (hf hx) (hg hx)

/-- The identity linear map is homogeneous of degree zero. -/
@[simp]
theorem isHomogeneous_id (𝒜 : ι → σM) :
    IsHomogeneous (LinearMap.id : M →ₗ[R] M) 𝒜 𝒜 0 := by
  intro p x hx
  simpa using hx

/-- Degrees add under composition of linear maps. -/
@[grind →]
theorem IsHomogeneous.comp {P : Type uP} {σP : Type*} [AddCommMonoid P] [Module R P]
    [SetLike σP P] {f : M →ₗ[R] N} {g : N →ₗ[R] P} {𝒜 : ι → σM}
    {ℬ : ι → σN} {𝒞 : ι → σP} {q r : ι}
    (hg : IsHomogeneous g ℬ 𝒞 r) (hf : IsHomogeneous f 𝒜 ℬ q) :
    IsHomogeneous (g.comp f) 𝒜 𝒞 (q + r) := by
  intro p x hx
  simpa only [_root_.LinearMap.comp_apply, add_assoc] using hg (hf hx)

end Semiring

section Neg

variable {R : Type uR} {ι : Type uι} {M : Type uM} {N : Type uN} {σM : Type*} {σN : Type*}
  [Semiring R] [AddMonoid ι] [AddCommMonoid M] [AddCommGroup N]
  [Module R M] [Module R N] [SetLike σM M] [SetLike σN N]

/-- The negative of a homogeneous linear map has the same degree. -/
@[grind ←]
theorem IsHomogeneous.neg [NegMemClass σN N] {f : M →ₗ[R] N} {𝒜 : ι → σM}
    {ℬ : ι → σN} {q : ι} (hf : IsHomogeneous f 𝒜 ℬ q) :
    IsHomogeneous (-f) 𝒜 ℬ q := by
  intro p x hx
  simpa using neg_mem (hf hx)

/-- A difference of linear maps of the same degree has that degree. -/
@[grind ←]
theorem IsHomogeneous.sub [AddMemClass σN N] [NegMemClass σN N] {f g : M →ₗ[R] N}
    {𝒜 : ι → σM} {ℬ : ι → σN} {q : ι} (hf : IsHomogeneous f 𝒜 ℬ q)
    (hg : IsHomogeneous g 𝒜 ℬ q) :
    IsHomogeneous (f - g) 𝒜 ℬ q := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

end Neg

section Scalars

variable {R : Type uR} {S : Type*} {ι : Type uι} {M : Type uM} {N : Type uN}
  {σM : Type*} {σN : Type*}
  [Semiring R] [AddMonoid ι] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] [SetLike σM M] [SetLike σN N]

/-- A scalar multiple of a homogeneous linear map has the same degree. -/
@[grind ←]
theorem IsHomogeneous.smul [DistribSMul S N] [SMulCommClass R S N]
    [SMulMemClass σN S N] {f : M →ₗ[R] N} {𝒜 : ι → σM}
    {ℬ : ι → σN} {q : ι} (hf : IsHomogeneous f 𝒜 ℬ q) (s : S) :
    IsHomogeneous (s • f) 𝒜 ℬ q := by
  intro p x hx
  simpa using SMulMemClass.smul_mem s (hf hx)

/-- Linear maps of a fixed degree form a submodule over any scalar ring acting on the target. -/
def homogeneousSubmodule [Semiring S] [Module S N] [SMulCommClass R S N]
    [AddSubmonoidClass σN N] [SMulMemClass σN S N] (𝒜 : ι → σM)
    (ℬ : ι → σN) (q : ι) : Submodule S (M →ₗ[R] N) where
  carrier := {f | IsHomogeneous f 𝒜 ℬ q}
  zero_mem' := isHomogeneous_zero 𝒜 ℬ q
  add_mem' hf hg := hf.add hg
  smul_mem' s _ hf := hf.smul s

@[simp, grind =]
theorem mem_homogeneousSubmodule [Semiring S] [Module S N] [SMulCommClass R S N]
    [AddSubmonoidClass σN N] [SMulMemClass σN S N]
    {f : M →ₗ[R] N} {𝒜 : ι → σM} {ℬ : ι → σN} {q : ι} :
    f ∈ homogeneousSubmodule (S := S) 𝒜 ℬ q ↔ IsHomogeneous f 𝒜 ℬ q :=
  Iff.rfl

end Scalars

section Reindex

variable {R : Type uR} {ι : Type uι} {M : Type uM} {N : Type uN} {σM : Type*} {σN : Type*}
  [Semiring R] [AddCommMonoid ι] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] [SetLike σM M] [SetLike σN N]

/-- Translating the indices of both gradings by the same amount preserves homogeneity. -/
theorem IsHomogeneous.reindex {f : M →ₗ[R] N} {𝒜 : ι → σM} {ℬ : ι → σN} {q : ι}
    (hf : IsHomogeneous f 𝒜 ℬ q) (p : ι) :
    IsHomogeneous f (fun n ↦ 𝒜 (n + p)) (fun n ↦ ℬ (n + p)) q := fun n _ hx ↦ by
  have h := hf.map_mem hx
  rwa [add_right_comm] at h

end Reindex

end LinearMap

end TauCeti
end CanonicalSource43

section CanonicalSource44
/- Source: TauCeti/Algebra/DirectSum/Internal.lean -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Internal direct sums from explicit equivalences

This file provides reusable infrastructure for direct sums of submodules.  The generic
`DirectSum.piInclusion`, `DirectSum.piSubmodule`, and `DirectSum.piSubmoduleEquiv` declarations
describe their componentwise inclusion and range, while `DirectSum.isInternal_of_lof` gives a
criterion for proving that a family of submodules is an internal direct sum by identifying its
summands with the components of a linear equivalence.

A second group of declarations concerns maps between decompositions.
`DirectSum.map_decompose_shift` says that an additive map carrying each summand of one
decomposition into a summand of another, along an injective reindexing of the degrees, commutes
with the homogeneous projections, while `DirectSum.isInternal_comap` and
`DirectSum.Decomposition.restrict` transport a decomposition backwards along an injective linear
map whose range contains the homogeneous projections of its elements, with
`DirectSum.map_decompose_restrict` computing the projections of the restricted decomposition.

A third group is about maps compatible with a decomposition. Two linear maps agreeing on every
member of a spanning family of submodules are equal, `LinearMap.ext_of_iSup_eq_top`; for an
internal direct sum the spanning hypothesis is `DirectSum.IsInternal.submodule_iSup_eq_top`. If a
linear map carries each summand of a spanning family into the corresponding member of an
independent family, then its kernel is spanned by its homogeneous parts,
`LinearMap.ker_eq_iSup_inf_of_map_le`. Conversely, `iSupIndep.map_of_ker_inf_iSup_le` shows that a
linear map preserves independence when the part of its kernel in the span is spanned by its
intersections with the summands.

`DirectSum.IsInternal.iSup_fiber` collects an internal decomposition along the fibers of any map.

`DirectSum.IsInternal.iSup_inf_eq_of_component_mem` restricts an internal decomposition to any
submodule that contains the canonical components of each of its elements.

`DirectSum.coe_decompose_smul_add_of_right_mem` computes the components of a scalar
action on a homogeneous element when the scalar and module decompositions are compatible.

Finally, the external direct sum `⨁ i, M i` of a family of `R`-modules is the internal direct sum
of its summands `DirectSum.summand R M i`, the ranges of the inclusions `DirectSum.lof R ι M i`
(`DirectSum.isInternal_summand`). The resulting decomposition `DirectSum.instDecompositionSummand`
has `i`-th component `DirectSum.of M i (x i)` (`DirectSum.coe_decompose_summand`).
-/


open scoped DirectSum

namespace TauCeti

/-- The canonical inclusion of a direct sum of submodules into the direct sum of their ambient
modules. -/
def DirectSum.piInclusion {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i)) :
    (⨁ i, N i) →ₗ[R] ⨁ i, M i :=
  DirectSum.lmap fun i ↦ (N i).subtype

/-- The submodule of the direct sum consisting of elements whose components lie in the given
submodules. -/
def DirectSum.piSubmodule {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i)) :
    Submodule R (⨁ i, M i) :=
  LinearMap.range (TauCeti.DirectSum.piInclusion N)

/-- The componentwise formula for the inclusion of a direct sum of submodules. -/
@[simp]
theorem DirectSum.piInclusion_apply {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i))
    (x : ⨁ i, N i) (i : ι) :
    TauCeti.DirectSum.piInclusion N x i = (x i : M i) := by
  rw [TauCeti.DirectSum.piInclusion, DirectSum.lmap_apply, Submodule.coe_subtype]

/-- The inclusion of a generator of a direct sum of submodules. -/
@[simp]
theorem DirectSum.piInclusion_lof {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i)) (i : ι)
    (x : N i)
    [DecidableEq ι] :
    TauCeti.DirectSum.piInclusion N
        (DirectSum.lof R ι (fun i ↦ N i) i x) = DirectSum.lof R ι (fun i ↦ M i) i x := by
  rw [TauCeti.DirectSum.piInclusion, DirectSum.lmap_lof, Submodule.coe_subtype]

private theorem DirectSum.piInclusion_injective {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i)) :
    Function.Injective (TauCeti.DirectSum.piInclusion N) := by
  rw [TauCeti.DirectSum.piInclusion]
  refine (DirectSum.lmap_injective fun i ↦ (N i).subtype).mpr fun i ↦ ?_
  exact (N i).injective_subtype

/-- The linear equivalence from the direct sum of submodules to `piSubmodule N`. -/
noncomputable def DirectSum.piSubmoduleEquiv {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i)) :
    (⨁ i, N i) ≃ₗ[R] TauCeti.DirectSum.piSubmodule N :=
  LinearEquiv.ofInjective (TauCeti.DirectSum.piInclusion N)
    (by exact TauCeti.DirectSum.piInclusion_injective N)

/-- The underlying map of `piSubmoduleEquiv` is the canonical inclusion. -/
@[simp]
theorem DirectSum.piSubmoduleEquiv_apply {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i))
    (x : ⨁ i, N i) :
    ((TauCeti.DirectSum.piSubmoduleEquiv N x : TauCeti.DirectSum.piSubmodule N) :
      ⨁ i, M i) = TauCeti.DirectSum.piInclusion N x := by
  rw [TauCeti.DirectSum.piSubmoduleEquiv]
  exact LinearEquiv.ofInjective_apply _ x

/-- The inverse of `piSubmoduleEquiv` has the expected componentwise values. -/
@[simp]
theorem DirectSum.piSubmoduleEquiv_symm_apply {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i))
    (y : TauCeti.DirectSum.piSubmodule N) (i : ι) :
    ((TauCeti.DirectSum.piSubmoduleEquiv N).symm y i : M i) = (y : ⨁ i, M i) i := by
  have h := TauCeti.DirectSum.piSubmoduleEquiv_apply N
    ((TauCeti.DirectSum.piSubmoduleEquiv N).symm y)
  rw [LinearEquiv.apply_symm_apply] at h
  have hi := congrArg (fun z : ⨁ i, M i ↦ z i) h
  simpa only [TauCeti.DirectSum.piInclusion_apply] using hi.symm

/-- Membership in the direct sum of a family of submodules is componentwise. -/
@[simp]
theorem DirectSum.mem_piSubmodule_iff {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i))
    (x : ⨁ i, M i) :
    x ∈ TauCeti.DirectSum.piSubmodule N ↔ ∀ i, x i ∈ N i := by
  rw [TauCeti.DirectSum.piSubmodule, TauCeti.DirectSum.piInclusion, DirectSum.range_lmap]
  simp [Submodule.mem_comap, DirectSum.coeFnLinearMap_apply, Submodule.mem_pi]

/-- An included summand belongs to the direct sum of a family of submodules. -/
theorem DirectSum.lof_mem_piSubmodule {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i)) (i : ι)
    (x : N i)
    [DecidableEq ι] :
    DirectSum.lof R ι M i x ∈ TauCeti.DirectSum.piSubmodule N := by
  refine ⟨DirectSum.lof R ι (fun i ↦ N i) i x, ?_⟩
  exact TauCeti.DirectSum.piInclusion_lof N i x

/-- Restrict an internal direct sum decomposition along an injective linear map `f` which detects
membership in the summands and whose range contains every homogeneous projection of each of its
elements: the summands `𝓝` pulled back from `ℳ` are again an internal direct sum. -/
theorem DirectSum.isInternal_comap {R ι M N : Type*} [Semiring R]
    [DecidableEq ι] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ] (𝓝 : ι → Submodule R N)
    (f : N →ₗ[R] M) (hf : Function.Injective f)
    (hmem : ∀ i x, x ∈ 𝓝 i ↔ f x ∈ ℳ i)
    (hproj : ∀ i x, (DirectSum.decompose ℳ (f x) i : M) ∈ LinearMap.range f) :
    DirectSum.IsInternal 𝓝 := by
  classical
  let φ : ∀ i, 𝓝 i →ₗ[R] ℳ i := fun i ↦
    (f.comp (𝓝 i).subtype).codRestrict (ℳ i) fun x ↦ (hmem i x).mp x.2
  have hφ : ∀ (i : ι) (x : 𝓝 i), (φ i x : M) = f x := fun _ _ ↦ rfl
  have hΦinj : Function.Injective (DirectSum.lmap φ) :=
    (DirectSum.lmap_injective φ).mpr fun i x y hxy ↦
      Subtype.ext (hf (by rw [← hφ i x, ← hφ i y, hxy]))
  have hcoe : ∀ y : ⨁ i, 𝓝 i, f (DirectSum.coeAddMonoidHom 𝓝 y) =
      DirectSum.coeAddMonoidHom ℳ (DirectSum.lmap φ y) := by
    intro y
    induction y using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      simp only [DirectSum.lmap_of, DirectSum.coeAddMonoidHom_of]
      exact hφ i x
    | add y z hy hz => simp [hy, hz]
  have hsurj : ∀ x : N, ∃ y : ⨁ i, 𝓝 i,
      DirectSum.lmap φ y = DirectSum.decompose ℳ (f x) := by
    intro x
    have hmemrange : DirectSum.decompose ℳ (f x) ∈ LinearMap.range (DirectSum.lmap φ) := by
      rw [← DirectSum.sum_support_of (DirectSum.decompose ℳ (f x))]
      refine Submodule.sum_mem _ fun i _ ↦ ?_
      obtain ⟨n, hn⟩ := hproj i x
      have hn' : n ∈ 𝓝 i := (hmem i n).mpr (by rw [hn]; exact SetLike.coe_mem _)
      refine ⟨DirectSum.of (fun i ↦ 𝓝 i) i ⟨n, hn'⟩, ?_⟩
      rw [DirectSum.lmap_of]
      exact congrArg _ (Subtype.ext hn)
    exact hmemrange
  refine ⟨fun y z hyz ↦ hΦinj ((DirectSum.Decomposition.isInternal ℳ).injective ?_), fun x ↦ ?_⟩
  · rw [← hcoe, ← hcoe, hyz]
  · obtain ⟨y, hy⟩ := hsurj x
    refine ⟨y, hf ?_⟩
    rw [hcoe, hy]
    simpa using DirectSum.Decomposition.left_inv (ℳ := ℳ) (f x)

/-- Restrict an internal decomposition along an injective linear map whose range contains every
homogeneous projection of each of its elements. -/
@[instance_reducible]
noncomputable def DirectSum.Decomposition.restrict {R ι M N : Type*} [Semiring R]
    [DecidableEq ι] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ] (𝓝 : ι → Submodule R N)
    (f : N →ₗ[R] M) (hf : Function.Injective f) (hmem : ∀ i x, x ∈ 𝓝 i ↔ f x ∈ ℳ i)
    (hproj : ∀ i x, (DirectSum.decompose ℳ (f x) i : M) ∈ LinearMap.range f) :
    DirectSum.Decomposition 𝓝 :=
  (DirectSum.isInternal_comap ℳ 𝓝 f hf hmem hproj).chooseDecomposition

end TauCeti

namespace DirectSum

/-- An additive map which carries the degree-`i` summand of one internal decomposition into the
degree-`σ i` summand of another, along an injective reindexing `σ` of the degrees, commutes with
the homogeneous projections. The summands may be any additive subobjects, including submodules
over unrelated scalar semirings. -/
theorem map_decompose_shift {ι κ M N S T : Type*}
    [DecidableEq ι] [DecidableEq κ] [AddCommMonoid M] [AddCommMonoid N]
    [SetLike S M] [AddSubmonoidClass S M] [SetLike T N] [AddSubmonoidClass T N]
    (ℳ : ι → S) [DirectSum.Decomposition ℳ] (𝓝 : κ → T)
    [DirectSum.Decomposition 𝓝] (f : M →+ N) (σ : ι → κ) (hσ : Function.Injective σ)
    (hf : ∀ (i : ι) (x : M), x ∈ ℳ i → f x ∈ 𝓝 (σ i)) (i : ι) (x : M) :
    f (DirectSum.decompose ℳ x i : M) = (DirectSum.decompose 𝓝 (f x) (σ i) : N) := by
  induction x using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous j x =>
    have hxM : (x : M) ∈ ℳ j := x.2
    have hxN : f (x : M) ∈ 𝓝 (σ j) := hf j x hxM
    by_cases hij : i = j
    · subst hij
      rw [DirectSum.decompose_of_mem_same ℳ hxM, DirectSum.decompose_of_mem_same 𝓝 hxN]
    · rw [DirectSum.decompose_of_mem_ne ℳ hxM (Ne.symm hij), map_zero,
        DirectSum.decompose_of_mem_ne 𝓝 hxN fun hc ↦ Ne.symm hij (hσ hc)]
  | add x y hx hy => simp [hx, hy]

end DirectSum

namespace TauCeti

/-- Homogeneous projection in a restricted decomposition agrees with projection in the ambient
module. -/
@[simp]
theorem DirectSum.map_decompose_restrict {R ι M N : Type*} [Semiring R]
    [DecidableEq ι] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ] (𝓝 : ι → Submodule R N)
    [DirectSum.Decomposition 𝓝] (f : N →ₗ[R] M) (hmem : ∀ i x, x ∈ 𝓝 i ↔ f x ∈ ℳ i)
    (i : ι) (x : N) :
    f (DirectSum.decompose 𝓝 x i : N) =
      (DirectSum.decompose ℳ (f x) i : M) :=
  DirectSum.map_decompose_shift 𝓝 ℳ f.toAddMonoidHom id Function.injective_id
    (fun i x hx ↦ (hmem i x).mp hx) i x

-- The inverse congruence is definitionally the direct sum of the componentwise inverses; this
-- helper exposes that computation through the `DirectSum.lmap` API.
private theorem DirectSum.congrLinearEquiv_symm_apply {R ι : Type*} {N P : ι → Type*}
    [Semiring R] [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]
    (e : ∀ i, N i ≃ₗ[R] P i) (x : ⨁ i, P i) :
    (DirectSum.congrLinearEquiv e).symm x =
      DirectSum.lmap (fun i ↦ (e i).symm.toLinearMap) x := by
  rfl

-- Mathlib defines `DirectSum.IsInternal A` as bijectivity of the canonical map
-- `DirectSum.coeAddMonoidHom A`; for a family of submodules that canonical map is
-- `DirectSum.coeLinearMap A` (the same function packaged as a `LinearMap`).  Mathlib states no
-- iff lemma for this module-level form, so the equivalence below is a definitional unfolding,
-- the same one Mathlib's own API relies on (e.g. `IsInternal.ofBijective_coeLinearMap_same`).
-- The helper is private and single-purpose, so a Mathlib refactor of either definition will
-- surface exactly here.
private theorem DirectSum.isInternal_iff_bijective_coeLinearMap {R ι M : Type*}
    [Semiring R] [DecidableEq ι] [AddCommMonoid M] [Module R M]
    {A : ι → Submodule R M} :
    DirectSum.IsInternal A ↔ Function.Bijective (DirectSum.coeLinearMap A) :=
  Iff.rfl

/-- The canonical inclusions of a family of submodules form an internal direct sum when they are
identified with the summands of an equivalence. -/
theorem DirectSum.isInternal_of_lof {R ι M : Type*} [Semiring R] [DecidableEq ι]
    [AddCommMonoid M] [Module R M] {A : ι → Submodule R M} {N : ι → Type*}
    [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)] (e : ∀ i, N i ≃ₗ[R] A i)
    (E : (⨁ i, N i) ≃ₗ[R] M)
    (hE : ∀ i (x : N i), E (DirectSum.lof R ι (fun i ↦ N i) i x) = (e i x : M)) :
    DirectSum.IsInternal A := by
  let F : (⨁ i, A i) ≃ₗ[R] M :=
    (DirectSum.congrLinearEquiv e).symm.trans E
  have hF : ∀ i (x : A i), F (DirectSum.lof R ι (fun i ↦ A i) i x) = (x : M) := by
    intro i x
    simp only [F, LinearEquiv.trans_apply]
    rw [DirectSum.congrLinearEquiv_symm_apply, DirectSum.lmap_lof]
    simpa using hE i ((e i).symm x)
  have hcoe : DirectSum.coeLinearMap A = F.toLinearMap := by
    apply DirectSum.linearMap_ext R
    intro i
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof]
    exact (hF i x).symm
  rw [DirectSum.isInternal_iff_bijective_coeLinearMap, hcoe]
  exact F.bijective

/-- Two semilinear maps that agree on every member of a family of submodules spanning the source
are equal. -/
theorem _root_.LinearMap.ext_of_iSup_eq_top {R R₂ ι M M₂ : Type*} [Semiring R] [Semiring R₂]
    [AddCommMonoid M] [Module R M] [AddCommMonoid M₂] [Module R₂ M₂] {σ : R →+* R₂}
    {A : ι → Submodule R M} (hA : ⨆ i, A i = ⊤) {f g : M →ₛₗ[σ] M₂}
    (h : ∀ i, ∀ x ∈ A i, f x = g x) : f = g :=
  LinearMap.ext_on (s := ⋃ i, (A i : Set M)) (by rw [← Submodule.iSup_eq_span, hA])
    fun x hx ↦ by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
      exact h i x hi

/-- **The kernel of a map compatible with a decomposition is spanned by its homogeneous parts.**
If the submodules `A i` span the source, the submodules `A' i` are independent, and `g` carries
`A i` into `A' i`, then the kernel of `g` is the supremum of its intersections with the `A i`.

The hypothesis on the source is only that its family spans; independence there is not used, and
an internal direct sum supplies it through `DirectSum.IsInternal.submodule_iSup_eq_top`. -/
theorem _root_.LinearMap.ker_eq_iSup_inf_of_map_le {R ι M N : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (g : M →ₗ[R] N) {A : ι → Submodule R M}
    {A' : ι → Submodule R N} (hA : ⨆ i, A i = ⊤) (hA' : iSupIndep A')
    (hg : ∀ i, (A i).map g ≤ A' i) :
    LinearMap.ker g = ⨆ i, LinearMap.ker g ⊓ A i := by
  classical
  refine le_antisymm (fun x hx ↦ ?_) (iSup_le fun _ ↦ inf_le_left)
  obtain ⟨c, hc, rfl⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp A x).1 (hA ▸ Submodule.mem_top)
  have hsum : ∑ i ∈ c.support, g (c i) = 0 := by
    rw [← map_sum]
    simpa [Finsupp.sum] using hx
  have hzero := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero A').1 hA' c.support
    (fun i ↦ g (c i)) (fun i _ ↦ hg i ⟨c i, hc i, rfl⟩) hsum
  simp only [Finsupp.sum]
  exact Submodule.sum_mem _ fun i hi ↦
    Submodule.mem_iSup_of_mem i ⟨LinearMap.mem_ker.2 (hzero i hi), hc i⟩

end TauCeti

/-- A linear map preserves independence of a family of submodules if the part of its kernel
in their span is spanned by its intersections with the family. In particular, a quotient by a
homogeneous submodule preserves independence.

The ring hypothesis is essential: for semimodules, even a map with zero kernel can identify
independent summands. -/
theorem iSupIndep.map_of_ker_inf_iSup_le {R ι M N : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] {A : ι → Submodule R M}
    (hA : iSupIndep A) (f : M →ₗ[R] N)
    (hker : LinearMap.ker f ⊓ (⨆ i, A i) ≤ ⨆ i, LinearMap.ker f ⊓ A i) :
    iSupIndep fun i ↦ (A i).map f := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  classical
  intro s v hv hv0 j hj
  have hall : ∀ i : ι, ∃ y, y ∈ A i ∧ (i ∈ s → f y = v i) ∧ (i ∉ s → y = 0) := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨y, hy, hf⟩ := Submodule.mem_map.1 (hv i hi)
      exact ⟨y, hy, fun _ ↦ hf, fun h ↦ absurd hi h⟩
    · exact ⟨0, Submodule.zero_mem _, fun h ↦ absurd h hi, fun _ ↦ rfl⟩
  choose a haA haf ha0 using hall
  have hasum : ∑ i ∈ s, a i ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker, map_sum]
    exact (Finset.sum_congr rfl fun i hi ↦ haf i hi).trans hv0
  have hasumA : ∑ i ∈ s, a i ∈ ⨆ i, A i :=
    Submodule.sum_mem _ fun i _ ↦ Submodule.mem_iSup_of_mem i (haA i)
  obtain ⟨c, hc, hca⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp _ _).1 (hker ⟨hasum, hasumA⟩)
  have haj : a j = c j := by
    refine (iSupIndep_iff_finsetSum_eq_imp_eq A).1 hA (s ∪ c.support) a c
      (fun i _ ↦ ⟨haA i, (hc i).2⟩) ?_ j (Finset.mem_union_left _ hj)
    calc
        ∑ i ∈ s ∪ c.support, a i = ∑ i ∈ s, a i := by
          symm
          apply Finset.sum_subset (Finset.subset_union_left)
          intro i _ hi
          exact ha0 i hi
        _ = ∑ i ∈ c.support, c i := hca.symm
        _ = ∑ i ∈ s ∪ c.support, c i := by
          apply Finset.sum_subset (Finset.subset_union_right)
          simp
  rw [← haf j hj, haj]
  exact LinearMap.mem_ker.mp (hc j).1

namespace DirectSum.IsInternal

/-- Collecting an internal decomposition along the fibers of any map again gives an internal
decomposition. Each new summand is the sum of the original summands over the corresponding fiber. -/
theorem iSup_fiber {R M ι κ : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [DecidableEq ι] [DecidableEq κ] {P : ι → Submodule R M}
    (hP : DirectSum.IsInternal P) (degree : ι → κ) :
    DirectSum.IsInternal fun j ↦ ⨆ i, ⨆ _ : degree i = j, P i := by
  -- For submodules, the additive recomposition map in `IsInternal` is the underlying function
  -- of the canonical linear recomposition map.
  change Function.Bijective (DirectSum.coeLinearMap fun j ↦ ⨆ i, ⨆ _ : degree i = j, P i)
  refine ⟨?_, ?_⟩
  · -- Projection onto each fiber recovers that component of the recomposed direct sum.
    let Q : κ → Submodule R M := fun j ↦ ⨆ i, ⨆ _ : degree i = j, P i
    let _ : DirectSum.Decomposition P := hP.chooseDecomposition
    let projection (j : κ) : M →ₗ[R] M :=
      (DirectSum.toModule R ι M fun i ↦
        if degree i = j then (P i).subtype else 0) ∘ₗ
          (DirectSum.decomposeLinearEquiv P).toLinearMap
    have projection_piece (j : κ) (i : ι) (x : P i) :
        projection j x = if degree i = j then (x : M) else 0 := by
      simp only [projection, LinearMap.comp_apply, LinearEquiv.coe_coe,
        DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.toModule_lof]
      split <;> rfl
    have projection_mem (j k : κ) {x : M} (hx : x ∈ Q k) :
        projection j x = if k = j then x else 0 := by
      dsimp only [Q] at hx
      rw [iSup_subtype'] at hx
      refine Submodule.iSup_induction (fun i : {i // degree i = k} ↦ P i)
        (motive := fun y ↦ projection j y = if k = j then y else 0) hx
        (fun i x hx ↦ ?_) (by simp) (fun x y ihx ihy ↦ ?_)
      · simpa only [i.property] using projection_piece j i ⟨x, hx⟩
      · simp only [map_add, ihx, ihy, ite_add_zero]
    have projection_coe (j : κ) (z : ⨁ k, ↥(Q k)) :
        projection j (DirectSum.coeLinearMap Q z) = z j := by
      induction z using DirectSum.induction_on with
      | zero => simp
      | of k x =>
          rw [DirectSum.coeLinearMap_of, projection_mem j k x.property]
          simp only [DirectSum.coe_of_apply]
          split <;> rfl
      | add x y ihx ihy =>
          rw [map_add (DirectSum.coeLinearMap Q), map_add (projection j), ihx, ihy]
          rfl
    intro x y hxy
    apply DirectSum.ext fun j ↦ Subtype.ext ?_
    exact (projection_coe j x).symm.trans ((congrArg (projection j) hxy).trans
      (projection_coe j y))
  · rw [← LinearMap.range_eq_top, DirectSum.range_coeLinearMap, iSup_comm]
    simpa only [iSup_iSup_eq_right] using hP.submodule_iSup_eq_top

/-- **Restricting an internal decomposition to a component-stable subspace.** If a subspace
contains every canonical component of each of its elements, then it is the internal sum of its
intersections with the original summands. -/
theorem iSup_inf_eq_of_component_mem
    {S V κ : Type*} [Semiring S] [AddCommMonoid V] [Module S V] [DecidableEq κ]
    {A : κ → Submodule S V} (h : DirectSum.IsInternal A) (p : Submodule S V)
    (hp : ∀ (m : V), m ∈ p → ∀ i,
      (((LinearEquiv.ofBijective (DirectSum.coeLinearMap A) h).symm m i : A i) : V) ∈ p) :
    ⨆ i, p ⊓ A i = p := by
  classical
  refine le_antisymm (iSup_le fun _ ↦ inf_le_left) fun m hm ↦ ?_
  let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap A) h
  have hsum : m = ∑ i ∈ (e.symm m).support, ((e.symm m i : A i) : V) := by
    conv_lhs => rw [← e.apply_symm_apply m, ← DirectSum.sum_support_of (e.symm m)]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ DirectSum.coeLinearMap_of A i (e.symm m i)
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ ↦
    Submodule.mem_iSup_of_mem i ⟨hp m hm i, (e.symm m i).2⟩

end DirectSum.IsInternal

namespace DirectSum

variable {ι A M σA σM : Type*} [DecidableEq ι] [Add ι] [IsRightCancelAdd ι]
  [Semiring A] [AddCommMonoid M] [Module A M]
  [SetLike σA A] [AddSubmonoidClass σA A] (𝒜 : ι → σA) [Decomposition 𝒜]
  [SetLike σM M] [AddSubmonoidClass σM M] (ℳ : ι → σM) [Decomposition ℳ]
  [SetLike.GradedSMul 𝒜 ℳ]

/-- For compatible decompositions of a semiring and its module, the degree-`i + j` component of
`a • x`, for `x` homogeneous of degree `j`, is the degree-`i` component of `a` acting on `x`.
Only right cancellation of addition on the degrees is needed. This is the module analogue of
Mathlib's `DirectSum.coe_decompose_mul_add_of_right_mem`. -/
theorem coe_decompose_smul_add_of_right_mem {a : A} {x : M} {i j : ι} (hx : x ∈ ℳ j) :
    (decompose ℳ (a • x) (i + j) : M) = (decompose 𝒜 a i : A) • x := by
  induction a using Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous k a =>
    have hmem : (a : A) • x ∈ ℳ (k + j) := SetLike.GradedSMul.smul_mem a.2 hx
    by_cases hki : k = i
    · subst k
      rw [decompose_of_mem_same ℳ hmem, decompose_of_mem_same 𝒜 a.2]
    · rw [decompose_of_mem_ne ℳ hmem (fun h ↦ hki (add_right_cancel h)),
        decompose_of_mem_ne 𝒜 a.2 hki, zero_smul]
  | add a b ha hb => simp [add_smul, ha, hb]

end DirectSum

namespace DirectSum

section Module

variable {ι : Type*} (R : Type*) (M : ι → Type*) [DecidableEq ι] [Semiring R]
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- The `i`-th summand of the external direct sum `⨁ i, M i`: the image of `M i` under the
inclusion `DirectSum.lof R ι M i`. -/
def summand (i : ι) : Submodule R (⨁ i, M i) :=
  LinearMap.range (DirectSum.lof R ι M i)

/-- The `i`-th summand is the range of the inclusion `DirectSum.lof R ι M i`. -/
theorem summand_def (i : ι) : summand R M i = LinearMap.range (DirectSum.lof R ι M i) :=
  (rfl)

variable {R M}

/-- An element of `⨁ i, M i` lies in the `i`-th summand exactly when it is `DirectSum.of M i m`
for some `m : M i`. -/
theorem mem_summand {i : ι} {x : ⨁ i, M i} :
    x ∈ summand R M i ↔ ∃ m : M i, DirectSum.of M i m = x := by
  simp [summand, DirectSum.lof_eq_of]

/-- The element `DirectSum.lof R ι M i m` lies in the `i`-th summand. -/
theorem lof_mem_summand (i : ι) (m : M i) : DirectSum.lof R ι M i m ∈ summand R M i :=
  LinearMap.mem_range_self _ m

/-- The element `DirectSum.of M i m` lies in the `i`-th summand. -/
theorem of_mem_summand (i : ι) (m : M i) : DirectSum.of M i m ∈ summand R M i :=
  mem_summand.mpr ⟨m, rfl⟩

/-- The summands of the external direct sum form an internal direct sum: they are the ranges of
the inclusions `DirectSum.lof R ι M i`. -/
theorem isInternal_summand : DirectSum.IsInternal (summand R M) :=
  TauCeti.DirectSum.isInternal_of_lof
    (e := fun i ↦ LinearEquiv.ofInjective (DirectSum.lof R ι M i) (DirectSum.of_injective i))
    (E := LinearEquiv.refl R _) fun _ _ ↦ rfl

/-- The external direct sum decomposes as the direct sum of its summands. -/
noncomputable instance instDecompositionSummand : DirectSum.Decomposition (summand R M) :=
  isInternal_summand.chooseDecomposition

/-- The `i`-th component of an element `x` of `⨁ i, M i` for the summand decomposition is the
summand `x i`. -/
@[simp]
theorem coe_decompose_summand (x : ⨁ i, M i) (i : ι) :
    (DirectSum.decompose (summand R M) x i : ⨁ i, M i) = DirectSum.of M i (x i) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j m =>
    rw [DirectSum.decompose_of_mem (summand R M) (of_mem_summand j m)]
    by_cases h : j = i
    · subst h
      simp
    · simp [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
  | add x y hx hy => simp [hx, hy]

end Module

end DirectSum
end CanonicalSource44

section CanonicalSource45
/- Source: TauCeti/Order/CompactlyGenerated.lean -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Compact elements and independent families

This file records preservation of compact elements by order isomorphisms and lattice consequences
of independence that involve compact elements and compact generation.

## Main declarations

* `iSupIndep.finite_ne_bot_of_isCompactElement`: an independent family whose supremum
  is a compact element has only finitely many nonzero members. Compactness confines the whole
  family to a finite subfamily, and independence then forces every index outside it to be `⊥`.
  This is the compactness variant of Mathlib's
  `WellFoundedGT.finite_ne_bot_of_iSupIndep`, which instead assumes the ascending
  chain condition.
* `iSupIndep.iSup₂_inf_iSup_eq_iSup₂`: a partial supremum of an independent family
  meets the total supremum of a pointwise dominated family in its corresponding partial supremum.
* `iSupIndep.iSup₂_inf_iSup₂_eq_iSup₂_and`: two partial suprema of an independent
  family meet in the supremum over the intersection of their index predicates.
* `OrderIso.isCompactElement` and `OrderIso.isCompactElement_iff`: an order isomorphism of
  preorders preserves and reflects compactness of elements.
-/


/-- An order isomorphism of preorders sends compact elements to compact elements. -/
theorem OrderIso.isCompactElement {α β : Type*} [Preorder α] [Preorder β]
    (f : α ≃o β) {a : α} (ha : IsCompactElement a) : IsCompactElement (f a) := by
  intro s u hs hdir hlub hle
  obtain ⟨x, ⟨y, hy, rfl⟩, hay⟩ := ha (f.symm '' s) (f.symm u) (hs.image _)
    (hdir.mono_comp fun _ _ h ↦ f.symm.monotone h)
    (f.symm.isLUB_image'.mpr hlub) (f.le_symm_apply.mpr hle)
  exact ⟨y, hy, f.le_symm_apply.mp hay⟩

/-- An order isomorphism of preorders preserves and reflects compactness of elements. -/
@[simp]
theorem OrderIso.isCompactElement_iff {α β : Type*} [Preorder α] [Preorder β]
    (f : α ≃o β) {a : α} : IsCompactElement (f a) ↔ IsCompactElement a :=
  ⟨fun h ↦ by simpa using f.symm.isCompactElement h, f.isCompactElement⟩

/-- An independent family whose supremum is a compact element has only finitely many nonzero
members. -/
theorem iSupIndep.finite_ne_bot_of_isCompactElement {α ι : Type*} [CompleteLattice α]
    {a : ι → α} (ha : iSupIndep a)
    (hc : IsCompactElement (⨆ i, a i)) : {i | a i ≠ ⊥}.Finite := by
  obtain ⟨s, hs⟩ := hc.exists_finset_of_le_iSup a le_rfl
  refine s.finite_toSet.subset fun i hi ↦ ?_
  by_contra his
  refine hi ((ha i).eq_bot_of_le ((le_iSup a i).trans (hs.trans (iSup₂_le fun j hj ↦ ?_))))
  exact le_iSup₂_of_le j (fun hji ↦ his (Finset.mem_coe.mpr (hji ▸ hj))) le_rfl

/-- **A subfamily of an independent family truncates a dominated supremum.** If `B i ≤ A i` for
every `i` and the `A i` are independent, then the total supremum of the `B` meets the partial
supremum of the `A` over the indices satisfying `P` in exactly the partial supremum of the `B` over
those indices. -/
theorem iSupIndep.iSup₂_inf_iSup_eq_iSup₂ {α ι : Type*} [CompleteLattice α]
    [IsModularLattice α] [IsCompactlyGenerated α] {A B : ι → α}
    (hA : iSupIndep A) (hB : ∀ i, B i ≤ A i) (P : ι → Prop) :
    (⨆ (i) (_ : P i), A i) ⊓ ⨆ i, B i = ⨆ (i) (_ : P i), B i := by
  have hle : (⨆ (i) (_ : P i), B i) ≤ ⨆ (i) (_ : P i), A i := iSup₂_mono fun i _ ↦ hB i
  have hdisj : Disjoint (⨆ (i) (_ : P i), A i) (⨆ (i) (_ : ¬ P i), B i) := by
    have h₀ : Disjoint (⨆ (i) (_ : P i), A i) (⨆ (i) (_ : ¬ P i), A i) := by
      simpa only [Set.mem_ofPred_eq] using
        hA.disjoint_biSup_biSup (s := {i | P i}) (t := {i | ¬ P i})
          (Set.disjoint_left.2 fun i hi hi' ↦ hi' hi)
    exact h₀.mono_right (iSup₂_mono fun i _ ↦ hB i)
  rw [iSup_split B P, inf_comm, sup_inf_assoc_of_le _ hle, inf_comm, hdisj.eq_bot, sup_bot_eq]

/-- Two partial suprema of an independent family meet in the partial supremum selected by both
index predicates. -/
theorem iSupIndep.iSup₂_inf_iSup₂_eq_iSup₂_and {α ι : Type*} [CompleteLattice α]
    [IsModularLattice α] [IsCompactlyGenerated α] {A : ι → α}
    (hA : iSupIndep A) (P Q : ι → Prop) :
    (⨆ (i) (_ : P i), A i) ⊓ (⨆ (i) (_ : Q i), A i) =
      ⨆ (i) (_ : P i ∧ Q i), A i := by
  classical
  have h := iSupIndep.iSup₂_inf_iSup_eq_iSup₂
    (A := A) (B := fun i ↦ if Q i then A i else ⊥) hA
    (fun i ↦ by split <;> simp_all) P
  simp only [iSup_ite, iSup_bot, sup_bot_eq] at h
  simpa only [iSup_and] using h
end CanonicalSource45

section CanonicalSource46
/- Source: TauCeti/Algebra/Module/Submodule/Finite.lean -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Finiteness for submodules and quotients

An independent family of submodules whose supremum is finitely generated has only finitely
many nonzero members. This specializes `iSupIndep.finite_ne_bot_of_isCompactElement` using the
equivalence between finite generation and compactness in the lattice of submodules.

`Submodule.toAddSubgroup` is reducible and keeps the carrier set, so `p` and `p.toAddSubgroup`
have the same elements and the same `ℤ`-module structure. Instance search is nevertheless keyed
on the head symbol, so a `Module.Finite ℤ p` instance is never tried against the goal
`Module.Finite ℤ p.toAddSubgroup`. This file records that transfer once, for every `ℤ`-submodule,
rather than at each lattice presented to an API that reads additive subgroups.

For compatible actions of a semiring `A` and a ring `R`, an `R`-submodule `N` and its
quotient being finite over `A` implies that the ambient module is finite over `A`. The
quotient is formed over `R`; the scalar semiring `A` need not be a ring. This is the
scalar-restriction version of Mathlib's `Module.Finite.of_submodule_quotient`.

## Main declarations

* `Submodule.finite_iff_fg_restrictScalars`: an `R`-submodule is finite over a compatible scalar
  semiring `A` exactly when its restriction of scalars to `A` is finitely generated.
* `Module.Finite.of_restrictScalars_submodule_quotient`: finiteness of a submodule and quotient
  over a compatible semiring implies finiteness of the ambient module.
* `iSupIndep.finite_ne_bot_of_fg`: an independent family of submodules with finitely generated
  supremum has finite support.
* `TauCeti.instModuleFiniteToAddSubgroup`: a finitely generated `ℤ`-submodule stays finitely
  generated when read as an additive subgroup.
-/


/-- An independent family of submodules spanning a finitely generated submodule has only finitely
many nonzero members. -/
theorem iSupIndep.finite_ne_bot_of_fg {R ι M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] {A : ι → Submodule R M} (hAi : iSupIndep A) (hAf : (⨆ i, A i).FG) :
    {i | A i ≠ ⊥}.Finite :=
  hAi.finite_ne_bot_of_isCompactElement ((Submodule.fg_iff_compact _).mp hAf)

namespace TauCeti

/-- A finitely generated `ℤ`-submodule is still finitely generated when read as an additive
subgroup, the two being the same type. -/
instance instModuleFiniteToAddSubgroup {M : Type*} [AddCommGroup M] (p : Submodule ℤ M)
    [Module.Finite ℤ p] : Module.Finite ℤ p.toAddSubgroup :=
  inferInstanceAs (Module.Finite ℤ p)

end TauCeti

/-- An `R`-submodule is a finite module over a compatible scalar semiring `A` exactly when its
restriction of scalars to `A` is finitely generated. -/
theorem Submodule.finite_iff_fg_restrictScalars {A R M : Type*} [Semiring A] [Semiring R]
    [AddCommMonoid M] [Module A M] [Module R M] [SMul A R] [IsScalarTower A R M]
    (N : Submodule R M) : Module.Finite A N ↔ (N.restrictScalars A).FG := by
  rw [← Module.Finite.iff_fg]
  let e := (N.restrictScalarsEquiv A).restrictScalars A
  exact ⟨fun _ ↦ .equiv e.symm, fun _ ↦ .equiv e⟩

/-- If an `R`-submodule and its quotient are finite over a compatible scalar semiring `A`,
then so is the ambient module. The quotient is formed over the ring `R`, so `A` need not
be a ring or commutative. -/
theorem Module.Finite.of_restrictScalars_submodule_quotient
    {A R M : Type*} [Semiring A] [Ring R] [AddCommGroup M]
    [Module A M] [Module R M] [SMul A R] [IsScalarTower A R M]
    (N : Submodule R M) [Module.Finite A N] [Module.Finite A (M ⧸ N)] :
    Module.Finite A M := by
  have : Module.Finite A (N.restrictScalars A) :=
    Module.Finite.equiv ((N.restrictScalarsEquiv A).restrictScalars A).symm
  classical
  -- Lift a finite set of quotient generators; together with the finite kernel they span.
  obtain ⟨s, hs⟩ := Module.finite_def.mp
    (inferInstance : Module.Finite A (M ⧸ N))
  choose lift hlift using N.mkQ_surjective
  let P := Submodule.span A (lift '' (s : Set (M ⧸ N)))
  have hP : P.map (N.mkQ.restrictScalars A) = ⊤ := by
    rw [Submodule.map_span, ← Set.image_comp]
    simpa only [Function.comp_def, LinearMap.restrictScalars_apply, hlift,
      Set.image_id'] using hs
  have htop : P ⊔ N.restrictScalars A = ⊤ := by
    refine top_unique fun x _ ↦ ?_
    have hx : N.mkQ x ∈ P.map (N.mkQ.restrictScalars A) := by rw [hP]; trivial
    obtain ⟨y, hy, hyx⟩ := hx
    simp only [LinearMap.restrictScalars_apply] at hyx
    -- The restricted kernel has the same carrier; quotient equality detects its differences.
    exact Submodule.mem_sup.mpr
      ⟨y, hy, x - y, (Submodule.Quotient.eq N).mp hyx.symm, add_sub_cancel _ _⟩
  refine ⟨?_⟩
  rw [← htop]
  exact (Submodule.fg_span (s.finite_toSet.image lift)).sup
    (Module.Finite.iff_fg.mp inferInstance)
end CanonicalSource46

section CanonicalSource47
/- Source: TauCeti/Algebra/Module/GradedModule/Internal.lean -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Internally graded modules

This file packages an indexed graded module as a total module together with an internal direct-sum
decomposition. The total-module presentation is convenient for DG and `A∞` operations, while
`DirectSum.IsInternal` ensures that every element is a finite, uniquely determined sum of
homogeneous elements.

Mathlib already provides the direct-sum equivalence and its induction principle through
`DirectSum.Decomposition`.  An `InternalGrading` retains the family of homogeneous submodules and
the proof that it is internal; the instance below makes Mathlib's decomposition API available
without duplicating it.

The file also records that a finitely generated internally graded module has only finitely many
nonzero pieces, the Koszul twist operator used to encode Koszul signs on homogeneous elements, and
the letterwise tuple operation that applies it on a half-open index interval. These sign
operations use integer degrees, while decomposition and transport allow any index type. The
Koszul twist and its tuple operation work over any ring: their integer signs are central scalars.

## Main definitions

* `InternalGrading`: an internal grading of a module, with integer degrees by default.
* `InternalGrading.ofDecomposition`: the internal grading carried by a family of submodules with a
  `DirectSum.Decomposition`, as graded algebras store it.
* `InternalGrading.map`: transport an internal grading across a linear equivalence.
* `InternalGrading.koszulTwist`: the operator scaling degree-`e` elements by `(-1)^(q * e)`.
* `InternalGrading.quadraticTwist`: multiplication of degree `p` by
  `(-1)^(p choose 2)`.
* `InternalGrading.twistedTuple`: a tuple with a consecutive block of letters Koszul-twisted.

## Main results

* `TauCeti.InternalGrading.ext`: internal gradings are determined by their homogeneous pieces.
* `TauCeti.InternalGrading.linearMap_ext`: linear maps agree when they agree on homogeneous
  elements.
* `TauCeti.InternalGrading.finite_piece_ne_bot`: a finitely generated internally graded module has
  only finitely many nonzero homogeneous pieces.
* `TauCeti.InternalGrading.koszulTwist_apply_of_mem`: the twist acts by the Koszul scalar on
  each homogeneous piece.
* `TauCeti.InternalGrading.koszulTwist_comp`: twists compose by adding the twist parameters.
* `TauCeti.InternalGrading.quadraticTwist_involutive`: the quadratic twist is an involution.
* `TauCeti.LinearMap.IsHomogeneous.linearEquiv_symm`: the inverse of a degree-zero homogeneous
  linear equivalence is homogeneous.
* `TauCeti.LinearMap.IsHomogeneous.map_decompose`: a homogeneous map commutes with homogeneous
  projection, up to the shift of degree.
* `TauCeti.LinearMap.IsHomogeneous.isHomogeneous_ker` and
  `TauCeti.LinearMap.IsHomogeneous.isHomogeneous_range`: the kernel and the image of a homogeneous
  map are homogeneous submodules.
* `TauCeti.LinearMap.IsHomogeneous.koszulTwist_apply` and
  `TauCeti.LinearMap.IsHomogeneous.koszulTwist_comp`: pointwise and operator forms of commuting a
  homogeneous linear map with Koszul twists up to the sign determined by its degree.
* `TauCeti.LinearMap.IsHomogeneous.twistedTuple_map`: a degree-zero homogeneous map commutes with
  twisting a block of a tuple.

Later files use Mathlib's decomposition API to define maps of nonzero degree, shifts,
tensor-product gradings, and signed multilinear operations.
-/


open scoped DirectSum

namespace TauCeti

universe u v w

variable (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M]

/-- An internal grading of an `R`-module `M` indexed by `ι`, with integer degrees by default.

The `isInternal` field says that the canonical map from the external direct sum of the `piece p`
to `M` is bijective.  Thus elements of `M` have unique finite homogeneous decompositions.

The index equality instance is required by Mathlib's `DirectSum.IsInternal` and
`DirectSum.Decomposition`. For an index type without a computable equality instance, use
`classical` locally to supply it; no computability assumption on the index type is needed. -/
structure InternalGrading (ι : Type := ℤ) [DecidableEq ι] where
  /-- The submodule of elements of degree `p`. -/
  piece : ι → Submodule R M
  /-- The homogeneous pieces form an internal direct sum. -/
  isInternal : DirectSum.IsInternal piece

namespace InternalGrading

variable {R M} {ι : Type} [DecidableEq ι]

/-- Two internal gradings of the same module are equal as soon as their homogeneous pieces
agree. -/
@[ext]
theorem ext : ∀ {G H : InternalGrading R M ι}, (∀ p, G.piece p = H.piece p) → G = H
  | ⟨_, _⟩, ⟨_, _⟩, h => by
    obtain rfl := funext h
    rfl

/-- The decomposition attached to an internal grading. -/
noncomputable instance (G : InternalGrading R M ι) : DirectSum.Decomposition G.piece :=
  G.isInternal.chooseDecomposition

/-- The internal grading carried by a family of submodules with a `DirectSum.Decomposition`.  This
is the bridge from Mathlib's decomposition typeclass, under which graded algebras are stated, to
the bundled internal grading of this file. -/
noncomputable def ofDecomposition (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ] :
    InternalGrading R M ι :=
  ⟨ℳ, DirectSum.Decomposition.isInternal ℳ⟩

@[simp]
theorem ofDecomposition_piece (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ] :
    (ofDecomposition ℳ).piece = ℳ := (rfl)

/-- A submodule is homogeneous for the internal grading `ofDecomposition ℳ` exactly when it is
homogeneous for `ℳ`: the decomposition carried by `ofDecomposition ℳ` is the given one, as
decompositions are unique. -/
@[simp]
theorem isHomogeneous_ofDecomposition_piece_iff (ℳ : ι → Submodule R M)
    [DirectSum.Decomposition ℳ] (U : Submodule R M) :
    DirectSum.SetLike.IsHomogeneous (ofDecomposition ℳ).piece U ↔
      DirectSum.SetLike.IsHomogeneous ℳ U :=
  Iff.of_eq (congrArg (fun d ↦ @DirectSum.SetLike.IsHomogeneous _ _ _ _ _ _ _ ℳ d _ _ U)
    (Subsingleton.elim _ _))

/-- The homogeneous elements of an internally graded module span it over any scalar semiring
acting on the total module. No compatibility between that action and the grading is needed. -/
theorem span_setOf_exists_mem_piece_eq_top (S : Type*) [Semiring S] [Module S M]
    (G : InternalGrading R M ι) : Submodule.span S {x : M | ∃ p, x ∈ G.piece p} = ⊤ := by
  classical
  apply top_unique
  intro y _
  rw [← DirectSum.sum_support_decompose G.piece y]
  exact Submodule.sum_mem _ fun p _ => Submodule.subset_span
    ⟨p, (DirectSum.decompose G.piece y p).property⟩

/-- Two linear maps over any scalar semiring on an internally graded module agree if they agree
on homogeneous elements. No compatibility between the scalar action and the grading is needed. -/
theorem linearMap_ext {S : Type*} [Semiring S] [Module S M]
    {N : Type w} [AddCommMonoid N] [Module S N]
    (G : InternalGrading R M ι) {f g : M →ₗ[S] N}
    (h : ∀ (p : ι) (x : M), x ∈ G.piece p → f x = g x) : f = g := by
  apply (Submodule.linearMap_eq_iff_of_span_eq_top f g
    (G.span_setOf_exists_mem_piece_eq_top S)).2
  rintro ⟨x, p, hx⟩
  exact h p x hx

section Map

variable {N : Type w} [AddCommMonoid N] [Module R N]

private noncomputable def mapPiecesEquiv (G : InternalGrading R M ι) (e : M ≃ₗ[R] N) :
    (⨁ p : ι, G.piece p) ≃ₗ[R] (⨁ p : ι, (G.piece p).map e.toLinearMap) :=
  DirectSum.congrLinearEquiv fun p ↦
    Submodule.equivMapOfInjective e.toLinearMap e.injective (G.piece p)

private theorem mapPiecesEquiv_lof (G : InternalGrading R M ι) (e : M ≃ₗ[R] N)
    (p : ι) (x : G.piece p) :
    mapPiecesEquiv G e (DirectSum.lof R ι (fun i ↦ G.piece i) p x) =
      DirectSum.lof R ι (fun i ↦ (G.piece i).map e.toLinearMap) p
        ((Submodule.equivMapOfInjective e.toLinearMap e.injective (G.piece p)).toLinearMap x) := by
  -- Expose the bundled linear map so the direct-sum application lemma can rewrite it.
  change (mapPiecesEquiv G e).toLinearMap
    (DirectSum.lof R ι (fun i ↦ G.piece i) p x) = _
  rw [mapPiecesEquiv, DirectSum.congrLinearEquiv_toLinearMap, DirectSum.lmap_lof]

private theorem coeLinearMap_comp_mapPiecesEquiv (G : InternalGrading R M ι)
    (e : M ≃ₗ[R] N) :
    (DirectSum.coeLinearMap fun p : ι ↦ (G.piece p).map e.toLinearMap) ∘ₗ
        (mapPiecesEquiv G e).toLinearMap =
      e.toLinearMap ∘ₗ DirectSum.coeLinearMap G.piece := by
  apply DirectSum.linearMap_ext R
  intro p
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  calc
    (DirectSum.coeLinearMap fun p : ι ↦ (G.piece p).map e.toLinearMap)
        ((mapPiecesEquiv G e).toLinearMap
          (DirectSum.lof R ι (fun i ↦ G.piece i) p x)) =
        (DirectSum.coeLinearMap fun p : ι ↦ (G.piece p).map e.toLinearMap)
          (DirectSum.lof R ι (fun i ↦ (G.piece i).map e.toLinearMap) p
            ((Submodule.equivMapOfInjective e.toLinearMap e.injective
              (G.piece p)).toLinearMap x)) :=
      congrArg _ (mapPiecesEquiv_lof G e p x)
    _ = e x := by
      rw [DirectSum.coeLinearMap_lof]
      exact Submodule.coe_equivMapOfInjective_apply e.toLinearMap e.injective (G.piece p) x
    _ = e.toLinearMap (DirectSum.coeLinearMap G.piece
        (DirectSum.lof R ι (fun i ↦ G.piece i) p x)) := by
      rw [DirectSum.coeLinearMap_lof]
      rfl

/-- Transport an internal grading across a linear equivalence. The degree-`p` piece of the target
is the image of the degree-`p` piece of the source. -/
noncomputable def map (G : InternalGrading R M ι) (e : M ≃ₗ[R] N) : InternalGrading R N ι where
  piece p := (G.piece p).map e.toLinearMap
  isInternal := by
    -- Expose `coeLinearMap` rather than its definitionally equal additive coercion so it can be
    -- composed with `mapPiecesEquiv` below.
    change Function.Bijective
      (DirectSum.coeLinearMap fun p : ι ↦ (G.piece p).map e.toLinearMap)
    let E := mapPiecesEquiv G e
    have hcomp : Function.Bijective
        ((DirectSum.coeLinearMap fun p : ι ↦ (G.piece p).map e.toLinearMap) ∘ₗ E.toLinearMap) := by
      rw [coeLinearMap_comp_mapPiecesEquiv]
      exact e.bijective.comp G.isInternal
    constructor
    · intro x y hxy
      obtain ⟨x', rfl⟩ := E.surjective x
      obtain ⟨y', rfl⟩ := E.surjective y
      exact congrArg E (hcomp.injective (by
        simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] using hxy))
    · intro y
      obtain ⟨x, hx⟩ := hcomp.surjective y
      exact ⟨E x, by
        simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] using hx⟩

/-- The degree-`p` piece of a transported grading is the image of the original piece. -/
@[simp]
theorem map_piece (G : InternalGrading R M ι) (e : M ≃ₗ[R] N) (p : ι) :
    (G.map e).piece p = (G.piece p).map e.toLinearMap :=
  (rfl)

/-- Membership in a transported piece can be checked after applying the inverse equivalence.

This is not a `simp` lemma: `map_piece` already rewrites the left-hand side to a `Submodule.map`,
on which the `simp` set fires `Submodule.mem_map_equiv` to reach the same right-hand side. -/
theorem mem_map_piece_iff (G : InternalGrading R M ι) (e : M ≃ₗ[R] N) (p : ι) (y : N) :
    y ∈ (G.map e).piece p ↔ e.symm y ∈ G.piece p := by
  exact Submodule.mem_map_equiv (p := G.piece p) (e := e)

/-- A linear equivalence maps a homogeneous element into the transported piece of the same
degree. This is the special case of `mem_map_piece_iff` that `simp` already reaches. -/
theorem apply_mem_map_piece_iff (G : InternalGrading R M ι) (e : M ≃ₗ[R] N) (p : ι) (x : M) :
    e x ∈ (G.map e).piece p ↔ x ∈ G.piece p := by
  simp

/-- Membership in a grading transported to a universe lift is checked after lowering. -/
theorem mem_map_ulift_piece_iff (G : InternalGrading R M ι) (p : ι) (x : ULift.{w} M) :
    x ∈ (G.map (ULift.moduleEquiv : ULift.{w} M ≃ₗ[R] M).symm).piece p ↔ x.down ∈ G.piece p := by
  rw [mem_map_piece_iff, LinearEquiv.symm_symm, ULift.moduleEquiv_apply]

/-- The equivalence used to transport a grading is homogeneous of degree zero. -/
theorem isHomogeneous_map [AddMonoid ι] (G : InternalGrading R M ι) (e : M ≃ₗ[R] N) :
    TauCeti.LinearMap.IsHomogeneous e.toLinearMap G.piece (G.map e).piece 0 := by
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro p x hx
  simpa using hx

/-- The inverse of an equivalence used to transport a grading is homogeneous of degree zero. -/
theorem isHomogeneous_map_symm [AddMonoid ι] (G : InternalGrading R M ι) (e : M ≃ₗ[R] N) :
    TauCeti.LinearMap.IsHomogeneous e.symm.toLinearMap (G.map e).piece G.piece 0 := by
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro p y hy
  simpa using hy

/-- Transport along the identity equivalence leaves an internal grading unchanged. -/
@[simp]
theorem map_refl (G : InternalGrading R M ι) : G.map (LinearEquiv.refl R M) = G := by
  apply InternalGrading.ext
  intro p
  apply Submodule.ext
  intro x
  simp

/-- Successive transport agrees with transport along the composite equivalence. -/
@[simp]
theorem map_trans {P : Type*} [AddCommMonoid P] [Module R P]
    (G : InternalGrading R M ι) (e : M ≃ₗ[R] N) (f : N ≃ₗ[R] P) :
    (G.map e).map f = G.map (e.trans f) := by
  apply InternalGrading.ext
  intro p
  apply Submodule.ext
  intro x
  simp

end Map

/-- An additive map that vanishes on every homogeneous piece except degree `i` sees only the
degree-`i` component of each argument. -/
theorem map_eq_map_decompose {N : Type w} [AddCommMonoid N] (G : InternalGrading R M ι)
    (f : M →+ N) {i : ι}
    (hf : ∀ j (x : M), x ∈ G.piece j → j ≠ i → f x = 0) (x : M) :
    f x = f (DirectSum.decompose G.piece x i : M) := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose G.piece x]
  rw [map_sum]
  refine Finset.sum_eq_single i (fun j _ hj ↦ ?_) fun hi ↦ ?_
  · exact hf j _ (DirectSum.decompose G.piece x j).2 hj
  · rw [DFinsupp.notMem_support_iff.mp hi, Submodule.coe_zero, map_zero]

end InternalGrading

namespace LinearMap.IsHomogeneous

variable {R S : Type*} {M : Type v} {N : Type w} [Semiring R] [Semiring S]
  [AddCommMonoid M] [Module R M] [Module S M] [AddCommMonoid N] [Module R N] [Module S N]

/-- The inverse of a degree-zero homogeneous linear equivalence of internally graded modules is
again homogeneous of degree zero. The equivalence may be linear over a ring `S` other than the
ring `R` over which the homogeneous pieces are submodules. -/
theorem linearEquiv_symm {ι : Type} [DecidableEq ι] [AddMonoid ι]
    {G : InternalGrading R M ι} {H : InternalGrading R N ι} {e : M ≃ₗ[S] N}
    (he : IsHomogeneous e.toLinearMap G.piece H.piece 0) :
    IsHomogeneous e.symm.toLinearMap H.piece G.piece 0 := by
  -- The restrictions `ep p : G.piece p → H.piece p` assemble to a map of direct sums lying over
  -- `e`; it is surjective because `e` and both decompositions are, hence so is each `ep p`.
  let ep : (p : ι) → G.piece p →+ H.piece p := fun p ↦
    { toFun := fun x ↦ ⟨e.toLinearMap x, by simpa only [add_zero] using he.map_mem x.2⟩
      map_zero' := Subtype.ext (map_zero e.toLinearMap)
      map_add' := fun x y ↦ Subtype.ext (map_add e.toLinearMap (x : M) (y : M)) }
  have hcomm : (DirectSum.coeAddMonoidHom H.piece).comp (DirectSum.map ep) =
      e.toAddEquiv.toAddMonoidHom.comp (DirectSum.coeAddMonoidHom G.piece) := by
    apply DirectSum.addHom_ext
    intro p x
    simp [ep]
  have hmap_surj : Function.Surjective (DirectSum.map ep) := by
    intro y
    obtain ⟨x, hx⟩ := G.isInternal.surjective (e.symm (DirectSum.coeAddMonoidHom H.piece y))
    refine ⟨x, H.isInternal.injective ?_⟩
    have hc := DFunLike.congr_fun hcomm x
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hx] at hc
    exact hc.trans (e.apply_symm_apply _)
  -- A degree-`p` element `y` is `e x` for some `x` of degree `p`, so `e.symm y = x`.
  rw [LinearMap.isHomogeneous_def]
  intro p y hy
  obtain ⟨x, hx⟩ := (DirectSum.map_surjective ep).mp hmap_surj p ⟨y, hy⟩
  have hxy : e.symm y = x := by
    rw [← e.symm_apply_apply (x : M)]
    exact congrArg e.symm (congrArg Subtype.val hx).symm
  simpa only [add_zero, LinearEquiv.coe_coe, hxy] using x.2

section Decompose

variable {ι : Type} [DecidableEq ι] [AddRightCancelMonoid ι]
  {R S : Type*} {M : Type v} {N : Type w} [Semiring R] [Semiring S]
  [AddCommMonoid M] [Module R M] [Module S M]
  [AddCommMonoid N] [Module R N] [Module S N]
  {f : M →ₗ[S] N} {r : ι}

/-- A homogeneous linear map of degree `r` carries the degree-`p` component of an element to the
degree-`(p + r)` component of its image.  The gradings are any families of submodules with
`DirectSum.Decomposition` instances, so this applies to the pieces of internal gradings and to
Mathlib's graded algebras alike. -/
theorem map_decompose {ℳ : ι → Submodule R M} [DirectSum.Decomposition ℳ]
    {𝓝 : ι → Submodule R N} [DirectSum.Decomposition 𝓝] (hf : LinearMap.IsHomogeneous f ℳ 𝓝 r)
    (p : ι) (x : M) :
    f (DirectSum.decompose ℳ x p : M) = (DirectSum.decompose 𝓝 (f x) (p + r) : N) :=
  DirectSum.map_decompose_shift ℳ 𝓝 f.toAddMonoidHom (· + r)
    (add_left_injective r) (fun _ _ hx ↦ hf.map_mem hx) p x

variable {G : InternalGrading R M ι} {H : InternalGrading R N ι}

/-- The kernel of a homogeneous linear map is a homogeneous submodule. -/
theorem isHomogeneous_ker (hf : LinearMap.IsHomogeneous f G.piece H.piece r) :
    DirectSum.SetLike.IsHomogeneous G.piece (_root_.LinearMap.ker f) := fun p x hx ↦ by
  rw [_root_.LinearMap.mem_ker] at hx ⊢
  rw [hf.map_decompose, hx, DirectSum.decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]

end Decompose

/-- The image of a homogeneous linear map is a homogeneous submodule, for degrees in any
additive monoid. -/
theorem isHomogeneous_range {ι : Type} [DecidableEq ι] [AddMonoid ι]
    {G : InternalGrading R M ι} {H : InternalGrading R N ι} {f : M →ₗ[S] N} {r : ι}
    (hf : LinearMap.IsHomogeneous f G.piece H.piece r) :
    DirectSum.SetLike.IsHomogeneous H.piece (_root_.LinearMap.range f) := by
  rintro q _ ⟨x, rfl⟩
  induction x using DirectSum.Decomposition.inductionOn G.piece with
  | zero => simp
  | @homogeneous p x =>
    by_cases hpq : p + r = q
    · subst q
      rw [DirectSum.decompose_of_mem_same H.piece (hf.map_mem x.2)]
      exact ⟨x, rfl⟩
    · rw [DirectSum.decompose_of_mem_ne H.piece (hf.map_mem x.2) hpq]
      exact Submodule.zero_mem _
  | add x y hx hy => simpa using Submodule.add_mem _ hx hy

end LinearMap.IsHomogeneous

section FiniteSupport

variable {ι : Type} [DecidableEq ι]
  {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

private theorem InternalGrading.finite_piece_ne_bot_aux (G : InternalGrading R M ι)
    [Module.Finite R M] : {p | G.piece p ≠ ⊥}.Finite :=
  G.isInternal.submodule_iSupIndep.finite_ne_bot_of_fg
    (by rw [G.isInternal.submodule_iSup_eq_top]; exact Module.Finite.fg_top)

/-- A finitely generated internally graded module has only finitely many nonzero homogeneous
pieces. -/
theorem InternalGrading.finite_piece_ne_bot (G : InternalGrading R M ι) [Module.Finite R M] :
    {p | G.piece p ≠ ⊥}.Finite :=
  G.finite_piece_ne_bot_aux

/-- Summing the homogeneous components over the finite set of nonzero pieces reconstructs the
original element. -/
theorem InternalGrading.sum_decompose_toFinset (G : InternalGrading R M ι)
    (hG : {p | G.piece p ≠ ⊥}.Finite) (x : M) :
    ∑ p ∈ hG.toFinset, (DirectSum.decompose G.piece x p : M) = x := by
  classical
  conv_rhs => rw [← DirectSum.sum_support_decompose G.piece x]
  refine (Finset.sum_subset (fun p hp ↦ ?_) fun p _ hp ↦ ?_).symm
  · refine hG.mem_toFinset.mpr fun hbot ↦ DFinsupp.mem_support_iff.mp hp
      (Submodule.coe_eq_zero.mp
        ((Submodule.eq_bot_iff _).mp hbot _ (DirectSum.decompose G.piece x p).2))
  · rw [DFinsupp.notMem_support_iff.mp hp]
    simp

end FiniteSupport

section KoszulTwist

variable {R : Type u} {M : Type v} [Ring R] [AddCommMonoid M] [Module R M]

/-- The Koszul twist of parameter `q`: on the homogeneous piece of degree `e` it acts as the
scalar `(-1)^(q * e)`.

This is multiplication by the same coefficient that `MultilinearMap.koszulSign` records for a
single homogeneous input of degree `e`.  Downstream modules express their Koszul signs through this
operator: the sign acquired by moving an operation of degree `q` past homogeneous inputs of total
degree `D` is the scalar by which `koszulTwist G q` scales those inputs. -/
noncomputable def InternalGrading.koszulTwist (G : InternalGrading R M) (q : ℤ) : M →ₗ[R] M :=
  DirectSum.coeLinearMap (fun e => G.piece e) ∘ₗ
    DirectSum.toModule R ℤ (⨁ e : ℤ, G.piece e)
      (fun e => DirectSum.lof R ℤ (fun e => G.piece e) e ∘ₗ
        Module.End.smulLeft (((q * e).negOnePow : ℤ) : R) (Set.intCast_mem_center R _)) ∘ₗ
    (DirectSum.decomposeLinearEquiv (ℳ := G.piece)).toLinearMap

/-- The tuple `x` with exactly the letters at positions in the half-open interval `[a, a + p)`
Koszul-twisted.  Downstream, the Taylor summand collapsing the block of length `d` starting at
`a + p` is supported on this tuple: the collapse carries the Koszul sign of moving the operation
past those preceding letters, and twisting them is how that sign is encoded. -/
noncomputable def InternalGrading.twistedTuple (G : InternalGrading R M) (q : ℤ) {n : ℕ}
    (x : Fin n → M) (a p : ℕ) : Fin n → M :=
  fun i => if a ≤ i.val ∧ i.val < a + p then koszulTwist G q (x i) else x i

end KoszulTwist

section KoszulTwistLemmas

variable {R : Type u} {M : Type v} [Ring R] [AddCommMonoid M] [Module R M]

/-- On a homogeneous element of degree `e`, the Koszul twist of parameter `q` acts as the scalar
`(-1)^(q * e)`. -/
theorem InternalGrading.koszulTwist_apply_of_mem (G : InternalGrading R M) {x : M} {e : ℤ}
    (hx : x ∈ G.piece e) (q : ℤ) :
    koszulTwist G q x = (((q * e).negOnePow : ℤ) : R) • x := by
  rw [koszulTwist]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    DirectSum.decomposeLinearEquiv_apply]
  rw [DirectSum.decompose_of_mem (ℳ := G.piece) hx,
    ← DirectSum.lof_eq_of R ℤ (fun i : ℤ => G.piece i)]
  simp [DirectSum.toModule_lof]

/-- The Koszul twist fixes the elements of degree zero. -/
theorem InternalGrading.koszulTwist_apply_of_mem_zero (G : InternalGrading R M) {x : M}
    (hx : x ∈ G.piece 0) (q : ℤ) : koszulTwist G q x = x := by
  rw [InternalGrading.koszulTwist_apply_of_mem G hx q, mul_zero, Int.negOnePow_zero,
    Units.val_one, Int.cast_one, one_smul]

/-- The Koszul twist of parameter one acts on an element of degree `e` as the sign `(-1)^e`. -/
theorem InternalGrading.koszulTwist_one_apply_of_mem (G : InternalGrading R M) {x : M} {e : ℤ}
    (hx : x ∈ G.piece e) : koszulTwist G 1 x = ((e.negOnePow : ℤ) : R) • x := by
  rw [InternalGrading.koszulTwist_apply_of_mem G hx 1, one_mul]

/-- The Koszul twist preserves each homogeneous piece. -/
theorem InternalGrading.koszulTwist_mem_piece (G : InternalGrading R M) {x : M} {e : ℤ}
    (hx : x ∈ G.piece e) (q : ℤ) :
    koszulTwist G q x ∈ G.piece e := by
  rw [InternalGrading.koszulTwist_apply_of_mem G hx q]
  exact Submodule.smul_mem _ _ hx

/-- The Koszul twist of the grading of a decomposition `ℳ` preserves each piece `ℳ k`. -/
theorem InternalGrading.koszulTwist_mem_ofDecomposition (ℳ : ℤ → Submodule R M)
    [DirectSum.Decomposition ℳ] {x : M} {k : ℤ} (hx : x ∈ ℳ k) (q : ℤ) :
    koszulTwist (InternalGrading.ofDecomposition ℳ) q x ∈ ℳ k := by
  have hx' : x ∈ (InternalGrading.ofDecomposition ℳ).piece k := by
    rwa [InternalGrading.ofDecomposition_piece]
  have := koszulTwist_mem_piece _ hx' q
  rwa [InternalGrading.ofDecomposition_piece] at this

/-- The Koszul twist of parameter zero is the identity. -/
@[simp]
theorem InternalGrading.koszulTwist_zero (G : InternalGrading R M) :
    koszulTwist G 0 = LinearMap.id := by
  refine DirectSum.decompose_lhom_ext (ℳ := G.piece) fun e => ?_
  ext x
  simp only [LinearMap.comp_apply]
  have h := InternalGrading.koszulTwist_apply_of_mem G (Submodule.coe_mem x) 0
  simpa using h

/-- Koszul twists compose by adding their parameters. -/
theorem InternalGrading.koszulTwist_comp (G : InternalGrading R M) (q q' : ℤ) :
    koszulTwist G q ∘ₗ koszulTwist G q' = koszulTwist G (q + q') := by
  refine DirectSum.decompose_lhom_ext (ℳ := G.piece) fun e => ?_
  ext x
  have hx : (x : M) ∈ G.piece e := Submodule.coe_mem x
  have : koszulTwist G q (koszulTwist G q' (x : M)) = koszulTwist G (q + q') (x : M) := by
    rw [koszulTwist_apply_of_mem G hx q', map_smul, koszulTwist_apply_of_mem G hx q,
      koszulTwist_apply_of_mem G hx (q + q'), smul_smul]
    congr 1
    rw [← Int.cast_mul, ← Units.val_mul, ← Int.negOnePow_add, add_mul, add_comm]
  simpa [LinearMap.comp_apply] using this

/-- The Koszul twist of an even parameter is the identity. -/
@[simp]
theorem InternalGrading.koszulTwist_two_mul (G : InternalGrading R M) (q : ℤ) :
    koszulTwist G (2 * q) = LinearMap.id := by
  refine DirectSum.decompose_lhom_ext (ℳ := G.piece) fun e => ?_
  ext x
  have hx : (x : M) ∈ G.piece e := Submodule.coe_mem x
  have : koszulTwist G (2 * q) (x : M) = (x : M) := by
    rw [koszulTwist_apply_of_mem G hx (2 * q), mul_assoc, Int.negOnePow_two_mul]
    simp
  simpa [LinearMap.comp_apply] using this

/-- The Koszul twist of parameter two is the identity. -/
@[simp]
theorem InternalGrading.koszulTwist_two (G : InternalGrading R M) :
    koszulTwist G 2 = LinearMap.id := by
  simpa using koszulTwist_two_mul G 1

/-- The Koszul twist of any parameter is an involution. -/
@[simp]
theorem InternalGrading.koszulTwist_comp_self (G : InternalGrading R M) (q : ℤ) :
    koszulTwist G q ∘ₗ koszulTwist G q = LinearMap.id := by
  rw [koszulTwist_comp, ← two_mul, koszulTwist_two_mul]

/-- The Koszul twist of any parameter is an involution, pointwise. -/
@[simp]
theorem InternalGrading.koszulTwist_koszulTwist (G : InternalGrading R M) (q : ℤ) (x : M) :
    koszulTwist G q (koszulTwist G q x) = x := by
  have h := LinearMap.congr_fun (koszulTwist_comp_self G q) x
  rwa [LinearMap.comp_apply, LinearMap.id_apply] at h

/-- The Koszul twist only depends on the parity of its parameter; in particular, negating the
parameter does not change it. -/
@[simp]
theorem InternalGrading.koszulTwist_neg (G : InternalGrading R M) (q : ℤ) :
    koszulTwist G (-q) = koszulTwist G q := by
  rw [← LinearMap.comp_id (koszulTwist G (-q)), ← koszulTwist_comp_self G q,
    ← LinearMap.comp_assoc, koszulTwist_comp, neg_add_cancel, koszulTwist_zero,
    LinearMap.id_comp]

namespace LinearMap.IsHomogeneous

variable {N : Type w} [AddCommMonoid N] [Module R N]

/-- A homogeneous linear map of degree `r` commutes pointwise with the Koszul twist of
parameter `q` up to the scalar `(-1)^(q * r)`. -/
theorem koszulTwist_apply {G : InternalGrading R M} {H : InternalGrading R N}
    {f : M →ₗ[R] N} {r : ℤ} (hf : LinearMap.IsHomogeneous f G.piece H.piece r) (q : ℤ) (x : M) :
    H.koszulTwist q (f x) = (((q * r).negOnePow : ℤ) : R) • f (G.koszulTwist q x) := by
  induction x using DirectSum.Decomposition.inductionOn G.piece with
  | zero => simp
  | @homogeneous p x =>
    rw [H.koszulTwist_apply_of_mem (hf.map_mem x.2) q,
      G.koszulTwist_apply_of_mem x.2 q, map_smul, smul_smul]
    congr 1
    rw [← Int.cast_mul, ← Units.val_mul, ← Int.negOnePow_add]
    congr 2
    ring_nf
  | add x y hx hy => simp [map_add, hx, hy, smul_add]

/-- A homogeneous linear map of degree `r` commutes with the Koszul twist of parameter `q` up to
the scalar `(-1)^(q * r)`. This is the operator form of the sign acquired by moving a degree-`r`
map past a homogeneous input. The sign acts through its central scalar endomorphism, so this
formula also applies over a noncommutative ring. -/
theorem koszulTwist_comp {G : InternalGrading R M} {H : InternalGrading R N}
    {f : M →ₗ[R] N} {r : ℤ} (hf : LinearMap.IsHomogeneous f G.piece H.piece r) (q : ℤ) :
    H.koszulTwist q ∘ₗ f =
      Module.End.smulLeft (((q * r).negOnePow : ℤ) : R) (Set.intCast_mem_center R _) ∘ₗ
        (f ∘ₗ G.koszulTwist q) := by
  ext x
  simpa only [LinearMap.comp_apply, Module.End.smulLeft_apply] using hf.koszulTwist_apply q x

/-- Over a commutative ring, the Koszul compatibility of a homogeneous map is a scalar multiple
of the composition with the source twist. -/
theorem koszulTwist_comp_eq_smul {R : Type u} [CommRing R] {M : Type v} {N : Type w}
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    {G : InternalGrading R M} {H : InternalGrading R N} {f : M →ₗ[R] N} {r : ℤ}
    (hf : LinearMap.IsHomogeneous f G.piece H.piece r) (q : ℤ) :
    H.koszulTwist q ∘ₗ f = (((q * r).negOnePow : ℤ) : R) • (f ∘ₗ G.koszulTwist q) := by
  simpa only [Module.End.smulLeft_eq, LinearMap.smul_comp, LinearMap.id_comp] using
    hf.koszulTwist_comp q

end LinearMap.IsHomogeneous

/-- Evaluation of `twistedTuple` on an index inside the twisted interval `[a, a + p)`. -/
@[simp]
theorem InternalGrading.twistedTuple_apply_of_mem_Ico (G : InternalGrading R M) (q : ℤ)
    {n : ℕ} (x : Fin n → M) (a p : ℕ) (i : Fin n) (hi : a ≤ i.val ∧ i.val < a + p) :
    twistedTuple G q x a p i = koszulTwist G q (x i) :=
  ite_eq_left hi

/-- Evaluation of `twistedTuple` on an index outside the twisted interval `[a, a + p)`. -/
@[simp]
theorem InternalGrading.twistedTuple_apply_of_not_mem_Ico (G : InternalGrading R M) (q : ℤ)
    {n : ℕ} (x : Fin n → M) (a p : ℕ) (i : Fin n) (hi : ¬(a ≤ i.val ∧ i.val < a + p)) :
    twistedTuple G q x a p i = x i :=
  ite_eq_right hi

/-- Unfolding of `twistedTuple` as a branch on membership in `[a, a + p)`. -/
@[simp]
theorem InternalGrading.twistedTuple_apply (G : InternalGrading R M) (q : ℤ) {n : ℕ}
    (x : Fin n → M) (a p : ℕ) (i : Fin n) :
    twistedTuple G q x a p i =
      if a ≤ i.val ∧ i.val < a + p then koszulTwist G q (x i) else x i := by
  split_ifs with h
  · exact twistedTuple_apply_of_mem_Ico G q x a p i h
  · exact twistedTuple_apply_of_not_mem_Ico G q x a p i h

/-- Two twistings of the same tuple agree at an index lying in both twisted intervals or in
neither. -/
theorem InternalGrading.twistedTuple_apply_eq_twistedTuple_apply (G : InternalGrading R M)
    (q : ℤ) {n : ℕ} (x : Fin n → M) {a p a' p' : ℕ} (i : Fin n)
    (h : a ≤ i.val ∧ i.val < a + p ↔ a' ≤ i.val ∧ i.val < a' + p') :
    twistedTuple G q x a p i = twistedTuple G q x a' p' i := by
  by_cases hi : a ≤ i.val ∧ i.val < a + p
  · rw [twistedTuple_apply_of_mem_Ico G q x a p i hi,
      twistedTuple_apply_of_mem_Ico G q x a' p' i (h.1 hi)]
  · rw [twistedTuple_apply_of_not_mem_Ico G q x a p i hi,
      twistedTuple_apply_of_not_mem_Ico G q x a' p' i (mt h.2 hi)]

/-- A degree-zero homogeneous linear map commutes with twisting a consecutive block of a tuple. -/
theorem LinearMap.IsHomogeneous.twistedTuple_map {N : Type w} [AddCommMonoid N] [Module R N]
    {G : InternalGrading R M} {H : InternalGrading R N} {f : M →ₗ[R] N}
    (hf : LinearMap.IsHomogeneous f G.piece H.piece 0) (q : ℤ) {n : ℕ}
    (x : Fin n → M) (a p : ℕ) :
    H.twistedTuple q (fun i ↦ f (x i)) a p = fun i ↦ f (G.twistedTuple q x a p i) := by
  funext i
  simp only [InternalGrading.twistedTuple_apply]
  split_ifs with h
  · simpa using hf.koszulTwist_apply q (x i)
  · rfl

/-- Twisting an empty interval leaves the tuple unchanged. -/
@[simp]
theorem InternalGrading.twistedTuple_zero_length (G : InternalGrading R M) (q : ℤ) {n : ℕ}
    (x : Fin n → M) (a : ℕ) : twistedTuple G q x a 0 = x := by
  funext i
  exact twistedTuple_apply_of_not_mem_Ico G q x a 0 i (by omega)

/-- The Koszul twist of parameter zero leaves every letter of the tuple unchanged. -/
@[simp]
theorem InternalGrading.twistedTuple_zero_twist (G : InternalGrading R M) {n : ℕ}
    (x : Fin n → M) (a p : ℕ) : twistedTuple G 0 x a p = x := by
  funext i
  simp [twistedTuple]

end KoszulTwistLemmas

namespace InternalGrading

section QuadraticTwist

variable {R : Type u} {M : Type v}
  [CommRing R] [AddCommMonoid M] [Module R M]

/-- The quadratic sign exponent attached to degree `p`, namely the generalized binomial
coefficient `p choose 2`. -/
def quadraticExponent (p : ℤ) : ℤ := Ring.choose p 2

/-- The quadratic exponent vanishes in degree zero. -/
@[simp]
theorem quadraticExponent_zero : quadraticExponent 0 = 0 := by
  norm_num [quadraticExponent]

/-- The quadratic exponent turns addition into addition plus the bilinear cross term. -/
theorem quadraticExponent_add (p q : ℤ) :
    quadraticExponent (p + q) = quadraticExponent p + quadraticExponent q + p * q := by
  rw [quadraticExponent, quadraticExponent, quadraticExponent,
    Ring.add_choose_eq 2 (Commute.all _ _)]
  norm_num [Finset.antidiagonal]
  ring

/-- The signs associated to the quadratic exponent differ under addition by the Koszul sign. -/
theorem negOnePow_quadraticExponent_add (p q : ℤ) :
    (quadraticExponent (p + q)).negOnePow =
      (p * q).negOnePow * (quadraticExponent p).negOnePow *
        (quadraticExponent q).negOnePow := by
  rw [quadraticExponent_add, Int.negOnePow_add, Int.negOnePow_add]
  ac_rfl

/-- The product of three quadratic signs reduces to the bilinear Koszul sign. -/
theorem negOnePow_quadraticExponent_cancel (p r : ℤ) :
    (quadraticExponent p).negOnePow *
        (quadraticExponent r).negOnePow *
        (quadraticExponent (r + p)).negOnePow = (p * r).negOnePow := by
  rw [negOnePow_quadraticExponent_add]
  calc
    _ = (r * p).negOnePow *
        ((quadraticExponent p).negOnePow *
          (quadraticExponent p).negOnePow) *
        ((quadraticExponent r).negOnePow *
          (quadraticExponent r).negOnePow) := by ac_rfl
    _ = (p * r).negOnePow := by rw [Int.units_mul_self, Int.units_mul_self, mul_one, mul_one,
      mul_comm r p]

/-- The quadratic signs of two negated degrees multiply with the Koszul composition sign. -/
theorem negOnePow_quadraticExponent_neg_add (s t : ℤ) :
    (quadraticExponent (-t)).negOnePow *
        (quadraticExponent (-s)).negOnePow =
      (s * t).negOnePow * (quadraticExponent (-(t + s))).negOnePow := by
  rw [neg_add, negOnePow_quadraticExponent_add, neg_mul_neg,
    mul_comm t s]
  rw [← mul_assoc, ← mul_assoc, Int.units_mul_self, one_mul]

/-- The quadratic twist multiplies the degree-`p` component by `(-1) ^ (p choose 2)`.

Transporting the ordinary opposite multiplication through this involution produces the
Koszul-signed opposite multiplication. -/
noncomputable def quadraticTwist (G : InternalGrading R M) : M →ₗ[R] M :=
  DirectSum.coeLinearMap (fun p => G.piece p) ∘ₗ
    DirectSum.toModule R ℤ (⨁ p : ℤ, G.piece p)
      (fun p => (((quadraticExponent p).negOnePow : ℤ) : R) •
        DirectSum.lof R ℤ (fun p => G.piece p) p) ∘ₗ
    (DirectSum.decomposeLinearEquiv (ℳ := G.piece)).toLinearMap

/-- On a homogeneous element of degree `p`, the quadratic twist is multiplication by
`(-1) ^ (p choose 2)`. -/
theorem quadraticTwist_apply_of_mem (G : InternalGrading R M) {x : M} {p : ℤ}
    (hx : x ∈ G.piece p) :
    G.quadraticTwist x = (((quadraticExponent p).negOnePow : ℤ) : R) • x := by
  rw [quadraticTwist]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    DirectSum.decomposeLinearEquiv_apply]
  rw [DirectSum.decompose_of_mem (ℳ := G.piece) hx,
    ← DirectSum.lof_eq_of R ℤ (fun i : ℤ => G.piece i)]
  simp [DirectSum.toModule_lof]

/-- The quadratic twist preserves every homogeneous piece. -/
theorem quadraticTwist_mem_piece (G : InternalGrading R M) {x : M} {p : ℤ}
    (hx : x ∈ G.piece p) : G.quadraticTwist x ∈ G.piece p := by
  rw [G.quadraticTwist_apply_of_mem hx]
  exact Submodule.smul_mem _ _ hx

/-- Applying the quadratic twist twice is the identity. -/
theorem quadraticTwist_involutive (G : InternalGrading R M) :
    Function.Involutive G.quadraticTwist :=
  fun x => by
    have hmaps : G.quadraticTwist ∘ₗ G.quadraticTwist = LinearMap.id := by
      apply G.linearMap_ext
      intro p y hy
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [G.quadraticTwist_apply_of_mem hy, map_smul, G.quadraticTwist_apply_of_mem hy,
        smul_smul]
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
      simp
    exact LinearMap.congr_fun hmaps x

/-- The quadratic twist as a linear involution. -/
noncomputable def quadraticTwistEquiv (G : InternalGrading R M) : M ≃ₗ[R] M :=
  LinearEquiv.ofInvolutive G.quadraticTwist G.quadraticTwist_involutive

@[simp]
theorem quadraticTwistEquiv_apply (G : InternalGrading R M) (x : M) :
    G.quadraticTwistEquiv x = G.quadraticTwist x := by
  exact congr_fun (LinearEquiv.coe_ofInvolutive G.quadraticTwist
    G.quadraticTwist_involutive) x

@[simp]
theorem quadraticTwistEquiv_symm_apply (G : InternalGrading R M) (x : M) :
    G.quadraticTwistEquiv.symm x = G.quadraticTwist x := by
  rfl

end QuadraticTwist

end InternalGrading

end TauCeti
end CanonicalSource47

section CanonicalSource48
/- Source: TauCeti/Algebra/Module/GradedModule/Finsupp.lean -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Grading finitely supported functions by assigned degrees

For an arbitrary assignment `g : I → ℤ`, `InternalGrading.finsupp A g` grades the free
`A`-module on `I` by placing its `i`-th basis vector in degree `g i`. A homogeneous element
has support in a single fibre of `g`. No finiteness or injectivity of `g` is required.

The internal direct sum gives every finitely supported function a unique finite homogeneous
decomposition, including when several basis vectors have the same degree. This construction
also applies after a linear change of coordinates, via `InternalGrading.map`.

The construction uses Mathlib's `Finsupp.supported` submodules and
`DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top`.
-/


namespace TauCeti.InternalGrading

variable (A : Type*) [Ring A] {I : Type*} (g : I → ℤ)

/-- The internal grading of the free module on `I` assigning its `i`-th basis vector
degree `g i`. The degree-`p` piece consists of functions supported in the fibre of `p`. -/
noncomputable def finsupp : InternalGrading A (I →₀ A) where
  piece p := Finsupp.supported A A {i | g i = p}
  isInternal := by
    classical
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · intro p
      dsimp only
      refine (Finsupp.disjoint_supported_supported (M := A) (R := A)
        (s := {i | g i = p}) (t := {i | g i ≠ p})
        (Set.disjoint_left.mpr fun _ hi hni => hni hi)).mono_right ?_
      refine iSup_le fun q => iSup_le fun hqp => Finsupp.supported_mono ?_
      intro i hi
      exact fun hip => hqp (hi.symm.trans hip)
    · rw [← Finsupp.supported_iUnion]
      have hcover : (⋃ p : ℤ, {i | g i = p}) = Set.univ := by
        ext i
        simp
      rw [hcover, Finsupp.supported_univ]

/-- The homogeneous piece is the supported submodule on the corresponding degree fibre. -/
theorem finsupp_piece (p : ℤ) :
    (finsupp A g).piece p = Finsupp.supported A A {i | g i = p} := (rfl)

variable {A g}

/-- A finitely supported function has degree `p` exactly when every nonzero coordinate
has assigned degree `p`. -/
@[simp]
theorem mem_finsupp_piece_iff {p : ℤ} {c : I →₀ A} :
    c ∈ (finsupp A g).piece p ↔ ∀ i, c i ≠ 0 → g i = p := by
  rw [finsupp_piece]
  simp [Finsupp.mem_supported, Set.subset_def]

/-- A single coordinate is homogeneous in its assigned degree, including a zero coefficient. -/
theorem single_mem_finsupp_piece (i : I) (a : A) :
    Finsupp.single i a ∈ (finsupp A g).piece (g i) := by
  rw [finsupp_piece]
  exact Finsupp.single_mem_supported A a rfl

/-- A single coordinate belongs to a homogeneous piece precisely when its coefficient
vanishes or its assigned degree is that of the piece. -/
theorem single_mem_finsupp_piece_iff (i : I) (a : A) (p : ℤ) :
    Finsupp.single i a ∈ (finsupp A g).piece p ↔ a = 0 ∨ g i = p := by
  classical
  rw [mem_finsupp_piece_iff]
  constructor
  · intro h
    by_cases ha : a = 0
    · exact Or.inl ha
    · exact Or.inr (h i (by simpa using ha))
  · rintro (rfl | hp) j hj
    · simp at hj
    · by_cases hji : j = i
      · simpa [hji] using hp
      · simp [hji] at hj

end TauCeti.InternalGrading
end CanonicalSource48

section CanonicalSource49
/- Source: TauCeti/Algebra/Module/GradedModule/Quotient.lean -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Gradings of homogeneous submodules and of their quotients

Let `G` be an internal indexed grading of an `R`-module `M`, and let `U` be a submodule which is
homogeneous in Mathlib's sense `SetLike.IsHomogeneous`: it contains every homogeneous component
of each of its elements.  Then `U` and `M ⧸ U` inherit internal gradings.

* On `U`, the degree-`p` piece is the part of `U` lying in `G.piece p`.
* On `M ⧸ U`, the degree-`p` piece is the image of `G.piece p` under the quotient map.  The
  images span because the quotient map is surjective, and they are independent because an
  element of `U` is the sum of its homogeneous components, all of which lie in `U`.

In both cases the homogeneous projections are those of `M`, transported along the inclusion and
the quotient map respectively.  Combining the two gives the grading of a subquotient, such as the
cohomology `ker d ⧸ im d` of a differential of degree one.

The submodule may be over a larger semiring `S` than the semiring `R` of the grading; it and,
for rings, the quotient by it then inherit gradings by `R`-submodules through scalar restriction.

The kernel of a homogeneous linear map is homogeneous
(`TauCeti.LinearMap.IsHomogeneous.isHomogeneous_ker`), so it inherits a grading in the same way.
The map may be linear over a larger ring `S` than the ring `R` of the grading, as for a
differential over a polynomial ring whose variables move the degree; the kernel is then an
`S`-module graded by `R`-submodules.

## Main definitions

* `TauCeti.InternalGrading.submodule`: the grading of a homogeneous submodule.
* `TauCeti.InternalGrading.ker`: the grading of the kernel of a homogeneous linear map.
* `TauCeti.InternalGrading.quotient`: the grading of the quotient by a homogeneous submodule.

## Main results

* `TauCeti.InternalGrading.coe_decompose_submodule`: homogeneous projection in a homogeneous
  submodule is homogeneous projection in the ambient module.
* `TauCeti.InternalGrading.mem_ker_piece`: an element of the kernel of a homogeneous map is
  homogeneous exactly when it is homogeneous in the source.
* `TauCeti.InternalGrading.decompose_quotient_mk`: homogeneous projection commutes with the
  quotient map.
* `TauCeti.InternalGrading.isHomogeneous_mkQ`: the quotient map has degree zero.
-/


open DirectSum

namespace TauCeti.InternalGrading

variable {R M : Type*} {ι : Type} [DecidableEq ι]

section Span

variable [Semiring R] [AddCommMonoid M] [Module R M]

/-- A submodule spanned by homogeneous elements is homogeneous. -/
theorem isHomogeneous_span (G : InternalGrading R M ι) (s : Set M)
    (hs : ∀ x ∈ s, ∃ p, x ∈ G.piece p) :
    SetLike.IsHomogeneous G.piece (Submodule.span R s) := by
  classical
  intro q x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp⟩ := hs x hx
    by_cases hpq : p = q
    · subst q
      rw [decompose_of_mem_same G.piece hp]
      exact Submodule.subset_span hx
    · rw [decompose_of_mem_ne G.piece hp hpq]
      exact Submodule.zero_mem _
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa using Submodule.add_mem _ ihx ihy
  | smul r x hx ih =>
    simpa only [decompose_smul, DirectSum.smul_apply, SetLike.val_smul] using
      Submodule.smul_mem _ r ih

end Span

section Submodule

variable {S : Type*} [Semiring R] [Semiring S] [SMul R S]
  [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
  (G : InternalGrading R M ι) (U : Submodule S M) (hU : SetLike.IsHomogeneous G.piece U)

include hU in
/-- The internal grading of a homogeneous `S`-submodule: its degree-`p` piece consists of the
elements lying in the degree-`p` piece of the ambient `R`-grading. -/
noncomputable def submodule : InternalGrading R U ι where
  piece p := (G.piece p).comap (U.subtype.restrictScalars R)
  isInternal := DirectSum.isInternal_comap G.piece _ (U.subtype.restrictScalars R)
    Subtype.val_injective
    (fun _ _ ↦ Iff.rfl) fun p x ↦ ⟨⟨_, hU p x.2⟩, rfl⟩

@[simp]
theorem submodule_piece (p : ι) :
    (G.submodule U hU).piece p = (G.piece p).comap (U.subtype.restrictScalars R) :=
  (rfl)

theorem mem_submodule_piece {p : ι} {x : U} :
    x ∈ (G.submodule U hU).piece p ↔ (x : M) ∈ G.piece p :=
  Iff.rfl

/-- Homogeneous projection in a homogeneous submodule is homogeneous projection in the ambient
module. -/
@[simp]
theorem coe_decompose_submodule (p : ι) (x : U) :
    ((decompose (G.submodule U hU).piece x p : U) : M) = decompose G.piece (x : M) p :=
  DirectSum.map_decompose_restrict G.piece (G.submodule U hU).piece (U.subtype.restrictScalars R)
    (fun _ _ ↦ Iff.rfl) p x

/-- The inclusion of a homogeneous submodule has degree zero. -/
theorem isHomogeneous_subtype [AddMonoid ι] :
    LinearMap.IsHomogeneous U.subtype (G.submodule U hU).piece G.piece 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by simpa using hx

end Submodule

section Ker

variable [AddRightCancelMonoid ι]

variable {S N : Type*} [Semiring R] [Semiring S] [SMul R S]
  [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommMonoid N] [Module R N] [Module S N]
  (G : InternalGrading R M ι) {H : InternalGrading R N ι} {f : M →ₗ[S] N} {r : ι}
  (hf : LinearMap.IsHomogeneous f G.piece H.piece r)

include hf in
/-- The internal grading of the kernel of a homogeneous linear map: its degree-`p` piece consists
of the elements of the kernel lying in the degree-`p` piece of `M`. -/
noncomputable def ker : InternalGrading R (_root_.LinearMap.ker f) ι :=
  G.submodule (_root_.LinearMap.ker f) hf.isHomogeneous_ker

/-- An element of the kernel of `f` is homogeneous of degree `p` exactly when it is homogeneous of
degree `p` in `M`. -/
@[simp]
theorem mem_ker_piece {p : ι} {z : _root_.LinearMap.ker f} :
    z ∈ (G.ker hf).piece p ↔ (z : M) ∈ G.piece p :=
  G.mem_submodule_piece (_root_.LinearMap.ker f) hf.isHomogeneous_ker

/-- Homogeneous projection in the kernel of `f` is homogeneous projection in `M`. -/
@[simp]
theorem coe_decompose_ker (p : ι) (z : _root_.LinearMap.ker f) :
    ((decompose (G.ker hf).piece z p : _root_.LinearMap.ker f) : M) =
      decompose G.piece (z : M) p :=
  G.coe_decompose_submodule (_root_.LinearMap.ker f) hf.isHomogeneous_ker p z

end Ker

section Quotient

variable {S : Type*} [Ring R] [Ring S] [SMul R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  (G : InternalGrading R M ι) (U : Submodule S M) (hU : SetLike.IsHomogeneous G.piece U)

include hU in
/-- The internal grading of the quotient by a homogeneous `S`-submodule: its degree-`p` piece is
the image of the degree-`p` piece of `M`. -/
noncomputable def quotient : InternalGrading R (M ⧸ U) ι where
  piece p := (G.piece p).map (U.mkQ.restrictScalars R)
  isInternal := by
    refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (G.isInternal.submodule_iSupIndep.map_of_ker_inf_iSup_le (U.mkQ.restrictScalars R) ?_) ?_
    · -- Map the internal decomposition of `U` into the ambient module.
      have hspan := congrArg (Submodule.map (U.subtype.restrictScalars R))
        (G.submodule U hU).isInternal.submodule_iSup_eq_top
      simp only [Submodule.map_iSup, submodule_piece, Submodule.map_comap_eq,
        Submodule.map_top, LinearMap.range_restrictScalars, Submodule.range_subtype] at hspan
      simpa only [LinearMap.ker_restrictScalars, Submodule.ker_mkQ, inf_comm] using
        inf_le_left.trans_eq hspan.symm
    · rw [← Submodule.map_iSup, G.isInternal.submodule_iSup_eq_top, Submodule.map_top,
        LinearMap.range_restrictScalars, Submodule.range_mkQ, Submodule.restrictScalars_top]

@[simp]
theorem quotient_piece (p : ι) :
    (G.quotient U hU).piece p = (G.piece p).map (U.mkQ.restrictScalars R) :=
  (rfl)

/-- An element of the quotient has degree `p` exactly when it is the class of an element of
degree `p`. -/
theorem mem_quotient_piece_iff {p : ι} {y : M ⧸ U} :
    y ∈ (G.quotient U hU).piece p ↔ ∃ x ∈ G.piece p, Submodule.Quotient.mk x = y := by
  simp only [quotient_piece, Submodule.mem_map, LinearMap.restrictScalars_apply,
    Submodule.mkQ_apply]

/-- The class of an element of degree `p` has degree `p`. -/
theorem mk_mem_quotient_piece {p : ι} {x : M} (hx : x ∈ G.piece p) :
    (Submodule.Quotient.mk x : M ⧸ U) ∈ (G.quotient U hU).piece p :=
  (G.mem_quotient_piece_iff U hU).2 ⟨x, hx, rfl⟩

/-- The quotient map by a homogeneous submodule has degree zero. -/
theorem isHomogeneous_mkQ [AddMonoid ι] :
    LinearMap.IsHomogeneous U.mkQ G.piece (G.quotient U hU).piece 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
    simpa using G.mk_mem_quotient_piece U hU hx

/-- Homogeneous projection commutes with the quotient map. -/
@[simp]
theorem decompose_quotient_mk (p : ι) (x : M) :
    (decompose (G.quotient U hU).piece (Submodule.Quotient.mk x : M ⧸ U) p : M ⧸ U) =
      Submodule.Quotient.mk (decompose G.piece x p : M) :=
  (DirectSum.map_decompose_shift G.piece (G.quotient U hU).piece U.mkQ.toAddMonoidHom
    id Function.injective_id (fun _ _ hx ↦ G.mk_mem_quotient_piece U hU hx) p x).symm

end Quotient

end TauCeti.InternalGrading
end CanonicalSource49

section CanonicalSource50
/- Source: TauCeti/RingTheory/SimpleModule/Socle.lean -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The socle of a module

The **socle** of a module is the supremum of its simple submodules.  Mathlib already uses the
submodule `sSup {m | IsSimpleModule R m}` as the object measuring how far a module is from being
semisimple — `IsSemisimpleModule.of_sSup_simples_eq_top` and
`sSup_simples_eq_top_iff_isSemisimpleModule` are stated with it — but does not name it.  This file
names it and records the two properties that pin it down: it is itself semisimple, and its
submodules are exactly the semisimple submodules.  So it is the largest semisimple submodule, and it
is everything exactly when the module is semisimple.

## Main definitions

* `TauCeti.socle`: the supremum of the simple submodules of a module.

## Main results

* `TauCeti.le_socle` and `TauCeti.socle_le`: the defining supremum property.
* `TauCeti.isSemisimpleModule_socle`: the socle is a semisimple module.
* `TauCeti.le_socle_iff_isSemisimpleModule`: a submodule lies in the socle exactly when it is
  semisimple, so the socle is the largest semisimple submodule.
* `TauCeti.socle_eq_top_iff`: the socle is everything exactly for a semisimple module.
-/


namespace TauCeti

variable (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]

/-- The socle of a module: the supremum of its simple submodules.  It is the largest semisimple
submodule, by `TauCeti.isSemisimpleModule_socle` and `TauCeti.le_socle_iff_isSemisimpleModule`. -/
def socle : Submodule R M :=
  sSup {m : Submodule R M | IsSimpleModule R m}

variable {R M}

/-- Every simple submodule lies in the socle. -/
theorem le_socle {m : Submodule R M} (hm : IsSimpleModule R m) : m ≤ socle R M :=
  le_sSup hm

/-- A submodule containing every simple submodule contains the socle. -/
theorem socle_le {N : Submodule R M} (h : ∀ m : Submodule R M, IsSimpleModule R m → m ≤ N) :
    socle R M ≤ N :=
  sSup_le h

/-- **The socle is semisimple.** -/
instance isSemisimpleModule_socle : IsSemisimpleModule R (socle R M) := by
  rw [socle, sSup_eq_iSup]
  exact isSemisimpleModule_biSup_of_isSemisimpleModule_submodule
    fun m (_ : IsSimpleModule R m) ↦ inferInstance

/-- **A submodule lies in the socle exactly when it is semisimple**, so the socle is the largest
semisimple submodule. -/
theorem le_socle_iff_isSemisimpleModule {N : Submodule R M} :
    N ≤ socle R M ↔ IsSemisimpleModule R N := by
  refine ⟨fun h ↦ .of_injective _ (Submodule.inclusion_injective h), fun _ ↦ ?_⟩
  rw [← N.map_subtype_top, ← IsSemisimpleModule.sSup_simples_eq_top R N,
    Submodule.map_le_iff_le_comap]
  refine sSup_le fun m (_ : IsSimpleModule R m) ↦ Submodule.map_le_iff_le_comap.1 (le_socle ?_)
  exact .congr (m.equivMapOfInjective _ N.subtype_injective).symm

/-- The socle is everything exactly for a semisimple module. -/
theorem socle_eq_top_iff : socle R M = ⊤ ↔ IsSemisimpleModule R M :=
  sSup_simples_eq_top_iff_isSemisimpleModule

/-- The socle of a semisimple module is everything. -/
@[simp]
theorem socle_eq_top [IsSemisimpleModule R M] : socle R M = ⊤ :=
  socle_eq_top_iff.2 ‹_›

end TauCeti
end CanonicalSource50

section CanonicalSource999
/- Source: HigherSpecht/CommonReferenceTableaux.lean -/



/-!
# Arbitrary reference tableaux in the common harmonic construction

The insertion run depends on the left tableau. Changing the right tableau
therefore relabels its embedded witness and rejection exponent. This file
proves covariance of the literal normalized adjoint-Young vectors, equality
of their full cyclic polynomial submodules, and the simultaneous-decomposition
theorems for every family of reference tableaux.

The transport statements hold for arbitrary Young tableaux; in particular
they hold for all standard right tableaux allowed in the manuscript.
-/

noncomputable section

open TauCeti TauCeti.YoungTableau MvPolynomial Module
open scoped Classical BigOperators

namespace HigherSpecht

/-- Simultaneous relabeling of a tableau and its polynomial conjugates the
adjoint Young operator, hence transports its value by the same permutation. -/
theorem adjointYoungApply_relabel {μ : YoungDiagram} (T : YoungTableau μ)
    (σ : Equiv.Perm (Fin μ.card)) (f : PolynomialRing μ.card ℂ) :
    adjointYoungApply (relabel σ T) (MvPolynomial.rename σ f) =
      MvPolynomial.rename σ (adjointYoungApply T f) := by
  classical
  calc
    adjointYoungApply (relabel σ T) (MvPolynomial.rename σ f) =
        (polynomialRepresentation ℂ μ.card).asAlgebraHom
          (youngSymmetrizerOver ℂ (relabel σ T)) (MvPolynomial.rename σ f) :=
      (asAlgebraHom_youngSymmetrizer_adjoint _ _).symm
    _ = MvPolynomial.rename σ
        ((polynomialRepresentation ℂ μ.card).asAlgebraHom
          (youngSymmetrizerOver ℂ T) f) := by
      rw [youngSymmetrizerOver_relabel]
      simp only [map_mul, Module.End.mul_apply, Representation.asAlgebraHom_single,
        LinearMap.smul_apply, one_smul, polynomialRepresentation_apply,
        MvPolynomial.rename_rename, Equiv.Perm.inv_def, Equiv.symm_comp_self,
        MvPolynomial.rename_id_apply]
    _ = MvPolynomial.rename σ (adjointYoungApply T f) := by
      rw [asAlgebraHom_youngSymmetrizer_adjoint]


private theorem mem_range_trans_perm_apply {k n : ℕ} (e : Fin k ↪ Fin n)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    σ i ∈ Set.range (e.trans σ.toEmbedding) ↔ i ∈ Set.range e := by
  constructor
  · rintro ⟨j, hj⟩
    change σ (e j) = σ i at hj
    exact ⟨j, σ.injective hj⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, rfl⟩

theorem exteriorExponent_trans_perm {k n : ℕ} (e : Fin k ↪ Fin n)
    (σ : Equiv.Perm (Fin n)) (s : ℕ) :
    exteriorExponent (e.trans σ.toEmbedding) s = (exteriorExponent e s).mapDomain σ := by
  ext j
  obtain ⟨i, rfl⟩ := σ.surjective j
  rw [Finsupp.mapDomain_apply_of_injective σ.injective]
  simp only [exteriorExponent, Finsupp.equivFunOnFinite_symm_apply_apply,
    mem_range_trans_perm_apply]

theorem exteriorPart_trans_perm {k n : ℕ} (e : Fin k ↪ Fin n)
    (σ : Equiv.Perm (Fin n)) (b : Fin n →₀ ℕ) :
    exteriorPart (e.trans σ.toEmbedding) (b.mapDomain σ) = (exteriorPart e b).mapDomain σ := by
  ext j
  obtain ⟨i, rfl⟩ := σ.surjective j
  rw [Finsupp.mapDomain_apply_of_injective σ.injective]
  simp only [exteriorPart, Finsupp.equivFunOnFinite_symm_apply_apply,
    mem_range_trans_perm_apply, Finsupp.mapDomain_apply_of_injective σ.injective]

theorem embeddedWitnessAlpha_trans_perm {k n : ℕ} (e : Fin k ↪ Fin n)
    (σ : Equiv.Perm (Fin n)) (a : Fin k →₀ ℕ) (s : ℕ) :
    embeddedWitnessAlpha (e.trans σ.toEmbedding) a s =
      (embeddedWitnessAlpha e a s).mapDomain σ := by
  simp only [embeddedWitnessAlpha, Finsupp.mapDomain_add, exteriorExponent_trans_perm]
  congr 1
  rw [← Finsupp.mapDomain_comp]
  rfl

theorem rename_partial_columnWitness {k n : ℕ} {ν : YoungDiagram}
    {R : Type*} [CommRing R] (U : ↥ν.cells ≃ Fin k) (e : Fin k ↪ Fin n)
    (σ : Equiv.Perm (Fin n)) (s : ℕ) :
    MvPolynomial.rename σ (columnWitness (R := R) (U.toEmbedding.trans e) s) =
      columnWitness (U.toEmbedding.trans (e.trans σ.toEmbedding)) s := by
  rw [← rename_fullColumnWitness_mul_exterior U e s, map_mul,
    MvPolynomial.rename_rename, MvPolynomial.rename_monomial,
    ← exteriorExponent_trans_perm e σ s]
  exact rename_fullColumnWitness_mul_exterior U (e.trans σ.toEmbedding) s

theorem prefixAmbientEmbedding_relabel {μ : YoungDiagram}
    (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (σ : Equiv.Perm (Fin μ.card)) (k : ℕ) (hk : k ≤ μ.card) :
    prefixAmbientEmbedding S (relabel σ T) k hk =
      (prefixAmbientEmbedding S T k hk).trans σ.toEmbedding := by
  apply Function.Embedding.ext
  intro i
  simp only [prefixAmbientEmbedding, Function.Embedding.trans_apply,
    Equiv.coe_toEmbedding, relabel_apply]

theorem transportedBoosted_relabel {μ : YoungDiagram}
    (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (σ : Equiv.Perm (Fin μ.card)) (η : YoungDiagram) :
    transportedBoosted S (relabel σ T) η = (transportedBoosted S T η).mapDomain σ := by
  ext j
  obtain ⟨i, rfl⟩ := σ.surjective j
  rw [Finsupp.mapDomain_apply_of_injective σ.injective]
  simp only [transportedBoosted, Finsupp.equivFunOnFinite_symm_apply_apply,
    relabel_symm_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply]

theorem griffinWitnessAlpha_relabel {μ : YoungDiagram}
    (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (σ : Equiv.Perm (Fin μ.card)) (k : ℕ) (hk : k ≤ μ.card) (s : ℕ) :
    griffinWitnessAlpha S (relabel σ T) k hk s = (griffinWitnessAlpha S T k hk s).mapDomain σ := by
  simp only [griffinWitnessAlpha, prefixAmbientEmbedding_relabel, embeddedWitnessAlpha_trans_perm]

theorem griffinWitnessRejection_relabel {μ : YoungDiagram}
    (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (σ : Equiv.Perm (Fin μ.card)) (η : YoungDiagram)
    (k : ℕ) (hk : k ≤ μ.card) (s : ℕ) :
    griffinWitnessRejection S (relabel σ T) η k hk s =
      (griffinWitnessRejection S T η k hk s).mapDomain σ := by
  simp only [griffinWitnessRejection, griffinWitnessAlpha_relabel,
    transportedBoosted_relabel, Finsupp.mapDomain_tsub σ.injective]

theorem griffinApolarWitness_relabel {μ : YoungDiagram} {R : Type*} [CommRing R]
    (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (σ : Equiv.Perm (Fin μ.card)) (k : ℕ) (hk : k ≤ μ.card) (s : ℕ) :
    griffinApolarWitness (R := R) S (relabel σ T) k hk s =
      MvPolynomial.rename σ (griffinApolarWitness S T k hk s) := by
  simp only [griffinApolarWitness, prefixAmbientEmbedding_relabel]
  exact (rename_partial_columnWitness
    (insertionFilling (prefixTableau S k hk) (prefixTableau S k hk).toTableau)
    (prefixAmbientEmbedding S T k hk) σ s).symm

theorem exponentFactorial_mapDomain_perm {n : ℕ} (a : Fin n →₀ ℕ)
    (σ : Equiv.Perm (Fin n)) : exponentFactorial (a.mapDomain σ) = exponentFactorial a := by
  exact exponentFactorial_mapDomain σ.toEmbedding a

theorem normalizedOrdinaryDerivative_rename {n : ℕ} (r : Fin n →₀ ℕ)
    (σ : Equiv.Perm (Fin n)) (G : PolynomialRing n ℂ) :
    normalizedOrdinaryDerivative (r.mapDomain σ) (MvPolynomial.rename σ G) =
      MvPolynomial.rename σ (normalizedOrdinaryDerivative r G) := by
  rw [normalizedOrdinaryDerivative, normalizedOrdinaryDerivative,
    exponentFactorial_mapDomain_perm, ← MvPolynomial.rename_monomial,
    ordinaryAction_rename_equiv, map_smul]

/-- The finite witness formula is covariant for every prefix and bound. -/
theorem griffinCommonVector_relabel {μ : YoungDiagram}
    (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (σ : Equiv.Perm (Fin μ.card)) (η : YoungDiagram)
    (k : ℕ) (hk : k ≤ μ.card) (s : ℕ) :
    adjointYoungApply (relabel σ T)
        (normalizedOrdinaryDerivative (griffinWitnessRejection S (relabel σ T) η k hk s)
          (griffinApolarWitness S (relabel σ T) k hk s)) =
      MvPolynomial.rename σ (adjointYoungApply T
        (normalizedOrdinaryDerivative (griffinWitnessRejection S T η k hk s)
          (griffinApolarWitness S T k hk s))) := by
  rw [griffinWitnessRejection_relabel, griffinApolarWitness_relabel,
    normalizedOrdinaryDerivative_rename, adjointYoungApply_relabel]

theorem untruncatedWitnessAlpha_relabel {μ : YoungDiagram}
    (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (σ : Equiv.Perm (Fin μ.card)) (η : YoungDiagram) (k : ℕ) (hk : k ≤ μ.card) :
    untruncatedWitnessAlpha S (relabel σ T) η k hk =
      (untruncatedWitnessAlpha S T η k hk).mapDomain σ := by
  simp only [untruncatedWitnessAlpha, prefixAmbientEmbedding_relabel,
    transportedBoosted_relabel, exteriorPart_trans_perm, Finsupp.mapDomain_add]
  congr 1
  rw [← Finsupp.mapDomain_comp]
  rfl

theorem untruncatedWitnessRejection_relabel {μ : YoungDiagram}
    (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (σ : Equiv.Perm (Fin μ.card)) (η : YoungDiagram) (k : ℕ) (hk : k ≤ μ.card) :
    untruncatedWitnessRejection S (relabel σ T) η k hk =
      (untruncatedWitnessRejection S T η k hk).mapDomain σ := by
  simp only [untruncatedWitnessRejection, untruncatedWitnessAlpha_relabel,
    transportedBoosted_relabel, Finsupp.mapDomain_tsub σ.injective]

theorem untruncatedApolarWitness_relabel {μ : YoungDiagram}
    (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (σ : Equiv.Perm (Fin μ.card)) (η : YoungDiagram) (k : ℕ) (hk : k ≤ μ.card) :
    untruncatedApolarWitness S (relabel σ T) η k hk =
      MvPolynomial.rename σ (untruncatedApolarWitness S T η k hk) := by
  simp only [untruncatedApolarWitness_eq, prefixAmbientEmbedding_relabel,
    transportedBoosted_relabel, exteriorPart_trans_perm,
    map_mul, map_prod, MvPolynomial.rename_monomial]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  exact (rename_columnAlternant σ.toEmbedding
    ((insertionFilling (prefixTableau S k hk) (prefixTableau S k hk).toTableau).toEmbedding.trans
      (prefixAmbientEmbedding S T k hk)) j).symm

/-- The untruncated product-of-Vandermondes formula is equally covariant. -/
theorem untruncatedCommonVector_relabel {μ : YoungDiagram}
    (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (σ : Equiv.Perm (Fin μ.card)) (η : YoungDiagram) (k : ℕ) (hk : k ≤ μ.card) :
    adjointYoungApply (relabel σ T)
        (normalizedOrdinaryDerivative (untruncatedWitnessRejection S (relabel σ T) η k hk)
          (untruncatedApolarWitness S (relabel σ T) η k hk)) =
      MvPolynomial.rename σ (adjointYoungApply T
        (normalizedOrdinaryDerivative (untruncatedWitnessRejection S T η k hk)
          (untruncatedApolarWitness S T η k hk))) := by
  rw [untruncatedWitnessRejection_relabel, untruncatedApolarWitness_relabel,
    normalizedOrdinaryDerivative_rename, adjointYoungApply_relabel]

/-- The same literal finite formula, with its reference tableau explicit. -/
def finiteCommonHarmonicVectorWithTableau {n s : ℕ} (i : FiniteHarmonicIndex n s)
    (T : YoungTableau (YoungDiagram.ofPartition i.part)) : PolynomialRing n ℂ :=
  MvPolynomial.rename (finCongr (YoungDiagram.card_ofPartition i.part))
    (adjointYoungApply T (normalizedOrdinaryDerivative
      (griffinWitnessRejection i.left T i.multiplier (maximalFinitePrefix i)
        (maximalFinitePrefix_le i) s)
      (griffinApolarWitness i.left T (maximalFinitePrefix i) (maximalFinitePrefix_le i) s)))

/-- The same literal untruncated formula, with its reference tableau explicit. -/
def untruncatedCommonHarmonicVectorWithTableau {n : ℕ} (i : UnboundedHarmonicIndex n)
    (T : YoungTableau (YoungDiagram.ofPartition i.part)) : PolynomialRing n ℂ :=
  MvPolynomial.rename (finCongr (YoungDiagram.card_ofPartition i.part))
    (adjointYoungApply T (normalizedOrdinaryDerivative
      (untruncatedWitnessRejection i.left T i.multiplier (maximalUntruncatedPrefix i)
        (maximalUntruncatedPrefix_le i))
      (untruncatedApolarWitness i.left T i.multiplier (maximalUntruncatedPrefix i)
        (maximalUntruncatedPrefix_le i))))

theorem finiteCommonHarmonicVectorWithTableau_canonical {n s : ℕ}
    (i : FiniteHarmonicIndex n s) :
    finiteCommonHarmonicVectorWithTableau i (StandardYoungTableau.rowSuperstandard _).toTableau =
      finiteCommonHarmonicVector i := by
  exact (finiteCommonHarmonicVector_eq_normalized i).symm

theorem untruncatedCommonHarmonicVectorWithTableau_canonical {n : ℕ}
    (i : UnboundedHarmonicIndex n) :
    untruncatedCommonHarmonicVectorWithTableau i (StandardYoungTableau.rowSuperstandard _).toTableau =
      untruncatedCommonHarmonicVector i := by
  exact (untruncatedCommonHarmonicVector_eq_normalized i).symm

private theorem rename_permCongr {n m : ℕ} (e : Fin n ≃ Fin m)
    (σ : Equiv.Perm (Fin n)) (p : PolynomialRing n ℂ) :
    MvPolynomial.rename (e.permCongr σ) (MvPolynomial.rename e p) =
      MvPolynomial.rename e (MvPolynomial.rename σ p) := by
  simp only [MvPolynomial.rename_rename]
  apply congrArg (fun f : Fin n → Fin m => MvPolynomial.rename (R := ℂ) f p)
  funext i
  simp only [Function.comp_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply]

/-- Changing the reference tableau relabels the finite common generator. -/
theorem finiteCommonHarmonicVectorWithTableau_covariant {n s : ℕ}
    (i : FiniteHarmonicIndex n s) (T₀ T₁ : YoungTableau (YoungDiagram.ofPartition i.part)) :
    finiteCommonHarmonicVectorWithTableau i T₁ =
      MvPolynomial.rename
        ((finCongr (YoungDiagram.card_ofPartition i.part)).permCongr (relabelPerm T₀ T₁))
        (finiteCommonHarmonicVectorWithTableau i T₀) := by
  have h := griffinCommonVector_relabel i.left T₀ (relabelPerm T₀ T₁) i.multiplier
    (maximalFinitePrefix i) (maximalFinitePrefix_le i) s
  rw [relabel_relabelPerm] at h
  unfold finiteCommonHarmonicVectorWithTableau
  rw [rename_permCongr]
  exact congrArg (MvPolynomial.rename (finCongr (YoungDiagram.card_ofPartition i.part))) h

/-- Changing the reference tableau relabels the untruncated common generator. -/
theorem untruncatedCommonHarmonicVectorWithTableau_covariant {n : ℕ}
    (i : UnboundedHarmonicIndex n) (T₀ T₁ : YoungTableau (YoungDiagram.ofPartition i.part)) :
    untruncatedCommonHarmonicVectorWithTableau i T₁ =
      MvPolynomial.rename
        ((finCongr (YoungDiagram.card_ofPartition i.part)).permCongr (relabelPerm T₀ T₁))
        (untruncatedCommonHarmonicVectorWithTableau i T₀) := by
  have h := untruncatedCommonVector_relabel i.left T₀ (relabelPerm T₀ T₁) i.multiplier
    (maximalUntruncatedPrefix i) (maximalUntruncatedPrefix_le i)
  rw [relabel_relabelPerm] at h
  unfold untruncatedCommonHarmonicVectorWithTableau
  rw [rename_permCongr]
  exact congrArg (MvPolynomial.rename (finCongr (YoungDiagram.card_ofPartition i.part))) h

theorem cyclicPolynomialCopy_rename {n : ℕ} (σ : Equiv.Perm (Fin n))
    (p : PolynomialRing n ℂ) :
    cyclicPolynomialCopy (MvPolynomial.rename σ p) = cyclicPolynomialCopy p := by
  unfold cyclicPolynomialCopy
  congr 1
  ext q
  constructor
  · rintro ⟨τ, rfl⟩
    refine ⟨τ * σ, ?_⟩
    change MvPolynomial.rename (τ * σ) p =
      MvPolynomial.rename τ (MvPolynomial.rename σ p)
    rw [MvPolynomial.rename_rename]
    rfl
  · rintro ⟨τ, rfl⟩
    refine ⟨τ * σ⁻¹, ?_⟩
    change MvPolynomial.rename (τ * σ⁻¹) (MvPolynomial.rename σ p) =
      MvPolynomial.rename τ p
    rw [MvPolynomial.rename_rename]
    apply congrArg (fun f : Fin n → Fin n => MvPolynomial.rename (R := ℂ) f p)
    funext i
    change τ (σ.symm (σ i)) = τ i
    rw [Equiv.symm_apply_apply]

def finiteCommonHarmonicCopyWithTableau {n s : ℕ} (i : FiniteHarmonicIndex n s)
    (T : YoungTableau (YoungDiagram.ofPartition i.part)) : Submodule ℂ (PolynomialRing n ℂ) :=
  cyclicPolynomialCopy (finiteCommonHarmonicVectorWithTableau i T)

def untruncatedCommonHarmonicCopyWithTableau {n : ℕ} (i : UnboundedHarmonicIndex n)
    (T : YoungTableau (YoungDiagram.ofPartition i.part)) : Submodule ℂ (PolynomialRing n ℂ) :=
  cyclicPolynomialCopy (untruncatedCommonHarmonicVectorWithTableau i T)

/-- Every right tableau gives exactly the same finite cyclic polynomial copy. -/
theorem finiteCommonHarmonicCopyWithTableau_eq {n s : ℕ} (i : FiniteHarmonicIndex n s)
    (T : YoungTableau (YoungDiagram.ofPartition i.part)) :
    finiteCommonHarmonicCopyWithTableau i T = finiteCommonHarmonicCopy i := by
  rw [finiteCommonHarmonicCopyWithTableau,
    finiteCommonHarmonicVectorWithTableau_covariant i
      (StandardYoungTableau.rowSuperstandard _).toTableau T,
    cyclicPolynomialCopy_rename, finiteCommonHarmonicVectorWithTableau_canonical]
  rfl

/-- Every right tableau gives exactly the same untruncated cyclic polynomial copy. -/
theorem untruncatedCommonHarmonicCopyWithTableau_eq {n : ℕ} (i : UnboundedHarmonicIndex n)
    (T : YoungTableau (YoungDiagram.ofPartition i.part)) :
    untruncatedCommonHarmonicCopyWithTableau i T = untruncatedCommonHarmonicCopy i := by
  rw [untruncatedCommonHarmonicCopyWithTableau,
    untruncatedCommonHarmonicVectorWithTableau_covariant i
      (StandardYoungTableau.rowSuperstandard _).toTableau T,
    cyclicPolynomialCopy_rename, untruncatedCommonHarmonicVectorWithTableau_canonical]
  rfl

/-- The full-prefix Springer specialization with an explicit right tableau. -/
def springerCommonHarmonicVectorWithTableau {n : ℕ} (hn : 0 < n)
    (z : SpringerCommonIndex n) (T : YoungTableau (YoungDiagram.ofPartition z.1)) :
    PolynomialRing n ℂ :=
  finiteCommonHarmonicVectorWithTableau (springerCommonFiniteIndex hn z) T

/-- Formula (5.1) for every right tableau: the original insertion witness,
the original rejection counts, and the manuscript's factorial normalization. -/
theorem springerCommonHarmonicVectorWithTableau_literal_formula {n : ℕ} (hn : 0 < n)
    (z : SpringerCommonIndex n) (T : YoungTableau (YoungDiagram.ofPartition z.1)) :
    springerCommonHarmonicVectorWithTableau hn z T =
      MvPolynomial.rename (finCongr (YoungDiagram.card_ofPartition z.1))
        (adjointYoungApply T
          (normalizedOrdinaryDerivative (insertionRejectionExponent z.2 T)
            (higherSpechtWitness z.2 T))) := by
  have full (k : ℕ) (hk : k ≤ (YoungDiagram.ofPartition z.1).card)
      (hfull : k = (YoungDiagram.ofPartition z.1).card) :
      griffinWitnessRejection z.2 T ⊥ k hk n = insertionRejectionExponent z.2 T ∧
        griffinApolarWitness (R := ℂ) z.2 T k hk n = higherSpechtWitness z.2 T := by
    subst k
    exact ⟨griffinWitnessRejection_full z.2 T n, griffinApolarWitness_full z.2 T n⟩
  obtain ⟨hr, hG⟩ := full
    (maximalFinitePrefix (springerCommonFiniteIndex hn z))
    (maximalFinitePrefix_le (springerCommonFiniteIndex hn z))
    ((springerCommonPrefix_full hn z).trans (YoungDiagram.card_ofPartition z.1).symm)
  exact congrArg₂
    (fun r G => MvPolynomial.rename (finCongr (YoungDiagram.card_ofPartition z.1))
      (adjointYoungApply T (normalizedOrdinaryDerivative r G))) hr hG

def springerCommonHarmonicCopyWithTableau {n : ℕ} (hn : 0 < n)
    (z : SpringerCommonIndex n) (T : YoungTableau (YoungDiagram.ofPartition z.1)) :
    Submodule ℂ (PolynomialRing n ℂ) :=
  cyclicPolynomialCopy (springerCommonHarmonicVectorWithTableau hn z T)

/-- The original full-tableau construction gives the same actual Springer
copy for every reference tableau. -/
theorem springerCommonHarmonicCopyWithTableau_eq {n : ℕ} (hn : 0 < n)
    (z : SpringerCommonIndex n) (T : YoungTableau (YoungDiagram.ofPartition z.1)) :
    springerCommonHarmonicCopyWithTableau hn z T = springerCommonHarmonicCopy hn z := by
  exact finiteCommonHarmonicCopyWithTableau_eq (springerCommonFiniteIndex hn z) T

/-- Theorem 5.2 with a fully arbitrary reference tableau in every shape. -/
theorem theorem_5_2_any_right_tableaux (n s : ℕ) (hn : 0 < n) (hs : 0 < s)
    (T : (part : n.Partition) → YoungTableau (YoungDiagram.ofPartition part)) :
    (∀ i : FiniteHarmonicIndex n s,
      IsSpechtPolynomialCopy i.part (finiteCommonHarmonicCopyWithTableau i (T i.part)) ∧
      finiteCommonHarmonicCopyWithTableau i (T i.part) ≤
        homogeneousSubmodule (Fin n) ℂ i.toUnboundedHarmonicIndex.degree) ∧
    iSupIndep (fun i : FiniteHarmonicIndex n s => finiteCommonHarmonicCopyWithTableau i (T i.part)) ∧
    ∀ (lam : YoungDiagram) (hk : lam.card ≤ n), lam.colLen 0 ≤ s →
      ordinaryHarmonics (griffinIdeal ℂ n lam s) =
        ⨆ i : {i : FiniteHarmonicIndex n s // i.toUnboundedHarmonicIndex.eligible lam hk},
          finiteCommonHarmonicCopyWithTableau i.val (T i.val.part) := by
  simpa only [finiteCommonHarmonicCopyWithTableau_eq] using theorem_5_2 n s hn hs

/-- All conclusions of Corollary 5.5 hold for every family of right tableaux. -/
theorem corollary_5_5_any_right_tableaux (n : ℕ) (hn : 0 < n)
    (T : (part : n.Partition) → YoungTableau (YoungDiagram.ofPartition part)) :
    (∀ z : SpringerCommonIndex n,
      IsSpechtPolynomialCopy z.1 (springerCommonHarmonicCopyWithTableau hn z (T z.1)) ∧
      springerCommonHarmonicCopyWithTableau hn z (T z.1) ≤
        homogeneousSubmodule (Fin n) ℂ (cochargeDegree z.2)) ∧
    iSupIndep (fun z : SpringerCommonIndex n =>
      springerCommonHarmonicCopyWithTableau hn z (T z.1)) ∧
    ordinaryHarmonics (untruncatedIdeal ℂ n (columnPartition n)) =
      (⨆ z : SpringerCommonIndex n, springerCommonHarmonicCopyWithTableau hn z (T z.1)) ∧
    ∀ (mu : YoungDiagram) (hmu : mu.card = n),
      ordinaryHarmonics (untruncatedIdeal ℂ n mu) =
        ⨆ z : {z : SpringerCommonIndex n // CatDominates z.2 mu},
          springerCommonHarmonicCopyWithTableau hn z.val (T z.val.1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z
    simpa only [springerCommonHarmonicCopyWithTableau_eq] using
      And.intro (springerCommonHarmonicCopy_isSpecht hn z) (springerCommonHarmonicCopy_degree hn z)
  · simpa only [springerCommonHarmonicCopyWithTableau_eq] using
      springerCommonHarmonicCopies_iSupIndep hn
  · simpa only [springerCommonHarmonicCopyWithTableau_eq] using corollary_5_5_master hn
  · intro mu hmu
    simpa only [springerCommonHarmonicCopyWithTableau_eq] using corollary_5_5_decomposition hn mu hmu

/-- Theorem 6.6 with a fully arbitrary reference tableau in every shape. -/
theorem theorem_6_6_any_right_tableaux (n : ℕ)
    (T : (part : n.Partition) → YoungTableau (YoungDiagram.ofPartition part)) :
    (∀ i : UnboundedHarmonicIndex n,
      IsSpechtPolynomialCopy i.part (untruncatedCommonHarmonicCopyWithTableau i (T i.part)) ∧
      untruncatedCommonHarmonicCopyWithTableau i (T i.part) ≤ homogeneousSubmodule (Fin n) ℂ i.degree) ∧
    iSupIndep (fun i : UnboundedHarmonicIndex n => untruncatedCommonHarmonicCopyWithTableau i (T i.part)) ∧
    (∀ d : ℕ, Set.Finite {i : UnboundedHarmonicIndex n | i.degree = d}) ∧
    ∀ (lam : YoungDiagram) (hk : lam.card ≤ n),
      ordinaryHarmonics (untruncatedIdeal ℂ n lam) =
        ⨆ i : {i : UnboundedHarmonicIndex n // i.eligible lam hk},
          untruncatedCommonHarmonicCopyWithTableau i.val (T i.val.part) := by
  simpa only [untruncatedCommonHarmonicCopyWithTableau_eq] using theorem_6_6 n

end HigherSpecht
end
end CanonicalSource999

section CanonicalSource1001
/- Source: HigherSpecht/ComplexYoungIdeal.lean -/



/-!
# The complex Young ideal is the ordinary Specht representation

The common harmonic copies are constructed from the left ideal generated by
the actual Young symmetrizer.  This file identifies that representation with
the complex scalar extension of the ordinary rational Specht module of the
same shape.

Character orthogonality and the verified Young-image rank formula show that
the symmetrizer has a one-dimensional image in that Specht module.  Any nonzero
vector in this image gives an injective intertwiner from the Young ideal.
The verified equality of dimensions makes it an equivalence.  This applies
also to the empty partition.
-/

noncomputable section

open TauCeti Module

namespace HigherSpecht

variable {n : ℕ}

/-- The Young symmetrizer of shape `part` has rank one on the ordinary
complex Specht module of that shape. -/
theorem complexSpechtYoungImage_finrank (part : n.Partition) :
    finrank ℂ (YoungImage (spechtModuleℂ part).ρ part) = 1 := by
  classical
  have hinv (sigma : Equiv.Perm (Fin n)) :
      spechtChar part sigma⁻¹ = spechtChar part sigma :=
    spechtChar_eq_of_isConj part
      (Equiv.Perm.isConj_iff_cycleType_eq.mpr (Equiv.Perm.cycleType_inv sigma))
  have hchar (sigma : Equiv.Perm (Fin n)) :
      Representation.character (spechtModuleℂ part).ρ sigma = (spechtChar part sigma : ℂ) :=
    character_spechtModuleℂ_intCast part sigma
  have hnorm :
      (∑ sigma : Equiv.Perm (Fin n),
        (spechtChar part sigma : ℂ) * (spechtChar part sigma : ℂ)) =
          (n.factorial : ℂ) := by
    simpa only [character_spechtModuleℂ_intCast, hinv,
      Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] using
      (FDRep.simple_iff_char_is_norm_one (spechtModuleℂ part)).mp inferInstance
  have hdim :=
    Representation.factorial_mul_finrank_range_asAlgebraHom_youngSymmetrizer
      (spechtModuleℂ part).ρ part
  apply Nat.cast_injective (R := ℂ)
  apply mul_left_cancel₀ (show (n.factorial : ℂ) ≠ 0 from
    Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  simpa only [Nat.cast_one, mul_one, YoungImage, hchar, hnorm] using hdim

/-- The concrete complex Young ideal is equivalent to the ordinary complex
Specht representation of the same partition.  The choice of a nonzero image
vector affects this equivalence, but not its source, target, or equivariance. -/
def complexYoungIdealSpechtEquiv (part : n.Partition) :
    Representation.Equiv (YoungIdealRepresentation (K := ℂ) part)
      (spechtModuleℂ part).ρ := by
  classical
  have hex : ∃ v : YoungImage (spechtModuleℂ part).ρ part, v ≠ 0 :=
    (Module.finrank_pos_iff_exists_ne_zero (R := ℂ)).mp (by
      rw [complexSpechtYoungImage_finrank]
      exact Nat.zero_lt_one)
  let v := Classical.choose hex
  have hv : v ≠ 0 := Classical.choose_spec hex
  let f := intertwinerOfYoungImage (spechtModuleℂ part).ρ part v
  have hf : Function.Injective f :=
    intertwinerOfYoungImage_injective (spechtModuleℂ part).ρ part v hv
  have hdim : finrank ℂ (YoungIdeal (K := ℂ) part) =
      finrank ℂ (spechtModuleℂ part) :=
    (part.finrank_span_youngSymmetrizer ℂ).trans (finrank_spechtModuleℂ part).symm
  exact f.ofBijective ⟨hf,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.toLinearMap) hdim).mp hf⟩

/-- In particular, the complex Young-ideal source used by the common-copy
construction is irreducible as a representation of the symmetric group. -/
theorem complexYoungIdealRepresentation_isIrreducible (part : n.Partition) :
    (YoungIdealRepresentation (K := ℂ) part).IsIrreducible := by
  let e := (complexYoungIdealSpechtEquiv part).symm
  exact Representation.isIrreducible_of_linearEquiv e.toLinearEquiv
    (fun g v => Representation.IntertwiningMap.isIntertwining
      (spechtModuleℂ part).ρ (YoungIdealRepresentation (K := ℂ) part)
      e.toIntertwiningMap g v)
    ((FDRep.simple_iff_isIrreducible (spechtModuleℂ part)).mp inferInstance)

end HigherSpecht
end
end CanonicalSource1001

section CanonicalSource1002
/- Source: HigherSpecht/CommonSpechtSemantics.lean -/



/-!
# The common polynomial copies as ordinary complex Specht modules

The Young ideal used to construct each common copy is equivalent to the
ordinary complex Specht module.  This file spells out what that identification
means for the actual polynomial subspaces: their restricted permutation action
is irreducible, and an equivalence identifies its shape.  It also proves the
converse, so the earlier injective-intertwiner predicate retains exactly this
mathematical content.

The three concluding theorems preserve the simultaneous decompositions,
degrees, independence, local finiteness, and arbitrary reference tableaux of
Theorem 5.2, Corollary 5.5, and Theorem 6.6.
-/

noncomputable section

open TauCeti TauCeti.YoungTableau Module MvPolynomial

namespace HigherSpecht

/-- The constructive Young-ideal formulation is equivalent to being an
actual irreducible copy of the ordinary complex Specht module in the given
polynomial subspace.  No finite-dimensional hypothesis is imposed on the
ambient polynomial representation. -/
theorem isSpechtPolynomialCopy_iff_complexSpecht {n : ℕ} (part : n.Partition)
    (W : Submodule ℂ (PolynomialRing n ℂ)) :
    IsSpechtPolynomialCopy part W ↔
      ∃ V : Subrepresentation (polynomialRepresentation ℂ n),
        V.toSubmodule = W ∧ V.toRepresentation.IsIrreducible ∧
          Nonempty (Representation.Equiv (spechtModuleℂ part).ρ V.toRepresentation) := by
  constructor
  · rintro ⟨phi, hphi, hrange⟩
    let E : Representation.Equiv (spechtModuleℂ part).ρ phi.range.toRepresentation :=
      (complexYoungIdealSpechtEquiv part).symm.trans (phi.equivOfRange hphi rfl)
    letI : Representation.IsIrreducible (spechtModuleℂ part).ρ :=
      (FDRep.simple_iff_isIrreducible (spechtModuleℂ part)).mp inferInstance
    exact ⟨phi.range, hrange, irreducible_of_representation_equiv E, ⟨E⟩⟩
  · rintro ⟨V, hV, _, ⟨e⟩⟩
    let E : Representation.Equiv (YoungIdealRepresentation (K := ℂ) part)
        V.toRepresentation := (complexYoungIdealSpechtEquiv part).trans e
    have hval (v : YoungIdeal (K := ℂ) part) :
        (V.subtype.comp E.toIntertwiningMap).toLinearMap v =
          (E v : PolynomialRing n ℂ) := by
      simp only [Representation.IntertwiningMap.toLinearMap_apply,
        Representation.IntertwiningMap.comp_apply,
        Representation.Equiv.coe_toIntertwiningMap, Subrepresentation.coe_subtype]
    refine ⟨V.subtype.comp E.toIntertwiningMap, ?_, ?_⟩
    · intro x y hxy
      apply E.toLinearEquiv.injective
      apply Subtype.ext
      exact (hval x).symm.trans (hxy.trans (hval y))
    · rw [← hV]
      apply le_antisymm
      · rintro p ⟨v, rfl⟩
        rw [hval]
        exact (E v).property
      · intro p hp
        obtain ⟨v, hv⟩ := E.toLinearEquiv.surjective ⟨p, hp⟩
        exact ⟨v, (hval v).trans (congrArg Subtype.val hv)⟩

/-- The full finite simultaneous theorem, with ordinary complex Specht
representations and irreducibility exposed in the conclusion. -/
theorem theorem_5_2_actual_specht (n s : ℕ) (hn : 0 < n) (hs : 0 < s)
    (T : (part : n.Partition) → YoungTableau (YoungDiagram.ofPartition part)) :
    (∀ i : FiniteHarmonicIndex n s,
      (∃ V : Subrepresentation (polynomialRepresentation ℂ n),
        V.toSubmodule = finiteCommonHarmonicCopyWithTableau i (T i.part) ∧
          V.toRepresentation.IsIrreducible ∧
          Nonempty (Representation.Equiv (spechtModuleℂ i.part).ρ V.toRepresentation)) ∧
      finiteCommonHarmonicCopyWithTableau i (T i.part) ≤
        homogeneousSubmodule (Fin n) ℂ i.toUnboundedHarmonicIndex.degree) ∧
    iSupIndep (fun i : FiniteHarmonicIndex n s =>
      finiteCommonHarmonicCopyWithTableau i (T i.part)) ∧
    ∀ (lam : YoungDiagram) (hk : lam.card ≤ n), lam.colLen 0 ≤ s →
      ordinaryHarmonics (griffinIdeal ℂ n lam s) =
        ⨆ i : {i : FiniteHarmonicIndex n s // i.toUnboundedHarmonicIndex.eligible lam hk},
          finiteCommonHarmonicCopyWithTableau i.val (T i.val.part) := by
  obtain ⟨hcopy, hind, hdecomp⟩ := theorem_5_2_any_right_tableaux n s hn hs T
  refine ⟨?_, hind, hdecomp⟩
  intro i
  exact ⟨(isSpechtPolynomialCopy_iff_complexSpecht i.part _).mp (hcopy i).1,
    (hcopy i).2⟩

/-- The full Springer specialization, including the master harmonic
space and every shape of size `n`, as actual irreducible complex Specht copies. -/
theorem corollary_5_5_actual_specht (n : ℕ) (hn : 0 < n)
    (T : (part : n.Partition) → YoungTableau (YoungDiagram.ofPartition part)) :
    (∀ z : SpringerCommonIndex n,
      (∃ V : Subrepresentation (polynomialRepresentation ℂ n),
        V.toSubmodule = springerCommonHarmonicCopyWithTableau hn z (T z.1) ∧
          V.toRepresentation.IsIrreducible ∧
          Nonempty (Representation.Equiv (spechtModuleℂ z.1).ρ V.toRepresentation)) ∧
      springerCommonHarmonicCopyWithTableau hn z (T z.1) ≤
        homogeneousSubmodule (Fin n) ℂ (cochargeDegree z.2)) ∧
    iSupIndep (fun z : SpringerCommonIndex n =>
      springerCommonHarmonicCopyWithTableau hn z (T z.1)) ∧
    ordinaryHarmonics (untruncatedIdeal ℂ n (columnPartition n)) =
      (⨆ z : SpringerCommonIndex n, springerCommonHarmonicCopyWithTableau hn z (T z.1)) ∧
    ∀ (mu : YoungDiagram) (hmu : mu.card = n),
      ordinaryHarmonics (untruncatedIdeal ℂ n mu) =
        ⨆ z : {z : SpringerCommonIndex n // CatDominates z.2 mu},
          springerCommonHarmonicCopyWithTableau hn z.val (T z.val.1) := by
  obtain ⟨hcopy, hind, hmaster, hdecomp⟩ := corollary_5_5_any_right_tableaux n hn T
  refine ⟨?_, hind, hmaster, hdecomp⟩
  intro z
  exact ⟨(isSpechtPolynomialCopy_iff_complexSpecht z.1 _).mp (hcopy z).1,
    (hcopy z).2⟩

/-- The full locally finite untruncated theorem, with no restriction on
`n` and with the ordinary complex Specht equivalence made explicit. -/
theorem theorem_6_6_actual_specht (n : ℕ)
    (T : (part : n.Partition) → YoungTableau (YoungDiagram.ofPartition part)) :
    (∀ i : UnboundedHarmonicIndex n,
      (∃ V : Subrepresentation (polynomialRepresentation ℂ n),
        V.toSubmodule = untruncatedCommonHarmonicCopyWithTableau i (T i.part) ∧
          V.toRepresentation.IsIrreducible ∧
          Nonempty (Representation.Equiv (spechtModuleℂ i.part).ρ V.toRepresentation)) ∧
      untruncatedCommonHarmonicCopyWithTableau i (T i.part) ≤
        homogeneousSubmodule (Fin n) ℂ i.degree) ∧
    iSupIndep (fun i : UnboundedHarmonicIndex n =>
      untruncatedCommonHarmonicCopyWithTableau i (T i.part)) ∧
    (∀ d : ℕ, Set.Finite {i : UnboundedHarmonicIndex n | i.degree = d}) ∧
    ∀ (lam : YoungDiagram) (hk : lam.card ≤ n),
      ordinaryHarmonics (untruncatedIdeal ℂ n lam) =
        ⨆ i : {i : UnboundedHarmonicIndex n // i.eligible lam hk},
          untruncatedCommonHarmonicCopyWithTableau i.val (T i.val.part) := by
  obtain ⟨hcopy, hind, hfinite, hdecomp⟩ := theorem_6_6_any_right_tableaux n T
  refine ⟨?_, hind, hfinite, hdecomp⟩
  intro i
  exact ⟨(isSpechtPolynomialCopy_iff_complexSpecht i.part _).mp (hcopy i).1,
    (hcopy i).2⟩

end HigherSpecht
end
end CanonicalSource1002
