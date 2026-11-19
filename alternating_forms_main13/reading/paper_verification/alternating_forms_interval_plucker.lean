module

public import PaperVerification.AlternatingFormsBandMinors
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Order.Interval.Finset.Fin

/-!
# The actual interval Plücker quotient and its band-matrix map

The Grassmannian relations are the polynomial identities of the maximal
minors of a generic matrix. The interval quotient adds the forbidden Plücker
variables. Its map to the literal band-matrix polynomial ring is constructed,
and all interval standard products are proved independent in that quotient.
The converse spanning/straightening statement is not assumed here.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Matrix
open scoped BigOperators

namespace PaperVerification.AlternatingForms

section MatchingBounds

variable {s n : ℕ}

/-- A matching to ordered lower bounds implies the diagonal lower bounds.
This is the order-statistic form of the paper's uncrossing argument. -/
theorem monotone_matching_lower (α I : Fin s → Fin n)
    (hα : Monotone α) (hI : Monotone I) (σ : Equiv.Perm (Fin s))
    (hmatch : ∀ i, α (σ i) ≤ I i) : ∀ i, α i ≤ I i := by
  classical
  intro a
  by_contra ha
  have hbad : I a < α a := lt_of_not_ge ha
  have hsub : (Finset.Iic a).image σ ⊆ Finset.Iio a := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    apply Finset.mem_Iio.mpr
    by_contra h
    have hai : a ≤ σ i := le_of_not_gt h
    have h₁ := hα hai
    have h₂ := hI (Finset.mem_Iic.mp hi)
    exact (not_lt_of_ge (h₁.trans ((hmatch i).trans h₂))) hbad
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ σ.injective,Fin.card_Iic,Fin.card_Iio] at hcard
  omega

theorem monotone_matching_upper (β I : Fin s → Fin n)
    (hβ : Monotone β) (hI : Monotone I) (σ : Equiv.Perm (Fin s))
    (hmatch : ∀ i, I i ≤ β (σ i)) : ∀ i, I i ≤ β i := by
  classical
  intro a
  by_contra ha
  have hbad : β a < I a := lt_of_not_ge ha
  have hsub : (Finset.Ici a).image σ ⊆ Finset.Ioi a := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    apply Finset.mem_Ioi.mpr
    by_contra h
    have hia : σ i ≤ a := le_of_not_gt h
    have h₁ := hβ hia
    have h₂ := hI (Finset.mem_Ici.mp hi)
    exact (not_lt_of_ge (h₂.trans ((hmatch i).trans h₁))) hbad
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ σ.injective,Fin.card_Ici,Fin.card_Ioi] at hcard
  have ha' := a.isLt
  omega

end MatchingBounds

section ForbiddenMinors

variable {K : Type*} [Field K] {s n : ℕ}

theorem bandMinor_eq_zero_of_forbidden (α β I : Fin s → Fin n)
    (hα : Monotone α) (hβ : Monotone β) (hI : StrictMono I)
    (hbad : ¬∀ i, α i ≤ I i ∧ I i ≤ β i) : bandMinor (K := K) α β I = 0 := by
  classical
  rw [bandMinor_expansion]
  apply Finset.sum_eq_zero
  intro σ hσ
  have hmiss : ∃ i, ¬(α (σ i) ≤ I i ∧ I i ≤ β (σ i)) := by
    by_contra h
    have hall : ∀ i, α (σ i) ≤ I i ∧ I i ≤ β (σ i) := by
      intro i
      exact not_not.mp (not_exists.mp h i)
    exact hbad fun i =>
      ⟨monotone_matching_lower α I hα hI.monotone σ (fun j => (hall j).1) i,
        monotone_matching_upper β I hβ hI.monotone σ (fun j => (hall j).2) i⟩
  obtain ⟨i,hi⟩ := hmiss
  have hz : (∏ j, bandEntryCoefficient (K := K) α β (σ j) (I j)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [bandEntryCoefficient,if_neg hi]
  simp only [minorTermCoefficient,hz,smul_zero,monomial_zero]

end ForbiddenMinors

section ActualPresentation

variable {K : Type*} [Field K] {s n : ℕ}

def PluckerIndex (s n : ℕ) := {I : Fin s → Fin n // StrictMono I}

instance pluckerIndex_fintype (s n : ℕ) : Fintype (PluckerIndex s n) := by
  classical
  unfold PluckerIndex
  infer_instance

def genericPluckerMinor (I : PluckerIndex s n) : MvPolynomial (Fin s × Fin n) K :=
  (Matrix.of fun i j : Fin s => (X (i,I.val j) : MvPolynomial (Fin s × Fin n) K)).det

/-- The universal maximal-minor map, so its kernel consists of actual
polynomial identities among generic maximal minors. -/
def genericPluckerMap :
    MvPolynomial (PluckerIndex s n) K →ₐ[K] MvPolynomial (Fin s × Fin n) K :=
  aeval genericPluckerMinor

def matrixPluckerIdeal : Ideal (MvPolynomial (PluckerIndex s n) K) :=
  RingHom.ker (genericPluckerMap (K := K) (s := s) (n := n)).toRingHom

def bandPluckerMap (α β : Fin s → Fin n) :
    MvPolynomial (PluckerIndex s n) K →ₐ[K] MvPolynomial (Fin s × Fin n) K :=
  aeval fun I => bandMinor α β I.val

def bandEntrySpecialization (α β : Fin s → Fin n) :
    MvPolynomial (Fin s × Fin n) K →ₐ[K] MvPolynomial (Fin s × Fin n) K :=
  aeval fun a => bandMatrix α β a.1 a.2

theorem bandEntrySpecialization_minor (α β : Fin s → Fin n) (I : PluckerIndex s n) :
    bandEntrySpecialization (K := K) α β (genericPluckerMinor I) = bandMinor α β I.val := by
  unfold genericPluckerMinor bandMinor
  rw [AlgHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  change bandEntrySpecialization (K := K) α β (X (i,I.val j)) =
    bandMatrix (K := K) α β i (I.val j)
  simp only [bandEntrySpecialization,aeval_X]

theorem bandPluckerMap_eq_comp (α β : Fin s → Fin n) :
    bandPluckerMap (K := K) α β = (bandEntrySpecialization α β).comp genericPluckerMap := by
  apply MvPolynomial.algHom_ext
  intro I
  simp only [bandPluckerMap,genericPluckerMap,AlgHom.comp_apply,aeval_X,
    bandEntrySpecialization_minor]

def intervalPluckerIdeal (α β : Fin s → Fin n) : Ideal (MvPolynomial (PluckerIndex s n) K) :=
  matrixPluckerIdeal ⊔ Ideal.span
    {p | ∃ I : PluckerIndex s n, (¬∀ i, α i ≤ I.val i ∧ I.val i ≤ β i) ∧ p = X I}

theorem intervalPluckerIdeal_le_kernel (α β : Fin s → Fin n)
    (hα : Monotone α) (hβ : Monotone β) :
    intervalPluckerIdeal (K := K) α β ≤ RingHom.ker (bandPluckerMap α β).toRingHom := by
  apply sup_le
  · intro p hp
    change bandPluckerMap α β p = 0
    rw [bandPluckerMap_eq_comp]
    change bandEntrySpecialization α β (genericPluckerMap p) = 0
    change genericPluckerMap p = 0 at hp
    rw [hp,map_zero]
  · apply Ideal.span_le.mpr
    rintro _ ⟨I,hI,rfl⟩
    change bandPluckerMap α β (X I) = 0
    rw [bandPluckerMap,aeval_X]
    exact bandMinor_eq_zero_of_forbidden α β I.val hα hβ I.property hI

def intervalBandMap (α β : Fin s → Fin n) (hα : Monotone α) (hβ : Monotone β) :
    (MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β) →ₐ[K]
      MvPolynomial (Fin s × Fin n) K :=
  Ideal.Quotient.liftₐ _ (bandPluckerMap α β)
    (fun p hp => intervalPluckerIdeal_le_kernel α β hα hβ hp)

def chainPluckerProduct (α β : Fin s → Fin n) {r : ℕ} (C : BandChain α β r) :
    MvPolynomial (PluckerIndex s n) K :=
  ∏ t, X ⟨C.val t,C.property.1 t⟩

def intervalStandardProduct (α β : Fin s → Fin n) {r : ℕ} (C : BandChain α β r) :
    MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β :=
  Ideal.Quotient.mk _ (chainPluckerProduct α β C)

theorem intervalBandMap_standardProduct (α β : Fin s → Fin n)
    (hα : Monotone α) (hβ : Monotone β) {r : ℕ} (C : BandChain α β r) :
    intervalBandMap (K := K) α β hα hβ (intervalStandardProduct α β C) =
      bandStandardProduct α β C := by
  change bandPluckerMap α β (chainPluckerProduct α β C) = _
  simp only [chainPluckerProduct,map_prod,bandStandardProduct]
  apply Finset.prod_congr rfl
  intro t ht
  change (MvPolynomial.aeval
    (fun I : PluckerIndex s n => bandMinor (K := K) α β I.val))
      (MvPolynomial.X ⟨C.val t,C.property.1 t⟩ :
        MvPolynomial (PluckerIndex s n) K) = bandMinor (K := K) α β (C.val t)
  exact MvPolynomial.aeval_X (R := K)
    (fun I : PluckerIndex s n => bandMinor (K := K) α β I.val)
    ⟨C.val t,C.property.1 t⟩

/-- Standard products are independent in the actual Plücker-identity quotient
with its forbidden coordinates, not just in an auxiliary vector space. -/
theorem intervalStandardProducts_linearIndependent (α β : Fin s → Fin n)
    (hα : Monotone α) (hβ : Monotone β) (r : ℕ) :
    LinearIndependent K (intervalStandardProduct (K := K) (r := r) α β) := by
  apply LinearIndependent.of_comp (intervalBandMap α β hα hβ).toLinearMap
  have he : (intervalBandMap α β hα hβ).toLinearMap ∘ intervalStandardProduct (r := r) α β =
      bandStandardProduct (K := K) (r := r) α β :=
    funext fun C => intervalBandMap_standardProduct α β hα hβ C
  rw [he]
  exact bandStandardProducts_linearIndependent α β r

end ActualPresentation

end PaperVerification.AlternatingForms
