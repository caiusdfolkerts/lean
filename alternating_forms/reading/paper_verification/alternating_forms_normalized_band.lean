module

public import PaperVerification.AlternatingFormsIntervalHilbert
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import TauCeti.RingTheory.KrullDimension.FiniteType
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# A polynomial normalization of the interval band matrix

Each leftmost allowed entry is specialized to one. One additional variable
multiplies row zero and records the Plücker degree. The missing pivot exponents
of a standard product are recovered from that degree and the other entries in
their row. Consequently the specialization is injective on the actual interval
Plücker ring. It uses exactly `1 + ∑ i, (β i - α i)` polynomial variables.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial Matrix

namespace PaperVerification.AlternatingForms

section SupportExpansion

variable {K σ ι : Type*} [Field K] [Fintype ι]

theorem isWeightMonic_of_supported_finite_expansion
    (w : σ → ℤ) (p : MvPolynomial σ K) (a : ι → σ →₀ ℕ) (c : ι → K) (i₀ : ι)
    (hp : p = ∑ i, monomial (a i) (c i)) (hc : c i₀ = 1)
    (hlt : ∀ i, i ≠ i₀ → c i ≠ 0 →
      Finsupp.weight w (a i) < Finsupp.weight w (a i₀)) :
    IsWeightMonic w p (a i₀) := by
  classical
  constructor
  · rw [hp,coeff_sum,Finset.sum_eq_single i₀]
    · simp only [coeff_monomial,ite_true,hc]
    · intro i hi hne
      by_cases hci : c i = 0
      · simp only [hci,monomial_zero,MvPolynomial.coeff_zero,Finsupp.zero_apply]
      · have ha : a i ≠ a i₀ := by
          intro he
          have h := hlt i hne hci
          rw [he] at h
          exact (lt_irrefl _ h)
        simp only [coeff_monomial,if_neg ha]
    · intro hi
      exact (hi (Finset.mem_univ _)).elim
  · intro b hba hweight
    rw [hp,coeff_sum]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hci : c i = 0
    · simp only [hci,monomial_zero,MvPolynomial.coeff_zero,Finsupp.zero_apply]
    · have hab : a i ≠ b := by
        intro he
        by_cases hei : i=i₀
        · subst i
          exact hba he.symm
        · have h := hlt i hei hci
          rw [he] at h
          exact (not_lt_of_ge hweight h)
      simp only [coeff_monomial,if_neg hab]

end SupportExpansion

variable {K : Type*} [Field K] {s n r : ℕ}

abbrev BandNonpivot (α β : Fin s → Fin n) :=
  (i : Fin s) × {j : Fin n // α i < j ∧ j ≤ β i}

abbrev NormalizedBandVariable (α β : Fin s → Fin n) := Option (BandNonpivot α β)

def normalizedEntryExponent (α β : Fin s → Fin n) (a : Fin s × Fin n) :
    NormalizedBandVariable α β →₀ ℕ :=
  (if a.1.val=0 then Finsupp.single none 1 else 0) +
    if h : α a.1 < a.2 ∧ a.2 ≤ β a.1 then
      Finsupp.single (some ⟨a.1,⟨a.2,h⟩⟩) 1 else 0

def normalizeBand (α β : Fin s → Fin n) :
    MvPolynomial (Fin s × Fin n) K →ₐ[K]
      MvPolynomial (NormalizedBandVariable α β) K :=
  aeval fun a => monomial (normalizedEntryExponent α β a) 1

def normalizedEntryWeight (α β : Fin s → Fin n) : NormalizedBandVariable α β → ℤ
  | none => 0
  | some a => (a.1.val : ℤ) * (a.2.val.val : ℤ) -
      (a.1.val : ℤ) * ((α a.1).val : ℤ)

def normalizedMinorTermExponent (α β I : Fin s → Fin n)
    (σ : Equiv.Perm (Fin s)) : NormalizedBandVariable α β →₀ ℕ :=
  ∑ i, normalizedEntryExponent α β (σ i,I i)

def normalizedChainTermExponent (α β : Fin s → Fin n) (I : Fin r → Fin s → Fin n)
    (σ : Fin r → Equiv.Perm (Fin s)) : NormalizedBandVariable α β →₀ ℕ :=
  ∑ t, normalizedMinorTermExponent α β (I t) (σ t)

def normalizedDiagonalExponent (α β : Fin s → Fin n) (I : Fin r → Fin s → Fin n) :
    NormalizedBandVariable α β →₀ ℕ :=
  normalizedChainTermExponent α β I (fun _ => 1)

theorem normalizeBand_entry (α β : Fin s → Fin n) (i : Fin s) (j : Fin n) :
    normalizeBand (K := K) α β (bandMatrix α β i j) =
      monomial (normalizedEntryExponent α β (i,j)) (bandEntryCoefficient α β i j) := by
  simp only [normalizeBand,bandMatrix,aeval_monomial,MvPolynomial.algebraMap_eq]
  rw [Finsupp.prod_single_index (by simp)]
  simp only [pow_one,C_mul_monomial,mul_one]

theorem normalizeBand_minor_expansion (α β I : Fin s → Fin n) :
    normalizeBand (K := K) α β (bandMinor α β I) =
      ∑ σ : Equiv.Perm (Fin s),
        monomial (normalizedMinorTermExponent α β I σ) (minorTermCoefficient α β I σ) := by
  classical
  rw [bandMinor,AlgHom.map_det,Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ hσ
  simp only [AlgHom.mapMatrix_apply,Matrix.map_apply,Matrix.submatrix_apply,id_eq,normalizeBand_entry,
    prod_monomial_eq_monomial_sum,smul_monomial,
    normalizedMinorTermExponent,minorTermCoefficient]

theorem normalizeBand_standard_expansion (α β : Fin s → Fin n) (C : BandChain α β r) :
    normalizeBand (K := K) α β (bandStandardProduct α β C) =
      ∑ σ : Fin r → Equiv.Perm (Fin s),
        monomial (normalizedChainTermExponent α β C.val σ)
          (chainTermCoefficient α β C.val σ) := by
  classical
  simp only [bandStandardProduct,map_prod,normalizeBand_minor_expansion]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  exact prod_monomial_eq_monomial_sum _ _

theorem normalizedEntryExponent_weight (α β : Fin s → Fin n) (i : Fin s) (j : Fin n)
    (h : α i ≤ j ∧ j ≤ β i) :
    Finsupp.weight (normalizedEntryWeight α β) (normalizedEntryExponent α β (i,j)) =
      (i.val : ℤ) * (j.val : ℤ) - (i.val : ℤ) * ((α i).val : ℤ) := by
  classical
  rcases h.1.eq_or_lt with he | he
  · subst j
    by_cases hi : i.val=0 <;>
      simp [normalizedEntryExponent,normalizedEntryWeight,hi,Finsupp.weight_single]
  · by_cases hi : i.val=0 <;>
      simp [normalizedEntryExponent,normalizedEntryWeight,he,h.2,hi,Finsupp.weight_single]

theorem minorTermCoefficient_ne_zero_allowed (α β I : Fin s → Fin n)
    (σ : Equiv.Perm (Fin s))
    (h : minorTermCoefficient (K := K) α β I σ ≠ 0) (i : Fin s) :
    α (σ i) ≤ I i ∧ I i ≤ β (σ i) := by
  classical
  by_contra hi
  apply h
  have hz : ∏ j, bandEntryCoefficient (K := K) α β (σ j) (I j) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [bandEntryCoefficient,if_neg hi])
  simp only [minorTermCoefficient,hz,smul_zero]

theorem normalizedMinorTermExponent_weight (α β I : Fin s → Fin n)
    (σ : Equiv.Perm (Fin s))
    (h : minorTermCoefficient (K := K) α β I σ ≠ 0) :
    Finsupp.weight (normalizedEntryWeight α β) (normalizedMinorTermExponent α β I σ) =
      Finsupp.weight (bandEntryWeight s n) (minorTermExponent I σ) -
        ∑ i, (i.val : ℤ) * ((α i).val : ℤ) := by
  simp only [normalizedMinorTermExponent,map_sum,
    normalizedEntryExponent_weight α β _ _ (minorTermCoefficient_ne_zero_allowed α β I σ h _),
    Finset.sum_sub_distrib,minorTermExponent_weight]
  rw [Equiv.sum_comp σ (fun i => (i.val : ℤ) * ((α i).val : ℤ))]

theorem normalizedChainTermExponent_weight (α β : Fin s → Fin n)
    (I : Fin r → Fin s → Fin n) (σ : Fin r → Equiv.Perm (Fin s))
    (h : chainTermCoefficient (K := K) α β I σ ≠ 0) :
    Finsupp.weight (normalizedEntryWeight α β) (normalizedChainTermExponent α β I σ) =
      Finsupp.weight (bandEntryWeight s n) (chainTermExponent I σ) -
        (r : ℤ) * ∑ i, (i.val : ℤ) * ((α i).val : ℤ) := by
  classical
  have ht (t : Fin r) : minorTermCoefficient (K := K) α β (I t) (σ t) ≠ 0 := by
    intro hz
    apply h
    exact Finset.prod_eq_zero (Finset.mem_univ t) hz
  simp only [normalizedChainTermExponent,chainTermExponent,map_sum,
    normalizedMinorTermExponent_weight α β _ _ (ht _),Finset.sum_sub_distrib,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem normalizeBand_standard_weightMonic (α β : Fin s → Fin n) (C : BandChain α β r) :
    IsWeightMonic (normalizedEntryWeight α β)
      (normalizeBand (K := K) α β (bandStandardProduct α β C))
      (normalizedDiagonalExponent α β C.val) := by
  have hc : chainTermCoefficient (K := K) α β C.val (fun _ => 1) = 1 := by
    simp only [chainTermCoefficient,
      minorTermCoefficient_diagonal α β _ (C.property.2.1 _),Finset.prod_const_one]
  apply isWeightMonic_of_supported_finite_expansion _ _ _ _ (fun _ => 1)
    (normalizeBand_standard_expansion α β C) hc
  intro σ hσ hnonzero
  rw [normalizedChainTermExponent_weight α β C.val σ hnonzero,
    normalizedChainTermExponent_weight α β C.val (fun _ => 1) (by rw [hc]; exact one_ne_zero)]
  exact sub_lt_sub_right
    (chainTermExponent_weight_lt_diagonal C.val C.property.1 σ hσ) _

@[simp] theorem normalizedEntryExponent_none (α β : Fin s → Fin n) (a : Fin s × Fin n) :
    normalizedEntryExponent α β a none = if a.1.val=0 then 1 else 0 := by
  classical
  simp only [normalizedEntryExponent,Finsupp.add_apply]
  split_ifs <;> simp [Finsupp.single_apply]

@[simp] theorem normalizedEntryExponent_some (α β : Fin s → Fin n)
    (a : Fin s × Fin n) (b : BandNonpivot α β) :
    normalizedEntryExponent α β a (some b) = if a=(b.1,b.2.val) then 1 else 0 := by
  classical
  have hnone : (if a.1.val=0 then Finsupp.single none 1 else
      (0 : NormalizedBandVariable α β →₀ ℕ)) (some b) = 0 := by
    split_ifs <;> simp [Finsupp.single_apply]
  rw [normalizedEntryExponent,Finsupp.add_apply,hnone,zero_add]
  by_cases ha : α a.1 < a.2 ∧ a.2 ≤ β a.1
  · rw [dif_pos ha,Finsupp.single_apply]
    have he : (some ⟨a.1,⟨a.2,ha⟩⟩ : NormalizedBandVariable α β) = some b ↔
        a = (b.1,b.2.val) := by
      constructor
      · intro h
        have h' := Option.some.inj h
        exact Prod.ext (congrArg Sigma.fst h')
          (congrArg (fun x : BandNonpivot α β => x.2.val) h')
      · intro h
        rcases a with ⟨i,j⟩
        cases h
        rfl
    simp only [he]
  · rw [dif_neg ha,Finsupp.zero_apply]
    symm
    apply if_neg
    intro he
    apply ha
    simpa only [he] using b.2.property

theorem normalizedDiagonalExponent_none (α β : Fin s → Fin n)
    (I : Fin r → Fin s → Fin n) (hs : 0 < s) :
    normalizedDiagonalExponent α β I none = r := by
  classical
  have hsum : (∑ i : Fin s, if i.val=0 then 1 else 0 : ℕ) = 1 := by
    let z : Fin s := ⟨0,hs⟩
    rw [Finset.sum_eq_single z]
    · simp only [z,ite_true]
    · intro i hi hiz
      rw [if_neg (fun hi0 => hiz (Fin.ext hi0))]
    · intro hz
      exact (hz (Finset.mem_univ _)).elim
  simp only [normalizedDiagonalExponent,normalizedChainTermExponent,
    normalizedMinorTermExponent,Finset.sum_apply',Equiv.Perm.one_apply,
    normalizedEntryExponent_none,hsum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,Nat.cast_id]

theorem normalizedDiagonalExponent_some (α β : Fin s → Fin n)
    (I : Fin r → Fin s → Fin n) (b : BandNonpivot α β) :
    normalizedDiagonalExponent α β I (some b) = chainDiagonalExponent I (b.1,b.2.val) := by
  classical
  simp only [normalizedDiagonalExponent,normalizedChainTermExponent,normalizedMinorTermExponent,
    chainDiagonalExponent,chainTermExponent,minorTermExponent,Finset.sum_apply',
    Equiv.Perm.one_apply,normalizedEntryExponent_some,Finsupp.single_apply]

theorem chainDiagonalExponent_row_sum (I : Fin r → Fin s → Fin n) (i : Fin s) :
    ∑ j : Fin n, chainDiagonalExponent I (i,j) = r := by
  classical
  simp only [chainDiagonalExponent,chainTermExponent,minorTermExponent,
    Finset.sum_apply',Equiv.Perm.one_apply]
  rw [Finset.sum_comm]
  have ht (t : Fin r) : (∑ j : Fin n, ∑ a : Fin s,
      Finsupp.single (a,I t a) 1 (i,j)) = 1 := by
    rw [Finset.sum_comm,Finset.sum_eq_single i]
    · simp [Finsupp.single_apply]
    · intro a ha hai
      simp [Finsupp.single_apply,hai]
    · intro hi
      exact (hi (Finset.mem_univ _)).elim
  simp only [ht,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,Nat.cast_id]

theorem chainDiagonalExponent_outside (α β : Fin s → Fin n) (C : BandChain α β r)
    (i : Fin s) (j : Fin n) (h : ¬ (α i ≤ j ∧ j ≤ β i)) :
    chainDiagonalExponent C.val (i,j) = 0 := by
  classical
  rw [chainDiagonalExponent_apply,List.count_eq_zero]
  intro hj
  obtain ⟨t,ht⟩ := List.mem_ofFn.mp hj
  exact h (ht ▸ C.property.2.1 t i)

theorem normalizedDiagonalExponent_injective (α β : Fin s → Fin n) (hs : 0 < s) :
    Function.Injective
      (fun C : Σ r, BandChain α β r => normalizedDiagonalExponent α β C.2.val) := by
  classical
  rintro ⟨r,C⟩ ⟨r',D⟩ h
  have hr := congrArg (fun a => a none) h
  simp only [normalizedDiagonalExponent_none α β _ hs] at hr
  subst r'
  have hnon (i : Fin s) (j : Fin n) (hj : j ≠ α i) :
      chainDiagonalExponent C.val (i,j) = chainDiagonalExponent D.val (i,j) := by
    by_cases hb : α i ≤ j ∧ j ≤ β i
    · let b : BandNonpivot α β := ⟨i,⟨j,lt_of_le_of_ne hb.1 (Ne.symm hj),hb.2⟩⟩
      simpa only [normalizedDiagonalExponent_some] using congrArg (fun a => a (some b)) h
    · rw [chainDiagonalExponent_outside α β C i j hb,
        chainDiagonalExponent_outside α β D i j hb]
  have he : chainDiagonalExponent C.val = chainDiagonalExponent D.val := by
    ext a
    rcases a with ⟨i,j⟩
    by_cases hj : j=α i
    · subst j
      have hrow := (chainDiagonalExponent_row_sum C.val i).trans
        (chainDiagonalExponent_row_sum D.val i).symm
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (α i)),
        ← Finset.sum_erase_add _ _ (Finset.mem_univ (α i))] at hrow
      have hrest : ∑ j ∈ Finset.univ.erase (α i), chainDiagonalExponent C.val (i,j) =
          ∑ j ∈ Finset.univ.erase (α i), chainDiagonalExponent D.val (i,j) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hnon i j (Finset.mem_erase.mp hj).1
      rw [hrest] at hrow
      exact Nat.add_left_cancel hrow
    · exact hnon i j hj
  have hCD := chainDiagonalExponent_injective α β he
  cases hCD
  rfl

theorem normalizedStandardProducts_linearIndependent (α β : Fin s → Fin n) (hs : 0 < s) :
    LinearIndependent K (fun C : Σ r, BandChain α β r =>
      normalizeBand (K := K) α β (bandStandardProduct α β C.2)) := by
  apply linearIndependent_iff_finset_linearIndependent.mpr
  intro S
  exact linearIndependent_of_weightMonic (normalizedEntryWeight α β) _ _
    ((normalizedDiagonalExponent_injective α β hs).comp Subtype.val_injective)
    (fun C => normalizeBand_standard_weightMonic α β C.val.2)

def normalizedIntervalMap (α β : Fin s → Fin n)
    (hα : Monotone α) (hβ : Monotone β) :
    MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β →ₐ[K]
      MvPolynomial (NormalizedBandVariable α β) K :=
  (normalizeBand α β).comp (intervalBandMap α β hα hβ)

theorem normalizedIntervalMap_injective (α β : Fin s → Fin n)
    (hα : Monotone α) (hβ : Monotone β) (hs : 0 < s) :
    Function.Injective (normalizedIntervalMap (K := K) α β hα hβ) := by
  apply LinearMap.injective_of_linearIndependent
    (f := (normalizedIntervalMap (K := K) α β hα hβ).toLinearMap)
    (show Submodule.span K (Set.range (intervalAllStandardProduct α β)) = ⊤ from
      intervalStandardSpan_eq_top α β)
  have he : (normalizedIntervalMap (K := K) α β hα hβ).toLinearMap ∘
      intervalAllStandardProduct α β =
      (fun C : Σ r, BandChain α β r => normalizeBand α β (bandStandardProduct α β C.2)) := by
    funext C
    change normalizeBand α β (intervalBandMap α β hα hβ (intervalStandardProduct α β C.2)) = _
    rw [intervalBandMap_standardProduct]
  rw [he]
  exact normalizedStandardProducts_linearIndependent α β hs

theorem normalizedBandVariable_card (α β : Fin s → Fin n) :
    Fintype.card (NormalizedBandVariable α β) = 1 + ∑ i, ((β i).val - (α i).val) := by
  classical
  rw [Fintype.card_option,Fintype.card_sigma]
  have hcard (i : Fin s) : Fintype.card {j : Fin n // α i < j ∧ j ≤ β i} =
      (β i).val - (α i).val := by
    let e : {j : Fin n // α i < j ∧ j ≤ β i} ≃ Finset.Ioc (α i) (β i) :=
      Equiv.subtypeEquivRight fun j => Finset.mem_Ioc.symm
    simpa only [Fintype.card_coe,Fin.card_Ioc] using Fintype.card_congr e
  simp only [hcard,Nat.add_comm]

theorem intervalPlucker_krullDim_le (α β : Fin s → Fin n)
    (hα : Monotone α) (hβ : Monotone β) (hs : 0 < s) :
    ringKrullDim (MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β) ≤
      (1 + ∑ i, ((β i).val - (α i).val) : ℕ) := by
  letI := intervalPluckerIdeal_isPrime (K := K) α β hα hβ hs
  rw [TauCeti.ringKrullDim_eq_toNat_trdeg K]
  have h := trdeg_le_of_injective (normalizedIntervalMap (K := K) α β hα hβ)
    (normalizedIntervalMap_injective α β hα hβ hs)
  rw [MvPolynomial.trdeg_of_isDomain] at h
  have hn := Cardinal.toNat_le_toNat h
    (Cardinal.lift_lt_aleph0.mpr (Cardinal.mk_lt_aleph0 (α := NormalizedBandVariable α β)))
  have hn' : (Algebra.trdeg K
      (MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β)).toNat ≤
        1 + ∑ i, ((β i).val - (α i).val) := by
    simpa only [Cardinal.toNat_lift,Cardinal.mk_toNat_eq_card,normalizedBandVariable_card]
      using hn
  exact_mod_cast hn'

end PaperVerification.AlternatingForms
