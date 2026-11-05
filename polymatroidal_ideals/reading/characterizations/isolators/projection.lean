import Characterizations.BoundedFamilies
import Characterizations.Localization
import Characterizations.Resolution.LinearQuotients

/-! # Exact minimal generators in localized deleted bounded families -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.Isolators
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

def indicatorExponent (T : Finset V) : Exponent V := ∑ i ∈ T, Finsupp.single i 1
@[simp] lemma indicatorExponent_apply (T : Finset V) (i : V) :
    indicatorExponent T i = if i ∈ T then 1 else 0 := by
  simp [indicatorExponent, Finsupp.single_apply]
@[simp] lemma indicatorExponent_degree (T : Finset V) : (indicatorExponent T).degree = T.card := by
  simp [indicatorExponent, map_sum]

def retainedCaps (T R : Finset V) : Finset R := univ.filter (fun i => i.val ∈ T)
@[simp] lemma mem_retainedCaps (T R : Finset V) (i : R) : i ∈ retainedCaps T R ↔ i.val ∈ T := by
  simp [retainedCaps]

lemma degree_split (R : Finset V) (a : Exponent V) :
    (restrictExponent R a).degree + subsetSum a Rᶜ = a.degree := by
  rw [restrictExponent_degree]
  have h := subsetSum_union_inter a R Rᶜ
  simpa using h

lemma degree_split_saturated (T R : Finset V) (h : Exponent V)
    (hsat : ∀ i ∈ T, h i = 1) (hcover : Rᶜ ⊆ T) :
    (restrictExponent R h).degree + Rᶜ.card = h.degree := by
  have he : subsetSum h Rᶜ = Rᶜ.card := by
    unfold subsetSum
    calc
      _ = ∑ i ∈ Rᶜ, (1 : ℕ) := sum_congr rfl (fun i hi => hsat i (hcover hi))
      _ = _ := by simp
  rw [← he]
  exact degree_split R h

lemma minimalFamily_eq_of_divisors {W : Type*} [Fintype W] [DecidableEq W]
    (A D : Family W) (hD : Antichain D) (hDA : D ⊆ A)
    (hdiv : ∀ a ∈ A, ∃ b ∈ D, b ≤ a) : minimalFamily A = D := by
  ext a
  constructor
  · intro ha
    obtain ⟨b, hb, hba⟩ := hdiv a (minimalFamily_subset A ha)
    have he := (mem_minimalFamily.mp ha).2 b (hDA hb) hba
    exact he ▸ hb
  · intro ha
    apply mem_minimalFamily.mpr
    refine ⟨hDA ha, ?_⟩
    intro b hb hba
    obtain ⟨c, hc, hcb⟩ := hdiv b hb
    have he := hD c hc a ha (hcb.trans hba)
    exact le_antisymm hba (he ▸ hcb)

/-- An extra exponent cannot leave the removed monomial as the only divisor:
its support supplies a different donor, and saturation excludes capped receivers. -/
lemma deletedBounded_below (T : Finset V) (h x : Exponent V)
    (hsat : ∀ i ∈ T, h i = 1) (hsupp : 2 ≤ h.support.card)
    (hdeg : h.degree ≤ x.degree) (hcap : ∀ i ∈ T, x i ≤ 1) (hne : x ≠ h) :
    Contains (deletedBounded h.degree T h) x := by
  obtain ⟨b, hbx, hbd⟩ := Finsupp.exists_le_degree_eq x h.degree hdeg
  by_cases hbh : b = h
  · subst b
    have hex : ∃ j, h j < x j := by
      by_contra hn
      push_neg at hn
      exact hne (le_antisymm hn hbx)
    obtain ⟨j, hj⟩ := hex
    obtain ⟨i, hi, hij⟩ := Finset.exists_mem_ne (show 1 < h.support.card by omega) j
    have hip : 0 < h i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
    have hjT : j ∉ T := by
      intro hjT
      have hc := hcap j hjT
      rw [hsat j hjT] at hj
      omega
    refine ⟨exchange h i j, (mem_deletedBounded _ _ _ _).mpr
      ⟨exchange_ne hij hip, exchange_degree h i j hip, ?_⟩, ?_⟩
    · intro v hv
      have hvj : v ≠ j := fun he => hjT (he ▸ hv)
      simp only [exchange_apply, if_neg hvj, Nat.add_zero, hsat v hv]
      omega
    · intro v
      have hv := hbx v
      by_cases hvj : v = j
      · subst v
        simp only [exchange_apply, if_neg hij.symm, ite_true, Nat.sub_zero]
        omega
      · simp only [exchange_apply, if_neg hvj, Nat.add_zero]
        split_ifs <;> omega
  · exact ⟨b, (mem_deletedBounded _ _ _ _).mpr
      ⟨hbh, hbd, fun i hi => (hbx i).trans (hcap i hi)⟩, hbx⟩

lemma restrict_lift (R : Finset V) (b : Exponent R) :
    restrictExponent R (extendExponent R b + indicatorExponent Rᶜ) = b := by
  ext i
  simp [extendExponent_apply, i.property]

/-- Exact minimal projected generators. The only hypotheses are saturated caps,
all omitted coordinates capped, and at least two retained support coordinates. -/
theorem localFamily_deletedBounded (T R : Finset V) (h : Exponent V)
    (hsat : ∀ i ∈ T, h i = 1) (hcover : Rᶜ ⊆ T)
    (hsupp : 2 ≤ (restrictExponent R h).support.card) :
    localFamily (deletedBounded h.degree T h) R =
      deletedBounded (restrictExponent R h).degree (retainedCaps T R) (restrictExponent R h) := by
  let D := deletedBounded (restrictExponent R h).degree (retainedCaps T R) (restrictExponent R h)
  have hsatR : ∀ i ∈ retainedCaps T R, restrictExponent R h i = 1 := by
    intro i hi
    exact hsat i.val ((mem_retainedCaps _ _ _).mp hi)
  have hdegree := degree_split_saturated T R h hsat hcover
  apply minimalFamily_eq_of_divisors _ D (deletedBounded_equigenerated _ _ _).antichain
  · intro b hb
    obtain ⟨hbne, hbdeg, hbcap⟩ := (mem_deletedBounded _ _ _ _).mp hb
    let x := extendExponent R b + indicatorExponent Rᶜ
    have hxres : restrictExponent R x = b := restrict_lift R b
    refine mem_image.mpr ⟨x, (mem_deletedBounded _ _ _ _).mpr ⟨?_, ?_, ?_⟩, hxres⟩
    · intro he
      exact hbne (hxres.symm.trans (congrArg (restrictExponent R) he))
    · rw [show x.degree = b.degree + Rᶜ.card by simp [x, map_add, extendExponent_degree]]
      rw [hbdeg, hdegree]
    · intro i hi
      by_cases hiR : i ∈ R
      · have hc := hbcap ⟨i, hiR⟩ (by simp [hi])
        simpa [x, extendExponent_apply, hiR] using hc
      · simp [x, extendExponent_apply, hiR]
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    obtain ⟨hxne, hxdeg, hxcap⟩ := (mem_deletedBounded _ _ _ _).mp hx
    apply deletedBounded_below (retainedCaps T R) (restrictExponent R h) (restrictExponent R x) hsatR hsupp
    · have hsplit := degree_split R x
      have hsum : subsetSum x Rᶜ ≤ Rᶜ.card := by
        calc
          _ ≤ ∑ i ∈ Rᶜ, 1 := sum_le_sum (fun i hi => hxcap i (hcover hi))
          _ = _ := by simp
      omega
    · intro i hi
      exact hxcap i.val ((mem_retainedCaps _ _ _).mp hi)
    · intro he
      apply hxne
      apply eq_of_le_of_degree_eq ?_ hxdeg
      intro i
      by_cases hiR : i ∈ R
      · exact le_of_eq (congrArg (fun a : Exponent R => a ⟨i, hiR⟩) he)
      · have hiT := hcover (mem_compl.mpr hiR)
        rw [hsat i hiT]
        exact hxcap i hiT

end Characterizations.Isolators
