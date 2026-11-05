module
public import graph_foundation.part013

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.FiniteOrderedComparison -/
section

/-! # Finite local comparison for an arbitrary monomial order

Only the finitely many weights occurring in one finite homogeneous component
are enumerated. This does not replace the original term order globally and
does not assume that it is representable by one integer weight vector.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.FiniteOrderedComparison

open Classical FilteredHomology

variable {K M I Γ : Type*} [Field K] [AddCommGroup M] [Module K M]
  [Fintype I] [LinearOrder Γ]
  (b : Module.Basis I K M) (w : I → Γ)

def weights : Finset Γ := Finset.univ.image w

def rankWeight (i : I) : ℕ :=
  ((weights w).orderIsoOfFin rfl).symm ⟨w i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩

theorem rankWeight_lt (i j : I) : rankWeight w i < rankWeight w j ↔ w i < w j :=
  ((weights w).orderIsoOfFin rfl).symm.lt_iff_lt

theorem rankWeight_le (i j : I) : rankWeight w i ≤ rankWeight w j ↔ w i ≤ w j :=
  ((weights w).orderIsoOfFin rfl).symm.le_iff_le

theorem rankWeight_bound (i : I) : rankWeight w i < (weights w).card :=
  (((weights w).orderIsoOfFin rfl).symm
    ⟨w i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩).isLt

abbrev rankFiltration : Filtration (K := K) M :=
  Universal.basisFiltration b (rankWeight w)

def level (n : Γ) : Submodule K M := Submodule.span K (b '' {i | w i ≤ n})
def lower (n : Γ) : Submodule K M := Submodule.span K (b '' {i | w i < n})

theorem rankFiltration_level_succ (i : I) :
    (rankFiltration b w).level (rankWeight w i + 1) = level b w (w i) := by
  change Submodule.span K (b '' {j | rankWeight w j < rankWeight w i + 1}) = _
  congr 1
  apply congrArg (Set.image b)
  ext j
  exact (Nat.lt_succ_iff).trans (rankWeight_le w j i)

theorem rankFiltration_level (i : I) :
    (rankFiltration b w).level (rankWeight w i) = lower b w (w i) := by
  change Submodule.span K (b '' {j | rankWeight w j < rankWeight w i}) = _
  congr 1
  apply congrArg (Set.image b)
  ext j
  exact rankWeight_lt w j i

theorem rankFiltration_top : (rankFiltration b w).level (weights w).card = ⊤ := by
  apply top_unique
  intro x _
  change x ∈ Submodule.span K (b '' {i | rankWeight w i < (weights w).card})
  rw [b.mem_span_image]
  intro i _
  exact rankWeight_bound w i

def LiftsCycles (d : Module.End K M) : Prop :=
  ∀ n x, x ∈ level b w n → d x ∈ lower b w n →
    ∃ z, z ∈ level b w n ∧ d z = 0 ∧ x - z ∈ lower b w n

theorem liftsCycles_of_rankLifts (d : Module.End K M)
    (h : FilteredHomology.LiftsCycles (rankFiltration b w) (rankFiltration b w) d) :
    LiftsCycles b w d := by
  intro n x hx hdx
  by_cases hn : ∃ i, w i = n
  · obtain ⟨i, rfl⟩ := hn
    have hx' : x ∈ (rankFiltration b w).level (rankWeight w i + 1) := by
      rw [rankFiltration_level_succ]
      exact hx
    have hdx' : d x ∈ (rankFiltration b w).level (rankWeight w i) := by
      rw [rankFiltration_level]
      exact hdx
    obtain ⟨z, hz, hdz, hxz⟩ := h (rankWeight w i) x hx' hdx'
    refine ⟨z, ?_, hdz, ?_⟩
    · simpa only [rankFiltration_level_succ] using hz
    · simpa only [rankFiltration_level] using hxz
  · refine ⟨0, (level b w n).zero_mem, map_zero d, ?_⟩
    rw [sub_zero]
    rw [level, b.mem_span_image] at hx
    rw [lower, b.mem_span_image]
    intro i hi
    exact lt_of_le_of_ne (hx hi) (fun he => hn ⟨i, he⟩)

theorem preserves_of_basis (d : Module.End K M)
    (hd : ∀ i j, b.repr (d (b i)) j ≠ 0 → w j ≤ w i) :
    Preserves (rankFiltration b w) (rankFiltration b w) d := by
  intro n x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      change d (b i) ∈ Submodule.span K (b '' {j | rankWeight w j < n})
      rw [b.mem_span_image]
      intro j hj
      exact ((rankWeight_le w j i).mpr (hd i j (Finsupp.mem_support_iff.mp hj))).trans_lt hi
  | zero => simpa only [map_zero] using ((rankFiltration b w).level n).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

theorem strict_difference_of_basis (d d₀ : Module.End K M)
    (hstrict : ∀ i j, b.repr ((d - d₀) (b i)) j ≠ 0 → w j < w i) :
    ∀ n x, x ∈ (rankFiltration b w).level (n + 1) →
      d x - d₀ x ∈ (rankFiltration b w).level n := by
  intro n x hx
  change (d - d₀) x ∈ (rankFiltration b w).level n
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      change (d - d₀) (b i) ∈ Submodule.span K (b '' {j | rankWeight w j < n})
      rw [b.mem_span_image]
      intro j hj
      exact ((rankWeight_lt w j i).mpr
        (hstrict i j (Finsupp.mem_support_iff.mp hj))).trans_le (Nat.lt_succ_iff.mp hi)
  | zero => simpa only [map_zero] using ((rankFiltration b w).level n).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

/-- Equality of actual homology dimensions makes every leading cycle lift,
with the original term-order filtration bounds retained exactly. -/
theorem liftsCycles_of_equal_homology
    (d d₀ : Module.End K M) (hdd : d.comp d = 0) (hdd₀ : d₀.comp d₀ = 0)
    (hd : ∀ i j, b.repr (d (b i)) j ≠ 0 → w j ≤ w i)
    (hhom : ∀ i j, b.repr (d₀ (b i)) j ≠ 0 → w j = w i)
    (hstrict : ∀ i j, b.repr ((d - d₀) (b i)) j ≠ 0 → w j < w i)
    (hdim : Module.finrank K (Homology d d hdd) = Module.finrank K (Homology d₀ d₀ hdd₀)) :
    LiftsCycles b w d := by
  letI : FiniteDimensional K M := Module.Finite.of_basis b
  apply liftsCycles_of_rankLifts b w d
  apply liftsCycles_of_equal_homology_strict_perturbation (rankFiltration b w) d d₀
    (preserves_of_basis b w d hd)
    (preserves_of_basis b w d₀ (fun i j hj => (hhom i j hj).le)) hdd hdd₀
    (strict_difference_of_basis b w d d₀ hstrict) _ (weights w).card (rankFiltration_top b w) hdim
  apply Universal.basisHomogeneous_liftsCycles b b (rankWeight w) (rankWeight w) d₀
  intro i
  rw [CommAlg.Grading.mem_piece]
  intro j hj
  exact le_antisymm ((rankWeight_le w j i).mpr (hhom i j hj).le)
    ((rankWeight_le w i j).mpr (hhom i j hj).ge)

end FourPapers.FiniteOrderedComparison

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.BasisSubmoduleComparison -/
section

/-! # Finite homogeneous submodules with their original weight bounds -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.BasisSubmodule

open Classical CommAlg FilteredHomology

variable {K M I Γ : Type*} [CommRing K] [AddCommGroup M] [Module K M]
  (b : Module.Basis I K M) (P : I → Prop)

abbrev space : Submodule K M := Submodule.span K (b '' {i | P i})
abbrev basis : Module.Basis {i // P i} K (space b P) := Grading.restrictedBasis b P

theorem mem_iff (x : M) : x ∈ space b P ↔ ∀ i, b.repr x i ≠ 0 → P i := by
  rw [space, b.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_setOf_eq]

theorem basis_repr (x : space b P) (i : {i // P i}) :
    (basis b P).repr x i = b.repr x.val i.val := by
  have he : (basis b P).coord i =
      (b.coord i.val).comp (space b P).subtype := by
    apply (basis b P).ext
    intro j
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self,
      LinearMap.comp_apply, Submodule.subtype_apply, Grading.restrictedBasis_val,
      Finsupp.single_apply]
    by_cases h : j = i
    · subst j
      simp
    · have hv : j.val ≠ i.val := fun hv => h (Subtype.ext hv)
      simp [h, hv]
  exact LinearMap.congr_fun he x

def restrictEnd (D : Module.End K M) (hD : ∀ x, x ∈ space b P → D x ∈ space b P) :
    Module.End K (space b P) :=
  (D.domRestrict (space b P)).codRestrict (space b P) (fun x => hD x.val x.property)

@[simp] theorem restrictEnd_val (D : Module.End K M)
    (hD : ∀ x, x ∈ space b P → D x ∈ space b P) (x : space b P) :
    (restrictEnd b P D hD x).val = D x.val := rfl

theorem restrictEnd_square (D : Module.End K M)
    (hD : ∀ x, x ∈ space b P → D x ∈ space b P) (hdd : D.comp D = 0) :
    (restrictEnd b P D hD).comp (restrictEnd b P D hD) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun hdd x.val

variable [LinearOrder Γ] (w : I → Γ)

theorem level_iff (n : Γ) (x : space b P) :
    x ∈ BasisCycleLifting.level (basis b P) (fun i => w i.val) n ↔
      x.val ∈ BasisCycleLifting.level b w n := by
  simp only [BasisCycleLifting.level, Module.Basis.mem_span_image]
  constructor
  · intro hx i hi
    have hP := (mem_iff b P x.val).mp x.property i (Finsupp.mem_support_iff.mp hi)
    exact hx (show (⟨i, hP⟩ : {i // P i}) ∈ ((basis b P).repr x).support from
      Finsupp.mem_support_iff.mpr (by simpa only [basis_repr] using Finsupp.mem_support_iff.mp hi))
  · intro hx i hi
    exact hx (show i.val ∈ (b.repr x.val).support from
      Finsupp.mem_support_iff.mpr (by simpa only [basis_repr] using Finsupp.mem_support_iff.mp hi))

theorem lower_iff (n : Γ) (x : space b P) :
    x ∈ BasisCycleLifting.lower (basis b P) (fun i => w i.val) n ↔
      x.val ∈ BasisCycleLifting.lower b w n := by
  simp only [BasisCycleLifting.lower, Module.Basis.mem_span_image]
  constructor
  · intro hx i hi
    have hP := (mem_iff b P x.val).mp x.property i (Finsupp.mem_support_iff.mp hi)
    exact hx (show (⟨i, hP⟩ : {i // P i}) ∈ ((basis b P).repr x).support from
      Finsupp.mem_support_iff.mpr (by simpa only [basis_repr] using Finsupp.mem_support_iff.mp hi))
  · intro hx i hi
    exact hx (show i.val ∈ (b.repr x.val).support from
      Finsupp.mem_support_iff.mpr (by simpa only [basis_repr] using Finsupp.mem_support_iff.mp hi))

end FourPapers.BasisSubmodule

namespace FourPapers.BasisSubmodule

open Classical CommAlg FilteredHomology

variable {K M I Γ : Type*} [Field K] [AddCommGroup M] [Module K M]
  [LinearOrder Γ] (b : Module.Basis I K M) (P : I → Prop) (w : I → Γ)
  [Finite {i // P i}]
  (D D₀ : Module.End K M)
  (hD : ∀ x, x ∈ space b P → D x ∈ space b P)
  (hD₀ : ∀ x, x ∈ space b P → D₀ x ∈ space b P)
  (hdd : D.comp D = 0) (hdd₀ : D₀.comp D₀ = 0)

/-- Equality on the actual finite submodule, together with a genuinely
strictly lower differential perturbation, lifts cycles with the original
ordered bounds. There is no global integer-weight assumption. -/
theorem lifts_of_equal_homology
    (hd : ∀ i j, b.repr (D (b i)) j ≠ 0 → w j ≤ w i)
    (hhom : ∀ i j, b.repr (D₀ (b i)) j ≠ 0 → w j = w i)
    (hstrict : ∀ i j, b.repr ((D-D₀) (b i)) j ≠ 0 → w j < w i)
    (hdim : Module.finrank K (Homology (restrictEnd b P D hD) (restrictEnd b P D hD)
        (restrictEnd_square b P D hD hdd)) =
      Module.finrank K (Homology (restrictEnd b P D₀ hD₀) (restrictEnd b P D₀ hD₀)
        (restrictEnd_square b P D₀ hD₀ hdd₀))) :
    BasisCycleLifting.LiftsOn b w D (space b P) := by
  letI : Fintype {i // P i} := Fintype.ofFinite _
  have hh := FiniteOrderedComparison.liftsCycles_of_equal_homology (basis b P)
    (fun i => w i.val) (restrictEnd b P D hD) (restrictEnd b P D₀ hD₀)
    (restrictEnd_square b P D hD hdd) (restrictEnd_square b P D₀ hD₀ hdd₀)
    (fun i j hij => hd i.val j.val (by
      simpa only [basis_repr, restrictEnd_val, Grading.restrictedBasis_val] using hij))
    (fun i j hij => hhom i.val j.val (by
      simpa only [basis_repr, restrictEnd_val, Grading.restrictedBasis_val] using hij))
    (fun i j hij => hstrict i.val j.val (by
      simpa only [basis_repr, LinearMap.sub_apply, Submodule.coe_sub,
        restrictEnd_val, Grading.restrictedBasis_val] using hij)) hdim
  intro n x hx hxF hdx
  have hx' : (⟨x,hx⟩ : space b P) ∈ FiniteOrderedComparison.level (basis b P)
      (fun i => w i.val) n := (level_iff b P w n ⟨x,hx⟩).mpr hxF
  have hdx' : restrictEnd b P D hD ⟨x,hx⟩ ∈ FiniteOrderedComparison.lower (basis b P)
      (fun i => w i.val) n := (lower_iff b P w n _).mpr hdx
  obtain ⟨z,hz,hdz,hxz⟩ := hh n ⟨x,hx⟩ hx' hdx'
  refine ⟨z.val,z.property,(level_iff b P w n z).mp hz,?_,?_⟩
  · exact congrArg Subtype.val hdz
  · exact (lower_iff b P w n (⟨x,hx⟩-z)).mp hxz

end FourPapers.BasisSubmodule

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.GroebnerIdealHomogeneousNatModule -/
section

/-!
# Homogeneous ideal coordinates with an explicit natural scalar action

Weighted homogeneity uses the canonical natural-number action on its
grading monoid. Concrete degree monoids can carry a different definition
of the same action. These wrappers use uniqueness of that action before
applying the proved homogeneous-coordinate theorem; they retain the exact
polynomials and degree functions.
-/

section
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace FourPapers.Sublattice

open Classical MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {K V Γ : Type*} [CommRing K] [Nontrivial K] [AddCommMonoid Γ]
  [hNat : Module ℕ Γ] [hDec : DecidableEq Γ]

theorem idealLift_homogeneous_withNatModule
    (m : MonomialOrder V) (J : Ideal (MvPolynomial V K))
    (G : Set (MvPolynomial V K)) (hG : m.IsGroebnerBasis G J)
    (hu : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))
    (deg : V → Γ)
    (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule K deg))
    (a : NonstandardIndex m J) :
    IsWeightedHomogeneous deg (idealLift m J G hG hu a).val
      (Finsupp.weight deg a.val) := by
  have hd : hDec = Classical.decEq Γ := Subsingleton.elim _ _
  subst hDec
  have h : hNat = (AddCommMonoid.toNatModule : Module ℕ Γ) := Subsingleton.elim _ _
  subst hNat
  exact idealLift_homogeneous m J G hG hu deg hJ a

theorem weightedHomogeneous_degree_withNatModule (deg : V → Γ)
    (p : MvPolynomial V K) (q : Γ) (hp : IsWeightedHomogeneous deg p q)
    (a : V →₀ ℕ) (ha : p.coeff a ≠ 0) : Finsupp.weight deg a = q := by
  have h : hNat = (AddCommMonoid.toNatModule : Module ℕ Γ) := Subsingleton.elim _ _
  subst hNat
  exact hp ha

/-- Multiplying homogeneous ideal coordinates preserves the sum of their
weights.  The natural scalar action is fixed before specializing the
grading monoid, so the concrete application need not compare two expanded
finite-support weight computations. -/
theorem idealLift_product_weight_withNatModule
    (m : MonomialOrder V) (J L : Ideal (MvPolynomial V K))
    (G H : Set (MvPolynomial V K))
    (hG : m.IsGroebnerBasis G J) (hH : m.IsGroebnerBasis H L)
    (hu : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))
    (hv : ∀ h ∈ H, h ≠ 0 → IsUnit (m.leadingCoeff h))
    (deg : V → Γ)
    (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule K deg))
    (hL : L.IsHomogeneous (weightedHomogeneousSubmodule K deg))
    (a : NonstandardIndex m J) (b : NonstandardIndex m L) (c : V →₀ ℕ)
    (hc : ((idealLift m J G hG hu a).val *
      (idealLift m L H hH hv b).val).coeff c ≠ 0) :
    Finsupp.weight deg c = Finsupp.weight deg a.val + Finsupp.weight deg b.val := by
  have hd : hDec = Classical.decEq Γ := Subsingleton.elim _ _
  subst hDec
  have h : hNat = (AddCommMonoid.toNatModule : Module ℕ Γ) := Subsingleton.elim _ _
  subst hNat
  exact ((idealLift_homogeneous m J G hG hu deg hJ a).mul
    (idealLift_homogeneous m L H hH hv deg hL b)) hc

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.GroebnerReesHomogeneous -/
section

/-! # The actual auxiliary, ordinary, and exterior gradings

Ordinary homogeneity is proved from homogeneity of the given ideal; it is
not inferred from a monomial-order bound. The exterior degree is recorded
in the integers so that its differential shift is injective, including at
degree zero where the differential vanishes.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg MvPolynomial
open scoped TensorProduct
attribute [local instance] MvPolynomial.weightedGradedAlgebra

universe u
variable {K V : Type u} [CommRing K] [Nontrivial K] [Fintype V] [LinearOrder V]
  (m : MonomialOrder V) (J I : Ideal (MvPolynomial V K))
  (hinit : ∀ s, initialIdealForBasis m (J ^ s) = I ^ s)
  (G : ℕ → Set (MvPolynomial V K))
  (hG : ∀ s, m.IsGroebnerBasis (G s) (J ^ s))
  (hu : ∀ s g, g ∈ G s → g ≠ 0 → IsUnit (m.leadingCoeff g))

def reesKoszulOrdinaryDegree (a : IdealReesKoszulIndex m J) : ℕ :=
  a.1.2.val.degree + a.2.card

def reesKoszulStrand (a : IdealReesKoszulIndex m J) : ℕ × ℕ :=
  (a.1.1, reesKoszulOrdinaryDegree m J a)

def reesKoszulFullDegree (a : IdealReesKoszulIndex m J) : (ℕ × ℕ) × ℤ :=
  (reesKoszulStrand m J a, a.2.card)

def koszulDegreeShift (a : (ℕ × ℕ) × ℤ) : (ℕ × ℕ) × ℤ := (a.1, a.2-1)

theorem koszulDegreeShift_injective : Function.Injective koszulDegreeShift := by
  rintro ⟨a,p⟩ ⟨b,q⟩ h
  have hab : a=b := congrArg Prod.fst h
  have he : p-1=q-1 := congrArg Prod.snd h
  have hpq : p=q := by omega
  exact Prod.ext hab hpq

theorem groebnerReesBasis_product_auxiliary
    (a b c : GroebnerReesIndex J m)
    (hc : (groebnerReesBasis J m G hG hu).repr
      (groebnerReesBasis J m G hG hu a * groebnerReesBasis J m G hG hu b) c ≠ 0) :
    c.1 = a.1+b.1 := by
  rw [groebnerReesBasis_repr, groebnerReesBasis_apply, groebnerReesBasis_apply] at hc
  change ((AddMonoidAlgebra.single a.1
    (idealLift m (J^a.1) (G a.1) (hG a.1) (hu a.1) a.2).val *
    AddMonoidAlgebra.single b.1
      (idealLift m (J^b.1) (G b.1) (hG b.1) (hu b.1) b.2).val).coeff c.1).coeff c.2.val ≠ 0 at hc
  rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply] at hc
  by_contra h
  simp only [if_neg (Ne.symm h), MvPolynomial.coeff_zero] at hc
  exact hc rfl

theorem groebnerReesKoszul_d_auxiliary_exterior
    (a z : IdealReesKoszulIndex m J)
    (hz : (groebnerReesKoszulBasis m J G hG hu).repr
      ((idealReesKoszulDGA J).d (groebnerReesKoszulBasis m J G hG hu a)) z ≠ 0) :
    z.1.1 = a.1.1 ∧ z.2.card + 1 = a.2.card := by
  rw [groebnerReesKoszul_d_basis, map_sum, Finsupp.finsetSum_apply] at hz
  obtain ⟨v,_,hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  rw [Simplicial.contraction_basis] at hv
  by_cases hvF : v ∈ a.2
  · rw [if_pos hvF, TensorProduct.tmul_smul, map_zsmul_unit,
      Finsupp.smul_apply, groebnerReesKoszulBasis, Module.Basis.tensorProduct_repr_tmul_apply,
      Module.Basis.repr_self, Finsupp.single_apply] at hv
    have hF : a.2.erase v = z.2 := by
      by_contra h
      simp [h] at hv
    rw [if_pos hF, one_smul, idealReesBaseVariable_basis m J G hG hu v] at hv
    have hc : (groebnerReesBasis J m G hG hu).repr
        (groebnerReesBasis J m G hG hu (idealReesZeroIndex m J (Finsupp.single v 1)) *
          groebnerReesBasis J m G hG hu a.1) z.1 ≠ 0 := by
      intro h
      simp only [h, smul_zero] at hv
      exact hv rfl
    refine ⟨?_, ?_⟩
    · simpa only [idealReesZeroIndex, zero_add] using
        groebnerReesBasis_product_auxiliary m J G hG hu _ _ _ hc
    · rw [← hF, Finset.card_erase_of_mem hvF]
      have hp := Finset.card_pos.mpr ⟨v,hvF⟩
      omega
  · rw [if_neg hvF, TensorProduct.tmul_zero, map_zero, Finsupp.zero_apply] at hv
    exact (hv rfl).elim

theorem initialReesKoszul_d_auxiliary_exterior
    (a z : IdealReesKoszulIndex m J)
    (hz : (initialReesKoszulBasis m J I hinit G hG hu).repr
      ((idealReesKoszulDGA I).d (initialReesKoszulBasis m J I hinit G hG hu a)) z ≠ 0) :
    z.1.1 = a.1.1 ∧ z.2.card + 1 = a.2.card := by
  have hf := initialReesKoszul_d_fine m J I hinit G hG hu a z hz
  have hw : reesKoszulWeight m J a ≤ reesKoszulWeight m J z := by
    simp only [reesKoszulWeight, hf, le_refl]
  apply groebnerReesKoszul_d_auxiliary_exterior m J G hG hu a z
  rwa [OrderedRees.differential_leading m J I hinit G hG hu a z hw]

variable (hJ : ∀ s, (J^s).IsHomogeneous
  (weightedHomogeneousSubmodule K (fun _ : V => (1 : ℕ))))

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 300000 in
set_option diagnostics true in
include hJ in
theorem groebnerReesBasis_product_ordinary
    (a b c : GroebnerReesIndex J m)
    (hc : (groebnerReesBasis J m G hG hu).repr
      (groebnerReesBasis J m G hG hu a * groebnerReesBasis J m G hG hu b) c ≠ 0) :
    c.2.val.degree = a.2.val.degree + b.2.val.degree := by
  have hs := groebnerReesBasis_product_auxiliary m J G hG hu a b c hc
  rw [groebnerReesBasis_repr, groebnerReesBasis_apply, groebnerReesBasis_apply] at hc
  change ((AddMonoidAlgebra.single a.1
    (idealLift m (J^a.1) (G a.1) (hG a.1) (hu a.1) a.2).val *
    AddMonoidAlgebra.single b.1
      (idealLift m (J^b.1) (G b.1) (hG b.1) (hu b.1) b.2).val).coeff c.1).coeff c.2.val ≠ 0 at hc
  rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply, if_pos hs.symm] at hc
  have he : Finsupp.weight (fun _ : V => (1 : ℕ)) c.2.val =
      Finsupp.weight (fun _ : V => (1 : ℕ)) a.2.val +
        Finsupp.weight (fun _ : V => (1 : ℕ)) b.2.val :=
    idealLift_product_weight_withNatModule m (J^a.1) (J^b.1) (G a.1) (G b.1)
      (hG a.1) (hG b.1) (hu a.1) (hu b.1) (fun _ : V => (1 : ℕ))
      (hJ a.1) (hJ b.1) a.2 b.2 c.2.val hc
  simpa only [← Finsupp.degree_eq_weight_one] using he

include hJ in
theorem groebnerReesKoszul_d_ordinary
    (a z : IdealReesKoszulIndex m J)
    (hz : (groebnerReesKoszulBasis m J G hG hu).repr
      ((idealReesKoszulDGA J).d (groebnerReesKoszulBasis m J G hG hu a)) z ≠ 0) :
    reesKoszulOrdinaryDegree m J z = reesKoszulOrdinaryDegree m J a := by
  have hcard := (groebnerReesKoszul_d_auxiliary_exterior m J G hG hu a z hz).2
  rw [groebnerReesKoszul_d_basis, map_sum, Finsupp.finsetSum_apply] at hz
  obtain ⟨v,_,hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  rw [Simplicial.contraction_basis] at hv
  by_cases hvF : v ∈ a.2
  · rw [if_pos hvF, TensorProduct.tmul_smul, map_zsmul_unit,
      Finsupp.smul_apply, groebnerReesKoszulBasis, Module.Basis.tensorProduct_repr_tmul_apply,
      Module.Basis.repr_self, Finsupp.single_apply] at hv
    have hF : a.2.erase v = z.2 := by
      by_contra h
      simp [h] at hv
    rw [if_pos hF, one_smul, idealReesBaseVariable_basis m J G hG hu v] at hv
    have hc : (groebnerReesBasis J m G hG hu).repr
        (groebnerReesBasis J m G hG hu (idealReesZeroIndex m J (Finsupp.single v 1)) *
          groebnerReesBasis J m G hG hu a.1) z.1 ≠ 0 := by
      intro h
      simp only [h, smul_zero] at hv
      exact hv rfl
    have hp := groebnerReesBasis_product_ordinary m J G hG hu hJ _ _ _ hc
    simp only [idealReesZeroIndex, Finsupp.degree_single] at hp
    dsimp only [reesKoszulOrdinaryDegree]
    omega
  · rw [if_neg hvF, TensorProduct.tmul_zero, map_zero, Finsupp.zero_apply] at hv
    exact (hv rfl).elim

include hJ in
theorem groebnerReesKoszul_d_fullDegree (a : IdealReesKoszulIndex m J) :
    (idealReesKoszulDGA J).d (groebnerReesKoszulBasis m J G hG hu a) ∈
      Grading.Piece (groebnerReesKoszulBasis m J G hG hu) (reesKoszulFullDegree m J)
        (koszulDegreeShift (reesKoszulFullDegree m J a)) := by
  rw [Grading.mem_piece]
  intro z hz
  have hs := groebnerReesKoszul_d_auxiliary_exterior m J G hG hu a z hz
  have hq := groebnerReesKoszul_d_ordinary m J G hG hu hJ a z hz
  apply Prod.ext
  · exact Prod.ext hs.1 hq
  · dsimp only [reesKoszulFullDegree, koszulDegreeShift]
    omega

include hJ in
theorem groebnerReesKoszul_d_strand (a : IdealReesKoszulIndex m J) :
    (idealReesKoszulDGA J).d (groebnerReesKoszulBasis m J G hG hu a) ∈
      Grading.Piece (groebnerReesKoszulBasis m J G hG hu) (reesKoszulStrand m J)
        (reesKoszulStrand m J a) := by
  rw [Grading.mem_piece]
  intro z hz
  exact Prod.ext (groebnerReesKoszul_d_auxiliary_exterior m J G hG hu a z hz).1
    (groebnerReesKoszul_d_ordinary m J G hG hu hJ a z hz)

/-- Each fixed ordinary and auxiliary component has a genuinely finite
basis, uniformly over arbitrary finite variable sets and all ideal powers. -/
instance reesKoszulStrand_finite (s q : ℕ) :
    Finite {a : IdealReesKoszulIndex m J // reesKoszulStrand m J a = (s,q)} := by
  let B := {a : V →₀ ℕ // a.degree ≤ q}
  letI : Finite B := (Finsupp.finite_of_degree_le q).to_subtype
  let f : {a : IdealReesKoszulIndex m J // reesKoszulStrand m J a = (s,q)} → B × Finset V :=
    fun a => (⟨a.val.1.2.val, by
      have hq := congrArg Prod.snd a.property
      change a.val.1.2.val.degree + a.val.2.card = q at hq
      omega⟩, a.val.2)
  apply Finite.of_injective f
  intro a b h
  apply Subtype.ext
  apply Prod.ext
  · have ha := congrArg Prod.fst a.property
    have hb := congrArg Prod.fst b.property
    have he : a.val.1.2.val = b.val.1.2.val := congrArg (fun z : B × Finset V => z.1.val) h
    have hs : a.val.1.1 = b.val.1.1 := ha.trans hb.symm
    cases a with
    | mk a ha =>
      cases b with
      | mk b hb =>
        rcases a with ⟨⟨r,a⟩,F⟩
        rcases b with ⟨⟨t,b⟩,H⟩
        dsimp only at hs he ⊢
        subst t
        exact congrArg (Sigma.mk r) (Subtype.ext he)
  · exact congrArg (fun z : B × Finset V => z.2) h

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.BasisEmbeddingLifting -/
section

/-! # Cycle lifting through literal basis embeddings -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.BasisEmbedding

open Classical CommAlg FilteredHomology

variable {K X M I J : Type*} [CommRing K]
  [AddCommGroup X] [Module K X] [AddCommGroup M] [Module K M]
  (b : Module.Basis I K X) (c : Module.Basis J K M)
  (φ : I → J) (hφ : Function.Injective φ) (e : X →ₗ[K] M)
  (he : ∀ i, e (b i) = c (φ i))

include hφ he in
theorem repr_image (x : X) (i : I) : c.repr (e x) (φ i) = b.repr x i := by
  have hh : (c.coord (φ i)).comp e = b.coord i := by
    apply b.ext
    intro j
    simp only [LinearMap.comp_apply, he, Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply, hφ.eq_iff]
  exact LinearMap.congr_fun hh x

include hφ he in
theorem injective : Function.Injective e := by
  intro x y h
  apply b.repr.injective
  ext i
  rw [← repr_image b c φ hφ e he x i, ← repr_image b c φ hφ e he y i, h]

include b hφ he in
theorem range_eq_span : LinearMap.range e = Submodule.span K (c '' Set.range φ) := by
  apply le_antisymm
  · rintro x ⟨y,rfl⟩
    have hy := b.mem_span y
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i,rfl⟩ := hy
      rw [he]
      exact Submodule.subset_span ⟨φ i, ⟨i,rfl⟩, rfl⟩
    | zero => simpa only [map_zero] using (Submodule.span K (c '' Set.range φ)).zero_mem
    | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
    | smul r x hx ih => simpa only [map_smul] using Submodule.smul_mem _ r ih
  · apply Submodule.span_le.mpr
    rintro x ⟨j,⟨i,rfl⟩,rfl⟩
    exact ⟨b i,he i⟩

variable {Γ : Type*} [LinearOrder Γ] (w : J → Γ)

include hφ he in
theorem span_iff (Q : Γ → Prop) (x : X) :
    x ∈ Submodule.span K (b '' {i | Q (w (φ i))}) ↔
      e x ∈ Submodule.span K (c '' {j | Q (w j)}) := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i,hi,rfl⟩ := hx
      rw [he]
      exact Submodule.subset_span ⟨φ i,hi,rfl⟩
    | zero => simpa only [map_zero] using (Submodule.span K (c '' {j | Q (w j)})).zero_mem
    | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
    | smul r x hx ih => simpa only [map_smul] using Submodule.smul_mem _ r ih
  · intro hx
    rw [b.mem_span_image]
    rw [c.mem_span_image] at hx
    intro i hi
    apply hx
    change φ i ∈ (c.repr (e x)).support
    rw [Finsupp.mem_support_iff, repr_image b c φ hφ e he]
    exact Finsupp.mem_support_iff.mp hi

end FourPapers.BasisEmbedding

namespace FourPapers.BasisEmbedding

open Classical

variable {K X Y M I J T Γ : Type*} [CommRing K] [LinearOrder Γ]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup M] [Module K M]
  (b : Module.Basis I K X) (b' : Module.Basis J K Y) (c : Module.Basis T K M)
  (φ : I → T) (hφ : Function.Injective φ) (ψ : J → T) (hψ : Function.Injective ψ)
  (e : X →ₗ[K] M) (e' : Y →ₗ[K] M)
  (he : ∀ i,e (b i)=c (φ i)) (he' : ∀ i,e' (b' i)=c (ψ i))
  (w : T → Γ) (f : X →ₗ[K] Y) (D : Module.End K M)
  (hd : ∀ x,D (e x)=e' (f x))

include hφ hψ he he' hd in
theorem ordered_coordinate_lifts_iff :
    BasisCycleLifting.LinearLifts b b' (w ∘ φ) (w ∘ ψ) f ↔
      BasisCycleLifting.LiftsOn c w D (Submodule.span K (c '' Set.range φ)) := by
  have hsrc (n : Γ) (x : X) : x∈BasisCycleLifting.level b (w ∘ φ) n ↔
      e x∈BasisCycleLifting.level c w n := span_iff b c φ hφ e he w (fun r => r≤n) x
  have hlo (n : Γ) (x : X) : x∈BasisCycleLifting.lower b (w ∘ φ) n ↔
      e x∈BasisCycleLifting.lower c w n := span_iff b c φ hφ e he w (fun r => r<n) x
  have htarget (n : Γ) (y : Y) : y∈BasisCycleLifting.lower b' (w ∘ ψ) n ↔
      e' y∈BasisCycleLifting.lower c w n := span_iff b' c ψ hψ e' he' w (fun r => r<n) y
  constructor
  · intro hlift n x hx hxF hdx
    rw [← range_eq_span b c φ hφ e he] at hx
    obtain ⟨y,rfl⟩ := hx
    obtain ⟨z,hz,hdz,herr⟩ := hlift n y ((hsrc n y).mpr hxF)
      ((htarget n (f y)).mpr (by simpa only [hd] using hdx))
    refine ⟨e z,?_,(hsrc n z).mp hz,?_,?_⟩
    · rw [← range_eq_span b c φ hφ e he]
      exact ⟨z,rfl⟩
    · rw [hd,hdz,map_zero]
    · simpa only [map_sub] using (hlo n (y-z)).mp herr
  · intro hlift n x hx hdx
    have hxW : e x∈Submodule.span K (c '' Set.range φ) := by
      rw [← range_eq_span b c φ hφ e he]
      exact ⟨x,rfl⟩
    obtain ⟨y,hyW,hyF,hdy,herr⟩ := hlift n (e x) hxW ((hsrc n x).mp hx)
      (by simpa only [hd] using (htarget n (f x)).mp hdx)
    rw [← range_eq_span b c φ hφ e he] at hyW
    obtain ⟨z,rfl⟩ := hyW
    refine ⟨z,(hsrc n z).mpr hyF,?_,?_⟩
    · apply injective b' c ψ hψ e' he'
      rw [map_zero,← hd,hdy]
    · apply (hlo n (x-z)).mpr
      simpa only [map_sub] using herr

end FourPapers.BasisEmbedding

namespace FourPapers.BasisEmbedding

open Classical FilteredHomology

variable {K X Y M I J T : Type*} [CommRing K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup M] [Module K M]
  (b : Module.Basis I K X) (b' : Module.Basis J K Y) (c : Module.Basis T K M)
  (φ : I → T) (hφ : Function.Injective φ) (ψ : J → T) (hψ : Function.Injective ψ)
  (e : X →ₗ[K] M) (e' : Y →ₗ[K] M)
  (he : ∀ i, e (b i) = c (φ i)) (he' : ∀ i, e' (b' i) = c (ψ i))
  (w : T → ℕ) (f : X →ₗ[K] Y) (D : Module.End K M)
  (hd : ∀ x, D (e x) = e' (f x))

include hφ hψ he he' hd in
/-- The one-step convention is explicit: the finite filtration uses
weights `< n`, while the ordered Rees filtration uses weights `≤ n`. -/
theorem coordinate_lifts_iff :
    LiftsCycles (Universal.basisFiltration b (fun i => w (φ i)))
      (Universal.basisFiltration b' (fun i => w (ψ i))) f ↔
    BasisCycleLifting.LiftsOn c w D (Submodule.span K (c '' Set.range φ)) := by
  have hsrc (n : ℕ) (x : X) :
      x ∈ (Universal.basisFiltration b (fun i => w (φ i))).level (n+1) ↔
        e x ∈ BasisCycleLifting.level c w n := by
    change x ∈ Submodule.span K (b '' {i | w (φ i) < n+1}) ↔ _
    simp only [Nat.lt_succ_iff]
    exact span_iff b c φ hφ e he w (fun r => r ≤ n) x
  have hsrcLower (n : ℕ) (x : X) :
      x ∈ (Universal.basisFiltration b (fun i => w (φ i))).level n ↔
        e x ∈ BasisCycleLifting.lower c w n :=
    span_iff b c φ hφ e he w (fun r => r < n) x
  have htgtLower (n : ℕ) (y : Y) :
      y ∈ (Universal.basisFiltration b' (fun i => w (ψ i))).level n ↔
        e' y ∈ BasisCycleLifting.lower c w n :=
    span_iff b' c ψ hψ e' he' w (fun r => r < n) y
  constructor
  · intro hlift n x hx hxF hdx
    rw [← range_eq_span b c φ hφ e he] at hx
    obtain ⟨y,rfl⟩ := hx
    obtain ⟨z,hz,hdz,herr⟩ := hlift n y ((hsrc n y).mpr hxF)
      ((htgtLower n (f y)).mpr (by simpa only [hd] using hdx))
    refine ⟨e z,?_,(hsrc n z).mp hz,?_,?_⟩
    · rw [← range_eq_span b c φ hφ e he]
      exact ⟨z,rfl⟩
    · rw [hd,hdz,map_zero]
    · have hh := (hsrcLower n (y-z)).mp herr
      simpa only [map_sub] using hh
  · intro hlift n x hx hdx
    have hxW : e x ∈ Submodule.span K (c '' Set.range φ) := by
      rw [← range_eq_span b c φ hφ e he]
      exact ⟨x,rfl⟩
    obtain ⟨y,hyW,hyF,hdy,herr⟩ := hlift n (e x) hxW ((hsrc n x).mp hx)
      (by simpa only [hd] using (htgtLower n (f x)).mp hdx)
    rw [← range_eq_span b c φ hφ e he] at hyW
    obtain ⟨z,rfl⟩ := hyW
    refine ⟨z,(hsrc n z).mpr hyF,?_,?_⟩
    · apply injective b' c ψ hψ e' he'
      rw [map_zero,← hd,hdy]
    · apply (hsrcLower n (x-z)).mpr
      simpa only [map_sub] using herr

end FourPapers.BasisEmbedding

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.GroebnerReesCoordinateLifting -/
section

/-! # Actual ideal-power coordinate lifts and Rees cycle lifts

The coordinate modules contain coefficients in the literal ideals `J^s`.
Their inclusions are the ordinary tensor Koszul inclusions followed by the
actual auxiliary-degree inclusion into the Rees algebra.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg CommAlg.Koszul MvPolynomial FilteredHomology
open scoped TensorProduct

universe u
variable {K V : Type u} [CommRing K] [Nontrivial K] [Fintype V] [LinearOrder V]
  (m : MonomialOrder V) (J : Ideal (MvPolynomial V K))
  (G : ℕ → Set (MvPolynomial V K))
  (hG : ∀ s, m.IsGroebnerBasis (G s) (J^s))
  (hu : ∀ s g, g ∈ G s → g ≠ 0 → IsUnit (m.leadingCoeff g))

abbrev PowerIdealIndex (s p : ℕ) := Σ F : Set.powersetCard V p, NonstandardIndex m (J^s)
abbrev PowerIdealCoordinates (s p : ℕ) := Set.powersetCard V p →₀ idealPowerPiece J s

def powerIdealCoefficientBasis (s p : ℕ) :
    Module.Basis (PowerIdealIndex m J s p) K (PowerIdealCoordinates J s p) :=
  Finsupp.basis (fun _ => groebnerPowerBasis J m G hG hu s)

def powerIdealReesIndex (s p : ℕ) (a : PowerIdealIndex m J s p) : IdealReesKoszulIndex m J :=
  (⟨s,a.2⟩,a.1.val)

theorem powerIdealReesIndex_injective (s p : ℕ) :
    Function.Injective (powerIdealReesIndex m J s p) := by
  rintro ⟨F,a⟩ ⟨H,b⟩ h
  have hF : F=H := Subtype.ext (congrArg Prod.snd h)
  subst H
  have hab : a.val=b.val := congrArg (fun t : IdealReesKoszulIndex m J => t.1.2.val) h
  exact congrArg (Sigma.mk F) (Subtype.ext hab)

def powerCoordinateInclusion (s p : ℕ) :
    PowerIdealCoordinates J s p →ₗ[K] IdealReesKoszul J :=
  (powerKoszulInclusion J s).comp (TensorExteriorKoszul.lift (K:=K) (M:=idealPowerPiece J s) p)

theorem powerCoordinateInclusion_basis (s p : ℕ) (a : PowerIdealIndex m J s p) :
    powerCoordinateInclusion J s p (powerIdealCoefficientBasis m J G hG hu s p a) =
      groebnerReesKoszulBasis m J G hG hu (powerIdealReesIndex m J s p a) := by
  rw [powerCoordinateInclusion,LinearMap.comp_apply,powerIdealCoefficientBasis,
    Finsupp.coe_basis,TensorExteriorKoszul.lift_single]
  simpa only [idealPowerKoszulBasis, Module.Basis.tensorProduct_apply', powerIdealReesIndex] using
    powerKoszulInclusion_basis m J G hG hu s (a.2,a.1.val)

def powerPreviousDifferential (s : ℕ) : ∀ p : ℕ,
    PowerIdealCoordinates J s p →ₗ[K] PowerIdealCoordinates J s p.pred
  | 0 => 0
  | p+1 => (CommAlg.Koszul.coordinateDifferential (X : V → MvPolynomial V K)
      (ModuleCat.of (MvPolynomial V K) (idealPowerPiece J s)) p).restrictScalars K

theorem powerCoordinateInclusion_d (s p : ℕ) (x : PowerIdealCoordinates J s p) :
    (idealReesKoszulDGA J).d (powerCoordinateInclusion J s p x) =
      powerCoordinateInclusion J s p.pred (powerPreviousDifferential J s p x) := by
  rw [powerCoordinateInclusion,LinearMap.comp_apply,powerKoszulInclusion_d]
  cases p with
  | zero =>
    have he : (idealPowerKoszulDifferential J s).comp
        (TensorExteriorKoszul.lift (K:=K) (M:=idealPowerPiece J s) 0) = 0 := by
      apply Finsupp.lhom_ext
      intro F a
      simp only [LinearMap.comp_apply,TensorExteriorKoszul.lift_single,
        LinearMap.zero_apply,idealPowerKoszulDifferential,
        TensorExteriorKoszul.differential_tmul]
      have hF : F.val=∅ := Finset.card_eq_zero.mp F.property
      simp only [hF,Simplicial.contraction_basis,Finset.notMem_empty,if_false,
        TensorProduct.tmul_zero,Finset.sum_const_zero]
    have hz := LinearMap.congr_fun he x
    change idealPowerKoszulDifferential J s (TensorExteriorKoszul.lift 0 x)=0 at hz
    simp only [hz,map_zero,powerPreviousDifferential,LinearMap.zero_apply]
  | succ p =>
    have he := TensorExteriorKoszul.differential_lift (K:=K) (R:=MvPolynomial V K)
      (M:=idealPowerPiece J s) (X : V → MvPolynomial V K) p x
    exact congrArg (powerKoszulInclusion J s) he

def powerCoordinateFiltration (ω : V → ℕ) (s p : ℕ) :
    Filtration (K:=K) (PowerIdealCoordinates J s p) :=
  Universal.basisFiltration (powerIdealCoefficientBasis m J G hG hu s p)
    (fun a => Finsupp.weight ω (a.2.val + faceExponent a.1.val))

/-- The finite weight on a power coordinate is the pullback of the
actual Rees weight along its literal basis inclusion. -/
theorem powerIdealReesIndex_weight (ω : V → ℕ) (s p : ℕ)
    (a : PowerIdealIndex m J s p) :
    WeightedRees.weight m J ω (powerIdealReesIndex m J s p a) =
      Finsupp.weight ω (a.2.val + faceExponent a.1.val) := rfl

/-- The same identity holds for the original monomial order. -/
theorem powerIdealReesIndex_order_weight (s p : ℕ) (a : PowerIdealIndex m J s p) :
    reesKoszulWeight m J (powerIdealReesIndex m J s p a) =
      m.toSyn (a.2.val + faceExponent a.1.val) := rfl

section
attribute [local irreducible] powerIdealCoefficientBasis groebnerReesKoszulBasis
  idealReesKoszulDGA

set_option diagnostics true in
set_option maxHeartbeats 300000 in
set_option backward.isDefEq.respectTransparency true in
theorem powerCoordinate_lifts_iff (ω : V → ℕ) (s p : ℕ) :
    LiftsCycles (powerCoordinateFiltration m J G hG hu ω s p)
      (powerCoordinateFiltration m J G hG hu ω s p.pred) (powerPreviousDifferential J s p) ↔
    BasisCycleLifting.LiftsOn (groebnerReesKoszulBasis m J G hG hu)
      (WeightedRees.weight m J ω) (idealReesKoszulDGA J).d
      (Submodule.span K ((groebnerReesKoszulBasis m J G hG hu) ''
        Set.range (powerIdealReesIndex m J s p))) := by
  have he := BasisEmbedding.coordinate_lifts_iff (K := K)
    (X := PowerIdealCoordinates J s p) (Y := PowerIdealCoordinates J s p.pred)
    (M := IdealReesKoszul J)
    (I := PowerIdealIndex m J s p) (J := PowerIdealIndex m J s p.pred)
    (T := IdealReesKoszulIndex m J)
    (powerIdealCoefficientBasis m J G hG hu s p)
    (powerIdealCoefficientBasis m J G hG hu s p.pred)
    (groebnerReesKoszulBasis m J G hG hu)
    (powerIdealReesIndex m J s p) (powerIdealReesIndex_injective m J s p)
    (powerIdealReesIndex m J s p.pred) (powerIdealReesIndex_injective m J s p.pred)
    (powerCoordinateInclusion J s p) (powerCoordinateInclusion J s p.pred)
    (powerCoordinateInclusion_basis m J G hG hu s p)
    (powerCoordinateInclusion_basis m J G hG hu s p.pred)
    (WeightedRees.weight m J ω) (powerPreviousDifferential J s p)
    (idealReesKoszulDGA J).d (powerCoordinateInclusion_d J s p)

  simpa only [powerCoordinateFiltration, powerIdealReesIndex_weight] using he

end

theorem powerIdealReesIndex_range (s p : ℕ) :
    Set.range (powerIdealReesIndex m J s p) =
      {a : IdealReesKoszulIndex m J | a.1.1=s ∧ (a.2.card : ℤ)=p} := by
  ext a
  constructor
  · rintro ⟨⟨F,b⟩,rfl⟩
    exact ⟨rfl,by exact_mod_cast F.property⟩
  · rintro ⟨hs,hp⟩
    rcases a with ⟨⟨t,a⟩,F⟩
    dsimp only at hs hp
    subst t
    exact ⟨⟨⟨F,by exact_mod_cast hp⟩,a⟩,rfl⟩

theorem basisSpan_inf_piece {A : Type*} (S : Set (IdealReesKoszulIndex m J))
    (deg : IdealReesKoszulIndex m J → A) (a : A) :
    Submodule.span K ((groebnerReesKoszulBasis m J G hG hu) '' S) ⊓
      Grading.Piece (groebnerReesKoszulBasis m J G hG hu) deg a =
    Submodule.span K ((groebnerReesKoszulBasis m J G hG hu) '' {i | i∈S ∧ deg i=a}) := by
  ext x
  simp only [Submodule.mem_inf,Grading.Piece,Module.Basis.mem_span_image,
    Set.subset_def,Finset.mem_coe,Set.mem_setOf_eq]
  constructor
  · rintro ⟨hS,ha⟩ i hi
    exact ⟨hS i hi,ha i hi⟩
  · intro h
    exact ⟨fun i hi => (h i hi).1,fun i hi => (h i hi).2⟩

theorem groebnerReesKoszul_d_exterior (a : IdealReesKoszulIndex m J) :
    (idealReesKoszulDGA J).d (groebnerReesKoszulBasis m J G hG hu a) ∈
      Grading.Piece (groebnerReesKoszulBasis m J G hG hu)
        (fun z => (z.2.card : ℤ)) ((a.2.card : ℤ)-1) := by
  rw [Grading.mem_piece]
  intro z hz
  have he := (groebnerReesKoszul_d_auxiliary_exterior m J G hG hu a z hz).2
  omega

/-- Full first-power coordinate lifting, in every exterior degree, gives
the exact relative lifting hypothesis consumed by multiplicative propagation. -/
theorem auxiliary_basis_lifts_of_coordinate_lifts (ω : V → ℕ) (s : ℕ)
    (hlift : ∀ p, LiftsCycles (powerCoordinateFiltration m J G hG hu ω s p)
      (powerCoordinateFiltration m J G hG hu ω s p.pred) (powerPreviousDifferential J s p)) :
    BasisCycleLifting.LiftsOn (groebnerReesKoszulBasis m J G hG hu)
      (WeightedRees.weight m J ω) (idealReesKoszulDGA J).d
      (WeightedRees.auxiliaryPiece m J G hG hu s) := by
  apply BasisCycleLifting.liftsOn_of_homogeneous_lifts
    (groebnerReesKoszulBasis m J G hG hu) (WeightedRees.weight m J ω)
    (idealReesKoszulDGA J).d {a | a.1.1=s} (fun a => (a.2.card : ℤ))
    (fun p : ℤ => p-1) (by
      intro r t h
      change r - 1 = t - 1 at h
      omega)
    (groebnerReesKoszul_d_exterior m J G hG hu)
  intro p
  by_cases hp : 0≤p
  · obtain ⟨r,rfl⟩ := Int.eq_ofNat_of_zero_le hp
    rw [basisSpan_inf_piece]
    simpa only [powerIdealReesIndex_range, Set.mem_setOf_eq] using
      (powerCoordinate_lifts_iff m J G hG hu ω s r).mp (hlift r)
  · intro n x hx hxF hdx
    have hx0 : x=0 := by
      apply (groebnerReesKoszulBasis m J G hG hu).repr.injective
      ext a
      rw [map_zero,Finsupp.zero_apply]
      by_contra ha
      have he := (Grading.mem_piece _ _ p x).mp hx.2 a ha
      exact hp (he ▸ Int.natCast_nonneg a.2.card)
    refine ⟨0,Submodule.zero_mem _,Submodule.zero_mem _,map_zero _,?_⟩
    rw [hx0,sub_self]
    exact Submodule.zero_mem _

theorem powerIdealReesIndex_range_degree (s p : ℕ) :
    Set.range (powerIdealReesIndex m J s p) =
      {a : IdealReesKoszulIndex m J | (a.1.1,(a.2.card : ℤ))=(s,(p : ℤ))} := by
  rw [powerIdealReesIndex_range]
  ext a
  change (a.1.1 = s ∧ (a.2.card : ℤ) = (p : ℤ)) ↔
    (a.1.1,(a.2.card : ℤ)) = (s,(p : ℤ))
  exact ⟨fun h => Prod.ext h.1 h.2,
    fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩

theorem groebnerReesKoszul_d_auxiliary_exterior_piece (a : IdealReesKoszulIndex m J) :
    (idealReesKoszulDGA J).d (groebnerReesKoszulBasis m J G hG hu a) ∈
      Grading.Piece (groebnerReesKoszulBasis m J G hG hu)
        (fun z => (z.1.1,(z.2.card : ℤ))) (a.1.1,(a.2.card : ℤ)-1) := by
  rw [Grading.mem_piece]
  intro z hz
  have he := groebnerReesKoszul_d_auxiliary_exterior m J G hG hu a z hz
  exact Prod.ext he.1 (by omega)

variable (I : Ideal (MvPolynomial V K))
  (hinit : ∀ s, initialIdealForBasis m (J^s)=I^s)
  (ω : V → ℕ)
  (htail : ∀ s g, g∈G s → g≠0 → ∀ a∈(monomial (m.degree g) 1-g).support,
    Finsupp.weight ω a < Finsupp.weight ω (m.degree g))

local notation "F" => WeightedRees.filtration m J I hinit G hG hu ω htail
local notation "b" => groebnerReesKoszulBasis m J G hG hu
local notation "w" => WeightedRees.weight m J ω

theorem relative_lifts_of_power_coordinate_lifts (s : ℕ)
    (hlift : ∀ p, LiftsCycles (powerCoordinateFiltration m J G hG hu ω s p)
      (powerCoordinateFiltration m J G hG hu ω s p.pred) (powerPreviousDifferential J s p)) :
    (F).RelativeLiftsCycles (idealReesKoszulDGA J) (WeightedRees.auxiliaryPiece m J G hG hu s) := by
  apply (OrderedBasis.relativeLiftsCycles_iff_basisLifts b w
    (fun a ha => le_of_eq (WeightedRees.one_weight m J G hG hu ω a ha))
    (OrderedBasis.product_nonincreasing b (initialReesKoszulBasis m J I hinit G hG hu) w
      (WeightedRees.product_homogeneous m J I hinit G hG hu ω)
      (WeightedRees.product_leading m J I hinit G hG hu ω htail))
    (idealReesKoszulDGA J) (WeightedRees.auxiliaryPiece m J G hG hu s)).mpr
  exact auxiliary_basis_lifts_of_coordinate_lifts m J G hG hu ω s hlift

/-- Global multiplicative lifting restricts to every actual ideal power and
every exterior degree. Projection is performed on actual cycle lifts. -/
theorem power_coordinate_lifts_of_all_lifts
    (hlift : (F).LiftsCycles (idealReesKoszulDGA J)) (s p : ℕ) :
    LiftsCycles (powerCoordinateFiltration m J G hG hu ω s p)
      (powerCoordinateFiltration m J G hG hu ω s p.pred) (powerPreviousDifferential J s p) := by
  apply (powerCoordinate_lifts_iff m J G hG hu ω s p).mpr
  rw [powerIdealReesIndex_range_degree]
  let deg := fun a : IdealReesKoszulIndex m J => (a.1.1,(a.2.card : ℤ))
  let shift := fun a : ℕ × ℤ => (a.1,a.2-1)
  have hshift : Function.Injective shift := by
    rintro ⟨a,r⟩ ⟨a',t⟩ h
    have hq : r - 1 = t - 1 := congrArg Prod.snd h
    have ha : a = a' := congrArg Prod.fst h
    exact Prod.ext ha (by omega)
  have hD : ∀ a, (idealReesKoszulDGA J).d (b a) ∈ Grading.Piece b deg (shift (deg a)) :=
    groebnerReesKoszul_d_auxiliary_exterior_piece m J G hG hu
  intro n x hx hxF hdx
  have hdx' : (idealReesKoszulDGA J).d x ∈ (F).lower n := by
    rw [WeightedRees.filtration, OrderedBasis.comparisonFiltration,
      OrderedBasis.filtration_lower]
    exact hdx
  obtain ⟨y,hyF,hdy,herr⟩ := hlift n x hxF hdx'
  have herr' : x-y ∈ BasisCycleLifting.lower b w n := by
    rw [WeightedRees.filtration, OrderedBasis.comparisonFiltration,
      OrderedBasis.filtration_lower] at herr
    exact herr
  have hxPiece : x ∈ Grading.Piece b deg (s,(p:ℤ)) := hx
  let z := Grading.projection b deg (s,(p:ℤ)) y
  refine ⟨z,Grading.projection_mem b deg (s,(p:ℤ)) y,
    projection_preserves_basisSpan b deg (s,(p:ℤ)) {a | w a≤n} y hyF,?_,?_⟩
  · have he := LinearMap.congr_fun
      (shiftedProjection_commutes b b deg deg shift hshift (idealReesKoszulDGA J).d hD (s,(p:ℤ))) y
    simpa only [LinearMap.comp_apply,hdy,map_zero] using he
  · have he := projection_preserves_basisSpan b deg (s,(p:ℤ)) {a | w a<n} (x-y) herr'
    simpa only [z, BasisCycleLifting.lower, map_sub,
      Grading.projection_eq_self hxPiece] using he

include htail in
/-- Ring-valued multiplicative propagation stated entirely with actual
ideal-power coordinate complexes. This is the interface used over ℤ[z]. -/
theorem all_power_coordinate_lifts
    (hgen : Algebra.adjoin K
      (IntegerFiltered.MultiplicativeFiltration.selectedHomologyClasses (idealReesKoszulDGA I)
        (WeightedRees.initialAuxiliaryPiece m J I hinit G hG hu 1))=⊤)
    (hfirst : ∀ p, LiftsCycles (powerCoordinateFiltration m J G hG hu ω 1 p)
      (powerCoordinateFiltration m J G hG hu ω 1 p.pred) (powerPreviousDifferential J 1 p))
    (s p : ℕ) :
    LiftsCycles (powerCoordinateFiltration m J G hG hu ω s p)
      (powerCoordinateFiltration m J G hG hu ω s p.pred) (powerPreviousDifferential J s p) :=
  power_coordinate_lifts_of_all_lifts m J G hG hu I hinit ω htail
    (WeightedRees.all_cycle_lifts m J I hinit G hG hu ω htail hgen
      (relative_lifts_of_power_coordinate_lifts m J G hG hu I hinit ω htail 1 hfirst)) s p

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.GroebnerReesCoordinateLeading -/
section

/-! # Leading coefficients of the literal ideal-power coordinate differential -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg CommAlg.Koszul MvPolynomial FilteredHomology
open scoped TensorProduct

universe u
variable {K V : Type u} [CommRing K] [Nontrivial K] [Fintype V] [LinearOrder V]
  (m : MonomialOrder V) (J I : Ideal (MvPolynomial V K))
  (hinit : ∀ s, initialIdealForBasis m (J^s)=I^s)
  (G : ℕ → Set (MvPolynomial V K))
  (hG : ∀ s, m.IsGroebnerBasis (G s) (J^s))
  (hu : ∀ s g, g∈G s → g≠0 → IsUnit (m.leadingCoeff g))

def initialPowerCoordinateBasis (s p : ℕ) :
    Module.Basis (PowerIdealIndex m J s p) K (PowerIdealCoordinates I s p) :=
  Finsupp.basis (fun _ => initialPowerBasis m J I hinit G hG hu s)

theorem initialPowerCoordinateInclusion_basis (s p : ℕ) (a : PowerIdealIndex m J s p) :
    powerCoordinateInclusion I s p (initialPowerCoordinateBasis m J I hinit G hG hu s p a) =
      initialReesKoszulBasis m J I hinit G hG hu (powerIdealReesIndex m J s p a) := by
  simp only [powerCoordinateInclusion,LinearMap.comp_apply,initialPowerCoordinateBasis,
    Finsupp.coe_basis,TensorExteriorKoszul.lift_single,powerKoszulInclusion,
    TensorProduct.map_tmul,LinearMap.id_apply,initialReesKoszulBasis,
    Module.Basis.tensorProduct_apply',powerIdealReesIndex,initialReesBasis_apply]

theorem powerPreviousDifferential_repr_rees (s p : ℕ)
    (x : PowerIdealCoordinates J s p) (a : PowerIdealIndex m J s p.pred) :
    (powerIdealCoefficientBasis m J G hG hu s p.pred).repr
      (powerPreviousDifferential J s p x) a =
    (groebnerReesKoszulBasis m J G hG hu).repr
      ((idealReesKoszulDGA J).d (powerCoordinateInclusion J s p x))
        (powerIdealReesIndex m J s p.pred a) := by
  rw [powerCoordinateInclusion_d]
  exact (BasisEmbedding.repr_image (K := K)
    (X := PowerIdealCoordinates J s p.pred) (M := IdealReesKoszul J)
    (I := PowerIdealIndex m J s p.pred) (J := IdealReesKoszulIndex m J)
    (powerIdealCoefficientBasis m J G hG hu s p.pred)
    (groebnerReesKoszulBasis m J G hG hu)
    (powerIdealReesIndex m J s p.pred) (powerIdealReesIndex_injective m J s p.pred)
    (powerCoordinateInclusion J s p.pred)
    (powerCoordinateInclusion_basis m J G hG hu s p.pred)
    (powerPreviousDifferential J s p x) a).symm

theorem initialPowerPreviousDifferential_repr_rees (s p : ℕ)
    (x : PowerIdealCoordinates I s p) (a : PowerIdealIndex m J s p.pred) :
    (initialPowerCoordinateBasis m J I hinit G hG hu s p.pred).repr
      (powerPreviousDifferential I s p x) a =
    (initialReesKoszulBasis m J I hinit G hG hu).repr
      ((idealReesKoszulDGA I).d (powerCoordinateInclusion I s p x))
        (powerIdealReesIndex m J s p.pred a) := by
  rw [powerCoordinateInclusion_d]
  exact (BasisEmbedding.repr_image (K := K)
    (X := PowerIdealCoordinates I s p.pred) (M := IdealReesKoszul I)
    (I := PowerIdealIndex m J s p.pred) (J := IdealReesKoszulIndex m J)
    (initialPowerCoordinateBasis m J I hinit G hG hu s p.pred)
    (initialReesKoszulBasis m J I hinit G hG hu)
    (powerIdealReesIndex m J s p.pred) (powerIdealReesIndex_injective m J s p.pred)
    (powerCoordinateInclusion I s p.pred)
    (initialPowerCoordinateInclusion_basis m J I hinit G hG hu s p.pred)
    (powerPreviousDifferential I s p x) a).symm

theorem power_coordinate_differential_order_leading (s p : ℕ)
    (a : PowerIdealIndex m J s p) (z : PowerIdealIndex m J s p.pred)
    (hz : m.toSyn (a.2.val+faceExponent a.1.val) ≤
      m.toSyn (z.2.val+faceExponent z.1.val)) :
    (powerIdealCoefficientBasis m J G hG hu s p.pred).repr
      (powerPreviousDifferential J s p (powerIdealCoefficientBasis m J G hG hu s p a)) z =
    (initialPowerCoordinateBasis m J I hinit G hG hu s p.pred).repr
      (powerPreviousDifferential I s p (initialPowerCoordinateBasis m J I hinit G hG hu s p a)) z := by
  rw [powerPreviousDifferential_repr_rees,initialPowerPreviousDifferential_repr_rees,
    powerCoordinateInclusion_basis,initialPowerCoordinateInclusion_basis]
  exact OrderedRees.differential_leading m J I hinit G hG hu _ _ hz

theorem power_coordinate_differential_weight_leading
    (ω : V → ℕ)
    (htail : ∀ s g, g∈G s → g≠0 → ∀ a∈(monomial (m.degree g) 1-g).support,
      Finsupp.weight ω a < Finsupp.weight ω (m.degree g))
    (s p : ℕ) (a : PowerIdealIndex m J s p) (z : PowerIdealIndex m J s p.pred)
    (hz : Finsupp.weight ω (a.2.val+faceExponent a.1.val) ≤
      Finsupp.weight ω (z.2.val+faceExponent z.1.val)) :
    (powerIdealCoefficientBasis m J G hG hu s p.pred).repr
      (powerPreviousDifferential J s p (powerIdealCoefficientBasis m J G hG hu s p a)) z =
    (initialPowerCoordinateBasis m J I hinit G hG hu s p.pred).repr
      (powerPreviousDifferential I s p (initialPowerCoordinateBasis m J I hinit G hG hu s p a)) z := by
  rw [powerPreviousDifferential_repr_rees,initialPowerPreviousDifferential_repr_rees,
    powerCoordinateInclusion_basis,initialPowerCoordinateInclusion_basis]
  exact WeightedRees.differential_leading m J I hinit G hG hu ω htail _ _ hz

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphHomologyDecomposition -/
section

/-! # Explicit coordinate changes and products of three-term homology

These maps act on literal kernels and boundary ranges. The product statement
uses actual componentwise differentials and applies over a commutative ring;
it neither invokes dimensions nor chooses an assumed homology basis.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace FourPapers.FilteredHomology
open Classical

section Congruence
variable {R X Y Z X' Y' Z' : Type*} [CommRing R]
  [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
  [AddCommGroup Z] [Module R Z] [AddCommGroup X'] [Module R X']
  [AddCommGroup Y'] [Module R Y'] [AddCommGroup Z'] [Module R Z']
  (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (hfg : g.comp f = 0)
  (f' : X' →ₗ[R] Y') (g' : Y' →ₗ[R] Z') (hfg' : g'.comp f' = 0)
  (eX : X ≃ₗ[R] X') (eY : Y ≃ₗ[R] Y') (eZ : Z ≃ₗ[R] Z')
  (hf : ∀ x, eY (f x) = f' (eX x))
  (hg : ∀ y, eZ (g y) = g' (eY y))

def threeTermCyclesEquiv : LinearMap.ker g ≃ₗ[R] LinearMap.ker g' where
  toFun x := ⟨eY x.val, by
    change g' (eY x.val) = 0
    rw [← hg, x.property, eZ.map_zero]⟩
  invFun y := ⟨eY.symm y.val, by
    change g (eY.symm y.val) = 0
    apply eZ.injective
    rw [hg, eY.apply_symm_apply, y.property, eZ.map_zero]⟩
  left_inv x := Subtype.ext (eY.symm_apply_apply x.val)
  right_inv y := Subtype.ext (eY.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (map_add eY x.val y.val)
  map_smul' r x := Subtype.ext (map_smul eY r x.val)

include eX hf in
lemma threeTermCyclesEquiv_boundaries :
    (LinearMap.range (boundaryMap f g hfg)).map
      (threeTermCyclesEquiv g g' eY eZ hg).toLinearMap =
    LinearMap.range (boundaryMap f' g' hfg') := by
  ext z
  constructor
  · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
    exact ⟨eX a, Subtype.ext (hf a).symm⟩
  · rintro ⟨a, rfl⟩
    refine ⟨boundaryMap f g hfg (eX.symm a), ⟨eX.symm a, rfl⟩, ?_⟩
    apply Subtype.ext
    change eY (f (eX.symm a)) = f' a
    rw [hf, eX.apply_symm_apply]

def threeTermHomologyEquiv : Homology f g hfg ≃ₗ[R] Homology f' g' hfg' :=
  Submodule.Quotient.equiv _ _ (threeTermCyclesEquiv g g' eY eZ hg)
    (threeTermCyclesEquiv_boundaries f g hfg f' g' hfg' eX eY eZ hf hg)

end Congruence

section Product
variable {R I : Type*} [CommRing R]
  {X Y Z : I → Type*}
  [∀ i, AddCommGroup (X i)] [∀ i, Module R (X i)]
  [∀ i, AddCommGroup (Y i)] [∀ i, Module R (Y i)]
  [∀ i, AddCommGroup (Z i)] [∀ i, Module R (Z i)]
  (f : ∀ i, X i →ₗ[R] Y i) (g : ∀ i, Y i →ₗ[R] Z i)
  (hfg : ∀ i, (g i).comp (f i) = 0)

def componentwiseMap (f : ∀ i, X i →ₗ[R] Y i) : (∀ i, X i) →ₗ[R] (∀ i, Y i) :=
  LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))

@[simp] lemma componentwiseMap_apply (x : ∀ i, X i) (i : I) :
    componentwiseMap f x i = f i (x i) := rfl

include hfg in
lemma componentwiseMap_comp : (componentwiseMap g).comp (componentwiseMap f) = 0 := by
  apply LinearMap.ext
  intro x
  funext i
  exact LinearMap.congr_fun (hfg i) (x i)

def componentwiseCycleEvaluation (i : I) :
    LinearMap.ker (componentwiseMap g) →ₗ[R] LinearMap.ker (g i) :=
  ((LinearMap.proj i).comp (LinearMap.ker (componentwiseMap g)).subtype).codRestrict _
    (fun x => congrFun x.property i)

def componentwiseClass : LinearMap.ker (componentwiseMap g) →ₗ[R]
    ∀ i, Homology (f i) (g i) (hfg i) :=
  LinearMap.pi (fun i => (homologyClass (f i) (g i) (hfg i)).comp
    (componentwiseCycleEvaluation g i))

lemma componentwiseClass_surjective : Function.Surjective (componentwiseClass f g hfg) := by
  intro y
  choose z hz using fun i =>
    (LinearMap.range (boundaryMap (f i) (g i) (hfg i))).mkQ_surjective (y i)
  refine ⟨⟨fun i => (z i).val, ?_⟩, ?_⟩
  · funext i
    exact (z i).property
  · funext i
    exact hz i

lemma componentwiseClass_ker :
    LinearMap.ker (componentwiseClass f g hfg) =
      LinearMap.range (boundaryMap (componentwiseMap f) (componentwiseMap g)
        (componentwiseMap_comp f g hfg)) := by
  ext x
  rw [LinearMap.mem_ker]
  constructor
  · intro hx
    have hi (i : I) : ∃ a : X i, f i a = x.val i := by
      have hzero := congrFun hx i
      change homologyClass (f i) (g i) (hfg i)
        (componentwiseCycleEvaluation g i x) = 0 at hzero
      obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero
        (LinearMap.range (boundaryMap (f i) (g i) (hfg i)))).mp hzero
      exact ⟨a, congrArg Subtype.val ha⟩
    choose a ha using hi
    exact ⟨a, Subtype.ext (funext ha)⟩
  · rintro ⟨a, rfl⟩
    funext i
    apply (Submodule.Quotient.mk_eq_zero
      (LinearMap.range (boundaryMap (f i) (g i) (hfg i)))).mpr
    exact ⟨a i, rfl⟩

/-- Actual componentwise homology commutes with products. A finite product
will be used for the finitely many fine degrees in a fixed ordinary degree. -/
def componentwiseHomologyEquiv :
    Homology (componentwiseMap f) (componentwiseMap g) (componentwiseMap_comp f g hfg) ≃ₗ[R]
      ∀ i, Homology (f i) (g i) (hfg i) :=
  (Submodule.quotEquivOfEq _ _ (componentwiseClass_ker f g hfg).symm).trans
    ((componentwiseClass f g hfg).quotKerEquivOfSurjective
      (componentwiseClass_surjective f g hfg))

end Product

section ProductComparison

variable {R X Y Z I : Type*} [CommRing R]
  [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
  [AddCommGroup Z] [Module R Z]
  {X' Y' Z' H' : I → Type*}
  [∀ i, AddCommGroup (X' i)] [∀ i, Module R (X' i)]
  [∀ i, AddCommGroup (Y' i)] [∀ i, Module R (Y' i)]
  [∀ i, AddCommGroup (Z' i)] [∀ i, Module R (Z' i)]
  [∀ i, AddCommGroup (H' i)] [∀ i, Module R (H' i)]

/-- A three-term complex identified componentwise with a product has the
product of the component homologies.  Keeping the ambient modules abstract
here avoids unfolding concrete polynomial bases when this comparison is used. -/
def threeTermProductHomologyEquiv
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (hfg : g.comp f = 0)
    (f' : ∀ i, X' i →ₗ[R] Y' i) (g' : ∀ i, Y' i →ₗ[R] Z' i)
    (hfg' : ∀ i, (g' i).comp (f' i) = 0)
    (eX : X ≃ₗ[R] ∀ i, X' i) (eY : Y ≃ₗ[R] ∀ i, Y' i)
    (eZ : Z ≃ₗ[R] ∀ i, Z' i)
    (hf : ∀ x i, eY (f x) i = f' i (eX x i))
    (hg : ∀ y i, eZ (g y) i = g' i (eY y i))
    (eH : ∀ i, Homology (f' i) (g' i) (hfg' i) ≃ₗ[R] H' i) :
    Homology f g hfg ≃ₗ[R] ∀ i, H' i :=
  (threeTermHomologyEquiv f g hfg
    (componentwiseMap f') (componentwiseMap g') (componentwiseMap_comp f' g' hfg')
    eX eY eZ (fun x => funext (hf x)) (fun y => funext (hg y))).trans
      ((componentwiseHomologyEquiv f' g' hfg').trans (LinearEquiv.piCongrRight eH))

end ProductComparison
end FourPapers.FilteredHomology

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ActualIdealLeading -/
section

/-! # The exact monomial model of the ideal's leading complex

The basis correspondence keeps each nonstandard exponent and each exterior
face. It identifies the leading chain groups with the actual monomial-ideal
Koszul coordinates. It is a coefficient-module equivalence; the original
and initial ideals are not identified as polynomial submodules.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000
noncomputable section

namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open FourPapers.Universal FourPapers.FilteredHomology
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance] ordinaryPieceAddCommGroup ordinaryPieceModule

private theorem basisEquiv_repr_apply
    {R X Y I J : Type*} [Semiring R]
    [AddCommMonoid X] [Module R X] [AddCommMonoid Y] [Module R Y]
    (b : Module.Basis I R X) (c : Module.Basis J R Y) (e : I ≃ J)
    (x : X) (i : I) : c.repr (b.equiv c e x) (e i) = b.repr x i := by
  have he : (c.coord (e i)).comp (b.equiv c e).toLinearMap = b.coord i := by
    apply b.ext
    intro j
    change (c.repr (b.equiv c e (b j))) (e i) = (b.repr (b j)) i
    simp only [Module.Basis.equiv_apply, Module.Basis.repr_self,
      Finsupp.single_apply, e.injective.eq_iff]
  exact LinearMap.congr_fun he x

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

/-- Nonstandard exponents are precisely monomials in the specified initial
ideal. The complement in the stored standard-monomial equality is used in
both directions. -/
def actualIdealMonomialIndexEquiv (P : QuotientGroebnerData V k) (p : ℕ) :
    ActualIdealIndex P p ≃ MonomialIndex P.family p where
  toFun a := ⟨a.1, ⟨a.2.val, by
    by_contra h
    exact a.2.property ((P.standard a.2.val).mpr h)⟩⟩
  invFun a := ⟨a.1, ⟨a.2.val, fun h => (P.standard a.2.val).mp h a.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem actualIdealMonomialIndexEquiv_degree (P : QuotientGroebnerData V k)
    (p : ℕ) (a : ActualIdealIndex P p) :
    monomialDegree (actualIdealMonomialIndexEquiv P p a) = actualIdealDegree a := rfl

def actualIdealMonomialEquiv (P : QuotientGroebnerData V k) (p : ℕ) :
    (Set.powersetCard V p →₀ P.ideal) ≃ₗ[k]
      (Set.powersetCard V p →₀ monomialIdeal k P.family) :=
  (actualIdealCoefficientBasis P p).equiv (monomialCoefficientBasis P.family p)
    (actualIdealMonomialIndexEquiv P p)

@[simp] theorem actualIdealMonomialEquiv_basis (P : QuotientGroebnerData V k)
    (p : ℕ) (a : ActualIdealIndex P p) :
    actualIdealMonomialEquiv P p (actualIdealCoefficientBasis P p a) =
      monomialCoefficientBasis P.family p (actualIdealMonomialIndexEquiv P p a) :=
  Module.Basis.equiv_apply _ _ _ _

theorem actualIdealMonomialEquiv_repr (P : QuotientGroebnerData V k) (p : ℕ)
    (x : Set.powersetCard V p →₀ P.ideal) (a : ActualIdealIndex P p) :
    (monomialCoefficientBasis P.family p).repr (actualIdealMonomialEquiv P p x)
      (actualIdealMonomialIndexEquiv P p a) = (actualIdealCoefficientBasis P p).repr x a :=
  basisEquiv_repr_apply (R := k)
    (X := Set.powersetCard V p →₀ P.ideal)
    (Y := Set.powersetCard V p →₀ monomialIdeal k P.family)
    (I := ActualIdealIndex P p) (J := MonomialIndex P.family p)
    (actualIdealCoefficientBasis P p) (monomialCoefficientBasis (k := k) P.family p)
    (actualIdealMonomialIndexEquiv P p) x a

theorem actualIdealMonomialEquiv_piece_iff {A : Type*}
    (P : QuotientGroebnerData V k) (p : ℕ) (coarse : Exponent V → A) (a : A)
    (x : Set.powersetCard V p →₀ P.ideal) :
    actualIdealMonomialEquiv P p x ∈
        Grading.Piece (monomialCoefficientBasis P.family p)
          (fun b => coarse (monomialDegree b)) a ↔
      x ∈ Grading.Piece (actualIdealCoefficientBasis P p)
        (fun b => coarse (actualIdealDegree b)) a := by
  rw [Grading.mem_piece, Grading.mem_piece]
  constructor
  · intro h b hb
    exact h (actualIdealMonomialIndexEquiv P p b)
      (by simpa only [actualIdealMonomialEquiv_repr] using hb)
  · intro h b hb
    obtain ⟨b, rfl⟩ := (actualIdealMonomialIndexEquiv P p).surjective b
    exact h b (by simpa only [actualIdealMonomialEquiv_repr] using hb)

/-- A basis-defined fine model piece is explicitly equivalent to the
literal fine component of the monomial ideal. -/
def actualIdealFineModelEquiv (P : QuotientGroebnerData V k) (α : Exponent V) (p : ℕ) :
    Grading.Piece (actualIdealCoefficientBasis P p) actualIdealDegree α ≃ₗ[k]
      homogeneousPiece (k := k) P.family α p where
  toFun x := ⟨actualIdealMonomialEquiv P p x.val,
    (actualIdealMonomialEquiv_piece_iff P p id α x.val).mpr x.property⟩
  invFun x := ⟨(actualIdealMonomialEquiv P p).symm x.val, by
    apply (actualIdealMonomialEquiv_piece_iff P p id α _).mp
    simpa only [homogeneousPiece, id_def, LinearEquiv.apply_symm_apply]
      using x.property⟩
  left_inv x := Subtype.ext (LinearEquiv.symm_apply_apply _ x.val)
  right_inv x := Subtype.ext (LinearEquiv.apply_symm_apply _ x.val)
  map_add' x y := Subtype.ext ((actualIdealMonomialEquiv P p).map_add x.val y.val)
  map_smul' r x := Subtype.ext ((actualIdealMonomialEquiv P p).map_smul r x.val)

/-- The actual monomial differential transported to the common basis of
the original ideal. This is the proposed leading map, subsequently proved
to be the associated differential by the strict coefficient comparison. -/
def initialActualIdealDifferential (P : QuotientGroebnerData V k) (p : ℕ) :
    (Set.powersetCard V (p+1) →₀ P.ideal) →ₗ[k] (Set.powersetCard V p →₀ P.ideal) :=
  (actualIdealMonomialEquiv P p).symm.toLinearMap.comp
    ((monomialDifferential P.family p).comp (actualIdealMonomialEquiv P (p+1)).toLinearMap)

def initialActualIdealPrevious (P : QuotientGroebnerData V k) : ∀ p : ℕ,
    (Set.powersetCard V p →₀ P.ideal) →ₗ[k] (Set.powersetCard V p.pred →₀ P.ideal)
  | 0 => 0
  | p+1 => initialActualIdealDifferential P p

@[simp] theorem actualIdealMonomialEquiv_differential (P : QuotientGroebnerData V k)
    (p : ℕ) (x : Set.powersetCard V (p+1) →₀ P.ideal) :
    actualIdealMonomialEquiv P p (initialActualIdealDifferential P p x) =
      monomialDifferential P.family p (actualIdealMonomialEquiv P (p+1) x) :=
  LinearEquiv.apply_symm_apply _ _

theorem initialActualIdealDifferential_basis_fine (P : QuotientGroebnerData V k)
    (p : ℕ) (a : ActualIdealIndex P (p+1)) :
    initialActualIdealDifferential P p (actualIdealCoefficientBasis P (p+1) a) ∈
      Grading.Piece (actualIdealCoefficientBasis P p) actualIdealDegree (actualIdealDegree a) := by
  apply (actualIdealMonomialEquiv_piece_iff P p id _ _).mp
  rw [actualIdealMonomialEquiv_differential, actualIdealMonomialEquiv_basis]
  have hb : monomialCoefficientBasis (k := k) P.family (p+1)
      (actualIdealMonomialIndexEquiv P (p+1) a) ∈
      homogeneousPiece (k := k) P.family (actualIdealDegree a) (p+1) := by
    simpa only [homogeneousPiece, actualIdealMonomialIndexEquiv_degree] using
      Grading.basis_mem_piece (monomialCoefficientBasis (k := k) P.family (p+1))
        monomialDegree (actualIdealMonomialIndexEquiv P (p+1) a)
  simpa only [homogeneousPiece, id_def] using
    monomialDifferential_homogeneous (k := k) P.family (actualIdealDegree a) p hb

theorem initialActualIdealDifferential_basis_regrade {A : Type*}
    (P : QuotientGroebnerData V k) (coarse : Exponent V → A) (p : ℕ)
    (a : ActualIdealIndex P (p+1)) :
    initialActualIdealDifferential P p (actualIdealCoefficientBasis P (p+1) a) ∈
      Grading.Piece (actualIdealCoefficientBasis P p)
        (fun b => coarse (actualIdealDegree b)) (coarse (actualIdealDegree a)) :=
  by
    rw [Grading.mem_piece]
    intro b hb
    exact congrArg coarse ((Grading.mem_piece (actualIdealCoefficientBasis P p)
      actualIdealDegree (actualIdealDegree a) _).mp
        (initialActualIdealDifferential_basis_fine P p a) b hb)

theorem initialActualIdealPrevious_basis_regrade {A : Type*}
    (P : QuotientGroebnerData V k) (coarse : Exponent V → A) (p : ℕ)
    (a : ActualIdealIndex P p) :
    initialActualIdealPrevious P p (actualIdealCoefficientBasis P p a) ∈
      Grading.Piece (actualIdealCoefficientBasis P p.pred)
        (fun b => coarse (actualIdealDegree b)) (coarse (actualIdealDegree a)) := by
  cases p with
  | zero => exact Submodule.zero_mem _
  | succ p => exact initialActualIdealDifferential_basis_regrade P coarse p a

theorem initialActualIdealDifferential_ordinary (P : QuotientGroebnerData V k) (q p : ℕ)
    (x : Set.powersetCard V (p+1) →₀ P.ideal)
    (hx : x ∈ actualIdealOrdinaryPiece P q (p+1)) :
    initialActualIdealDifferential P p x ∈ actualIdealOrdinaryPiece P q p :=
  map_mem_piece_of_basis_monoid (R := k)
    (X := Set.powersetCard V (p+1) →₀ P.ideal) (Y := Set.powersetCard V p →₀ P.ideal)
    (I := ActualIdealIndex P (p+1)) (J := ActualIdealIndex P p) (A := ℕ)
    (actualIdealCoefficientBasis P (p+1)) (actualIdealCoefficientBasis P p)
    (fun a => (actualIdealDegree a).degree) (fun a => (actualIdealDegree a).degree)
    (initialActualIdealDifferential P p)
    (initialActualIdealDifferential_basis_regrade P Finsupp.degree p) q hx

def initialActualIdealOrdinaryDifferential (P : QuotientGroebnerData V k) (q p : ℕ) :
    actualIdealOrdinaryPiece P q (p+1) →ₗ[k] actualIdealOrdinaryPiece P q p :=
  ((initialActualIdealDifferential P p).domRestrict
    (actualIdealOrdinaryPiece P q (p+1))).codRestrict
      (actualIdealOrdinaryPiece P q p)
      (fun x => initialActualIdealDifferential_ordinary P q p x.val x.property)

@[simp] theorem initialActualIdealOrdinaryDifferential_val
    (P : QuotientGroebnerData V k) (q p : ℕ) (x : actualIdealOrdinaryPiece P q (p+1)) :
    (initialActualIdealOrdinaryDifferential P q p x).val =
      initialActualIdealDifferential P p x.val := rfl

def initialActualIdealOrdinaryPrevious (P : QuotientGroebnerData V k) (q : ℕ) : ∀ p : ℕ,
    actualIdealOrdinaryPiece P q p →ₗ[k] actualIdealOrdinaryPiece P q p.pred
  | 0 => 0
  | p+1 => initialActualIdealOrdinaryDifferential P q p

@[simp] theorem initialActualIdealOrdinaryPrevious_val (P : QuotientGroebnerData V k)
    (q p : ℕ) (x : actualIdealOrdinaryPiece P q p) :
    (initialActualIdealOrdinaryPrevious P q p x).val = initialActualIdealPrevious P p x.val := by
  cases p <;> rfl

theorem initialActualIdealDifferential_comp (P : QuotientGroebnerData V k) (p : ℕ) :
    (initialActualIdealPrevious P p).comp (initialActualIdealDifferential P p) = 0 := by
  cases p with
  | zero => simp only [initialActualIdealPrevious, LinearMap.zero_comp]
  | succ p =>
      apply LinearMap.ext
      intro x
      apply (actualIdealMonomialEquiv P p).injective
      change actualIdealMonomialEquiv P p
        (initialActualIdealDifferential P p (initialActualIdealDifferential P (p+1) x)) = _
      rw [LinearMap.zero_apply, map_zero, actualIdealMonomialEquiv_differential,
        actualIdealMonomialEquiv_differential]
      exact LinearMap.congr_fun (monomialDifferential_comp P.family p)
        (actualIdealMonomialEquiv P (p+2) x)

theorem initialActualIdealOrdinaryDifferential_comp (P : QuotientGroebnerData V k)
    (q p : ℕ) :
    (initialActualIdealOrdinaryPrevious P q p).comp
      (initialActualIdealOrdinaryDifferential P q p) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [initialActualIdealOrdinaryPrevious_val]
  exact LinearMap.congr_fun (initialActualIdealDifferential_comp P p) x.val

abbrev initialActualIdealOrdinaryHomology (P : QuotientGroebnerData V k) (q p : ℕ) :=
  Homology (initialActualIdealOrdinaryDifferential P q p)
    (initialActualIdealOrdinaryPrevious P q p) (initialActualIdealOrdinaryDifferential_comp P q p)

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ActualIdealGradedMaps -/
section

/-! # Actual graded ideal differential maps

These literal associated differential maps and their strict comparison are
shared by the field Betti comparison and the integral homology decomposition.
The fine decomposition is developed separately in ClosedGraphIdealGradedHomology.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open FourPapers.Universal FourPapers.FilteredHomology
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance] ordinaryPieceAddCommGroup ordinaryPieceModule
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

variable (P : QuotientGroebnerData V k)
  (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k (fun _ : V => (1 : ℕ))))
  (w : V → ℕ)
  (htail : ∀ g ∈ P.generators, g ≠ 0 →
    ∀ a ∈ (monomial (P.order.degree g) 1-g).support,
      Finsupp.weight w a < Finsupp.weight w (P.order.degree g))
  (hstrict : ∀ p (a : ActualIdealIndex P p) (b : ActualIdealIndex P p.pred),
    Finsupp.weight w (actualIdealDegree a) ≤ Finsupp.weight w (actualIdealDegree b) →
    (actualIdealCoefficientBasis P p.pred).repr
      (actualIdealPreviousDifferential P.ideal p (actualIdealCoefficientBasis P p a) -
        initialActualIdealPrevious P p (actualIdealCoefficientBasis P p a)) b = 0)

theorem initialActualIdealOrdinaryPrevious_basis_weight (q p : ℕ)
    (a : {a : ActualIdealIndex P p // (actualIdealDegree a).degree = q}) :
    initialActualIdealOrdinaryPrevious P q p (actualIdealOrdinaryBasis P q p a) ∈
      Grading.Piece (actualIdealOrdinaryBasis P q p.pred)
        (fun b => Finsupp.weight w (actualIdealDegree b.val))
        (Finsupp.weight w (actualIdealDegree a.val)) := by
  rw [Grading.mem_piece]
  intro b hb
  rw [actualIdealOrdinaryBasis_repr, initialActualIdealOrdinaryPrevious_val,
    actualIdealOrdinaryBasis_val] at hb
  exact (Grading.mem_piece (actualIdealCoefficientBasis P p.pred)
    (fun i => Finsupp.weight w (actualIdealDegree i))
    (Finsupp.weight w (actualIdealDegree a.val)) _).mp
      (initialActualIdealPrevious_basis_regrade P (Finsupp.weight w) p a.val) b.val hb

include hstrict in
theorem actualIdealOrdinaryPrevious_strictly_lowers (q p : ℕ)
    (a : {a : ActualIdealIndex P p // (actualIdealDegree a).degree = q})
    (b : {b : ActualIdealIndex P p.pred // (actualIdealDegree b).degree = q})
    (hab : Finsupp.weight w (actualIdealDegree a.val) ≤
      Finsupp.weight w (actualIdealDegree b.val)) :
    (actualIdealOrdinaryBasis P q p.pred).repr
      ((actualIdealOrdinaryPrevious P hJ q p-initialActualIdealOrdinaryPrevious P q p)
        (actualIdealOrdinaryBasis P q p a)) b = 0 := by
  rw [actualIdealOrdinaryBasis_repr]
  cases p with
  | zero => simp only [actualIdealOrdinaryPrevious, initialActualIdealOrdinaryPrevious,
      sub_self, LinearMap.zero_apply, ZeroMemClass.coe_zero, map_zero, Finsupp.zero_apply]
  | succ p =>
      change (actualIdealCoefficientBasis P p).repr
        (actualIdealCoordinateDifferential P.ideal p
          ((actualIdealOrdinaryBasis P q (p+1) a).val) -
          initialActualIdealDifferential P p ((actualIdealOrdinaryBasis P q (p+1) a).val)) b.val = 0
      rw [actualIdealOrdinaryBasis_val]
      exact hstrict (p+1) a.val b.val hab

def actualIdealGradePrevious (q p n : ℕ) :
    Grade (actualIdealOrdinaryFiltration P w q p) n →ₗ[k]
      Grade (actualIdealOrdinaryFiltration P w q p.pred) n :=
  gradeMap _ _ (actualIdealOrdinaryPrevious P hJ q p)
    (actualIdealOrdinaryPrevious_preserves P hJ w htail q p) n

def actualIdealGradeDifferential (q p n : ℕ) :
    Grade (actualIdealOrdinaryFiltration P w q (p+1)) n →ₗ[k]
      Grade (actualIdealOrdinaryFiltration P w q p) n :=
  gradeMap _ _ (actualIdealOrdinaryDifferential P hJ q p)
    (actualIdealOrdinaryDifferential_preserves P hJ w htail q p) n

theorem actualIdealGradeDifferential_comp (q p n : ℕ) :
    (actualIdealGradePrevious P hJ w htail q p n).comp
      (actualIdealGradeDifferential P hJ w htail q p n) = 0 :=
  gradeMap_comp _ _ _ _ _
    (actualIdealOrdinaryDifferential_preserves P hJ w htail q p)
    (actualIdealOrdinaryPrevious_preserves P hJ w htail q p)
    (actualIdealOrdinaryDifferential_comp P hJ q p) n

abbrev actualIdealGradedHomology (q p n : ℕ) :=
  Homology (actualIdealGradeDifferential P hJ w htail q p n)
    (actualIdealGradePrevious P hJ w htail q p n)
    (actualIdealGradeDifferential_comp P hJ w htail q p n)

end FourPapers.Sublattice

end
end
end


end
