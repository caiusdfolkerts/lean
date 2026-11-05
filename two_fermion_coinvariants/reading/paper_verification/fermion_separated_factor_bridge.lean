module

public import PaperVerification.FermionSeparatedGlobalFormulas
public import PaperVerification.FermionHomogenizedFamily

/-!
# Univariate factors forced by a separated product

Over a domain, a nonzero product which involves only one variable has
univariate factors.  This removes any ambiguity about whether the monic
factors in Section 7 were initially presented as multivariate polynomials.
The original highest-power conditions recover the degrees and monicity of
the univariate representatives.  The final construction returns the
original paired data exactly when re-embedded in the polynomial ring.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.Fermion

section UnivariateRepresentation

variable {R : Type*} [CommRing R] {n : ℕ}

theorem separated_aeval_X_eq_rename (p : Polynomial R) (i : Fin n) :
    Polynomial.aeval (MvPolynomial.X i : PolynomialRing R n) p=
      MvPolynomial.rename (fun _ : Unit ↦ i)
        ((MvPolynomial.uniqueAlgEquiv R Unit).symm p) := by
  change Polynomial.toMvPolynomial i p=_
  rw [Polynomial.toMvPolynomial_eq_rename_comp,AlgHom.comp_apply,AlgEquiv.coe_toAlgHom]

theorem separated_aeval_X_vars_subset (p : Polynomial R) (i : Fin n) :
    (Polynomial.aeval (MvPolynomial.X i : PolynomialRing R n) p).vars⊆{i} := by
  rw [separated_aeval_X_eq_rename]
  intro j hj
  obtain ⟨u,hu,he⟩ := MvPolynomial.mem_vars_rename
    (fun _ : Unit ↦ i) ((MvPolynomial.uniqueAlgEquiv R Unit).symm p) hj
  exact Finset.mem_singleton.mpr he.symm

theorem exists_univariate_of_vars_subset (a : PolynomialRing R n) (i : Fin n)
    (ha : a.vars⊆{i}) :
    ∃ p : Polynomial R,Polynomial.aeval (MvPolynomial.X i) p=a := by
  let f : Unit → Fin n := fun _ ↦ i
  have hf : Function.Injective f := fun _ _ _ ↦ Subsingleton.elim _ _
  have hvars : (a.vars : Set (Fin n))⊆Set.range f := by
    intro j hj
    refine ⟨(),?_⟩
    exact (Finset.mem_singleton.mp (ha hj)).symm
  obtain ⟨q,hq⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range a f hf hvars
  refine ⟨MvPolynomial.uniqueAlgEquiv R Unit q,?_⟩
  rw [separated_aeval_X_eq_rename,AlgEquiv.symm_apply_apply]
  exact hq

variable [NoZeroDivisors R]

theorem nonzero_factor_vars_subset (a b : PolynomialRing R n)
    (ha : a≠0) (hb : b≠0) : a.vars⊆(a*b).vars ∧ b.vars⊆(a*b).vars := by
  constructor
  · intro j hj
    have hd := MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hj
    rw [MvPolynomial.mem_vars_iff_degreeOf_ne_zero,MvPolynomial.degreeOf_mul_eq ha hb]
    omega
  · intro j hj
    have hd := MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hj
    rw [MvPolynomial.mem_vars_iff_degreeOf_ne_zero,MvPolynomial.degreeOf_mul_eq ha hb]
    omega

/-- The representatives and their exact polynomial product, rather than
an assumed presentation equivalence. -/
structure UnivariateFactorization (i : Fin n) (p : Polynomial R)
    (a b : PolynomialRing R n) where
  left : Polynomial R
  right : Polynomial R
  eval_left : Polynomial.aeval (MvPolynomial.X i) left=a
  eval_right : Polynomial.aeval (MvPolynomial.X i) right=b
  mul_eq : left*right=p

/-- Every nonzero factorization of an embedded univariate polynomial
already has literal univariate factors. -/
theorem exists_univariate_factorization (i : Fin n) (p : Polynomial R) (hp : p≠0)
    (a b : PolynomialRing R n)
    (hab : a*b=Polynomial.aeval (MvPolynomial.X i) p) :
    Nonempty (UnivariateFactorization i p a b) := by
  have hp' : Polynomial.aeval (MvPolynomial.X i : PolynomialRing R n) p≠0 := by
    intro h
    apply hp
    apply Polynomial.toMvPolynomial_injective i
    simpa only [Polynomial.toMvPolynomial,map_zero] using h
  have ha : a≠0 := by
    intro h
    apply hp'
    rw [←hab,h,zero_mul]
  have hb : b≠0 := by
    intro h
    apply hp'
    rw [←hab,h,mul_zero]
  have hprod : (a*b).vars⊆{i} := by
    rw [hab]
    exact separated_aeval_X_vars_subset p i
  have hsub := nonzero_factor_vars_subset a b ha hb
  obtain ⟨a',ha'⟩ := exists_univariate_of_vars_subset a i (hsub.1.trans hprod)
  obtain ⟨b',hb'⟩ := exists_univariate_of_vars_subset b i (hsub.2.trans hprod)
  refine ⟨⟨a',b',ha',hb',?_⟩⟩
  apply Polynomial.toMvPolynomial_injective i
  change Polynomial.aeval (MvPolynomial.X i) (a'*b')=
    Polynomial.aeval (MvPolynomial.X i) p
  rw [map_mul,ha',hb',hab]

end UnivariateRepresentation

section HighestPowerRecovery

variable {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}

/-- The original highest-power statement determines both the degree and
the monicity of a univariate representative. -/
theorem monic_natDegree_of_aeval_X_highestPower
    (r : Fin n → ℕ) (hr : ∀ i,0<r i) (p : Polynomial R) (i : Fin n) (d : ℕ)
    (hp : HasHighestPower r (Polynomial.aeval (MvPolynomial.X i : PolynomialRing R n) p) i d) :
    p.Monic ∧ p.natDegree=d := by
  have htop : p.coeff d=1 :=
    (separated_aeval_X_coeff_single p i d).symm.trans hp.1
  have hpne : p≠0 := by
    intro h
    have hz : p.coeff d=0 := by simp only [h,Polynomial.coeff_zero]
    exact one_ne_zero (htop.symm.trans hz)
  have hle : p.natDegree≤d := by
    by_cases he : p.natDegree=d
    · exact he.le
    · have hmem : Finsupp.single i p.natDegree∈
          (Polynomial.aeval (MvPolynomial.X i : PolynomialRing R n) p).support := by
        rw [MvPolynomial.mem_support_iff,separated_aeval_X_coeff_single]
        exact Polynomial.mem_support_iff.mp (Polynomial.natDegree_mem_support_of_nonzero hpne)
      have hne : Finsupp.single i p.natDegree≠Finsupp.single i d :=
        (Finsupp.single_injective i).ne he
      have hw := hp.2 _ hmem hne
      have hw' : (p.natDegree : ℚ)/(r i : ℚ)<(d : ℚ)/(r i : ℚ) := by
        simpa [monomialWeight,Finsupp.single_apply,ite_div] using hw
      have hlt : (p.natDegree : ℚ)<(d : ℚ) :=
        (div_lt_div_iff_of_pos_right (by exact_mod_cast hr i)).mp hw'
      exact_mod_cast hlt.le
  exact ⟨Polynomial.monic_of_natDegree_le_of_coeff_eq_one d hle htop,
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [htop]; exact one_ne_zero)⟩

end HighestPowerRecovery

/-- The extra assumptions of Section 7 on an arbitrary original paired
datum: the covers are separated and the products share one monic G.
The factors a_i and b_i are still allowed to be multivariate here. -/
structure SeparatedCoverOfPairedData {F : Type*} [Field F] {n : ℕ}
    (d : PairedData (K := F) (n := n)) where
  G : Polynomial F
  G_monic : G.Monic
  G_pos : 0<G.natDegree
  phi : Fin n → Polynomial F
  phi_eq : ∀ i,Polynomial.aeval (MvPolynomial.X i) (phi i)=d.phi i
  paired_product : ∀ i,d.a i*d.b i=Polynomial.aeval (d.phi i) G

namespace SeparatedCoverOfPairedData

variable {F : Type*} [Field F] {n : ℕ} {d : PairedData (K := F) (n := n)}
  (c : SeparatedCoverOfPairedData d)

theorem phi_monic_degree (i : Fin n) :
    (c.phi i).Monic ∧ (c.phi i).natDegree=d.r i :=
  monic_natDegree_of_aeval_X_highestPower d.r d.positive_r (c.phi i) i (d.r i)
    (by rw [c.phi_eq]; exact d.highest_phi i)

theorem phi_positive (i : Fin n) : 0<(c.phi i).natDegree := by
  rw [(c.phi_monic_degree i).2]
  exact d.positive_r i

theorem product_as_univariate (i : Fin n) :
    d.a i*d.b i=Polynomial.aeval (MvPolynomial.X i) (c.G.comp (c.phi i)) := by
  rw [Polynomial.aeval_comp,c.phi_eq]
  exact c.paired_product i

def factors (i : Fin n) : UnivariateFactorization i (c.G.comp (c.phi i)) (d.a i) (d.b i) :=
  Classical.choice (exists_univariate_factorization i (c.G.comp (c.phi i))
    (c.G_monic.comp (c.phi_monic_degree i).1 (c.phi_positive i).ne').ne_zero
    (d.a i) (d.b i) (c.product_as_univariate i))

theorem a_monic_degree (i : Fin n) :
    (c.factors i).left.Monic ∧ (c.factors i).left.natDegree=d.u i :=
  monic_natDegree_of_aeval_X_highestPower d.r d.positive_r (c.factors i).left i (d.u i)
    (by rw [(c.factors i).eval_left]; exact d.highest_a i)

theorem b_monic_degree (i : Fin n) :
    (c.factors i).right.Monic ∧ (c.factors i).right.natDegree=d.v i :=
  monic_natDegree_of_aeval_X_highestPower d.r d.positive_r (c.factors i).right i (d.v i)
    (by rw [(c.factors i).eval_right]; exact d.highest_b i)

theorem G_degree : c.G.natDegree=d.s := by
  let i : Fin n := ⟨0,d.positive_n⟩
  have h := congrArg Polynomial.natDegree (c.factors i).mul_eq
  rw [(c.a_monic_degree i).1.natDegree_mul (c.b_monic_degree i).1,
    Polynomial.natDegree_comp,(c.a_monic_degree i).2,(c.b_monic_degree i).2,
    (c.phi_monic_degree i).2,d.degree_split i] at h
  apply Nat.eq_of_mul_eq_mul_left (d.positive_r i)
  exact (Nat.mul_comm _ _).trans h.symm

/-- A literal separated input for the local theorem, with every monicity,
degree, weight, and product hypothesis proved from the original paired input. -/
def toSeparatedData : SeparatedPairedData F n where
  beta := d.beta
  G := c.G
  phi := c.phi
  beta_units := d.allowed_weights.2
  G_monic := c.G_monic
  G_pos := c.G_pos
  phi_monic i := (c.phi_monic_degree i).1
  phi_pos := c.phi_positive
  a i := (c.factors i).left
  b i := (c.factors i).right
  a_monic i := (c.a_monic_degree i).1
  b_monic i := (c.b_monic_degree i).1
  paired_product i := (c.factors i).mul_eq

@[simp] theorem toSeparatedData_phiPolynomial : c.toSeparatedData.phiPolynomial=d.phi := by
  funext i
  exact c.phi_eq i

@[simp] theorem toSeparatedData_aPolynomial : c.toSeparatedData.aPolynomial=d.a := by
  funext i
  exact (c.factors i).eval_left

@[simp] theorem toSeparatedData_bPolynomial : c.toSeparatedData.bPolynomial=d.b := by
  funext i
  exact (c.factors i).eval_right

theorem toSeparatedData_superIdeal :
    c.toSeparatedData.superIdeal=pairedIdeal d.beta d.phi d.a d.b := by
  change pairedIdeal d.beta c.toSeparatedData.phiPolynomial
    c.toSeparatedData.aPolynomial c.toSeparatedData.bPolynomial=_
  rw [c.toSeparatedData_phiPolynomial,c.toSeparatedData_aPolynomial,c.toSeparatedData_bPolynomial]

/-- The identity on every original ambient representative identifies the
resulting separated quotient with the original paired quotient. -/
def superEquivOriginal :
    c.toSeparatedData.SuperQuotient ≃ₐ[F] PairedQuotient d.beta d.phi d.a d.b :=
  superQuotientCongr c.toSeparatedData_superIdeal

@[simp] theorem superEquivOriginal_mk (x : SuperRing F n) :
    c.superEquivOriginal (c.toSeparatedData.superMk x)=
      (pairedIdeal d.beta d.phi d.a d.b).ringCon.mkₐ F x := rfl

variable [CharZero F]

/-- Re-embedding the constructed separated input recovers the entire
original paired datum, including all parameters and polynomial fields. -/
theorem toSeparatedData_toPairedData :
    c.toSeparatedData.toPairedData d.positive_n=d := by
  apply PairedData.eq_of_fields
  · exact c.G_degree
  · funext i
    exact (c.phi_monic_degree i).2
  · funext i
    exact (c.a_monic_degree i).2
  · funext i
    exact (c.b_monic_degree i).2
  · rfl
  · exact c.toSeparatedData_phiPolynomial
  · exact c.toSeparatedData_aPolynomial
  · exact c.toSeparatedData_bPolynomial

end SeparatedCoverOfPairedData

namespace SeparatedCoverOfPairedData

variable {F : Type} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
  {d : PairedData (K := F) (n := n)} (c : SeparatedCoverOfPairedData d)

/-- The original coupled-factor presentation has exactly the full product
of local signed tensor factors supplied by Theorem 7.2. -/
def originalSuperTensorProductEquiv :
    PairedQuotient d.beta d.phi d.a d.b ≃ₐ[F]
      ∀ rho : c.toSeparatedData.O.SupportPoint,
        (c.toSeparatedData.localClusterFamily rho).tensor.Carrier :=
  c.superEquivOriginal.symm.trans c.toSeparatedData.globalSuperTensorProductEquiv

end SeparatedCoverOfPairedData
end PaperVerification.Fermion
