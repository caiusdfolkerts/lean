module

public import PaperVerification.FermionGlobalOddPresentation
public import PaperVerification.FermionLocalCoefficientTransport
public import PaperVerification.FermionIndependentClusterTensor
public import PaperVerification.FermionClusterReindex

/-!
# Single-cluster factors are the original homogeneous paired algebras

This compares the two literal presentations. The ordinary all-moment ideal
equals its first-n-moment presentation. Scalar quotienting is then followed
by the three actual odd moment families, including the unweighted mixed one.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.Fermion

section OddTransport
variable {F A B ι : Type*} [CommRing F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B] [Fintype ι]

theorem separatedOddCurrent_coefficient_map (e : A ≃ₐ[F] B)
    (node beta a b : ι → A) (family : LocalOddFamily) (k : ℕ) :
    finiteExteriorCoefficientEquiv e (separatedOddCurrent node beta a b family k)=
      separatedOddCurrent (fun i ↦ e (node i)) (fun i ↦ e (beta i))
        (fun i ↦ e (a i)) (fun i ↦ e (b i)) family k := by
  cases family <;>
    simp only [separatedOddCurrent,map_sum,finiteExteriorCoefficientEquiv_smul,
      map_pow,map_mul,clusterTheta,clusterXi,finiteExteriorCoefficientEquiv_generator]

theorem separatedOddIdeal_coefficient_map (e : A ≃ₐ[F] B)
    (node beta a b : ι → A) (x : ClusterExterior A ι)
    (hx : x∈separatedOddIdeal node beta a b) :
    finiteExteriorCoefficientEquiv e x∈
      separatedOddIdeal (fun i ↦ e (node i)) (fun i ↦ e (beta i))
        (fun i ↦ e (a i)) (fun i ↦ e (b i)) := by
  have hle : separatedOddIdeal node beta a b≤
      (separatedOddIdeal (fun i ↦ e (node i)) (fun i ↦ e (beta i))
        (fun i ↦ e (a i)) (fun i ↦ e (b i))).comap
          (finiteExteriorCoefficientEquiv e).toRingEquiv.toRingHom := by
    apply TwoSidedIdeal.span_le.mpr
    rintro x ⟨⟨family,k⟩,rfl⟩
    change separatedOddCurrent node beta a b family k ∈
      (separatedOddIdeal (fun i ↦ e (node i)) (fun i ↦ e (beta i))
        (fun i ↦ e (a i)) (fun i ↦ e (b i))).comap
          (finiteExteriorCoefficientEquiv e).toRingEquiv.toRingHom
    rw [TwoSidedIdeal.mem_comap]
    change finiteExteriorCoefficientEquiv e (separatedOddCurrent node beta a b family k) ∈
      separatedOddIdeal (fun i ↦ e (node i)) (fun i ↦ e (beta i))
        (fun i ↦ e (a i)) (fun i ↦ e (b i))
    rw [separatedOddCurrent_coefficient_map]
    exact TwoSidedIdeal.subset_span ⟨(family,k),rfl⟩
  have h := hle hx
  rw [TwoSidedIdeal.mem_comap] at h
  exact h

def separatedOddCoefficientEquiv (e : A ≃ₐ[F] B) (node beta a b : ι → A) :
    SeparatedOddQuotient node beta a b ≃ₐ[F]
      SeparatedOddQuotient (fun i ↦ e (node i)) (fun i ↦ e (beta i))
        (fun i ↦ e (a i)) (fun i ↦ e (b i)) :=
  twoSidedQuotientEquiv (finiteExteriorCoefficientEquiv e)
    (separatedOddIdeal node beta a b)
    (separatedOddIdeal (fun i ↦ e (node i)) (fun i ↦ e (beta i))
      (fun i ↦ e (a i)) (fun i ↦ e (b i)))
    (separatedOddIdeal_coefficient_map e node beta a b)
    (by
      intro x hx
      rw [finiteExteriorCoefficientEquiv_symm]
      simpa only [AlgEquiv.symm_apply_apply] using
        separatedOddIdeal_coefficient_map e.symm (fun i ↦ e (node i))
          (fun i ↦ e (beta i)) (fun i ↦ e (a i)) (fun i ↦ e (b i)) x hx)

end OddTransport

theorem separatedOddCurrent_power_eq_cluster {A ι : Type*} [CommRing A] [Fintype ι]
    (z beta : ι → A) (r u v : ι → ℕ) (family : LocalOddFamily) (k : ℕ) :
    separatedOddCurrent (fun i ↦ z i^r i) beta (fun i ↦ z i^u i) (fun i ↦ z i^v i) family k=
      clusterOddCurrent (fun _ : ι ↦ ()) z beta r u v family () k := by
  cases family with
  | theta =>
    simpa only [separatedOddCurrent,clusterOddCurrent,pow_mul] using
      (sum_constantFiber (ι := ι) (C := ClusterExterior A ι)
        (fiberFintype := constantFiberClassicalFintype ι)
        (fun i ↦ z i^(r i*k) • z i^v i • clusterTheta i)).symm
  | xi =>
    simpa only [separatedOddCurrent,clusterOddCurrent,pow_mul] using
      (sum_constantFiber (ι := ι) (C := ClusterExterior A ι)
        (fiberFintype := constantFiberClassicalFintype ι)
        (fun i ↦ z i^(r i*k) • (beta i*z i^u i) • clusterXi i)).symm
  | mixed =>
    simpa only [separatedOddCurrent,clusterOddCurrent,pow_mul] using
      (sum_constantFiber (ι := ι) (C := ClusterExterior A ι)
        (fiberFintype := constantFiberClassicalFintype ι)
        (fun i ↦ z i^(r i*k) • (clusterTheta i*clusterXi i))).symm

theorem separatedOddIdeal_power_eq_cluster {A ι : Type*} [CommRing A] [Fintype ι]
    (z beta : ι → A) (r u v : ι → ℕ) :
    separatedOddIdeal (fun i ↦ z i^r i) beta (fun i ↦ z i^u i) (fun i ↦ z i^v i)=
      clusterOddIdeal (fun _ : ι ↦ ()) z beta r u v := by
  apply le_antisymm
  · apply TwoSidedIdeal.span_le.mpr
    rintro x ⟨⟨family,k⟩,rfl⟩
    dsimp only
    rw [separatedOddCurrent_power_eq_cluster]
    exact TwoSidedIdeal.subset_span ⟨((),family,k),rfl⟩
  · apply TwoSidedIdeal.span_le.mpr
    rintro x ⟨⟨c,family,k⟩,rfl⟩
    cases c
    dsimp only
    rw [←separatedOddCurrent_power_eq_cluster]
    exact TwoSidedIdeal.subset_span ⟨(family,k),rfl⟩

section PowerData

variable {F : Type*} [Field F] {n : ℕ}
  (beta : Fin n → F)
  (hbeta : ∀ U : Finset (Fin n),U.Nonempty → IsUnit (∑ i∈U,beta i))
  (r : Fin n → ℕ) (hr : ∀ i,0<r i) (s : ℕ) (hs : 0<s)
  (u v : Fin n → ℕ) (huv : ∀ i,u i+v i=r i*s)

def powerSeparatedData : SeparatedPairedData F n where
  beta := beta
  G := Polynomial.X^s
  phi i := Polynomial.X^r i
  beta_units := hbeta
  G_monic := Polynomial.monic_X_pow s
  G_pos := by simpa only [Polynomial.natDegree_X_pow] using hs
  phi_monic i := Polynomial.monic_X_pow (r i)
  phi_pos i := by simpa only [Polynomial.natDegree_X_pow] using hr i
  a i := Polynomial.X^u i
  b i := Polynomial.X^v i
  a_monic i := Polynomial.monic_X_pow (u i)
  b_monic i := Polynomial.monic_X_pow (v i)
  paired_product i := by
    rw [←pow_add,huv,Polynomial.X_pow_comp,pow_mul]

theorem power_ordinary_moment_eq_cluster (k : ℕ) :
    moment (fun i ↦ Polynomial.aeval (MvPolynomial.X i : PolynomialRing F n) (Polynomial.X^r i : Polynomial F))
      (fun i ↦ algebraMap F (PolynomialRing F n) (beta i)*
        Polynomial.aeval (Polynomial.aeval (MvPolynomial.X i : PolynomialRing F n) (Polynomial.X^r i : Polynomial F))
          (Polynomial.X^s : Polynomial F)) k=
      clusterPowerMoment beta (fun _ : Fin n ↦ ()) r (fun _ ↦ s) () k := by
  calc
    _ = ∑ i : Fin n, MvPolynomial.C (beta i) *
        (MvPolynomial.X i : PolynomialRing F n)^(r i*(s+k)) := by
      simp only [moment,smul_eq_mul,Polynomial.aeval_X_pow,MvPolynomial.algebraMap_eq]
      apply Finset.sum_congr rfl
      intro i hi
      rw [←pow_mul,←pow_mul,Nat.mul_add,pow_add]
      ring
    _ = _ := by
      simpa only [clusterPowerMoment] using
        (sum_constantFiber (ι := Fin n) (C := PolynomialRing F n)
          (fiberFintype := constantFiberClassicalFintype (Fin n))
          (fun i ↦ MvPolynomial.C (beta i) *
            (MvPolynomial.X i : PolynomialRing F n)^(r i*(s+k)))).symm

theorem power_ordinary_ideal_eq_cluster :
    separatedOrdinaryIdeal beta (Polynomial.X^s) (fun i ↦ Polynomial.X^r i)=
      clusterPowerIdeal beta (fun _ : Fin n ↦ ()) r (fun _ ↦ s) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro p ⟨k,rfl⟩
    dsimp only
    rw [power_ordinary_moment_eq_cluster]
    exact clusterPowerMoment_mem beta (fun _ ↦ ()) r (fun _ ↦ s) () k
  · apply Ideal.span_le.mpr
    rintro p ⟨⟨c,k⟩,rfl⟩
    cases c
    dsimp only
    rw [←power_ordinary_moment_eq_cluster]
    exact ordinaryMoment_mem _ beta (Polynomial.X^s) k

def powerOrdinaryEquiv :
    (powerSeparatedData beta hbeta r hr s hs u v huv).O.Ordinary ≃ₐ[F]
      ClusterOrdinary beta (fun _ : Fin n ↦ ()) r (fun _ ↦ s) :=
  Ideal.quotientEquivAlgOfEq F (power_ordinary_ideal_eq_cluster beta r s)

@[simp] theorem powerOrdinaryEquiv_x (i : Fin n) :
    powerOrdinaryEquiv beta hbeta r hr s hs u v huv
      ((powerSeparatedData beta hbeta r hr s hs u v huv).O.ordinaryX i)=
        clusterZ beta (fun _ : Fin n ↦ ()) r (fun _ ↦ s) i :=
  Ideal.quotientEquivAlgOfEq_mk F _ (MvPolynomial.X i)

/-- The literal homogeneous single-cluster presentation is equivalent to
the paper's original polynomial-tensor-exterior paired quotient. -/
def pairedPowerEquivSingleCluster :
    PairedQuotient beta (fun i ↦ MvPolynomial.X i^r i)
      (fun i ↦ MvPolynomial.X i^u i) (fun i ↦ MvPolynomial.X i^v i) ≃ₐ[F]
      HomogeneousClusterAlgebra beta (fun _ : Fin n ↦ ()) r (fun _ ↦ s) u v := by
  let d := powerSeparatedData beta hbeta r hr s hs u v huv
  let e := powerOrdinaryEquiv beta hbeta r hr s hs u v huv
  let z := clusterZ beta (fun _ : Fin n ↦ ()) r (fun _ ↦ s)
  let betaB := fun i ↦ algebraMap F (ClusterOrdinary beta (fun _ : Fin n ↦ ()) r (fun _ ↦ s)) (beta i)
  have hn (i : Fin n) : e (d.O.ordinaryNode i)=z i^r i := by
    change e (Polynomial.aeval (d.O.ordinaryX i) (Polynomial.X^r i))=_
    rw [Polynomial.aeval_X_pow,map_pow,powerOrdinaryEquiv_x]
  have ha (i : Fin n) : e (d.ordinaryA i)=z i^u i := by
    change e (Polynomial.aeval (d.O.ordinaryX i) (Polynomial.X^u i))=_
    rw [Polynomial.aeval_X_pow,map_pow,powerOrdinaryEquiv_x]
  have hb (i : Fin n) : e (d.ordinaryB i)=z i^v i := by
    change e (Polynomial.aeval (d.O.ordinaryX i) (Polynomial.X^v i))=_
    rw [Polynomial.aeval_X_pow,map_pow,powerOrdinaryEquiv_x]
  let e1 := (d.globalSuperEquivOddPresentation).restrictScalars F
  let e2 :
      SeparatedOddQuotient d.O.ordinaryNode
        (fun i ↦ algebraMap F d.O.Ordinary (d.beta i)) d.ordinaryA d.ordinaryB ≃ₐ[F]
      SeparatedOddQuotient (fun i ↦ z i^r i) betaB (fun i ↦ z i^u i) (fun i ↦ z i^v i) := by
    have hnode : (fun i ↦ e (d.O.ordinaryNode i)) = (fun i ↦ z i^r i) := funext hn
    have hleft : (fun i ↦ e (d.ordinaryA i)) = (fun i ↦ z i^u i) := funext ha
    have hright : (fun i ↦ e (d.ordinaryB i)) = (fun i ↦ z i^v i) := funext hb
    have hweight : (fun i ↦ e (algebraMap F d.O.Ordinary (d.beta i))) = betaB := by
      funext i
      exact e.commutes (beta i)
    have ee := separatedOddCoefficientEquiv e
      d.O.ordinaryNode (fun i ↦ algebraMap F d.O.Ordinary (d.beta i)) d.ordinaryA d.ordinaryB
    rw [hnode,hleft,hright,hweight] at ee
    exact ee
  let e3 :
      SeparatedOddQuotient (fun i ↦ z i^r i) betaB (fun i ↦ z i^u i) (fun i ↦ z i^v i) ≃ₐ[F]
      HomogeneousClusterAlgebra beta (fun _ : Fin n ↦ ()) r (fun _ ↦ s) u v :=
    twoSidedQuotientEquivOfEq (R := F) (separatedOddIdeal_power_eq_cluster z betaB r u v)
  have eall := e1.trans (e2.trans e3)
  have hphi : d.phiPolynomial = (fun i ↦ MvPolynomial.X i^r i) := by
    funext i
    change Polynomial.aeval (MvPolynomial.X i) (Polynomial.X^r i) = _
    exact Polynomial.aeval_X_pow _
  have hpa : d.aPolynomial = (fun i ↦ MvPolynomial.X i^u i) := by
    funext i
    change Polynomial.aeval (MvPolynomial.X i) (Polynomial.X^u i) = _
    exact Polynomial.aeval_X_pow _
  have hpb : d.bPolynomial = (fun i ↦ MvPolynomial.X i^v i) := by
    funext i
    change Polynomial.aeval (MvPolynomial.X i) (Polynomial.X^v i) = _
    exact Polynomial.aeval_X_pow _
  change PairedQuotient d.beta d.phiPolynomial d.aPolynomial d.bPolynomial ≃ₐ[F]
    HomogeneousClusterAlgebra beta (fun _ : Fin n ↦ ()) r (fun _ ↦ s) u v at eall
  rw [hphi,hpa,hpb] at eall
  exact eall

end PowerData
end PaperVerification.Fermion

