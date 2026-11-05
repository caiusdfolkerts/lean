module

public import PaperVerification.FermionGlobalBigrading
public import PaperVerification.FermionSingleClusterPresentation

/-!
# The paired presentation bridge preserves both exterior degrees

The original quotient pieces are defined by original exterior word images
before using the factor equivalence. Scalar transport, equality of the
literal relation ideals, and finite reindexing preserve these pieces.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.Fermion

section Generic

variable {F A B ι : Type*} [CommRing F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B] [Fintype ι] [LinearOrder (ι⊕ι)]

theorem separatedOddCoefficientEquiv_bigraded_iff (e : A ≃ₐ[F] B)
    (node beta a b : ι → A) (g : ℕ×ℕ)
    (x : SeparatedOddQuotient node beta a b) :
    separatedOddCoefficientEquiv e node beta a b x∈
      separatedOddBigradedPart (fun i ↦ e (node i)) (fun i ↦ e (beta i))
        (fun i ↦ e (a i)) (fun i ↦ e (b i)) g ↔
      x∈separatedOddBigradedPart node beta a b g := by
  let f := separatedOddCoefficientEquiv e node beta a b
  let d := finiteExteriorCoefficientEquiv (ι := ι⊕ι) e
  constructor
  · rintro ⟨y,hy,hey⟩
    refine ⟨d.symm y,?_,?_⟩
    · rw [finiteExteriorCoefficientEquiv_symm]
      exact exteriorWeighted_coefficient_map_mem oddBidegree e.symm hy
    · apply f.injective
      change (separatedOddIdeal (fun i ↦ e (node i)) (fun i ↦ e (beta i))
        (fun i ↦ e (a i)) (fun i ↦ e (b i))).ringCon.mkₐ B (d (d.symm y))=f x
      rw [AlgEquiv.apply_symm_apply]
      exact hey
  · rintro ⟨y,hy,rfl⟩
    exact ⟨d y,exteriorWeighted_coefficient_map_mem oddBidegree e hy,rfl⟩

end Generic

section Power

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}
  (beta : Fin n → F)
  (hbeta : ∀ U : Finset (Fin n),U.Nonempty → IsUnit (∑ i∈U,beta i))
  (r : Fin n → ℕ) (hr : ∀ i,0<r i) (s : ℕ) (hs : 0<s)
  (u v : Fin n → ℕ) (huv : ∀ i,u i+v i=r i*s)

local instance FermionSingleClusterBigraded_powerOddOrder : LinearOrder (Fin n⊕Fin n) := finiteIndexLinearOrder _

/-- Evaluation of the univariate powers gives the same literal ambient
relation ideal. This comparison is the identity on original representatives. -/
def pairedPowerOriginalEquiv :
    (powerSeparatedData beta hbeta r hr s hs u v huv).SuperQuotient ≃ₐ[F]
      PairedQuotient beta (fun i ↦ MvPolynomial.X i^r i)
        (fun i ↦ MvPolynomial.X i^u i) (fun i ↦ MvPolynomial.X i^v i) := by
  let d := powerSeparatedData beta hbeta r hr s hs u v huv
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
  exact twoSidedQuotientEquivOfEq (R := F) (show d.superIdeal=
    pairedIdeal beta (fun i ↦ MvPolynomial.X i^r i)
      (fun i ↦ MvPolynomial.X i^u i) (fun i ↦ MvPolynomial.X i^v i) from by
        change pairedIdeal d.beta d.phiPolynomial d.aPolynomial d.bPolynomial=_
        rw [hphi,hpa,hpb]
        rfl)

-- Kernel reduction compares the two explicit quotient presentations here.
set_option maxHeartbeats 1000000 in
@[simp] theorem pairedPowerOriginalEquiv_mk (x : SuperRing F n) :
    pairedPowerOriginalEquiv beta hbeta r hr s hs u v huv
      ((powerSeparatedData beta hbeta r hr s hs u v huv).superMk x)=
      (pairedIdeal beta (fun i ↦ MvPolynomial.X i^r i)
        (fun i ↦ MvPolynomial.X i^u i) (fun i ↦ MvPolynomial.X i^v i)).ringCon.mkₐ F x := by
  dsimp only [pairedPowerOriginalEquiv,SeparatedPairedData.superMk]
  exact twoSidedQuotientEquivOfEq_mk (R := F) (A := SuperRing F n) _ x

def pairedPowerBigradedPart (g : ℕ×ℕ) :
    Submodule F (PairedQuotient beta (fun i ↦ MvPolynomial.X i^r i)
      (fun i ↦ MvPolynomial.X i^u i) (fun i ↦ MvPolynomial.X i^v i)) :=
  (((powerSeparatedData beta hbeta r hr s hs u v huv).globalSuperBigradedPart g).restrictScalars F).map
      (pairedPowerOriginalEquiv beta hbeta r hr s hs u v huv).toLinearMap

set_option maxHeartbeats 1000000 in
/-- The original homogeneous paired quotient and the independent
single-cluster presentation agree as exterior-bigraded algebras. -/
theorem pairedPowerBigradedEquivExists :
    ∃ e : PairedQuotient beta (fun i ↦ MvPolynomial.X i^r i)
      (fun i ↦ MvPolynomial.X i^u i) (fun i ↦ MvPolynomial.X i^v i) ≃ₐ[F]
        HomogeneousClusterAlgebra beta (fun _ : Fin n ↦ ()) r (fun _ ↦ s) u v,
      ∀ g x,e x∈homogeneousClusterBigradedPart beta (fun _ : Fin n ↦ ())
        r (fun _ ↦ s) u v g ↔ x∈pairedPowerBigradedPart beta hbeta r hr s hs u v huv g := by
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
  have hnode : (fun i ↦ e (d.O.ordinaryNode i)) = (fun i ↦ z i^r i) := funext hn
  have hleft : (fun i ↦ e (d.ordinaryA i)) = (fun i ↦ z i^u i) := funext ha
  have hright : (fun i ↦ e (d.ordinaryB i)) = (fun i ↦ z i^v i) := funext hb
  have hweight : (fun i ↦ e (algebraMap F d.O.Ordinary (d.beta i))) = betaB := by
    funext i
    exact e.commutes (beta i)
  let e1 := d.globalSuperEquivOddPresentation.restrictScalars F
  let eRaw := separatedOddCoefficientEquiv e
    d.O.ordinaryNode (fun i ↦ algebraMap F d.O.Ordinary (d.beta i)) d.ordinaryA d.ordinaryB
  have hIdeal : separatedOddIdeal (fun i ↦ e (d.O.ordinaryNode i))
      (fun i ↦ e (algebraMap F d.O.Ordinary (d.beta i)))
      (fun i ↦ e (d.ordinaryA i)) (fun i ↦ e (d.ordinaryB i)) =
      separatedOddIdeal (fun i ↦ z i^r i) betaB (fun i ↦ z i^u i) (fun i ↦ z i^v i) := by
    rw [hnode,hleft,hright,hweight]
  let eIdentity := twoSidedQuotientEquivOfEq (R := F) hIdeal
  let e2 :
      SeparatedOddQuotient d.O.ordinaryNode
        (fun i ↦ algebraMap F d.O.Ordinary (d.beta i)) d.ordinaryA d.ordinaryB ≃ₐ[F]
      SeparatedOddQuotient (fun i ↦ z i^r i) betaB (fun i ↦ z i^u i) (fun i ↦ z i^v i) :=
    eRaw.trans eIdentity
  let e3 :
      SeparatedOddQuotient (fun i ↦ z i^r i) betaB (fun i ↦ z i^u i) (fun i ↦ z i^v i) ≃ₐ[F]
      HomogeneousClusterAlgebra beta (fun _ : Fin n ↦ ()) r (fun _ ↦ s) u v :=
    twoSidedQuotientEquivOfEq (R := F) (separatedOddIdeal_power_eq_cluster z betaB r u v)
  have H :
      ∃ ee : d.SuperQuotient ≃ₐ[F]
        HomogeneousClusterAlgebra beta (fun _ : Fin n ↦ ()) r (fun _ ↦ s) u v,
        ∀ g x,ee x∈homogeneousClusterBigradedPart beta (fun _ : Fin n ↦ ())
          r (fun _ ↦ s) u v g ↔ x∈(d.globalSuperBigradedPart g).restrictScalars F := by
    refine ⟨e1.trans (e2.trans e3),?_⟩
    intro g x
    have h1 := d.globalSuperOddPresentation_bigraded_iff g x
    have h2 := separatedOddCoefficientEquiv_bigraded_iff e d.O.ordinaryNode
      (fun i ↦ algebraMap F d.O.Ordinary (d.beta i)) d.ordinaryA d.ordinaryB g (e1 x)
    have hIdentity := twoSidedQuotientEquivOfEq_image_iff (F := F)
      exteriorBigradedPart hIdeal g (eRaw (e1 x))
    have h2' : e2 (e1 x)∈separatedOddBigradedPart
        (fun i ↦ z i^r i) betaB (fun i ↦ z i^u i) (fun i ↦ z i^v i) g ↔
        e1 x∈separatedOddBigradedPart d.O.ordinaryNode
          (fun i ↦ algebraMap F d.O.Ordinary (d.beta i)) d.ordinaryA d.ordinaryB g := by
      simpa only [e2,eRaw,eIdentity,AlgEquiv.trans_apply,separatedOddBigradedPart] using
        hIdentity.trans h2
    have h3 := twoSidedQuotientEquivOfEq_image_iff (F := F) exteriorBigradedPart
      (separatedOddIdeal_power_eq_cluster z betaB r u v) g (e2 (e1 x))
    simpa only [e1,e3,AlgEquiv.trans_apply,AlgEquiv.restrictScalars_apply,
      homogeneousClusterBigradedPart,restrictGradedPart,
      clusterOddBigradedPart,separatedOddBigradedPart,Submodule.restrictScalars_mem] using
      h3.trans (h2'.trans h1)
  obtain ⟨ee,hee⟩ := H
  let e0 := pairedPowerOriginalEquiv beta hbeta r hr s hs u v huv
  refine ⟨e0.symm.trans ee,?_⟩
  intro g x
  change ee (e0.symm x)∈homogeneousClusterBigradedPart beta (fun _ : Fin n ↦ ())
      r (fun _ ↦ s) u v g ↔
    x∈((d.globalSuperBigradedPart g).restrictScalars F).map e0.toLinearMap
  constructor
  · intro hx
    exact ⟨e0.symm x,(hee g _).mp hx,e0.apply_symm_apply x⟩
  · rintro ⟨y,hy,hyx⟩
    change e0 y=x at hyx
    rw [←hyx,AlgEquiv.symm_apply_apply]
    exact (hee g y).mpr hy

end Power
end PaperVerification.Fermion

