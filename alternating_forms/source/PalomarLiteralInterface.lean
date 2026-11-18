module
public import PalomarOriginalSolution

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace PalomarAlternatingLiteral

namespace PaperVerification.AlternatingForms
section
open scoped BigOperators
open Module MvPolynomial
variable {K M N : Type*} [Field K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
variable {I J B : Type*} [Fintype I] [Fintype J] [Fintype B]
  [DecidableEq I] [DecidableEq J] [DecidableEq B]
  (q : ℕ) (b₂ : Basis I K (⋀[K]^2 M))
  (bq : Basis J K (⋀[K]^q M)) (bout : Basis B K (⋀[K]^(2 + q) M))
/-- Literal PaperVerification.AlternatingForms.orbitFormsFromCoordinates; precise source and scope recorded in the extraction map. -/
def orbitFormsFromCoordinates (x : (I ⊕ I) → K) : (⋀[K]^2 M) × (⋀[K]^2 M) :=
  (∑ i, x (Sum.inl i) • b₂ i, ∑ i, x (Sum.inr i) • b₂ i)
end
end PaperVerification.AlternatingForms

namespace PaperVerification.AlternatingForms
section
set_option backward.isDefEq.respectTransparency false
variable {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]
/-- Literal PaperVerification.AlternatingForms.exteriorRelationIdeal; precise source and scope recorded in the extraction map. -/
def exteriorRelationIdeal (f g : ⋀[K]^2 M) : Ideal (ExteriorAlgebra K M) :=
  Ideal.span {(f : ExteriorAlgebra K M), (g : ExteriorAlgebra K M)}
/-- Literal PaperVerification.AlternatingForms.exteriorDegreeRelations; precise source and scope recorded in the extraction map. -/
def exteriorDegreeRelations (f g : ⋀[K]^2 M) (d : ℕ) :
    Submodule K (⋀[K]^d M) :=
  ((exteriorRelationIdeal f g).restrictScalars K).comap
    (Submodule.subtype (⋀[K]^d M))
/-- Literal PaperVerification.AlternatingForms.ExteriorQuotientDegree; precise source and scope recorded in the extraction map. -/
abbrev ExteriorQuotientDegree (f g : ⋀[K]^2 M) (d : ℕ) :=
  (⋀[K]^d M) ⧸ exteriorDegreeRelations f g d
end
end PaperVerification.AlternatingForms

namespace PaperVerification.AlternatingForms
section
open scoped BigOperators
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
/-- Literal PaperVerification.AlternatingForms.exteriorPair; precise source and scope recorded in the extraction map. -/
def exteriorPair (u v : M) : ⋀[K]^2 M :=
  exteriorPower.ιMulti K 2 ![u, v]
end
end PaperVerification.AlternatingForms

namespace PaperVerification.AlternatingForms.StripWalks
section
open scoped BigOperators
/-- Literal PaperVerification.AlternatingForms.StripWalks.walkCount; precise source and scope recorded in the extraction map. -/
def walkCount (w N : ℕ) : ℕ :=
  Fintype.card {p : (SimpleGraph.pathGraph (w + 1)).Walk 0 (Fin.last w) // p.length = N}
/-- Literal PaperVerification.AlternatingForms.StripWalks.paperWalkCount; precise source and scope recorded in the extraction map. -/
def paperWalkCount (n s : ℕ) : ℕ := walkCount (n + 2 - 2 * s) (n + 2)
end
end PaperVerification.AlternatingForms.StripWalks

namespace PaperVerification.AlternatingForms
section
open MvPolynomial Matrix
open scoped BigOperators
variable {K : Type*} [Field K] {s n : ℕ}
/-- Literal PaperVerification.AlternatingForms.PluckerIndex; precise source and scope recorded in the extraction map. -/
def PluckerIndex (s n : ℕ) := {I : Fin s → Fin n // StrictMono I}
end
end PaperVerification.AlternatingForms

namespace PaperVerification.AlternatingForms
section
open scoped BigOperators
variable {K M ι : Type*} [Field K] [AddCommGroup M] [Module K M]
  [Fintype ι] [DecidableEq ι]
/-- Literal PaperVerification.AlternatingForms.matchingQuadratic; precise source and scope recorded in the extraction map. -/
def matchingQuadratic (u v : ι → M) : ⋀[K]^2 M :=
  ∑ i, exteriorPair (K := K) (u i) (v i)
end
end PaperVerification.AlternatingForms

namespace PaperVerification.AlternatingForms
section
open scoped BigOperators
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
/-- Literal PaperVerification.AlternatingForms.oddPathFirstLeft; precise source and scope recorded in the extraction map. -/
def oddPathFirstLeft {k : ℕ} (i : Fin k) : Fin (2 * k + 1) :=
  ⟨2 * i.val, by have := i.isLt; omega⟩
/-- Literal PaperVerification.AlternatingForms.oddPathMiddle; precise source and scope recorded in the extraction map. -/
def oddPathMiddle {k : ℕ} (i : Fin k) : Fin (2 * k + 1) :=
  ⟨2 * i.val + 1, by have := i.isLt; omega⟩
/-- Literal PaperVerification.AlternatingForms.oddPathSecondRight; precise source and scope recorded in the extraction map. -/
def oddPathSecondRight {k : ℕ} (i : Fin k) : Fin (2 * k + 1) :=
  ⟨2 * i.val + 2, by have := i.isLt; omega⟩
/-- Literal PaperVerification.AlternatingForms.oddPathFirstQuadratic; precise source and scope recorded in the extraction map. -/
def oddPathFirstQuadratic {k : ℕ} (z : Fin (2 * k + 1) → M) : ⋀[K]^2 M :=
  matchingQuadratic (fun i => z (oddPathFirstLeft i)) (fun i => z (oddPathMiddle i))
/-- Literal PaperVerification.AlternatingForms.oddPathSecondQuadratic; precise source and scope recorded in the extraction map. -/
def oddPathSecondQuadratic {k : ℕ} (z : Fin (2 * k + 1) → M) : ⋀[K]^2 M :=
  matchingQuadratic (fun i => z (oddPathMiddle i)) (fun i => z (oddPathSecondRight i))
end
end PaperVerification.AlternatingForms

namespace PaperVerification.AlternatingForms
section
open MvPolynomial
open scoped BigOperators
variable {K : Type*} [Field K] {s n t m : ℕ}
/-- Literal PaperVerification.AlternatingForms.pluckerOrderEmbeddingEquiv; precise source and scope recorded in the extraction map. -/
def pluckerOrderEmbeddingEquiv (s n : ℕ) :
    PluckerIndex s n ≃ (Fin s ↪o Fin n) where
  toFun I := OrderEmbedding.ofStrictMono I.val I.property
  invFun f := ⟨f,f.strictMono⟩
  left_inv I := rfl
  right_inv f := by ext i; rfl
/-- Literal PaperVerification.AlternatingForms.pluckerSubsetEquiv; precise source and scope recorded in the extraction map. -/
def pluckerSubsetEquiv (s n : ℕ) :
    PluckerIndex s n ≃ Set.powersetCard (Fin n) s :=
  (pluckerOrderEmbeddingEquiv s n).trans Set.powersetCard.ofFinEmbEquiv
/-- Literal PaperVerification.AlternatingForms.exteriorPluckerBasis; precise source and scope recorded in the extraction map. -/
def exteriorPluckerBasis (s n : ℕ) :
    Module.Basis (PluckerIndex s n) K (⋀[K]^s (Fin n → K)) :=
  ((Pi.basisFun K (Fin n)).exteriorPower s).reindex (pluckerSubsetEquiv s n).symm
end
end PaperVerification.AlternatingForms

namespace PaperVerification.AlternatingForms
section
open MvPolynomial
variable {K : Type*} [Field K]
/-- Literal PaperVerification.AlternatingForms.GoodOddIndex; precise source and scope recorded in the extraction map. -/
def GoodOddIndex (k s : ℕ) :=
  {I : PluckerIndex s (2*k+1) // ∀ i,
    2*i.val≤(I.val i).val ∧ (I.val i).val+2*s≤2*k+2+2*i.val}
/-- Literal PaperVerification.AlternatingForms.OddExteriorQuotientDegree; precise source and scope recorded in the extraction map. -/
abbrev OddExteriorQuotientDegree (k s : ℕ) :=
  ExteriorQuotientDegree
    (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))))
    (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) s
/-- Literal PaperVerification.AlternatingForms.paper_theorem_1_3_exterior_basis; precise source and scope recorded in the extraction map. -/
theorem paper_theorem_1_3_exterior_basis [CharZero K] (k s : ℕ) :
    ∃ B : Module.Basis (GoodOddIndex k s) K (OddExteriorQuotientDegree (K := K) k s),
      ∀ I,B I=Submodule.Quotient.mk
        (exteriorPower.ιMulti K s (fun i => Pi.basisFun K (Fin (2*k+1)) (I.val.val i))) := by
  exact _root_.PaperVerification.AlternatingForms.paper_theorem_1_3_exterior_basis (k := k) (s := s)
end
end PaperVerification.AlternatingForms

namespace PaperVerification.AlternatingForms
section
variable {K M N : Type*} [Field K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
/-- Literal PaperVerification.AlternatingForms.standardBasisEquiv; precise source and scope recorded in the extraction map. -/
def standardBasisEquiv {n : ℕ} (b : Module.Basis (Fin n) K M) :
    (Fin n → K) ≃ₗ[K] M :=
  (Pi.basisFun K (Fin n)).equiv b (Equiv.refl (Fin n))
end
end PaperVerification.AlternatingForms

namespace PaperVerification.AlternatingForms.PathDeterminant
section
open scoped BigOperators Matrix Classical
/-- Literal PaperVerification.AlternatingForms.PathDeterminant.paperMatrix; precise source and scope recorded in the extraction map. -/
def paperMatrix (w s : ℕ) : Matrix (Fin s) (Fin s) ℤ :=
  fun i j => if i.val ≤ j.val+1 then
    ((w+i.val-j.val).choose (j.val+1-i.val) : ℤ) else 0
/-- Literal PaperVerification.AlternatingForms.PathDeterminant.paperWalkCount_determinant; precise source and scope recorded in the extraction map. -/
theorem paperWalkCount_determinant (n s : ℕ) (hs : 2*s ≤ n+2) :
    (StripWalks.paperWalkCount n s : ℤ) = (paperMatrix (n+2-2*s) s).det := by
  exact _root_.PaperVerification.AlternatingForms.PathDeterminant.paperWalkCount_determinant (n := n) (s := s) (hs := hs)
end
end PaperVerification.AlternatingForms.PathDeterminant

namespace PaperVerification.FiniteHilbertSeries
section
open scoped BigOperators PowerSeries
/-- Literal PaperVerification.FiniteHilbertSeries.expression; precise source and scope recorded in the extraction map. -/
def expression (a : ℕ → ℕ) (d : ℕ) : ℕ⟦X⟧ :=
  1 + ∑ s ∈ Finset.Icc 1 d, PowerSeries.C (a s) * PowerSeries.X ^ s
end
end PaperVerification.FiniteHilbertSeries

namespace PaperVerification.AlternatingForms
section
open MvPolynomial
open scoped BigOperators Classical PowerSeries
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
/-- Literal PaperVerification.AlternatingForms.exteriorPairHilbertSeries; precise source and scope recorded in the extraction map. -/
def exteriorPairHilbertSeries (f g : ⋀[K]^2 M) : ℕ⟦X⟧ :=
  PowerSeries.mk fun s => Module.finrank K (ExteriorQuotientDegree f g s)
/-- Literal PaperVerification.AlternatingForms.paperExteriorHilbertSeries; precise source and scope recorded in the extraction map. -/
def paperExteriorHilbertSeries (n : ℕ) : ℕ⟦X⟧ :=
  FiniteHilbertSeries.expression (StripWalks.paperWalkCount n) ((n+1)/2)
end
end PaperVerification.AlternatingForms

namespace TauCeti.Sym
section
variable {α β : Type*} {m n : ℕ}
/-- Literal TauCeti.Sym.ofFn; precise source and scope recorded in the extraction map. -/
def ofFn (f : Fin n → α) : Sym α n :=
  Sym.ofVector (List.Vector.ofFn f)
/-- Literal TauCeti.Sym.ofFn_surjective; precise source and scope recorded in the extraction map. -/
theorem ofFn_surjective : Function.Surjective (ofFn : (Fin n → α) → Sym α n) := by
  exact _root_.TauCeti.Sym.ofFn_surjective
end
end TauCeti.Sym

namespace TauCeti
section

/-- Literal TauCeti.symFinTwoEquiv; precise source and scope recorded in the extraction map. -/
noncomputable def symFinTwoEquiv (d : ℕ) : Sym (Fin 2) d ≃ Fin (d + 1) :=
  (Sym.equivNatSumOfFintype (Fin 2) d).trans <|
    ((finTwoArrowEquiv ℕ).subtypeEquiv fun _ => by
      simp [Fin.sum_univ_two, Finset.mem_antidiagonal]).trans
        (Finset.Nat.antidiagonalEquivFin d)
end
end TauCeti

namespace PaperVerification.AlternatingForms.TopInterlacing
section
open scoped Classical BigOperators
/-- Literal PaperVerification.AlternatingForms.TopInterlacing.abIndex; precise source and scope recorded in the extraction map. -/
def abIndex (k : ℕ) : Fin k ⊕ Fin (k+1) ≃ Fin (2*k+1) where
  toFun
    | .inl i => ⟨2*i.val+1, by have := i.isLt; omega⟩
    | .inr j => ⟨2*j.val, by have := j.isLt; omega⟩
  invFun j := if h : j.val%2=0 then .inr ⟨j.val/2, by have := j.isLt; omega⟩
    else .inl ⟨j.val/2, by have := j.isLt; omega⟩
  left_inv i := by
    cases i with
    | inl i =>
        have h : ¬(2*i.val+1)%2=0 := by omega
        simp only [h, dite_false, Sum.inl.injEq]
        apply Fin.ext
        dsimp only
        omega
    | inr i =>
        have h : (2*i.val)%2=0 := by omega
        simp only [h, dite_true, Sum.inr.injEq]
        apply Fin.ext
        dsimp only
        omega
  right_inv i := by
    dsimp only
    split_ifs <;> apply Fin.ext <;> dsimp only <;> omega
end
end PaperVerification.AlternatingForms.TopInterlacing

namespace SymmetricPower
section
open scoped _root_.TensorProduct
universe u v
variable {R ι : Type u} {M : Type v}
variable [CommSemiring R]
variable [AddCommMonoid M] [Module R M]
/-- Literal SymmetricPower.ext; precise source and scope recorded in the extraction map. -/
theorem ext {N : Type*} [AddCommMonoid N] [Module R N] {g h : Sym[R] ι M →ₗ[R] N}
    (hgh : ∀ m : ι → M, g (⨂ₛ[R] i, m i) = h (⨂ₛ[R] i, m i)) : g = h := by
  exact _root_.SymmetricPower.ext (hgh := hgh)
/-- Literal SymmetricPower.map_rel; precise source and scope recorded in the extraction map. -/
theorem map_rel {N : Type*} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) :
    addConGen (_root_.SymmetricPower.Rel R ι M) ≤
      AddCon.ker ((_root_.SymmetricPower.mk R ι N).toAddMonoidHom.comp
        (PiTensorProduct.map fun _ : ι => f).toAddMonoidHom) := by
  exact _root_.SymmetricPower.map_rel (f := f)
end
end SymmetricPower

namespace SymmetricPower
section
open scoped _root_.TensorProduct
universe u v w
variable {R ι : Type u} {M : Type v} {N : Type w}
variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable (f : MultilinearMap R (fun _ : ι ↦ M) N)
/-- Literal SymmetricPower.lift_rel; precise source and scope recorded in the extraction map. -/
theorem lift_rel (hf : ∀ e : Equiv.Perm ι, f.domDomCongr e = f) :
    addConGen (_root_.SymmetricPower.Rel R ι M) ≤ AddCon.ker (PiTensorProduct.lift f).toAddMonoidHom := by
  exact _root_.SymmetricPower.lift_rel (f := f) (hf := hf)
/-- Literal SymmetricPower.lift; precise source and scope recorded in the extraction map. -/
noncomputable def lift (hf : ∀ e : Equiv.Perm ι, f.domDomCongr e = f) : Sym[R] ι M →ₗ[R] N where
  toFun := (addConGen (_root_.SymmetricPower.Rel R ι M)).lift (PiTensorProduct.lift f).toAddMonoidHom (lift_rel f hf)
  map_add' := map_add _
  map_smul' r x := AddCon.induction_on x fun x => (PiTensorProduct.lift f).map_smul r x
end
end SymmetricPower

namespace SymmetricPower
section
open scoped _root_.TensorProduct
universe u v
variable {R ι : Type u} {M : Type v}
variable [CommSemiring R]
variable [AddCommMonoid M] [Module R M]
/-- Literal SymmetricPower.map; precise source and scope recorded in the extraction map. -/
noncomputable def map {N : Type*} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) :
    Sym[R] ι M →ₗ[R] Sym[R] ι N where
  toFun :=
    (addConGen (_root_.SymmetricPower.Rel R ι M)).lift
      ((_root_.SymmetricPower.mk R ι N).toAddMonoidHom.comp
        (PiTensorProduct.map fun _ : ι => f).toAddMonoidHom)
      (map_rel f)
  map_add' := map_add _
  map_smul' r x := AddCon.induction_on x fun x => by
    exact congrArg (_root_.SymmetricPower.mk R ι N) ((PiTensorProduct.map fun _ : ι => f).map_smul r x)
/-- Literal SymmetricPower.map_id; precise source and scope recorded in the extraction map. -/
theorem map_id :
    map (ι := ι) (LinearMap.id (R := R) (M := M)) = LinearMap.id := by
  exact _root_.SymmetricPower.map_id (R := R) (ι := ι) (M := M)
/-- Literal SymmetricPower.map_comp; precise source and scope recorded in the extraction map. -/
theorem map_comp {N : Type*} {P : Type*}
    [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    map (ι := ι) (g.comp f) = (map (ι := ι) g).comp (map (ι := ι) f) := by
  exact _root_.SymmetricPower.map_comp (f := f) (g := g)
end
end SymmetricPower

namespace SymmetricPower
section
open Module
open scoped _root_.TensorProduct
universe v w
variable {R : Type} {M : Type v} {κ : Type w} {n : ℕ}
/-- Literal SymmetricPower.orderOfSym; precise source and scope recorded in the extraction map. -/
noncomputable def orderOfSym (s : Sym κ n) : Fin n → κ :=
  Function.surjInv TauCeti.Sym.ofFn_surjective s
/-- Literal SymmetricPower.ofFn_orderOfSym; precise source and scope recorded in the extraction map. -/
theorem ofFn_orderOfSym (s : Sym κ n) : TauCeti.Sym.ofFn (orderOfSym s) = s := by
  exact _root_.SymmetricPower.ofFn_orderOfSym (s := s)
end
end SymmetricPower

namespace SymmetricPower
section
open Module
open scoped _root_.TensorProduct
universe v w
variable {R : Type} {M : Type v} {κ : Type w} {n : ℕ}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable (R)
/-- Literal SymmetricPower.tprodOfSym; precise source and scope recorded in the extraction map. -/
noncomputable def tprodOfSym (v : κ → M) (s : Sym κ n) : Sym[R]^n M :=
  ⨂ₛ[R] i, v (orderOfSym s i)
end
end SymmetricPower

namespace SymmetricPower
section
open Module
open scoped _root_.TensorProduct
universe v w
variable {R : Type} {M : Type v} {κ : Type w} {n : ℕ}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
/-- Literal SymmetricPower.tprodOfSym_ofFn; precise source and scope recorded in the extraction map. -/
theorem tprodOfSym_ofFn (v : κ → M) (f : Fin n → κ) :
    tprodOfSym R v (TauCeti.Sym.ofFn f) = ⨂ₛ[R] i, v (f i) := by
  exact _root_.SymmetricPower.tprodOfSym_ofFn (R := R) (v := v) (f := f)
end
end SymmetricPower

namespace SymmetricPower
section
open Module
open scoped _root_.TensorProduct
universe v w
variable {R : Type} {M : Type v} {κ : Type w} {n : ℕ}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable (b : Basis κ R M)
/-- Literal SymmetricPower.toFinsuppAux; precise source and scope recorded in the extraction map. -/
noncomputable def toFinsuppAux : (⨂[R] (_ : Fin n), M) →ₗ[R] (Sym κ n →₀ R) :=
  (Basis.piTensorProduct fun _ : Fin n => b).constr R
    fun f => Finsupp.single (TauCeti.Sym.ofFn f) 1
/-- Literal SymmetricPower.toFinsuppMultilinear; precise source and scope recorded in the extraction map. -/
noncomputable def toFinsuppMultilinear :
    MultilinearMap R (fun _ : Fin n ↦ M) (Sym κ n →₀ R) :=
  (toFinsuppAux b).compMultilinearMap (PiTensorProduct.tprod R)
/-- Literal SymmetricPower.toFinsuppMultilinear_domDomCongr; precise source and scope recorded in the extraction map. -/
theorem toFinsuppMultilinear_domDomCongr (e : Equiv.Perm (Fin n)) :
    (toFinsuppMultilinear b).domDomCongr e = toFinsuppMultilinear b := by
  exact _root_.SymmetricPower.toFinsuppMultilinear_domDomCongr (b := b) (e := e)
end
end SymmetricPower

namespace SymmetricPower
section
open Module
open scoped _root_.TensorProduct
universe v w
variable {R : Type} {M : Type v} {κ : Type w} {n : ℕ}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable (b : Basis κ R M)
variable (n)
/-- Literal SymmetricPower.toFinsupp; precise source and scope recorded in the extraction map. -/
noncomputable def toFinsupp : Sym[R]^n M →ₗ[R] (Sym κ n →₀ R) :=
  lift (toFinsuppMultilinear b) (toFinsuppMultilinear_domDomCongr b)
end
end SymmetricPower

namespace SymmetricPower
section
open Module
open scoped _root_.TensorProduct
universe v w
variable {R : Type} {M : Type v} {κ : Type w} {n : ℕ}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable (b : Basis κ R M)
/-- Literal SymmetricPower.toFinsupp_tprod_basis; precise source and scope recorded in the extraction map. -/
theorem toFinsupp_tprod_basis (f : Fin n → κ) :
    toFinsupp n b (⨂ₛ[R] i, b (f i)) = Finsupp.single (TauCeti.Sym.ofFn f) 1 := by
  exact _root_.SymmetricPower.toFinsupp_tprod_basis (b := b) (f := f)
end
end SymmetricPower

namespace SymmetricPower
section
open Module
open scoped _root_.TensorProduct
universe v w
variable {R : Type} {M : Type v} {κ : Type w} {n : ℕ}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable (b : Basis κ R M)
variable (n)
/-- Literal SymmetricPower.linearEquivFinsupp; precise source and scope recorded in the extraction map. -/
noncomputable def linearEquivFinsupp : Sym[R]^n M ≃ₗ[R] (Sym κ n →₀ R) :=
  LinearEquiv.ofLinearMap (toFinsupp n b) (Finsupp.linearCombination R (tprodOfSym R b))
    (by
      refine Finsupp.lhom_ext' fun s => LinearMap.ext_ring ?_
      simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.id_apply]
      rw [Finsupp.linearCombination_single, one_smul, ← ofFn_orderOfSym s, tprodOfSym_ofFn,
        toFinsupp_tprod_basis, ofFn_orderOfSym])
    (by
      apply (LinearMap.cancel_right (LinearMap.range_eq_top.1 (_root_.SymmetricPower.range_mk R (Fin n) M))).1
      refine (Basis.piTensorProduct fun _ : Fin n => b).ext fun f => ?_
      -- `⨂ₛ` is the quotient map applied to `⨂ₜ`.
      have hmk : _root_.SymmetricPower.mk R (Fin n) M (⨂ₜ[R] i, b (f i)) = ⨂ₛ[R] i, b (f i) := by
        rw [_root_.SymmetricPower.tprod, LinearMap.compMultilinearMap_apply]
      simp [hmk, toFinsupp_tprod_basis, tprodOfSym_ofFn])
end
end SymmetricPower

namespace Representation
section
open scoped _root_.TensorProduct
universe v w w'
variable {R : Type} {G : Type v} {M : Type w} {N : Type w'}
variable [CommSemiring R] [Monoid G]
variable [AddCommMonoid M] [Module R M]
/-- Literal Representation.symmetricPower; precise source and scope recorded in the extraction map. -/
noncomputable def symmetricPower (ρ : Representation R G M) (d : ℕ) :
    Representation R G (Sym[R]^d M) where
  toFun g := SymmetricPower.map (ι := Fin d) (ρ g)
  map_one' := by
    rw [ρ.map_one, Module.End.one_eq_id, SymmetricPower.map_id,
      Module.End.one_eq_id]
  map_mul' g h := by
    simpa only [map_mul, Module.End.mul_eq_comp] using
      (SymmetricPower.map_comp (ι := Fin d) (ρ h) (ρ g))
end
end Representation

namespace SymmetricPower
section
open Module
open scoped _root_.TensorProduct
universe v w
variable {R : Type} {M : Type v} {κ : Type w} {n : ℕ}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable (b : Basis κ R M)
variable (n)
/-- Literal Module.Basis.symmetricPower; precise source and scope recorded in the extraction map. -/
noncomputable def _root_.PalomarAlternatingLiteral.Module.Basis.symmetricPower : Basis (Sym κ n) R (Sym[R]^n M) :=
  Basis.ofRepr (linearEquivFinsupp n b)
end
end SymmetricPower

namespace TauCeti
section
open Matrix
universe u
variable (k : Type u) (n : ℕ)
variable [CommRing k]
/-- Literal TauCeti.stdRep; precise source and scope recorded in the extraction map. -/
def stdRep : Representation k (GL (Fin n) k) (Fin n → k) :=
  (Units.coeHom ((Fin n → k) →ₗ[k] (Fin n → k))).comp
    Matrix.GeneralLinearGroup.toLin.toMonoidHom
end
end TauCeti

namespace TauCeti
section
open Matrix
open scoped _root_.TensorProduct
variable (k : Type) (n d : ℕ)
variable [CommRing k]
/-- Literal TauCeti.symPowerRep; precise source and scope recorded in the extraction map. -/
noncomputable abbrev symPowerRep :
    Representation k (GL (Fin n) k) (Sym[k]^d (Fin n → k)) :=
  PalomarAlternatingLiteral.Representation.symmetricPower (stdRep k n) d
end
end TauCeti

namespace Representation
section
open scoped _root_.TensorProduct
universe u v w w'
variable {R : Type u} {G : Type v} {M : Type w} {N : Type w'}
variable [CommRing R] [Monoid G]
variable [AddCommGroup M] [Module R M]
/-- Literal Representation.exteriorPower; precise source and scope recorded in the extraction map. -/
noncomputable def exteriorPower (ρ : Representation R G M) (d : ℕ) :
    Representation R G (⋀[R]^d M) where
  toFun g := _root_.exteriorPower.map d (ρ g)
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' g h := by simp [Module.End.mul_eq_comp]
/-- Literal Representation.exteriorPower_apply; precise source and scope recorded in the extraction map. -/
theorem exteriorPower_apply (ρ : Representation R G M) (d : ℕ) (g : G) :
    PalomarAlternatingLiteral.Representation.exteriorPower ρ d g = _root_.exteriorPower.map d (ρ g) := by
  exact _root_.Representation.exteriorPower_apply (ρ := ρ) (d := d) (g := g)
end
end Representation

namespace PaperVerification.AlternatingForms.SymmetricPencil
section
set_option backward.isDefEq.respectTransparency false
open scoped _root_.TensorProduct BigOperators Classical
variable (K : Type) [Field K]
/-- Literal PaperVerification.AlternatingForms.SymmetricPencil.Standard; precise source and scope recorded in the extraction map. -/
abbrev Standard := Fin 2 → K
/-- Literal PaperVerification.AlternatingForms.SymmetricPencil.SymmetricDegree; precise source and scope recorded in the extraction map. -/
abbrev SymmetricDegree (d : ℕ) := Sym[K]^d (Standard K)
/-- Literal PaperVerification.AlternatingForms.SymmetricPencil.binaryIndex; precise source and scope recorded in the extraction map. -/
def binaryIndex (d : ℕ) : Sym (Fin 2) d ≃ Fin (d+1) :=
  (TauCeti.symFinTwoEquiv d).trans Fin.revPerm
/-- Literal PaperVerification.AlternatingForms.SymmetricPencil.binaryBasis; precise source and scope recorded in the extraction map. -/
def binaryBasis (d : ℕ) : Module.Basis (Fin (d+1)) K (SymmetricDegree K d) :=
  (PalomarAlternatingLiteral.Module.Basis.symmetricPower (b := Pi.basisFun K (Fin 2)) (n := d)).reindex (binaryIndex d)
/-- Literal PaperVerification.AlternatingForms.SymmetricPencil.Model; precise source and scope recorded in the extraction map. -/
abbrev Model (t : ℕ) := Module.Dual K (SymmetricDegree K t) × SymmetricDegree K (t+1)
/-- Literal PaperVerification.AlternatingForms.SymmetricPencil.modelRepresentation; precise source and scope recorded in the extraction map. -/
def modelRepresentation (t : ℕ) : Representation K (GL (Fin 2) K) (Model K t) :=
  (TauCeti.symPowerRep K 2 t).dual.prod (TauCeti.symPowerRep K 2 (t+1))
/-- Literal PaperVerification.AlternatingForms.SymmetricPencil.modelBasis; precise source and scope recorded in the extraction map. -/
def modelBasis (t : ℕ) : Module.Basis (Fin (2*(t+1)+1)) K (Model K t) :=
  ((binaryBasis K t).dualBasis.prod (binaryBasis K (t+1))).reindex (TopInterlacing.abIndex (t+1))
end
end PaperVerification.AlternatingForms.SymmetricPencil

namespace PaperVerification.AlternatingForms.Bidegree
section
open scoped BigOperators Classical
variable {K : Type*} [Field K]
/-- Literal PaperVerification.AlternatingForms.Bidegree.aIndexDegree; precise source and scope recorded in the extraction map. -/
def aIndexDegree {k : ℕ} (i : Fin (2*k+1)) : ℕ := if i.val%2=1 then 1 else 0
/-- Literal PaperVerification.AlternatingForms.Bidegree.aWordDegree; precise source and scope recorded in the extraction map. -/
def aWordDegree {k s : ℕ} (a : Fin s → Fin (2*k+1)) : ℕ :=
  ∑ j,aIndexDegree (a j)
end
end PaperVerification.AlternatingForms.Bidegree

namespace PaperVerification.AlternatingForms.Bidegree
section
open scoped Classical
variable {K : Type*} [Field K] [CharZero K]
/-- Literal PaperVerification.AlternatingForms.Bidegree.exteriorASubdegree; precise source and scope recorded in the extraction map. -/
def exteriorASubdegree (k s p : ℕ) :
    Submodule K (⋀[K]^s (Fin (2*k+1) → K)) :=
  Submodule.span K {x | ∃ I : PluckerIndex s (2*k+1),
    aWordDegree I.val=p ∧ x=exteriorPluckerBasis s (2*k+1) I}
/-- Literal PaperVerification.AlternatingForms.Bidegree.quotientASubdegree; precise source and scope recorded in the extraction map. -/
def quotientASubdegree (k s p : ℕ) :
    Submodule K (OddExteriorQuotientDegree (K := K) k s) :=
  (exteriorASubdegree k s p).map
    (exteriorDegreeRelations
      (oddPathFirstQuadratic (Pi.basisFun K (Fin (2*k+1))))
      (oddPathSecondQuadratic (Pi.basisFun K (Fin (2*k+1)))) s).mkQ
/-- Literal PaperVerification.AlternatingForms.Bidegree.actualBigradedPiece; precise source and scope recorded in the extraction map. -/
def actualBigradedPiece (k p q : ℕ) :
    Submodule K (OddExteriorQuotientDegree (K := K) k (p+q)) :=
  quotientASubdegree k (p+q) p
end
end PaperVerification.AlternatingForms.Bidegree

namespace PaperVerification.AlternatingForms.SymmetricPencil
section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical
variable (K : Type) [Field K]
/-- Literal PaperVerification.AlternatingForms.SymmetricPencil.Coordinates; precise source and scope recorded in the extraction map. -/
abbrev Coordinates (t : ℕ) := Fin (2*(t+1)+1) → K
/-- Literal PaperVerification.AlternatingForms.SymmetricPencil.coordinateEquiv; precise source and scope recorded in the extraction map. -/
def coordinateEquiv (t : ℕ) : Coordinates K t ≃ₗ[K] Model K t :=
  standardBasisEquiv (modelBasis K t)
/-- Literal PaperVerification.AlternatingForms.SymmetricPencil.coordinateRepresentation; precise source and scope recorded in the extraction map. -/
def coordinateRepresentation (t : ℕ) :
    Representation K (GL (Fin 2) K) (Coordinates K t) where
  toFun g := (coordinateEquiv K t).symm.toLinearMap ∘ₗ
    modelRepresentation K t g ∘ₗ (coordinateEquiv K t).toLinearMap
  map_one' := by
    ext x
    simp only [map_one, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Module.End.one_apply, LinearEquiv.symm_apply_apply]
  map_mul' g h := by
    ext x
    simp only [map_mul, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Module.End.mul_apply, LinearEquiv.apply_symm_apply]
set_option maxHeartbeats 1000000 in
/-- Literal PaperVerification.AlternatingForms.SymmetricPencil.original_relations_invariant; precise source and scope recorded in the extraction map. -/
theorem original_relations_invariant (t s : ℕ) (g : GL (Fin 2) K) :
    exteriorDegreeRelations
        (oddPathFirstQuadratic (Pi.basisFun K (Fin (2*(t+1)+1))))
        (oddPathSecondQuadratic (Pi.basisFun K (Fin (2*(t+1)+1)))) s ≤
      (exteriorDegreeRelations
        (oddPathFirstQuadratic (Pi.basisFun K (Fin (2*(t+1)+1))))
        (oddPathSecondQuadratic (Pi.basisFun K (Fin (2*(t+1)+1)))) s).comap
        (exteriorPower.map s (coordinateRepresentation K t g)) := by
  exact _root_.PaperVerification.AlternatingForms.SymmetricPencil.original_relations_invariant (K := K) (t := t) (s := s) (g := g)
/-- Literal PaperVerification.AlternatingForms.SymmetricPencil.quotientRepresentation; precise source and scope recorded in the extraction map. -/
def quotientRepresentation (t s : ℕ) :
    Representation K (GL (Fin 2) K) (OddExteriorQuotientDegree (K := K) (t+1) s) :=
  (PalomarAlternatingLiteral.Representation.exteriorPower (coordinateRepresentation K t) s).quotient _
    (by
      intro g
      simpa only [Representation.exteriorPower_apply] using original_relations_invariant K t s g)
end
end PaperVerification.AlternatingForms.SymmetricPencil

namespace PaperVerification.AlternatingForms.SymmetricPencil
section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical
variable (K : Type) [Field K] [CharZero K]
/-- Literal PaperVerification.AlternatingForms.SymmetricPencil.bigradedPiece_invariant; precise source and scope recorded in the extraction map. -/
theorem bigradedPiece_invariant (t p q : ℕ) (g : GL (Fin 2) K) :
    Bidegree.actualBigradedPiece (K := K) (t+1) p q ≤
      (Bidegree.actualBigradedPiece (K := K) (t+1) p q).comap
        (quotientRepresentation K t (p+q) g) := by
  exact _root_.PaperVerification.AlternatingForms.SymmetricPencil.bigradedPiece_invariant (K := K) (t := t) (p := p) (q := q) (g := g)
/-- Literal PaperVerification.AlternatingForms.SymmetricPencil.bigradedRepresentation; precise source and scope recorded in the extraction map. -/
def bigradedRepresentation (t p q : ℕ) :
    Representation K (GL (Fin 2) K)
      (Bidegree.actualBigradedPiece (K := K) (t+1) p q) :=
  (quotientRepresentation K t (p+q)).subrepresentation _
    (bigradedPiece_invariant K t p q)
end
end PaperVerification.AlternatingForms.SymmetricPencil

namespace PaperVerification.AlternatingForms.SymmetricPencil
section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators _root_.TensorProduct Classical
open TopInterlacing
variable (K : Type) [Field K]
variable [CharZero K]
/-- Literal PaperVerification.AlternatingForms.SymmetricPencil.naturalBigradedRepresentation; precise source and scope recorded in the extraction map. -/
def naturalBigradedRepresentation : (k p q : ℕ) →
    Representation K (GL (Fin 2) K) (Bidegree.actualBigradedPiece (K := K) k p q)
  | 0, p, q => Representation.trivial K (GL (Fin 2) K) _
  | t+1, p, q => bigradedRepresentation K t p q
end
end PaperVerification.AlternatingForms.SymmetricPencil

namespace PaperVerification.AlternatingForms.TopRepresentation
section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators _root_.TensorProduct
open Matrix
open SymmetricPencil TopInterlacing TauCeti
variable (K : Type) [Field K]
/-- Literal PaperVerification.AlternatingForms.TopRepresentation.plethysmRepresentation; precise source and scope recorded in the extraction map. -/
def plethysmRepresentation (p q : ℕ) :
    Representation K (GL (Fin 2) K) (Sym[K]^(2*p+1) (Sym[K]^q (Fin 2 → K))) :=
  PalomarAlternatingLiteral.Representation.symmetricPower (TauCeti.symPowerRep K 2 q) (2*p+1)
end
end PaperVerification.AlternatingForms.TopRepresentation

namespace PaperVerification.AlternatingForms.TopRepresentation
section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators _root_.TensorProduct
open Matrix
open SymmetricPencil TopInterlacing TauCeti
variable (K : Type) [Field K]
variable [CharZero K]
/-- Literal PaperVerification.AlternatingForms.TopRepresentation.paper_corollary_5_2; precise source and scope recorded in the extraction map. -/
theorem paper_corollary_5_2 (p q : ℕ) :
    Nonempty
      (Representation.Equiv
        ((naturalBigradedRepresentation ℂ (p+q) p q).comp Matrix.SpecialLinearGroup.toGL)
        ((plethysmRepresentation ℂ p q).comp Matrix.SpecialLinearGroup.toGL)) ∧
      Module.finrank ℂ (Bidegree.actualBigradedPiece (K := ℂ) (p+q) p q) =
        (2*p+q+1).choose q := by
  exact _root_.PaperVerification.AlternatingForms.TopRepresentation.paper_corollary_5_2 (p := p) (q := q)
end
end PaperVerification.AlternatingForms.TopRepresentation




namespace PaperVerification.MainStatements
section
open MvPolynomial PaperVerification.AlternatingForms
variable {K M : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]
/-- Literal PaperVerification.MainStatements.genericHilbertSeriesAndVanishing; precise source and scope recorded in the extraction map. -/
theorem genericHilbertSeriesAndVanishing (n : ℕ) (hdim : Module.finrank K M = n) :
    ∃ (ι : Type) (fin : Fintype ι),
      letI := fin
      ∃ b₂ : Module.Basis ι K (⋀[K]^2 M),
        ∃ Q : MvPolynomial (ι ⊕ ι) K, Q ≠ 0 ∧
          (∃ y : (ι ⊕ ι) → K, eval y Q ≠ 0) ∧
          ∀ y : (ι ⊕ ι) → K, eval y Q ≠ 0 →
            exteriorPairHilbertSeries
                (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 =
              paperExteriorHilbertSeries n ∧
            ∀ s : ℕ, (n + 1) / 2 < s →
              ∀ x : ExteriorQuotientDegree
                (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 s,
                x = 0 := by
  exact _root_.PaperVerification.MainStatements.genericHilbertSeriesAndVanishing (n := n) (hdim := hdim)
end
end PaperVerification.MainStatements

end PalomarAlternatingLiteral
