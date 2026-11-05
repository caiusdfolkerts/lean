import Characterizations.Strands.TotalDimension
import Characterizations.Strands.DeletedGeneratorTheorem
import CommAlg.KoszulComplex.ResidueCoefficients
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

/-! # The manuscript's `Tor(I,k)` and its genuine homogeneous submodules

The existing Koszul construction resolves the residue module in the first tensor
factor. Tensor braiding identifies that derived functor with Mathlib's `Tor(I,k)`,
which resolves the same residue module in the second factor. This does not use or
assume a balance theorem between two different projective resolutions.
-/
noncomputable section
namespace Characterizations
open CategoryTheory CategoryTheory.MonoidalCategory CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V]

section Ring
variable [CommRing k]

def tensorBraidingDerivedIso (M : ModuleCat.{u} (MvPolynomial V k)) (i : ℕ) :
    (((tensoringRight _).obj M).leftDerived i) ≅
      (((tensoringLeft _).obj M).leftDerived i) where
  hom := NatTrans.leftDerived (BraidedCategory.tensorLeftIsoTensorRight M).inv i
  inv := NatTrans.leftDerived (BraidedCategory.tensorLeftIsoTensorRight M).hom i
  hom_inv_id := by
    rw [← NatTrans.leftDerived_comp, Iso.inv_hom_id, NatTrans.leftDerived_id]
  inv_hom_id := by
    rw [← NatTrans.leftDerived_comp, Iso.hom_inv_id, NatTrans.leftDerived_id]

/-- The exact chain isomorphism inducing the change of tensor order. -/
def tensorBraidingChainIso (M : ModuleCat.{u} (MvPolynomial V k))
    (P : ChainComplex (ModuleCat.{u} (MvPolynomial V k)) ℕ) :
    (((tensoringRight _).obj M).mapHomologicalComplex (ComplexShape.down ℕ)).obj P ≅
      (((tensoringLeft _).obj M).mapHomologicalComplex (ComplexShape.down ℕ)).obj P :=
  (NatIso.mapHomologicalComplex (BraidedCategory.tensorLeftIsoTensorRight M).symm
    (ComplexShape.down ℕ)).app P

/-- In each chain degree the map merely switches the two tensor factors;
in particular both their polynomial and exterior degrees are retained. -/
@[simp] theorem tensorBraidingChainIso_tmul
    (M : ModuleCat.{u} (MvPolynomial V k))
    (P : ChainComplex (ModuleCat.{u} (MvPolynomial V k)) ℕ)
    (j : ℕ) (x : P.X j) (m : M) :
    (tensorBraidingChainIso M P).hom.f j (x ⊗ₜ[MvPolynomial V k] m) =
      m ⊗ₜ[MvPolynomial V k] x := rfl

/-- Compatibility with the actual homology map of the displayed chain braiding. -/
theorem tensorBraidingDerivedIso_eq_homology
    {X : ModuleCat.{u} (MvPolynomial V k)} (P : ProjectiveResolution X)
    (M : ModuleCat.{u} (MvPolynomial V k)) (i : ℕ) :
    (tensorBraidingDerivedIso M i).hom.app X =
      (P.isoLeftDerivedObj ((tensoringRight _).obj M) i).hom ≫
        (HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ) i).map
          (tensorBraidingChainIso M P.complex).hom ≫
        (P.isoLeftDerivedObj ((tensoringLeft _).obj M) i).inv :=
  P.leftDerived_app_eq (BraidedCategory.tensorLeftIsoTensorRight M).inv i

/-- The manuscript's derived Tor with the actual coefficient ring carrying
the polynomial action by evaluation at zero. -/
def paperTor (M : ModuleCat.{u} (MvPolynomial V k)) (i : ℕ) :=
  ((Tor (ModuleCat (MvPolynomial V k)) i).obj M).obj
    (residueCoefficientModule (V := V) (k := k))

/-- Canonical agreement with the exact argument ordering `Tor_i(M,k)`. -/
def polynomialTorOrderIso (M : ModuleCat.{u} (MvPolynomial V k)) (i : ℕ) :
    finitePolynomialTor i M ≅ paperTor M i :=
  (tensorBraidingDerivedIso M i).app
      (ModuleCat.of (MvPolynomial V k) (FiniteResidue V k)) ≪≫
    ((Tor (ModuleCat (MvPolynomial V k)) i).obj M).mapIso residueCoefficientIso

def coefficientTorOrderIso (B : Family V) (i : ℕ) :=
  (ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).mapIso
    (polynomialTorOrderIso (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)) i)

end Ring

section Field
variable [Field k]

/-- The fine-degree piece transported through the canonical derived tensor braiding. -/
def paperGradedTor (B : Family V) (a : Exponent V) (i : ℕ) :=
  (gradedTor (k := k) B a i).map (coefficientTorOrderIso (k := k) B i).hom.hom

/-- The total-degree piece inside Mathlib's literal `Tor_i(I,k)`. -/
def paperTotalDegreeTor (B : Family V) (i j : ℕ) :=
  (totalDegreeTor (k := k) B i j).map (coefficientTorOrderIso (k := k) B i).hom.hom

theorem paperTotalDegreeTor_eq_sum (B : Family V) (i j : ℕ) :
    paperTotalDegreeTor (k := k) B i j =
      ⨆ (a : Exponent V) (_ : a.degree = j), paperGradedTor (k := k) B a i := by
  simp only [paperTotalDegreeTor, totalDegreeTor, Submodule.map_iSup, paperGradedTor]

theorem paperGradedTor_finrank (B : Family V) (a : Exponent V) (i : ℕ) :
    Module.finrank k (paperGradedTor (k := k) B a i) = bettiNumber (k := k) B a i :=
  (coefficientTorOrderIso (k := k) B i).toLinearEquiv.finrank_map_eq _

theorem paperGradedTor_finite (B : Family V) (a : Exponent V) (i : ℕ) :
    FiniteDimensional k (paperGradedTor (k := k) B a i) := by
  let e := (coefficientTorOrderIso (k := k) B i).toLinearEquiv.submoduleMap
    (gradedTor (k := k) B a i)
  exact FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective

theorem paperTotalDegreeTor_finrank (B : Family V) (i j : ℕ) :
    Module.finrank k (paperTotalDegreeTor (k := k) B i j) =
      Strands.totalBettiNumber (k := k) B i j := by
  exact ((coefficientTorOrderIso (k := k) B i).toLinearEquiv.finrank_map_eq _).trans
    (Strands.finrank_totalDegreeTor B i j)

theorem paperTotalDegreeTor_finite (B : Family V) (i j : ℕ) :
    FiniteDimensional k (paperTotalDegreeTor (k := k) B i j) := by
  letI := Strands.totalDegreeTor_finite (k := k) B i j
  let e := (coefficientTorOrderIso (k := k) B i).toLinearEquiv.submoduleMap
    (totalDegreeTor (k := k) B i j)
  exact FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective

theorem paperTotalDegreeTor_eq_bot_iff (B : Family V) (i j : ℕ) :
    paperTotalDegreeTor (k := k) B i j = ⊥ ↔ totalDegreeTor (k := k) B i j = ⊥ :=
  Submodule.map_eq_bot_iff (e := (coefficientTorOrderIso (k := k) B i).toLinearEquiv)

/-- No part of `Tor(I,k)` is lost by the transported total grading. -/
theorem iSup_paperTotalDegreeTor (B : Family V) (i : ℕ) :
    (⨆ j : ℕ, paperTotalDegreeTor (k := k) B i j) = ⊤ := by
  simp only [paperTotalDegreeTor, ← Submodule.map_iSup, iSup_totalDegreeTor]
  exact (Submodule.map_eq_top_iff
    (e := (coefficientTorOrderIso (k := k) B i).toLinearEquiv)).mpr rfl

/-- The paper's initial-segment condition with its literal derived tensor order. -/
def PaperRetainedTorLinearThrough (B : Family V) (U : Finset V) (e t : ℕ) : Prop :=
  ∀ i : ℕ, i ≤ t → ∀ j : ℕ, j ≠ e+i →
    paperTotalDegreeTor (k := k) (localFamily B U) i j = ⊥

theorem paperRetainedTorLinearThrough_iff (B : Family V) (U : Finset V) (e t : ℕ) :
    PaperRetainedTorLinearThrough (k := k) B U e t ↔
      RetainedTorLinearThrough (k := k) B U e t := by
  simp only [PaperRetainedTorLinearThrough, RetainedTorLinearThrough,
    paperTotalDegreeTor_eq_bot_iff]

/-- Theorem 4.2 with actual `Tor_i(I_U,k)` over `k[U]`. -/
theorem polymatroidal_iff_degree_tests_paperTor {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) : IsPolymatroidal B ↔
    ∀ U : Finset V, ∃ e, Equigenerated (localFamily B U) e ∧
      (0 < e → PaperRetainedTorLinearThrough (k := k) B U e (e-1)) := by
  simp only [paperRetainedTorLinearThrough_iff]
  exact polymatroidal_iff_degree_tests_totalTor hB hanti

/-- The equivalent degree-and-dimension cutoff in Theorem 4.2. -/
theorem polymatroidal_iff_degree_dimension_tests_paperTor {B : Family V}
    (hB : B.Nonempty) (hanti : Antichain B) : IsPolymatroidal B ↔
    ∀ U : Finset V, ∃ e, Equigenerated (localFamily B U) e ∧
      (0 < e → PaperRetainedTorLinearThrough (k := k) B U e (min (e-1) (U.card-1))) := by
  simp only [paperRetainedTorLinearThrough_iff]
  exact polymatroidal_iff_degree_dimension_tests_totalTor hB hanti

/-- Theorem 4.9 in exactly the manuscript's derived tensor order. -/
theorem polymatroidal_iff_triangular_paperTor {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (hd2 : 2 ≤ d) : IsPolymatroidal B ↔
    ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-1 →
      ∃ e, Equigenerated (localFamily B U) e ∧
        (0 < e → PaperRetainedTorLinearThrough (k := k) B U e
          (min (e-1) (min (d-1-(Fintype.card V-U.card)) (U.card-1)))) := by
  simp only [paperRetainedTorLinearThrough_iff]
  exact polymatroidal_iff_triangular_totalTor hB hd hd2

/-- Proposition 4.3's total nonlinear strand as a dimension inside `Tor_i(I,k)`. -/
theorem deleted_generator_paperTor_finrank (a : Exponent V)
    (ha : 2 ≤ a.support.card) (i : ℕ) :
    Module.finrank k (paperTotalDegreeTor (k := k) (deletedVeronese a) i (a.degree+i+1)) =
      if a.support.card ≤ i+1 then
        Nat.choose (Fintype.card V-a.support.card) (i+1-a.support.card) else 0 := by
  rw [paperTotalDegreeTor_finrank]
  exact Strands.deletedVeronese_total_nonlinear a ha i

/-- Proposition 4.3's complete nonlinear fine strand inside literal `Tor_i(I,k)`. -/
theorem deleted_generator_paperGradedTor_finrank (a b : Exponent V)
    (ha : 2 ≤ a.support.card) (i : ℕ) (hoff : b.degree ≠ a.degree+i) :
    Module.finrank k (paperGradedTor (k := k) (deletedVeronese a) b i) =
      if ∃ T : Finset V, a.support ⊆ T ∧ T.card=i+1 ∧ b=a+faceExponent T
        then 1 else 0 := by
  rw [paperGradedTor_finrank]
  exact (Strands.deleted_generator_nonlinear_strand (k := k) a ha).2.1 i b hoff

end Field
end Characterizations
