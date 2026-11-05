import CommAlg.KoszulComplex.Faces
import CommAlg.KoszulComplex.MonomialDifferential

/-! # Homogeneous Koszul components are genuinely isomorphic to upper-face chains -/

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false

namespace CommAlg.Koszul

open Classical CommAlg.Polymatroid CategoryTheory

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

lemma boundary_basis_sum (s : Finset V) :
    Simplicial.boundary (Simplicial.basis (k := k) s) =
      ∑ j : {j // j ∈ s}, TauCeti.ExteriorAlgebra.basisEraseSign j.val s •
        Simplicial.basis (s.erase j.val) := by
  rw [Simplicial.boundary_eq_sum]
  calc
    ∑ j : V, Simplicial.contraction j (Simplicial.basis s) =
        ∑ j ∈ s, Simplicial.contraction j (Simplicial.basis s) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j hj hnot
      simp only [Simplicial.contraction_basis, if_neg hnot]
    _ = ∑ j : {j // j ∈ s}, Simplicial.contraction j.val (Simplicial.basis s) :=
      Finset.sum_subtype s (fun _ => Iff.rfl) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Simplicial.contraction_basis, if_pos j.property]

def eraseFace {B : Family V} {a : Exponent V} {i : ℕ}
    (s : FaceIndex B a (i + 1)) (j : {j // j ∈ s.val}) : FaceIndex B a i :=
  ⟨s.val.erase j.val,
    (koszulFaces_downward B a) (Finset.erase_subset _ _) s.property.1,
    by simp [Finset.card_erase_of_mem j.property, s.property.2]⟩

lemma faceChainDifferential_basis (B : Family V) (a : Exponent V) (i : ℕ)
    (s : FaceIndex B a (i + 1)) :
    Simplicial.chainDifferential (k := k) (koszulFaces_downward B a) i
      (faceChainBasis (k := k) B a (i + 1) s) =
      ∑ j : {j // j ∈ s.val}, TauCeti.ExteriorAlgebra.basisEraseSign j.val s.val •
        faceChainBasis (k := k) B a i (eraseFace s j) := by
  apply Subtype.ext
  simp only [Simplicial.chainDifferential_val, faceChainBasis_val,
    Submodule.coe_sum, Submodule.coe_smul_of_tower, eraseFace]
  exact boundary_basis_sum s.val

lemma faceMonomialEquiv_erase (B : Family V) (a : Exponent V) (i : ℕ)
    (s : FaceIndex B a (i + 1)) (j : {j // j ∈ s.val}) :
    (faceMonomialEquiv B a i (eraseFace s j)).val =
      differentialIndex (faceMonomialEquiv B a (i + 1) s).val j := by
  have hExp : a - faceExponent (s.val.erase j.val) =
      a - faceExponent s.val + Finsupp.single j.val 1 := by
    have he := faceExponent_erase_add j.property
    have hle := s.property.1.1
    ext v
    have hv := hle v
    have hev := congrArg (fun b : Exponent V => b v) he
    simp only [Finsupp.add_apply, Finsupp.tsub_apply] at *
    omega
  exact congrArg (fun b : {b : Exponent V // Contains B b} =>
    (⟨eraseIndex ⟨s.val, s.property.2⟩ j, b⟩ : MonomialIndex B i)) (Subtype.ext hExp)

lemma faceHomogeneousEquiv_comm (B : Family V) (a : Exponent V) (i : ℕ) :
    (faceHomogeneousEquiv (k := k) B a i).toLinearMap ∘ₗ
        Simplicial.chainDifferential (koszulFaces_downward B a) i =
      homogeneousDifferential (k := k) B a i ∘ₗ
        (faceHomogeneousEquiv (k := k) B a (i + 1)).toLinearMap := by
  apply (faceChainBasis (k := k) B a (i + 1)).ext
  intro s
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, faceChainDifferential_basis,
    map_sum, map_zsmul_unit]
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, faceHomogeneousEquiv_basis]
  change _ = monomialDifferential (k := k) B i
    ((faceHomogeneousEquiv (k := k) B a (i + 1))
      ((faceChainBasis (k := k) B a (i + 1)) s)).val
  rw [faceHomogeneousEquiv_basis, monomialDifferential_basis]
  apply Finset.sum_congr rfl
  intro j hj
  rw [faceMonomialEquiv_erase]
  rfl

/-- Kernel-checked chain isomorphism, including every homological and multigraded degree. -/
def homogeneousFacesIso (B : Family V) (a : Exponent V) :
    Simplicial.chainComplex (k := k) (koszulFaces_downward B a) ≅
      homogeneousComplex (k := k) B a :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (faceHomogeneousEquiv (k := k) B a i).toModuleIso) (by
      intro i j hij
      obtain rfl : i = j + 1 := hij.symm
      rw [Simplicial.chainComplex_d, homogeneousComplex_d]
      apply ModuleCat.hom_ext
      exact (faceHomogeneousEquiv_comm B a j).symm)

/-- Nonvanishing of an actual homogeneous Koszul homology group is exactly the face-chain condition. -/
lemma homogeneous_homology_nonzero_iff (B : Family V) (a : Exponent V) (i : ℕ) :
    ¬ CategoryTheory.Limits.IsZero ((homogeneousComplex (k := k) B a).homology i) ↔
      Simplicial.NonzeroHomology (k := k) (koszulFaces B a) i := by
  have e := (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) i).mapIso
    (homogeneousFacesIso (k := k) B a)
  have he : CategoryTheory.Limits.IsZero
      ((Simplicial.chainComplex (k := k) (koszulFaces_downward B a)).homology i) ↔
      CategoryTheory.Limits.IsZero ((homogeneousComplex (k := k) B a).homology i) :=
    e.isZero_iff
  exact (not_congr he.symm).trans (Simplicial.homology_nonzero_iff _ i)

end CommAlg.Koszul
