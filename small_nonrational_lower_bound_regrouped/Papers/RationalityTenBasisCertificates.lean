module
public import Papers.RationalityTenBasisCatalogue
public import Mathlib.Data.Fintype.Card

@[expose] public section

namespace Papers.RationalityTen.BasisCertificates

open Finset BasisFamilies BasisReconstruction BasisCatalogue

abbrev Point := Fin 8

/-- A balanced literal lookup expression. No search-order invariant is assumed:
every returned witness is checked against the mathematical statement. -/
inductive Table (α : Type) where
  | leaf : α → Table α
  | node : ℕ → Table α → Table α → Table α

def Table.get {α : Type} (t : Table α) (i : ℕ) : α :=
  match t with
  | .leaf a => a
  | .node k l r => if i < k then l.get i else r.get i

def maskPoints (m : ℕ) : Finset Point :=
  univ.filter fun x => m.testBit x.val = true

def familyOfMasks (masks : List ℕ) : Finset (Finset Point) :=
  masks.toFinset.image maskPoints

def permutationFunction (code : ℕ) (i : Point) : Point :=
  ⟨(code / 8^i.val) % 8,Nat.mod_lt _ (by decide)⟩

def ValidPermutation (n code : ℕ) : Prop :=
  Function.Injective (permutationFunction code) ∧
    ∀ x : Point, n ≤ x.val → permutationFunction code x = x

instance (n code : ℕ) : Decidable (ValidPermutation n code) := by
  unfold ValidPermutation Function.Injective
  infer_instance

noncomputable def checkedPermutation (n code : ℕ) (h : ValidPermutation n code) :
    Equiv.Perm Point :=
  Equiv.ofBijective (permutationFunction code)
    ⟨h.1,Finite.surjective_of_injective h.1⟩

theorem checkedPermutation_apply (n code : ℕ) (h : ValidPermutation n code) (x : Point) :
    checkedPermutation n code h x = permutationFunction code x := rfl

def ValidWitness (n : ℕ) (A B : Finset (Finset Point)) (code : ℕ) : Prop :=
  ValidPermutation n code ∧
    A.image (fun S => S.image (permutationFunction code)) = B

instance (n : ℕ) (A B : Finset (Finset Point)) (code : ℕ) :
    Decidable (ValidWitness n A B code) := by
  unfold ValidWitness
  infer_instance

theorem validWitness_sound (n : ℕ) (A B : Finset (Finset Point)) (code : ℕ)
    (h : ValidWitness n A B code) : IsomorphicWithin n A B := by
  refine ⟨checkedPermutation n code h.1,h.1.2,?_⟩
  exact h.2

/-- Images of a complete finite basis grid enumerate every possible basis;
the equality is finite data checked separately for each n and rank. -/
theorem basis_grid_complete {n r k : ℕ}
    (U : Fin k → Finset Point)
    (hgrid : univ.image U = (groundPrefix n).powersetCard r)
    (M : BasisFamily (groundPrefix n) r) :
    ∀ A ∈ M.bases, ∃ i, U i = A := by
  intro A hA
  have hh : A ∈ (groundPrefix n).powersetCard r :=
    mem_powersetCard.mpr ⟨M.subset_ground A hA,M.basis_card A hA⟩
  rw [← hgrid] at hh
  obtain ⟨i,hi,heq⟩ := mem_image.mp hh
  exact ⟨i,heq⟩


open BasisExtensionCNF in
theorem extension_covered_of_certificate
    {n r k t l : ℕ} (hn : n < 8)
    (C : Catalogue) (old : Finset (Finset Point))
    (U : Fin k → Finset Point) (newIndex : Fin t → Fin k)
    (models : Fin l → ℕ)
    (certificates : List (Origin k l × List Sat.Literal))
    (hgrid : univ.image U = (groundPrefix (n+1)).powersetCard r)
    (holdcomplete : ∀ A ∈ old, ∃ i, U i = A)
    (holdavoid : ∀ A ∈ old, (⟨n,hn⟩ : Point) ∉ A)
    (hnew : ∀ i, (⟨n,hn⟩ : Point) ∈ U i → ∃ j, newIndex j = i)
    (hvalid : ∀ oc ∈ certificates,
      ValidOrigin U ⟨n,hn⟩ old newIndex models oc.1 oc.2)
    (hrefute : Sat.Fmla.proof (certificates.map Prod.snd) [])
    (hmodels : ∀ w : Fin l, ∃ B ∈ C (n+1) r,
      IsomorphicWithin (n+1) (extensionFamily old U newIndex (models w)) B) :
    ∀ M : BasisFamily (groundPrefix (n+1)) r,
      M.bases.filter ((⟨n,hn⟩ : Point) ∉ ·) = old →
      ∃ B ∈ C (n+1) r, IsomorphicWithin (n+1) M.bases B := by
  intro M hrestriction
  have hcomplete := basis_grid_complete U hgrid M
  have hold : ∀ i, (⟨n,hn⟩ : Point) ∉ U i →
      (U i ∈ M.bases ↔ U i ∈ old) := by
    intro i hi
    rw [← hrestriction,mem_filter]
    exact ⟨fun h=>⟨h,hi⟩,And.left⟩
  obtain ⟨w,hw⟩ := exists_model_of_refutation M U ⟨n,hn⟩ old newIndex models
    certificates hcomplete (by simp only [mem_groundPrefix]; omega) hold hvalid hrefute
  have heq := extensionFamily_eq M U ⟨n,hn⟩ old newIndex (models w)
    hcomplete hold holdcomplete holdavoid hnew hw
  rw [heq]
  exact hmodels w

end Papers.RationalityTen.BasisCertificates
