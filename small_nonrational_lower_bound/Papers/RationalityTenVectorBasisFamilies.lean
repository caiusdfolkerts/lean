module
public import Papers.RationalityTenBasisCertificates
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

@[expose] public section
noncomputable section

namespace Papers.RationalityTen.VectorBasisFamilies

open Finset Submodule
open BasisFamilies BasisReconstruction

abbrev Point := Fin 8

variable {K : Type*} [Field K]

theorem groundPrefix_eight : groundPrefix 8 = (univ : Finset Point) := by
  ext x
  simp only [mem_groundPrefix,mem_univ,iff_true]
  exact x.isLt

theorem span_image_eq_range (p : Point → Fin 4 → K) (S : Finset Point) :
    p '' (S : Set Point) = Set.range (fun i : S => p i.val) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,rfl⟩
  · rintro ⟨x,rfl⟩
    exact ⟨x.val,x.property,rfl⟩

theorem card_of_independent_spanning (p : Point → Fin 4 → K)
    (S : Finset Point) (hLI : LinearIndepOn K p (S : Set Point))
    (hspan : span K (p '' (S : Set Point)) = ⊤) : S.card = 4 := by
  have hLI' : LinearIndependent K (fun i : S => p i.val) := hLI
  have h := finrank_span_eq_card hLI'
  rw [← span_image_eq_range p S,hspan] at h
  simpa only [finrank_top,Module.finrank_pi,Module.finrank_self,Fintype.card_fin,
    Fintype.card_coe,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using h.symm

theorem span_of_independent_card (p : Point → Fin 4 → K)
    (S : Finset Point) (hLI : LinearIndepOn K p (S : Set Point))
    (hcard : S.card = 4) : span K (p '' (S : Set Point)) = ⊤ := by
  rw [span_image_eq_range p S]
  have hLI' : LinearIndependent K (fun i : S => p i.val) := hLI
  apply hLI'.span_eq_top_of_card_eq_finrank'
  simpa only [Fintype.card_coe,Module.finrank_pi,Module.finrank_self,Fintype.card_fin,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using hcard

theorem exists_four_basis_extension (p : Point → Fin 4 → K)
    (hspan : span K (Set.range p) = ⊤) (S : Set Point)
    (hLI : LinearIndepOn K p S) :
    ∃ A : Finset Point, S ⊆ A ∧ A.card = 4 ∧
      LinearIndepOn K p (A : Set Point) := by
  classical
  obtain ⟨T,hT,hST,hsp,hTLI⟩ := exists_linearIndepOn_extension hLI (Set.subset_univ S)
  let A := T.toFinset
  have hAset : (A : Set Point) = T := Set.coe_toFinset T
  have hspT : span K (p '' T) = ⊤ := by
    apply top_unique
    rw [← hspan]
    apply span_le.mpr
    simpa only [Set.image_univ] using hsp
  have hALI : LinearIndepOn K p (A : Set Point) := hAset.symm ▸ hTLI
  refine ⟨A,?_,card_of_independent_spanning p A hALI ?_,hALI⟩
  · simpa only [hAset] using hST
  · simpa only [hAset] using hspT

def vectorBases (p : Point → Fin 4 → K) : Finset (Finset Point) := by
  classical
  exact (univ.powersetCard 4).filter fun A => LinearIndepOn K p (A : Set Point)

theorem mem_vectorBases (p : Point → Fin 4 → K) (A : Finset Point) :
    A ∈ vectorBases p ↔ A.card = 4 ∧ LinearIndepOn K p (A : Set Point) := by
  simp [vectorBases]

def vectorBasisFamily (p : Point → Fin 4 → K)
    (hspan : span K (Set.range p) = ⊤) (hnz : ∀ i, p i ≠ 0) :
    BasisFamily (groundPrefix 8) 4 where
  bases := vectorBases p
  nonempty := by
    obtain ⟨A,hA,hcard,hLI⟩ := exists_four_basis_extension p hspan ∅ (by simp)
    exact ⟨A,(mem_vectorBases p A).mpr ⟨hcard,hLI⟩⟩
  subset_ground := by
    intro A hA
    rw [groundPrefix_eight]
    exact subset_univ _
  basis_card := fun A hA => ((mem_vectorBases p A).mp hA).1
  exchange := by
    intro A hA B hB x hxA hxB
    obtain ⟨hAc,hALI⟩ := (mem_vectorBases p A).mp hA
    obtain ⟨hBc,hBLI⟩ := (mem_vectorBases p B).mp hB
    have hxnot : p x ∉ span K (p '' ((A.erase x : Finset Point) : Set Point)) := by
      simpa only [Finset.coe_erase] using hALI.notMem_span hxA
    have hBspan := span_of_independent_card p B hBLI hBc
    have hex : ∃ y ∈ B, p y ∉ span K (p '' ((A.erase x : Finset Point) : Set Point)) := by
      by_contra h
      have hall : ∀ y ∈ B, p y ∈ span K (p '' ((A.erase x : Finset Point) : Set Point)) := by
        intro y hy
        by_contra hn
        exact h ⟨y,hy,hn⟩
      have hs : span K (p '' (B : Set Point)) ≤
          span K (p '' ((A.erase x : Finset Point) : Set Point)) := by
        apply span_le.mpr
        rintro z ⟨y,hy,rfl⟩
        exact hall y hy
      rw [hBspan] at hs
      exact hxnot (hs (by trivial))
    obtain ⟨y,hyB,hynot⟩ := hex
    have hyA : y ∉ A := by
      intro hyA
      have hyx : y ≠ x := fun h => hxB (h ▸ hyB)
      exact hynot (subset_span ⟨y,mem_erase.mpr ⟨hyx,hyA⟩,rfl⟩)
    refine ⟨y,hyB,hyA,(mem_vectorBases p _).mpr ⟨?_,?_⟩⟩
    · rw [card_insert_of_notMem (fun h=>hyA (mem_erase.mp h).2),
        card_erase_of_mem hxA,hAc]
    · have hErase : LinearIndepOn K p ((A.erase x : Finset Point) : Set Point) :=
        hALI.mono (by exact erase_subset _ _)
      simpa only [Finset.coe_insert] using hErase.insert hynot
  loopless := by
    intro x hx
    have hLI : LinearIndepOn K p ({x} : Set Point) :=
      (linearIndepOn_singleton_iff (R:=K)).mpr (hnz x)
    obtain ⟨A,hxA,hcard,hALI⟩ := exists_four_basis_extension p hspan {x} hLI
    exact ⟨A,(mem_vectorBases p A).mpr ⟨hcard,hALI⟩,hxA (by simp)⟩

@[simp] theorem vectorBasisFamily_bases (p : Point → Fin 4 → K)
    (hspan : span K (Set.range p) = ⊤) (hnz : ∀ i, p i ≠ 0) :
    (vectorBasisFamily p hspan hnz).bases = vectorBases p := rfl

end Papers.RationalityTen.VectorBasisFamilies
