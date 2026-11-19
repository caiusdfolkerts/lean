module
public import Papers.RationalityTenVectorBasisFamilies
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section
noncomputable section

namespace Papers.RationalityTen.VectorBasisFamilies

open Finset Matrix

variable {K : Type*} [Field K]

theorem det_ne_zero_iff_basis_image (p : Point → Fin 4 → K)
    (b : Fin 4 → Point) :
    Matrix.det (fun i j => p (b i) j)≠0 ↔
      Finset.univ.image b∈vectorBases p := by
  classical
  let A : Matrix (Fin 4) (Fin 4) K := fun i j=>p (b i) j
  have hdet : A.det≠0 ↔ LinearIndependent K (p∘b) := by
    rw [←isUnit_iff_ne_zero,←Matrix.isUnit_iff_isUnit_det,
      ←Matrix.linearIndependent_row_iff_isUnit]
    rfl
  rw [hdet,mem_vectorBases]
  have hset : ((Finset.univ.image b : Finset Point) : Set Point)=Set.range b := by
    simp only [Finset.coe_image,Finset.coe_univ,Set.image_univ]
  rw [hset]
  constructor
  · intro hLI
    have hb : Function.Injective b := hLI.injective.of_comp
    refine ⟨?_,(linearIndepOn_range_iff hb p).mpr hLI⟩
    rw [Finset.card_image_of_injective _ hb,Finset.card_univ,Fintype.card_fin]
  · rintro ⟨hcard,hLI⟩
    have hb : Function.Injective b := by
      have hh : (Finset.univ.image b).card=(Finset.univ : Finset (Fin 4)).card := by
        simpa only [Finset.card_univ,Fintype.card_fin] using hcard
      exact fun i j hij=>(Finset.card_image_iff.mp hh) (Finset.mem_univ i) (Finset.mem_univ j) hij
    exact (linearIndepOn_range_iff hb p).mp hLI

theorem det_zero_iff_not_basis_image (p : Point → Fin 4 → K)
    (b : Fin 4 → Point) :
    Matrix.det (fun i j=>p (b i) j)=0 ↔
      Finset.univ.image b∉vectorBases p := by
  simpa only [not_not] using not_congr (det_ne_zero_iff_basis_image p b)

theorem ordered_zero_minors_of_equal_bases
    (p q : Point → Fin 4 → K) (h : vectorBases p=vectorBases q) :
    ∀ b : Fin 4 → Point,
      Matrix.det (fun i j=>p (b i) j)=0 ↔
      Matrix.det (fun i j=>q (b i) j)=0 := by
  intro b
  rw [det_zero_iff_not_basis_image,det_zero_iff_not_basis_image,h]

/-- Exact passage from a complete list of four-element subsets to every
ordered four-tuple, including repeated labels. -/
theorem ordered_zero_minors_of_subset_grid
    {k : ℕ} (U : Fin k → Finset Point) (b : Fin k → Fin 4 → Point)
    (hgrid : ∀ A : Finset Point,A.card=4 → ∃ i,U i=A)
    (hb : ∀ i,Finset.univ.image (b i)=U i)
    (p q : Point → Fin 4 → K)
    (hzero : ∀ i, Matrix.det (fun j a=>p (b i j) a)=0 ↔
      Matrix.det (fun j a=>q (b i j) a)=0) :
    ∀ c : Fin 4 → Point,
      Matrix.det (fun i j=>p (c i) j)=0 ↔
      Matrix.det (fun i j=>q (c i) j)=0 := by
  apply ordered_zero_minors_of_equal_bases
  ext A
  by_cases hc : A.card=4
  · obtain ⟨i,rfl⟩ := hgrid A hc
    have hi := hzero i
    rw [det_zero_iff_not_basis_image,det_zero_iff_not_basis_image,hb i] at hi
    exact not_iff_not.mp hi
  · simp only [mem_vectorBases,hc,false_and]

end Papers.RationalityTen.VectorBasisFamilies
