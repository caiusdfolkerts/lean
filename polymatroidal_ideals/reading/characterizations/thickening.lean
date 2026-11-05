import Characterizations.CoordinatePrime
import Characterizations.FiniteHoles

/-! # Multiplication by every power of the homogeneous maximal ideal -/
noncomputable section
namespace Characterizations
open Classical CommAlg CommAlg.Polymatroid Finset MvPolynomial
variable {V : Type*} [Fintype V] [DecidableEq V]

def degreeFamily (q : ℕ) : Family V := (Finsupp.finite_of_degree_eq (σ := V) q).toFinset

@[simp] theorem mem_degreeFamily (q : ℕ) (a : Exponent V) : a ∈ degreeFamily q ↔ a.degree = q := by
  simp [degreeFamily]

def thickening (B : Family V) (q : ℕ) : Family V :=
  (B.product (degreeFamily q)).image (fun bc => bc.1 + bc.2)

theorem thickening_equigenerated {B : Family V} {d : ℕ} (hd : Equigenerated B d) (q : ℕ) :
    Equigenerated (thickening B q) (d + q) := by
  intro a ha
  obtain ⟨⟨b,c⟩, hbc, rfl⟩ := mem_image.mp ha
  obtain ⟨hb,hc⟩ := mem_product.mp hbc
  simp only [map_add, hd b hb, (mem_degreeFamily q c).mp hc]

theorem contains_thickening_iff {B : Family V} {d : ℕ} (hd : Equigenerated B d)
    (q : ℕ) (a : Exponent V) :
    Contains (thickening B q) a ↔ Contains B a ∧ d + q ≤ a.degree := by
  constructor
  · rintro ⟨w, hw, hwa⟩
    obtain ⟨⟨b,c⟩, hbc, rfl⟩ := mem_image.mp hw
    obtain ⟨hb,hc⟩ := mem_product.mp hbc
    refine ⟨⟨b,hb,(le_add_right le_rfl).trans hwa⟩, ?_⟩
    have h := degree_mono hwa
    simpa only [map_add, hd b hb, (mem_degreeFamily q c).mp hc] using h
  · rintro ⟨⟨b,hb,hba⟩, hdeg⟩
    have hdiff : q ≤ (a-b).degree := by
      have h := congrArg Finsupp.degree (tsub_add_cancel_of_le hba)
      simp only [map_add, hd b hb] at h
      omega
    obtain ⟨c,hc,hcd⟩ := Finsupp.exists_le_degree_eq (a-b) q hdiff
    refine ⟨b+c, mem_image.mpr ⟨(b,c), mem_product.mpr ⟨hb,(mem_degreeFamily q c).mpr hcd⟩,rfl⟩, ?_⟩
    calc
      b+c ≤ b+(a-b) := add_le_add le_rfl hc
      _ = a := by rw [add_comm, tsub_add_cancel_of_le hba]

theorem thickening_mono {B C : Family V} (h : B ⊆ C) (q : ℕ) :
    thickening B q ⊆ thickening C q := by
  intro a ha
  obtain ⟨⟨b,c⟩,hbc,rfl⟩ := mem_image.mp ha
  exact mem_image.mpr ⟨(b,c),mem_product.mpr ⟨h (mem_product.mp hbc).1,(mem_product.mp hbc).2⟩,rfl⟩

theorem thickening_nonempty [Nonempty V] {B : Family V} (hB : B.Nonempty) (q : ℕ) :
    (thickening B q).Nonempty := by
  obtain ⟨b,hb⟩ := hB
  obtain ⟨i⟩ := ‹Nonempty V›
  exact ⟨b+Finsupp.single i q,mem_image.mpr ⟨(b,Finsupp.single i q),
    mem_product.mpr ⟨hb,by simp⟩,rfl⟩⟩

def raisedTopRank (r : Finset V → ℕ) (q : ℕ) (U : Finset V) : ℕ :=
  if U = Finset.univ then r U + q else r U

theorem raisedTopRank_supermodular {r : Finset V → ℕ} (hr : Supermodular r) (q : ℕ) :
    Supermodular (raisedTopRank r q) := by
  intro A C
  by_cases hA : A = Finset.univ
  · subst A
    have hu : (Finset.univ : Finset V) ∪ C = Finset.univ :=
      Finset.Subset.antisymm (Finset.subset_univ _) Finset.subset_union_left
    rw [hu]
    simp
  by_cases hC : C = Finset.univ
  · subst C
    have hu : A ∪ (Finset.univ : Finset V) = Finset.univ :=
      Finset.Subset.antisymm (Finset.subset_univ _) Finset.subset_union_right
    rw [hu]
    simp [add_comm]
  have h := hr A C
  have hle (U : Finset V) : r U ≤ raisedTopRank r q U := by
    unfold raisedTopRank; split_ifs <;> omega
  have hU := hle (A ∪ C)
  have hI := hle (A ∩ C)
  simp only [raisedTopRank, if_neg hA, if_neg hC]
  change r A + r C ≤ raisedTopRank r q (A ∪ C) + raisedTopRank r q (A ∩ C)
  omega

theorem raisedTopRank_feasible_iff {r : Finset V → ℕ} (q : ℕ) (a : Exponent V) :
    LowerFeasible (raisedTopRank r q) a ↔ LowerFeasible r a ∧ r Finset.univ + q ≤ a.degree := by
  constructor
  · intro h
    refine ⟨fun U => ?_, ?_⟩
    · have hh := h U
      unfold raisedTopRank at hh
      split_ifs at hh <;> omega
    · simpa [raisedTopRank] using h Finset.univ
  · rintro ⟨h,hdeg⟩ U
    by_cases hU : U = Finset.univ
    · subst U; simpa [raisedTopRank] using hdeg
    · simpa only [raisedTopRank, if_neg hU] using h U

theorem thickening_polymatroidal {B : Family V} (hB : B.Nonempty)
    (hp : IsPolymatroidal B) (q : ℕ) : IsPolymatroidal (thickening B q) := by
  obtain ⟨d,hd⟩ := hp.1
  have hr := lowerRank_supermodular hB (polymatroidal_locallyEquigenerated hp)
  apply polymatroidal_of_lower_inequalities (thickening_equigenerated hd q)
    (raisedTopRank_supermodular hr q)
  intro a
  rw [contains_thickening_iff hd, contains_iff_canonical_lower B hB d hd hp,
    raisedTopRank_feasible_iff, lowerRank_univ_of_equigenerated hB hd]

variable (k : Type*) [CommRing k]

theorem degreeFamily_ideal_eq_maximal_pow (q : ℕ) :
    monomialIdeal k (degreeFamily (V := V) q) = (coordinatePrime k Finset.univ) ^ q := by
  ext f
  rw [mem_monomialIdeal_iff, mem_coordinatePrime_pow_iff]
  apply forall₂_congr
  intro a ha
  simp only [subsetSum_univ]
  constructor
  · rintro ⟨b,hb,hba⟩
    exact ((mem_degreeFamily q b).mp hb).symm.le.trans (degree_mono hba)
  · intro h
    obtain ⟨b,hba,hbd⟩ := Finsupp.exists_le_degree_eq a q h
    exact ⟨b,(mem_degreeFamily q b).mpr hbd,hba⟩

theorem thickening_ideal_eq (B : Family V) (q : ℕ) :
    monomialIdeal k (thickening B q) = (coordinatePrime k Finset.univ) ^ q * monomialIdeal k B := by
  rw [← degreeFamily_ideal_eq_maximal_pow, mul_comm, monomialIdeal_mul]
  rfl

end Characterizations
