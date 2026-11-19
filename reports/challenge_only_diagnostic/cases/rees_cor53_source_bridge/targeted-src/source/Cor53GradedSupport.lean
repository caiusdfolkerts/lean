module
public import Cor53Data
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Classical MvPolynomial CategoryTheory
open scoped BigOperators
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace PalomarSublatticeCor53
universe u
variable {V k : Type u} [Field k] [Fintype V] [LinearOrder V]

private theorem coefficientMap_single (J : Ideal (MvPolynomial V k))
    (f : MvPolynomial V k) (hf : f ∈ J) (s p : ℕ)
    (a : Set.powersetCard V p) (x : ↥(J^s)) :
    coefficientMap J f hf s p (Finsupp.single a x) =
      Finsupp.single a (multiplication J f hf s x) := by
  simp [coefficientMap]

theorem coefficientMap_apply_val (J : Ideal (MvPolynomial V k))
    (f : MvPolynomial V k) (hf : f ∈ J) (s p : ℕ)
    (z : Koszul.Coordinates (J^s) p) (a : Set.powersetCard V p) :
    (coefficientMap J f hf s p z a).val = f*(z a).val := by
  simp [coefficientMap,multiplication]

private theorem differential_single (I : Ideal (MvPolynomial V k)) (p : ℕ)
    (a : Set.powersetCard V (p+1)) (x : I) :
    Koszul.differential I p (Finsupp.single a x) =
      ∑ j : {j // j ∈ a.val}, Finsupp.single (Koszul.eraseIndex a j)
        ((X j.val * (((Koszul.eraseSign j.val a.val : ℤˣ) : ℤ) : MvPolynomial V k)) • x) := by
  simp only [Koszul.differential,LinearMap.restrictScalars_apply,Finsupp.lsum_single,
    LinearMap.sum_apply,LinearMap.comp_apply,Finsupp.lsingle_apply,LinearMap.lsmul_apply]

/-- The actual coefficient multiplier commutes with the deletion differential. -/
private theorem coefficientMap_differential (J : Ideal (MvPolynomial V k))
    (f : MvPolynomial V k) (hf : f ∈ J) (s p : ℕ)
    (z : Koszul.Coordinates (J^s) (p+1)) :
    coefficientMap J f hf s p (Koszul.differential (J^s) p z) =
      Koszul.differential (J^(s+1)) p (coefficientMap J f hf s (p+1) z) := by
  have h : (coefficientMap J f hf s p).comp (Koszul.differential (J^s) p) =
      (Koszul.differential (J^(s+1)) p).comp (coefficientMap J f hf s (p+1)) := by
    apply Finsupp.lhom_ext
    intro a x
    simp only [LinearMap.comp_apply,coefficientMap_single,differential_single,map_sum]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    exact (multiplication J f hf s).hom.map_smul _ x
  exact LinearMap.congr_fun h z

private theorem coefficientMap_previous (J : Ideal (MvPolynomial V k))
    (f : MvPolynomial V k) (hf : f ∈ J) (s p : ℕ)
    (z : Koszul.Coordinates (J^s) p) :
    coefficientMap J f hf s p.pred (Koszul.previous (J^s) p z) =
      Koszul.previous (J^(s+1)) p (coefficientMap J f hf s p z) := by
  cases p with
  | zero => simp only [Koszul.previous,LinearMap.zero_apply,map_zero]
  | succ p => exact coefficientMap_differential J f hf s p z

private theorem homogeneous_nat_to_int (f : MvPolynomial V k) (d : ℕ)
    (hf : f.IsWeightedHomogeneous (fun _ : V => (1 : ℕ)) d) :
    f.IsWeightedHomogeneous (fun _ : V => (1 : ℤ)) (d : ℤ) := by
  intro a ha
  have he : Finsupp.weight (fun _ : V => (1 : ℤ)) a =
      (Finsupp.weight (fun _ : V => (1 : ℕ)) a : ℤ) := by
    simp only [Finsupp.weight_apply,Finsupp.sum,nsmul_eq_mul,mul_one,Nat.cast_sum,Nat.cast_id]
  rw [he,hf ha]

private theorem coefficientMap_piece (J : Ideal (MvPolynomial V k))
    (f : MvPolynomial V k) (hf : f ∈ J) (d : ℕ)
    (hhom : f.IsWeightedHomogeneous (fun _ : V => (1 : ℕ)) d)
    (s p : ℕ) (q : ℤ) (z : Koszul.Coordinates (J^s) p)
    (hz : z ∈ Koszul.piece (J^s) q p) :
    coefficientMap J f hf s p z ∈ Koszul.piece (J^(s+1)) (q+(d : ℤ)) p := by
  simp only [Koszul.piece,Submodule.mem_iInf,Submodule.mem_comap] at hz ⊢
  intro a
  have ha := hz a
  change (z a).val.IsWeightedHomogeneous (fun _ : V => (1 : ℤ)) (q-(p : ℤ)) at ha
  change (coefficientMap J f hf s p z a).val.IsWeightedHomogeneous
    (fun _ : V => (1 : ℤ)) ((q+(d : ℤ))-(p : ℤ))
  rw [coefficientMap_apply_val]
  convert (homogeneous_nat_to_int f d hhom).mul ha using 1; omega

theorem multiplication_cycles (J : Ideal (MvPolynomial V k)) (f : MvPolynomial V k)
    (hf : f ∈ J) (d : ℕ)
    (hhom : f.IsWeightedHomogeneous (fun _ : V => (1 : ℕ)) d)
    (s p : ℕ) (q : ℤ) (z : Koszul.cycles (J^s) q p) :
    coefficientMap J f hf s p z.val ∈ Koszul.cycles (J^(s+1)) (q+(d : ℤ)) p := by
  refine ⟨?_,coefficientMap_piece J f hf d hhom s p q z.val z.property.2⟩
  change Koszul.previous (J^(s+1)) p (coefficientMap J f hf s p z.val)=0
  rw [← coefficientMap_previous,show Koszul.previous (J^s) p z.val=0 from z.property.1,map_zero]

/-- The induced linear map on the actual homogeneous cycles. -/
def cyclesMap (J : Ideal (MvPolynomial V k)) (f : MvPolynomial V k)
    (hf : f ∈ J) (d : ℕ)
    (hhom : f.IsWeightedHomogeneous (fun _ : V => (1 : ℕ)) d)
    (s p : ℕ) (q : ℤ) :
    Koszul.cycles (J^s) q p →ₗ[k] Koszul.cycles (J^(s+1)) (q+(d : ℤ)) p :=
  ((coefficientMap J f hf s p).domRestrict _).codRestrict _
    (fun z => multiplication_cycles J f hf d hhom s p q z)

theorem multiplication_boundaries (J : Ideal (MvPolynomial V k)) (f : MvPolynomial V k)
    (hf : f ∈ J) (d : ℕ)
    (hhom : f.IsWeightedHomogeneous (fun _ : V => (1 : ℕ)) d)
    (s p : ℕ) (q : ℤ) :
    Koszul.boundaries (J^s) q p ≤
      (Koszul.boundaries (J^(s+1)) (q+(d : ℤ)) p).comap
        (cyclesMap J f hf d hhom s p q) := by
  intro z hz
  change z.val ∈ Submodule.map (Koszul.differential (J^s) p)
    (Koszul.piece (J^s) q (p+1)) at hz
  obtain ⟨w,hw,hwz⟩ := hz
  change coefficientMap J f hf s p z.val ∈
    Submodule.map (Koszul.differential (J^(s+1)) p)
      (Koszul.piece (J^(s+1)) (q+(d : ℤ)) (p+1))
  refine ⟨coefficientMap J f hf s (p+1) w,
    coefficientMap_piece J f hf d hhom s (p+1) q w hw,?_⟩
  rw [← coefficientMap_differential,hwz]

/-- The literal induced map on the genuine degree-q Koszul homology quotient.
Its target degree is q+d for every signed integer q. -/
def homologyMap (J : Ideal (MvPolynomial V k)) (f : MvPolynomial V k)
    (hf : f ∈ J) (d : ℕ)
    (hhom : f.IsWeightedHomogeneous (fun _ : V => (1 : ℕ)) d)
    (s p : ℕ) (q : ℤ) :
    Koszul.Homology (J^s) q p →ₗ[k] Koszul.Homology (J^(s+1)) (q+(d : ℤ)) p :=
  (Koszul.boundaries (J^s) q p).mapQ
    (Koszul.boundaries (J^(s+1)) (q+(d : ℤ)) p)
    (cyclesMap J f hf d hhom s p q) (multiplication_boundaries J f hf d hhom s p q)

/-- Actual boundary reflection is the exact quotient-injectivity criterion. -/
theorem homologyMap_injective_of_boundary_reflection
    (J : Ideal (MvPolynomial V k)) (f : MvPolynomial V k) (hf : f ∈ J) (d : ℕ)
    (hhom : f.IsWeightedHomogeneous (fun _ : V => (1 : ℕ)) d)
    (s p : ℕ) (q : ℤ)
    (h : ∀ z : Koszul.cycles (J^s) q p,
      cyclesMap J f hf d hhom s p q z ∈ Koszul.boundaries (J^(s+1)) (q+(d : ℤ)) p →
        z ∈ Koszul.boundaries (J^s) q p) :
    Function.Injective (homologyMap J f hf d hhom s p q) := by
  apply LinearMap.ker_eq_bot.mp
  rw [homologyMap,Submodule.ker_mapQ]
  apply le_antisymm
  · rintro z ⟨x,hx,rfl⟩
    change (Koszul.boundaries (J^s) q p).mkQ x=0
    rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
    exact h x hx
  · exact bot_le

end PalomarSublatticeCor53
