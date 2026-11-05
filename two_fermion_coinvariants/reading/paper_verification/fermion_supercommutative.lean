module

public import PaperVerification.FermionExteriorMultigrading
public import PaperVerification.FermionGradedTensorQuotient

/-!
# Supercommutativity of the actual exterior quotient gradings

The sign law is proved on multilinear exterior products, extended by linear
span, and then passed through the actual homogeneous quotient map.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical TensorProduct

namespace PaperVerification.Fermion

def IsSupercommutative {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (part : ℕ → Submodule R A) : Prop :=
  ∀ i j (a : part i) (b : part j),
    (a : A)*(b : A)=(-1 : ℤˣ)^(j*i) • ((b : A)*(a : A))

theorem exteriorPower_supercommutative {R M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] :
    IsSupercommutative (fun n : ℕ ↦ ⋀[R]^n M) := by
  intro i j a b
  have ha := a.property
  have hb := b.property
  dsimp only at ha hb
  have ha := (ExteriorAlgebra.ιMulti_span_fixedDegree R i).ge ha
  have hb := (ExteriorAlgebra.ιMulti_span_fixedDegree R j).ge hb
  refine Submodule.span_induction₂ (p := fun x y hx hy ↦
    x*y=(-1 : ℤˣ)^(j*i) • (y*x)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ha hb
  · rintro x y ⟨mx,rfl⟩ ⟨my,rfl⟩
    exact ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm R mx my
  all_goals simp +contextual [add_mul,mul_add,smul_mul_assoc,mul_smul_comm]
  all_goals
    intro r x y hx hy hxy
    rcases Int.units_eq_one_or ((-1 : ℤˣ)^(j*i)) with hs|hs <;>
      simp only [hs,Units.neg_smul,one_smul,smul_neg]

theorem exteriorTotalPart_eq_standard {A ι : Type*} [CommRing A]
    [Fintype ι] [LinearOrder (ι⊕ι)] :
    exteriorTotalPart (A := A) (ι := ι)=
      fun n : ℕ ↦ ⋀[A]^n ((ι⊕ι)→A) := by
  apply basisDegreePart_eq_existing
  intro T
  have h : exteriorWordDegree (fun _ : ι⊕ι ↦ (1:ℕ)) T=T.card := by
    simp [exteriorWordDegree]
  rw [h]
  rw [ExteriorAlgebra.basis_eq_coe_basis (Pi.basisFun A (ι⊕ι))
    (⟨T,rfl⟩ : Set.powersetCard (ι⊕ι) T.card)]
  exact ((Pi.basisFun A (ι⊕ι)).exteriorPower T.card ⟨T,rfl⟩).property

theorem exteriorTotalPart_supercommutative {A ι : Type*} [CommRing A]
    [Fintype ι] [LinearOrder (ι⊕ι)] :
    IsSupercommutative (exteriorTotalPart (A := A) (ι := ι)) := by
  rw [exteriorTotalPart_eq_standard]
  exact exteriorPower_supercommutative

theorem gradedImage_supercommutative {R A B : Type*} [CommRing R] [Ring A] [Ring B]
    [Algebra R A] [Algebra R B] (part : ℕ → Submodule R A)
    (q : A →ₐ[R] B) (h : IsSupercommutative part) :
    IsSupercommutative (gradedImagePart part q) := by
  intro i j a b
  obtain ⟨a,ha,hea⟩ := a.property
  obtain ⟨b,hb,heb⟩ := b.property
  change q a = _ at hea
  change q b = _ at heb
  rw [←hea,←heb,←map_mul,←map_mul,h i j ⟨a,ha⟩ ⟨b,hb⟩]
  exact AlgHom.map_smul_of_tower q _ _

theorem clusterOddTotalPart_supercommutative
    {A ι κ : Type*} [CommRing A] [Fintype ι] [Fintype κ]
    [LinearOrder (ι⊕ι)] (cluster : ι → κ) (z beta : ι → A) (r u v : ι → ℕ) :
    IsSupercommutative (clusterOddTotalPart cluster z beta r u v) :=
  gradedImage_supercommutative exteriorTotalPart
    ((clusterOddIdeal cluster z beta r u v).ringCon.mkₐ A)
    exteriorTotalPart_supercommutative

theorem supercommutative_degree_zero_central
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (part : ℕ → Submodule R A) [GradedAlgebra part]
    (h : IsSupercommutative part) {a : A} (ha : a∈part 0) (b : A) :
    Commute a b := by
  induction b using DirectSum.Decomposition.inductionOn part with
  | zero => exact Commute.zero_right a
  | add b c hb hc => exact hb.add_right hc
  | homogeneous b =>
      change a*(b:A)=(b:A)*a
      simpa only [Nat.mul_zero,pow_zero,one_smul] using h 0 _ ⟨a,ha⟩ b

theorem supercommutative_odd_square_zero
    {F A : Type*} [Field F] [CharZero F] [Ring A] [Algebra F A]
    (part : ℕ → Submodule F A) (h : IsSupercommutative part)
    {a : A} (ha : a∈part 1) : a*a=0 := by
  have he : a*a=-(a*a) := by
    simpa only [Nat.one_mul,pow_one,Units.neg_smul,one_smul] using h 1 1 ⟨a,ha⟩ ⟨a,ha⟩
  have hz : (2:F) • (a*a)=0 := by
    rw [show (2:F)=1+1 by norm_num,add_smul,one_smul]
    exact eq_neg_iff_add_eq_zero.mp he
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

end PaperVerification.Fermion

