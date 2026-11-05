module
public import PaperVerification.TriangularMinimum
public import PaperVerification.TriangularDepthSum
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

abbrev TriTriple := Fin 3 → TriPoint
abbrev E6Index := ZMod 3 × (Fin 3 → EisInt)

def l6Point (p : E6Index) : TriTriple :=
  fun i ↦ eisEmbed (p.2 i)+(p.1.val : ℝ)•triC

def l6Set : Set TriTriple := Set.range l6Point

def triTripleSqDist (z w : TriTriple) : ℝ := ∑ i, triQ (z i-w i)

def l6Gaussian (α : ℝ) (z : TriTriple) : ℝ :=
  ∑' p : E6Index, Real.exp (-α*triTripleSqDist (l6Point p) z)

def l6Depth (z : TriTriple) : ℝ :=
  sInf (Set.range fun p : E6Index ↦ triTripleSqDist (l6Point p) z)

def IsL6ColdSpot (α : ℝ) (z : TriTriple) : Prop := ∀ w, l6Gaussian α z ≤ l6Gaussian α w

def IsL6DeepHole (z : TriTriple) : Prop := ∀ w, l6Depth w ≤ l6Depth z

theorem l6Point_injective : Function.Injective l6Point := by
  intro p q h
  have h0 := congrArg Prod.fst (congrFun h 0)
  change ((p.2 0).1 : ℝ)+(p.1.val : ℝ)*(1/3) =
    ((q.2 0).1 : ℝ)+(q.1.val : ℝ)*(1/3) at h0
  have hi : (3:ℤ)*((p.2 0).1-(q.2 0).1) = (q.1.val : ℤ)-(p.1.val : ℤ) := by
    apply Int.cast_injective (α:=ℝ)
    push_cast
    linarith
  have hr0 := congrArg (fun k : ℤ ↦ (k : ZMod 3)) hi
  simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_sub, Int.cast_natCast,
    ZMod.natCast_zmod_val, zmodThree_three_eq_zero, zero_mul] at hr0
  have hr : p.1=q.1 := by linear_combination hr0
  apply Prod.ext hr
  funext i
  apply eisEmbed_injective
  have hh := congrFun h i
  change eisEmbed (p.2 i)+(p.1.val : ℝ)•triC=eisEmbed (q.2 i)+(q.1.val : ℝ)•triC at hh
  rw [hr] at hh
  exact add_right_cancel hh

def l6Equiv : E6Index ≃ l6Set := Equiv.ofInjective l6Point l6Point_injective

theorem l6Set_iff_integer_glue (z : TriTriple) : z ∈ l6Set ↔
    ∃ m : Fin 3 → EisInt, ∃ k : ℤ, ∀ i, z i=eisEmbed (m i)+(k : ℝ)•triC := by
  constructor
  · rintro ⟨⟨r,m⟩,rfl⟩
    exact ⟨m,(r.val : ℤ),fun _ ↦ rfl⟩
  · rintro ⟨m,k,h⟩
    let r : ZMod 3 := k
    let q : ℤ := k/3
    have hk : k=(r.val : ℤ)+3*q := by
      have hr : (r.val : ℤ)=k%3 := by
        simpa [r] using (ZMod.val_intCast (n:=3) k)
      dsimp [q]
      omega
    refine ⟨(r,fun i ↦ m i+q•(1,-1)),?_⟩
    funext i
    rw [h i]
    dsimp [l6Point]
    rw [map_add]
    have hkr : (k:ℝ)=(r.val:ℝ)+3*(q:ℝ) := by exact_mod_cast hk
    ext <;> dsimp [triC,eisEmbed] <;> push_cast <;> rw [hkr] <;> ring

theorem l6Gaussian_actual_set (α : ℝ) (z : TriTriple) :
    l6Gaussian α z = ∑' p : l6Set, Real.exp (-α*triTripleSqDist p.val z) :=
  l6Equiv.tsum_eq (fun p : l6Set ↦ Real.exp (-α*triTripleSqDist p.val z))

theorem l6Depth_actual_set (z : TriTriple) :
    l6Depth z = sInf ((fun p ↦ triTripleSqDist p z) '' l6Set) := by
  unfold l6Depth l6Set
  exact congrArg sInf (Set.range_comp' (fun p : TriTriple ↦ triTripleSqDist p z) l6Point)

theorem l6_term_factor (α : ℝ) (z : TriTriple) (r : ZMod 3) (m : Fin 3 → EisInt) :
    Real.exp (-α*triTripleSqDist (l6Point (r,m)) z) =
      ∏ i, Real.exp (-α*triQ (eisEmbed (m i)-(z i-(r.val : ℝ)•triC))) := by
  unfold triTripleSqDist
  rw [Finset.mul_sum,Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i hi
  have hpoint : l6Point (r,m) i-z i =
      eisEmbed (m i)-(z i-(r.val : ℝ)•triC) := by
    dsimp only [l6Point]
    abel
  exact congrArg (fun v : TriPoint ↦ Real.exp (-α*triQ v)) hpoint

theorem summable_l6Gaussian {α : ℝ} (hα : 0 < α) (z : TriTriple) :
    Summable (fun p : E6Index ↦ Real.exp (-α*triTripleSqDist (l6Point p) z)) := by
  apply (summable_prod_of_nonneg (fun _ ↦ (Real.exp_pos _).le)).mpr
  refine ⟨?_,Summable.of_finite⟩
  intro r
  simp only [l6_term_factor]
  exact summable_fin_product 3
    (fun i m ↦ Real.exp (-α*triQ (eisEmbed m-(z i-(r.val : ℝ)•triC))))
    (fun i ↦ summable_triangularGaussian hα (z i-(r.val : ℝ)•triC))

theorem l6Gaussian_cosets {α : ℝ} (hα : 0 < α) (z : TriTriple) :
    l6Gaussian α z = ∑ r : ZMod 3, ∏ i, triangularGaussian α (z i-(r.val : ℝ)•triC) := by
  unfold l6Gaussian
  rw [(summable_l6Gaussian hα z).tsum_prod,tsum_fintype]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [l6_term_factor]
  exact tsum_fin_product 3
    (fun i m ↦ Real.exp (-α*triQ (eisEmbed m-(z i-(r.val : ℝ)•triC))))
    (fun i ↦ summable_triangularGaussian hα (z i-(r.val : ℝ)•triC))

theorem l6Depth_nonneg (z : TriTriple) : 0 ≤ l6Depth z := by
  apply le_csInf (Set.range_nonempty _)
  rintro t ⟨p,rfl⟩
  exact Finset.sum_nonneg (fun i hi ↦ triQ_nonneg _)

theorem l6Depth_le (z : TriTriple) (p : E6Index) :
    l6Depth z ≤ triTripleSqDist (l6Point p) z :=
  csInf_le ⟨0,by rintro t ⟨q,rfl⟩; exact Finset.sum_nonneg (fun i hi ↦ triQ_nonneg _)⟩
    (Set.mem_range_self p)

def l6CosetDepth (z : TriTriple) (r : ZMod 3) : ℝ :=
  ∑ i, triangularDepth (z i-(r.val : ℝ)•triC)

theorem l6Depth_le_cosetDepth (z : TriTriple) (r : ZMod 3) : l6Depth z ≤ l6CosetDepth z r := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have he : 0 < ε/3 := by positivity
  have hex (i : Fin 3) : ∃ m : EisInt,
      triQ (eisEmbed m-(z i-(r.val : ℝ)•triC)) < triangularDepth (z i-(r.val : ℝ)•triC)+ε/3 := by
    obtain ⟨a,⟨m,rfl⟩,hm⟩ := exists_lt_of_csInf_lt
      (Set.range_nonempty (fun m : EisInt ↦ triQ (eisEmbed m-(z i-(r.val : ℝ)•triC))))
      (lt_add_of_pos_right (triangularDepth (z i-(r.val : ℝ)•triC)) he)
    exact ⟨m,hm⟩
  choose m hm using hex
  have h := l6Depth_le z (r,m)
  have heq : triTripleSqDist (l6Point (r,m)) z =
      ∑ i, triQ (eisEmbed (m i)-(z i-(r.val : ℝ)•triC)) := by
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    dsimp [l6Point]
    abel
  rw [heq] at h
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) ↦ (hm i).le)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul] at hs
  unfold l6CosetDepth
  linarith

end PaperVerification.ColdSpots
