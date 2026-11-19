module

public import Papers.GraphicalZonotopes.TwoHubFunctions

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H J : Type*} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]

theorem assembled_hub_cover (z : SetFunction H) (F : J → SetFunction H)
    (w : J → ℝ) (v : H) (X : Finset H) (Y : Finset J) :
    assembled z F w (context (insert v X) Y)-assembled z F w (context X Y)=
      z (insert v X)-z X+∑ j∈Y,w j*(F j (insert v X)-F j X) := by
  rw [assembled_context,assembled_context]
  simp only [mul_sub,Finset.sum_sub_distrib]
  ring

theorem context_insert_hub (X : Finset H) (Y : Finset J) (v : H) :
    context (insert v X) Y=insert (Sum.inl v) (context X Y) := by
  ext x
  cases x <;> simp

end BooleanModule

namespace TwoHub
open Finset BooleanModule
open scoped BigOperators Pointwise
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem module_a_zero_cover (ε Y : Finset I) :
    moduleFunction ε (context {false} Y)-moduleFunction ε (context ∅ Y)=
      eta ε+∑ i∈Y,if i∈ε then (1 : ℝ) else 0 := by
  have hh := assembled_hub_cover (central ε) (fun i => corner (decide (i∈ε)))
    (fun _ => 1) false ∅ Y
  simp only [insert_empty_eq] at hh
  simp only [moduleFunction]
  rw [hh]
  simp only [central,pair_false,pair_empty,sub_zero,corner_false,corner_empty,one_mul]
  congr 1
  apply sum_congr rfl
  intro i hi
  by_cases he : i∈ε <;> simp [he]

theorem module_a_one_cover (ε Y : Finset I) :
    moduleFunction ε (context univ Y)-moduleFunction ε (context {true} Y)=
      eta ε+(ε.card : ℝ)-1+∑ i∈Y,if i∈ε then (0 : ℝ) else 1 := by
  have hb : insert false ({true} : Finset Bool)=univ := by decide
  have hh := assembled_hub_cover (central ε) (fun i => corner (decide (i∈ε)))
      (fun _ => 1) false {true} Y
  rw [hb] at hh
  simp only [moduleFunction]
  rw [hh]
  simp only [central,pair_full,pair_true,corner_full,corner_true,one_mul]
  have hs : (∑ i∈Y,(1-(if decide (i∈ε) then (1 : ℝ) else 0)))=
      ∑ i∈Y,if i∈ε then (0 : ℝ) else 1 := by
    apply sum_congr rfl
    intro i hi
    by_cases he : i∈ε <;> simp [he]
  rw [hs]
  ring

theorem module_b_zero_cover (ε Y : Finset I) :
    moduleFunction ε (context {true} Y)-moduleFunction ε (context ∅ Y)=
      (Fintype.card I : ℝ)-(ε.card : ℝ)+∑ i∈Y,if i∈ε then (1 : ℝ) else -1 := by
  have hh := assembled_hub_cover (central ε) (fun i => corner (decide (i∈ε)))
      (fun _ => 1) true ∅ Y
  simp only [insert_empty_eq] at hh
  simp only [moduleFunction]
  rw [hh]
  simp only [central,pair_true,pair_empty,sub_zero,corner_true,corner_empty,one_mul]
  congr 1
  apply sum_congr rfl
  intro i hi
  by_cases he : i∈ε <;> simp [he]

theorem module_b_one_cover (ε Y : Finset I) :
    moduleFunction ε (context univ Y)-moduleFunction ε (context {false} Y)=
      (Fintype.card I : ℝ)-1 := by
  have hb : insert true ({false} : Finset Bool)=univ := by decide
  have hh := assembled_hub_cover (central ε) (fun i => corner (decide (i∈ε)))
      (fun _ => 1) true {false} Y
  rw [hb] at hh
  simp only [moduleFunction]
  rw [hh]
  simp only [central,pair_full,pair_false,corner_full,corner_false,sub_self,mul_zero,sum_const_zero,add_zero]
  ring

theorem module_b_complement_zero (ε : Finset I) :
    moduleFunction ε (context {true} (univ\ε))-
      moduleFunction ε (context ∅ (univ\ε))=0 := by
  rw [module_b_zero_cover]
  have hs : (∑ i∈univ\ε,if i∈ε then (1 : ℝ) else -1)=
      -(Fintype.card I : ℝ)+(ε.card : ℝ) := by
    calc
      _ = ∑ _i∈univ\ε,(-1 : ℝ) := by
        apply sum_congr rfl
        intro i hi
        rw [if_neg (mem_sdiff.mp hi).2]
      _ = -((Fintype.card I-ε.card : ℕ) : ℝ) := by
        simp [card_sdiff_of_subset (subset_univ ε)]
      _ = _ := by rw [Nat.cast_sub (card_le_univ ε)]; ring
  rw [hs]
  ring

theorem private_corner_of_tight (ε : Finset I) (f : SetFunction (Hub I))
    (hcover : ∀ v X,v∉X → moduleFunction ε (insert v X)-moduleFunction ε X=0 →
      f (insert v X)-f X=0)
    (hdelta : ∀ v w,v≠w → ∀ X,v∉X → w∉X →
      delta (moduleFunction ε) v w X=0 → delta f v w X=0)
    (i : I) : ∃ c : ℝ,privateSlice f i=c • corner (decide (i∈ε)) := by
  apply corner_private_line
  · have hh:=hcover (u i) (hubSet (if decide (i∈ε) then ∅ else {true}))
      (notMem_hubSet_outer _ i)
    have hz : moduleFunction ε (insert (u i) (hubSet (if decide (i∈ε) then ∅ else {true})))-
        moduleFunction ε (hubSet (if decide (i∈ε) then ∅ else {true}))=0 := by
      rw [module_spoke]
      by_cases hi : i∈ε <;> simp [hi,corner]
    exact hh hz
  · have hh := hdelta a (u i) (by simp [a,u])
      (hubSet (if decide (i∈ε) then {true} else ∅))
      (by by_cases hi : i∈ε <;> simp [a,hi])
      (notMem_hubSet_outer _ i)
    have hz : delta (moduleFunction ε) a (u i)
        (hubSet (if decide (i∈ε) then {true} else ∅))=0 := by
      rw [a,module_hub_spoke]
      by_cases hi : i∈ε <;> simp [hi,corner]
    have h:=hh hz
    rw [a,u,← privateSlice_cover] at h
    by_cases hi : i∈ε
    · have hu : insert false ({true} : Finset Bool)=univ := by decide
      simpa [hi,hu] using sub_eq_zero.mp h
    · simpa [hi] using sub_eq_zero.mp h
  · have hh := hdelta b (u i) (by simp [b,u]) (hubSet {false})
      (by simp [b]) (notMem_hubSet_outer _ i)
    have hz : delta (moduleFunction ε) b (u i) (hubSet {false})=0 := by
      rw [b,module_hub_spoke]
      simp [corner]
    have h:=hh hz
    rw [b,u,← privateSlice_cover] at h
    have hu : insert true ({false} : Finset Bool)=univ := by decide
    rw [hu] at h
    exact sub_eq_zero.mp h

theorem delta_weighted_corners (h : SetFunction Bool) (ε Y : Finset I) (γ : I → ℝ) :
    delta (assembled h (fun i => corner (decide (i∈ε))) γ) a b (outerSet Y)=
      delta h false true ∅+∑ i∈Y,if i∈ε then -γ i else γ i := by
  rw [a,b,delta_assembled_hubs]
  have hh : hubs (outerSet (H:=Bool) Y)=∅ := by ext v; simp
  rw [hh]
  simp only [mem_outerSet_outer,delta_corner]
  have hs : (∑ i : I,γ i*(if i∈Y then (if decide (i∈ε) then (-1 : ℝ) else 1) else 0))=
      ∑ i∈Y,if i∈ε then -γ i else γ i := by
    simp only [mul_ite,mul_zero,mul_neg,mul_one]
    rw [←sum_filter]
    have hY : (univ.filter (fun i => i∈Y))=Y := by ext i; simp
    rw [hY]
    apply sum_congr rfl
    intro i hi
    simp
  rw [hs]

theorem module_private_rigid [Nonempty I] (ε : Finset I) : PrivateRigid (moduleFunction ε) := by
  intro f hf hcover hdelta
  have hout : OuterZero f := by
    intro i j hij X hi hj
    exact hdelta (Sum.inr i) (Sum.inr j) (by simpa using hij) X hi hj
      (module_outer_zero ε i j hij X hi hj)
  choose γ hγ using private_corner_of_tight ε f hcover hdelta
  have hrep := eq_assembled_of_privateSlices hout
    (fun i => corner (decide (i∈ε))) γ hγ
  let h:=boundarySlice f
  have hh0 : h ∅=0 := by simpa [h,boundarySlice] using hf
  have hscale (j : I) : delta h false true ∅-(∑ i∈ε,γ i)+γ j=0 := by
    have hz := hdelta a b (by simp [a,b]) (outerSet (neighbor ε j))
      (by simp [a]) (by simp [b]) (module_ab_neighbor ε j)
    rw [hrep,delta_weighted_corners,signed_sum_neighbor] at hz
    dsimp [h]
    linarith
  let j₀ : I:=Classical.choice ‹Nonempty I›
  let c:=γ j₀
  have hγc (j : I) : γ j=c := by
    have h1:=hscale j
    have h2:=hscale j₀
    dsimp [c]
    linarith
  have hC : delta h false true ∅=((ε.card : ℝ)-1)*c := by
    have he:=hscale j₀
    simp_rw [hγc] at he
    simp only [sum_const,nsmul_eq_mul] at he
    linarith
  have hB : h {true}=((Fintype.card I : ℝ)-(ε.card : ℝ))*c := by
    have hz := hcover b (context ∅ (univ\ε)) (by simp [b]) (by
      rw [b,←context_insert_hub,insert_empty_eq]
      exact module_b_complement_zero ε)
    rw [hrep,b,←context_insert_hub,assembled_hub_cover] at hz
    have hS : (∑ i∈univ\ε,γ i*(corner (decide (i∈ε)) (insert true ∅)-
        corner (decide (i∈ε)) ∅))= -((Fintype.card I : ℝ)-(ε.card : ℝ))*c := by
      calc
        _ = ∑ _i∈univ\ε,-c := by
          apply sum_congr rfl
          intro i hi
          simp [(mem_sdiff.mp hi).2,hγc i,corner]
        _ = _ := by
          simp [card_sdiff_of_subset (subset_univ ε),Nat.cast_sub (card_le_univ ε)] <;> ring
    rw [hS] at hz
    change h {true}-h ∅+ -((Fintype.card I : ℝ)-(ε.card : ℝ))*c=0 at hz
    rw [hh0] at hz
    linarith
  have hA : h {false}=eta ε*c := by
    by_cases he : ε=∅
    · have hz := hcover a (context {true} (∅ : Finset I)) (by simp [a]) (by
        rw [a,←context_insert_hub]
        have hu : insert false ({true} : Finset Bool)=univ := by decide
        rw [hu,module_a_one_cover]
        simp [he,eta])
      rw [hrep,a,←context_insert_hub,assembled_hub_cover] at hz
      have hu : insert false ({true} : Finset Bool)=univ := by decide
      simp only [hu,sum_empty,add_zero] at hz
      change h univ-h {true}=0 at hz
      have hCab : delta h false true ∅=h univ-h {false}-h {true}+h ∅ := by
        simp only [delta,insert_empty_eq,hu]
      rw [hCab,hh0,he,card_empty,Nat.cast_zero] at hC
      simp only [eta,he,ite_true,one_mul]
      linarith
    · have hz := hcover a (context ∅ (∅ : Finset I)) (by simp [a]) (by
        rw [a,←context_insert_hub]
        simpa [eta,he] using module_a_zero_cover ε (∅ : Finset I))
      rw [hrep,a,←context_insert_hub,assembled_hub_cover] at hz
      change h {false}-h ∅+0=0 at hz
      rw [hh0] at hz
      simp only [eta,if_neg he,zero_mul]
      linarith
  have hcentral : h=c • central ε := by
    rw [eq_pair h hh0]
    apply bool_set_ext
    · simp [central]
    · simp [central,hA,mul_comm]
    · simp [central,hB,mul_comm]
    · have hCab : delta h false true ∅=h univ-h {false}-h {true}+h ∅ := by
        have hu : insert false ({true} : Finset Bool)=univ := by decide
        simp only [delta,insert_empty_eq,hu]
      rw [hCab,hh0] at hC
      simp only [pair_full,Pi.smul_apply,smul_eq_mul,central]
      nlinarith [hA,hB]
  refine ⟨c,?_⟩
  rw [hrep]
  change assembled h _ γ=c • moduleFunction ε
  have hg : γ=c • (fun _ : I => (1 : ℝ)) := by
    funext i
    simp [hγc i]
  rw [hcentral,hg,assembled_smul]
  rfl

end TwoHub
end GraphicalZonotopes
