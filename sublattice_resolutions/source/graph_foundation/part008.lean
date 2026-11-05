module
public import graph_foundation.part007

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.PowerWeightSpaces -/
section

set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)} {r s : ℕ}

def powerWeightedFaces (m : ℕ) (α : Exponent (FiniteVariable.{u} n))
    (R : ℕ → Prop) (F : Finset (FiniteVariable.{u} n)) : Prop :=
  ∃a : ChainFaceIndex n E m α,a.2.val=F ∧ R (finiteChainFactorWeight.{u} a.1.val)

def powerWeightedSpan (m : ℕ) (α : Exponent (FiniteVariable.{u} n)) (R : ℕ → Prop) :
    Submodule k (Simplicial.Ambient (FiniteVariable.{u} n) k) :=
  basisSpan Simplicial.basis (powerWeightedFaces (n := n) (E := E) m α R)

lemma powerWeightedSpan_mono (m : ℕ) (α : Exponent (FiniteVariable.{u} n))
    {R T : ℕ → Prop} (h : ∀a,R a→T a) :
    powerWeightedSpan (k := k) (E := E) m α R≤powerWeightedSpan (E := E) m α T := by
  apply Submodule.span_mono
  apply Set.image_mono
  rintro F ⟨a,ha,hw⟩
  exact ⟨a,ha,h _ hw⟩

lemma powerWeightedSpan_basis (α : Exponent (FiniteVariable.{u} n)) (R : ℕ → Prop)
    (a : ChainFaceIndex n E r α) (ha : R (finiteChainFactorWeight.{u} a.1.val)) :
    Simplicial.basis (k := k) a.2.val∈powerWeightedSpan (E := E) r α R :=
  Submodule.subset_span ⟨a.2.val,⟨a,rfl,ha⟩,rfl⟩

lemma powerWeightedSpan_mul (hE : finiteLatticeClosed n E)
    (α β : Exponent (FiniteVariable.{u} n)) (R S T : ℕ → Prop)
    (hbound : ∀a b c,R a→S b→c≤a+b→T c)
    {x y : Simplicial.Ambient (FiniteVariable.{u} n) k}
    (hx : x∈powerWeightedSpan (E := E) r α R)
    (hy : y∈powerWeightedSpan (E := E) s β S) :
    x*y∈powerWeightedSpan (E := E) (r+s) (α+β) T := by
  apply faceSpan_mul_mem _ _ _ _ hx hy
  rintro F ⟨a,rfl,ha⟩ G ⟨b,rfl,hb⟩ hab
  exact ⟨chainFaceProduct hE a b hab,(chainFaceProduct_face hE a b hab).trans
      (finsetUnion_decidableEq _ _ _ _),
    hbound _ _ _ ha hb (chainFaceProduct_factorWeight_le hE a b hab)⟩

lemma powerWeightedSpan_mul_le (hE : finiteLatticeClosed n E)
    (α β : Exponent (FiniteVariable.{u} n)) (A B : ℕ)
    {x y : Simplicial.Ambient (FiniteVariable.{u} n) k}
    (hx : x∈powerWeightedSpan (E := E) r α (fun a => a≤A))
    (hy : y∈powerWeightedSpan (E := E) s β (fun b => b≤B)) :
    x*y∈powerWeightedSpan (E := E) (r+s) (α+β) (fun c => c≤A+B) :=
  powerWeightedSpan_mul hE α β _ _ _ (by intros;omega) hx hy

lemma powerWeightedSpan_mul_lt_left (hE : finiteLatticeClosed n E)
    (α β : Exponent (FiniteVariable.{u} n)) (A B : ℕ)
    {x y : Simplicial.Ambient (FiniteVariable.{u} n) k}
    (hx : x∈powerWeightedSpan (E := E) r α (fun a => a<A))
    (hy : y∈powerWeightedSpan (E := E) s β (fun b => b≤B)) :
    x*y∈powerWeightedSpan (E := E) (r+s) (α+β) (fun c => c<A+B) :=
  powerWeightedSpan_mul hE α β _ _ _ (by intros;omega) hx hy

lemma powerWeightedSpan_mul_lt_right (hE : finiteLatticeClosed n E)
    (α β : Exponent (FiniteVariable.{u} n)) (A B : ℕ)
    {x y : Simplicial.Ambient (FiniteVariable.{u} n) k}
    (hx : x∈powerWeightedSpan (E := E) r α (fun a => a≤A))
    (hy : y∈powerWeightedSpan (E := E) s β (fun b => b<B)) :
    x*y∈powerWeightedSpan (E := E) (r+s) (α+β) (fun c => c<A+B) :=
  powerWeightedSpan_mul hE α β _ _ _ (by intros;omega) hx hy

lemma chainTotalEquiv_mem_powerWeightedSpan (hE : finiteLatticeClosed n E)
    (m : ℕ) (α : Exponent (FiniteVariable.{u} n)) (A : ℕ)
    {x : ChainTotalModule n E m α k}
    (hx : x∈weightBelow (chainTotalBasis n E m α k)
      (fun a => finiteChainFactorWeight.{u} a.1.val) A) :
    (chainTotalEquiv hE m α k x).val∈
      powerWeightedSpan (E := E) m α (fun a => a<A) := by
  let b := chainTotalBasis n E m α k
  let f := (TotalFaceModule (k := k)
    (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α)).subtype.comp
      (chainTotalEquiv hE m α k).toLinearMap
  change f x∈_
  rw [←b.linearCombination_repr x,Finsupp.linearCombination_apply,Finsupp.sum,map_sum]
  apply Submodule.sum_mem
  intro a ha
  rw [map_smul]
  apply Submodule.smul_mem
  have hw : finiteChainFactorWeight.{u} a.1.val<A := by
    by_contra hn
    exact (Finsupp.mem_support_iff.mp ha) (hx a (Nat.le_of_not_gt hn))
  change (chainTotalEquiv hE m α k (chainTotalBasis n E m α k a)).val∈_
  rw [chainTotalEquiv_basis,totalFaceBasis_val,chainFaceEquiv_val]
  exact powerWeightedSpan_basis α _ a hw

lemma powerWeightedSpan_to_chainTotal (hE : finiteLatticeClosed n E)
    (m : ℕ) (α : Exponent (FiniteVariable.{u} n)) (A : ℕ)
    (x : ChainTotalModule n E m α k)
    (hx : (chainTotalEquiv hE m α k x).val∈
      powerWeightedSpan (E := E) m α (fun a => a<A)) :
    x∈weightBelow (chainTotalBasis n E m α k)
      (fun a => finiteChainFactorWeight.{u} a.1.val) A := by
  let W := weightBelow (chainTotalBasis n E m α k)
    (fun a => finiteChainFactorWeight.{u} a.1.val) A
  let f := (TotalFaceModule (k := k)
    (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α)).subtype.comp
      (chainTotalEquiv hE m α k).toLinearMap
  have hinj : Function.Injective f := fun a b h =>
    (chainTotalEquiv hE m α k).injective (Subtype.ext h)
  have hspan : powerWeightedSpan (k := k) (E := E) m α (fun a => a<A)≤W.map f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨F,⟨a,rfl,ha⟩,rfl⟩
    refine ⟨chainTotalBasis n E m α k a,basis_mem_weightBelow _ _ ha,?_⟩
    change (chainTotalEquiv hE m α k (chainTotalBasis n E m α k a)).val=Simplicial.basis a.2.val
    rw [chainTotalEquiv_basis,totalFaceBasis_val,chainFaceEquiv_val]
  obtain ⟨y,hy,he⟩ := hspan hx
  exact hinj he ▸ hy

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FirstPowerLiftWeight -/
section

set_option autoImplicit false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

def firstPowerRawFace {β : Exponent (FiniteVariable.{u} n)} {a : E}
    (hβ : RowMaximum β a.val)
    (s : {s // quotientKoszulFaces (finitePredecessorFamily n E a.val)
      (β-finiteRowExponent n a.val) s}) :
    {s // quotientKoszulFaces (finiteChainCoefficientFamily n (firstPowerTarget hβ).val)
      (β-finiteChainShift n (firstPowerTarget hβ).val) s} :=
  ⟨s.val,by
    simpa only [firstPowerTarget,singletonChain_coefficient,singletonChain_shift]
      using s.property⟩

lemma firstPowerSourceCast_basis
    {β : Exponent (FiniteVariable.{u} n)} {a : E} (hβ : RowMaximum β a.val)
    (s : {s // quotientKoszulFaces (finitePredecessorFamily n E a.val)
      (β-finiteRowExponent n a.val) s}) :
    firstPowerSourceCast (k := k) hβ (totalFaceBasis _ s) =
      totalFaceBasis _ (firstPowerRawFace hβ s) := by
  apply Subtype.ext
  rw [firstPowerSourceCast_val,totalFaceBasis_val,totalFaceBasis_val]
  rfl

/-- The actual exterior lift has leading coefficient one at the literal source
face, and every correction has strictly smaller standard-chain factor weight. -/
theorem firstPowerExteriorLift_lower_basis (hE : finiteLatticeClosed n E)
    {β : Exponent (FiniteVariable.{u} n)} {a : E} (hβ : RowMaximum β a.val)
    (s : {s // quotientKoszulFaces (finitePredecessorFamily n E a.val)
      (β-finiteRowExponent n a.val) s}) :
    (firstPowerExteriorLift (k := k) hE hβ (totalFaceBasis _ s)).val -
        Simplicial.basis s.val ∈
      powerWeightedSpan (E := E) 1 β
        (fun r => r < reesVariableWeight (finiteTupleImage E) (finiteTupleToNat a.val)) := by
  have h := chainTotalEquiv_mem_powerWeightedSpan hE 1 β _
    (firstPowerChainSection_lower_basis (k := k) hE hβ (firstPowerRawFace hβ s))
  simp only [map_sub,Submodule.coe_sub,chainTotalEquiv_basis,totalFaceBasis_val,
    chainFaceEquiv_val] at h
  change (chainTotalEquiv hE 1 β k
      (firstPowerChainSection hE hβ (firstPowerSourceCast hβ (totalFaceBasis _ s)))).val -
    Simplicial.basis s.val ∈ _
  rw [firstPowerSourceCast_basis]
  simpa only [firstPowerTarget,singletonChain_factorWeight,firstPowerRawFace] using h

theorem firstPowerRawFace_weight_le
    {β : Exponent (FiniteVariable.{u} n)} {a : E} (hβ : RowMaximum β a.val)
    (s : {s // quotientKoszulFaces (finitePredecessorFamily n E a.val)
      (β-finiteRowExponent n a.val) s}) :
    Simplicial.basis (k := k) s.val ∈
      powerWeightedSpan (E := E) 1 β
        (fun r => r ≤ reesVariableWeight (finiteTupleImage E) (finiteTupleToNat a.val)) := by
  exact powerWeightedSpan_basis β _ ⟨firstPowerTarget hβ,firstPowerRawFace hβ s⟩
    (by simp [firstPowerTarget])

theorem firstPowerExteriorLift_weight_le (hE : finiteLatticeClosed n E)
    {β : Exponent (FiniteVariable.{u} n)} {a : E} (hβ : RowMaximum β a.val)
    (s : {s // quotientKoszulFaces (finitePredecessorFamily n E a.val)
      (β-finiteRowExponent n a.val) s}) :
    (firstPowerExteriorLift (k := k) hE hβ (totalFaceBasis _ s)).val ∈
      powerWeightedSpan (E := E) 1 β
        (fun r => r ≤ reesVariableWeight (finiteTupleImage E) (finiteTupleToNat a.val)) := by
  have h := powerWeightedSpan_mono (k := k) (E := E) 1 β
    (fun _ hr => Nat.le_of_lt hr) (firstPowerExteriorLift_lower_basis hE hβ s)
  have hh := Submodule.add_mem _ h (firstPowerRawFace_weight_le (k := k) hβ s)
  simpa only [sub_add_cancel] using hh

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.OrderedProductWeight -/
section

set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

/-- A finite ordered product preserves the leading term whenever every factor
does so.  The strict estimate remains strict in every positive power. -/
theorem orderedProduct_weight_control (hE : finiteLatticeClosed n E) (m : ℕ)
    (β : Fin (m+1) → Exponent (FiniteVariable.{u} n)) (A : Fin (m+1) → ℕ)
    (x y : Fin (m+1) → Simplicial.Ambient (FiniteVariable.{u} n) k)
    (hy : ∀p,y p∈powerWeightedSpan (E := E) 1 (β p) (fun a => a≤A p))
    (hδ : ∀p,x p-y p∈powerWeightedSpan (E := E) 1 (β p) (fun a => a<A p)) :
    (List.ofFn x).prod∈powerWeightedSpan (E := E) (m+1) (∑p,β p) (fun a => a≤∑p,A p) ∧
    (List.ofFn x).prod-(List.ofFn y).prod∈
      powerWeightedSpan (E := E) (m+1) (∑p,β p) (fun a => a<∑p,A p) := by
  have hx (p) : x p∈powerWeightedSpan (E := E) 1 (β p) (fun a => a≤A p) := by
    have hδ' := powerWeightedSpan_mono (k := k) (E := E) 1 (β p)
      (fun _ h => h.le) (hδ p)
    simpa only [sub_add_cancel] using Submodule.add_mem _ hδ' (hy p)
  induction m with
  | zero =>
    simpa only [List.ofFn_succ,List.ofFn_zero,List.prod_cons,List.prod_nil,mul_one,
      Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] using And.intro (hx 0) (hδ 0)
  | succ m ih =>
    have ht := ih (fun p => β p.succ) (fun p => A p.succ)
      (fun p => x p.succ) (fun p => y p.succ)
      (fun p => hy p.succ) (fun p => hδ p.succ) (fun p => hx p.succ)
    have hprod := powerWeightedSpan_mul_le (k := k) (r := 1) (s := m+1) hE (β 0) (∑p : Fin (m+1),β p.succ)
      (A 0) (∑p : Fin (m+1),A p.succ) (hx 0) ht.1
    have hleft := powerWeightedSpan_mul_lt_left (k := k) (r := 1) (s := m+1) hE (β 0) (∑p : Fin (m+1),β p.succ)
      (A 0) (∑p : Fin (m+1),A p.succ) (hδ 0) ht.1
    have hright := powerWeightedSpan_mul_lt_right (k := k) (r := 1) (s := m+1) hE (β 0) (∑p : Fin (m+1),β p.succ)
      (A 0) (∑p : Fin (m+1),A p.succ) (hy 0) ht.2
    constructor
    · simpa only [List.ofFn_succ,List.prod_cons,Fin.sum_univ_succ,Nat.one_add] using hprod
    · have he : x 0*(List.ofFn (fun p : Fin (m+1) => x p.succ)).prod-
        y 0*(List.ofFn (fun p : Fin (m+1) => y p.succ)).prod =
        (x 0-y 0)*(List.ofFn (fun p : Fin (m+1) => x p.succ)).prod+
        y 0*((List.ofFn (fun p : Fin (m+1) => x p.succ)).prod-
          (List.ofFn (fun p : Fin (m+1) => y p.succ)).prod) := by noncomm_ring
      have hadd := Submodule.add_mem _ hleft hright
      rw [←he] at hadd
      simpa only [List.ofFn_succ,List.prod_cons,Fin.sum_univ_succ,Nat.one_add] using hadd

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.CrossingLiftWeight -/
section

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open scoped TensorProduct
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)} {m : ℕ}

def crossingFaceFamily (hE : finiteLatticeClosed n E) (w : FiniteMultichain n E m)
    (v : Exponent (FiniteVariable.{u} n))
    (F : {F // quotientKoszulFaces (finiteChainCoefficientFamily n w) v F})
    (p : Fin m) : {F // crossingBlockFaces w v p F} :=
  ⟨finiteBlockFace w p F.val,((finiteChainQuotientFaces_blocks hE w v F.val).mp F.property).2 p⟩

lemma crossingFaceFamily_union (hE : finiteLatticeClosed n E) (w : FiniteMultichain n E m)
    (v : Exponent (FiniteVariable.{u} n)) (hv : CrossingCovered w v)
    (F : {F // quotientKoszulFaces (finiteChainCoefficientFamily n w) v F}) :
    finiteFaceUnion (fun p => (crossingFaceFamily hE w v F p).val)=F.val := by
  ext x
  simp only [mem_finiteFaceUnion,crossingFaceFamily,mem_finiteBlockFace]
  constructor
  · rintro ⟨p,hx,_⟩
    exact hx
  · intro hx
    have hpos : v x≠0 := by
      have h := F.property.1 x
      simpa only [faceExponent_apply,if_pos hx,Nat.one_le_iff_ne_zero] using h
    obtain ⟨p,hp⟩ := hv x hpos
    exact ⟨p,hx,hp⟩

def crossingFaceShuffle (hE : finiteLatticeClosed n E) (w : FiniteMultichain n E m)
    (v : Exponent (FiniteVariable.{u} n))
    (F : {F // quotientKoszulFaces (finiteChainCoefficientFamily n w) v F}) : ℤˣ :=
  faceListSign _ (finiteFamily_faces_pairwise (finiteCrosses w) (crossingBlockFaces w v)
    (fun p q hpq x hp hq => hpq (finiteCrosses_unique hp hq))
    (crossingBlockFaces_supported w v) (crossingFaceFamily hE w v F))

lemma crossingFace_product (hE : finiteLatticeClosed n E) (w : FiniteMultichain n E m)
    (v : Exponent (FiniteVariable.{u} n)) (hv : CrossingCovered w v)
    (F : {F // quotientKoszulFaces (finiteChainCoefficientFamily n w) v F}) :
    (List.ofFn (fun p => Simplicial.basis (k := k) (crossingFaceFamily hE w v F p).val)).prod =
      crossingFaceShuffle hE w v F • Simplicial.basis F.val := by
  have h := faceBasis_list_product (k := k) _
    (finiteFamily_faces_pairwise (finiteCrosses w) (crossingBlockFaces w v)
      (fun p q hpq x hp hq => hpq (finiteCrosses_unique hp hq))
      (crossingBlockFaces_supported w v) (crossingFaceFamily hE w v F))
  simpa only [List.map_ofFn,Function.comp_def,faceListUnion_ofFn,
    crossingFaceFamily_union hE w v hv F,crossingFaceShuffle] using h

lemma crossingBlockTensorEquiv_basis_decomposition (hE : finiteLatticeClosed n E)
    (w : FiniteMultichain n E m) (v : Exponent (FiniteVariable.{u} n))
    (hv : CrossingCovered w v)
    (F : {F // quotientKoszulFaces (finiteChainCoefficientFamily n w) v F}) :
    (crossingBlockTensorEquiv (k := k) hE w v hv).symm (totalFaceBasis _ F) =
      (crossingFaceShuffle hE w v F)⁻¹ •
        (⨂ₜ[k] p,totalFaceBasis (crossingBlockFaces w v p) (crossingFaceFamily hE w v F p)) := by
  let e := crossingBlockTensorEquiv (k := k) hE w v hv
  apply e.injective
  rw [e.apply_symm_apply]
  rw [LinearMapClass.map_smul_of_tower (S := k) e (crossingFaceShuffle hE w v F)⁻¹
    (⨂ₜ[k] p,totalFaceBasis (crossingBlockFaces w v p) (crossingFaceFamily hE w v F p))]
  apply Subtype.ext
  have he := LinearMap.congr_fun (crossingBlockTensorEquiv_actual_product (k := k) hE w v hv)
    (⨂ₜ[k] p,totalFaceBasis (crossingBlockFaces w v p) (crossingFaceFamily hE w v F p))
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,Submodule.subtype_apply,
    finiteFaceProduct,PiTensorProduct.lift.tprod,MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebraFin_apply,totalFaceBasis_val] at he
  simp only [Submodule.coe_smul_of_tower,totalFaceBasis_val]
  rw [he,crossingFace_product hE w v hv F]
  exact (inv_smul_smul (crossingFaceShuffle hE w v F) (Simplicial.basis F.val)).symm

def crossingRawFace (w : FiniteMultichain n E m) (v : Exponent (FiniteVariable.{u} n))
    (p : Fin m) (F : {F // crossingBlockFaces w v p F}) :
    {F // quotientKoszulFaces (finitePredecessorFamily n E (w.val p).val)
      (crossingBlockFineDegree w v p-finiteRowExponent n (w.val p).val) F} :=
  ⟨F.val,by simpa only [crossingBlockFaces,crossingBlockFineDegree,
    add_tsub_cancel_right] using F.property⟩

lemma crossingBlockSourceCast_basis (w : FiniteMultichain n E m)
    (v : Exponent (FiniteVariable.{u} n)) (p : Fin m)
    (F : {F // crossingBlockFaces w v p F}) :
    crossingBlockSourceCast (k := k) w v p (totalFaceBasis _ F) =
      totalFaceBasis _ (crossingRawFace w v p F) := by
  apply Subtype.ext
  simp only [crossingBlockSourceCast_val,totalFaceBasis_val]
  rfl

theorem crossingWholeLift_lower_basis (hE : finiteLatticeClosed n E)
    (w : FiniteMultichain n E m) (hm : 0< m) (v : Exponent (FiniteVariable.{u} n))
    (hv : CrossingCovered w v)
    (F : {F // quotientKoszulFaces (finiteChainCoefficientFamily n w) v F}) :
    (crossingWholeLift (k := k) hE w v hv (totalFaceBasis _ F)).val-Simplicial.basis F.val ∈
      powerWeightedSpan (E := E) m (∑p,crossingBlockFineDegree w v p)
        (fun a => a<finiteChainFactorWeight.{u} w) := by
  cases m with
  | zero => omega
  | succ m =>
    let fs := crossingFaceFamily hE w v F
    let A := fun p => reesVariableWeight (finiteTupleImage E) (finiteTupleToNat (w.val p).val)
    let x := fun p => (crossingBlockLift (k := k) hE w v p (totalFaceBasis _ (fs p))).val
    let y := fun p => Simplicial.basis (k := k) (fs p).val
    have hy : ∀p,y p∈powerWeightedSpan (E := E) 1 (crossingBlockFineDegree w v p)
        (fun a => a≤A p) := by
      intro p
      exact firstPowerRawFace_weight_le (k := k) (rowMaximum_block w p v)
        (crossingRawFace w v p (fs p))
    have hδ : ∀p,x p-y p∈powerWeightedSpan (E := E) 1 (crossingBlockFineDegree w v p)
        (fun a => a<A p) := by
      intro p
      change (firstPowerExteriorLift (k := k) hE (rowMaximum_block w p v)
        (crossingBlockSourceCast w v p (totalFaceBasis _ (fs p)))).val-y p∈_
      rw [crossingBlockSourceCast_basis]
      exact firstPowerExteriorLift_lower_basis hE (rowMaximum_block w p v)
        (crossingRawFace w v p (fs p))
    have hp := (orderedProduct_weight_control hE m (crossingBlockFineDegree w v) A x y hy hδ).2
    have hA : (∑p,A p)=finiteChainFactorWeight.{u} w := (finiteChainFactorWeight_sum w).symm
    rw [hA] at hp
    have hs : (crossingFaceShuffle hE w v F)⁻¹ •
        ((List.ofFn x).prod-(List.ofFn y).prod) ∈
        powerWeightedSpan (k := k) (E := E) (m+1)
          (∑p,crossingBlockFineDegree w v p) (fun a => a<finiteChainFactorWeight.{u} w) :=
      (powerWeightedSpan (k := k) (E := E) (m+1)
        (∑p,crossingBlockFineDegree w v p) (fun a => a<finiteChainFactorWeight.{u} w)).toAddSubgroup.zsmul_mem
        hp ((crossingFaceShuffle hE w v F)⁻¹).val
    change ((crossingLiftTensorProduct hE w v)
      ((crossingBlockTensorEquiv hE w v hv).symm (totalFaceBasis _ F))).val-
      Simplicial.basis F.val∈_
    rw [crossingBlockTensorEquiv_basis_decomposition]
    erw [LinearMapClass.map_smul_of_tower (S := k) (crossingLiftTensorProduct (k := k) hE w v)
      (crossingFaceShuffle hE w v F)⁻¹
      (⨂ₜ[k] p,totalFaceBasis (crossingBlockFaces w v p) (crossingFaceFamily hE w v F p))]
    simp only [Submodule.coe_smul_of_tower,crossingLiftTensorProduct,LinearMap.comp_apply,
      PiTensorProduct.map_tprod,idealPowerOrderedProduct_tprod_val]
    have he : (crossingFaceShuffle hE w v F)⁻¹ • (List.ofFn y).prod=Simplicial.basis F.val := by
      rw [crossingFace_product hE w v hv F]
      exact inv_smul_smul (crossingFaceShuffle hE w v F) (Simplicial.basis F.val)
    simpa only [smul_sub,he] using hs

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ContractibleBlockLift -/
section

set_option autoImplicit false
noncomputable section
namespace FourPapers.Sublattice
variable {K A B : Type*} [CommRing K]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]

/-- Extend the ordinary inclusion of a contractible source block to a chain
map. This formula uses only its integral contraction and the two differentials. -/
def contractibleBlockLift (D : Module.End K B) (d h : Module.End K A)
    (s : A →ₗ[K] B) : A →ₗ[K] B :=
  (D.comp s).comp h + (s.comp h).comp d

theorem contractibleBlockLift_chain (D : Module.End K B) (d h : Module.End K A)
    (s : A →ₗ[K] B) (hD : D*D=0) (hd : d*d=0) :
    D.comp (contractibleBlockLift D d h s) = (contractibleBlockLift D d h s).comp d := by
  have hDD (y : B) : D (D y)=0 := LinearMap.congr_fun hD y
  have hdd (x : A) : d (d x)=0 := LinearMap.congr_fun hd x
  apply LinearMap.ext
  intro x
  simp only [contractibleBlockLift,LinearMap.comp_apply,LinearMap.add_apply,map_add]
  rw [hDD,hdd,map_zero,map_zero]
  simp only [map_zero,zero_add,add_zero]

/-- The correction is exactly the ordinary differential's off-diagonal defect
after the same-block contraction. Thus a weight-lowering defect gives a
weight-lowering correction without requiring a contraction of the target. -/
theorem contractibleBlockLift_sub (D : Module.End K B) (d h : Module.End K A)
    (s : A →ₗ[K] B) (hc : d*h+h*d=1) :
    contractibleBlockLift D d h s - s = (D.comp s - s.comp d).comp h := by
  apply LinearMap.ext
  intro x
  have hc' : d (h x)+h (d x)=x := LinearMap.congr_fun hc x
  have hs : s (d (h x))+s (h (d x))=s x := by
    simpa only [map_add] using congrArg s hc'
  change D (s (h x))+s (h (d x))-s x = D (s (h x))-s (d (h x))
  rw [←hs]
  abel

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.AllPowersChainEquiv -/
section

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)} {m : ℕ}
variable {α : Exponent (FiniteVariable.{u} n)}

/-- Literal inclusion of one coefficient block in the direct sum. -/
def chainTotalSingle (w : AdmissibleChain n E m α) :
    TotalFaceModule (k := k) (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
      (α-finiteChainShift n w.val)) →ₗ[k] ChainTotalModule n E m α k :=
  DFinsupp.lsingle (R := k) (M := fun z : AdmissibleChain n E m α =>
    TotalFaceModule (k := k) (quotientKoszulFaces (finiteChainCoefficientFamily n z.val)
      (α-finiteChainShift n z.val))) w

@[simp] lemma facePredicateEquiv_val {V : Type u} [Fintype V] [LinearOrder V]
    (P Q : Finset V → Prop) (h : ∀ F,P F↔Q F)
    (x : TotalFaceModule (k := k) P) :
    (facePredicateEquiv (k := k) P Q h x).val=x.val := rfl

lemma crossingFineDegree_admissible (w : AdmissibleChain n E m α)
    (hw : CrossingCovered w.val (α-finiteChainShift n w.val)) :
    (∑p,crossingBlockFineDegree w.val (α-finiteChainShift n w.val) p)=α := by
  rw [crossingBlockFineDegree_sum _ _ hw,tsub_add_cancel_of_le w.property]

def coveredBlockLift (hE : finiteLatticeClosed n E) (w : AdmissibleChain n E m α)
    (hw : CrossingCovered w.val (α-finiteChainShift n w.val)) :
    TotalFaceModule (k := k) (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
      (α-finiteChainShift n w.val)) →ₗ[k] ChainTotalModule n E m α k :=
  (chainTotalEquiv hE m α k).symm.toLinearMap.comp
    ((facePredicateEquiv _ _ (fun F => by rw [crossingFineDegree_admissible w hw])).toLinearMap.comp
      (crossingWholeLift hE w.val (α-finiteChainShift n w.val) hw))

lemma coveredBlockLift_chain (hE : finiteLatticeClosed n E) (w : AdmissibleChain n E m α)
    (hw : CrossingCovered w.val (α-finiteChainShift n w.val)) :
    (chainTotalOrdinaryDifferential hE m α k).comp (coveredBlockLift (k := k) hE w hw) =
      (coveredBlockLift (k := k) hE w hw).comp
        (quotientTotalDifferential (finiteChainCoefficientFamily n w.val) (α-finiteChainShift n w.val)) := by
  apply LinearMap.ext
  intro x
  apply (chainTotalEquiv hE m α k).injective
  simp only [LinearMap.comp_apply,chainTotalOrdinaryDifferential,coveredBlockLift,
    LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  simp only [idealTotalDifferential_val,facePredicateEquiv_val]
  have h := congrArg Subtype.val (LinearMap.congr_fun
    (crossingWholeLift_is_chain (k := k) hE w.val (α-finiteChainShift n w.val) hw) x)
  simpa only [LinearMap.comp_apply,idealTotalDifferential_val] using h

lemma coveredBlockLift_lower_basis (hE : finiteLatticeClosed n E) (hm : 0< m)
    (w : AdmissibleChain n E m α) (hw : CrossingCovered w.val (α-finiteChainShift n w.val))
    (F : {F // quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
      (α-finiteChainShift n w.val) F}) :
    coveredBlockLift (k := k) hE w hw (totalFaceBasis _ F)-chainTotalBasis n E m α k ⟨w,F⟩ ∈
      weightBelow (chainTotalBasis n E m α k)
        (fun a => finiteChainFactorWeight.{u} a.1.val) (finiteChainFactorWeight.{u} w.val) := by
  apply powerWeightedSpan_to_chainTotal hE m α (finiteChainFactorWeight.{u} w.val)
  simp only [map_sub,Submodule.coe_sub,chainTotalEquiv_basis,totalFaceBasis_val,chainFaceEquiv_val,
    coveredBlockLift,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,facePredicateEquiv_val]
  have h := crossingWholeLift_lower_basis (k := k) hE w.val hm (α-finiteChainShift n w.val) hw F
  simpa only [crossingFineDegree_admissible w hw] using h

lemma uncoveredBlock_contraction (hE : finiteLatticeClosed n E) (w : AdmissibleChain n E m α)
    (hw : ¬CrossingCovered w.val (α-finiteChainShift n w.val)) :
    ∃H : Module.End k (TotalFaceModule (k := k)
      (quotientKoszulFaces (finiteChainCoefficientFamily n w.val) (α-finiteChainShift n w.val))),
      quotientTotalDifferential (finiteChainCoefficientFamily n w.val) (α-finiteChainShift n w.val)*H+
        H*quotientTotalDifferential (finiteChainCoefficientFamily n w.val) (α-finiteChainShift n w.val)=1 ∧
      ∀i x,x∈totalFacePiece
        (quotientKoszulFaces (finiteChainCoefficientFamily n w.val) (α-finiteChainShift n w.val)) i →
        H x∈totalFacePiece
        (quotientKoszulFaces (finiteChainCoefficientFamily n w.val) (α-finiteChainShift n w.val)) (i+1) := by
  unfold CrossingCovered at hw
  obtain ⟨e,he⟩ := not_forall.mp hw
  have hp : (α-finiteChainShift n w.val) e≠0 := by
    by_contra hn
    exact he (fun h => (h hn).elim)
  have hn : ∀p,¬finiteCrosses w.val p e := by
    intro p h
    exact he (fun _ => ⟨p,h⟩)
  exact uncoveredCrossingBlock_contractible hE w.val (α-finiteChainShift n w.val) e
    (Nat.pos_of_ne_zero hp) hn

def uncoveredBlockHomotopy (hE : finiteLatticeClosed n E) (w : AdmissibleChain n E m α)
    (hw : ¬CrossingCovered w.val (α-finiteChainShift n w.val)) :=
  (uncoveredBlock_contraction (k := k) hE w hw).choose

def uncoveredBlockLift (hE : finiteLatticeClosed n E) (w : AdmissibleChain n E m α)
    (hw : ¬CrossingCovered w.val (α-finiteChainShift n w.val)) :
    TotalFaceModule (k := k) (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
      (α-finiteChainShift n w.val)) →ₗ[k] ChainTotalModule n E m α k :=
  contractibleBlockLift (chainTotalOrdinaryDifferential hE m α k)
    (quotientTotalDifferential (finiteChainCoefficientFamily n w.val) (α-finiteChainShift n w.val))
    (uncoveredBlockHomotopy (k := k) hE w hw) (chainTotalSingle (k := k) w)

lemma chainTotalSpecial_lsingle (w : AdmissibleChain n E m α)
    (x : TotalFaceModule (k := k)
      (quotientKoszulFaces (finiteChainCoefficientFamily n w.val) (α-finiteChainShift n w.val))) :
    chainTotalSpecialDifferential n E m α k ((chainTotalSingle (k := k) w) x) =
      chainTotalSingle (k := k) w (quotientTotalDifferential (finiteChainCoefficientFamily n w.val)
        (α-finiteChainShift n w.val) x) :=
  dfinsuppBlockMap_lsingle (K := k)
    (M := fun z : AdmissibleChain n E m α => TotalFaceModule (k := k)
      (quotientKoszulFaces (finiteChainCoefficientFamily n z.val) (α-finiteChainShift n z.val)))
    (fun z => quotientTotalDifferential (k := k) (finiteChainCoefficientFamily n z.val)
      (α-finiteChainShift n z.val)) w x

lemma chainTotalDefect_block_lower (hE : finiteLatticeClosed n E) (w : AdmissibleChain n E m α)
    (x : TotalFaceModule (k := k)
      (quotientKoszulFaces (finiteChainCoefficientFamily n w.val) (α-finiteChainShift n w.val))) :
    (chainTotalOrdinaryDifferential hE m α k-chainTotalSpecialDifferential n E m α k)
        (chainTotalSingle (k := k) w x) ∈
      weightBelow (chainTotalBasis n E m α k)
        (fun a => finiteChainFactorWeight.{u} a.1.val) (finiteChainFactorWeight.{u} w.val) := by
  let b := totalFaceBasis (k := k)
    (quotientKoszulFaces (finiteChainCoefficientFamily n w.val) (α-finiteChainShift n w.val))
  rw [←b.linearCombination_repr x,Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_sum]
  apply Submodule.sum_mem
  intro F hF
  rw [map_smul,map_smul]
  apply Submodule.smul_mem
  have hs : chainTotalSingle (k := k) w (b F)=chainTotalBasis n E m α k ⟨w,F⟩ :=
    (chainTotalBasis_apply n E m α k w F).symm
  rw [hs]
  exact fun j hj => chainTotalDifferential_strictLower hE m α k ⟨w,F⟩ j hj

lemma uncoveredBlockLift_chain (hE : finiteLatticeClosed n E) (w : AdmissibleChain n E m α)
    (hw : ¬CrossingCovered w.val (α-finiteChainShift n w.val)) :
    (chainTotalOrdinaryDifferential hE m α k).comp (uncoveredBlockLift (k := k) hE w hw) =
      (uncoveredBlockLift (k := k) hE w hw).comp
        (quotientTotalDifferential (finiteChainCoefficientFamily n w.val) (α-finiteChainShift n w.val)) :=
  contractibleBlockLift_chain _ _ _ _ (chainTotalOrdinaryDifferential_square_zero hE m α k)
    (quotientTotalDifferential_comp _ _)

lemma uncoveredBlockLift_lower_basis (hE : finiteLatticeClosed n E)
    (w : AdmissibleChain n E m α) (hw : ¬CrossingCovered w.val (α-finiteChainShift n w.val))
    (F : {F // quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
      (α-finiteChainShift n w.val) F}) :
    uncoveredBlockLift (k := k) hE w hw (totalFaceBasis _ F)-chainTotalBasis n E m α k ⟨w,F⟩ ∈
      weightBelow (chainTotalBasis n E m α k)
        (fun a => finiteChainFactorWeight.{u} a.1.val) (finiteChainFactorWeight.{u} w.val) := by
  have hc := (uncoveredBlock_contraction (k := k) hE w hw).choose_spec.1
  have he := LinearMap.congr_fun (contractibleBlockLift_sub
    (chainTotalOrdinaryDifferential hE m α k)
    (quotientTotalDifferential (finiteChainCoefficientFamily n w.val) (α-finiteChainShift n w.val))
    (uncoveredBlockHomotopy (k := k) hE w hw) (chainTotalSingle (k := k) w) hc) (totalFaceBasis _ F)
  simp only [LinearMap.sub_apply,LinearMap.comp_apply] at he
  rw [chainTotalBasis_apply]
  change contractibleBlockLift _ _ _ _ (totalFaceBasis _ F)-chainTotalSingle (k := k) w (totalFaceBasis _ F)∈_
  rw [he]
  change chainTotalOrdinaryDifferential hE m α k (chainTotalSingle (k := k) w _) -
    chainTotalSingle (k := k) w (quotientTotalDifferential _ _ _)∈_
  rw [←chainTotalSpecial_lsingle]
  exact chainTotalDefect_block_lower hE w _

def allPowerBlockLift (hE : finiteLatticeClosed n E) (w : AdmissibleChain n E m α) :
    TotalFaceModule (k := k) (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
      (α-finiteChainShift n w.val)) →ₗ[k] ChainTotalModule n E m α k :=
  if hw : CrossingCovered w.val (α-finiteChainShift n w.val)
  then coveredBlockLift (k := k) hE w hw else uncoveredBlockLift (k := k) hE w hw

lemma allPowerBlockLift_chain (hE : finiteLatticeClosed n E) (w : AdmissibleChain n E m α) :
    (chainTotalOrdinaryDifferential hE m α k).comp (allPowerBlockLift (k := k) hE w) =
      (allPowerBlockLift (k := k) hE w).comp
        (quotientTotalDifferential (finiteChainCoefficientFamily n w.val) (α-finiteChainShift n w.val)) := by
  unfold allPowerBlockLift
  split_ifs
  · exact coveredBlockLift_chain hE w _
  · exact uncoveredBlockLift_chain hE w _

lemma allPowerBlockLift_lower_basis (hE : finiteLatticeClosed n E) (hm : 0< m)
    (w : AdmissibleChain n E m α)
    (F : {F // quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
      (α-finiteChainShift n w.val) F}) :
    allPowerBlockLift (k := k) hE w (totalFaceBasis _ F)-chainTotalBasis n E m α k ⟨w,F⟩ ∈
      weightBelow (chainTotalBasis n E m α k)
        (fun a => finiteChainFactorWeight.{u} a.1.val) (finiteChainFactorWeight.{u} w.val) := by
  unfold allPowerBlockLift
  split_ifs
  · exact coveredBlockLift_lower_basis hE hm w _ F
  · exact uncoveredBlockLift_lower_basis hE w _ F

def allPowerChange (hE : finiteLatticeClosed n E) (m : ℕ)
    (α : Exponent (FiniteVariable.{u} n)) : Module.End k (ChainTotalModule n E m α k) :=
  DFinsupp.lsum k (allPowerBlockLift (k := k) hE)

lemma allPowerChange_basis (hE : finiteLatticeClosed n E)
    (a : ChainFaceIndex n E m α) :
    allPowerChange (k := k) hE m α (chainTotalBasis n E m α k a) =
      allPowerBlockLift (k := k) hE a.1 (totalFaceBasis _ a.2) := by
  rcases a with ⟨w,F⟩
  rw [chainTotalBasis_apply]
  exact DFinsupp.lsum_single _ _ _ _

lemma allPowerChange_single (hE : finiteLatticeClosed n E)
    (w : AdmissibleChain n E m α)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
      (α-finiteChainShift n w.val))) :
    allPowerChange (k := k) hE m α (chainTotalSingle (k := k) w x) =
      allPowerBlockLift (k := k) hE w x :=
  DFinsupp.lsum_single _ _ _ _

theorem allPowerChange_is_chain (hE : finiteLatticeClosed n E) (m : ℕ)
    (α : Exponent (FiniteVariable.{u} n)) :
    (chainTotalOrdinaryDifferential hE m α k).comp (allPowerChange (k := k) hE m α) =
      (allPowerChange (k := k) hE m α).comp (chainTotalSpecialDifferential n E m α k) := by
  apply DFinsupp.lhom_ext
  intro w x
  change chainTotalOrdinaryDifferential hE m α k
      (allPowerChange (k := k) hE m α (chainTotalSingle (k := k) w x)) =
    allPowerChange (k := k) hE m α
      (chainTotalSpecialDifferential n E m α k (chainTotalSingle (k := k) w x))
  rw [chainTotalSpecial_lsingle,allPowerChange_single,allPowerChange_single]
  simpa only [LinearMap.comp_apply] using
    LinearMap.congr_fun (allPowerBlockLift_chain (k := k) hE w) x

lemma allPowerChange_lower_basis (hE : finiteLatticeClosed n E) (hm : 0< m)
    (a : ChainFaceIndex n E m α) :
    allPowerChange (k := k) hE m α (chainTotalBasis n E m α k a)-chainTotalBasis n E m α k a ∈
      weightBelow (chainTotalBasis n E m α k)
        (fun b => finiteChainFactorWeight.{u} b.1.val) (finiteChainFactorWeight.{u} a.1.val) := by
  rw [allPowerChange_basis]
  exact allPowerBlockLift_lower_basis hE hm a.1 a.2

/-- The actual ordinary and coefficient-block differentials are conjugate in
every positive power, over every commutative coefficient ring. -/
theorem allPowerTotalChainEquiv_exists (hE : finiteLatticeClosed n E) (m : ℕ) (hm : 0< m)
    (α : Exponent (FiniteVariable.{u} n)) :
    ∃e : ChainTotalModule n E m α k ≃ₗ[k] ChainTotalModule n E m α k,
      e.toLinearMap=allPowerChange (k := k) hE m α ∧
      (chainTotalOrdinaryDifferential hE m α k).comp e.toLinearMap =
        e.toLinearMap.comp (chainTotalSpecialDifferential n E m α k) := by
  let b := chainTotalBasis n E m α k
  let rank := fun a : ChainFaceIndex n E m α => finiteChainFactorWeight.{u} a.1.val
  have hdiag : ∀i,b.repr (allPowerChange (k := k) hE m α (b i)) i=1 := by
    intro i
    have h := allPowerChange_lower_basis (k := k) hE hm i i le_rfl
    simpa only [map_sub,Finsupp.sub_apply,Module.Basis.repr_self,Finsupp.single_eq_same,
      sub_eq_zero] using h
  have htri : ∀i j,i≠j → rank i≤rank j →
      b.repr (allPowerChange (k := k) hE m α (b i)) j=0 := by
    intro i j hij hr
    have h := allPowerChange_lower_basis (k := k) hE hm i j hr
    simpa only [map_sub,Finsupp.sub_apply,Module.Basis.repr_self,
      Finsupp.single_eq_of_ne (Ne.symm hij),sub_zero] using h
  refine ⟨triangularLinearEquiv b (allPowerChange (k := k) hE m α) rank hdiag htri,?_,?_⟩
  · exact triangularLinearEquiv_toLinearMap _ _ _ _ _
  · rw [triangularLinearEquiv_toLinearMap]
    exact allPowerChange_is_chain hE m α

end FourPapers.Sublattice


end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.CrossingLiftDegree -/
section

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open scoped TensorProduct
universe u

section Ambient
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

lemma faceDegree_forget (P : Finset V → Prop) (i : ℕ)
    {z : Simplicial.Ambient V k} (hz : z ∈ Simplicial.Chains P i) :
    z ∈ Simplicial.Chains (fun _ => True) i :=
  Simplicial.chains_mono (fun _ _ => True.intro) i hz

lemma faceDegree_of_support (P : Finset V → Prop) (i : ℕ)
    {z : Simplicial.Ambient V k}
    (hP : z ∈ basisSpan Simplicial.basis P)
    (hi : z ∈ Simplicial.Chains (fun _ => True) i) :
    z ∈ Simplicial.Chains P i := by
  change z ∈ Submodule.span k (Simplicial.basis '' {F | P F}) at hP
  change z ∈ Submodule.span k (Simplicial.basis '' {F | True ∧ F.card=i}) at hi
  change z ∈ Submodule.span k (Simplicial.basis '' {F | P F ∧ F.card=i})
  rw [Simplicial.basis.mem_span_image] at hP hi ⊢
  intro F hF
  exact ⟨hP hF,(hi hF).2⟩

lemma faceDegree_mul (i j : ℕ) {x y : Simplicial.Ambient V k}
    (hx : x ∈ Simplicial.Chains (fun _ => True) i)
    (hy : y ∈ Simplicial.Chains (fun _ => True) j) :
    x*y ∈ Simplicial.Chains (fun _ => True) (i+j) := by
  apply faceSpan_mul_mem (fun F => True ∧ F.card=i) (fun G => True ∧ G.card=j)
    (fun H => True ∧ H.card=i+j) _ hx hy
  intro F hF G hG hd
  exact ⟨True.intro,by rw [Finset.card_union_of_disjoint hd,hF.2,hG.2]⟩

lemma faceDegree_ordered_product (m : ℕ) (degree : Fin m → ℕ)
    (x : Fin m → Simplicial.Ambient V k)
    (hx : ∀p,x p ∈ Simplicial.Chains (fun _ => True) (degree p)) :
    (List.ofFn x).prod ∈ Simplicial.Chains (fun _ => True) (∑p,degree p) := by
  induction m with
  | zero =>
    have h : Simplicial.basis (V := V) (k := k) ∅ ∈
        Simplicial.Chains (fun _ => True) 0 := Simplicial.basis_mem True.intro rfl
    simpa only [faceBasis_empty,List.ofFn_zero,List.prod_nil,Fin.sum_univ_zero] using h
  | succ m ih =>
    simpa only [List.ofFn_succ,List.prod_cons,Fin.sum_univ_succ] using
      faceDegree_mul (degree 0) (∑p : Fin m,degree p.succ) (hx 0)
        (ih (fun p => degree p.succ) (fun p => x p.succ) (fun p => hx p.succ))
end Ambient

variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)} {m : ℕ}

lemma crossingBlockLift_preserves_degree (hE : finiteLatticeClosed n E)
    (w : FiniteMultichain n E m) (v : Exponent (FiniteVariable.{u} n)) (p : Fin m)
    (i : ℕ) (x : TotalFaceModule (k := k) (crossingBlockFaces w v p))
    (hx : x ∈ totalFacePiece (crossingBlockFaces w v p) i) :
    crossingBlockLift hE w v p x ∈
      totalFacePiece (koszulFaces (exponentPowerFamily (finiteRowFamily n E) 1)
        (crossingBlockFineDegree w v p)) i := by
  rw [crossingBlockLift_apply]
  have hxcast : crossingBlockSourceCast (k := k) w v p x ∈
      totalFacePiece (quotientKoszulFaces (finitePredecessorFamily n E (w.val p).val)
        (crossingBlockFineDegree w v p-finiteRowExponent n (w.val p).val)) i := by
    change (crossingBlockSourceCast (k := k) w v p x).val ∈ Simplicial.Chains (k := k)
      (quotientKoszulFaces (finitePredecessorFamily n E (w.val p).val)
        (crossingBlockFineDegree w v p-finiteRowExponent n (w.val p).val)) i
    rw [crossingBlockSourceCast_val]
    change x.val ∈ Simplicial.Chains (crossingBlockFaces w v p) i at hx
    simpa only [crossingBlockFineDegree,add_tsub_cancel_right,crossingBlockFaces] using hx
  exact firstPowerExteriorLift_preserves_degree (k := k) hE
    (β := crossingBlockFineDegree w v p) (a := w.val p) (rowMaximum_block w p v) i
    (crossingBlockSourceCast (k := k) w v p x) hxcast

lemma crossingFaceFamily_card_sum (hE : finiteLatticeClosed n E)
    (w : FiniteMultichain n E m) (v : Exponent (FiniteVariable.{u} n))
    (hv : CrossingCovered w v)
    (F : {F // quotientKoszulFaces (finiteChainCoefficientFamily n w) v F}) :
    (∑p,(crossingFaceFamily hE w v F p).val.card)=F.val.card := by
  have hd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      (fun p => (crossingFaceFamily hE w v F p).val) := by
    intro p hp q hq hpq
    apply Finset.disjoint_left.mpr
    intro x hpx hqx
    exact hpq (finiteCrosses_unique
      (crossingBlockFaces_supported w v p _ (crossingFaceFamily hE w v F p).property x hpx)
      (crossingBlockFaces_supported w v q _ (crossingFaceFamily hE w v F q).property x hqx))
  have hc := Finset.card_biUnion hd
  have hu : finiteFaceUnion (fun p => (crossingFaceFamily hE w v F p).val) =
      Finset.univ.biUnion (fun p => (crossingFaceFamily hE w v F p).val) := by
    ext x
    simp only [mem_finiteFaceUnion,Finset.mem_biUnion,Finset.mem_univ,true_and]
  rw [←hu,crossingFaceFamily_union hE w v hv F] at hc
  exact hc.symm

/-- The actual exterior lift preserves homological degree for every power.
The proof uses degree addition in the exterior algebra and disjointness of the
crossing blocks, including the empty product. -/
theorem crossingWholeLift_preserves_degree (hE : finiteLatticeClosed n E)
    (w : FiniteMultichain n E m) (v : Exponent (FiniteVariable.{u} n))
    (hv : CrossingCovered w v) (i : ℕ)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces (finiteChainCoefficientFamily n w) v))
    (hx : x ∈ totalFacePiece (quotientKoszulFaces (finiteChainCoefficientFamily n w) v) i) :
    crossingWholeLift hE w v hv x ∈
      totalFacePiece (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m)
        (∑p,crossingBlockFineDegree w v p)) i := by
  have hle : totalFacePiece (k := k)
      (quotientKoszulFaces (finiteChainCoefficientFamily n w) v) i ≤
      (totalFacePiece (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m)
        (∑p,crossingBlockFineDegree w v p)) i).comap (crossingWholeLift hE w v hv) := by
    rw [totalFacePiece_eq_basis_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨F,hF,rfl⟩
    change (crossingWholeLift hE w v hv (totalFaceBasis _ F)).val ∈ Simplicial.Chains _ i
    apply faceDegree_of_support _ i (crossingWholeLift hE w v hv (totalFaceBasis _ F)).property
    let fs := crossingFaceFamily hE w v F
    have hp := faceDegree_ordered_product m (fun p => (fs p).val.card)
      (fun p => (crossingBlockLift (k := k) hE w v p (totalFaceBasis _ (fs p))).val)
      (fun p => faceDegree_forget _ _ (crossingBlockLift_preserves_degree hE w v p _ _
        (totalFaceBasis_mem_degree _ (fs p))))
    have hc : (∑p,(fs p).val.card)=i :=
      (crossingFaceFamily_card_sum hE w v hv F).trans hF
    rw [hc] at hp
    have hs : (crossingFaceShuffle hE w v F)⁻¹ •
        (List.ofFn (fun p =>
          (crossingBlockLift (k := k) hE w v p (totalFaceBasis _ (fs p))).val)).prod ∈
        Simplicial.Chains (fun _ => True) i :=
      (Simplicial.Chains (V := FiniteVariable.{u} n) (k := k)
        (fun _ => True) i).toAddSubgroup.zsmul_mem hp
          ((crossingFaceShuffle hE w v F)⁻¹).val
    change ((crossingLiftTensorProduct hE w v)
      ((crossingBlockTensorEquiv hE w v hv).symm (totalFaceBasis _ F))).val ∈ _
    rw [crossingBlockTensorEquiv_basis_decomposition]
    erw [LinearMapClass.map_smul_of_tower (S := k) (crossingLiftTensorProduct (k := k) hE w v)
      (crossingFaceShuffle hE w v F)⁻¹
      (⨂ₜ[k] p,totalFaceBasis (crossingBlockFaces w v p) (crossingFaceFamily hE w v F p))]
    simpa only [Submodule.coe_smul_of_tower,crossingLiftTensorProduct,LinearMap.comp_apply,
      PiTensorProduct.map_tprod,idealPowerOrderedProduct_tprod_val] using hs
  exact hle hx

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.AllPowersChainDegrees -/
section

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)} {m : ℕ}
variable {α : Exponent (FiniteVariable.{u} n)}

def chainTotalPiece (n : Fin d → ℕ) (E : Finset (FiniteTuple n)) (m : ℕ)
    (α : Exponent (FiniteVariable.{u} n)) (k : Type u) [CommRing k] (i : ℕ) :
    Submodule k (ChainTotalModule n E m α k) :=
  basisDegreePiece (chainTotalBasis n E m α k) (fun a => a.2.val.card) i

lemma chainTotalPiece_iff (i : ℕ) (x : ChainTotalModule n E m α k) :
    x ∈ chainTotalPiece n E m α k i ↔ ∀w,x w ∈
      totalFacePiece (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
        (α-finiteChainShift n w.val)) i := by
  simpa only [chainTotalPiece,chainTotalBasis,totalFacePiece_eq_basisDegreePiece] using
    dfinsupp_basis_degree_iff
      (fun w : AdmissibleChain n E m α => totalFaceBasis (k := k)
        (quotientKoszulFaces (finiteChainCoefficientFamily n w.val) (α-finiteChainShift n w.val)))
      (fun _ s => s.val.card) i x

lemma chainTotalPiece_single (i : ℕ) (w : AdmissibleChain n E m α)
    (x : TotalFaceModule (k := k)
      (quotientKoszulFaces (finiteChainCoefficientFamily n w.val) (α-finiteChainShift n w.val)))
    (hx : x ∈ totalFacePiece
      (quotientKoszulFaces (finiteChainCoefficientFamily n w.val) (α-finiteChainShift n w.val)) i) :
    chainTotalSingle (k := k) w x ∈ chainTotalPiece n E m α k i := by
  rw [chainTotalPiece_iff]
  intro z
  by_cases hz : w=z
  · subst z
    simpa only [chainTotalSingle,DFinsupp.lsingle_apply,DFinsupp.single_eq_same] using hx
  · simp [chainTotalSingle,hz]

lemma chainTotalEquiv_preserves_chainTotalPiece (hE : finiteLatticeClosed n E) (i : ℕ)
    (x : ChainTotalModule n E m α k) (hx : x ∈ chainTotalPiece n E m α k i) :
    chainTotalEquiv hE m α k x ∈ totalFacePiece
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α) i :=
  chainTotalEquiv_preserves_degree hE m α i hx

lemma chainTotalEquiv_symm_preserves_chainTotalPiece (hE : finiteLatticeClosed n E) (i : ℕ)
    (x : TotalFaceModule (k := k)
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α))
    (hx : x ∈ totalFacePiece
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α) i) :
    (chainTotalEquiv hE m α k).symm x ∈ chainTotalPiece n E m α k i := by
  have hle : totalFacePiece (k := k)
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α) i ≤
      (chainTotalPiece n E m α k i).comap (chainTotalEquiv hE m α k).symm.toLinearMap := by
    rw [totalFacePiece_eq_basis_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨F,hF,rfl⟩
    change (chainTotalEquiv hE m α k).symm (totalFaceBasis _ F) ∈
      chainTotalPiece n E m α k i
    rw [chainTotalEquiv_symm_basis]
    apply Submodule.subset_span
    refine ⟨(chainFaceEquiv hE α).symm F,?_,rfl⟩
    have he := congrArg (fun a => a.val.card)
      ((chainFaceEquiv hE α).apply_symm_apply F)
    have hc : ((chainFaceEquiv hE α).symm F).2.val.card=F.val.card := by
      simpa only [chainFaceEquiv_val] using he
    exact hc.trans hF
  exact hle hx

lemma coveredBlockLift_preserves_degree (hE : finiteLatticeClosed n E) (i : ℕ)
    (w : AdmissibleChain n E m α) (hw : CrossingCovered w.val (α-finiteChainShift n w.val))
    (x : TotalFaceModule (k := k)
      (quotientKoszulFaces (finiteChainCoefficientFamily n w.val) (α-finiteChainShift n w.val)))
    (hx : x ∈ totalFacePiece
      (quotientKoszulFaces (finiteChainCoefficientFamily n w.val) (α-finiteChainShift n w.val)) i) :
    coveredBlockLift (k := k) hE w hw x ∈ chainTotalPiece n E m α k i := by
  apply chainTotalEquiv_symm_preserves_chainTotalPiece
  change (crossingWholeLift hE w.val (α-finiteChainShift n w.val) hw x).val ∈
    Simplicial.Chains (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α) i
  have h := crossingWholeLift_preserves_degree hE w.val (α-finiteChainShift n w.val) hw i x hx
  change (crossingWholeLift (k := k) hE w.val (α-finiteChainShift n w.val) hw x).val ∈
    Simplicial.Chains (k := k) (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m)
      (∑p,crossingBlockFineDegree w.val (α-finiteChainShift n w.val) p)) i at h
  simpa only [crossingFineDegree_admissible w hw] using h

lemma uncoveredBlockLift_preserves_degree (hE : finiteLatticeClosed n E) (i : ℕ)
    (w : AdmissibleChain n E m α) (hw : ¬CrossingCovered w.val (α-finiteChainShift n w.val))
    (x : TotalFaceModule (k := k)
      (quotientKoszulFaces (finiteChainCoefficientFamily n w.val) (α-finiteChainShift n w.val)))
    (hx : x ∈ totalFacePiece
      (quotientKoszulFaces (finiteChainCoefficientFamily n w.val) (α-finiteChainShift n w.val)) i) :
    uncoveredBlockLift (k := k) hE w hw x ∈ chainTotalPiece n E m α k i := by
  have hH := (uncoveredBlock_contraction (k := k) hE w hw).choose_spec.2
  dsimp only [uncoveredBlockLift,contractibleBlockLift,LinearMap.add_apply,LinearMap.comp_apply]
  apply Submodule.add_mem
  · apply basisDegreePiece_differential_lowers (chainTotalBasis n E m α k)
      (fun a => a.2.val.card) (chainTotalOrdinaryDifferential hE m α k)
      (chainTotalOrdinaryDifferential_degreeSupport hE m α k) i
    exact chainTotalPiece_single (i+1) w _ (hH i x hx)
  · cases i with
    | zero =>
      have hd := quotientTotalDifferential_zero_degree _ _ x hx
      simp only [LinearMap.comp_apply,hd,map_zero]
      exact Submodule.zero_mem _
    | succ i =>
      exact chainTotalPiece_single (i+1) w _
        (hH i _ (quotientTotalDifferential_lowers _ _ i x hx))

lemma allPowerBlockLift_preserves_degree (hE : finiteLatticeClosed n E) (i : ℕ)
    (w : AdmissibleChain n E m α)
    (x : TotalFaceModule (k := k)
      (quotientKoszulFaces (finiteChainCoefficientFamily n w.val) (α-finiteChainShift n w.val)))
    (hx : x ∈ totalFacePiece
      (quotientKoszulFaces (finiteChainCoefficientFamily n w.val) (α-finiteChainShift n w.val)) i) :
    allPowerBlockLift (k := k) hE w x ∈ chainTotalPiece n E m α k i := by
  unfold allPowerBlockLift
  split_ifs
  · exact coveredBlockLift_preserves_degree hE i w _ x hx
  · exact uncoveredBlockLift_preserves_degree hE i w _ x hx

lemma allPowerChange_preserves_degree (hE : finiteLatticeClosed n E) (i : ℕ)
    (x : ChainTotalModule n E m α k) (hx : x ∈ chainTotalPiece n E m α k i) :
    allPowerChange (k := k) hE m α x ∈ chainTotalPiece n E m α k i := by
  have hle : chainTotalPiece n E m α k i ≤
      (chainTotalPiece n E m α k i).comap (allPowerChange (k := k) hE m α) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,rfl⟩
    change allPowerChange (k := k) hE m α (chainTotalBasis n E m α k a) ∈
      chainTotalPiece n E m α k i
    rw [allPowerChange_basis]
    apply allPowerBlockLift_preserves_degree
    rw [totalFacePiece_eq_basis_span]
    exact Submodule.subset_span ⟨a.2,ha,rfl⟩
  exact hle hx

/-- The triangular comparison and its inverse preserve every actual
homological degree, in addition to intertwining the two differentials. -/
theorem allPowerGradedChainEquiv_exists (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0< m) (α : Exponent (FiniteVariable.{u} n)) :
    ∃e : ChainTotalModule n E m α k ≃ₗ[k] ChainTotalModule n E m α k,
      e.toLinearMap=allPowerChange (k := k) hE m α ∧
      (chainTotalOrdinaryDifferential hE m α k).comp e.toLinearMap =
        e.toLinearMap.comp (chainTotalSpecialDifferential n E m α k) ∧
      (∀i x,x∈chainTotalPiece n E m α k i → e x∈chainTotalPiece n E m α k i) ∧
      (∀i x,x∈chainTotalPiece n E m α k i → e.symm x∈chainTotalPiece n E m α k i) := by
  obtain ⟨e,he,hchain⟩ := allPowerTotalChainEquiv_exists (k := k) hE m hm α
  have hp : ∀i x,x∈chainTotalPiece n E m α k i → e x∈chainTotalPiece n E m α k i := by
    intro i x hx
    change e.toLinearMap x∈_
    rw [he]
    exact allPowerChange_preserves_degree hE i x hx
  refine ⟨e,he,hchain,hp,?_⟩
  intro i x hx
  apply triangularInverse_preserves_span (chainTotalBasis n E m α k)
    (fun a => finiteChainFactorWeight.{u} a.1.val) e
  · intro a
    change (chainTotalBasis n E m α k).repr (e.toLinearMap _) a=1
    rw [he]
    have h := allPowerChange_lower_basis (k := k) hE hm a a le_rfl
    simpa only [map_sub,Finsupp.sub_apply,Module.Basis.repr_self,Finsupp.single_eq_same,
      sub_eq_zero] using h
  · intro a b hab hr
    change (chainTotalBasis n E m α k).repr (e.toLinearMap _) b=0
    rw [he]
    have h := allPowerChange_lower_basis (k := k) hE hm a b hr
    simpa only [map_sub,Finsupp.sub_apply,Module.Basis.repr_self,
      Finsupp.single_eq_of_ne (Ne.symm hab),sub_zero] using h
  · exact fun y hy => hp i y hy
  · exact hx

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.allPowerTotalChainEquiv_exists
#print axioms FourPapers.Sublattice.allPowerGradedChainEquiv_exists

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.AllPowersHomology -/
section

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CategoryTheory.Limits CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

/-- The total triangular comparison, restricted to its actual homological
pieces. Both the forward and inverse degree conditions are proved, not assumed. -/
def allPowerFaceComparisonIso (hE : finiteLatticeClosed n E) (m : ℕ) (hm : 0< m)
    (α : Exponent (FiniteVariable.{u} n)) :
    (FourPapers.dfinsuppComplexData (fun w : AdmissibleChain n E m α =>
      quotientTotalData (k := k) (finiteChainCoefficientFamily n w.val)
        (α-finiteChainShift n w.val))).complex ≅
    (idealTotalData (k := k) (koszulFaces_downward
      (exponentPowerFamily (finiteRowFamily n E) m) α)).complex := by
  let C := FourPapers.dfinsuppComplexData (fun w : AdmissibleChain n E m α =>
    quotientTotalData (k := k) (finiteChainCoefficientFamily n w.val)
      (α-finiteChainShift n w.val))
  let D := idealTotalData (k := k) (koszulFaces_downward
    (exponentPowerFamily (finiteRowFamily n E) m) α)
  let e := (allPowerGradedChainEquiv_exists (k := k) hE m hm α).choose
  have he := (allPowerGradedChainEquiv_exists (k := k) hE m hm α).choose_spec
  let t := chainTotalEquiv hE m α k
  refine C.isoOfTotal D (e.trans t) ?_ ?_ ?_
  · intro i x hx
    change x ∈ FourPapers.dfinsuppPiece (fun w : AdmissibleChain n E m α =>
      totalFacePiece (k := k) (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
        (α-finiteChainShift n w.val)) i) at hx
    have hx' : x ∈ chainTotalPiece n E m α k i :=
      (chainTotalPiece_iff i x).mpr ((FourPapers.mem_dfinsuppPiece _ x).mp hx)
    exact chainTotalEquiv_preserves_chainTotalPiece hE i (e x) (he.2.2.1 i x hx')
  · intro i x hx
    change e.symm (t.symm x) ∈ FourPapers.dfinsuppPiece
      (fun w : AdmissibleChain n E m α => totalFacePiece (k := k)
        (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
          (α-finiteChainShift n w.val)) i)
    apply (FourPapers.mem_dfinsuppPiece _ _).mpr
    apply (chainTotalPiece_iff i _).mp
    exact he.2.2.2 i (t.symm x)
      (chainTotalEquiv_symm_preserves_chainTotalPiece hE i x hx)
  · apply LinearMap.ext
    intro x
    change idealTotalDifferential
      (koszulFaces_downward (exponentPowerFamily (finiteRowFamily n E) m) α)
      (t (e x)) = t (e (chainTotalSpecialDifferential n E m α k x))
    have hx : chainTotalOrdinaryDifferential hE m α k (e x) =
        e (chainTotalSpecialDifferential n E m α k x) :=
      LinearMap.congr_fun he.2.1 x
    have h := congrArg t hx
    change t (t.symm (idealTotalDifferential
      (koszulFaces_downward (exponentPowerFamily (finiteRowFamily n E) m) α)
      (t (e x)))) = t (e (chainTotalSpecialDifferential n E m α k x)) at h
    rwa [t.apply_symm_apply] at h

/-- The homology of the actual ideal strand is the finite product of the
actual quotient-strand homologies, for all positive powers and fine degrees. -/
def allPowerHomogeneousHomologyIso (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0< m) (α : Exponent (FiniteVariable.{u} n)) (i : ℕ) :
    (homogeneousComplex (k := k) (exponentPowerFamily (finiteRowFamily n E) m) α).homology i ≅
      ModuleCat.of k (∀w : AdmissibleChain n E m α,
        (quotientHomogeneousComplex (k := k) (finiteChainCoefficientFamily n w.val)
          (α-finiteChainShift n w.val)).homology i) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ) i).mapIso
      ((idealTotalKoszulIso (k := k) (exponentPowerFamily (finiteRowFamily n E) m) α).symm ≪≫
        (allPowerFaceComparisonIso (k := k) hE m hm α).symm) ≪≫
    FourPapers.dfinsuppComplexHomologyIso
      (fun w : AdmissibleChain n E m α => quotientTotalData (k := k)
        (finiteChainCoefficientFamily n w.val) (α-finiteChainShift n w.val)) i ≪≫
    (LinearEquiv.piCongrRight (fun w : AdmissibleChain n E m α =>
      ((HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ) i).mapIso
        (quotientTotalKoszulIso (k := k) (finiteChainCoefficientFamily n w.val)
          (α-finiteChainShift n w.val))).toLinearEquiv)).toModuleIso

section Field
variable {K : Type u} [Field K]

/-- The full natural fine-degree Betti equality, expressed over the admissible
chains. Dimensions are dimensions of the actual derived-Tor pieces. -/
theorem allPowerBetti_admissible (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0< m) (p : ℕ) (α : Exponent (FiniteVariable.{u} n)) :
    bettiNumber (k := K) (exponentPowerFamily (finiteRowFamily n E) m) α p =
      ∑w : AdmissibleChain n E m α,
        quotientBettiNumber (k := K) (finiteChainCoefficientFamily n w.val)
          (α-finiteChainShift n w.val) p := by
  unfold bettiNumber
  rw [← (gradedTorIso (k := K) (exponentPowerFamily (finiteRowFamily n E) m) α p).toLinearEquiv.finrank_eq]
  rw [(allPowerHomogeneousHomologyIso (k := K) hE m hm α p).toLinearEquiv.finrank_eq,
    Module.finrank_pi_fintype]
  apply Finset.sum_congr rfl
  intro w _
  exact (quotientBettiNumber_eq_homology (k := K) _ _ _).symm

/-- The Betti-equality clause of Theorem 1.2 in natural fine degrees: every multichain occurs,
and an inadmissible residual degree contributes zero. -/
theorem allPowersBettiFormula (hE : finiteLatticeClosed n E) :
    AllPowersBettiFormula.{u} n E := by
  intro K _ m hm p α
  rw [allPowerBetti_admissible hE m hm p α]
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype
    (Finset.univ.filter (fun w : FiniteMultichain n E m => finiteChainShift n w ≤ α))
    (fun w => by simp) (fun w => quotientBettiNumber (k := K)
      (finiteChainCoefficientFamily n w) (α-finiteChainShift n w) p)).symm

/-- The same actual Tor formula with arbitrary integer fine degrees. -/
theorem allPowersIntegerBettiFormula (hE : finiteLatticeClosed n E)
    (K : Type u) [Field K] (m : ℕ) (hm : 0< m) (p : ℕ)
    (α : FiniteVariable.{u} n →₀ ℤ) :
    integerBettiNumber (k := K) (exponentPowerFamily (finiteRowFamily n E) m) α p =
      ∑w : FiniteMultichain n E m,
        quotientIntegerBettiNumber (k := K) (finiteChainCoefficientFamily n w)
          (α-integerExponent (finiteChainShift n w)) p :=
  integerFormula_of_allPowersBettiFormula n E (allPowersBettiFormula hE) K m hm p α
end Field
end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.allPowersBettiFormula
#print axioms FourPapers.Sublattice.allPowersIntegerBettiFormula

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.AllPowersComplete -/
section

/-!
# Compatibility import for the verified all-powers development

Every mathematical declaration lives in its original modular provider.
The former exact-source bundle is preserved for audit; this module adds no
new declarations, assumptions, or proof transformations.
-/

end

/- BEGIN EXACT BODY: FourPapers.Symmetric.Vendor.RingTheory.MvPolynomial.MonomialOrder -/
section

section
noncomputable section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Leading monomials for a monomial order

This file collects facts about leading monomials of multivariate polynomials for a monomial order
`m` on `σ →₀ ℕ`: comparisons of degrees with their `WithBot` forms, the degree of a monomial
multiple, the cancellation of leading terms by an S-polynomial, the behaviour of leading data
under a change of coefficients, leading data of the weighted homogeneous component containing
the leading monomial, leading data of renamed polynomials, elimination orders and the
lexicographic ones among them, agreement of leading exponents under two monomial orders, and
algebraic independence from leading monomials.

The product `X^a * b`, normalized to leading coefficient one when `b` has a unit leading
coefficient, differs from another such product of the same degree by a monomial multiple of
their S-polynomial. This is the cancellation of leading terms behind Buchberger's criterion.

Let `yᵢ`, `i ∈ σ`, be polynomials in the variables `Xᵢ` over a ring without zero divisors. If the
leading monomial of each `yᵢ` is the variable `Xᵢ`, then the `yᵢ` are algebraically independent:
the image of a monomial `c X^d` under `Xᵢ ↦ yᵢ` has leading monomial `X^d`, so the images of the
distinct monomials of a nonzero polynomial have distinct leading monomials and cannot cancel.

This is the triangularity argument for a family such as `yₙ = cₙ Xₙ + qₙ(X₁, …, Xₙ₋₁)` with
`cₙ ≠ 0`, ordered lexicographically with the variables of larger index more significant, as for
the images of the generators of the Lazard ring in a polynomial ring.

## Main results

* `MonomialOrder.degree_eq_of_forall_lt`, `MonomialOrder.degree_eq_of_forall_mem_lt`: strict
  comparisons preserving the leading exponent, including comparisons on a set containing the
  support and original leading exponent.
* `MonomialOrder.leadingCoeff_eq_of_degree_eq`, `MonomialOrder.leadingTerm_eq_of_degree_eq`,
  `MonomialOrder.sPolynomial_eq_of_degree_eq`: orders agreeing on leading exponents also agree
  on the corresponding leading coefficients, leading terms and S-polynomials.
* `MonomialOrder.toWithBotSyn_withBotDegree_le_toSyn_degree`: the `WithBot` degree of a polynomial
  is at most its degree.
* `MonomialOrder.withBotDegree_sub_lt`: if `q` has degree at most that of `f ≠ 0` and the same
  coefficient of `X^(deg f)`, then `f - q` has smaller degree than `f`.
* `MvPolynomial.monomial_mem_iff_monomial_one_mem`: a set closed under scalar multiplication
  contains `c X^a` for a unit `c` if and only if it contains `X^a`.
* `MonomialOrder.leadingTerm_mem_iff`: a set closed under scalar multiplication contains the
  leading term of a polynomial with unit leading coefficient if and only if it contains its
  leading monomial.
* `MonomialOrder.toSyn_degree_monomial_mul_le`: `c X^a * b` has degree at most `a + deg b`.
* `MonomialOrder.monomial_one_mul_sub_smul_eq_monomial_mul_sPolynomial`: if `b₀` has a unit
  leading coefficient, then `X^a * b` minus `lc b` times the product of `b₀` of the same degree
  normalized to leading coefficient one is a monomial multiple of the S-polynomial
  `m.sPolynomial b b₀`.
* `MonomialOrder.degree_map_of_injective`, `MonomialOrder.leadingCoeff_map_of_injective`,
  `MonomialOrder.leadingTerm_map_of_injective`, `MonomialOrder.sPolynomial_map_of_injective`: an
  injective coefficient map `φ` preserves leading monomials and commutes with leading
  coefficients, leading terms and S-polynomials.
* `MonomialOrder.leadingTerm_weightedHomogeneousComponent_weight_degree`: the weighted
  homogeneous component of `f` containing its leading monomial has the leading term of `f`.
* `MonomialOrder.degree_rename`, `MonomialOrder.leadingCoeff_rename` and
  `MonomialOrder.leadingTerm_rename`: renaming the variables along a relabeling which carries one
  monomial order to another commutes with leading monomials, coefficients and terms; such a
  relabeling is injective by `MonomialOrder.injective_of_forall_toSyn_le_iff`.
* `MonomialOrder.exists_rename_eq_of_coe_support_degree_subset`: for an elimination order, a
  polynomial whose leading monomial only involves the variables `e τ` is a renamed polynomial.
* `MonomialOrder.coe_support_subset_of_lex_le`: monomials supported in an upper set of variables
  form a lower set for the lexicographic order.
* `MonomialOrder.algebraicIndependent_of_degree_eq_single`: polynomials `yᵢ` whose leading
  monomial is `Xᵢ` are algebraically independent.
-/


open MvPolynomial

/-- A set of polynomials closed under scalar multiplication (for example a submodule or a
subalgebra) contains a monomial with unit coefficient if and only if it contains the
corresponding monomial with coefficient one. -/
theorem MvPolynomial.monomial_mem_iff_monomial_one_mem {σ R S : Type*} [CommSemiring R]
    [SetLike S (MvPolynomial σ R)] [SMulMemClass S R (MvPolynomial σ R)]
    {a : σ →₀ ℕ} {c : R} (C : S) (hc : IsUnit c) :
    monomial a c ∈ C ↔ monomial a 1 ∈ C := by
  obtain ⟨u, rfl⟩ := hc
  have h : monomial a (u : R) = (u : R) • monomial a 1 := by simp [smul_monomial]
  rw [h]
  refine ⟨fun hu => ?_, SMulMemClass.smul_mem _⟩
  simpa [smul_smul] using SMulMemClass.smul_mem ((u⁻¹ : Rˣ) : R) hu

namespace MonomialOrder

variable {σ R : Type*} (m : MonomialOrder σ)

/-- Two monomial orders give the same leading exponent of `f` if every other exponent in its
support remains strictly below its original leading exponent. -/
theorem degree_eq_of_forall_lt [CommSemiring R] (n : MonomialOrder σ)
    (f : MvPolynomial σ R)
    (h : ∀ a ∈ f.support, a ≠ m.degree f → a ≺[n] m.degree f) :
    n.degree f = m.degree f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  apply n.toSyn.injective
  refine le_antisymm (n.degree_le_iff.2 fun a ha ↦ ?_)
    (n.le_degree (m.degree_mem_support hf))
  rcases eq_or_ne a (m.degree f) with rfl | hne
  · exact le_rfl
  · exact (h a ha hne).le

/-- Orders preserving strict comparisons on a set containing the support and original leading
exponent of a polynomial give it the same leading exponent. -/
theorem degree_eq_of_forall_mem_lt [CommSemiring R] (n : MonomialOrder σ)
    (f : MvPolynomial σ R) {s : Set (σ →₀ ℕ)}
    (h : ∀ a ∈ s, ∀ b ∈ s, a ≺[m] b → a ≺[n] b)
    (hf : ↑f.support ⊆ s) (hd : m.degree f ∈ s) : n.degree f = m.degree f := by
  apply m.degree_eq_of_forall_lt n f
  intro a ha hne
  exact h a (hf ha) _ hd (lt_of_le_of_ne (m.le_degree ha) (m.toSyn.injective.ne hne))

/-- Orders agreeing on the leading exponent of a polynomial agree on its leading coefficient. -/
theorem leadingCoeff_eq_of_degree_eq [CommSemiring R] (n : MonomialOrder σ)
    {f : MvPolynomial σ R} (h : n.degree f = m.degree f) :
    n.leadingCoeff f = m.leadingCoeff f := by
  simp only [leadingCoeff, h]

/-- Orders agreeing on the leading exponent of a polynomial agree on its leading term. -/
theorem leadingTerm_eq_of_degree_eq [CommSemiring R] (n : MonomialOrder σ)
    {f : MvPolynomial σ R} (h : n.degree f = m.degree f) :
    n.leadingTerm f = m.leadingTerm f := by
  rw [leadingTerm, leadingTerm, h, m.leadingCoeff_eq_of_degree_eq n h]

/-- Orders agreeing on the leading exponents of two polynomials give the same S-polynomial. -/
theorem sPolynomial_eq_of_degree_eq [CommRing R] (n : MonomialOrder σ)
    {f g : MvPolynomial σ R} (hf : n.degree f = m.degree f) (hg : n.degree g = m.degree g) :
    n.sPolynomial f g = m.sPolynomial f g := by
  simp only [sPolynomial, hf, hg, m.leadingCoeff_eq_of_degree_eq n hf,
    m.leadingCoeff_eq_of_degree_eq n hg]

/-- The `WithBot` degree of a polynomial is at most its degree. -/
theorem toWithBotSyn_withBotDegree_le_toSyn_degree [CommSemiring R] (p : MvPolynomial σ R) :
    m.toWithBotSyn (m.withBotDegree p) ≤ m.toSyn (m.degree p) := by
  classical
  rw [withBotDegree_eq]
  split_ifs <;> simp [toWithBotSyn_apply_coe]

/-- If `q` has degree at most that of `f ≠ 0` and the same coefficient of `X^(deg f)`, then
`f - q` has smaller degree than `f`. -/
theorem withBotDegree_sub_lt [CommRing R] {f q : MvPolynomial σ R} (hf : f ≠ 0)
    (hq : m.toWithBotSyn (m.withBotDegree q) ≤ m.toWithBotSyn (m.withBotDegree f))
    (hqf : q.coeff (m.degree f) = m.leadingCoeff f) :
    m.toWithBotSyn (m.withBotDegree (f - q)) < m.toWithBotSyn (m.withBotDegree f) := by
  refine lt_of_le_of_ne ?_ fun heq ↦ ?_
  · simpa [sub_eq_add_neg] using
      (m.withBotDegree_add_le f (-q)).trans (max_le le_rfl (by rwa [withBotDegree_neg]))
  rw [EmbeddingLike.apply_eq_iff_eq, withBotDegree_eq_withBotDegree_iff] at heq
  have := m.degree_mem_support fun h0 ↦ hf (heq.2.1 h0)
  rw [heq.1, mem_support_iff, coeff_sub, hqf, leadingCoeff, sub_self] at this
  exact this rfl

/-- A monomial multiple `c X^a * b` has degree at most `a + deg b`. -/
theorem toSyn_degree_monomial_mul_le [CommSemiring R] (a : σ →₀ ℕ) (c : R)
    (b : MvPolynomial σ R) : m.toSyn (m.degree (monomial a c * b)) ≤ m.toSyn (a + m.degree b) := by
  rw [map_add]
  exact m.toSyn_degree_mul_le.trans (by gcongr; exact m.degree_monomial_le c)

/-- A set of polynomials closed under scalar multiplication (for example a submodule or a
subalgebra) contains the leading term of a polynomial with unit leading coefficient if and only
if it contains its leading monomial. -/
theorem leadingTerm_mem_iff [CommSemiring R] {S : Type*} [SetLike S (MvPolynomial σ R)]
    [SMulMemClass S R (MvPolynomial σ R)] {f : MvPolynomial σ R} (C : S)
    (hf : IsUnit (m.leadingCoeff f)) :
    m.leadingTerm f ∈ C ↔ monomial (m.degree f) 1 ∈ C := by
  rw [leadingTerm, monomial_mem_iff_monomial_one_mem C hf]

/-- **Cancellation of leading terms by an S-polynomial.** If `b₀` has unit leading coefficient
`u₀` and `deg b₀ ≤ a + deg b`, the difference between `X^a * b` and `lc b` times the normalized
product `X^(a + deg b - deg b₀) * b₀ / lc b₀` is `X^(a + deg b - L) / lc b₀ * S(b, b₀)`, where
`L = deg b ⊔ deg b₀`. -/
theorem monomial_one_mul_sub_smul_eq_monomial_mul_sPolynomial [CommRing R] {a : σ →₀ ℕ}
    {b b₀ : MvPolynomial σ R} (hb₀ : m.degree b₀ ≤ a + m.degree b) (u₀ : Rˣ)
    (hu₀ : (u₀ : R) = m.leadingCoeff b₀) :
    monomial a 1 * b -
        m.leadingCoeff b • (monomial (a + m.degree b - m.degree b₀) ((u₀⁻¹ : Rˣ) : R) * b₀) =
      monomial (a + m.degree b - m.degree b ⊔ m.degree b₀) ((u₀⁻¹ : Rˣ) : R) *
        m.sPolynomial b b₀ := by
  have hL : m.degree b ⊔ m.degree b₀ ≤ a + m.degree b := sup_le le_add_self hb₀
  -- The exponents of the two summands of the right-hand side.
  have e₁ : a + m.degree b - m.degree b ⊔ m.degree b₀ + (m.degree b ⊔ m.degree b₀ - m.degree b) =
      a := by
    rw [tsub_add_tsub_cancel hL le_sup_left, add_tsub_cancel_right]
  have e₂ : a + m.degree b - m.degree b ⊔ m.degree b₀ + (m.degree b ⊔ m.degree b₀ - m.degree b₀) =
      a + m.degree b - m.degree b₀ :=
    tsub_add_tsub_cancel hL le_sup_right
  -- The coefficient of the first summand.
  have hc : ((u₀⁻¹ : Rˣ) : R) * m.leadingCoeff b₀ = 1 := by rw [← hu₀, Units.inv_mul]
  simp only [sPolynomial_def, mul_sub, ← mul_assoc, monomial_mul_monomial, smul_eq_C_mul,
    C_mul_monomial, e₁, e₂, hc, mul_comm (m.leadingCoeff b)]

section Map

variable {S : Type*}

section CommSemiring

variable [CommSemiring R] [CommSemiring S] (φ : R →+* S) {f : MvPolynomial σ R}

/-- A coefficient map that does not kill the leading coefficient preserves the leading monomial. -/
theorem degree_map_of_leadingCoeff_ne_zero (h : φ (m.leadingCoeff f) ≠ 0) :
    m.degree (map φ f) = m.degree f := by
  have hmem : m.degree f ∈ (map φ f).support := by
    rwa [mem_support_iff, coeff_map]
  exact m.toSyn.injective <| le_antisymm
    (m.degree_le_iff.2 fun _ hc ↦ m.le_degree (support_map_subset φ f hc)) (m.le_degree hmem)

/-- A coefficient map that does not kill the leading coefficient maps it to the leading
coefficient of the image. -/
theorem leadingCoeff_map_of_leadingCoeff_ne_zero (h : φ (m.leadingCoeff f) ≠ 0) :
    m.leadingCoeff (map φ f) = φ (m.leadingCoeff f) := by
  rw [leadingCoeff, degree_map_of_leadingCoeff_ne_zero m φ h, coeff_map, leadingCoeff]

variable {φ}

/-- An injective coefficient map preserves the leading monomial. -/
theorem degree_map_of_injective (hφ : Function.Injective φ) (f : MvPolynomial σ R) :
    m.degree (map φ f) = m.degree f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  exact m.degree_map_of_leadingCoeff_ne_zero φ
    ((map_ne_zero_iff φ hφ).2 (m.leadingCoeff_ne_zero_iff.2 hf))

/-- An injective coefficient map preserves the `WithBot` degree. -/
theorem withBotDegree_map_of_injective (hφ : Function.Injective φ) (f : MvPolynomial σ R) :
    m.withBotDegree (map φ f) = m.withBotDegree f := by
  classical
  simp [withBotDegree_eq, m.degree_map_of_injective hφ, map_eq_zero_iff _ (map_injective φ hφ)]

/-- An injective coefficient map sends the leading coefficient to the leading coefficient of the
image. -/
theorem leadingCoeff_map_of_injective (hφ : Function.Injective φ) (f : MvPolynomial σ R) :
    m.leadingCoeff (map φ f) = φ (m.leadingCoeff f) := by
  rw [leadingCoeff, m.degree_map_of_injective hφ, coeff_map, leadingCoeff]

/-- An injective coefficient map sends the leading term to the leading term of the image. -/
theorem leadingTerm_map_of_injective (hφ : Function.Injective φ) (f : MvPolynomial σ R) :
    m.leadingTerm (map φ f) = map φ (m.leadingTerm f) := by
  rw [leadingTerm, leadingTerm, map_monomial, m.degree_map_of_injective hφ,
    m.leadingCoeff_map_of_injective hφ]

end CommSemiring

#check leadingTerm_map_of_injective

set_option maxHeartbeats 100000 in
/-- An injective coefficient map sends the S-polynomial of `f` and `g` to the S-polynomial of
their images. -/
theorem sPolynomial_map_of_injective [CommRing R] [CommRing S] {φ : R →+* S}
    (hφ : Function.Injective φ) (f g : MvPolynomial σ R) :
    m.sPolynomial (map φ f) (map φ g) = map φ (m.sPolynomial f g) := by
  unfold sPolynomial
  rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_mul,
    MvPolynomial.map_monomial, MvPolynomial.map_monomial,
    m.degree_map_of_injective hφ f, m.degree_map_of_injective hφ g,
    m.leadingCoeff_map_of_injective hφ f, m.leadingCoeff_map_of_injective hφ g]

#check sPolynomial_map_of_injective

end Map

section WeightedHomogeneous

open Finsupp

variable {M : Type*} [AddCommMonoid M] [CommSemiring R] (w : σ → M)

/-- The weighted homogeneous component of `f` whose weight is that of the leading monomial of `f`
has the same leading monomial as `f`. -/
@[simp]
theorem degree_weightedHomogeneousComponent_weight_degree (f : MvPolynomial σ R) :
    m.degree (weightedHomogeneousComponent w (weight w (m.degree f)) f) = m.degree f := by
  classical
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hsupp := support_weightedHomogeneousComponent (w := w) (weight w (m.degree f)) f
  refine m.toSyn.injective (le_antisymm (m.degree_le_iff.2 fun c hc ↦ ?_) (m.le_degree ?_))
  · rw [hsupp] at hc
    exact m.le_degree (Finset.mem_filter.1 hc).1
  · rw [hsupp]
    exact Finset.mem_filter.2 ⟨m.degree_mem_support hf, rfl⟩

/-- The weighted homogeneous component of `f` containing its leading monomial has the same leading
coefficient as `f`. -/
@[simp]
theorem leadingCoeff_weightedHomogeneousComponent_weight_degree (f : MvPolynomial σ R) :
    m.leadingCoeff (weightedHomogeneousComponent w (weight w (m.degree f)) f) =
      m.leadingCoeff f := by
  classical
  simp [leadingCoeff, coeff_weightedHomogeneousComponent]

/-- The weighted homogeneous component of `f` containing its leading monomial has the same leading
term as `f`. -/
@[simp]
theorem leadingTerm_weightedHomogeneousComponent_weight_degree (f : MvPolynomial σ R) :
    m.leadingTerm (weightedHomogeneousComponent w (weight w (m.degree f)) f) =
      m.leadingTerm f := by
  simp [leadingTerm]

/-- The weighted homogeneous component of `f` containing its leading monomial is weighted
homogeneous of the weight of its own leading monomial. -/
theorem isWeightedHomogeneous_weightedHomogeneousComponent_weight_degree (f : MvPolynomial σ R) :
    IsWeightedHomogeneous w (weightedHomogeneousComponent w (weight w (m.degree f)) f)
      (weight w (m.degree (weightedHomogeneousComponent w (weight w (m.degree f)) f))) := by
  rw [degree_weightedHomogeneousComponent_weight_degree]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

end WeightedHomogeneous

section Rename

variable {τ : Type*} [CommSemiring R] {m} {m' : MonomialOrder τ} {e : τ → σ}

/-- A relabeling of variables which carries the monomial order `m'` to `m` is injective. -/
theorem injective_of_forall_toSyn_le_iff
    (hm : ∀ a b : τ →₀ ℕ, a ≼[m'] b ↔ a.mapDomain e ≼[m] b.mapDomain e) :
    Function.Injective e := by
  intro i j hij
  -- The two variables `X i`, `X j` are renamed to the same variable, so neither exceeds the other.
  have hsingle : m.toSyn ((Finsupp.single i 1).mapDomain e) =
      m.toSyn ((Finsupp.single j 1).mapDomain e) := by
    simp [hij]
  have h := m'.toSyn.injective <| le_antisymm ((hm _ _).2 hsingle.le) ((hm _ _).2 hsingle.ge)
  simpa [Finsupp.single_left_inj] using h

/-- Renaming the variables along a relabeling which carries the monomial order `m'` to `m` renames
the leading monomial. -/
theorem degree_rename (hm : ∀ a b : τ →₀ ℕ, a ≼[m'] b ↔ a.mapDomain e ≼[m] b.mapDomain e)
    (p : MvPolynomial τ R) : m.degree (rename e p) = (m'.degree p).mapDomain e := by
  classical
  have he := injective_of_forall_toSyn_le_iff hm
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  refine m.toSyn.injective (le_antisymm (m.degree_le_iff.2 fun c hc ↦ ?_) (m.le_degree ?_))
  · rw [support_rename_of_injective he, Finset.mem_image] at hc
    obtain ⟨a, ha, rfl⟩ := hc
    exact (hm _ _).1 (m'.le_degree ha)
  · rw [support_rename_of_injective he]
    exact Finset.mem_image_of_mem _ (m'.degree_mem_support hp)

/-- Renaming the variables along a relabeling which carries the monomial order `m'` to `m`
preserves the leading coefficient. -/
theorem leadingCoeff_rename (hm : ∀ a b : τ →₀ ℕ, a ≼[m'] b ↔ a.mapDomain e ≼[m] b.mapDomain e)
    (p : MvPolynomial τ R) : m.leadingCoeff (rename e p) = m'.leadingCoeff p := by
  rw [leadingCoeff, degree_rename hm,
    coeff_rename_mapDomain _ (injective_of_forall_toSyn_le_iff hm), leadingCoeff]

/-- Renaming the variables along a relabeling which carries the monomial order `m'` to `m`
renames the leading term. -/
theorem leadingTerm_rename (hm : ∀ a b : τ →₀ ℕ, a ≼[m'] b ↔ a.mapDomain e ≼[m] b.mapDomain e)
    (p : MvPolynomial τ R) : m.leadingTerm (rename e p) = rename e (m'.leadingTerm p) := by
  rw [leadingTerm, leadingTerm, degree_rename hm, leadingCoeff_rename hm, rename_monomial]

/-- For an elimination order `m` for the variables `e τ`, that is, one in which every monomial
below a monomial in these variables is again a monomial in these variables, a polynomial whose
leading monomial only involves the variables `e τ` is the renaming of a polynomial in the
variables `τ`. -/
theorem exists_rename_eq_of_coe_support_degree_subset
    (helim : ∀ a b : σ →₀ ℕ, a ≼[m] b → ↑b.support ⊆ Set.range e → ↑a.support ⊆ Set.range e)
    (he : Function.Injective e) {g : MvPolynomial σ R}
    (hg : ↑(m.degree g).support ⊆ Set.range e) : ∃ g' : MvPolynomial τ R, rename e g' = g := by
  classical
  refine exists_rename_eq_of_vars_subset_range g e he fun i hi ↦ ?_
  obtain ⟨d, hd, hid⟩ := (mem_vars_iff_mem_support i).1 hi
  exact helim d _ (m.le_degree hd) hg hid

end Rename

section Lex

/-- For the lexicographic order, the monomials supported in an upper set of variables form a
lower set: with the antitone variable convention these are the smallest variables. -/
theorem coe_support_subset_of_lex_le [LinearOrder σ] [WellFoundedGT σ] {s : Set σ}
    (hs : IsUpperSet s) {a b : σ →₀ ℕ} (hab : a ≼[lex] b) (hb : ↑b.support ⊆ s) :
    ↑a.support ⊆ s := by
  intro j hj
  by_contra hjs
  rcases eq_or_ne a b with rfl | hne
  · exact hjs (hb hj)
  -- `a < b` first differs from `b` at some `i` with `0 ≤ a i < b i`, so `i ∈ s`; since `j ∉ s`,
  -- `j < i`, and then `a j = b j = 0`.
  obtain ⟨i, hi, hlt⟩ := Finsupp.Lex.lt_iff.1 <| lex_lt_iff.1 <|
    lt_of_le_of_ne hab (lex.toSyn.injective.ne hne)
  have hbi : i ∈ s := hb (Finsupp.mem_support_iff.2 (Nat.zero_lt_of_lt hlt).ne')
  have hji : j < i := lt_of_not_ge fun hij ↦ hjs (hs hij hbi)
  have hbj : b j = 0 := Finsupp.notMem_support_iff.1 fun h ↦ hjs (hb h)
  exact (Finsupp.mem_support_iff.1 hj) ((hi j hji).trans hbj)

end Lex

variable [CommRing R] [NoZeroDivisors R]

/-- **Algebraic independence from leading monomials.** Over a ring without zero divisors, a family
`yᵢ` of polynomials in the variables `Xᵢ` whose leading monomial for a monomial order is `Xᵢ` is
algebraically independent. -/
theorem algebraicIndependent_of_degree_eq_single {y : σ → MvPolynomial σ R}
    (hy : ∀ i, m.degree (y i) = Finsupp.single i 1) : AlgebraicIndependent R y := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact algebraicIndependent_iff_injective_aeval.2 fun _ _ _ ↦ Subsingleton.elim _ _
  have hy0 (i : σ) : y i ≠ 0 := fun h ↦ by
    simpa [h] using congrArg (fun d ↦ d i) (hy i)
  have hne (d : σ →₀ ℕ) : (d.prod fun i k ↦ y i ^ k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ ↦ pow_ne_zero _ (hy0 i)
  -- The image `c ∏ yᵢ ^ dᵢ` of a monomial `c X^d` with `c ≠ 0` has leading monomial `X^d`.
  have hterm {c : R} (hc : c ≠ 0) (d : σ →₀ ℕ) : m.degree (aeval y (monomial d c)) = d := by
    rw [aeval_monomial, algebraMap_eq, m.degree_mul (C_ne_zero.2 hc) (hne d), m.degree_C,
      zero_add, Finsupp.prod, m.degree_prod fun i _ ↦ pow_ne_zero _ (hy0 i)]
    simp_rw [m.degree_pow, hy, Finsupp.smul_single, smul_eq_mul, mul_one]
    exact d.sum_single
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
  intro p hp
  by_contra hp0
  rw [p.as_sum, map_sum] at hp
  -- The images of the monomials of `p` have pairwise distinct leading monomials, so their sum is
  -- nonzero.
  refine AddMonoidAlgebra.sum_ne_zero_of_injOn_supDegree (D := m.toSyn)
    (support_nonempty.2 hp0) (fun d hd ↦ ?_) (fun d hd e he hde ↦ ?_) hp
  · rw [aeval_monomial, algebraMap_eq]
    exact mul_ne_zero (C_ne_zero.2 (mem_support_iff.1 hd)) (hne d)
  · have key (d : σ →₀ ℕ) (hd : d ∈ p.support) :
        AddMonoidAlgebra.supDegree m.toSyn (aeval y (monomial d (p.coeff d))) = m.toSyn d := by
      -- `m.degree` is defined as the supremum `AddMonoidAlgebra.supDegree m.toSyn`, read back
      -- through `m.toSyn`.
      have h : m.toSyn (m.degree (aeval y (monomial d (p.coeff d)))) =
          AddMonoidAlgebra.supDegree m.toSyn (aeval y (monomial d (p.coeff d))) := by
        rw [degree, AddEquiv.apply_symm_apply]
        rfl
      rw [← h, hterm (mem_support_iff.1 hd)]
    have hde' :
        AddMonoidAlgebra.supDegree m.toSyn (aeval y (monomial d (p.coeff d))) =
          AddMonoidAlgebra.supDegree m.toSyn (aeval y (monomial e (p.coeff e))) := hde
    rw [key d hd, key e he] at hde'
    exact m.toSyn.injective hde'

end MonomialOrder

end

end
end

/- BEGIN EXACT BODY: FourPapers.Symmetric.Vendor.RingTheory.MvPolynomial.Groebner.Basic -/
section

section
noncomputable section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Remainders and Gröbner bases

Let `m` be a monomial order on `σ →₀ ℕ`. This file defines remainders on division by a set of
multivariate polynomials, and Gröbner bases of an ideal, and proves that remainders on division by
a Gröbner basis decide ideal membership.

* `MonomialOrder.IsRemainder m f B r`: `r` is a remainder of `f` on division by `B`, i.e.
  `f = ∑ g_b * b + r` where each product `g_b * b` has degree at most that of `f`, and no monomial
  of `r` is divisible by the leading monomial of a nonzero `b ∈ B`. The degree condition is
  stated with `MonomialOrder.withBotDegree`, so that the zero polynomial has degree `⊥`, and as
  the inequality `deg b + deg g_b ≤ deg f`; the remainder condition only concerns divisibility,
  not a comparison of degrees.
* `MonomialOrder.IsGroebnerBasis m G I`: `G` is a subset of the ideal `I` whose leading terms
  span the same ideal as the leading terms of all elements of `I`.

## Main results

* `MonomialOrder.exists_isRemainder`: remainders exist when every nonzero divisor has a unit
  leading coefficient; this is `MonomialOrder.div_set`.
* `MonomialOrder.IsGroebnerBasis.exists_degree_le_degree`: the leading monomial of every nonzero
  element of `I` is divisible by the leading monomial of a nonzero element of a Gröbner basis.
* `MonomialOrder.isGroebnerBasis_iff_forall_exists_degree_le_degree`: the converse, for a family
  whose nonzero members have unit leading coefficients.
* `MonomialOrder.IsGroebnerBasis.image_leadingTerm`: the leading terms of such a Gröbner basis of
  `I` form a Gröbner basis of the ideal of leading terms of `I`.
* `MonomialOrder.IsGroebnerBasis.sub_mem_iff`: for remainders `r₁`, `r₂` of `f₁`, `f₂` on division
  by a Gröbner basis of `I`, `f₁ - f₂ ∈ I` if and only if `r₁ = r₂`. In particular remainders on
  division by a Gröbner basis are unique (`MonomialOrder.IsGroebnerBasis.eq_of_isRemainder`) and
  a remainder vanishes exactly on `I` (`MonomialOrder.IsGroebnerBasis.remainder_eq_zero_iff_mem`).
* `MonomialOrder.IsGroebnerBasis.isRemainder_zero_iff_mem`: `0` is a remainder of `f` on division
  by a Gröbner basis of `I` if and only if `f ∈ I`, whatever the leading coefficients of the basis:
  every element of `I` has a standard representation (Adams–Loustaunau, Theorem 4.1.12).
* `MonomialOrder.IsGroebnerBasis.ideal_eq_span`: a Gröbner basis generates its ideal.
* `MonomialOrder.isGroebnerBasis_iff_isRemainder_zero`: `G ⊆ I` is a Gröbner basis of `I` if and
  only if every element of `I` has remainder `0` on division by `G`.

None of these results assume that the coefficients form a field: the statements needing division
assume that the nonzero members of the divisor set have unit leading coefficients, which over a
field is discharged by `MonomialOrder.isUnit_leadingCoeff`.

## References

The definitions `IsRemainder` and `IsGroebnerBasis` are those of Junyu Guo and Hao Shen in
Mathlib pull request 29203, upstreamed from the WuProver Gröbner basis project.

* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 2, §§5–6.
* W. W. Adams, P. Loustaunau, *An Introduction to Gröbner Bases*, Graduate Studies in
  Mathematics 3, American Mathematical Society, 1994, §4.1: Gröbner bases over rings and standard
  representations.
-/


namespace MonomialOrder

open MvPolynomial

variable {σ R : Type*} (m : MonomialOrder σ)

section CommSemiring

variable [CommSemiring R]

/-- `r` is a remainder of `f` on division by the set `B` for the monomial order `m`: there is a
finitely supported family `g : B →₀ MvPolynomial σ R` such that

1. `f = ∑ g_b * b + r`;
2. for each `b ∈ B`, `deg b + deg g_b ≤ deg f`, degrees being taken in `WithBot` so that the zero
   polynomial has degree `⊥`;
3. no monomial of `r` is divisible by the leading monomial of a nonzero `b ∈ B`. -/
def IsRemainder (f : MvPolynomial σ R) (B : Set (MvPolynomial σ R)) (r : MvPolynomial σ R) :
    Prop :=
  (∃ g : B →₀ MvPolynomial σ R,
    f = Finsupp.linearCombination _ (fun b : B ↦ (b : MvPolynomial σ R)) g + r ∧
    ∀ b : B, m.toWithBotSyn (m.withBotDegree (b : MvPolynomial σ R)) +
      m.toWithBotSyn (m.withBotDegree (g b)) ≤ m.toWithBotSyn (m.withBotDegree f)) ∧
  ∀ c ∈ r.support, ∀ b ∈ B, b ≠ 0 → ¬ m.degree b ≤ c

/-- A subset `G` of an ideal `I` is a Gröbner basis of `I` for the monomial order `m` if the
leading terms of the elements of `G` span the same ideal as the leading terms of all elements
of `I`. -/
def IsGroebnerBasis (G : Set (MvPolynomial σ R)) (I : Ideal (MvPolynomial σ R)) : Prop :=
  G ⊆ I ∧ Ideal.span (m.leadingTerm '' I) = Ideal.span (m.leadingTerm '' G)

variable {m} {f r : MvPolynomial σ R} {B G G' : Set (MvPolynomial σ R)}
  {I : Ideal (MvPolynomial σ R)}

/-- Unfolding lemma for `MonomialOrder.IsRemainder`. -/
theorem isRemainder_iff : m.IsRemainder f B r ↔
    (∃ g : B →₀ MvPolynomial σ R,
      f = Finsupp.linearCombination _ (fun b : B ↦ (b : MvPolynomial σ R)) g + r ∧
      ∀ b : B, m.toWithBotSyn (m.withBotDegree (b : MvPolynomial σ R)) +
        m.toWithBotSyn (m.withBotDegree (g b)) ≤ m.toWithBotSyn (m.withBotDegree f)) ∧
    ∀ c ∈ r.support, ∀ b ∈ B, b ≠ 0 → ¬ m.degree b ≤ c :=
  Iff.rfl

/-- The division representation of a remainder: `f = ∑ g_b * b + r` with
`deg b + deg g_b ≤ deg f` for each `b ∈ B`. -/
theorem IsRemainder.exists_linearCombination (h : m.IsRemainder f B r) :
    ∃ g : B →₀ MvPolynomial σ R,
      f = Finsupp.linearCombination _ (fun b : B ↦ (b : MvPolynomial σ R)) g + r ∧
      ∀ b : B, m.toWithBotSyn (m.withBotDegree (b : MvPolynomial σ R)) +
        m.toWithBotSyn (m.withBotDegree (g b)) ≤ m.toWithBotSyn (m.withBotDegree f) :=
  h.1

/-- No monomial of a remainder is divisible by the leading monomial of a nonzero divisor. -/
theorem IsRemainder.not_degree_le (h : m.IsRemainder f B r) {c : σ →₀ ℕ} (hc : c ∈ r.support)
    {b : MvPolynomial σ R} (hb : b ∈ B) (hb0 : b ≠ 0) : ¬ m.degree b ≤ c :=
  h.2 c hc b hb hb0

/-- Unfolding lemma for `MonomialOrder.IsGroebnerBasis`. -/
theorem isGroebnerBasis_iff : m.IsGroebnerBasis G I ↔
    G ⊆ I ∧ Ideal.span (m.leadingTerm '' I) = Ideal.span (m.leadingTerm '' G) :=
  Iff.rfl

/-- A subset of `I` whose leading terms span the ideal of leading terms of `I` is a Gröbner basis
of `I`. -/
theorem IsGroebnerBasis.mk (hGI : G ⊆ I)
    (hspan : Ideal.span (m.leadingTerm '' I) = Ideal.span (m.leadingTerm '' G)) :
    m.IsGroebnerBasis G I :=
  ⟨hGI, hspan⟩

/-- For nonzero `p`, `q` and `f`, the `WithBot` degree bound `deg p + deg q ≤ deg f` used in
`MonomialOrder.IsRemainder` is the corresponding bound on `MonomialOrder.degree`. -/
theorem toWithBotSyn_withBotDegree_add_le_iff {p q : MvPolynomial σ R} (hp : p ≠ 0) (hq : q ≠ 0)
    (hf : f ≠ 0) :
    m.toWithBotSyn (m.withBotDegree p) + m.toWithBotSyn (m.withBotDegree q) ≤
        m.toWithBotSyn (m.withBotDegree f) ↔
      m.toSyn (m.degree p) + m.toSyn (m.degree q) ≤ m.toSyn (m.degree f) := by
  simp [(m.withBotDegree_eq_coe_degree_iff _).2, toWithBotSyn_apply_coe, ← WithBot.coe_add, *]

/-- The remainders of `0` are exactly `0`. -/
@[simp]
theorem isRemainder_zero_left_iff : m.IsRemainder 0 B r ↔ r = 0 := by
  refine ⟨fun ⟨⟨g, hg, hdeg⟩, _⟩ ↦ ?_, fun hr ↦ ⟨⟨0, by simp [hr], by simp⟩, by simp [hr]⟩⟩
  -- Each product `g b * b` vanishes, since its degree is bounded by the degree `⊥` of `0`.
  have hgb (b : B) : g b • (b : MvPolynomial σ R) = 0 := by
    have := hdeg b
    simp only [withBotDegree_zero, toWithBotSyn_apply_bot, le_bot_iff, WithBot.add_eq_bot,
      toWithBotSyn_apply_eq_bot_iff, withBotDegree_eq_bot_iff] at this
    rcases this with h | h <;> simp [h]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_eq_zero fun b _ ↦ hgb b,
    zero_add] at hg
  exact hg.symm

/-- A polynomial is a remainder of itself on division by `B` exactly when none of its monomials is
divisible by the leading monomial of a nonzero element of `B`. -/
theorem isRemainder_self_iff :
    m.IsRemainder r B r ↔ ∀ c ∈ r.support, ∀ b ∈ B, b ≠ 0 → ¬ m.degree b ≤ c :=
  ⟨And.right, fun h ↦ ⟨⟨0, by simp, by simp⟩, h⟩⟩

/-- If `0` is a remainder of `f` on division by `B`, then the leading term of `f` lies in the ideal
spanned by the leading terms of `B`. -/
theorem leadingTerm_mem_span_leadingTerm_of_isRemainder_zero (h : m.IsRemainder f B 0) :
    m.leadingTerm f ∈ Ideal.span (m.leadingTerm '' B) := by
  classical
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  obtain ⟨g, hfg, hdeg⟩ := h.exists_linearCombination
  rw [add_zero, Finsupp.linearCombination_apply, Finsupp.sum] at hfg
  -- `lt f` is the sum of the `deg f` terms of the products `g_b * b`.
  have hlt : m.leadingTerm f = ∑ b ∈ g.support,
      monomial (m.degree f) ((g b * (b : MvPolynomial σ R)).coeff (m.degree f)) := by
    simp_rw [← map_sum, ← coeff_sum, ← smul_eq_mul, ← hfg, leadingTerm, leadingCoeff]
  refine hlt ▸ sum_mem fun b _ ↦ ?_
  by_cases hb : m.degree f ∈ (g b * (b : MvPolynomial σ R)).support
  · have hgb0 : g b ≠ 0 := fun h ↦ by simp [h] at hb
    have hb0 : (b : MvPolynomial σ R) ≠ 0 := fun h ↦ by simp [h] at hb
    -- The degree condition gives `deg b + deg g_b ≤ deg f`, and `deg f` is a monomial of
    -- `g_b * b`, so the two sides are equal and the `deg f` term is `lt g_b * lt b`.
    have hle := (toWithBotSyn_withBotDegree_add_le_iff hb0 hgb0 hf).1 (hdeg b)
    have heq : m.degree f = m.degree (g b) + m.degree (b : MvPolynomial σ R) :=
      m.toSyn.injective <| by
        rw [map_add]
        exact le_antisymm ((m.le_degree hb).trans m.toSyn_degree_mul_le)
          ((add_comm _ _).trans_le hle)
    rw [heq, coeff_mul_of_degree_add, ← monomial_mul_monomial]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨b, b.2, rfl⟩)
  · rw [notMem_support_iff.1 hb, map_zero]
    exact zero_mem _

/-- Every monomial of an element of the ideal spanned by the leading terms of `G` is divisible by
the leading monomial of a nonzero element of `G`. -/
theorem exists_degree_le_of_mem_span_leadingTerm {p : MvPolynomial σ R}
    (hp : p ∈ Ideal.span (m.leadingTerm '' G)) {c : σ →₀ ℕ} (hc : c ∈ p.support) :
    ∃ g ∈ G, g ≠ 0 ∧ m.degree g ≤ c := by
  have hle : Ideal.span (m.leadingTerm '' G) ≤
      Ideal.span ((fun d ↦ monomial d (1 : R)) '' (m.degree '' (G \ {0}))) := by
    rw [← m.span_leadingTerm_sdiff_singleton_zero, Ideal.span_le, Set.image_subset_iff]
    intro g hg
    rw [Set.mem_preimage, SetLike.mem_coe, ← C_mul_leadingCoeff_monomial_degree]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨m.degree g, ⟨g, hg, rfl⟩, rfl⟩)
  obtain ⟨_, ⟨g, ⟨hgG, hg0⟩, rfl⟩, hgc⟩ := mem_ideal_span_monomial_image.1 (hle hp) c hc
  exact ⟨g, hgG, by simpa using hg0, hgc⟩

/-- If `0` is a remainder of a nonzero `f` on division by `B`, then the leading monomial of `f` is
divisible by the leading monomial of a nonzero element of `B`. -/
theorem exists_degree_le_degree_of_isRemainder_zero (h : m.IsRemainder f B 0) (hf : f ≠ 0) :
    ∃ b ∈ B, b ≠ 0 ∧ m.degree b ≤ m.degree f :=
  exists_degree_le_of_mem_span_leadingTerm (leadingTerm_mem_span_leadingTerm_of_isRemainder_zero h)
    (by rw [m.support_leadingTerm' hf]; exact Finset.mem_singleton_self _)

/-- The coefficient of `X^D` in an element of the ideal spanned by the leading terms of `G` lies in
the ideal of `R` spanned by the leading coefficients of those `g ∈ G` with `deg g ≤ D`. -/
theorem coeff_mem_span_leadingCoeff {p : MvPolynomial σ R}
    (hp : p ∈ Ideal.span (m.leadingTerm '' G)) (D : σ →₀ ℕ) :
    p.coeff D ∈ Ideal.span (m.leadingCoeff '' {g ∈ G | m.degree g ≤ D}) := by
  classical
  induction hp using Submodule.span_induction generalizing D with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    rw [leadingTerm, coeff_monomial]
    split_ifs with h
    · exact Ideal.subset_span ⟨g, ⟨hg, h.le⟩, rfl⟩
    · exact zero_mem _
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem (hx D) (hy D)
  | smul a x _ hx =>
    -- Each term `a_e * x_{e'}` of the `D` coefficient of `a * x` has `e' ≤ D`.
    rw [smul_eq_mul, coeff_mul]
    refine sum_mem fun e he ↦ Ideal.mul_mem_left _ _ <|
      Ideal.span_mono (Set.image_mono ?_) (hx e.2)
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at he
    exact fun g hg ↦ ⟨hg.1, hg.2.trans (he ▸ le_add_self)⟩

/-- A Gröbner basis of `I` is contained in `I`. -/
theorem IsGroebnerBasis.subset (h : m.IsGroebnerBasis G I) : G ⊆ I :=
  h.1

/-- The leading terms of a Gröbner basis of `I` span the ideal of leading terms of `I`. -/
theorem IsGroebnerBasis.span_leadingTerm_image (h : m.IsGroebnerBasis G I) :
    Ideal.span (m.leadingTerm '' I) = Ideal.span (m.leadingTerm '' G) :=
  h.2

/-- An ideal is a Gröbner basis of itself. -/
theorem isGroebnerBasis_self (I : Ideal (MvPolynomial σ R)) : m.IsGroebnerBasis (I : Set _) I :=
  .mk subset_rfl rfl

/-- Adjoining further elements of `I` to a Gröbner basis of `I` gives a Gröbner basis of `I`. -/
theorem IsGroebnerBasis.mono (h : m.IsGroebnerBasis G I) (hGG' : G ⊆ G') (hG'I : G' ⊆ I) :
    m.IsGroebnerBasis G' I :=
  .mk hG'I <| le_antisymm
    (h.span_leadingTerm_image.le.trans (Ideal.span_mono (Set.image_mono hGG')))
    (Ideal.span_mono (Set.image_mono hG'I))

/-- Removing `0` does not change whether a set is a Gröbner basis. -/
@[simp]
theorem isGroebnerBasis_sdiff_singleton_zero :
    m.IsGroebnerBasis (G \ {0}) I ↔ m.IsGroebnerBasis G I := by
  simp only [isGroebnerBasis_iff, m.span_leadingTerm_sdiff_singleton_zero,
    Set.sdiff_singleton_subset_iff, Set.insert_eq_of_mem (show (0 : MvPolynomial σ R) ∈ (I : Set _)
      from I.zero_mem)]

/-- The leading monomial of every nonzero element of `I` is divisible by the leading monomial of a
nonzero element of a Gröbner basis of `I`. -/
theorem IsGroebnerBasis.exists_degree_le_degree (h : m.IsGroebnerBasis G I)
    {p : MvPolynomial σ R} (hp : p ∈ I) (hp0 : p ≠ 0) :
    ∃ g ∈ G, g ≠ 0 ∧ m.degree g ≤ m.degree p := by
  refine exists_degree_le_of_mem_span_leadingTerm
    (h.span_leadingTerm_image ▸ Ideal.subset_span ⟨p, hp, rfl⟩ : m.leadingTerm p ∈ _) ?_
  rw [m.support_leadingTerm' hp0]
  exact Finset.mem_singleton_self _

/-- No monomial of a remainder on division by a Gröbner basis of `I` is divisible by the leading
monomial of a nonzero element of `I`. -/
theorem IsGroebnerBasis.not_degree_le_of_isRemainder (h : m.IsGroebnerBasis G I)
    (hr : m.IsRemainder f G r) {c : σ →₀ ℕ} (hc : c ∈ r.support) {p : MvPolynomial σ R}
    (hp : p ∈ I) (hp0 : p ≠ 0) : ¬ m.degree p ≤ c := fun hle ↦
  let ⟨_, hg, hg0, hgp⟩ := h.exists_degree_le_degree hp hp0
  hr.not_degree_le hc hg hg0 (hgp.trans hle)

/-- A subset `G` of `I` whose nonzero members have unit leading coefficients is a Gröbner basis of
`I` if and only if the leading monomial of every nonzero element of `I` is divisible by the
leading monomial of a nonzero element of `G`. -/
theorem isGroebnerBasis_iff_forall_exists_degree_le_degree
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis G I ↔
      G ⊆ I ∧ ∀ p ∈ I, p ≠ 0 → ∃ g ∈ G, g ≠ 0 ∧ m.degree g ≤ m.degree p := by
  refine ⟨fun h ↦ ⟨h.subset, fun p hp hp0 ↦ h.exists_degree_le_degree hp hp0⟩,
    fun ⟨hGI, hdeg⟩ ↦ .mk hGI (le_antisymm ?_ (Ideal.span_mono (Set.image_mono hGI)))⟩
  rw [Ideal.span_le, Set.image_subset_iff]
  intro p hp
  rcases eq_or_ne p 0 with rfl | hp0
  · simp
  obtain ⟨g, hgG, hg0, hgp⟩ := hdeg p hp hp0
  -- `lt p = (lc p / lc g) X^(deg p - deg g) * lt g`.
  have hu := hG g hgG hg0
  have hlt : m.leadingTerm p = monomial (m.degree p - m.degree g)
      (m.leadingCoeff p * ↑hu.unit⁻¹) * m.leadingTerm g := by
    simp [leadingTerm, monomial_mul_monomial, tsub_add_cancel_of_le hgp, mul_assoc]
  rw [Set.mem_preimage, SetLike.mem_coe, hlt]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨g, hgG, rfl⟩)

/-- If the nonzero members of `G` have unit leading coefficients, then so do the nonzero leading
terms of members of `G`. -/
theorem isUnit_leadingCoeff_of_mem_image_leadingTerm
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    ∀ p ∈ m.leadingTerm '' G, p ≠ 0 → IsUnit (m.leadingCoeff p) := by
  rintro _ ⟨g, hg, rfl⟩ hg0
  rw [leadingCoeff_leadingTerm]
  exact hG g hg (by rintro rfl; simp at hg0)

/-- The leading terms of a Gröbner basis `G` of `I` whose nonzero members have unit leading
coefficients form a Gröbner basis of the ideal of leading terms of `I`. -/
theorem IsGroebnerBasis.image_leadingTerm (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis (m.leadingTerm '' G) (Ideal.span (m.leadingTerm '' I)) := by
  refine (isGroebnerBasis_iff_forall_exists_degree_le_degree
    (isUnit_leadingCoeff_of_mem_image_leadingTerm hG)).2 ⟨?_, fun p hp hp0 ↦ ?_⟩
  · rw [h.span_leadingTerm_image]
    exact Ideal.subset_span
  · rw [h.span_leadingTerm_image] at hp
    obtain ⟨g, hg, hg0, hgp⟩ :=
      exists_degree_le_of_mem_span_leadingTerm hp (m.degree_mem_support hp0)
    exact ⟨m.leadingTerm g, ⟨g, hg, rfl⟩, (m.leadingTerm_eq_zero_iff g).not.2 hg0,
      (m.degree_leadingTerm g).symm ▸ hgp⟩

end CommSemiring

section CommRing

variable [CommRing R] {m} {f f₁ f₂ r r₁ r₂ : MvPolynomial σ R} {B G : Set (MvPolynomial σ R)}
  {I : Ideal (MvPolynomial σ R)}

/-- A polynomial differs from its remainders by an element of the ideal spanned by the divisors. -/
theorem IsRemainder.sub_mem_span (h : m.IsRemainder f B r) : f - r ∈ Ideal.span B := by
  obtain ⟨g, hf, -⟩ := h.exists_linearCombination
  rw [hf, add_sub_cancel_right, Finsupp.linearCombination_apply]
  exact Submodule.sum_mem _ fun b _ ↦ Submodule.smul_mem _ _ (Ideal.subset_span b.2)

/-- **Existence of remainders.** If every nonzero element of `B` has a unit leading coefficient,
then every polynomial has a remainder on division by `B`. -/
theorem exists_isRemainder (hB : ∀ b ∈ B, b ≠ 0 → IsUnit (m.leadingCoeff b))
    (f : MvPolynomial σ R) : ∃ r, m.IsRemainder f B r := by
  classical
  rcases eq_or_ne f 0 with rfl | hf
  · exact ⟨0, isRemainder_zero_left_iff.2 rfl⟩
  -- Divide by the nonzero elements of `B`, then extend the quotients by `0` to all of `B`.
  obtain ⟨g, r, hfgr, hdeg, hr⟩ := m.div_set (B := B \ {0}) (fun b hb ↦ hB b hb.1 hb.2) f
  refine ⟨r, ⟨g.mapDomain (Set.inclusion Set.sdiff_subset), ?_, fun b ↦ ?_⟩,
    fun c hc b hb hb0 ↦ hr c hc b ⟨hb, hb0⟩⟩
  · rwa [Finsupp.linearCombination_mapDomain]
  by_cases hb0 : (b : MvPolynomial σ R) = 0
  · simp [hb0]
  have hgb : g.mapDomain (Set.inclusion Set.sdiff_subset) b = g ⟨b, b.2, hb0⟩ :=
    Finsupp.mapDomain_apply_of_injective (Set.inclusion_injective _) g ⟨b, b.2, hb0⟩
  rw [hgb, ← map_add, ← withBotDegree_mul_of_left_mem_nonZeroDivisors
    (hB b b.2 hb0).mem_nonZeroDivisors, withBotDegree_le_withBotDegree_iff]
  exact ⟨hdeg ⟨b, b.2, hb0⟩, fun h ↦ absurd h hf⟩

/-- **Remainders modulo a Gröbner basis.** If `r₁` and `r₂` are remainders of `f₁` and `f₂` on
division by a Gröbner basis of `I`, then `f₁ - f₂ ∈ I` if and only if `r₁ = r₂`. -/
theorem IsGroebnerBasis.sub_mem_iff (h : m.IsGroebnerBasis G I) (h₁ : m.IsRemainder f₁ G r₁)
    (h₂ : m.IsRemainder f₂ G r₂) : f₁ - f₂ ∈ I ↔ r₁ = r₂ := by
  classical
  have hdiff : f₁ - f₂ - (r₁ - r₂) ∈ I := by
    have := Ideal.span_le.2 h.subset (Ideal.sub_mem _ h₁.sub_mem_span h₂.sub_mem_span)
    rwa [sub_sub_sub_comm] at this
  rw [← sub_add_cancel (f₁ - f₂) (r₁ - r₂), I.add_mem_iff_right hdiff]
  refine ⟨fun hr ↦ by_contra fun hne ↦ ?_, fun hr ↦ by simp [hr]⟩
  -- The leading monomial of the nonzero `r₁ - r₂ ∈ I` would be a reducible monomial of `r₁`
  -- or `r₂`.
  have hne' : r₁ - r₂ ≠ 0 := sub_ne_zero.2 hne
  obtain ⟨g, hgG, hg0, hgd⟩ := h.exists_degree_le_degree hr hne'
  rcases Finset.mem_union.1 (support_sub σ r₁ r₂ (m.degree_mem_support hne')) with hc | hc
  · exact h₁.not_degree_le hc hgG hg0 hgd
  · exact h₂.not_degree_le hc hgG hg0 hgd

/-- **Uniqueness of remainders.** Remainders on division by a Gröbner basis are unique. -/
theorem IsGroebnerBasis.eq_of_isRemainder (h : m.IsGroebnerBasis G I) (h₁ : m.IsRemainder f G r₁)
    (h₂ : m.IsRemainder f G r₂) : r₁ = r₂ :=
  (h.sub_mem_iff h₁ h₂).1 (by simp)

/-- **Ideal membership.** A remainder on division by a Gröbner basis of `I` vanishes if and only
if the divided polynomial lies in `I`. -/
theorem IsGroebnerBasis.remainder_eq_zero_iff_mem (h : m.IsGroebnerBasis G I)
    (hr : m.IsRemainder f G r) : r = 0 ↔ f ∈ I := by
  simpa using (h.sub_mem_iff hr (isRemainder_zero_left_iff.2 rfl)).symm

/-- If `r` is a remainder of `X^a` on division by a Gröbner basis of `I`, and `a` is the leading
exponent of a nonzero element of `I`, then `X^a - r` is a nonzero monic element of `I` with
leading exponent `a`. -/
theorem IsGroebnerBasis.monic_monomial_sub_of_isRemainder (h : m.IsGroebnerBasis G I)
    {a : σ →₀ ℕ} (hr : m.IsRemainder (monomial a 1) G r)
    {p : MvPolynomial σ R} (hp : p ∈ I) (hp0 : p ≠ 0) (hpa : m.degree p = a) :
    monomial a 1 - r ∈ I ∧ monomial a 1 - r ≠ 0 ∧ m.degree (monomial a 1 - r) = a ∧
      m.Monic (monomial a 1 - r) := by
  classical
  have hmem : monomial a 1 - r ∈ I := Ideal.span_le.2 h.subset hr.sub_mem_span
  have hcoeff : (monomial a 1 - r).coeff a = 1 := by
    have : a ∉ r.support := fun hc ↦ h.not_degree_le_of_isRemainder hr hc hp hp0 hpa.le
    simp [notMem_support_iff.1 this]
  have hne : monomial a 1 - r ≠ 0 := by
    have : Nontrivial R := nontrivial_of_ne _ _ (m.leadingCoeff_ne_zero_iff.2 hp0)
    exact fun h0 ↦ by simp [h0] at hcoeff
  -- The leading monomial is not a monomial of `r`, so it is `a`.
  have hdeg : m.degree (monomial a 1 - r) = a := by
    rcases Finset.mem_union.1 (support_sub σ _ _ (m.degree_mem_support hne)) with hc | hc
    · exact Finset.mem_singleton.1 (support_monomial_subset hc)
    · exact absurd le_rfl (h.not_degree_le_of_isRemainder hr hc hmem hne)
  exact ⟨hmem, hne, hdeg, by rw [Monic, leadingCoeff, hdeg, hcoeff]⟩

variable (m) in
/-- The polynomials `∑ g_b * b` over `b ∈ B` with `deg b + deg g_b ≤ d` for every `b`: the
`R`-span of the monomial multiples of elements of `B` of degree at most `d`. -/
private def boundedSpan (B : Set (MvPolynomial σ R)) (d : WithBot m.syn) :
    Submodule R (MvPolynomial σ R) where
  carrier := {p | ∃ g : B →₀ MvPolynomial σ R,
    p = Finsupp.linearCombination _ (fun b : B ↦ (b : MvPolynomial σ R)) g ∧
    ∀ b : B, m.toWithBotSyn (m.withBotDegree (b : MvPolynomial σ R)) +
      m.toWithBotSyn (m.withBotDegree (g b)) ≤ d}
  zero_mem' := ⟨0, by simp, by simp⟩
  add_mem' := by
    rintro _ _ ⟨g, rfl, hg⟩ ⟨g', rfl, hg'⟩
    refine ⟨g + g', by rw [map_add], fun b ↦ ?_⟩
    refine (add_le_add_right (m.withBotDegree_add_le _ _) _).trans ?_
    rw [← max_add_add_left]
    exact max_le (hg b) (hg' b)
  smul_mem' := by
    rintro r _ ⟨g, rfl, hg⟩
    refine ⟨r • g, by rw [LinearMap.map_smul_of_tower], fun b ↦ le_trans ?_ (hg b)⟩
    exact add_le_add_right (m.withBotDegree_le_withBotDegree_of_support_subset support_smul) _

/-- `boundedSpan m B d` is monotone in the bound `d`. -/
private theorem boundedSpan_mono {d d' : WithBot m.syn} (hdd' : d ≤ d') :
    boundedSpan m B d ≤ boundedSpan m B d' := by
  rintro _ ⟨g, rfl, hg⟩
  exact ⟨g, rfl, fun b ↦ (hg b).trans hdd'⟩

/-- An element of `boundedSpan m B d` lies in the ideal spanned by `B`. -/
private theorem mem_span_of_mem_boundedSpan {d : WithBot m.syn} {p : MvPolynomial σ R}
    (hp : p ∈ boundedSpan m B d) : p ∈ Ideal.span B := by
  obtain ⟨g, rfl, -⟩ := hp
  exact (Finsupp.mem_span_iff_linearCombination _ _ _).2 ⟨g, rfl⟩

/-- An element of `boundedSpan m B d` has degree at most `d`. -/
private theorem withBotDegree_le_of_mem_boundedSpan {d : WithBot m.syn} {p : MvPolynomial σ R}
    (hp : p ∈ boundedSpan m B d) : m.toWithBotSyn (m.withBotDegree p) ≤ d := by
  obtain ⟨g, rfl, hg⟩ := hp
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine m.withBotDegree_sum_le.trans (Finset.sup_le fun b _ ↦ ?_)
  exact (m.toWithBotSyn_withBotDegree_mul_le _ _).trans ((add_comm _ _).trans_le (hg b))

/-- An element of the ideal of `R` spanned by the leading coefficients of those `g ∈ G` with
`deg g ≤ D` is the coefficient of `X^D` in an element of `boundedSpan m G D`. -/
private theorem span_leadingCoeff_le_map_boundedSpan (D : σ →₀ ℕ) :
    Ideal.span (m.leadingCoeff '' {g ∈ G | m.degree g ≤ D}) ≤
      (boundedSpan m G (m.toSyn D)).map (lcoeff R D) := by
  classical
  rw [Ideal.span_le]
  rintro _ ⟨g, ⟨hgG, hgD⟩, rfl⟩
  -- `lc g` is the `D` coefficient of `X^(D - deg g) * g`.
  refine ⟨monomial (D - m.degree g) 1 * g,
    ⟨Finsupp.single ⟨g, hgG⟩ (monomial (D - m.degree g) 1), by simp, fun b ↦ ?_⟩, ?_⟩
  · rw [Finsupp.single_apply]
    split_ifs with h
    · subst h
      refine (add_le_add (m.toWithBotSyn_withBotDegree_le_toSyn_degree _)
        ((m.toWithBotSyn_withBotDegree_le_toSyn_degree _).trans
          (WithBot.coe_le_coe.2 (m.degree_monomial_le _)))).trans_eq ?_
      rw [← WithBot.coe_add, ← map_add, add_tsub_cancel_of_le hgD]
    · simp
  · simp [coeff_monomial_mul', tsub_tsub_cancel_of_le hgD, leadingCoeff]

/-- **Standard representations** (Adams–Loustaunau, Theorem 4.1.12): every element `f` of `I` is
`∑ g_b * b` over a Gröbner basis `G` of `I` with `deg b + deg g_b ≤ deg f` for every `b`.
No condition on leading coefficients is needed. -/
private theorem IsGroebnerBasis.mem_boundedSpan (h : m.IsGroebnerBasis G I) (hf : f ∈ I) :
    f ∈ boundedSpan m G (m.toWithBotSyn (m.withBotDegree f)) := by
  classical
  -- Induct on the degree of `f` in the well-founded synonym order.
  induction hd : m.toWithBotSyn (m.withBotDegree f) using WellFoundedLT.induction
    generalizing f with
  | ind d ih =>
  subst hd
  rcases eq_or_ne f 0 with rfl | hf0
  · exact zero_mem _
  have hW : m.toWithBotSyn (m.withBotDegree f) = m.toSyn (m.degree f) := by
    rw [(m.withBotDegree_eq_coe_degree_iff f).2 hf0, toWithBotSyn_apply_coe]
  -- Some `q ∈ boundedSpan m G (deg f)` has the same leading coefficient as `f`, and then
  -- `f - q ∈ I` has smaller degree than `f`.
  have hlt : m.leadingTerm f ∈ Ideal.span (m.leadingTerm '' G) :=
    h.span_leadingTerm_image ▸ Ideal.subset_span ⟨f, hf, rfl⟩
  have hc := coeff_mem_span_leadingCoeff hlt (m.degree f)
  rw [leadingTerm, coeff_monomial, ite_eq_left rfl] at hc
  obtain ⟨q, hq, hqf⟩ := span_leadingCoeff_le_map_boundedSpan (m.degree f) hc
  rw [← hW] at hq
  have hdeg := m.withBotDegree_sub_lt hf0 (withBotDegree_le_of_mem_boundedSpan hq) hqf
  have hqI : q ∈ I := Ideal.span_le.2 h.subset (mem_span_of_mem_boundedSpan hq)
  have := add_mem (boundedSpan_mono hdeg.le (ih _ hdeg (sub_mem hf hqI) rfl)) hq
  rwa [sub_add_cancel] at this

/-- For a Gröbner basis `G` of `I`, `0` is a remainder of `f` on division by `G` exactly when
`f ∈ I`. No condition on the leading coefficients of `G` is needed. -/
theorem IsGroebnerBasis.isRemainder_zero_iff_mem (h : m.IsGroebnerBasis G I) :
    m.IsRemainder f G 0 ↔ f ∈ I := by
  refine ⟨fun hr ↦ (h.remainder_eq_zero_iff_mem hr).1 rfl, fun hf ↦ ?_⟩
  obtain ⟨g, hg, hdeg⟩ := h.mem_boundedSpan hf
  exact ⟨⟨g, by rwa [add_zero], hdeg⟩, by simp⟩

/-- A Gröbner basis of `I` generates `I`. -/
theorem IsGroebnerBasis.ideal_eq_span (h : m.IsGroebnerBasis G I) : I = Ideal.span G := by
  refine le_antisymm (fun f hf ↦ ?_) (Ideal.span_le.2 h.subset)
  simpa using (h.isRemainder_zero_iff_mem.2 hf).sub_mem_span

/-- Remainders on division by a Gröbner basis whose nonzero members have unit leading
coefficients exist and are unique. -/
theorem IsGroebnerBasis.existsUnique_isRemainder (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) (f : MvPolynomial σ R) :
    ∃! r, m.IsRemainder f G r :=
  (exists_isRemainder hG f).elim fun r hr ↦ ⟨r, hr, fun _ hr' ↦ h.eq_of_isRemainder hr' hr⟩

/-- A subset `G` of `I` is a Gröbner basis of `I` if and only if every element of `I` has remainder
`0` on division by `G`. -/
theorem isGroebnerBasis_iff_isRemainder_zero :
    m.IsGroebnerBasis G I ↔ G ⊆ I ∧ ∀ f ∈ I, m.IsRemainder f G 0 := by
  refine ⟨fun h ↦ ⟨h.subset, fun f ↦ h.isRemainder_zero_iff_mem.2⟩, fun ⟨hGI, h0⟩ ↦ .mk hGI ?_⟩
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_mono (Set.image_mono hGI))
  rintro _ ⟨f, hf, rfl⟩
  exact leadingTerm_mem_span_leadingTerm_of_isRemainder_zero (h0 f hf)

end CommRing

end MonomialOrder

end

end
end

/- BEGIN EXACT BODY: FourPapers.Symmetric.Vendor.RingTheory.MvPolynomial.RestrictSupport -/
section

section
noncomputable section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The monomial basis of polynomials with restricted support

Mathlib's `MvPolynomial.basisRestrictSupport R s` is the basis of `MvPolynomial.restrictSupport R s`
indexed by `s`. This file records its coordinates (the coefficients) and its basis vectors (the
monomials with coefficient `1`).
-/


namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R] {s : Set (σ →₀ ℕ)}

/-- The coordinates of a polynomial in `basisRestrictSupport` are its coefficients. -/
@[simp]
theorem basisRestrictSupport_repr_apply (p : restrictSupport R s) (c : s) :
    (basisRestrictSupport R s).repr p c = (p : MvPolynomial σ R).coeff c :=
  -- `basisRestrictSupport` is defined through `AddMonoidAlgebra.supportedEquivFinsupp`, which
  -- reads off coefficients.
  rfl

/-- The basis vectors of `basisRestrictSupport` are the monomials with coefficient `1`. -/
@[simp]
theorem basisRestrictSupport_apply_coe (c : s) :
    (basisRestrictSupport R s c : MvPolynomial σ R) = monomial (c : σ →₀ ℕ) 1 := by
  classical
  have hc : monomial (c : σ →₀ ℕ) (1 : R) ∈ restrictSupport R s := by simp
  suffices basisRestrictSupport R s c = ⟨_, hc⟩ from congrArg Subtype.val this
  refine (basisRestrictSupport R s).repr.injective (Finsupp.ext fun d ↦ ?_)
  simp [Finsupp.single_apply, coeff_monomial, Subtype.ext_iff]

end MvPolynomial

end

end
end


end
