module
public import SegreVerified.Stage028.HomogeneousSections
public import SegreVerified.Stage027.TensorSections
import all Lean.Util.CollectAxioms

set_option Elab.async false
set_option linter.all false

#eval do
  let toolchain ← IO.FS.readFile "lean-toolchain"
  let manifest ← IO.FS.readFile "lake-manifest.json"
  IO.println ("SEGRE_PUBLIC_ENVIRONMENT_BEGIN\n" ++ Lean.versionString ++ "\n" ++
    Lean.githash ++ "\n" ++ toolchain.trimAscii.toString ++ "\n" ++ manifest ++
    "\nSEGRE_PUBLIC_ENVIRONMENT_END")

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless env.header.trustLevel == 0 do
    throwError "The retained source check requires kernel trust level zero"
  let imported := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  let rows := CollectAxioms.runM (env.setExporting false) do
    #[``Nat.add_comm, ``Nat.zero_add].mapM fun name =>
      return (name, ← CollectAxioms.collectAndGet imported.find? name)
  for (name, axioms) in rows do
    unless (env.checked.get.find? name).isSome do throwError "Unchecked smoke target: {name}"
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved shared-collector smoke axiom: {ax}"
  logInfo "SEGRE_SHARED_COLLECTOR_READY"


set_option Elab.async false
set_option maxErrors 0
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section ProbeLayer391



/-!
# Singular-vector geometry and all-format spanning theorems

The named sections preserve the original proof stages and local scopes.
-/

@[expose] public section

-- Emit compilation progress immediately while checking this large unit.
set_option stderrAsMessages false
-- Style linting is separate from elaboration, kernel checking, and the axiom audit.
set_option linter.all false
noncomputable section
set_option autoImplicit false


section SegreGlobalCriticalSections

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE Stage028.PullbackSections"
  out.flush

/-!
# Global critical sections and their literal chart equations

The named sections preserve the original proof stages and local scopes.
-/



section SegreFinitePullbackSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

/-!
# The full product comparison on actual pure sections

The canonical recursive external-product sections and the finite tensor of
actual pulled-back sections agree under the actual product comparison.
The proof includes the identity projection, pullback of the tensor unit,
all tensor comparisons, and all composition isomorphisms.

-/

set_option autoImplicit false

namespace PaperVerification.Segre.FinitePullbackSections

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open SheafCoefficientContraction SheafCoefficientComplex FiniteTensorSections
open PullbackTensorSections FixedProductProjections FixedProductCohomology
open FiniteGlobalSections ExternalSections
open scoped TensorProduct

universe u v w


/-- Composition evaluated in the native scheme section spaces. -/
private theorem hom_comp_app_apply {Y : Scheme.{u}} {M N P : Y.Modules}
    (f : M ⟶ N) (g : N ⟶ P) (U : Y.Opens) (s : Γ(M,U)) :
    (f ≫ g).app U s = g.app U (f.app U s) := rfl

/-- The identity acts as the identity on every actual section. -/
private theorem hom_id_app_apply {Y : Scheme.{u}} (M : Y.Modules)
    (U : Y.Opens) (s : Γ(M,U)) : Scheme.Modules.Hom.app (𝟙 M) U s = s := rfl

/-- Naturality in the native scheme-module presentation, before any
concrete product scheme is substituted. -/
private theorem tensorSection_map_native {Y : Scheme.{u}}
    {M M' N N' : Y.Modules} (f : M ⟶ M') (g : N ⟶ N')
    (U : Y.Opens) (s : Γ(M,U)) (t : Γ(N,U)) :
    (f ⊗ₘ g).app U (tensorSection Y.sheaf M N (op U) s t) =
      tensorSection Y.sheaf M' N' (op U) (f.app U s) (g.app U t) :=
  SheafCoefficientComplex.tensorSection_map Y.sheaf f g (op U) s t

/-- The finite factorwise comparison in native scheme section spaces. -/
private theorem tensorFamilyIso_section_native {Y : Scheme.{u}} {l : ℕ}
    {M N : Fin l → Y.Modules} (e : ∀ i, M i ≅ N i)
    (U : Y.Opens) (s : ∀ i, Γ(M i,U)) :
    (tensorFamilyIso e).hom.app U (finiteTensorSection Y.sheaf M (op U) s) =
      finiteTensorSection Y.sheaf N (op U) (fun i => (e i).hom.app U (s i)) :=
  FiniteTensorSections.tensorFamilyIso_section Y.sheaf e (op U) s

/-- The identity-pullback comparison is the identity on the actual pulled
section, not merely some isomorphism of the corresponding section spaces. -/
theorem pullbackId_section {Y : Scheme.{u}} (M : Y.Modules)
    (U : Y.Opens) (s : Γ(M,U)) :
    ((pullbackId Y).hom.app M).app U (Scheme.Hom.pullbackSections (𝟙 Y) M U s)=s := by
  have h := CategoryTheory.unit_conjugateEquiv Adjunction.id
    (pullbackPushforwardAdjunction (𝟙 Y)) (pullbackId Y).hom M
  rw [conjugateEquiv_pullbackId_hom] at h
  simp only [Adjunction.id_unit, NatTrans.id_app, Category.id_comp] at h
  have hs := congrArg (β := Γ(M, U))
    (fun f : M ⟶ (pushforward (𝟙 Y)).obj M => f.app U s) h
  rw [Scheme.Hom.pullbackSections_apply]
  calc
    ((pullbackId Y).hom.app M).app U
        (((pullbackPushforwardAdjunction (𝟙 Y)).unit.app M).app U s) =
      ((pullbackPushforwardAdjunction (𝟙 Y)).unit.app M ≫
        (pushforward (𝟙 Y)).map ((pullbackId Y).hom.app M)).app U s := rfl
    _ = ((pushforwardId Y).inv.app M).app U s := hs.symm
    _ = s := by
      rw [pushforwardId_inv_app_app]
      rfl

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PULLBACK_SECTIONS pullbackId_section"
  out.flush

theorem pullbackId_inv_section {Y : Scheme.{u}} (M : Y.Modules)
    (U : Y.Opens) (s : Γ(M,U)) :
    ((pullbackId Y).inv.app M).app U s =
      Scheme.Hom.pullbackSectionsLE (𝟙 Y) M U U (by simp) s := by
  let e := (pullbackId Y).app M
  let z := Scheme.Hom.pullbackSections (𝟙 Y) M U s
  have hz : e.hom.app U z = s := pullbackId_section M U s
  calc
    e.inv.app U s = e.inv.app U (e.hom.app U z) :=
      congrArg (fun y : Γ(M, U) => e.inv.app U y) hz.symm
    _ = z := by
      have hi := congrArg (β := Γ((Scheme.Modules.pullback (𝟙 Y)).obj M, U))
        (fun g : (Scheme.Modules.pullback (𝟙 Y)).obj M ⟶ (Scheme.Modules.pullback (𝟙 Y)).obj M =>
          g.app U z) e.hom_inv_id
      simpa only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app,
        ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using hi
    _ = Scheme.Hom.pullbackSectionsLE (𝟙 Y) M U U (by simp) s :=
      (Scheme.Hom.pullbackSectionsLE_self (𝟙 Y) M U s).symm

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PULLBACK_SECTIONS pullbackId_inv_section"
  out.flush

/-- The inverse right unitor inserts the genuine unit section. -/
theorem rightUnitor_inv_section {Y : Scheme.{u}} (M : Y.Modules)
    (U : Y.Opens) (m : Γ(M,U)) :
    (ρ_ M).inv.app U m =
      tensorSection Y.sheaf M (𝟙_ Y.Modules) (op U) m (1 : Γ(Y,U)) := by
  have h := tensorSection_rightUnitor Y.sheaf M (op U) m (1 : Γ(Y,U))
  rw [one_smul] at h
  calc
    (ρ_ M).inv.app U m =
        (ρ_ M).inv.app U ((ρ_ M).hom.app U
          (tensorSection Y.sheaf M (𝟙_ Y.Modules) (op U) m (1 : Γ(Y,U)))) :=
      congrArg (fun z : Γ(M,U) => (ρ_ M).inv.app U z) h.symm
    _ = tensorSection Y.sheaf M (𝟙_ Y.Modules) (op U) m (1 : Γ(Y,U)) := by
      have hi := congrArg (β := Γ(M ⊗ (𝟙_ Y.Modules), U))
        (fun g : M ⊗ (𝟙_ Y.Modules) ⟶ M ⊗ (𝟙_ Y.Modules) =>
          g.app U (tensorSection Y.sheaf M (𝟙_ Y.Modules) (op U) m (1 : Γ(Y,U))))
        (ρ_ M).hom_inv_id
      simpa only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app,
        ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using hi

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PULLBACK_SECTIONS rightUnitor_inv_section"
  out.flush

/-- Pullback of the entire finite pure section, including the unit in
length zero, has the expected canonical formula. -/
theorem pullbackFiniteTensorIso_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    {l : ℕ} (M : Fin l → Y.Modules) (hM : ∀ i,(M i).IsQuasicoherent)
    (U : Y.Opens) (V : X.Opens) (hV : V≤f ⁻¹ᵁ U) (s : ∀ i,Γ(M i,U)) :
    (pullbackFiniteTensorIso f M hM).hom.app V
      (f.pullbackSectionsLE (FiniteTensor.tensorObj M) U V hV
        (finiteTensorSection Y.sheaf M (op U) s)) =
      finiteTensorSection X.sheaf (fun i => (Scheme.Modules.pullback f).obj (M i)) (op V)
        (fun i => f.pullbackSectionsLE (M i) U V hV (s i)) := by
  induction l with
  | zero =>
      simpa only [pullbackFiniteTensorIso, finiteTensorSection,
        FiniteTensor.tensorObj, map_one] using
        pullbackUnit_sectionLE f U V hV (1 : Γ(Y,U))
  | succ l ih =>
      let Mt : Fin l → Y.Modules := fun i => M i.succ
      let hMt : ∀ i, (Mt i).IsQuasicoherent := fun i => hM i.succ
      let st : ∀ i, Γ(Mt i, U) := fun i => s i.succ
      letI := hM 0
      letI := FixedProductProjections.finiteTensor_quasicoherent Mt hMt
      let H := (Scheme.Modules.pullback f).obj (M 0)
      let T := FiniteTensor.tensorObj Mt
      let Q : Fin l → X.Modules := fun i => (Scheme.Modules.pullback f).obj (Mt i)
      let et : (Scheme.Modules.pullback f).obj T ≅ FiniteTensor.tensorObj Q :=
        pullbackFiniteTensorIso f Mt hMt
      let p : Γ(H, V) := f.pullbackSectionsLE (M 0) U V hV (s 0)
      let q : Γ((Scheme.Modules.pullback f).obj T, V) :=
        f.pullbackSectionsLE T U V hV (finiteTensorSection Y.sheaf Mt (op U) st)
      have ht : et.hom.app V q =
          finiteTensorSection X.sheaf Q (op V)
            (fun i => f.pullbackSectionsLE (Mt i) U V hV (st i)) :=
        ih Mt hMt st
      have hδ := pullbackTensor_sectionLE f (M 0) T U V hV (s 0)
        (finiteTensorSection Y.sheaf Mt (op U) st)
      simp only [pullbackFiniteTensorIso, finiteTensorSection, FiniteTensor.tensorObj,
        Iso.trans_hom, tensorIso_hom, asIso_hom, hom_comp_app_apply, Iso.refl_hom]
      exact (congrArg
        (fun z : Γ(H ⊗ (Scheme.Modules.pullback f).obj T, V) =>
          (𝟙 H ⊗ₘ et.hom).app V z) hδ).trans
        ((tensorSection_map_native (𝟙 H) et.hom V p q).trans
          (congrArg₂ (tensorSection X.sheaf H (FiniteTensor.tensorObj Q) (op V))
            (hom_id_app_apply H V p) ht))

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PULLBACK_SECTIONS pullbackFiniteTensorIso_section"
  out.flush

/-- Equal-open transport is the unique restriction along that inclusion.
Comparing arrows in the thin category of opens avoids eliminating an equality
inside a concrete product scheme. -/
theorem map_eqToIso_op_inv_generic {Y : Scheme.{u}}
    {C : Type v} [Category.{w} C] (F : Y.Opensᵒᵖ ⥤ C)
    {U V : Y.Opens} (h : U = V) :
    (F.mapIso (eqToIso h).op).inv = F.map (homOfLE h.ge).op := by
  change F.map ((eqToIso h).inv.op) = F.map (homOfLE h.ge).op
  exact congrArg (fun f : op U ⟶ op V => F.map f) (Subsingleton.elim _ _)

/-- On presheaf sections a transport through an equality of opens is the
literal restriction along the equal inclusion. -/
theorem map_eqToIso_op_inv_apply {Y : Scheme.{u}} (F : Y.Opensᵒᵖ ⥤ ModuleCat.{u} ℤ)
    {U V : Y.Opens} (h : U=V) (s : F.obj (op U)) :
    (F.mapIso (eqToIso h).op).inv s=F.map (homOfLE h.ge).op s := by
  subst V
  simp

variable {K : Type u} [Field K]

/-- Transporting the top external-product rectangle to the top open gives
precisely the tensor of the two genuine pulled-back sections.  The proof is
made on arbitrary schemes, before specializing to a chosen product scheme. -/
theorem externalProduct_top_transport (R : Type u) [CommRing R]
    {X Y Z : Scheme.{u}} [X.Over (Spec (.of R))]
    [Y.Over (Spec (.of R))] [Z.Over (Spec (.of R))]
    (f : Z ⟶ X) (g : Z ⟶ Y)
    [f.IsOver (Spec (.of R))] [g.IsOver (Spec (.of R))]
    (M : X.Modules) (N : Y.Modules)
    (h : rectangle f g ⊤ ⊤ = (⊤ : Z.Opens))
    (m : sections R M ⊤) (n : sections R N ⊤) :
    ((((sectionsBasePresheafFunctor R).obj (ExternalSections.externalTensor f g M N)).mapIso
      (eqToIso h).op).inv) (externalProduct R f g M N ⊤ ⊤ (m ⊗ₜ[R] n)) =
      tensorSection Z.sheaf ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback g).obj N) (op ⊤)
        (f.pullbackSectionsLE M ⊤ ⊤ (by simp) m)
        (g.pullbackSectionsLE N ⊤ ⊤ (by simp) n) := by
  let MP := (Scheme.Modules.pullback f).obj M
  let NP := (Scheme.Modules.pullback g).obj N
  let U := rectangle f g ⊤ ⊤
  let F := (sectionsBasePresheafFunctor R).obj (MP ⊗ NP)
  let z : F.obj (op U) := externalProduct R f g M N ⊤ ⊤ (m ⊗ₜ[R] n)
  have heq := congrArg (fun a : F.obj (op U) ⟶ F.obj (op ⊤) => a z)
    (map_eqToIso_op_inv_generic F h)
  have hm := pullbackBaseLE_restrict R f M
    (U := ⊤) (U' := ⊤) (W := U) (W' := ⊤)
    le_rfl h.ge inf_le_left (by simp) m
  have hn := pullbackBaseLE_restrict R g N
    (U := ⊤) (U' := ⊤) (W := U) (W' := ⊤)
    le_rfl h.ge inf_le_right (by simp) n
  have hm_id : (((sectionsBasePresheafFunctor R).obj M).map
      (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_rfl)).op) m = m := by
    change (((sectionsBasePresheafFunctor R).obj M).map (𝟙 (op ⊤))) m = m
    rw [CategoryTheory.Functor.map_id]
    rfl
  have hn_id : (((sectionsBasePresheafFunctor R).obj N).map
      (homOfLE (show (⊤ : Y.Opens) ≤ ⊤ from le_rfl)).op) n = n := by
    change (((sectionsBasePresheafFunctor R).obj N).map (𝟙 (op ⊤))) n = n
    rw [CategoryTheory.Functor.map_id]
    rfl
  have hm' := hm.trans (congrArg (pullbackBaseLE R f M ⊤ ⊤ (by simp)) hm_id)
  have hn' := hn.trans (congrArg (pullbackBaseLE R g N ⊤ ⊤ (by simp)) hn_id)
  calc
    _ = F.map (homOfLE h.ge).op z := heq
    _ = F.map (homOfLE h.ge).op
        (sectionProduct R MP NP U
          (pullbackBaseLE R f M ⊤ U inf_le_left m)
          (pullbackBaseLE R g N ⊤ U inf_le_right n)) :=
      congrArg (fun w : F.obj (op U) => F.map (homOfLE h.ge).op w)
        (externalProduct_tmul R f g M N ⊤ ⊤ m n)
    _ = sectionProduct R MP NP ⊤
        ((((sectionsBasePresheafFunctor R).obj MP).map (homOfLE h.ge).op)
          (pullbackBaseLE R f M ⊤ U inf_le_left m))
        ((((sectionsBasePresheafFunctor R).obj NP).map (homOfLE h.ge).op)
          (pullbackBaseLE R g N ⊤ U inf_le_right n)) :=
      sectionProduct_restrict R MP NP (homOfLE h.ge)
        (pullbackBaseLE R f M ⊤ U inf_le_left m)
        (pullbackBaseLE R g N ⊤ U inf_le_right n)
    _ = sectionProduct R MP NP ⊤
        (pullbackBaseLE R f M ⊤ ⊤ (by simp) m)
        (pullbackBaseLE R g N ⊤ ⊤ (by simp) n) :=
      congrArg₂ (fun x : sections R MP ⊤ => fun y : sections R NP ⊤ =>
        sectionProduct R MP NP ⊤ x y) hm' hn'
    _ = sectionProduct R MP NP ⊤
        (f.pullbackSectionsLE M ⊤ ⊤ (by simp) m)
        (g.pullbackSectionsLE N ⊤ ⊤ (by simp) n) :=
      congrArg₂ (fun x : sections R MP ⊤ => fun y : sections R NP ⊤ =>
        sectionProduct R MP NP ⊤ x y)
        (pullbackBaseLE_apply R f M ⊤ ⊤ (by simp) m)
        (pullbackBaseLE_apply R g N ⊤ ⊤ (by simp) n)
    _ = _ := sectionProduct_apply R MP NP ⊤
      (f.pullbackSectionsLE M ⊤ ⊤ (by simp) m)
      (g.pullbackSectionsLE N ⊤ ⊤ (by simp) n)

/-- The binary comparison, expressed directly in terms of the two actual
pulled-back global sections over the actual top open. -/
theorem binaryExternalSection_formula (A B : CoveredScheme K)
    (M : A.scheme.Modules) (N : B.scheme.Modules)
    (m : sections K M ⊤) (n : sections K N ⊤) :
    binaryExternalSection A B M N m n=
      tensorSection (CoveredScheme.product A B).scheme.sheaf
        ((Scheme.Modules.pullback (pullback.fst A.toBase B.toBase)).obj M)
        ((Scheme.Modules.pullback (pullback.snd A.toBase B.toBase)).obj N) (op ⊤)
        ((pullback.fst A.toBase B.toBase).pullbackSectionsLE M ⊤ ⊤ (by simp) m)
        ((pullback.snd A.toBase B.toBase).pullbackSectionsLE N ⊤ ⊤ (by simp) n) := by
  let p := pullback.fst A.toBase B.toBase
  let q := pullback.snd A.toBase B.toBase
  letI : (pullback A.toBase B.toBase).Over (Spec (.of K)) := ⟨p ≫ A.toBase⟩
  letI : p.IsOver (Spec (.of K)) := ⟨rfl⟩
  letI : q.IsOver (Spec (.of K)) :=
    ⟨(pullback.condition (f := A.toBase) (g := B.toBase)).symm⟩
  have ht : rectangle p q ⊤ ⊤ = (⊤ : (CoveredScheme.product A B).scheme.Opens) := by
    simp [rectangle]
  exact externalProduct_top_transport K p q M N ht m n

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PULLBACK_SECTIONS binaryExternalSection_formula"
  out.flush

/-- The canonical finite external-product sheaf comparison carries every
actual pure global section to precisely the tensor of its projection
pullbacks. Every factor and the final tensor unit are retained. -/
theorem finiteExternalTensorIso_section {l : ℕ}
    (A : Fin (l+1) → CoveredScheme K) (M : ∀ i,(A i).scheme.Modules)
    (hM : ∀ i,(M i).IsQuasicoherent) (s : ∀ i,sections K (M i) ⊤) :
    (finiteExternalTensorIso A M hM).hom.app ⊤ (finiteExternalSection A M s)=
      finiteTensorSection (CoveredScheme.finiteProduct A).scheme.sheaf
        (fun i => (Scheme.Modules.pullback (projection A i)).obj (M i)) (op ⊤)
        (fun i => (projection A i).pullbackSectionsLE (M i) ⊤ ⊤ (by simp) (s i)) := by
  induction l with
  | zero =>
      simp only [finiteExternalTensorIso, id_eq, finiteExternalSection,
        Iso.trans_hom, Iso.symm_hom, Iso.app_inv, hom_comp_app_apply,
        rightUnitor_inv_section, pullbackId_inv_section,
        finiteTensorSection, FiniteTensor.tensorObj, projection, Fin.cases_zero]
      exact congrArg
        (fun t : Γ((Scheme.Modules.pullback (𝟙 (A 0).scheme)).obj (M 0), ⊤) =>
          tensorSection (A 0).scheme.sheaf
            ((Scheme.Modules.pullback (𝟙 (A 0).scheme)).obj (M 0))
            (𝟙_ (A 0).scheme.Modules) (op ⊤) t (1 : Γ((A 0).scheme, ⊤)))
        (pullbackId_inv_section (M 0) ⊤ (s 0))
  | succ l ih =>
      let A' : Fin (l + 1) → CoveredScheme K := fun i => A i.succ
      let M' : ∀ i, (A' i).scheme.Modules := fun i => M i.succ
      let s' : ∀ i, sections K (M' i) ⊤ := fun i => s i.succ
      let hM' : ∀ i, (M' i).IsQuasicoherent := fun i => hM i.succ
      let B := CoveredScheme.finiteProduct A'
      let N := CoveredScheme.finiteExternalTensor A' M'
      let X := (CoveredScheme.finiteProduct A).scheme
      let p : X ⟶ (A 0).scheme := pullback.fst (A 0).toBase B.toBase
      let q : X ⟶ B.scheme := pullback.snd (A 0).toBase B.toBase
      let r : ∀ i : Fin (l + 1), B.scheme ⟶ (A' i).scheme :=
        fun i => projection A' i
      let P : Fin (l + 1) → B.scheme.Modules :=
        fun i => (Scheme.Modules.pullback (r i)).obj (M' i)
      have hP : ∀ i, (P i).IsQuasicoherent := by
        intro i
        letI : (M' i).IsQuasicoherent := hM' i
        change ((Scheme.Modules.pullback (r i)).obj (M' i)).IsQuasicoherent
        infer_instance
      let Q : Fin (l + 1) → X.Modules :=
        fun i => (Scheme.Modules.pullback (q ≫ r i)).obj (M' i)
      let sN : Γ(N, ⊤) := finiteExternalSection A' M' s'
      let sP : ∀ i, Γ(P i, ⊤) :=
        fun i => (r i).pullbackSectionsLE (M' i) ⊤ ⊤ (by simp) (s' i)
      let sQP : ∀ i, Γ((Scheme.Modules.pullback q).obj (P i), ⊤) :=
        fun i => q.pullbackSectionsLE (P i) ⊤ ⊤ (by simp) (sP i)
      let sQ : ∀ i, Γ(Q i, ⊤) :=
        fun i => (q ≫ r i).pullbackSectionsLE (M' i) ⊤ ⊤ (by simp) (s' i)
      let e0 : N ≅ FiniteTensor.tensorObj P :=
        finiteExternalTensorIso A' M' hM'
      let e1 := pullbackFiniteTensorIso q P hP
      let ef : ∀ i, (Scheme.Modules.pullback q).obj (P i) ≅ Q i :=
        fun i => (pullbackComp q (r i)).app (M' i)
      let e2 := tensorFamilyIso ef
      let e : (Scheme.Modules.pullback q).obj N ≅ FiniteTensor.tensorObj Q :=
        (Scheme.Modules.pullback q).mapIso e0 ≪≫ e1 ≪≫ e2
      have h0 : e0.hom.app ⊤ sN =
          finiteTensorSection B.scheme.sheaf P (op ⊤) sP :=
        ih A' M' hM' s'
      have hn : ((Scheme.Modules.pullback q).map e0.hom).app ⊤
          (q.pullbackSectionsLE N ⊤ ⊤ (by simp) sN) =
          q.pullbackSectionsLE (FiniteTensor.tensorObj P) ⊤ ⊤ (by simp)
            (finiteTensorSection B.scheme.sheaf P (op ⊤) sP) :=
        (Scheme.Hom.pullbackSectionsLE_naturality q N ⊤ ⊤ (by simp)
          e0.hom sN).trans
          (congrArg
            (q.pullbackSectionsLE (FiniteTensor.tensorObj P) ⊤ ⊤ (by simp)) h0)
      have hf : (fun i => (ef i).hom.app ⊤ (sQP i)) = sQ := by
        funext i
        exact Scheme.Hom.pullbackSectionsLE_comp_hom (r i) (M' i) ⊤ q ⊤
          (by simp) (by simp) (s' i)
      have ht : e.hom.app ⊤ (q.pullbackSectionsLE N ⊤ ⊤ (by simp) sN) =
          finiteTensorSection X.sheaf Q (op ⊤) sQ := by
        calc
          e.hom.app ⊤ (q.pullbackSectionsLE N ⊤ ⊤ (by simp) sN) =
              e2.hom.app ⊤ (e1.hom.app ⊤
                (((Scheme.Modules.pullback q).map e0.hom).app ⊤
                  (q.pullbackSectionsLE N ⊤ ⊤ (by simp) sN))) := rfl
          _ = e2.hom.app ⊤ (e1.hom.app ⊤
                (q.pullbackSectionsLE (FiniteTensor.tensorObj P) ⊤ ⊤ (by simp)
                  (finiteTensorSection B.scheme.sheaf P (op ⊤) sP))) :=
              congrArg
                (fun z : Γ((Scheme.Modules.pullback q).obj
                    (FiniteTensor.tensorObj P), ⊤) =>
                  e2.hom.app ⊤ (e1.hom.app ⊤ z)) hn
          _ = e2.hom.app ⊤
                (finiteTensorSection X.sheaf
                  (fun i => (Scheme.Modules.pullback q).obj (P i)) (op ⊤) sQP) :=
              congrArg (fun z => e2.hom.app ⊤ z)
                (pullbackFiniteTensorIso_section q P hP ⊤ ⊤ (by simp) sP)
          _ = finiteTensorSection X.sheaf Q (op ⊤)
                (fun i => (ef i).hom.app ⊤ (sQP i)) :=
              tensorFamilyIso_section_native ef ⊤ sQP
          _ = finiteTensorSection X.sheaf Q (op ⊤) sQ :=
              congrArg (finiteTensorSection X.sheaf Q (op ⊤)) hf
      let H := (Scheme.Modules.pullback p).obj (M 0)
      let headS : Γ(H, ⊤) := p.pullbackSectionsLE (M 0) ⊤ ⊤ (by simp) (s 0)
      have hw : (𝟙 H ⊗ₘ e.hom).app ⊤
          (tensorSection X.sheaf H ((Scheme.Modules.pullback q).obj N) (op ⊤)
            headS (q.pullbackSectionsLE N ⊤ ⊤ (by simp) sN)) =
          tensorSection X.sheaf H (FiniteTensor.tensorObj Q) (op ⊤) headS
            (finiteTensorSection X.sheaf Q (op ⊤) sQ) :=
        (tensorSection_map_native (𝟙 H) e.hom ⊤ headS
          (q.pullbackSectionsLE N ⊤ ⊤ (by simp) sN)).trans
          (congrArg₂
            (tensorSection X.sheaf H (FiniteTensor.tensorObj Q) (op ⊤))
            (hom_id_app_apply H ⊤ headS) ht)
      calc
        (finiteExternalTensorIso A M hM).hom.app ⊤ (finiteExternalSection A M s) =
            (𝟙 H ⊗ₘ e.hom).app ⊤
              (tensorSection X.sheaf H ((Scheme.Modules.pullback q).obj N) (op ⊤)
                headS (q.pullbackSectionsLE N ⊤ ⊤ (by simp) sN)) :=
          congrArg
            (fun z : Γ(H ⊗ (Scheme.Modules.pullback q).obj N, ⊤) =>
              (𝟙 H ⊗ₘ e.hom).app ⊤ z)
            (binaryExternalSection_formula (A 0) B (M 0) N (s 0) sN)
        _ = _ := hw

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PULLBACK_SECTIONS finiteExternalTensorIso_section"
  out.flush

/-- The canonical full H⁰ equivalence, now landing in the literal tensor
of factor pullbacks used by the critical functional. -/
def finitePullbackGlobalSectionsIso {l : ℕ}
    (A : Fin (l+1) → CoveredScheme K) (M : ∀ i,(A i).scheme.Modules)
    (hM : ∀ i,(M i).IsQuasicoherent) :
    FiniteTensor.tensorObj (fun i => sections K (M i) ⊤) ≅
      sections K (FiniteTensor.tensorObj (fun i => (Scheme.Modules.pullback (projection A i)).obj (M i))) ⊤ :=
  finiteGlobalSectionsIso A M hM ≪≫
    ((sectionsBasePresheafFunctor K).mapIso (finiteExternalTensorIso A M hM)).app (op ⊤)

/-- This fixes the entire H⁰ map on its pure-tensor generating family. -/
theorem finitePullbackGlobalSectionsIso_pure {l : ℕ}
    (A : Fin (l+1) → CoveredScheme K) (M : ∀ i,(A i).scheme.Modules)
    (hM : ∀ i,(M i).IsQuasicoherent) (s : ∀ i,sections K (M i) ⊤) :
    (finitePullbackGlobalSectionsIso A M hM).hom
      (FiniteTensorLinear.pure (fun i => sections K (M i) ⊤) s)=
      finiteTensorSection (CoveredScheme.finiteProduct A).scheme.sheaf
        (fun i => (Scheme.Modules.pullback (projection A i)).obj (M i)) (op ⊤)
        (fun i => (projection A i).pullbackSectionsLE (M i) ⊤ ⊤ (by simp) (s i)) := by
  rw [finitePullbackGlobalSectionsIso, Iso.trans_hom, ModuleCat.comp_apply,
    finiteGlobalSectionsIso_pure]
  exact finiteExternalTensorIso_section A M hM s

end PaperVerification.Segre.FinitePullbackSections

end SegreFinitePullbackSections


end SegreGlobalCriticalSections

end
end
end ProbeLayer391


/-! Future-only kernel audit for one exported mathematical stage.

Append to the stage being checked, with Lean.Util.CollectAxioms available through
both `public import Lean.Util.CollectAxioms` and `import all Lean.Util.CollectAxioms`
in that stage's header, as required by the reviewed FullFlattenedAudit.

Every new declaration in the checked kernel environment is included: public,
private, generated and vendored declarations receive the same direct-sorry and
transitive-axiom checks. This is evidence for this stage only. Later principal
theorems need not exist yet, and the final full principal audit remains required.

This preparation does not execute the audit, export a module or alter a proof.
-/

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  unless env.header.trustLevel == 0 do
    throwError "The stage kernel audit requires kernel trust level zero"
  let names := (env.checked.get.constants.foldStage2
    (fun (names : Array Name) name _ => names.push name) #[]).qsort Name.quickLt
  unless names.size > 0 do throwError "The stage mathematical module is empty"
  -- Reject direct proof holes before computing transitive axiom closures.
  -- The complete successful audit below remains unchanged.
  for name in names do
    let some info := env.checked.get.find? name
      | throwError "Authored declaration is not kernel checked: {name}"
    if let .axiomInfo _ := info then throwError "Authored axiom: {name}"
    if info.type.hasSorry || ((info.value? (allowOpaque := true)).any (·.hasSorry)) then
      throwError "Authored declaration contains a sorry expression: {name}"
  let privateEnv := env.setExporting false
  let importedAxioms := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  -- Match Lean's ordinary export audit, sharing its traversal cache across names.
  let axiomRows := CollectAxioms.runM privateEnv do
    names.mapM fun name =>
      return (name, ← CollectAxioms.collectAndGet importedAxioms.find? name)
  let mut theoremCount : Nat := 0
  for (name, axioms) in axiomRows do
    let some info := env.checked.get.find? name
      | throwError "Authored declaration is not kernel checked: {name}"
    if let .axiomInfo _ := info then throwError "Authored axiom: {name}"
    if info.type.hasSorry || ((info.value? (allowOpaque := true)).any (·.hasSorry)) then
      throwError "Authored declaration contains a sorry expression: {name}"
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved transitive axiom in {name}: {ax}"
    if let .thmInfo _ := info then
      theoremCount := theoremCount + 1
  let report := Json.mkObj [
    ("main_module", toJson env.header.mainModule.toString),
    ("declaration_count", toJson names.size),
    ("theorem_count", toJson theoremCount),
    ("trust_level", toJson env.header.trustLevel.toNat),
    ("allowed_axioms", toJson #["propext", "Classical.choice", "Quot.sound"]),
    ("audit_scope", toJson "current_stage_new_declarations")]
  logInfo m!"SEGRE_STAGE_KERNEL_AUDIT_PASS {report.compress}"
