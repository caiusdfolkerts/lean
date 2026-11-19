module
prelude
public import GraphRouteCasesData
public import SharedSmallRoots30

@[expose] public section
noncomputable section

@[reducible] def Papers.RationalityTen.SharedEmptyKeys.Row30.offset : Nat :=
25499
def Papers.RationalityTen.SharedEmptyKeys.Row30.rootCode : Fin
    Papers.RationalityTen.SharedSmallRootCertificates.Row30.rootCount →
  Nat :=
fun i => (Papers.RationalityTen.SharedSmallRootCertificates.Row30.entry i).val.snd
def Papers.RationalityTen.SharedEmptyKeys.Row30.test : Nat → Bool :=
fun i =>
  Decidable.decide
    (Papers.RationalityTen.GraphRoutes.emptyRootKeys.entry (Papers.RationalityTen.SharedEmptyKeys.Row30.offset + i) =
      (30,
        Papers.RationalityTen.SharedSmallRootReplay.complement
          (Papers.RationalityTen.SharedEmptyKeys.Row30.rootCode
            (Fin.ofNat Papers.RationalityTen.SharedSmallRootCertificates.Row30.rootCount i))))

