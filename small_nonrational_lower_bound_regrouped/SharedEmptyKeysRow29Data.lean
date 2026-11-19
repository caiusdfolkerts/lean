module
prelude
public import GraphRouteCasesData
public import SharedSmallRoots29

@[expose] public section
noncomputable section

@[reducible] def Papers.RationalityTen.SharedEmptyKeys.Row29.offset : Nat :=
24362
def Papers.RationalityTen.SharedEmptyKeys.Row29.rootCode : Fin
    Papers.RationalityTen.SharedSmallRootCertificates.Row29.rootCount →
  Nat :=
fun i => (Papers.RationalityTen.SharedSmallRootCertificates.Row29.entry i).val.snd
def Papers.RationalityTen.SharedEmptyKeys.Row29.test : Nat → Bool :=
fun i =>
  Decidable.decide
    (Papers.RationalityTen.GraphRoutes.emptyRootKeys.entry (Papers.RationalityTen.SharedEmptyKeys.Row29.offset + i) =
      (29,
        Papers.RationalityTen.SharedSmallRootReplay.complement
          (Papers.RationalityTen.SharedEmptyKeys.Row29.rootCode
            (Fin.ofNat Papers.RationalityTen.SharedSmallRootCertificates.Row29.rootCount i))))

