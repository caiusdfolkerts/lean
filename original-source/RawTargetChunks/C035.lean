module
public import RawTargetChunks.C035A
public import RawTargetChunks.C035B

@[expose] public section
namespace Nonrational.TerminalData

noncomputable def chunkTree035 : TargetTree :=
  .branch 64 chunkPart035A chunkPart035B

end Nonrational.TerminalData
