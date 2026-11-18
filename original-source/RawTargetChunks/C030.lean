module
public import RawTargetChunks.C030A
public import RawTargetChunks.C030B

@[expose] public section
namespace Nonrational.TerminalData

noncomputable def chunkTree030 : TargetTree :=
  .branch 64 chunkPart030A chunkPart030B

end Nonrational.TerminalData
