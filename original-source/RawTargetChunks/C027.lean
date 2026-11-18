module
public import RawTargetChunks.C027A
public import RawTargetChunks.C027B

@[expose] public section
namespace Nonrational.TerminalData

noncomputable def chunkTree027 : TargetTree :=
  .branch 64 chunkPart027A chunkPart027B

end Nonrational.TerminalData
