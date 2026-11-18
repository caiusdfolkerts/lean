module
public import RawTargetChunks.C020A
public import RawTargetChunks.C020B

@[expose] public section
namespace Nonrational.TerminalData

noncomputable def chunkTree020 : TargetTree :=
  .branch 64 chunkPart020A chunkPart020B

end Nonrational.TerminalData
