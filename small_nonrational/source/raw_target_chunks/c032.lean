module
public import RawTargetChunks.C032A
public import RawTargetChunks.C032B

@[expose] public section
namespace Nonrational.TerminalData

noncomputable def chunkTree032 : TargetTree :=
  .branch 64 chunkPart032A chunkPart032B

end Nonrational.TerminalData
