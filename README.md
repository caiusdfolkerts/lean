# Pure geometry diagnostic for an 18-key graph block

This ordinary Lean 4.35.0 job checks the original endpoint `Papers.RationalityTen.GraphFiniteDispatch.Block 21816 21834` with the same 18 records, all growth nodes, geometric frames, keys and terminal dispositions used in the preceding successful block diagnostic.

The previous data reader expanded 12 derived numerical fields before exporting the record. Here the reader places the 46 independent fields and the selected six-component catalogue tuples into Lean expressions. A transparent, total Lean decoder constructs the 12 fields from these inputs. `PureGeometryProbe.exactRecords` combines 18 individual definitional equality proofs to show that the entire ordered list of decoded records equals the prior list, including all 58 numerical components per record. The generic proof consumes the same RawData type and uses its previously checked metadata, nodes, geometric, row and key predicates.

The build records the export of the same abstract predicate applied to each list, then the generic theorem and the exact graph endpoint. Each receipt includes the exported declaration count, natural-literal count, decimal digit bytes, export length, SHA-256, and axioms. The proof export is replayed with Lean's kernel, NanoDa, and verified con-ron. The prior direct-literal endpoint was measured on the same compiler in GitHub Actions run 44325444351. This diagnostic covers one of 1,056 graph blocks. Full Theorem 2 and Corollary 4 still require the whole classification proof.

The workspace source comes from caiusdfolkerts/research at e0696fddcd3d10b5d6461e62e9b2f02c4195be37. LICENSE, NOTICE and the numerical pack files accompany the source. The workflow uses ephemeral build products and retains bounded JSON receipts.
