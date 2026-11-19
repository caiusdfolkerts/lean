module
prelude
public meta import LowerSchemas.Metadata
public import GraphInputsRow29Part00005Data
public import SharedGraphCellPool
public import SharedSmallCellPoolChecked
public import GraphInputsRow25Part00001Metadata

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool FiniteChecks

cert_graph_alignment_2 000 0 0 64 25 00001 022
cert_graph_alignment_2 000 1 64 114 25 00001 022
cert_graph_alignment_checked_5 000 114
cert_graph_aligned_2 000
cert_graph_local_2 000 0 0 64 64
cert_graph_local_2 000 1 64 114 50
cert_graph_local_checked 000 114
cert_graph_kind_checked_2 000 25 00001 022
cert_graph_ridge_matrix 000 25 00001 022
cert_graph_edge_matrix_2 000 25 00001 022
cert_graph_missing_matrix_2 000 25 00001 022
cert_graph_matrix_checked_2 000
cert_graph_validity 000
cert_graph_vertex_width_2 000 25 00001 022
cert_graph_vertex_code_3 000 25 00001 022
cert_graph_literal 000
cert_graph_cells_exact_2 000

cert_graph_alignment_2 001 0 0 64 25 00001 023
cert_graph_alignment_2 001 1 64 107 25 00001 023
cert_graph_alignment_checked_5 001 107
cert_graph_aligned_2 001
cert_graph_local_2 001 0 0 64 64
cert_graph_local_2 001 1 64 107 43
cert_graph_local_checked_2 001 107
cert_graph_kind_checked_2 001 25 00001 023
cert_graph_ridge_matrix 001 25 00001 023
cert_graph_edge_matrix_2 001 25 00001 023
cert_graph_missing_matrix_2 001 25 00001 023
cert_graph_matrix_checked_2 001
cert_graph_validity 001
cert_graph_vertex_width_2 001 25 00001 023
cert_graph_vertex_code_3 001 25 00001 023
cert_graph_literal 001
cert_graph_cells_exact_2 001

cert_graph_alignment_2 002 0 0 64 25 00001 024
cert_graph_alignment_2 002 1 64 117 25 00001 024
cert_graph_alignment_checked_5 002 117
cert_graph_aligned_2 002
cert_graph_local_2 002 0 0 64 64
cert_graph_local_2 002 1 64 117 53
cert_graph_local_checked_2 002 117
cert_graph_kind_checked_2 002 25 00001 024
cert_graph_ridge_matrix 002 25 00001 024
cert_graph_edge_matrix_2 002 25 00001 024
cert_graph_missing_matrix_2 002 25 00001 024
cert_graph_matrix_checked_2 002
cert_graph_validity 002
cert_graph_vertex_width_2 002 25 00001 024
cert_graph_vertex_code_3 002 25 00001 024
cert_graph_literal 002
cert_graph_cells_exact_2 002

cert_graph_alignment_3 003 0 0 64 64
cert_graph_alignment_3 003 1 64 109 45
cert_graph_alignment_checked_5 003 109
cert_graph_aligned_2 003
cert_graph_local_2 003 0 0 64 64
cert_graph_local_2 003 1 64 109 45
cert_graph_local_checked 003 109
cert_graph_kind_checked 003
cert_graph_ridge_matrix_2 003
cert_graph_edge_matrix 003
cert_graph_missing_matrix 003
cert_graph_matrix_checked_2 003
cert_graph_validity 003
cert_graph_vertex_width 003
cert_graph_vertex_code 003
cert_graph_literal 003
cert_graph_cells_exact_2 003

cert_graph_alignment_3 004 0 0 64 64
cert_graph_alignment_3 004 1 64 112 48
cert_graph_alignment_checked_5 004 112
cert_graph_aligned_2 004
cert_graph_local_2 004 0 0 64 64
cert_graph_local_2 004 1 64 112 48
cert_graph_local_checked 004 112
cert_graph_kind_checked 004
cert_graph_ridge_matrix_2 004
cert_graph_edge_matrix 004
cert_graph_missing_matrix 004
cert_graph_matrix_checked_2 004
cert_graph_validity 004
cert_graph_vertex_width 004
cert_graph_vertex_code 004
cert_graph_literal 004
cert_graph_cells_exact_2 004

cert_graph_alignment_2 005 0 0 64 25 00001 025
cert_graph_alignment_2 005 1 64 106 25 00001 025
cert_graph_alignment_checked_5 005 106
cert_graph_aligned_2 005
cert_graph_local_2 005 0 0 64 64
cert_graph_local_2 005 1 64 106 42
cert_graph_local_checked 005 106
cert_graph_kind_checked_2 005 25 00001 025
cert_graph_ridge_matrix 005 25 00001 025
cert_graph_edge_matrix_2 005 25 00001 025
cert_graph_missing_matrix_2 005 25 00001 025
cert_graph_matrix_checked_2 005
cert_graph_validity 005
cert_graph_vertex_width_2 005 25 00001 025
cert_graph_vertex_code_3 005 25 00001 025
cert_graph_literal 005
cert_graph_cells_exact_2 005

cert_graph_alignment_2 006 0 0 64 25 00001 026
cert_graph_alignment_2 006 1 64 93 25 00001 026
cert_graph_alignment_checked_5 006 93
cert_graph_aligned_2 006
cert_graph_local_2 006 0 0 64 64
cert_graph_local_2 006 1 64 93 29
cert_graph_local_checked 006 93
cert_graph_kind_checked_2 006 25 00001 026
cert_graph_ridge_matrix 006 25 00001 026
cert_graph_edge_matrix_2 006 25 00001 026
cert_graph_missing_matrix_2 006 25 00001 026
cert_graph_matrix_checked_2 006
cert_graph_validity 006
cert_graph_vertex_width_2 006 25 00001 026
cert_graph_vertex_code_3 006 25 00001 026
cert_graph_literal 006
cert_graph_cells_exact_2 006

cert_graph_alignment_2 007 0 0 64 25 00001 027
cert_graph_alignment_2 007 1 64 93 25 00001 027
cert_graph_alignment_checked_5 007 93
cert_graph_aligned_2 007
cert_graph_local_2 007 0 0 64 64
cert_graph_local_2 007 1 64 93 29
cert_graph_local_checked 007 93
cert_graph_kind_checked_2 007 25 00001 027
cert_graph_ridge_matrix 007 25 00001 027
cert_graph_edge_matrix_2 007 25 00001 027
cert_graph_missing_matrix_2 007 25 00001 027
cert_graph_matrix_checked_2 007
cert_graph_validity 007
cert_graph_vertex_width_2 007 25 00001 027
cert_graph_vertex_code_3 007 25 00001 027
cert_graph_literal 007
cert_graph_cells_exact_2 007

cert_graph_alignment_2 008 0 0 64 25 00001 028
cert_graph_alignment_2 008 1 64 90 25 00001 028
cert_graph_alignment_checked_5 008 90
cert_graph_aligned_2 008
cert_graph_local_2 008 0 0 64 64
cert_graph_local_2 008 1 64 90 26
cert_graph_local_checked 008 90
cert_graph_kind_checked_2 008 25 00001 028
cert_graph_ridge_matrix 008 25 00001 028
cert_graph_edge_matrix_2 008 25 00001 028
cert_graph_missing_matrix_2 008 25 00001 028
cert_graph_matrix_checked_2 008
cert_graph_validity 008
cert_graph_vertex_width_2 008 25 00001 028
cert_graph_vertex_code_3 008 25 00001 028
cert_graph_literal 008
cert_graph_cells_exact_2 008

cert_graph_alignment_2 009 0 0 64 25 00001 029
cert_graph_alignment_2 009 1 64 92 25 00001 029
cert_graph_alignment_checked_5 009 92
cert_graph_aligned_2 009
cert_graph_local_2 009 0 0 64 64
cert_graph_local_2 009 1 64 92 28
cert_graph_local_checked_2 009 92
cert_graph_kind_checked_2 009 25 00001 029
cert_graph_ridge_matrix 009 25 00001 029
cert_graph_edge_matrix_2 009 25 00001 029
cert_graph_missing_matrix_2 009 25 00001 029
cert_graph_matrix_checked_2 009
cert_graph_validity 009
cert_graph_vertex_width_2 009 25 00001 029
cert_graph_vertex_code_3 009 25 00001 029
cert_graph_literal 009
cert_graph_cells_exact_2 009

cert_graph_alignment_2 010 0 0 64 25 00001 030
cert_graph_alignment_2 010 1 64 96 25 00001 030
cert_graph_alignment_checked_5 010 96
cert_graph_aligned_2 010
cert_graph_local_2 010 0 0 64 64
cert_graph_local_2 010 1 64 96 32
cert_graph_local_checked 010 96
cert_graph_kind_checked_2 010 25 00001 030
cert_graph_ridge_matrix 010 25 00001 030
cert_graph_edge_matrix_2 010 25 00001 030
cert_graph_missing_matrix_2 010 25 00001 030
cert_graph_matrix_checked_2 010
cert_graph_validity 010
cert_graph_vertex_width_2 010 25 00001 030
cert_graph_vertex_code_3 010 25 00001 030
cert_graph_literal 010
cert_graph_cells_exact_2 010

cert_graph_alignment_3 011 0 0 64 64
cert_graph_alignment_3 011 1 64 110 46
cert_graph_alignment_checked_5 011 110
cert_graph_aligned_2 011
cert_graph_local_2 011 0 0 64 64
cert_graph_local_2 011 1 64 110 46
cert_graph_local_checked 011 110
cert_graph_kind_checked 011
cert_graph_ridge_matrix_2 011
cert_graph_edge_matrix 011
cert_graph_missing_matrix 011
cert_graph_matrix_checked_2 011
cert_graph_validity 011
cert_graph_vertex_width 011
cert_graph_vertex_code 011
cert_graph_literal 011
cert_graph_cells_exact_2 011

cert_graph_alignment_3 012 0 0 64 64
cert_graph_alignment_3 012 1 64 113 49
cert_graph_alignment_checked_5 012 113
cert_graph_aligned_2 012
cert_graph_local_2 012 0 0 64 64
cert_graph_local_2 012 1 64 113 49
cert_graph_local_checked_2 012 113
cert_graph_kind_checked 012
cert_graph_ridge_matrix_2 012
cert_graph_edge_matrix 012
cert_graph_missing_matrix 012
cert_graph_matrix_checked_2 012
cert_graph_validity 012
cert_graph_vertex_width 012
cert_graph_vertex_code 012
cert_graph_literal 012
cert_graph_cells_exact_2 012

cert_graph_alignment_3 013 0 0 64 64
cert_graph_alignment_3 013 1 64 105 41
cert_graph_alignment_checked_5 013 105
cert_graph_aligned_2 013
cert_graph_local_2 013 0 0 64 64
cert_graph_local_2 013 1 64 105 41
cert_graph_local_checked 013 105
cert_graph_kind_checked 013
cert_graph_ridge_matrix_2 013
cert_graph_edge_matrix 013
cert_graph_missing_matrix 013
cert_graph_matrix_checked_2 013
cert_graph_validity 013
cert_graph_vertex_width 013
cert_graph_vertex_code 013
cert_graph_literal 013
cert_graph_cells_exact_2 013

cert_graph_alignment_2 014 0 0 64 25 00001 031
cert_graph_alignment_2 014 1 64 107 25 00001 031
cert_graph_alignment_checked_5 014 107
cert_graph_aligned_2 014
cert_graph_local_2 014 0 0 64 64
cert_graph_local_2 014 1 64 107 43
cert_graph_local_checked_2 014 107
cert_graph_kind_checked_2 014 25 00001 031
cert_graph_ridge_matrix 014 25 00001 031
cert_graph_edge_matrix_2 014 25 00001 031
cert_graph_missing_matrix_2 014 25 00001 031
cert_graph_matrix_checked_2 014
cert_graph_validity 014
cert_graph_vertex_width_2 014 25 00001 031
cert_graph_vertex_code_3 014 25 00001 031
cert_graph_literal 014
cert_graph_cells_exact_2 014

cert_graph_alignment_3 015 0 0 64 64
cert_graph_alignment_3 015 1 64 102 38
cert_graph_alignment_checked_5 015 102
cert_graph_aligned_2 015
cert_graph_local_2 015 0 0 64 64
cert_graph_local_2 015 1 64 102 38
cert_graph_local_checked 015 102
cert_graph_kind_checked 015
cert_graph_ridge_matrix_2 015
cert_graph_edge_matrix 015
cert_graph_missing_matrix 015
cert_graph_matrix_checked_2 015
cert_graph_validity 015
cert_graph_vertex_width 015
cert_graph_vertex_code 015
cert_graph_literal 015
cert_graph_cells_exact_2 015

cert_graph_alignment_2 016 0 0 64 25 00001 032
cert_graph_alignment_2 016 1 64 96 25 00001 032
cert_graph_alignment_checked_5 016 96
cert_graph_aligned_2 016
cert_graph_local_2 016 0 0 64 64
cert_graph_local_2 016 1 64 96 32
cert_graph_local_checked 016 96
cert_graph_kind_checked_2 016 25 00001 032
cert_graph_ridge_matrix 016 25 00001 032
cert_graph_edge_matrix_2 016 25 00001 032
cert_graph_missing_matrix_2 016 25 00001 032
cert_graph_matrix_checked_2 016
cert_graph_validity 016
cert_graph_vertex_width_2 016 25 00001 032
cert_graph_vertex_code_3 016 25 00001 032
cert_graph_literal 016
cert_graph_cells_exact_2 016

cert_graph_alignment_2 017 0 0 64 25 00001 033
cert_graph_alignment_2 017 1 64 100 25 00001 033
cert_graph_alignment_checked_5 017 100
cert_graph_aligned_2 017
cert_graph_local_2 017 0 0 64 64
cert_graph_local_2 017 1 64 100 36
cert_graph_local_checked_2 017 100
cert_graph_kind_checked_2 017 25 00001 033
cert_graph_ridge_matrix 017 25 00001 033
cert_graph_edge_matrix_2 017 25 00001 033
cert_graph_missing_matrix_2 017 25 00001 033
cert_graph_matrix_checked_2 017
cert_graph_validity 017
cert_graph_vertex_width_2 017 25 00001 033
cert_graph_vertex_code_3 017 25 00001 033
cert_graph_literal 017
cert_graph_cells_exact_2 017

end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005
