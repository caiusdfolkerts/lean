module
prelude
public meta import LowerSchemas.Metadata
public import GraphInputsRow29Part00045Data
public import SharedGraphCellPool
public import SharedSmallCellPoolChecked
public import GraphInputsRow25Part00006Metadata

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool FiniteChecks

cert_graph_alignment_2 000 0 0 64 25 00006 045
cert_graph_alignment_2 000 1 64 128 25 00006 045
cert_graph_alignment_2 000 2 128 130 25 00006 045
cert_graph_alignment_checked 000 130
cert_graph_aligned_2 000
cert_graph_local_2 000 0 0 64 64
cert_graph_local_2 000 1 64 128 64
cert_graph_local_2 000 2 128 130 2
cert_graph_local_checked_4 000 130
cert_graph_kind_checked_2 000 25 00006 045
cert_graph_ridge_matrix 000 25 00006 045
cert_graph_edge_matrix_2 000 25 00006 045
cert_graph_missing_matrix_2 000 25 00006 045
cert_graph_matrix_checked_2 000
cert_graph_validity 000
cert_graph_vertex_width_2 000 25 00006 045
cert_graph_vertex_code_3 000 25 00006 045
cert_graph_literal 000
cert_graph_cells_exact_2 000

cert_graph_alignment_3 001 0 0 64 64
cert_graph_alignment_3 001 1 64 114 50
cert_graph_alignment_checked_5 001 114
cert_graph_aligned_2 001
cert_graph_local_2 001 0 0 64 64
cert_graph_local_2 001 1 64 114 50
cert_graph_local_checked 001 114
cert_graph_kind_checked 001
cert_graph_ridge_matrix_2 001
cert_graph_edge_matrix 001
cert_graph_missing_matrix 001
cert_graph_matrix_checked_2 001
cert_graph_validity 001
cert_graph_vertex_width 001
cert_graph_vertex_code 001
cert_graph_literal 001
cert_graph_cells_exact_2 001

cert_graph_alignment_2 002 0 0 64 25 00006 046
cert_graph_alignment_2 002 1 64 113 25 00006 046
cert_graph_alignment_checked_5 002 113
cert_graph_aligned_2 002
cert_graph_local_2 002 0 0 64 64
cert_graph_local_2 002 1 64 113 49
cert_graph_local_checked 002 113
cert_graph_kind_checked_2 002 25 00006 046
cert_graph_ridge_matrix 002 25 00006 046
cert_graph_edge_matrix_2 002 25 00006 046
cert_graph_missing_matrix_2 002 25 00006 046
cert_graph_matrix_checked_2 002
cert_graph_validity 002
cert_graph_vertex_width_2 002 25 00006 046
cert_graph_vertex_code_3 002 25 00006 046
cert_graph_literal 002
cert_graph_cells_exact_2 002

cert_graph_alignment_3 003 0 0 64 64
cert_graph_alignment_3 003 1 64 98 34
cert_graph_alignment_checked_5 003 98
cert_graph_aligned_2 003
cert_graph_local_2 003 0 0 64 64
cert_graph_local_2 003 1 64 98 34
cert_graph_local_checked 003 98
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

cert_graph_alignment_2 004 0 0 64 25 00006 047
cert_graph_alignment_2 004 1 64 109 25 00006 047
cert_graph_alignment_checked_5 004 109
cert_graph_aligned_2 004
cert_graph_local_2 004 0 0 64 64
cert_graph_local_2 004 1 64 109 45
cert_graph_local_checked 004 109
cert_graph_kind_checked_2 004 25 00006 047
cert_graph_ridge_matrix 004 25 00006 047
cert_graph_edge_matrix_2 004 25 00006 047
cert_graph_missing_matrix_2 004 25 00006 047
cert_graph_matrix_checked_2 004
cert_graph_validity 004
cert_graph_vertex_width_2 004 25 00006 047
cert_graph_vertex_code_3 004 25 00006 047
cert_graph_literal 004
cert_graph_cells_exact_2 004

cert_graph_alignment_3 005 0 0 64 64
cert_graph_alignment_3 005 1 64 106 42
cert_graph_alignment_checked_5 005 106
cert_graph_aligned_2 005
cert_graph_local_2 005 0 0 64 64
cert_graph_local_2 005 1 64 106 42
cert_graph_local_checked 005 106
cert_graph_kind_checked 005
cert_graph_ridge_matrix_2 005
cert_graph_edge_matrix 005
cert_graph_missing_matrix 005
cert_graph_matrix_checked_2 005
cert_graph_validity 005
cert_graph_vertex_width 005
cert_graph_vertex_code 005
cert_graph_literal 005
cert_graph_cells_exact_2 005

cert_graph_alignment_2 006 0 0 64 25 00006 048
cert_graph_alignment_2 006 1 64 104 25 00006 048
cert_graph_alignment_checked_5 006 104
cert_graph_aligned_2 006
cert_graph_local_2 006 0 0 64 64
cert_graph_local_2 006 1 64 104 40
cert_graph_local_checked 006 104
cert_graph_kind_checked_2 006 25 00006 048
cert_graph_ridge_matrix 006 25 00006 048
cert_graph_edge_matrix_2 006 25 00006 048
cert_graph_missing_matrix_2 006 25 00006 048
cert_graph_matrix_checked_2 006
cert_graph_validity 006
cert_graph_vertex_width_2 006 25 00006 048
cert_graph_vertex_code_3 006 25 00006 048
cert_graph_literal 006
cert_graph_cells_exact_2 006

cert_graph_alignment_2 007 0 0 64 25 00006 049
cert_graph_alignment_2 007 1 64 107 25 00006 049
cert_graph_alignment_checked_5 007 107
cert_graph_aligned_2 007
cert_graph_local_2 007 0 0 64 64
cert_graph_local_2 007 1 64 107 43
cert_graph_local_checked_2 007 107
cert_graph_kind_checked_2 007 25 00006 049
cert_graph_ridge_matrix 007 25 00006 049
cert_graph_edge_matrix_2 007 25 00006 049
cert_graph_missing_matrix_2 007 25 00006 049
cert_graph_matrix_checked_2 007
cert_graph_validity 007
cert_graph_vertex_width_2 007 25 00006 049
cert_graph_vertex_code_3 007 25 00006 049
cert_graph_literal 007
cert_graph_cells_exact_2 007

cert_graph_alignment_2 008 0 0 64 25 00006 050
cert_graph_alignment_2 008 1 64 105 25 00006 050
cert_graph_alignment_checked_5 008 105
cert_graph_aligned_2 008
cert_graph_local_2 008 0 0 64 64
cert_graph_local_2 008 1 64 105 41
cert_graph_local_checked 008 105
cert_graph_kind_checked_2 008 25 00006 050
cert_graph_ridge_matrix 008 25 00006 050
cert_graph_edge_matrix_2 008 25 00006 050
cert_graph_missing_matrix_2 008 25 00006 050
cert_graph_matrix_checked_2 008
cert_graph_validity 008
cert_graph_vertex_width_2 008 25 00006 050
cert_graph_vertex_code_3 008 25 00006 050
cert_graph_literal 008
cert_graph_cells_exact_2 008

cert_graph_alignment_3 009 0 0 64 64
cert_graph_alignment_3 009 1 64 102 38
cert_graph_alignment_checked_5 009 102
cert_graph_aligned_2 009
cert_graph_local_2 009 0 0 64 64
cert_graph_local_2 009 1 64 102 38
cert_graph_local_checked 009 102
cert_graph_kind_checked 009
cert_graph_ridge_matrix_2 009
cert_graph_edge_matrix 009
cert_graph_missing_matrix 009
cert_graph_matrix_checked_2 009
cert_graph_validity 009
cert_graph_vertex_width 009
cert_graph_vertex_code 009
cert_graph_literal 009
cert_graph_cells_exact_2 009

cert_graph_alignment_2 010 0 0 64 25 00006 051
cert_graph_alignment_2 010 1 64 96 25 00006 051
cert_graph_alignment_checked_5 010 96
cert_graph_aligned_2 010
cert_graph_local_2 010 0 0 64 64
cert_graph_local_2 010 1 64 96 32
cert_graph_local_checked 010 96
cert_graph_kind_checked_2 010 25 00006 051
cert_graph_ridge_matrix 010 25 00006 051
cert_graph_edge_matrix_2 010 25 00006 051
cert_graph_missing_matrix_2 010 25 00006 051
cert_graph_matrix_checked_2 010
cert_graph_validity 010
cert_graph_vertex_width_2 010 25 00006 051
cert_graph_vertex_code_3 010 25 00006 051
cert_graph_literal 010
cert_graph_cells_exact_2 010

cert_graph_alignment_2 011 0 0 64 25 00006 052
cert_graph_alignment_2 011 1 64 95 25 00006 052
cert_graph_alignment_checked_5 011 95
cert_graph_aligned_2 011
cert_graph_local_2 011 0 0 64 64
cert_graph_local_2 011 1 64 95 31
cert_graph_local_checked_2 011 95
cert_graph_kind_checked_2 011 25 00006 052
cert_graph_ridge_matrix 011 25 00006 052
cert_graph_edge_matrix_2 011 25 00006 052
cert_graph_missing_matrix_2 011 25 00006 052
cert_graph_matrix_checked_2 011
cert_graph_validity 011
cert_graph_vertex_width_2 011 25 00006 052
cert_graph_vertex_code_3 011 25 00006 052
cert_graph_literal 011
cert_graph_cells_exact_2 011

cert_graph_alignment_3 012 0 0 64 64
cert_graph_alignment_3 012 1 64 105 41
cert_graph_alignment_checked_5 012 105
cert_graph_aligned_2 012
cert_graph_local_2 012 0 0 64 64
cert_graph_local_2 012 1 64 105 41
cert_graph_local_checked 012 105
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

cert_graph_alignment_2 013 0 0 64 25 00006 053
cert_graph_alignment_2 013 1 64 104 25 00006 053
cert_graph_alignment_checked_5 013 104
cert_graph_aligned_2 013
cert_graph_local_2 013 0 0 64 64
cert_graph_local_2 013 1 64 104 40
cert_graph_local_checked 013 104
cert_graph_kind_checked_2 013 25 00006 053
cert_graph_ridge_matrix 013 25 00006 053
cert_graph_edge_matrix_2 013 25 00006 053
cert_graph_missing_matrix_2 013 25 00006 053
cert_graph_matrix_checked_2 013
cert_graph_validity 013
cert_graph_vertex_width_2 013 25 00006 053
cert_graph_vertex_code_3 013 25 00006 053
cert_graph_literal 013
cert_graph_cells_exact_2 013

cert_graph_alignment_2 014 0 0 64 25 00006 054
cert_graph_alignment_2 014 1 64 105 25 00006 054
cert_graph_alignment_checked_5 014 105
cert_graph_aligned_2 014
cert_graph_local_2 014 0 0 64 64
cert_graph_local_2 014 1 64 105 41
cert_graph_local_checked 014 105
cert_graph_kind_checked_2 014 25 00006 054
cert_graph_ridge_matrix 014 25 00006 054
cert_graph_edge_matrix_2 014 25 00006 054
cert_graph_missing_matrix_2 014 25 00006 054
cert_graph_matrix_checked_2 014
cert_graph_validity 014
cert_graph_vertex_width_2 014 25 00006 054
cert_graph_vertex_code_3 014 25 00006 054
cert_graph_literal 014
cert_graph_cells_exact_2 014

cert_graph_alignment_2 015 0 0 64 25 00006 055
cert_graph_alignment_2 015 1 64 111 25 00006 055
cert_graph_alignment_checked_5 015 111
cert_graph_aligned_2 015
cert_graph_local_2 015 0 0 64 64
cert_graph_local_2 015 1 64 111 47
cert_graph_local_checked_2 015 111
cert_graph_kind_checked_2 015 25 00006 055
cert_graph_ridge_matrix 015 25 00006 055
cert_graph_edge_matrix_2 015 25 00006 055
cert_graph_missing_matrix_2 015 25 00006 055
cert_graph_matrix_checked_2 015
cert_graph_validity 015
cert_graph_vertex_width_2 015 25 00006 055
cert_graph_vertex_code_3 015 25 00006 055
cert_graph_literal 015
cert_graph_cells_exact_2 015

cert_graph_alignment_2 016 0 0 64 25 00006 056
cert_graph_alignment_2 016 1 64 104 25 00006 056
cert_graph_alignment_checked_5 016 104
cert_graph_aligned_2 016
cert_graph_local_2 016 0 0 64 64
cert_graph_local_2 016 1 64 104 40
cert_graph_local_checked 016 104
cert_graph_kind_checked_2 016 25 00006 056
cert_graph_ridge_matrix 016 25 00006 056
cert_graph_edge_matrix_2 016 25 00006 056
cert_graph_missing_matrix_2 016 25 00006 056
cert_graph_matrix_checked_2 016
cert_graph_validity 016
cert_graph_vertex_width_2 016 25 00006 056
cert_graph_vertex_code_3 016 25 00006 056
cert_graph_literal 016
cert_graph_cells_exact_2 016

cert_graph_alignment_3 017 0 0 64 64
cert_graph_alignment_3 017 1 64 101 37
cert_graph_alignment_checked_5 017 101
cert_graph_aligned_2 017
cert_graph_local_2 017 0 0 64 64
cert_graph_local_2 017 1 64 101 37
cert_graph_local_checked 017 101
cert_graph_kind_checked 017
cert_graph_ridge_matrix_2 017
cert_graph_edge_matrix 017
cert_graph_missing_matrix 017
cert_graph_matrix_checked_2 017
cert_graph_validity 017
cert_graph_vertex_width 017
cert_graph_vertex_code 017
cert_graph_literal 017
cert_graph_cells_exact_2 017

cert_graph_alignment_3 018 0 0 64 64
cert_graph_alignment_3 018 1 64 118 54
cert_graph_alignment_checked_5 018 118
cert_graph_aligned_2 018
cert_graph_local_2 018 0 0 64 64
cert_graph_local_2 018 1 64 118 54
cert_graph_local_checked_2 018 118
cert_graph_kind_checked 018
cert_graph_ridge_matrix_2 018
cert_graph_edge_matrix 018
cert_graph_missing_matrix 018
cert_graph_matrix_checked_2 018
cert_graph_validity 018
cert_graph_vertex_width 018
cert_graph_vertex_code 018
cert_graph_literal 018
cert_graph_cells_exact_2 018

cert_graph_alignment_3 019 0 0 64 64
cert_graph_alignment_3 019 1 64 115 51
cert_graph_alignment_checked_5 019 115
cert_graph_aligned_2 019
cert_graph_local_2 019 0 0 64 64
cert_graph_local_2 019 1 64 115 51
cert_graph_local_checked 019 115
cert_graph_kind_checked 019
cert_graph_ridge_matrix_2 019
cert_graph_edge_matrix 019
cert_graph_missing_matrix 019
cert_graph_matrix_checked_2 019
cert_graph_validity 019
cert_graph_vertex_width 019
cert_graph_vertex_code 019
cert_graph_literal 019
cert_graph_cells_exact_2 019

cert_graph_alignment_3 020 0 0 64 64
cert_graph_alignment_3 020 1 64 101 37
cert_graph_alignment_checked_5 020 101
cert_graph_aligned_2 020
cert_graph_local_2 020 0 0 64 64
cert_graph_local_2 020 1 64 101 37
cert_graph_local_checked_2 020 101
cert_graph_kind_checked 020
cert_graph_ridge_matrix_2 020
cert_graph_edge_matrix 020
cert_graph_missing_matrix 020
cert_graph_matrix_checked_2 020
cert_graph_validity 020
cert_graph_vertex_width 020
cert_graph_vertex_code 020
cert_graph_literal 020
cert_graph_cells_exact_2 020

cert_graph_alignment_2 021 0 0 64 25 00006 057
cert_graph_alignment_2 021 1 64 102 25 00006 057
cert_graph_alignment_checked_5 021 102
cert_graph_aligned_2 021
cert_graph_local_2 021 0 0 64 64
cert_graph_local_2 021 1 64 102 38
cert_graph_local_checked_2 021 102
cert_graph_kind_checked_2 021 25 00006 057
cert_graph_ridge_matrix 021 25 00006 057
cert_graph_edge_matrix_2 021 25 00006 057
cert_graph_missing_matrix_2 021 25 00006 057
cert_graph_matrix_checked_2 021
cert_graph_validity 021
cert_graph_vertex_width_2 021 25 00006 057
cert_graph_vertex_code_3 021 25 00006 057
cert_graph_literal 021
cert_graph_cells_exact_2 021

cert_graph_alignment_2 022 0 0 64 25 00006 058
cert_graph_alignment_2 022 1 64 99 25 00006 058
cert_graph_alignment_checked_5 022 99
cert_graph_aligned_2 022
cert_graph_local_2 022 0 0 64 64
cert_graph_local_2 022 1 64 99 35
cert_graph_local_checked_2 022 99
cert_graph_kind_checked_2 022 25 00006 058
cert_graph_ridge_matrix 022 25 00006 058
cert_graph_edge_matrix_2 022 25 00006 058
cert_graph_missing_matrix_2 022 25 00006 058
cert_graph_matrix_checked_2 022
cert_graph_validity 022
cert_graph_vertex_width_2 022 25 00006 058
cert_graph_vertex_code_3 022 25 00006 058
cert_graph_literal 022
cert_graph_cells_exact_2 022

cert_graph_alignment_3 023 0 0 64 64
cert_graph_alignment_3 023 1 64 101 37
cert_graph_alignment_checked_5 023 101
cert_graph_aligned_2 023
cert_graph_local_2 023 0 0 64 64
cert_graph_local_2 023 1 64 101 37
cert_graph_local_checked 023 101
cert_graph_kind_checked 023
cert_graph_ridge_matrix_2 023
cert_graph_edge_matrix 023
cert_graph_missing_matrix 023
cert_graph_matrix_checked_2 023
cert_graph_validity 023
cert_graph_vertex_width 023
cert_graph_vertex_code 023
cert_graph_literal 023
cert_graph_cells_exact_2 023

cert_graph_alignment_2 024 0 0 64 25 00006 059
cert_graph_alignment_2 024 1 64 114 25 00006 059
cert_graph_alignment_checked_5 024 114
cert_graph_aligned_2 024
cert_graph_local_2 024 0 0 64 64
cert_graph_local_2 024 1 64 114 50
cert_graph_local_checked_2 024 114
cert_graph_kind_checked_2 024 25 00006 059
cert_graph_ridge_matrix 024 25 00006 059
cert_graph_edge_matrix_2 024 25 00006 059
cert_graph_missing_matrix_2 024 25 00006 059
cert_graph_matrix_checked_2 024
cert_graph_validity 024
cert_graph_vertex_width_2 024 25 00006 059
cert_graph_vertex_code_3 024 25 00006 059
cert_graph_literal 024
cert_graph_cells_exact_2 024

end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045
