module
public import complete_verification
public import paper_statements

/-!
# Gröbner bases for symmetric rank conditions

This is the public entry point for the complete formalisation. It imports all
mathematical results and the closed-statement audit of the principal theorems.

Start with `PaperStatements.lean` for the expanded core theorem statements and
`PAPER_CORRESPONDENCE.md` for every numbered result and the supplementary
conclusions. The detailed dependency audits are separate Lake build targets;
`bash check.sh` builds them along with this library.
-/
