SED=`which sed`

syntax:
	autosubst -f -s urocq -v ge813 AST.sig -o AST.v -p AST_preamble.v
	${SED} -i '' -e '10s/^/From LocalComp.autosubst /' unscoped.v
