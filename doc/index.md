Controlling computation in type theory, *locally*
=================================================

### Utility

General tactics, lemmas and notations are defined in
[Util](doc/coqdoc/LocalComp.Util.html).

### Syntax

We define a common syntax for both MLTT and its extension.
[BasicAST] contains the notion of references (for variables).
`autosubst/AST.sig` is used to generate the [autosubst/AST] module.
[autosubst/core], [autosubst/unscoped] and [autosubst/SubstNotations] contain
the Autosubst library and some notations.
[autosubst/RAsimpl] contains implementation for the `rasimpl` tactic,
a faster substitution simplification tactic,
whereas [autosubst/AST_rasimpl] provide the corresponding instance for our
syntax.

[Env] defines global, interface, and local environments.

[Inst] defines operations to instantiate an interface.

[BasicAST]: doc/coqdoc/LocalComp.BasicAST.html
[autosubst/AST]: doc/coqdoc/LocalComp.autosubst.AST.html
[autosubst/core]: doc/coqdoc/LocalComp.autosubst.core.html
[autosubst/unscoped]: doc/coqdoc/LocalComp.autosubst.unscoped.html
[autosubst/RAsimpl]: doc/coqdoc/LocalComp.autosubst.RAsimpl.html
[autosubst/AST_rasimpl]: doc/coqdoc/LocalComp.autosubst.AST_rasimpl.html
[autosubst/SubstNotations]: doc/coqdoc/LocalComp.autosubst.SubstNotations.html
[Env]: doc/coqdoc/LocalComp.Env.html
[Inst]: doc/coqdoc/LocalComp.Inst.html

### Type Theory and its meta-theory

| Module            | Description                                   |
| :---------------- | :-------------------------------------------- |
| [GScope]          | Notion of global scope                        |
| [IScope]          | Interface scoping                             |
| [Typing]          | Conversion and typing judgements              |
| [BasicMetaTheory] | Meta-theory like substitution and validity    |
| [Inversion]       | Inversion of typing lemmas                    |
| [Inlining]        | Inlining and conservativity results           |
| [Confluence]      | Generic results about confluence              |
| [Reduction]       | Reduction, injectvity of Π, subject reduction |
| [Pattern]         | Proof-of-concept confluence proof             |

[GScope]: doc/coqdoc/LocalComp.GScope.html
[IScope]: doc/coqdoc/LocalComp.IScope.html
[Typing]: doc/coqdoc/LocalComp.Typing.html
[BasicMetaTheory]: doc/coqdoc/LocalComp.BasicMetaTheory.html
[Inversion]: doc/coqdoc/LocalComp.Inversion.html
[Inlining]: doc/coqdoc/LocalComp.Inlining.html
[Confluence]: doc/coqdoc/LocalComp.Confluence.html
[Reduction]: doc/coqdoc/LocalComp.Reduction.html
[Pattern]: doc/coqdoc/LocalComp.Pattern.html
