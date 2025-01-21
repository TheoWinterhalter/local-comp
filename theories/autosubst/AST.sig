list : Functor

-- Global references
gref : Type

-- Extension references
eref : Type
aref : Type

-- Universe levels
level : Type

-- Syntax

term(var) : Type

Sort : level -> term

Pi : term -> (bind term in term) -> term
lam : term -> (bind term in term) -> term
app : term -> term -> term

const : gref -> "list" ("list" (term)) -> term
assm : eref -> aref -> term
