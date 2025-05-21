list : Functor
option : Functor

-- Global references
gref : Type

-- Assumption references
aref : Type

-- Universe levels
level : Type

-- Syntax

term(var) : Type

Sort : level -> term

Pi : term -> (bind term in term) -> term
lam : term -> (bind term in term) -> term
app : term -> term -> term

const : gref -> "list" ("option" (term)) -> term
assm : aref -> term
