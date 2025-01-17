-- Universe levels
level : Type

-- Syntax

term(var) : Type

Sort : level -> term

Pi : term -> (bind term in term) -> term
lam : term -> (bind term in term) -> term
app : term -> term -> term

-- TODO
