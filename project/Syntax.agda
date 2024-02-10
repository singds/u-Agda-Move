open import project.IncludeBase

module project.Syntax (Nm Ns Nf Nsf Nfa : ℕ) where
{-
Module Parameters:
    Nm   -- # of modules
    Ns   -- # of structures for each module
    Nf   -- # of functions for each module
    Nsf  -- # of fields for each structure
    Nfa  -- # of arguments for each function
-}

private
    variable
        n : ℕ

record StrId : Set where
    constructor sId
    field
        m : Fin Nm
        s : Fin Ns

record FunId : Set where
    constructor fId
    field
        m : Fin Nm
        f : Fin Nf

-- K is the Set of resource identifiers.
K : Set
K = ℕ
k0 = 0

-- Language Terms
-- The terms the programmer can use to write a program.
data LTerm : Set where
    num_           : (n : ℕ) → LTerm                                 -- constant
    var_           : (x : ℕ) → LTerm                                 -- variable. x is a de Bruijn index
    Let_In_        : (t1 t2 : LTerm) → LTerm                         -- let t1 in t2
    call           : (fid : FunId) → (ts : Vec LTerm n) → LTerm      -- f(ts)  function call
    if_then_else_  : (t1 t2 t3 : LTerm) → LTerm                      -- if t1 then t2 else t3
    pack           : (sid : StrId) → (ts : Vec LTerm n) → LTerm      -- pack M.S [t1 ... tn]
    unpack_In_     : (t1 t2 : LTerm) → LTerm                         -- unpack t1 in t2
    _·_            : (x : ℕ) → (j : Fin Nsf) → LTerm                 -- x.j
    pub_           : (t : LTerm) → LTerm                             -- publish t

-- Runtime Terms
-- LTerm + runtimes terms
data Term : Set where
    num_           : (n : ℕ) → Term
    var_           : (x : ℕ) → Term
    Let_In_        : (t1 t2 : Term) → Term
    call           : (fid : FunId) → (ts : Vec Term n) → Term
    if_then_else_  : (t1 t2 t3 : Term) → Term
    pack           : (sid : StrId) → (ts : Vec Term n) → Term
    unpack_In_     : (t1 t2 : Term) → Term
    _·_            : (t : Term) → (j : Fin Nsf) → Term
    pub_           : (t : Term) → Term

    struct         : {n : ℕ} → (k : K) → (sid : StrId) → (ts : Vec Term n) → Term
    exec           : (M2 : Fin Nm) → Term → Term

infix  30 var_
infixl 30 num_
infix  20 Let_In_
infix  20 unpack_In_

-- Converts an LTerm to a Term. It is simply a mapping of the constructors.
-- toRun because LTerm are the program source code while Term are the runtime terms.
toRun : LTerm → Term
toRun-vec : {n : ℕ} → Vec LTerm n → Vec Term n

toRun (num n) = num n
toRun (var x) = var x
toRun (Let t1 In t2) = Let (toRun t1) In (toRun t2)
toRun (call fid ts) = call fid (toRun-vec ts)
toRun (if t1 then t2 else t3) = if (toRun t1) then (toRun t2) else (toRun t3)
toRun (pack sid ts) = pack sid (toRun-vec ts)
toRun (unpack t1 In t2) = unpack (toRun t1) In (toRun t2)
toRun (x · j) = (var x) · j
toRun (pub t) = pub (toRun t)

toRun-vec V.[] = V.[]
toRun-vec (t V.∷ ts) = toRun t V.∷ toRun-vec ts

data Type : Set where
    Tint : Type
    Tst  : StrId → Type -- Every struct identifier is also a type

record Str : Set where
    constructor str
    field
        isLin   : Bool -- true if the structure is a linear type
        fieldsT : Vec Type Nsf
        -- The types of the fields of the struct.
        -- Field 0 has type gFieldsT[0], etc.
        -- Struct fields don't have names.

record Fun : Set where
    constructor fun
    field
        argsT : Vec Type Nfa    -- Argument types
        retT  : Type            -- Return type
        body  : LTerm

record Module : Set where
    constructor mod
    field
        strs : Vec Str Ns
        funs : Vec Fun Nf

record Program : Set where
    constructor prog
    field
        mods : Vec Module Nm


-- Definition of value; defines what terms are considered values.
-- Value t: "Term t is a value".
-- ValueV ts: "All the terms in ts are values".
data Value : Term → Set
data ValueV : {n : ℕ} → Vec Term n → Set

data Value where
    Vnum  : Value (num n)

    Vstruct :
          {k : K} {sid : StrId} {ts : Vec Term n}
        → (vs : ValueV ts)
        → Value (struct k sid ts)

data ValueV where
    -- A vector of 0 terms is a vector of values
    V[]  : ValueV V.[]
    
    -- If we add a value at the beginning of a vector of values, we get a new vector of values
    _V∷_ :
        {t : Term}
        {ts : Vec Term n}
        → Value t
        → ValueV ts
        → ValueV (t V.∷ ts)

infixr 20 _V∷_


vLookup : {n : ℕ} {ts : Vec Term n} →
    (i : Fin n) → ValueV ts → Value (V.lookup ts i)
vLookup F.zero    (v V∷ vs) = v
vLookup (F.suc i) (v V∷ vs) = vLookup i vs


data All  {p : Level} (P : Pred Term p) : Term → Set p
data AllV {p : Level} (P : Pred Term p) : Vec Term n → Set p

-- All P t: "The term t satisy P, and all its subterms satisy P recursively".
data All P where
    all-num    : {n : ℕ}
        → P (num n)
        → All P (num n)
    all-var    : {x : ℕ}
        → P (var x)
        → All P (var x)
    all-let    : {t1 t2 : Term}
        → P (Let t1 In t2)
        → All P t1
        → All P t2
        → All P (Let t1 In t2)
    all-call   : {fid : FunId} {ts : Vec Term n}
        → P (call fid ts)
        → AllV P ts
        → All  P (call fid ts)
    all-if     : {t1 t2 t3 : Term}
        → P (if t1 then t2 else t3)
        → All P t1
        → All P t2
        → All P t3
        → All P (if t1 then t2 else t3)
    all-pack   : {sid : StrId} {ts : Vec Term n}
        → P (pack sid ts)
        → AllV P ts
        → All  P (pack sid ts)
    all-unpack : {t1 t2 : Term}
        → P (unpack t1 In t2)
        → All P t1
        → All P t2
        → All P (unpack t1 In t2)
    all-·      : {t : Term} {j : Fin Nsf}
        → P (t · j)
        → All P t
        → All P (t · j)
    all-pub    : {t : Term}
        → P (pub t)
        → All P t
        → All P (pub t)
    all-struct : {k : K} {sid : StrId} {ts : Vec Term n}
        → P (struct k sid ts)
        → AllV P ts
        → All  P (struct k sid ts)
    all-exec   : {M2 : Fin Nm} {t : Term}
        → P (exec M2 t)
        → All P t
        → All P (exec M2 t)

data AllV P where
    all-vec[]  : AllV P V.[]
    all-vec∷   : {t : Term} {ts : Vec Term n}
        → All  P t
        → AllV P ts
        → AllV P (t V.∷ ts)

allLookup : {p : Level} {ts : Vec Term n} {P : Pred Term p} →
    (i : Fin n) → AllV P ts → All P (V.lookup ts i)
allLookup F.zero    (all-vec∷ a as) = a
allLookup (F.suc i) (all-vec∷ a as) = allLookup i as


-------------------------------------------------------------- UTILITY FUNCTIONS
_⨾ : {A : Set} → A → V.Vec A 1
_⨾ x = x V.∷ V.[]

infix 40 _⨾

#0 = # 0; #1 = # 1; #2 = # 2; #3 = # 3; #4 = # 4
#5 = # 5; #6 = # 6; #7 = # 7; #8 = # 8


v0 v1 v2 v3 v4 v5 v6 : LTerm
v0 = var 0; v1 = var 1; v2 = var 2; v3 = var 3
v4 = var 4; v5 = var 5; v6 = var 6

v0' v1' v2' v3' v4' v5' v6' : Term
v0' = var 0; v1' = var 1; v2' = var 2; v3' = var 3
v4' = var 4; v5' = var 5; v6' = var 6


N0 N1 N2 N3 N4 N5 N6 : LTerm
N0 = num 0; N1 = num 1; N2 = num 2; N3 = num 3
N4 = num 4; N5 = num 5; N6 = num 6

N0' N1' N2' N3' N4' N5' N6' : Term
N0' = num 0; N1' = num 1; N2' = num 2; N3' = num 3
N4' = num 4; N5' = num 5; N6' = num 6
