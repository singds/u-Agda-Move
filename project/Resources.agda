open import project.IncludeBase
import project.Syntax as Syntax
import project.Typing as Typing

module project.Resources
    (Nm Ns Nf Nsf Nfa : ℕ)
    (P : Syntax.Program Nm Ns Nf Nsf Nfa)
    where

open Syntax Nm Ns Nf Nsf Nfa
open Typing Nm Ns Nf Nsf Nfa P
open import project.Evaluation Nm Ns Nf Nsf Nfa P
open import Data.List.Relation.Binary.Permutation.Propositional

private
    variable
        t t'    : Term
        n l lv  : ℕ
        M M2    : Fin Nm


-- R t: "The resources of t"
-- R defines what we consider the resources of a term.
-- The resources of a term are a list of keys (or better, a list of identifiers),
--   that is the list of struct identifiers appearing in the term (with their multiplicity).
-- R t is a list, but we don't care about the order of the elements in the list.
-- We use the list type to represent a multi-set.
R  :           Term       → List K
Rv : {n : ℕ} → Vec Term n → List K

R (num n)                   = L.[]
R (var x)                   = L.[]
R (Let t1 In t2)            = R t1 L.++ R t2
R (call fid ts)             = Rv ts
R (if t1 then t2 else t3)   = R t1 L.++ R t2
R (pack sid ts)             = Rv ts
R (unpack t1 In t2)         = R t1 L.++ R t2
R (t · j)                   = L.[]
R (pub t)                   = R t
R (struct k sid ts) with tyIsLin (Tst sid)
... | yes yLin              = k L.∷ Rv ts
... | no  nLin              = Rv ts
R (exec M2 t)               = R t

Rv V.[]         = L.[]
Rv (t V.∷ ts)   = R t L.++ (Rv ts)


-- RI ev: "The resources introduced by ev"
-- RI defines what are the resources introduced by a step of evaluation.
-- The output is a multi-set of sturct identifiers, that we represent as a list.
RI  :                         M ∋ t  ⇒  t'  → List K
RIv : {ts ts' : Vec Term n} → M ∋ ts ⇒v ts' → List K

RI (Elet ev)     = RI ev
RI (Elet2 v)     = L.[]
RI (Epack evv)   = RIv evv
RI (Epacked {M = M} {s = s} k vs) with tyIsLin (Tst (sId M s))
... | yes yLin   = k L.∷ L.[]
... | no  nLin   = L.[]
RI (Eunpack ev)  = RI ev
RI (Eunpacked x) = L.[]
RI (Ecall evv)   = RIv evv
RI (Ecalled vs)  = L.[]
RI (Eexec ev)    = RI ev
RI (Eexecuted x) = L.[]
RI (Eif ev)      = RI ev
RI (Eiftrue nz)  = L.[]
RI Eiffalse      = L.[]
RI (Eselect vs)  = L.[]
RI (Epub ev)     = RI ev
RI (Epub2 v)     = L.[]

RIv (E[ ev ] vs) = RI ev
RIv (t E∷ evv)   = RIv evv


-- RI ev: "The resources used by ev"
RU  :                         M ∋ t  ⇒  t'  → List K
RUv : {ts ts' : Vec Term n} → M ∋ ts ⇒v ts' → List K

RU (Elet ev)         = RU ev
RU (Elet2 v)         = L.[]
RU (Epack evv)       = RUv evv
RU (Epacked k vs)    = L.[]
RU (Eunpack ev)      = RU ev
RU (Eunpacked {M = M} {k = k} {s = s} vs) with tyIsLin (Tst (sId M s))
... | yes yLin       = k L.∷ L.[]
... | no  nLin       = L.[]
RU (Ecall evv)       = RUv evv
RU (Ecalled vs)      = L.[]
RU (Eexec ev)        = RU ev
RU (Eexecuted x)     = L.[]
RU (Eif ev)          = RU ev
RU (Eiftrue nz)      = L.[]
RU Eiffalse          = L.[]
RU (Eselect vs)      = L.[]
RU (Epub ev)         = RU ev
RU (Epub2 {t = t} v) = R t

RUv (E[ ev ] vs)   = RU ev
RUv (t E∷ evv)     = RUv evv


-- A predicate about a Term: "If t is an if-then-else term, then R t2 ↭ R t3"
tIsIf⇒Rt2↭Rt3 : Term → Set
tIsIf⇒Rt2↭Rt3 t = {t1 t2 t3 : Term}
    → t ≡ if t1 then t2 else t3
    → R t2 ↭ R t3



-- Language terms, which are a subset of all the terms of the language, never contain resources.
-- More precisely, terms that are the outputs of a conversion from a language term (LTerm)
--   to a term (Term), don't contain resources.
Rlterm≡[] : (t : LTerm)                    → R  (toRun t)      ≡ L.[]
Rlterm≡[]-vec : {n : ℕ} (ts : Vec LTerm n) → Rv (toRun-vec ts) ≡ L.[]

Rlterm≡[] (num n)                                                       = refl
Rlterm≡[] (var x)                                                       = refl
Rlterm≡[] (Let t1 In t2)            rewrite Rlterm≡[] t1 | Rlterm≡[] t2 = refl
Rlterm≡[] (call fid ts)             rewrite Rlterm≡[]-vec ts            = refl
Rlterm≡[] (if t1 then t2 else t3)   rewrite Rlterm≡[] t1 | Rlterm≡[] t2 = refl
Rlterm≡[] (pack sid ts)             rewrite Rlterm≡[]-vec ts            = refl
Rlterm≡[] (unpack t1 In t2)         rewrite Rlterm≡[] t1 | Rlterm≡[] t2 = refl
Rlterm≡[] (x · j)                                                       = refl
Rlterm≡[] (pub t)                   rewrite Rlterm≡[] t                 = refl

Rlterm≡[]-vec V.[]                                              = refl
Rlterm≡[]-vec (t V.∷ ts) rewrite Rlterm≡[] t | Rlterm≡[]-vec ts = refl


-- The shift-back operation applied to a term doesn't change its resources.
shift-back-presR : (c : ℕ) → (t : Term)
    → R (shift-back c t) ≡ R t
shift-back-presR-vec : (c : ℕ) → (ts : Vec Term n)
    → Rv (shift-back-vec c ts) ≡ Rv ts

shift-back-presR c (num n) = refl
shift-back-presR c (var x) with x <? c
... | yes p = refl
... | no ¬p = refl
shift-back-presR c (Let t1 In t2)
    rewrite shift-back-presR c t1 | shift-back-presR (c + 1) t2 = refl
shift-back-presR c (call fid ts) rewrite shift-back-presR-vec c ts = refl
shift-back-presR c (pack sid ts) rewrite shift-back-presR-vec c ts = refl
shift-back-presR c (struct k sid ts) with tyIsLin (Tst sid)
... | yes _ rewrite shift-back-presR-vec c ts = refl
... | no  _ rewrite shift-back-presR-vec c ts = refl
shift-back-presR c (if t1 then t2 else t3)
    rewrite shift-back-presR c t1 | shift-back-presR c t2 = refl
shift-back-presR c (unpack t1 In t2)
    rewrite shift-back-presR c t1 | shift-back-presR (c + Nsf) t2 = refl
shift-back-presR c (t · j) = refl
shift-back-presR c (pub t) rewrite shift-back-presR c t = refl
shift-back-presR c (exec M2 t) = refl

shift-back-presR-vec c V.[] = refl
shift-back-presR-vec c (t V.∷ ts)
    rewrite shift-back-presR c t | shift-back-presR-vec c ts = refl
