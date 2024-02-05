open import project.IncludeBase
import project.Syntax as Syntax

module project.Evaluation
    (Nm Ns Nf Nsf Nfa : ℕ)
    (P : Syntax.Program Nm Ns Nf Nsf Nfa)
    where

open Syntax Nm Ns Nf Nsf Nfa
open import project.Utility Nm Ns Nf Nsf Nfa P


private
    variable
        t t' t1 t1' t2 t2' t3 : Term
        n n1 n2 x             : ℕ
        M M1 M2               : Fin Nm
        fid                   : FunId



-- Substitute all the occurences of variable j in t2 with the term t1.
subst     : (j : ℕ) → (t1 : Term) → (t2 : Term) → Term
-- The same substitution as above, but on each term of the vector
subst-vec : (j : ℕ) → (t1 : Term) → (ts : Vec Term n) → Vec Term n


subst j t1 (num n) = num n
subst j t1 (var x) with x ≟ j
... | no ¬p = var x
... | yes p = t1
subst j t1 (Let t2 In t3) = Let (subst j t1 t2) In (subst (j + 1) t1 t3)
subst j t1 (call id ts) = call id (subst-vec j t1 ts)
subst j t1 (if t2 then t3 else t4) = if (subst j t1 t2) then (subst j t1 t3) else (subst j t1 t4)
subst j t1 (pack id ts) = pack id (subst-vec j t1 ts)
subst j t1 (struct k id ts) = struct k id (subst-vec j t1 ts)
subst j t1 (unpack t2 In t3) = unpack (subst j t1 t2) In (subst (j + Nsf) t1 t3)
subst j t1 (exec m t) = exec m t
subst j t1 (t · q) = (subst j t1 t) · q
subst j t1 (pub t) = pub (subst j t1 t)

-- Apply the substitution to a vector of terms
subst-vec j t1 V.[] = V.[]
subst-vec j t1 (t V.∷ ts) = (subst j t1 t) V.∷ (subst-vec j t1 ts)



-- Shift operation (used to define substitution)
-- Used to increase by "d" (shift up) the free variables of a term.
shift     : (d : ℕ) → (d : ℕ) → Term → Term
shift-vec : (d : ℕ) → (c : ℕ) → (ts : Vec Term n) → Vec Term n

shift d c (num n) = num n
shift d c (var x) with x <? c
... | yes  p                       = var x
... | no  ¬p                       = var (x + d)
shift d c (Let t1 In t2)           = Let (shift d c t1) In (shift d (suc c) t2)
shift d c (call id ts)             = call id (shift-vec d c ts)
shift d c (if t1 then t2 else t3)  = if (shift d c t1) then (shift d c t2) else (shift d c t3)
shift d c (pack id ts)             = pack id (shift-vec d c ts)
shift d c (struct k id ts)         = struct k id (shift-vec d c ts)
shift d c (unpack t1 In t2)        = unpack (shift d c t1) In (shift d (c + Nsf) t2)
shift d c (exec m t)               = exec m t
shift d c (t · j)                  = (shift d c t) · j
shift d c (pub t)                  = pub (shift d c t)

shift-vec d c V.[] = V.[]
shift-vec d c (t V.∷ ts) = (shift d c t) V.∷ (shift-vec d c ts)



-- Decrease by 1 all the de-Brujin that are < c that appear in t1.
shift-back     : (c : ℕ) → (t1 : Term) → Term
-- The same shift as above but applied to each term of the vector
shift-back-vec : (c : ℕ) → (ts : Vec Term n) → Vec Term n

-- Shift-back by 1 all the de-Brujin indexes of a term
shift-back c (num n)              = num n
shift-back c (var x) with x <? c 
... | yes p = var x
... | no ¬p = var (x - 1)
shift-back c (Let t1 In t2)           = Let (shift-back c t1) In (shift-back (c + 1) t2)
shift-back c (call id ts)             = call id (shift-back-vec c ts)
shift-back c (if t1 then t2 else t3)  = if (shift-back c t1) then (shift-back c t2) else (shift-back c t3)
shift-back c (pack id ts)             = pack id (shift-back-vec c ts)
shift-back c (struct k id ts)         = struct k id (shift-back-vec c ts)
shift-back c (unpack t1 In t2)        = unpack (shift-back c t1) In (shift-back (c + Nsf) t2)
shift-back c (exec m t)               = exec m t
shift-back c (t · j)                  = (shift-back c t) · j
shift-back c (pub t)                  = pub (shift-back c t)


-- Shift-back by 1 all the de-Brujin indexes in a vector of terms
shift-back-vec c V.[] = V.[]
shift-back-vec c (t V.∷ ts) = (shift-back c t) V.∷ (shift-back-vec c ts)


subst+back : (j : ℕ) → (t1 : Term) → (t2 : Term) → Term
subst+back j t1 t2 = shift-back j (subst j t1 t2)

subst+back-vec : (j : ℕ) → (t1 : Term) → (ts : Vec Term n) → Vec Term n
subst+back-vec j t1 ts = shift-back-vec j (subst-vec j t1 ts)


{-
Beta reduction.
Just to get an idea:
    `var 0` occuring in `t2` are replaced by ts[len(ts) - 1].
    `var 1` occuring in `t2` are replaced by ts[len(ts) - 2].
    and so on...
    `var (len(ts) - 1)` occuring in `t2` are replaced by ts[0].
-}
beta-red : (ts : Vec Term n) → (t : Term) → Term
beta-red V.[]        t = t
beta-red (t1 V.∷ ts) t = shift-back 0 (subst 0 t1 (beta-red ts t))

-- t1 ⇒ t2   means    "Term t1 can do a step to t2".
data _∋_⇒_ : Fin Nm → Term → Term → Set
-- ts1 ⇒v ts2 means   "A term inside ts1 can do a step such that ts1 goes to ts2 ".
data _∋_⇒v_ : Fin Nm → Vec Term n → Vec Term n → Set


-- When a term can do a step.
data _∋_⇒_ where

    Elet :
          (ev : M ∋ t1 ⇒ t1')
        --------------------
        → M ∋ (Let t1 In t2) ⇒ (Let t1' In t2)
    
    Elet2 :
          (v : Value t1)
        --------------------
        → M ∋ (Let t1 In t2) ⇒ beta-red (t1 V.∷ V.[]) t2

    Epack :
          {s : Fin Ns}
          {ts ts' : Vec Term Nsf}
        → (ev : M ∋ ts ⇒v ts')
        --------------------
        → M ∋ (pack (sId M s) ts) ⇒ (pack (sId M s) ts')

    Epacked :
          {s : Fin Ns}
          {ts : Vec Term Nsf}
        → (k : K)
        → (vs : ValueV ts)
        --------------------
        → M ∋ (pack (sId M s) ts) ⇒ (struct k (sId M s) ts)

    Eunpack :
          (ev : M ∋ t1 ⇒ t1')
        --------------------
        → M ∋ (unpack t1 In t2) ⇒ (unpack t1' In t2)

    Eunpacked :
          {k : K}
          {s : Fin Ns}
          {ts : Vec Term Nsf}
        → (vs : ValueV ts)
        --------------------
        → M ∋ (unpack (struct k (sId M s) ts) In t2) ⇒ beta-red ts t2

    Ecall :
          {ts ts' : Vec Term Nfa}
        → (ev : M ∋ ts ⇒v ts')
        --------------------
        → M ∋ (call fid ts) ⇒ (call fid ts')

    Ecalled :
          {f : Fin Nf}
        → {ts : Vec Term Nfa}
        → (vs : ValueV ts)
        --------------------
        → M ∋ (call (fId M2 f) ts) ⇒ exec M2 (beta-red ts (toRun (body M2 f)))

    Eexec :
          (ev : M2 ∋ t ⇒ t')
        --------------------
        → M ∋ (exec M2 t) ⇒ (exec M2 t')

    Eexecuted :
          Value t
        --------------------
        → M ∋ (exec M2 t) ⇒ t

    Eif :
          M ∋ t1 ⇒ t1'
        --------------------
        → M ∋ (if t1 then t2 else t3) ⇒ (if t1' then t2 else t3)

    Eiftrue :
          {g : ℕ} → (nz : ¬ g ≡ 0)
        --------------------
        → M ∋ (if (num g) then t2 else t3) ⇒ t2
    
    Eiffalse :
        M ∋ (if (num 0) then t2 else t3) ⇒ t3

    Eselect :
          {k : K} {s  : Fin Ns}
          {ts : Vec Term Nsf}
          {j  : Fin Nsf}
        → (vs : ValueV ts)
        --------------------
        → M ∋ (struct k (sId M s) ts) · j ⇒ V.lookup ts j

    Epub :
          M ∋ t ⇒ t'
        --------------------
        → M ∋ (pub t) ⇒ (pub t')

    Epub2 :
          (v : Value t)
        --------------------
        → M ∋ (pub t) ⇒ num 0



-- When a vector of terms can do a step.
data _∋_⇒v_ where
    E[_]_ : -- some term inside ts1 can do a step
          {ts : Vec Term n2}
        → M ∋ t ⇒ t'
        → ValueV ts
        --------------------
        → M ∋ (t V.∷ ts) ⇒v (t' V.∷ ts)
    
    _E∷_ :
          {ts ts' : Vec Term n}
        → (t : Term)
        → M ∋ ts ⇒v ts'
        --------------------
        → M ∋ (t V.∷ ts) ⇒v (t V.∷ ts')





-- Evaluation in multiple steps.
-- The "evaluation in multiple steps" relation is the reflexive and transitive
--   closure of the one-step evaluation relation.
data _∋_⇒*_ : Fin Nm → Term → Term → Set where
    e-refl  : M ∋ t1 ⇒* t1  -- reflexivity
    e-trans : M ∋ t1 ⇒* t2  -- transitivity
            → M ∋ t2 ⇒  t3
            → M ∋ t1 ⇒* t3


-- -----------------------------------------------------------------------------
-- ------------------------------------------------------------ HELPER FUNCTIONS
ev-proof : M ∋ t1 ⇒  t2
        →  M ∋ t2 ⇒* t3
        →  M ∋ t1 ⇒* t3
ev-proof p1 e-refl           = e-trans e-refl p1
ev-proof p1 (e-trans p2 p3)  = e-trans (ev-proof p1 p2) p3


begin⇒_ : (t : Term) → Term
begin⇒ t = t


_⇒⟨_⟩_ : (t1 : Term)
    → M ∋ t1 ⇒ t2
    → M ∋ t2 ⇒* t3
    → M ∋ t1 ⇒* t3
t1 ⇒⟨ p1 ⟩ p2 = ev-proof p1 p2

_⇒∎ : (t : Term) → M ∋ t ⇒* t
t ⇒∎ = e-refl


infix  4 begin⇒_
infix  3 _⇒∎
infixr 2 _⇒⟨_⟩_



