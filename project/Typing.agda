open import project.IncludeBase
import project.Syntax as Syntax

module project.Typing
    (Nm Ns Nf Nsf Nfa : ℕ)
    (P : Syntax.Program Nm Ns Nf Nsf Nfa)
    where

open Syntax Nm Ns Nf Nsf Nfa
open import project.Utility Nm Ns Nf Nsf Nfa P


-- A base environment is a vector of types.
Env = Vec Type

-- A Usage is a type T with a marker, either ∘ or •.
-- T ∘ and T • are two elements of type Usage T.
data Usage : Type → Set where
    _∘ : (T : Type) → Usage T
    _• : (T : Type) → Usage T

-- A Usage environment is a vector of Usages.
data UEnv : {l : ℕ} → Env l → Set where
    []   : UEnv V.[]
    _u∷_ : {l : ℕ} {T : Type} {Δ : Env l}
        → Usage T → UEnv Δ
        → UEnv (T V.∷ Δ)

infixr 5 _u∷_

----------------------------------------------------- MANIPULATION FUNC FOR UENV
uLookup : {l : ℕ} {Δ : Env l} →
    (i : Fin l) → UEnv Δ → Usage (V.lookup Δ i)
uLookup F.zero    (T u∷ Γ) = T
uLookup (F.suc i) (T u∷ Γ) = uLookup i Γ

_u++_ : {l1 l2 : ℕ} {Δ1 : Env l1} {Δ2 : Env l2} →
    UEnv Δ1 → UEnv Δ2 → UEnv (Δ1 V.++ Δ2)
[] u++ ys        = ys
(x u∷ xs) u++ ys = x u∷ (xs u++ ys)

uInsert : {l : ℕ} {Δ : Env l} → {T : Type} →
    UEnv Δ → (i : Fin (suc l)) → Usage T → UEnv (V.insert Δ i T)
uInsert Γ         F.zero    U  = U u∷ Γ
uInsert (U1 u∷ Γ) (F.suc i) U2 = U1 u∷ uInsert Γ i U2

uRemove : {l : ℕ} {Δ : Env (suc l)} →
    UEnv Δ → (i : Fin (suc l)) → UEnv (V.remove Δ i)
uRemove (_ u∷ Γ)          F.zero    = Γ
uRemove (U1 u∷ (U2 u∷ Γ)) (F.suc i) = U1 u∷ uRemove (U2 u∷ Γ) i

uUpdateAt : {l : ℕ} {Δ : Env l} →
    (i : Fin l) → ({T : Type} → Usage T → Usage T) → UEnv Δ → UEnv Δ
uUpdateAt F.zero    f (U u∷ Γ) = f U u∷ Γ
uUpdateAt (F.suc i) f (U u∷ Γ) = U   u∷ uUpdateAt i f Γ



private
    variable
        l           : ℕ
        Δ           : Env l
        Γ Γ1 Γ2 Γ3  : UEnv Δ
        T T1 T2     : Type
        t t1 t2 t3  : Term
        n x         : ℕ

-- IsLinear T: "The type T is linear."
data IsLinear : Type → Set where
    lin :
          {m : Fin Nm} {s : Fin Ns}
        → gIsLin m s ≡ true
        → IsLinear (Tst (sId m s))

-- Computable function to check if a type is linear
tyIsLin : (T : Type) → Dec (IsLinear T)
tyIsLin Tint                 = no (λ { () })
tyIsLin (Tst (sId m s)) with gIsLin m s BP.≟ true
tyIsLin (Tst (sId m s)) | no ¬p = no λ { (lin {.m} {.s} pl) → ¬p pl }
tyIsLin (Tst (sId m s)) | yes p = yes (lin p)

-- Tint is not linear
¬linTint : ¬ IsLinear Tint
¬linTint ()

data HasTypeX : UEnv Δ → ℕ → Type → UEnv Δ → Set
data HasType  (M : Fin Nm) : UEnv Δ → Term → Type → UEnv Δ → Set
data HasTypeV (M : Fin Nm) : UEnv Δ → Vec Term n → Vec Type n → UEnv Δ → Set
data HasTypeI (M : Fin Nm) : UEnv Δ → Vec Type n → Term → Type → UEnv Δ → Set

data HasTypeX where
    Xz  : -- Lookup of a variable with normal type
          (nLin : ¬ IsLinear T)
        --------------------
        → HasTypeX ((T ∘) u∷ Γ) 0 T ((T ∘) u∷ Γ)
        --                              ^----------- note the ∘

    XzL : -- Lookup of a linear variable with linear type
          (yLin : IsLinear T)
        --------------------
        → HasTypeX ((T ∘) u∷ Γ) 0 T ((T •) u∷ Γ)
        --                              ^----------- note the •

    Xs  : {U : Usage T2}
        → (htx : HasTypeX Γ1 x T Γ2)
        --------------------
        → HasTypeX (U u∷ Γ1) (suc x) T (U u∷ Γ2)


htxIsTy :
    {Γ1 Γ2 : UEnv Δ}
    {i : Fin l}
    → HasTypeX Γ1 (toℕ i) T Γ2
    → T ≡ V.lookup Δ i
htxIsTy {i = Fin.zero}  (Xz  nLin) = refl
htxIsTy {i = Fin.zero}  (XzL yLin) = refl
htxIsTy {i = Fin.suc i} (Xs htx)   = htxIsTy htx


-- HasType M Γ1 t T Γ2: "In env. Γ1, term t has type T,
--  and Γ2 is the env. Γ1 with the linear variables used by t marked as used.
--  M is the module executing the term."
data HasType M where
    Tnum :
        --------------------
        HasType M Γ (num n) Tint Γ

    Tvar :
          (htx : HasTypeX Γ1 x T Γ2)
        --------------------
        → HasType M Γ1 (var x) T Γ2
    
    Tlet :
          (ht  : HasType M Γ1 t1 T1 Γ2)
        → (hti : HasTypeI M Γ2 (T1 V.∷ V.[]) t2 T2 Γ3)
        --------------------
        → HasType M Γ1 (Let t1 In t2) T2 Γ3

    Tpack :
          {s : Fin Ns}
        → {ts : Vec Term Nsf}
        → (htv : HasTypeV M Γ1 ts (gFieldsT M s) Γ2)
        --------------------
        → HasType M Γ1 (pack (sId M s) ts) (Tst (sId M s)) Γ2

    Tstruct :
          {k : K} {s : Fin Ns}
          {M2 : Fin Nm}
        → {ts : Vec Term Nsf}
        → (vs : ValueV ts)
        → (htv : HasTypeV M Γ ts (gFieldsT M2 s) Γ)
        --------------------
        → HasType M Γ (struct k (sId M2 s) ts) (Tst (sId M2 s)) Γ

    Tcall :
          {M2 : Fin Nm}
        → {f : Fin Nf}
        → {ts : Vec Term Nfa}
        → (htv : HasTypeV M Γ1 ts (gArgsT M2 f) Γ2)
        --------------------
        → HasType M Γ1 (call (fId M2 f) ts) (gRetT M2 f) Γ2

    Tunpack :
          {s : Fin Ns}
        → (ht  : HasType  M Γ1 t1 (Tst (sId M s)) Γ2)
        → (hti : HasTypeI M Γ2 (gFieldsT M s) t2 T2 Γ3)
        --------------------
        → HasType M Γ1 (unpack t1 In t2) T2 Γ3

    Texec :
          {M2 : Fin Nm}
        → HasType M2 [] t T []
        --------------------
        → HasType M Γ (exec M2 t) T Γ

    Tif :
          (ht1 : HasType M Γ1 t1 Tint Γ2)
        → (ht2 : HasType M Γ2 t2 T    Γ3)
        → (ht3 : HasType M Γ2 t3 T    Γ3)
        --------------------
        → HasType M Γ1 (if t1 then t2 else t3) T Γ3

    TselX :
          {s : Fin Ns}
          {j : Fin Nsf}
        → (htx : HasTypeX Γ1 x (Tst (sId M s)) Γ2)
        → (nLin : ¬ IsLinear (V.lookup (gFieldsT M s) j))
        --------------------
        → HasType M Γ1 ((var x) · j) (V.lookup (gFieldsT M s) j) Γ1

    TselV :
          {s : Fin Ns}
          {j : Fin Nsf}
        → (v  : Value t)
        → (ht : HasType M Γ t (Tst (sId M s)) Γ)
        → (nLin : ¬ IsLinear (V.lookup (gFieldsT M s) j))
        --------------------
        → HasType M Γ (t · j) (V.lookup (gFieldsT M s) j) Γ

    Tpub :
          (ht   : HasType M Γ1 t T Γ2)
        → (yLin : IsLinear T)
        --------------------
        → HasType M Γ1 (pub t) Tint Γ2


-- HasTypeI M Γ1 Ts t T Γ2: "In env. Γ1 extended with the Vec of types Ts, term t has type T,
--  and Γ2 is the env. Γ1 with the linear variables used by t marked as used.
--  M is the module executing the term."
data HasTypeI M where
    I[_] :
          (ht : HasType M Γ1 t T Γ2)
        --------------------
        → HasTypeI M Γ1 V.[] t T Γ2

    _I∷_ :
          {Ts : Vec Type n}
        → (nLin : ¬ IsLinear T1)
        → (hti  : HasTypeI M ((T1 ∘) u∷ Γ1) Ts t T ((T1 ∘) u∷ Γ2))
        --------------------
        → HasTypeI M Γ1 (T1 V.∷ Ts) t T Γ2

    _I∷l_ :
          {Ts : Vec Type n}
        → (yLin : IsLinear T1)
        → (hti  : HasTypeI M ((T1 ∘) u∷ Γ1) Ts t T ((T1 •) u∷ Γ2))
        --------------------
        → HasTypeI M Γ1 (T1 V.∷ Ts) t T Γ2

infixr 5 _I∷_
infixr 5 _I∷l_

-- HasTypeV M Γ1 ts Ts Γ2: "In env. Γ1 the terms ts have types Ts with out context Γ2."
data HasTypeV M where
    T[] :
        --------------------
        HasTypeV M Γ V.[] V.[] Γ

    _T∷_ :
        {ts : Vec Term n}
        → {Ts : Vec Type n}
        → HasType  M Γ1 t T Γ2
        → HasTypeV M Γ2 ts Ts Γ3
        --------------------        
        → HasTypeV M Γ1 (t V.∷ ts) (T V.∷ Ts) Γ3

infixr 5 _T∷_


-- WellFun M F: "The function F in module M is well formed."
record WellFun (M : Fin Nm) (F : Fin Nf) : Set where
    constructor well
    field
        hti : HasTypeI M [] (gArgsT M F) (toRun (gBody M F)) (gRetT M F) []

-- WellStr M S: "The struct S in module M is well formed."
record WellStr (M : Fin Nm) (S : Fin Ns) : Set where
    constructor well
    field
        nLin : (¬ IsLinear (Tst (sId M S))
            → (j : Fin Nsf)
            → ¬ IsLinear (V.lookup (gFieldsT M S) j))

-- WellMod M: "The module M is well formed."
record WellMod (M : Fin Nm) : Set where
    field
        wf : (F : Fin Nf) → WellFun M F
        ws : (S : Fin Ns) → WellStr M S

WellProg = ∀ (M : Fin Nm) → WellMod M


wellF : WellProg → (M : Fin Nm) → (F : Fin Nf) → WellFun M F
wellF wp M F = WellMod.wf (wp M) F

wellHti : WellProg → (M : Fin Nm) → (F : Fin Nf) → HasTypeI M [] (gArgsT M F) (toRun (gBody M F)) (gRetT M F) []
wellHti wp M F = WellFun.hti (wellF wp M F)
