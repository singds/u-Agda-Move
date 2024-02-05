{-# OPTIONS --allow-unsolved-metas #-}

import Data.Nat
import project.Syntax as Syntax
import project.Typing as Typing

module project.Properties.FreeVar-old
    (Nm Ns Nf Nsf Nfa : Data.Nat.ℕ)
    (P : Syntax.Program Nm Ns Nf Nsf Nfa)
    where

open import project.IncludeBase
open Syntax Nm Ns Nf Nsf Nfa
open import project.Evaluation Nm Ns Nf Nsf Nfa P


import Data.List.Membership.DecPropositional as DecPropMembership

open DecPropMembership Nat._≟_ public
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Binary.Subtraction

private
    variable
        n        : ℕ
        t tv     : Term
        t1 t2 t3 : Term

postulate
    y≡x⇒y∈fvx       : {x y : ℕ} → y ≡ x → y ∈ fv (var x)
    ¬y∈fvx⇒¬y≡x     : {x y : ℕ} → ¬ (y ∈ fv (var x)) → ¬ (y ≡ x)
    y∈fvx⇒x∈fvy     : {x y : ℕ} → y ∈ fv (var x) → x ∈ fv (var y)
    ¬y∈fvx⇒¬x∈fvy   : {x y : ℕ} → y ∉ fv (var x) → x ∉ fv (var y)

    ¬x∈fvif⇒¬x∈fvt1 : {x : ℕ} → x ∉ fv (if t1 then t2 else t3) → x ∉ fv t1
    ¬x∈fvif⇒¬x∈fvt2 : {x : ℕ} → x ∉ fv (if t1 then t2 else t3) → x ∉ fv t2
    ¬x∈fvif⇒¬x∈fvt3 : {x : ℕ} → x ∉ fv (if t1 then t2 else t3) → x ∉ fv t3
    
    x∉fvtts⇒x∉fvt   : {x : ℕ} → {ts : Vec Term n} → x ∉ fvVec (t V.∷ ts) → x ∉ fv t
    x∉fvtts⇒x∉fvts  : {x : ℕ} → {ts : Vec Term n} → x ∉ fvVec (t V.∷ ts) → x ∉ fvVec ts

    x∉fvlet⇒x∉fvt1  : {x : ℕ} → x ∉ fv (Let t1 In t2) → x ∉ fv t1
    x∉fvlet⇒x∉fvt2  : {x : ℕ} → x ∉ fv (Let t1 In t2) → (x + 1) ∉ fv t2

    x∉fvunp⇒x∉fvt1  : {x : ℕ} → x ∉ fv (unpack t1 In t2) → x ∉ fv t1
    x∉fvunp⇒x∉fvt2  : {x : ℕ} → x ∉ fv (unpack t1 In t2) → (x + Nsf) ∉ fv t2

fv-val : Value t → fv t ≡ L.[]
fv-valVec : {ts : Vec Term n} → ValueV ts → fvVec ts ≡ L.[]

fv-val Vnum = refl
fv-val (Vstruct vs) rewrite fv-valVec vs = refl

fv-valVec V[] = refl
fv-valVec (v V∷ vs) rewrite fv-val v | fv-valVec vs = refl


fv-subst : Value tv → (t : Term) → (x : ℕ) → x ∉ (fv (subst x tv t))
fv-substVec : Value tv → (ts : Vec Term n) → (x : ℕ) → x ∉ (fvVec (subst-vec x tv ts))

fv-subst = {!   !}
fv-substVec = {!   !}
