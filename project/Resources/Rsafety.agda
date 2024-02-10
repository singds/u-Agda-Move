import Data.Nat
import project.Syntax as Syntax
import project.Typing as Typing

module project.Resources.Rsafety
    (Nm Ns Nf Nsf Nfa : Data.Nat.ℕ)
    (P : Syntax.Program Nm Ns Nf Nsf Nfa)
    (W : Typing.WellProg Nm Ns Nf Nsf Nfa P)
    where

open import project.Properties.Include Nm Ns Nf Nsf Nfa P
open import project.Properties.UsageConstraints Nm Ns Nf Nsf Nfa P
open import project.Properties.Misc Nm Ns Nf Nsf Nfa P
open import project.Properties.ValueType Nm Ns Nf Nsf Nfa P
open import project.Resources.RnonLinValues Nm Ns Nf Nsf Nfa P W
open import project.Resources.Rsubstitution Nm Ns Nf Nsf Nfa P W
open import project.Resources.RifBranches Nm Ns Nf Nsf Nfa P W

open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
open PermutationReasoning

private
    variable
        n l lv  : ℕ
        Δ       : Env l
        M M2    : Fin Nm
        Γ1 Γ2   : UEnv Δ
        t t'    : Term
        T       : Type


lemma↭3 : {xs xs' : List K}
    → (ys zs ws : List K)
    → zs L.++ xs ↭ ws L.++ xs'
    → zs L.++ (xs L.++ ys) ↭ ws L.++ (xs' L.++ ys)
lemma↭3 {xs} {xs'} ys zs ws p1 = begin
    zs   L.++ (xs  L.++ ys)     ↭⟨ ↭-sym (++-assoc zs xs ys) ⟩
    (zs  L.++ xs)  L.++ ys      ↭⟨ ++⁺ʳ ys p1 ⟩
    (ws  L.++ xs') L.++ ys      ↭⟨ ++-assoc ws xs' ys ⟩
    ws L.++ (xs' L.++ ys) ∎



Rsafety :
      All tIsIf⇒Rt2↭Rt3 t
    → HasType M Γ1 t T Γ2
    → (ev : M ∋ t ⇒ t')
    → RI ev L.++ R t ↭ RU ev L.++ R t'
Rsafety-vec :
    {ts ts' : Vec Term n} {Ts : Vec Type n}
    → AllV tIsIf⇒Rt2↭Rt3 ts
    → HasTypeV M Γ1 ts Ts Γ2
    → (ev : M ∋ ts ⇒v ts')
    → RIv ev L.++ Rv ts ↭ RUv ev L.++ Rv ts'

Rsafety (all-let p a1 a2) (Tlet {t1 = t1} {t2 = t2} ht hti) (Elet {t1' = t1'} ev)
    = lemma↭3 (R t2) (RI ev) (RU ev) (Rsafety a1 ht ev)
Rsafety a (Tlet {t1 = t1} {t2 = t2} ht hti) (Elet2 v)
    =
    begin
    R t1 L.++ R t2                   ↭⟨ ++-comm (R t1) (R t2) ⟩
    R t2 L.++ R t1                   ↭⟨ ++⁺ˡ (R t2) (↭-sym (++-identityʳ (R t1))) ⟩
    R t2 L.++ (R t1 L.++ L.[])       ↭⟨ ↭-sym ↭1 ⟩
    R (shift-back 0 (subst 0 t1 t2)) ∎
    where
        ↭1 = Rsubsti-multi (ht T∷ T[]) (v V∷ V[]) hti

Rsafety (all-pack p av) (Tpack htv) (Epack ev) = Rsafety-vec av htv ev
Rsafety a (Tpack {ts = ts} htv) (Epacked {M = M} {s = s} k x) with tyIsLin (Tst (sId M s))
... | yes yLin = refl
... | no  nLin = refl
Rsafety (all-call p av) (Tcall htv) (Ecall ev) = Rsafety-vec av htv ev

-- Here we use the fact that the function is well formed, and that the body
--   of the function is an LTerm (a language term).
-- LTerms are a subset of Terms
Rsafety a (Tcall {M2 = M2} {f = f} {ts = ts} htv) (Ecalled vs)
    = begin
    Rv ts               ↭⟨ refl ⟩
    L.[] L.++ Rv ts
        ↭⟨ ++⁺ʳ (Rv ts) (↭-sym (↭-reflexive (Rlterm≡[] (body M2 f)))) ⟩
    R (toRun (body M2 f)) L.++ Rv ts
        ↭⟨ ↭-sym (Rsubsti-multi htv vs (wellHti W M2 f)) ⟩
    R (beta-red ts (toRun (body M2 f))) ∎

Rsafety (all-unpack p a1 a2) (Tunpack {t1 = t1} {t2 = t2} ht hti) (Eunpack ev)
    = lemma↭3 (R t2) (RI ev) (RU ev) (Rsafety a1 ht ev)
Rsafety a (Tunpack (Tstruct _ htv) hti) (Eunpacked {M = M} {t2 = t2} {k = k} {s = s} {ts = ts} vs)
    with tyIsLin (Tst (sId M s))
... | yes yLin = begin
    k L.∷ (Rv ts L.++ R t2)   ↭⟨ prep k (++-comm (Rv ts) (R t2)) ⟩
    k L.∷ (R t2 L.++ Rv ts)   ↭⟨ prep k (↭-sym (Rsubsti-multi htv vs hti)) ⟩
    k L.∷ R (beta-red ts t2)  ∎
... | no  nLin = begin
    Rv ts L.++ R t2     ↭⟨ ++-comm (Rv ts) (R t2) ⟩
    R t2 L.++ Rv ts     ↭⟨ ↭-sym (Rsubsti-multi htv vs hti) ⟩
    R (beta-red ts t2) ∎

Rsafety (all-exec p a) (Texec ht) (Eexec ev) = Rsafety a ht ev
Rsafety a (Texec ht) (Eexecuted v) = refl
Rsafety (all-if p a1 a2 a3) (Tif {t2 = t2} ht1 ht2 ht3) (Eif ev)
    = lemma↭3 (R t2) (RI ev) (RU ev) (Rsafety a1 ht1 ev)
Rsafety a (Tif ht1 ht2 ht3) (Eiftrue nz) = refl

-- Here we use the tIsIf⇒Rt2↭Rt3 property
Rsafety (all-if p a1 a2 a3) (Tif {t3 = t3} ht1 ht2 ht3) Eiffalse = p refl

Rsafety a (TselV {j = j} v (Tstruct _ htv) nLin) (Eselect vs)
    rewrite RnLin (htvLookup vs htv j) nLin (vLookup j vs) = refl
Rsafety (all-pub p a) (Tpub ht yLin) (Epub ev) = Rsafety a ht ev
Rsafety a (Tpub {t = t} ht yLin) (Epub2 v) rewrite l++[]≡l (R t) = refl
     
Rsafety-vec (all-vec∷ a av) (_T∷_ {ts = ts} ht htv) (E[ ev ] vs)
    = lemma↭3 (Rv ts) (RI ev) (RU ev) (Rsafety a ht ev)
Rsafety-vec (all-vec∷ a av) (ht T∷ htv) (_E∷_ {ts = ts} {ts' = ts'} t evs) =
    begin
    RIv evs L.++ (R t L.++ Rv ts)   ↭⟨ ++⁺ˡ (RIv evs) (++-comm (R t) (Rv ts)) ⟩
    RIv evs L.++ (Rv ts L.++ R t)   ↭⟨ ↭-sym (++-assoc (RIv evs) (Rv ts) (R t)) ⟩
    (RIv evs L.++ Rv ts) L.++ R t   ↭⟨ ++⁺ʳ (R t) (Rsafety-vec av htv evs) ⟩
    (RUv evs L.++ Rv ts') L.++ R t  ↭⟨ ++-assoc (RUv evs) (Rv ts') (R t) ⟩
    RUv evs L.++ (Rv ts' L.++ R t)  ↭⟨ ++⁺ˡ (RUv evs) (++-comm (Rv ts') (R t)) ⟩
    RUv evs L.++ (R t L.++ Rv ts')  ∎
