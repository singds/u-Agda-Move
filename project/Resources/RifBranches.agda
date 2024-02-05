import Data.Nat
import project.Syntax as Syntax
import project.Typing as Typing

module project.Resources.RifBranches
    (Nm Ns Nf Nsf Nfa : Data.Nat.ℕ)
    (P : Syntax.Program Nm Ns Nf Nsf Nfa)
    (W : Typing.WellProg Nm Ns Nf Nsf Nfa P)
    where

open import project.Properties.Include Nm Ns Nf Nsf Nfa P
open import project.Properties.Substitution Nm Ns Nf Nsf Nfa P
open import project.Resources.RifLterm Nm Ns Nf Nsf Nfa P
open import project.Resources.RifSubst Nm Ns Nf Nsf Nfa P W
open import project.Resources.RifShiftBack Nm Ns Nf Nsf Nfa P

open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
open PermutationReasoning

private
    variable
        n l lv  : ℕ
        Δ       : Env l
        Δv      : Env lv
        M M2    : Fin Nm
        t t' t2 : Term
        T       : Type



RifBeta :
    {Γ1 Γ2 : UEnv Δ}
    {Γv1 Γv2 : UEnv Δv}
    {ts : Vec Term n} {Ts : Vec Type n}
    → HasTypeV M2 Γv1 ts Ts Γv2
    → ValueV ts
    → HasTypeI M Γ1 Ts t2 T Γ2
    → All tIsIf⇒Rt2↭Rt3 t2
    → All tIsIf⇒Rt2↭Rt3 (beta-red ts t2)
RifBeta ht' V[] I[ ht ] a = a
RifBeta {t2 = t2} (_T∷_ {t = t} {ts = ts} ht' htv') (v V∷ vs) (nLin I∷  hti) a = RifShiftBack p3 0
    where
        p2 : All tIsIf⇒Rt2↭Rt3 (beta-red ts t2)
        p2 = RifBeta htv' vs hti a
        
        ht2 = substi-multi htv' vs hti
        
        p3 : All tIsIf⇒Rt2↭Rt3 (subst 0 t (beta-red ts t2))
        p3 = RifSubst v ht' ht2 p2

RifBeta {t2 = t2} (_T∷_ {t = t} {ts = ts} ht' htv') (v V∷ vs) (yLin I∷l hti) a = RifShiftBack p3 0
    where
        p2 : All tIsIf⇒Rt2↭Rt3 (beta-red ts t2)
        p2 = RifBeta htv' vs hti a
        
        ht2 = substi-multi htv' vs hti
        
        p3 : All tIsIf⇒Rt2↭Rt3 (subst 0 t (beta-red ts t2))
        p3 = RifSubst v ht' ht2 p2



RifEval :
    {Γ1 Γ2 : UEnv Δ}
    → HasType M Γ1 t T Γ2
    → M ∋ t ⇒ t'
    → All tIsIf⇒Rt2↭Rt3 t
    → All tIsIf⇒Rt2↭Rt3 t'
RifEval-vec :
    {Δ : Env l}
    {Γ1 Γ2 : UEnv Δ}
    {ts ts' : Vec Term n} {Ts : Vec Type n}
    → HasTypeV M Γ1 ts Ts Γ2
    → M ∋ ts ⇒v ts'
    → AllV tIsIf⇒Rt2↭Rt3 ts
    → AllV tIsIf⇒Rt2↭Rt3 ts'

RifEval (Tlet ht hti) (Elet ev) (all-let _ a1 a2)
    = all-let (λ ()) (RifEval ht ev a1) a2
RifEval (Tlet ht hti) (Elet2 v) (all-let _ a1 a2)
    = RifBeta (ht T∷ T[]) (v V∷ V[]) hti a2
RifEval (Tpack htv) (Epack ev) (all-pack _ a)
    = all-pack (λ ()) (RifEval-vec htv ev a)
RifEval ht (Epacked k x) (all-pack _ a) = all-struct (λ ()) a
RifEval (Tunpack ht hti) (Eunpack ev) (all-unpack _ a1 a2) = all-unpack (λ ()) (RifEval ht ev a1) a2
RifEval (Tunpack (Tstruct _ htv) hti) (Eunpacked vs) (all-unpack _ a1 a2)
    = RifBeta htv vs hti a2
RifEval (Tcall htv) (Ecall ev) (all-call _ a)
    = all-call (λ ()) (RifEval-vec htv ev a)
RifEval (Tcall {M2 = M2} {f = f} htv) (Ecalled vs) _
    = all-exec (λ ()) (RifBeta htv vs (WellFun.hti ((WellMod.wf (W M2)) f)) (RifLterm (body M2 f)))
RifEval (Texec ht) (Eexec ev) (all-exec _ a) = all-exec (λ ()) (RifEval ht ev a)
RifEval ht (Eexecuted v) (all-exec _ a) = a
RifEval (Tif ht1 ht2 ht3) (Eif ev) (all-if p a1 a2 a3) = all-if (λ { refl → p refl }) (RifEval ht1 ev a1) a2 a3
RifEval ht (Eiftrue nz) (all-if _ a1 a2 a3) = a2
RifEval ht Eiffalse (all-if _ a1 a2 a3) = a3
RifEval ht (Eselect {j = j} vs) (all-· _ (all-struct _ as)) = allLookup j as
RifEval (Tpub ht _) (Epub ev) (all-pub _ a) = all-pub (λ ()) (RifEval ht ev a)
RifEval ht (Epub2 v) a = all-num (λ ())

RifEval-vec (ht T∷ htv) (E[ ev ] vs) (all-vec∷ a as) = all-vec∷ (RifEval ht ev a) as
RifEval-vec (ht T∷ htv) (t E∷ evs)   (all-vec∷ a as) = all-vec∷ a (RifEval-vec htv evs as)
