import Data.Nat
import project.Syntax as Syntax
import project.Typing as Typing

module project.Properties.Progress
    (Nm Ns Nf Nsf Nfa : Data.Nat.ℕ)
    (P : Syntax.Program Nm Ns Nf Nsf Nfa)
    where

open import project.Properties.Include Nm Ns Nf Nsf Nfa P

progress :
    {M : Fin Nm}
    {t : Term} {T : Type}
    → HasType M [] t T []
    → (Value t) ⊎ (P.∃ λ t' → M ∋ t ⇒ t')

progress-vec :
    {M : Fin Nm}
    {n : ℕ} {ts : Vec Term n} {Ts : Vec Type n}
    → HasTypeV M [] ts Ts []
    → (ValueV ts) ⊎ (P.∃ λ ts' → M ∋ ts ⇒v ts')

progress Tnum = inj₁ Vnum
progress (Tlet {Γ1 = []} {t1 = t1} {Γ2 = []} {t2 = t2} ht hti)
    with progress ht
... | inj₁ v         = inj₂ (beta-red (t1 V.∷ V.[]) t2 , Elet2 v)
... | inj₂ (t' , ev) = inj₂ (Let t' In t2              , Elet ev)
progress {M = M} (Tpack {s = s} {ts = ts} htv)
    with progress-vec htv
-- I can chose whatever k0 I want here. There is no constraint on the identifier 'k'
--   assigned to a new packed value.
... | inj₁ vs         = inj₂ (struct k0 (sId M s) ts    , Epacked k0 vs)
... | inj₂ (ts' , ev) = inj₂ (pack (sId M s) ts'        , Epack ev)
progress (Tstruct vs htv) = inj₁ (Vstruct vs)
progress (Tcall {M2 = M2} {f = f} {ts = ts} htv)
    with progress-vec htv
... | inj₁ vs          = inj₂ (exec M2 (beta-red ts (toRun (gBody M2 f))) , Ecalled vs)
... | inj₂ (ts' , ev)  = inj₂ (call (fId M2 f) ts'                       , Ecall ev)
progress (Tunpack {Γ1 = []} {Γ2 = []} {t2 = t2} ht hti)
    with progress ht
progress (Tunpack {Γ1 = .[]} {Γ2 = .[]} {t2 = t2} (Tstruct _ htv) hti)
    | inj₁ (Vstruct {ts = ts} vs) = inj₂ (beta-red ts t2 , Eunpacked vs)
progress (Tunpack {Γ1 = []} {Γ2 = []} {t2 = t2} ht hti)
    | inj₂ (t' , ev)              = inj₂ (unpack t' In t2 , Eunpack ev)
progress (Texec {t = t} {M2 = M2} ht) with progress ht
... | inj₁ v         = inj₂ (t           , Eexecuted v)
... | inj₂ (t' , ev) = inj₂ (exec M2 t'  , Eexec ev)
progress (Tif {Γ1 = []} {Γ2 = []} {t2 = t2} {t3 = t3} ht1 ht2 ht3) with progress ht1
progress (Tif {Γ1 = []} {t1 = t1} {Γ2 = []} {t2 = t2} {t3 = t3} ht1 ht2 ht3) | inj₁ (Vnum {0})
    = inj₂ (t3 , Eiffalse)
progress (Tif {Γ1 = []} {t1 = t1} {Γ2 = []} {t2 = t2} {t3 = t3} ht1 ht2 ht3) | inj₁ (Vnum {suc n})
    = inj₂ (t2 , Eiftrue ¬sx≡z)
progress (Tif {Γ1 = []} {Γ2 = []} {t2 = t2} {t3 = t3} ht1 ht2 ht3) | inj₂ (t' , ev)
    = inj₂ (if t' then t2 else t3  , Eif ev)
progress (TselV {j = j} (Vstruct {n = .Nsf} {ts = ts} vs) (Tstruct _ htv) nLin)
    = inj₂ (V.lookup ts j , Eselect vs)
progress (Tpub ht yLin) with progress ht
progress (Tpub Tnum ()) | inj₁ Vnum
progress (Tpub ht yLin) | inj₁ v          = inj₂ (num 0  , Epub2 v)
progress (Tpub ht yLin) | inj₂ (t' , ev)  = inj₂ (pub t' , Epub ev)


progress-vec T[] = inj₁ V[] 
progress-vec (_T∷_ {Γ1 = []} {t = t} {Γ2 = []} {Γ3 = []} {ts = ts} ht htv)
    with progress-vec htv | progress ht
... | inj₂ (ts' , ev) | _ = inj₂ (t V.∷ ts' , t E∷ ev)
... | inj₁ vs         | inj₂ (t' , ev) = inj₂ (t' V.∷ ts , (E[ ev ] vs))
... | inj₁ vs         | inj₁ v         = inj₁ (v V∷ vs)
