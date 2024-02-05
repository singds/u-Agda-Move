import Data.Nat
import project.Syntax as Syntax

module project.Resources.RifShiftBack
    (Nm Ns Nf Nsf Nfa : Data.Nat.ℕ)
    (P : Syntax.Program Nm Ns Nf Nsf Nfa)
    where

open import project.Properties.Include Nm Ns Nf Nsf Nfa P

open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
open PermutationReasoning

private
    variable
        n   : ℕ
        t   : Term
        ts : Vec Term n

RifShiftBack     :
      All tIsIf⇒Rt2↭Rt3 t
    → (c : ℕ)
    → All tIsIf⇒Rt2↭Rt3 (shift-back c t)
RifShiftBack-vec :
      AllV tIsIf⇒Rt2↭Rt3 ts
    → (c : ℕ)
    → AllV tIsIf⇒Rt2↭Rt3 (shift-back-vec c ts)

RifShiftBack {num n} a c = all-num (λ ())
RifShiftBack {var x} a c with x <? c
... | yes _ = all-var (λ ())
... | no  _ = all-var (λ ())
RifShiftBack {Let t1 In t2} (all-let _ a1 a2) c
    = all-let (λ ()) (RifShiftBack a1 c) (RifShiftBack a2 (c + 1))
RifShiftBack {call fid ts} (all-call _ a) c
    = all-call (λ ()) (RifShiftBack-vec a c)
RifShiftBack {if t1 then t2 else t3} (all-if p a1 a2 a3) c
    = all-if r (RifShiftBack a1 c) (RifShiftBack a2 c) (RifShiftBack a3 c)
    where
        r : {t4 t5 t6 : Term}
            → (if shift-back c t1 then shift-back c t2 else shift-back c t3) ≡ (if t4 then t5 else t6)
            → R t5 ↭ R t6
        r {t4} {t5} {t6} refl = begin
            R (shift-back c t2) ↭⟨ ↭-reflexive (shift-back-presR c t2) ⟩
            R t2                ↭⟨ p refl ⟩
            R t3                ↭⟨ ↭-sym (↭-reflexive (shift-back-presR c t3)) ⟩
            R (shift-back c t3) ∎
RifShiftBack {pack sid ts} (all-pack _ a) c
    = all-pack (λ ()) (RifShiftBack-vec a c)
RifShiftBack {unpack t1 In t2} (all-unpack _ a1 a2) c
    = all-unpack (λ ()) (RifShiftBack a1 c) (RifShiftBack a2 (c + Nsf))
RifShiftBack {t · j} (all-· _ a) c
    = all-· (λ ()) (RifShiftBack a c)
RifShiftBack {pub t} (all-pub _ a) c
    = all-pub (λ ()) (RifShiftBack a c)
RifShiftBack {struct k sid ts} (all-struct _ a) c
    = all-struct (λ ()) (RifShiftBack-vec a c)
RifShiftBack {exec M2 t} (all-exec _ a) c = all-exec (λ ()) a

RifShiftBack-vec {ts = V.[]} a c = all-vec[]
RifShiftBack-vec {ts = t V.∷ ts} (all-vec∷ a1 a2) c
    = all-vec∷ (RifShiftBack a1 c) (RifShiftBack-vec a2 c)
