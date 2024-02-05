import Data.Nat
import project.Syntax as Syntax

module project.Resources.RifLterm
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

RifLterm     : (t : LTerm)        → All  tIsIf⇒Rt2↭Rt3 (toRun t)
RifLterm-vec : (ts : Vec LTerm n) → AllV tIsIf⇒Rt2↭Rt3 (toRun-vec ts)

RifLterm (num n) = all-num (λ ())
RifLterm (var x) = all-var (λ ())
RifLterm (Let t1 In t2) = all-let (λ ()) (RifLterm t1) (RifLterm t2)
RifLterm (call fid ts) = all-call (λ ()) (RifLterm-vec ts)
RifLterm (if t1 then t2 else t3)
    = all-if p (RifLterm t1) (RifLterm t2) (RifLterm t3)
    where
        p : {t4 t5 t6 : Term} →
            (if toRun t1 then toRun t2 else toRun t3) ≡ (if t4 then t5 else t6) →
            R t5 ↭ R t6
        p {t4} {t5} {t6} refl = begin
            R t5 ↭⟨ ↭-reflexive (Rlterm≡[] t2) ⟩
            L.[] ↭⟨ ↭-sym (↭-reflexive (Rlterm≡[] t3)) ⟩
            R t6 ∎

RifLterm (pack sid ts) = all-pack (λ ()) (RifLterm-vec ts)
RifLterm (unpack t1 In t2) = all-unpack (λ ()) (RifLterm t1) (RifLterm t2)
RifLterm (x · j) = all-· (λ ()) (RifLterm (var x))
RifLterm (pub t) = all-pub (λ ()) (RifLterm t)

RifLterm-vec V.[] = all-vec[]
RifLterm-vec (t V.∷ ts) = all-vec∷ (RifLterm t) (RifLterm-vec ts)
