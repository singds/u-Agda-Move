
open import Data.Nat using (ℕ)
import project.Syntax as Syntax
import project.Typing as Typing

module project.Properties.Include
    {Nm Ns Nf Nsf Nfa : ℕ}
    (P : Syntax.Program Nm Ns Nf Nsf Nfa)
    where

open import Data.Nat using (ℕ; suc; _<_; _≤_; _<?_; _≤?_; _≥_; _≟_; s≤s; z≤n; _+_) public
open import Agda.Builtin.Equality public
open import Agda.Builtin.Nat public using (_-_)
open import Agda.Primitive public using (Level)
open import Agda.Builtin.Sigma public using (_,_)
open import Data.Empty public using (⊥)

open import Relation.Binary.PropositionalEquality public using (cong; cong₂)
open import Data.Vec public using (Vec; []; _∷_)
open import Data.Fin public using (Fin; toℕ)
open import Data.Bool public using (Bool; true; false)
open import Data.List public using (List)
open import Relation.Nullary public using (Dec; yes; no; ¬_; ofⁿ)
open import Function using (case_of_; _∘_) public
open import Data.Product public using (_×_; ∃)
open import Data.Sum public using (_⊎_; inj₁; inj₂)

import Data.Vec.Properties


open import project.TrivialFacts public
open Syntax                    Nm Ns Nf Nsf Nfa public
open Typing                    Nm Ns Nf Nsf Nfa P public
open import project.Utility    Nm Ns Nf Nsf Nfa P public
open import project.Evaluation Nm Ns Nf Nsf Nfa P public
open import project.Resources  Nm Ns Nf Nsf Nfa P public

module Nat = Data.Nat
module F = Data.Fin
module V = Data.Vec
module L = Data.List
module RN = Relation.Nullary
module Eq = Relation.Binary.PropositionalEquality
module VP = Data.Vec.Properties
module P = Data.Product
