
module project.IncludeBase where

open import Data.Nat public using (ℕ; suc; _<_; _<?_; _≤_; _≤?_; _>_; _>?_; _≥_; _≟_; s≤s; z≤n; _+_)

open import Agda.Builtin.Equality public
open import Agda.Builtin.Nat public using (_-_)
open import Agda.Primitive public using (Level)
open import Agda.Builtin.Sigma public using (_,_)
open import Data.Empty public using (⊥)

open import Relation.Binary.PropositionalEquality public using (cong)
open import Data.Vec public using (Vec)
open import Data.Fin public using (Fin; toℕ; #_)
open import Data.Bool public using (Bool; true; false)
open import Data.List public using (List)
open import Relation.Nullary public using (Dec; yes; no; ¬_; ofⁿ)
open import Function using (case_of_; _∘_) public
open import Data.Product public using (_×_; ∃)
open import Data.Sum public using (_⊎_; inj₁; inj₂)
open import Relation.Unary public using (Pred)

import Data.Vec.Properties
import Data.Bool.Properties

module Nat = Data.Nat
module F = Data.Fin
module V = Data.Vec
module L = Data.List
module RN = Relation.Nullary
module Eq = Relation.Binary.PropositionalEquality
module VP = Data.Vec.Properties
module BP = Data.Bool.Properties
module P = Data.Product
