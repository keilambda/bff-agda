{-# OPTIONS --guardedness #-}

module BFFAgda where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Vec using (Vec; []; _∷_)

data Bit : Set where
  O : Bit
  I : Bit

Byte : Set
Byte = Vec Bit 8

inc : {n : Nat} → Vec Bit n → Vec Bit n
inc [] = []
inc (O ∷ xs) = I ∷ xs
inc (I ∷ xs) = O ∷ inc xs

dec : {n : Nat} → Vec Bit n → Vec Bit n
dec [] = []
dec (O ∷ xs) = I ∷ dec xs
dec (I ∷ xs) = O ∷ xs

zero? : {n : Nat} → Vec Bit n → Bool
zero? [] = true
zero? (O ∷ xs) = zero? xs
zero? (I ∷ xs) = false

init : {n : Nat} → Vec Bit n
init {zero}  = []
init {suc m} = O ∷ init
