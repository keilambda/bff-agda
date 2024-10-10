{-# OPTIONS --guardedness #-}

module BFFAgda where

open import Agda.Builtin.Nat using (Nat; suc) renaming (zero to z)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_)
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

zero : {n : Nat} → Vec Bit n
zero {z}     = []
zero {suc m} = O ∷ zero

record Stream (A : Set) : Set where
  coinductive
  constructor cons
  field
    head : A
    tail : Stream A

open Stream

zeros : Stream Byte
zeros .head = zero
zeros .tail = zeros

record State : Set where
  constructor _,_,_,_,_
  field
    left : Stream Byte
    curr : Byte
    right : Stream Byte
    stdin : Stream Byte
    stdout : List Byte

open State

init : Stream Byte → State
init stdin = zeros , zero , zeros , stdin , []

stepLeft : State → State
stepLeft (l , c , r , i , o) = tail l , head l , cons c r , i , o

stepRight : State → State
stepRight (l , c , r , i , o) = cons c (tail l) , head r , tail r , i , o

output : State → State
output (l , c , r , i , o) = l , c , r , i , (c ∷ o)

input : State → State
input (l , c , r , i , o) = l , head i , r , tail i , o

increment : State → State
increment (l , c , r , i , o) = l , (inc c) , r , i , o

decrement : State → State
decrement (l , c , r , i , o) = l , (dec c) , r , i , o
