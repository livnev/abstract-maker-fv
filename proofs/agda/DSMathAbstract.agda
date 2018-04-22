module DSMathAbstract where

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Data.Nat as ℕ using (ℕ)
open import Data.Nat.DivMod using (_div_)

module Modulo where
  

module Ray where

  _<<<10_ : ℕ → ℕ → ℕ
  a <<<10 places = a div (10 ℕ.^ places)

  record ∞Ray (places : ℕ) : 

  record Ray (N places : ℕ) : Set where
    constructor Ray_⟨_⟩
    field
      n : ℕ
      <N : (n ℕ.< N)

  Ray-to-ℕ : {N places : ℕ} → (Ray N places) → ℕ
  Ray-to-ℕ Ray n ⟨ _ ⟩ = n

  Ray-one : {N places : ℕ} → ((10 ℕ.^ places) ℕ.< N) → (Ray N places)
  Ray-one N places 10^places<N = Ray (10 ℕ.^ places) ⟨ 10^places<N ⟩ 

  Ray-delta : {N places : ℕ} → (N ℕ.> 1) → (Ray N places)
  Ray-delta N>1 = Ray 1 ⟨ sym N>1 ⟩

  _+_ : {N places : ℕ} → ¬(N ≡ 0) → (a : Ray N places) → (b : Ray N places) → ((Ray-to-ℕ a) ℕ.+ (Ray-to-ℕ b) ℕ.< N) → (Ray N places)
  (Ray a ⟨ _ ⟩) + (Ray b ⟨ _ ⟩) safe = Ray ((Ray-to-ℕ a) + (Ray-to-ℕ b)) ⟨ safe ⟩ 

  _*_ : {N places : ℕ} → ¬(N ≡ 0) → (a : Ray N places) → (b : Ray N places) → ((Ray-to-ℕ a) ℕ.* (Ray-to-ℕ b) ℕ.< N) → (Ray N places)
  (Ray a ⟨ _ ⟩) * (Ray b ⟨ _ ⟩) safe = Ray ((Ray-to-ℕ a) * (Ray-to-ℕ b)) <<<10 places ⟨ safe ⟩ 



  naive-rpow : {N places : ℕ} → (Ray N places) → ℕ → (Ray N places)
  naive-rpow x ⟨ _ ⟩ ℕ.zero = Ray-one N places
  naive-rpow x ⟨ _ ⟩ (ℕ.suc n) = x * (naive-rpow x n)

  -- statement about precision of naive-rpow
  -- naive-rpow-correct : {N places : ℕ} → (x : Ray N places) → (n : ℕ) → | (Ray-to-ℕ (naive-rpow x n)) - ((Ray-to-ℕ x) ^ (Ray-to-ℕ n)) | < Ray-delta * ...
     
