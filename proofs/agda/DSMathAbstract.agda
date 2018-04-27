module DSMathAbstract where

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Data.Nat as ℕ using (ℕ)
open import Data.Nat.DivMod using (_div_)
open import Data.Integer.Base as ℤ using (ℤ; ∣_∣) renaming (_⊖_ to _ℕ-_)


module Ray where

  pow≢0 : (a : ℕ) → (b : ℕ) → (a ℕ.^ b ≢ ℕ.zero)
  pow≢0 a ℕ.zero = {!!}
  pow≢0 a (ℕ.suc b) = {!!}

  -- shifting in base 10, truncates instead of rounding (TODO: round instead, like the real rmul)
  _10<<_ : ℕ → ℕ → ℕ
  a 10<< places = _div_ a (10 ℕ.^ places) {{! ? pow≢0 a places!}}

  record Ray (N places : ℕ) : Set where
    constructor Ray_⟨_⟩
    field
      n : ℕ
      <N : (n ℕ.< N)

  Ray-to-ℕ : {N places : ℕ} → (Ray N places) → ℕ
  Ray-to-ℕ Ray n ⟨ _ ⟩ = n

  Ray-one : {N places : ℕ} → ((10 ℕ.^ places) ℕ.< N) → (Ray N places)
  Ray-one {N} {places} 10^places<N = Ray (10 ℕ.^ places) ⟨ 10^places<N ⟩ 

  Ray-delta : {N places : ℕ} → (N ℕ.> 1) → (Ray N places)
  Ray-delta N>1 = Ray 1 ⟨ N>1 ⟩

  _+_⟨_⟩ : {N places : ℕ} → {t : ¬(N ≡ 0)} →  (a : Ray N places) → (b : Ray N places) → ((Ray-to-ℕ a) ℕ.+ (Ray-to-ℕ b) ℕ.< N) → (Ray N places)
  (Ray a ⟨ asafe ⟩) + (Ray b ⟨ bsafe ⟩) ⟨ safe ⟩ = Ray (a ℕ.+ b) ⟨ safe ⟩ 

  _*_⟨_⟩ : {N places : ℕ} → {t : ¬(N ≡ 0)} → (x : Ray N places) → (y : Ray N places) → ((Ray-to-ℕ x) ℕ.* (Ray-to-ℕ y) ℕ.< N) → (Ray N places)
  -- needed to abandon mixfix for definition? :(
  _*_⟨_⟩ {N} {places} {t} (Ray a ⟨ asafe ⟩)  (Ray b ⟨ bsafe ⟩) absafe = Ray ((a ℕ.* b) 10<< places ) ⟨ {!!} ⟩ 

  naive-rpow : {N places : ℕ} → {t : ¬(N ≡ 0)} → {s : 10 ℕ.^ places ℕ.< N} → (Ray N places) → ℕ → (Ray N places)
  naive-rpow {N} {places} {t} {s} x ℕ.zero = Ray-one {N} {places} s
  naive-rpow {N} {places} {t} {s} x (ℕ.suc n) = _*_⟨_⟩ {N} {places} {t} x (naive-rpow {N} {places} {t} {s} x n) {!!}

  -- statement about precision of naive-rpow
  -- cases (1) x <= 1 and (2) x > 1
  -- there is stronger bound at O(n-1) rather than O(n) (and O(x^(n-1)) rather than O(x^n)), but we use n for simplicity
  naive-rpow-correct-case1 : {N places : ℕ} → {t : N ℕ.> 1} → {s : 10 ℕ.^ places ℕ.< N} → (x : Ray N places) → (n : ℕ) → ((Ray-to-ℕ x) ℕ.≤ 1) → ∣ (Ray-to-ℕ (naive-rpow {N} {places} {{!!}} {s} x n)) ℕ- ((Ray-to-ℕ x) ℕ.^ n) ∣ ℕ.< ((Ray-to-ℕ (Ray-delta t)) ℕ.* n)
  naive-rpow-correct-case1 = {!!}

  naive-rpow-correct-case2 : {N places : ℕ} → {t : N ℕ.> 1} → {s : 10 ℕ.^ places ℕ.< N} → (x : Ray N places) → (n : ℕ) → ((Ray-to-ℕ x) ℕ.< 1) → ∣ (Ray-to-ℕ (naive-rpow {N} {places} {{!!}} {s} x n)) ℕ- ((Ray-to-ℕ x) ℕ.^ n) ∣ ℕ.< ((Ray-to-ℕ (Ray-delta t)) ℕ.* n ℕ.* ((Ray-to-ℕ x) ℕ.^ n))
  naive-rpow-correct-case2 = {!!}

  rpow : {N places : ℕ} → {t : ¬(N ≡ 0)} → {s : 10 ℕ.^ places ℕ.< N} → (Ray N places) → ℕ → (Ray N places)
  rpow {N} {places} {t} {s} x ℕ.zero = Ray-one {N} {places} s
  rpow {N} {places} {t} {s} x (ℕ.suc n) = {!!}
