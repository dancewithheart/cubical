module Cubical.HITs.FreeSemilattice.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws hiding (assoc)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.HITs.FreeSemilattice.Base as FSL

private variable
  ℓ : Level
  A : Type ℓ

open FSL

absorb-middle : (x y : FreeSemilattice A) → x ⊔ (x ⊔ y) ≡ x ⊔ y
absorb-middle x y =
  x ⊔ (x ⊔ y)
    ≡⟨ assoc x x y ⟩
  (x ⊔ x) ⊔ y
    ≡⟨ cong (_⊔ y) (idem x) ⟩
  x ⊔ y ∎

absorb-middle-sym : (x y : FreeSemilattice A) → x ⊔ (y ⊔ x) ≡ x ⊔ y
absorb-middle-sym x y =
  x ⊔ (y ⊔ x)
    ≡⟨ cong (x ⊔_) (comm y x) ⟩
  x ⊔ (x ⊔ y)
    ≡⟨ absorb-middle x y ⟩
  x ⊔ y ∎

absorb-left : (x y : FreeSemilattice A) → (x ⊔ y) ⊔ x ≡ x ⊔ y
absorb-left x y =
  (x ⊔ y) ⊔ x
    ≡⟨ comm (x ⊔ y) x ⟩
  x ⊔ (x ⊔ y)
    ≡⟨ absorb-middle x y ⟩
  x ⊔ y ∎

ε-idem : ε {A = A} ⊔ ε ≡ ε
ε-idem = identityᵣ ε

swap-middle : (x y z : FreeSemilattice A) → x ⊔ (y ⊔ z) ≡ y ⊔ (x ⊔ z)
swap-middle x y z =
  x ⊔ (y ⊔ z)
    ≡⟨ assoc x y z ⟩
  (x ⊔ y) ⊔ z
    ≡⟨ cong (_⊔ z) (comm x y) ⟩
  (y ⊔ x) ⊔ z
    ≡⟨ sym (assoc y x z) ⟩
  y ⊔ (x ⊔ z) ∎
