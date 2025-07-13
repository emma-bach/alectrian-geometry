```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; step-≡-∣; _∎)

open import Data.Product
open import Relation.Nullary using (¬_)
```

```agda
data Point : Set where
  x : Point
  y : Point
  z : Point
```

```agda
-- Congruence:
-- C w x y z if the length of the line segments w x and y z are equal
data C : Point → Point → Point → Point → Set where
  C-refl : ∀(a b : Point) → C a b b a
  C-trans : ∀(a b c d e f : Point) → C a b c d → C c d e f → C a b e f
  C-sym : ∀(a b c d : Point) → C a b c d → C c d a b

postulate C-id : ∀(a b c : Point) → C a b c c → a ≡ b

C-order-irrel-l : ∀(a b c d : Point) → C a b c d → C b a c d
C-order-irrel-l a b c d Cabcd = C-trans b a a b c d (C-refl b a) Cabcd

C-order-irrel-r : ∀(a b c d : Point) → C a b c d → C a b d c
C-order-irrel-r a b c d Cabcd = C-trans a b c d d c Cabcd (C-refl c d)

C-order-irrel-b : ∀(a b c d : Point) → C a b c d → C b a d c
C-order-irrel-b a b c d Cabcd = C-order-irrel-l a b d c (C-order-irrel-r a b c d Cabcd)
```

```agda
-- Betweenness:
-- B x y z if y is between x and z
data B : Point → Point → Point → Set where

postulate B-id : ∀(a b : Point) → B a b a → a ≡ b
postulate B-Pasch : ∀(a b c d e : Point) → B a b e → B c d e → ∃[ p ] (B b p d × B d p a)
postulate B-schema : ∀(φ ψ : Point → Set) → ∃[ p ] (∀(x y : Point) → ((φ x × ψ y) → B p x y)) → ∃[ q ] (∀(x y : Point) → B x q y)

postulate B-lower-dimension : ∃[ a ] ∃[ b ] ∃[ c ] (¬(B a b c) × ¬(B b c a) × ¬(B c a b))
```
