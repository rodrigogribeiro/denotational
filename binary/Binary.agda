open import Data.Nat
open import Data.Nat.Properties
open import Data.Product

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

module Binary where

-- binary numbers

data Bit : Set where
  #0 #1 : Bit

data Bin : ℕ → Set where
  ε   : ∀ {n} → Bin n
  _∙_ : ∀ {n} → Bin n → Bit → Bin (1 + n)

infixl 6 _∙_

-- bounded natural numbers

data ℕω[_] (n : ℕ) : Set where
  Mk : ∀ {m} → m < 2 ^ n → ℕω[ n ]
  ω  : ℕω[ n ]

-- simple expressions

data Exp (n : ℕ) : Set where
  Const : Bin n → Exp n
  _⊕_   : Exp n → Exp n → Exp n
  _⊗_   : Exp n → Exp n → Exp n


-- several auxiliar lemmas

≤-n-twice : ∀ {n} → n ≤ n + n
≤-n-twice {zero} = z≤n
≤-n-twice {suc n} with ≤-n-twice {n}
...| p rewrite +-comm n (suc n)
  = s≤s (≤-trans p (n≤1+n (n + n)))

exp-one : ∀ {n} → 1 ≤ 2 ^ n
exp-one {zero} = s≤s z≤n
exp-one {suc n} with exp-one {n}
...| p rewrite +-identityʳ (2 ^ n)
  = ≤-trans p (≤-n-twice {2 ^ n})

exp-zero-l : ∀ n → 0 < 2 ^ n
exp-zero-l zero = s≤s z≤n
exp-zero-l (suc n) with exp-zero-l n
...| p rewrite +-identityʳ (2 ^ n)
  = ≤-trans p (≤-n-twice {2 ^ n})

≤-double : ∀ {n m} → n ≤ m → n + n ≤ m + m
≤-double z≤n = z≤n
≤-double (s≤s {n}{m} p) rewrite +-identityʳ n
                              | +-identityʳ m
                              | +-suc n n
                              | +-suc m m
  = s≤s (s≤s (≤-double p))

+-lemma : ∀ n m p → n + m ≤ n + (m + p)
+-lemma zero zero p = z≤n
+-lemma zero (suc m) p = s≤s (+-lemma zero m p)
+-lemma (suc n) zero p = s≤s (+-lemma n zero p)
+-lemma (suc n) (suc m) zero = s≤s (+-lemma n (suc m) zero)
+-lemma (suc n) (suc m) (suc p) = s≤s (+-lemma n (suc m) (suc p))

-- semantics of binary numbers

N : ∀ {n} → Bin n → ℕω[ n ]
N {n} ε = Mk (exp-zero-l n)
N {suc n} (d ∙ b) with N d
... | ω = ω
... | Mk {m} p
   = Mk {suc n}{suc (m + m)} lemma
  where
  open ≤-Reasoning
  oblig1 : ∀ m → suc (suc (m + m)) ≤ (suc m) + (suc m)
  oblig1 zero = s≤s (s≤s z≤n)
  oblig1 (suc m) with oblig1 m
  ... | s≤s p rewrite +-comm m (suc m)
      | +-comm m (suc (suc m))
        = s≤s (s≤s (s≤s p))

  lemma : suc (suc (m + m)) ≤ (2 ^ n) + ((2 ^ n) + 0)
  lemma
    = begin
         suc (suc (m + m))       ≤⟨ oblig1 m ⟩
         (suc m) + (suc m)       ≤⟨ ≤-double p ⟩
         (2 ^ n) + (2 ^ n)       ≤⟨ +-lemma (2 ^ n) (2 ^ n) 0 ⟩
         (2 ^ n) + ((2 ^ n) + 0)
      ∎

-- lifting the addition and product.

_+n_ : ∀ {n} → ℕω[ n ] → ℕω[ n ] → ℕω[ n ]
_+n_ {n} (Mk {m} p)(Mk {m'} q) with (m + m') <? (2 ^ n)
... | yes pq = Mk pq
... | no  pq = ω
Mk _ +n ω = ω
ω +n m = ω

_*n_ : ∀ {n} → ℕω[ n ] → ℕω[ n ] → ℕω[ n ]
_*n_ {n} (Mk {m} p) (Mk {m'} q) with (m * m') <? (2 ^ n)
... | yes pq = Mk pq
... | no  pq = ω
Mk x *n ω = ω
ω *n m = ω

-- semantics of expressions

E[_] : ∀ {n} → Exp n → ℕω[ n ]
E[ Const b ] = N b
E[ e ⊕ e' ] = E[ e ] +n E[ e' ]
E[ e ⊗ e' ] = E[ e ] *n E[ e' ]
