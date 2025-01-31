module Bounded

import Data.Vect

-- Various operations on bounded natural numbers
--  * vector lookup
--  * increase/decrease bounds
--  * checked addition/increment

%default total

-- | Bounded natural numbers
public export
data Bounded : Nat -> Type where
     Bound : (k : Nat) -> Bounded (plus (S k) n)

export
implementation Show (Bounded n) where
     show = show' where
        show' : Bounded n' -> String
        show' (Bound k) = show k

export
mkBounded : (k : Nat) -> Bounded (plus k (S n))
mkBounded {n} k ?= Bound {n} k

export
lookup : Bounded n -> Vect n a -> a
lookup (Bound Z)     (x :: xs) = x
lookup (Bound (S k)) (x :: xs) = lookup (Bound k) xs

export
update : Bounded n -> a -> Vect n a -> Vect n a
update (Bound Z)     val (x :: xs) = val :: xs
update (Bound (S k)) val (x :: xs) = x :: update (Bound k) val xs

weaken : Bounded n -> Bounded (S n)
weaken (Bound {n} k) ?= Bound {n = S n} k

weakenP : Bounded n -> Bounded (n + m)
weakenP {m} (Bound {n} k) ?= Bound {n = n + m} k

strengthen : Bounded (S n) -> Either (Bounded (S n)) (Bounded n)
strengthen (Bound {n = Z} x) = Left (Bound x)
strengthen (Bound {n = S k} x) = ?strengthenZK

inBound : Nat -> (b : Nat) -> Maybe (Bounded b)
inBound x b with (cmp x b)
  inBound x (x + S y) | CmpLT y = rewrite sym (plusSuccRightSucc x y) in
                                  Just (Bound x)
  inBound x x         | CmpEQ   = Nothing
  inBound (y + S k) y | CmpGT k = Nothing

(+) : Bounded n -> Bounded n -> Maybe (Bounded n)
(+) a b = plusB a b Refl where
  plusB : Bounded x -> Bounded y -> (x = y) -> Maybe (Bounded x)
  plusB (Bound a) (Bound b) p = inBound (a + b) _

export
inc : Bounded n -> Bounded (S n)
inc (Bound x) = Bound (S x)

safeinc : Bounded n -> Either (Bounded (S n)) (Bounded n)
safeinc (Bound {n = Z} x) = Left (Bound (S x))
safeinc (Bound {n = S k} x) = rewrite sym (plusSuccRightSucc x k) in
                              Right (Bound (S x))

---------- Proofs ----------

Bounded.weakenP_lemma_1 = proof {
  compute;
  intros;
  rewrite plusAssociative k n m;
  trivial;
}

Bounded.weaken_lemma_1 = proof {
  intros;
  rewrite sym (plusSuccRightSucc k n);
  trivial;
}

Bounded.mkBounded_lemma_1 = proof {
  intros;
  rewrite plusCommutative (S n) k;
  rewrite plusCommutative k n;
  trivial;
}

Bounded.strengthenZK = proof {
  intros;
  refine Right;
  rewrite plusCommutative (S k) x;
  rewrite plusCommutative x k;
  refine Bound;
  exact x;
  exact k;
}
