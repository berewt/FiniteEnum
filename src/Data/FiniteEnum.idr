module Data.FiniteEnum

import Control.Isomorphism

import Data.Vect
import Data.Fin

%default total

export
enumerateIso : (prf : Iso a (Fin card)) -> Vect card a
enumerateIso (MkIso to from toFrom fromTo) = map from range

interface FinEnum a (n : Nat) | a where
  finIso : Iso a (Fin n)

enumerate : FinEnum a n => Vect n a
enumerate = enumerateIso finIso

-- FinEnum 1 Unit

public export
unitFin1Iso : Iso () (Fin 1)
unitFin1Iso = MkIso fromUnit toUnit unitFromTo unitToFrom
  where

    fromUnit : () -> Fin 1
    fromUnit = const FZ

    toUnit : Fin 1 -> ()
    toUnit = const ()

    unitFromTo : (y : Fin 1) -> fromUnit (toUnit y) = y
    unitFromTo FZ = Refl
    unitFromTo (FS x) = absurd x

    unitToFrom : (x : ()) -> toUnit (fromUnit x) = x
    unitToFrom () = Refl

FinEnum Unit 1 where
    finIso = unitFin1Iso


-- FinEnum 2 Bool

public export
boolFin2Iso : Iso Bool (Fin 2)
boolFin2Iso = MkIso fromBool toBool boolFromTo boolToFrom
  where

    fromBool : Bool -> Fin 2
    fromBool False = FZ
    fromBool True = FS FZ

    toBool : Fin 2 -> Bool
    toBool FZ = False
    toBool (FS x) = True

    boolFromTo : (y : Fin 2) -> fromBool (toBool y) = y
    boolFromTo FZ = Refl
    boolFromTo (FS FZ) = Refl
    boolFromTo (FS (FS x)) = absurd x

    boolToFrom : (x : Bool) -> toBool (fromBool x) = x
    boolToFrom False = Refl
    boolToFrom True = Refl

FinEnum Bool 2 where
    finIso = boolFin2Iso


-- FinEnum (Either a b)

data SumFin : (n : Nat) -> (m : Nat) -> Fin (n + m) -> Type where
  SumLeft : (x : Fin n) -> SumFin n m (weakenN m x)
  SumRight : (x : Fin m) -> SumFin n m (shift n x)

sumFin : (n : Nat) -> (m : Nat) -> (x : Fin (n + m)) -> SumFin n m x
sumFin Z m x = SumRight x
sumFin (S n) m FZ = SumLeft FZ
sumFin (S n) m (FS x) with (sumFin n m x)
  sumFin (S n) m (FS (weakenN m y)) | (SumLeft y) = SumLeft (FS y)
  sumFin (S n) m (FS (shift n y)) | (SumRight y) = SumRight y

sumFinLeft : (n: Nat) ->
                (m : Nat) ->
                (y : Fin n) ->
                sumFin n m (weakenN m y) = SumLeft y
sumFinLeft Z m y = absurd y
sumFinLeft (S n) m FZ = Refl
sumFinLeft (S n) m (FS x) = rewrite sumFinLeft n m x in Refl

sumFinRight : (n: Nat) ->
                 (m : Nat) ->
                 (y : Fin m) ->
                 sumFin n m (shift n y) = SumRight y
sumFinRight Z m y = Refl
sumFinRight (S n) m y = rewrite (sumFinRight n m y) in Refl

eitherTo : (aTo : a -> Fin n) ->
           (bTo : b -> Fin m) ->
           Either a b -> Fin (n+m)
eitherTo aTo bTo (Left l) {m} = weakenN m (aTo l)
eitherTo aTo bTo (Right r) {n} = shift n (bTo r)

eitherFrom : (aFrom : Fin n -> a) ->
             (bFrom : Fin m -> b) ->
             Fin (n+m) -> Either a b
eitherFrom aFrom bFrom x {n} {m} with (sumFin n m x)
  eitherFrom aFrom bFrom (weakenN m y) | (SumLeft y) = Left (aFrom y)
  eitherFrom aFrom bFrom (shift n y) | (SumRight y) = Right (bFrom y)

eitherFromLeft : (aFrom : Fin n -> a) ->
                 (bFrom : Fin m -> b) ->
                 (x : Fin n) ->
                 eitherFrom aFrom bFrom (weakenN m x) = Left (aFrom x)
eitherFromLeft aFrom bFrom x {n} {m} = rewrite sumFinLeft n m x in Refl

eitherFromRight : (aFrom : Fin n -> a) ->
                 (bFrom : Fin m -> b) ->
                 (x : Fin m) ->
                 eitherFrom aFrom bFrom (shift n x) = Right (bFrom x)
eitherFromRight aFrom bFrom x {n} {m} = rewrite sumFinRight n m x in Refl


eitherToFrom : (aTo : a -> Fin n) ->
               (bTo : b -> Fin m) ->
               (aFrom : Fin n -> a) ->
               (bFrom : Fin m -> b) ->
               (aToFrom : (x : Fin n) -> aTo (aFrom x) = x) ->
               (bToFrom : (x : Fin m) -> bTo (bFrom x) = x) ->
               (y : Fin (n+m)) ->
               eitherTo aTo bTo (eitherFrom aFrom bFrom y) = y
eitherToFrom aTo bTo aFrom bFrom aToFrom bToFrom y {n} {m} with (sumFin n m y)
  eitherToFrom aTo bTo aFrom bFrom aToFrom bToFrom (weakenN m x)
             | (SumLeft x) = cong (aToFrom x)
  eitherToFrom aTo bTo aFrom bFrom aToFrom bToFrom (shift n x)
             | (SumRight x) = cong (bToFrom x)

eitherFromToLeft : (aTo : a -> Fin n) ->
                   (aFrom : Fin n -> a) ->
                   (bFrom : Fin m -> b) ->
                   (aFromTo : (x : a) -> aFrom (aTo x) = x) ->
                   (l : a) ->
                   eitherFrom aFrom bFrom (weakenN m (aTo l)) = Left l
eitherFromToLeft aTo aFrom bFrom aFromTo l
  = rewrite eitherFromLeft aFrom bFrom (aTo l) in cong (aFromTo l)

eitherFromToRight : (bTo : b -> Fin m) ->
                    (aFrom : Fin n -> a) ->
                    (bFrom : Fin m -> b) ->
                    (bFromTo : (x : b) -> bFrom (bTo x) = x) ->
                    (r : b) ->
                    eitherFrom aFrom bFrom (shift n (bTo r)) = Right r
eitherFromToRight bTo aFrom bFrom bFromTo r
  = rewrite eitherFromRight aFrom bFrom (bTo r) in cong (bFromTo r)

eitherFromTo : (aTo : a -> Fin n) ->
               (bTo : b -> Fin m) ->
               (aFrom : Fin n -> a) ->
               (bFrom : Fin m -> b) ->
               (aFromTo : (x : a) -> aFrom (aTo x) = x) ->
               (bFromTo : (x : b) -> bFrom (bTo x) = x) ->
               (y : Either a b) ->
               eitherFrom aFrom bFrom (eitherTo aTo bTo y) = y
eitherFromTo aTo bTo aFrom bFrom aFromTo bFromTo (Left l)
  = eitherFromToLeft aTo aFrom bFrom aFromTo l
eitherFromTo aTo bTo aFrom bFrom aFromTo bFromTo (Right r)
  = eitherFromToRight bTo aFrom bFrom bFromTo r

eitherFinIso : Iso a (Fin n) -> Iso b (Fin m) -> Iso (Either a b) (Fin (n+m))
eitherFinIso (MkIso aTo aFrom aToFrom aFromTo) (MkIso bTo bFrom bToFrom bFromTo)
  = MkIso (eitherTo aTo bTo)
          (eitherFrom aFrom bFrom)
          (eitherToFrom aTo bTo aFrom bFrom aToFrom bToFrom)
          (eitherFromTo aTo bTo aFrom bFrom aFromTo bFromTo)

(FinEnum a n, FinEnum b m) => FinEnum (Either a b) (n + m) where
     finIso = eitherFinIso finIso finIso


-- FinEnum (a, b)

finProduct : (x : Fin n) -> (y : Fin m) -> Fin (n * m)
finProduct FZ y {n = S n} {m} = weakenN (n * m) y
finProduct (FS x) y {m} = shift m $ finProduct x y

data ProductFin : (m : Nat) -> (j : Nat) -> (k : Nat) -> Fin (m*j + k) -> Type where

tupleTo : (aTo : a -> Fin n) ->
          (bTo : b -> Fin m) ->
          (a, b) -> Fin (n*m)
tupleTo aTo bTo (x, y) = finProduct (aTo x) (bTo y)

ltePlusBoth : (n : Nat) -> (prf : LTE x y) -> LTE (n + x) (n + y)
ltePlusBoth Z prf = prf
ltePlusBoth (S k) prf = LTESucc (ltePlusBoth k prf)

leftLteMult : (n : Nat) -> (m : Nat) -> LTE (S m) (S n * S m)
leftLteMult Z m = rewrite (plusZeroRightNeutral m) in lteRefl
leftLteMult (S k) Z = LTESucc LTEZero
leftLteMult (S k) (S j)
  = lteTransitive (leftLteMult k (S j))
                  (LTESucc (LTESucc (recLeftLteMult (mult k (S (S j))) j)))
  where
    groundCase : (j : Nat) -> (k : Nat) -> LTE k (S (S (plus j k)))
    groundCase j k = lteSuccRight $ lteSuccRight $ rewrite plusCommutative j k in lteAddRight k

    recLeftLteMult : (k : Nat) -> (j : Nat) -> LTE (plus j k) (plus j (S (S (plus j k))))
    recLeftLteMult k j = ltePlusBoth j (the (LTE k (S (S (plus j k)))) (groundCase j k))

tupleFrom : (aFrom : Fin n -> a) ->
            (bFrom : Fin m -> b) ->
            Fin (n*m) -> (a, b)

