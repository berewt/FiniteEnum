module Data.FiniteEnum

import Control.Isomorphism

import Data.Vect
import public Data.Fin

%default total

export
enumerateIso : (prf : Iso a (Fin card)) -> Vect card a
enumerateIso (MkIso to from toFrom fromTo) = map from range

public export
interface FinEnum a (n : Nat) | a where
  finIso : Iso a (Fin n)

export
enumerate : FinEnum a n => Vect n a
enumerate = enumerateIso finIso

public export
fromFinIso : (prf : Iso a (Fin card)) -> Fin card -> a
fromFinIso (MkIso to from toFrom fromTo) = from

public export
fromFin : FinEnum a n => Fin n -> a
fromFin = fromFinIso finIso

public export
toFinIso : (prf : Iso a (Fin card)) -> a -> Fin card
toFinIso (MkIso to from toFrom fromTo) = to

public export
toFin : FinEnum a n => a -> Fin n
toFin = toFinIso finIso

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


FinEnum (Fin m) m where
  finIso = isoRefl


(FinEnum a m, FinEnum b n) => FinEnum (Either a b) (m + n) where
  finIso = isoTrans (eitherCong finIso finIso) eitherFinPlus


(FinEnum a m, FinEnum b n) => FinEnum (a, b) (m * n) where
  finIso = isoTrans (pairCong finIso finIso) finPairTimes


FinEnum a m => FinEnum (Maybe a) (S m) where
  finIso = isoTrans (maybeCong finIso) maybeIsoS

private
decOnFin :  FinEnum a m
         => (x: a) -> (y : a)
         -> (from : Fin m -> a)
         -> (to : a -> Fin m)
         -> (fromTo : (z : a) -> from (to z) = z)
         -> Dec (x = y)
decOnFin x y from to fromTo with (decEq (to x) (to y))
  | (Yes prf) = Yes $ rewrite sym (fromTo x) in
                      rewrite sym (fromTo y) in cong prf
  | (No contra) = No (contra . cong)

-- Deriving via for Finite Enum

[finEnumDecEq] FinEnum a m => DecEq a where
  decEq x y {a} {m}= let
    MkIso to from _ fromTo = finIso {a} {n = m}
    in decOnFin x y from to fromTo

[finEnumEq] FinEnum a m => Eq a where
  (==) x y = decAsBool (decEq @{finEnumDecEq} x y)

private
compareOnFin : (x : Fin m) -> (y : Fin m) -> Ordering
compareOnFin = compare

[finEnumOrd] FinEnum a m => Ord a using finEnumEq where
  compare x y = compareOnFin (toFin x) (toFin y)

[finEnumMinBound] FinEnum a (S m) => MinBound a using finEnumOrd where
  minBound = fromFin FZ

[finEnumMaxBound] FinEnum a (S m) => MaxBound a using finEnumOrd where
  maxBound = fromFin last

private
toNatViaFin : FinEnum a (S m) => a -> Nat
toNatViaFin = toNat . toFin

private
fromNatViaFin : FinEnum a (S m) => Nat -> a
fromNatViaFin = fromFin . fromNat

private
predViaFin : FinEnum a (S m) => a -> a
predViaFin = fromFin . pred . toFin

private
succViaFin : FinEnum a (S m) => a -> a
succViaFin = fromFin . succ . toFin

[finEnumEnum] FinEnum a (S m) => Enum a where

  pred = predViaFin
  succ = succViaFin
  toNat = toNatViaFin
  fromNat = fromNatViaFin
