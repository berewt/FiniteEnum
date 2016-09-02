module Data.FiniteEnum

import Control.Isomorphism

import Data.Vect
import Data.Fin

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

export
fromFinIso : (prf : Iso a (Fin card)) -> Fin card -> a
fromFinIso (MkIso to from toFrom fromTo) = from

export
fromFin : FinEnum a n => Fin n -> a
fromFin = fromFinIso finIso

export
toFinIso : (prf : Iso a (Fin card)) -> a -> Fin card
toFinIso (MkIso to from toFrom fromTo) = to

export
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
