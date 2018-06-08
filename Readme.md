# Finite Enum

`FiniteEnum` is a type class for types that are isomorphic
to `Fin n` for a given `n`. Using this isomorphism, we can enumerate
the values of the type.

Example:

```idris
*src/Data/FiniteEnum> the (Vect _ (Maybe Bool)) enumerate
[Nothing, Just False, Just True] : Vect 3 (Maybe Bool)
```

Thanks to the isomorphism with `Fin`, we can also _derive_ instances for many interfaces:

- `DecEq` (name of the instance" `finEnumDecEq`);
- `Eq` (name of the instance" `finEnumEq`);
- `Ord` (name of the instance" `finEnumOrd`);
- `MinBound` (name of the instance" `finEnumMinBound`);
- `MaxBound` (name of the instance" `finEnumMaxBound`);
- `Enum` (name of the instance" `finEnumEnum`).
