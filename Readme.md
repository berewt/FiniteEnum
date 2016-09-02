# Finite Enum

`FiniteEnum` is a type class for types that are isomorphic
to `Fin n` for a given `n`. Using this isomorphism, we can enumerate
the values of the type.

Example:

```idris
*src/Data/FiniteEnum> the (Vect _ (Maybe Bool)) enumerate
[Nothing, Just False, Just True] : Vect 3 (Maybe Bool)
```
