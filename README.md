# Compiler from CuMin to SaLT

This implements a translation from the functional-logic language CuMin to the lower-level language SaLT.
These programming languages and the translation are described in detail
in [my bachelor's thesis](https://github.com/fanzier/cs-bsc-thesis).

**I currently don't maintain this project anymore.**

## Example run

The **CuMin input program**

```haskell
length :: forall a. List a -> Nat
length list = case list of
  Nil -> 0
  Cons x xs -> 1 + length<:a:> xs
```

is **automatically translated** (after optimizations) to

```haskell
length :: forall a. Set (List a -> Set Nat)
length = {\list_56 :: List a -> case list_56 of
    Nil -> {0}
    Cons x_57 xs_58 -> length<:a:> >>= (\arg_59 :: (List a
                                           -> Set Nat) -> arg_59 xs_58 >>=
      (\primOpArg_60 :: Nat -> {1 + primOpArg_60}))}
```

A **manual translation** gives the same result (up to variable renaming):
```haskell
length :: forall a. Set (List a -> Set Nat)
length = { \list :: List a -> case list of
  Nil -> {0}
  Cons x xs -> length<:a:> >>=
    \length' :: (List a -> Set Nat) ->
    length' xs >>= \l :: Nat -> {1 + l} }
```
