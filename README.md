# anonymous-credentials-hs

**This library has not been independently audited. Use at your own risk.**

A Haskell implementation of algebraic MAC-based anonymous credential schemes,
following "Algebraic MACs and Keyed-Verification Anonymous Credentials"
(Chase, Meiklejohn, Zaverucha, CCS 2014).

## Schemes

The library provides two MAC constructions:

- **BBS** (`Crypto.AnonymousCredentials.BBS`) -- MACs include auxiliary base
  points derived from the secret key, giving simpler zero-knowledge
  presentations at the cost of a larger MAC representation.

- **CMZ** (`Crypto.AnonymousCredentials.CMZ`) -- A compact alternative using
  Pedersen commitments for hidden attributes during presentation. MACs are
  just two group elements.

Both schemes support selective disclosure, unlinkable presentations, and
scoped pseudonyms via the Dodis-Yampolskiy PRF.

## Building

Requires the [`sigma-proofs`](https://github.com/SamuelSchlesinger/sigma-hs)
library (Ristretto255 via Rust FFI), so you will need GHC, Cabal, and a Rust
toolchain.

```
cabal build
cabal test
```
