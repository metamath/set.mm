# How are the databases verified?

We work to provide *extremely* high confidence that the
proofs are completely correct in these databases,
especially for the set.mm and iset.mm databases (the
primary databases under active development).
Most published mathematical proofs don't have a formal proof at all
(a formal proof is a proof where every step is completely and
automatically verified by machine).
Most other projects would be delighted to have formal verification of
proofs by a *single* verification tool.
We could do that in Metamath, too, but we go much further.

Changes ("commits") to any database are first automatically verified
before they are accepted, using GitHub actions.
In *every* change, the proofs of *each* of the set.mm and iset.mm databases
is re-verified by *five* different verifiers:

* metamath.exe aka Cmetamath (the original C verifier by Norman Megill)
* checkmm (a C++ verifier by Eric Schmidt)
* smetamath-rs (smm3) (a Rust verifier by Stefan O'Rear)
* mmj2 (a Java verifier by Mel L. O'Cat and Mario Carneiro)
* mmverify.py (a Python verifier by Raph Levien)

Note that these are different verifiers written in different programming
languages by different people. The verification algorithm
is also intentionally simple (it fits in two pages in the Metamath book),
so it's relatively easy to implement a verifier, it's more likely to be
correct (because of its simplicity), and it's relatively
easy to review a verifier.

All other databases' proofs are verified by one verifier (metamath.exe).

Other checks are also performed.
Text markup is checked by metamath-exe, and definitions are checked by mmj2.

The actual script that implements these checks is
[verifiers.yml](.github/workflows/verifiers.yml)
which you can investigate for yourself.

The verifiers vary in their speed. The parallel Rust verifier is the
fastest; it can typically verify set.mm (the largest database) in
less than a second. The metamath.exe verifier, written in C, can verify
databases in seconds. The Python verifier is slower, because the most
widely used implementation of Python is relatively slow, but it's still
fast enough to be used in every commit.

See [README.md](./README.md) for more general information.
