# FVPgen: automatically generating rewrite theories and proving Finite Variant Property

### Installation 

The tool requires **OCaml** (https://ocaml.org) as well as **Maude** (http://maude.cs.illinois.edu/w/index.php/Maude_download_and_installation). Our tool was tested on MacOS and relied on the fact that the maude executable should be found in the path. Make sure that an executable `maude` is in your path as the name has been hardcoded in our tool. Moreover, **Maude** version 3.x should be installed as the tool is incompatible with earlier versions 2.x. The tool was mostly tested with **maude 3.4**.

To compile you only need to rune `make`. If you are using **dune**, you can run `make dune` which will run **dune** in the background. Upon completion, an executable `fvpgen` should have appeared in your main folder.

### Executing the tool on an input file

Our tool can be executed with the command `./fvpgen <my_file>`. The input file should follow the structure below.

The first part should declare the function symbols with their arity. When the symbol should be associative and commutative, it should be declare with the option `[AC]`.

```
plus/2 [AC].
zero/0.
```
Then the file should contain a strict ordering on symbols.
```
zero < plus.
```
If the signature contains more than two symbols, the order on symbols should follow the syntax ` f1 < f2 < f3 < ... < fn.`

Finally, the equational theory should declared in a separate section:
```
=== Equational Theory

plus(x,x) = zero.
plus(x,zero) = x.
```

#### Example of Exclusive-Or

```
plus/2 [AC].
zero/0.

zero < plus.

=== Equational Theory

plus(x,x) = zero.
plus(x,zero) = x.
```

#### Example of Diffie Hellman with non-inverse + encryption/decryption scheme

```
mult/2 [AC].
one/0.
exp/2.
decrypt/3.
encrypt/4.

one < mult < exp < encrypt < decrypt.

=== Equational Theory

mult(x,one) = x.
exp(x,one) = x.
exp(one,x) = one.
exp(exp(z,x),y) = exp(z,mult(x,y)).
decrypt(encrypt(m, x, exp(x, y), r), x, y) = m.
```

### Reading the output of the tool

In the case of Diffie Hellman with non-inverse + encryption/decryption scheme, the output is split in several sections:

---
```
Order read: one/0 < mult/2 < exp/2 < encrypt/4 < decrypt/3 < bin/2 < name/1
file parsed...
---Input equation
  (X_1 mult one) = X_1
  exp(X_1,one) = X_1
  exp(one,X_1) = one
  exp(exp(X_1,X_2),X_3) = exp(X_1,(X_2 mult X_3))
  decrypt(encrypt(X_1,X_2,exp(X_2,X_3),X_4),X_2,X_3) = X_1
```
This display the equation read by the tool, i.e it corresponds $E'$ in the paper.

---

```
--- Initial maude theory
fmod TH is
  sort Bitstring .
  sort FakeType .
  op name : Bitstring -> Bitstring [ctor] .
  op bin : Bitstring Bitstring -> Bitstring [ctor] .
  op decrypt : Bitstring Bitstring Bitstring -> Bitstring [ctor] .
  op encrypt : Bitstring Bitstring Bitstring Bitstring -> Bitstring [ctor] .
  op exp : Bitstring Bitstring -> Bitstring [ctor] .
  op mult : Bitstring Bitstring -> Bitstring [ctor assoc comm] .
  op one :  -> Bitstring [ctor] .
  op __ : Bitstring Bitstring -> Bitstring [assoc ctor] .
endfm
```
The maude theory that is fed to **Maude** to compute university modulo AC.

---
```
--- Starting Generate extended signature
Rewrite system rwsysEn:
  (X_1 mult X_2) -> (X_2 mult X_1)
  ((X_1 mult X_2) mult X_3) -> (X_1 mult (X_2 mult X_3))
  (X_1 mult (X_2 mult X_3)) -> ((X_1 mult X_2) mult X_3)
```
This is initial value of the rewrite system $\mathcal{R}$ used in the Algorithm 3 in our paper.

---
```
---Extended signature
Rewrite system R:
  name(X_1) -> name(X_1)
  bin(X_2,X_1) -> bin(X_2,X_1)
  decrypt(X_3,X_2,X_1) -> decrypt(X_3,X_2,X_1)
  encrypt(X_4,X_3,X_2,X_1) -> encrypt(X_4,X_3,X_2,X_1)
  exp(X_2,X_1) -> exp(X_2,X_1)
  (X_2 mult X_1) -> (X_2 mult X_1)
  one -> one
  (one mult X_1) -> X_1
  decrypt(encrypt(X_1,exp(X_2,X_3),exp(X_2,(X_3 mult X_4)),X_5),exp(X_2,X_3),X_4) -> X_1
  exp(exp(X_1,X_2),X_3) -> exp(X_1,(X_2 mult X_3))
  (X_1 mult one) -> X_1
  decrypt(encrypt(X_1,X_2,X_2,X_3),X_2,one) -> X_1
  decrypt(encrypt(X_1,one,one,X_2),one,X_3) -> X_1
  decrypt(encrypt(X_1,X_2,exp(X_2,X_3),X_4),X_2,X_3) -> X_1
  exp(one,X_1) -> one
  exp(X_1,one) -> X_1
Rewrite system Rn:
  (X_1 mult one) -> X_1
  exp(X_1,one) -> X_1
  exp(one,X_1) -> one
  exp(exp(X_1,X_2),X_3) -> exp(X_1,(X_2 mult X_3))
  decrypt(encrypt(X_1,X_2,exp(X_2,X_3),X_4),X_2,X_3) -> X_1
  decrypt(encrypt(X_1,one,one,X_2),one,X_3) -> X_1
  decrypt(encrypt(X_1,X_2,X_2,X_3),X_2,one) -> X_1
  decrypt(encrypt(X_1,exp(X_2,X_3),exp(X_2,(X_3 mult X_4)),X_5),exp(X_2,X_3),X_4) -> X_1
Equations En
  (X_1 mult X_2) = (X_2 mult X_1)
  ((X_1 mult X_2) mult X_3) = (X_1 mult (X_2 mult X_3))
```
The extended signature contained the three main elements from the paper: `R` is the constraint system $\mathcal{R}$, `Rn` is the constraint system $\mathcal{R}_{\downarrow}$ and the equations `En` is the equational theory $E_{\downarrow}$. 

---
```
The following rewrite system is En-convergent for E
  (one mult X_1) -> X_1
  decrypt(encrypt(X_1,exp(X_2,X_3),exp(X_2,(X_3 mult X_4)),X_5),exp(X_2,X_3),X_4) -> X_1
  exp(exp(X_1,X_2),X_3) -> exp(X_1,(X_2 mult X_3))
  (X_1 mult one) -> X_1
  decrypt(encrypt(X_1,X_2,X_2,X_3),X_2,one) -> X_1
  decrypt(encrypt(X_1,one,one,X_2),one,X_3) -> X_1
  decrypt(encrypt(X_1,X_2,exp(X_2,X_3),X_4),X_2,X_3) -> X_1
  exp(one,X_1) -> one
  exp(X_1,one) -> X_1
```
Finally, the output check whether we can derive a rewrite constraint system that is $E_{\downarrow}$-convergent for $E_{\downarrow} \cup E'$.


### Inputting an additional constraint system. 

Our tool also allow to declare in addition to the equational theory a constraint system that should be at least terminating and possibly convergent.

```
mult/2 [AC].
one/0.
inv/1.

one < inv < mult.

=== Terminating Rewrite System

mult(x,one) -> x.
inv(one) -> one.
mult(x,inv(x)) -> one.
mult(inv(x),inv(y)) -> inv(mult(x,y)).
mult(inv(mult(x,y)),y) -> inv(x).
inv(inv(x)) -> x.
inv(mult(inv(x),y)) -> mult(x,inv(y)).
mult(x,mult(inv(x),y)) -> y.
mult(inv(x),mult(inv(y),z)) -> mult(inv(mult(x,y)),z).
mult(inv(mult(x,y)), mult(y,z)) -> mult(inv(x),z).

=== Equational Theory

mult(x,inv(x)) = one.
mult(x,one) = x.
```
In that case, the tool makes two assumptions on the input constraint system $\mathcal{R}_{\downarrow}$.
1. It is $E_{\downarrow}$-terminating
2. There exists an $E_{\downarrow}$-strong reduction order compatible with $\mathcal{R}_{\downarrow}$ (see Section 7 **Discussion** for details on how to build such order).

The tool will try to prove anyway $E_{\downarrow}$-termination using the order implemented so that it applies more optimisations, but in the negative, it will continue assuming that it is true (but then assume that the order is not computable). 

If an extended signature is generated then it implies that the signature models the equational theory $E_{\downarrow} \cup E' \cup \mathcal{R}^=_{\downarrow}$.

We can also declare a constraint system to be convergent:
```
mult/2 [AC].
one/0.
inv/1.

one < inv < mult.

=== Convergent Rewrite System

mult(x,one) -> x.
inv(one) -> one.
mult(x,inv(x)) -> one.
mult(inv(x),inv(y)) -> inv(mult(x,y)).
mult(inv(mult(x,y)),y) -> inv(x).
inv(inv(x)) -> x.
inv(mult(inv(x),y)) -> mult(x,inv(y)).
mult(x,mult(inv(x),y)) -> y.
mult(inv(x),mult(inv(y),z)) -> mult(inv(mult(x,y)),z).
mult(inv(mult(x,y)), mult(y,z)) -> mult(inv(x),z).

=== Equational Theory

mult(x,inv(x)) = one.
mult(x,one) = x.
```
It is assumed that the constraint system $\mathcal{R}_{\downarrow}$ is $E_{\downarrow}$-convergent for $E'$. This allows us to apply additional optimisations. Note that the tool will anyway try to show convergence of the constraint system given as input. 


---

Copyright (C) 2024 Vincent Cheval (University of Oxford).

GNU GENERAL PUBLIC LICENSE Version 3