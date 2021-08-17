# Subtype Universes

Files from this directory are based on the paper [Subtype Universes](http://www.cs.rhul.ac.uk/home/zhaohui/Subtype%20Universes.pdf) by Harry Maclean and Zhaohui Luo.

The basic idea is for every type `A` to have a type `U(A)` representing the universe of subtypes of `A`, i.e. types `X` that satisfy `X <= A` become `X : U(A)`.

The type theory from the paper is ECC (which is a particular presentation of the Calculus of Constructions, described in [Luo's thesis](http://www.cs.rhul.ac.uk/home/zhaohui/ECS-LFCS-90-118.pdf) and in [book form based on the thesis](https://global.oup.com/academic/product/computation-and-reasoning-9780198538356?cc=gb&lang=en&) + coercions (described [here](https://hal.archives-ouvertes.fr/hal-01130574/document).