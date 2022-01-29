# Week 2

## Proving Question:

Prove that in all, there are p^r(p^r+1)/2 numbers binom(n)(m), with 0 <= n < p^r, 0 <= m <= n, of which exactly p^r(p+1)^r/2^r are not divisible by p.

[Source. Use link for LaTeX math expressions](https://math.stackexchange.com/questions/3388991/number-of-binomnm-not-divisible-by-a-prime-p)

[Proof Explained](https://math.stackexchange.com/a/3767593)

## Programming Question:

Tower of Hanoi is a mathematical puzzle where we have three rods and n disks. The objective of the puzzle is to move the entire stack to another rod, obeying the following simple rules: 

1. Only one disk can be moved at a time.
2. Each move consists of taking the upper disk from one of the stacks and placing it on top of another stack i.e. a disk can only be moved if it is the uppermost disk on a stack.
3. No disk may be placed on top of a smaller disk.

The challenge is to create a function that receives a natural number `n` and returns the steps necessary to move `n` discs from a rod to another.

Extra:
* Prove that your function only makes valid moves
* Prove that your function indeed solves the challenge
