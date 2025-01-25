# Flean

Flean is an attempt at formalizing floating point numbers in Lean 4.

![Look what they need to match a fraction](meme.png)

# Goals and Non-Goals

**Personally**: Learn Lean in a serious but not hard way. I've already learned a lot.

In general, the idea is to (1) model the floating point numbers, (2) characterize their properties via a convenient set of rules,
and (3) apply that logic to prove things about Lean's `Float` by declaring an interface axiomatically.

## Goals

- Be capable of matching operations of normal floating points as exactly as possible [IEEE 754](https://en.wikipedia.org/wiki/IEEE_754)
- Extensible to different precisions
- Theoretically capable of supporting lots of bounds on Lean's `Float` 

## Non-Goals

- Performance
- Fixed-point arithmetic
- Interval arithmetic
- Using [SMT](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories) solvers to [bitblast](https://github.com/bitwuzla/bitwuzla) our way to happiness--which is almost certainly the most practical approach.

