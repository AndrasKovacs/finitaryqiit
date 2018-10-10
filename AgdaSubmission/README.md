
### Agda code for "Constructing QIITs"

This folder has been tested with Agda 2.5.4.

Agda does not have native support for QIITs, which are required to
work with intrinsic embedded syntaxes of type theories. Hence, we need
to use postulation and rewrite pragmas to recover needed functionality.

[`Lib.agda`](Lib.agda) is a general library, which does not use
uniqueness of identity (UIP). [`StrctLib.agda`](StrictLib.agda) is a
standard library which does rely on UIP. The splitting allows us to
conveniently choose whether to depend on UIP, but in this development,
we always depend on it.

[`Syntax.agda`](Syntax.agda) postulates the syntax, so that we can
refer to it from other models, and get some computational behavior.
Immediately after postulating syntax, we also reflect most beta rules
using REWRITE pragmas. This confers a huge benefit when constructing
dependent models, since we do not have to transport over equality
constructors which hold definitionally. Unfortunately, Agda 2.5.4. is
not liberal enough when matching REWRITE rules, so we need to add a
number of specialized rule instances, and even then the system does
not always rewrite as expected.

[`ModelTemplate.agda`](ModelTemplate.agda) is a module which postulates
the signature of a model of the syntax. As the name suggests,
this is just a template for writing models. We use it the following way:

1. Copy and paste from `ModelTemplate.agda`.
2. Remove all `postulate`-s, and provide definitions for components.
3. When done with defining all components, uncomment the REWRITE rules
   to get recursors.

You may also notice that [`ModelTemplate.agda`](ModelTemplate.agda)
has all types in forms where implicit arguments are printed
explicitly. This is to aid type inference during construction of
models: without explicit annotation, Agda is not able to solve
metavariables in component types for pretty much any non-trivial
model. This makes component types fairly unreadable, but you can refer
to [`Syntax.agda`](Syntax.agda) for the corresponding readable
non-expanded
forms.[`DependentModelTemplate.agda`](DependentModelTemplate.agda) is
similar, except that it is for dependent models (which correspond to
doing induction on syntax, as opposed to doing recursion on syntax).
Now, this infrastructure is not particularly nice to work with, and it
is very time-consuming to manually write out recursors, eliminators,
models, and dependent models (displayed algebras) for entire type
theories. However, we are not aware of better infrastructures which
let us do comparable formalization. Coq in particular is better suited
for large projects, but unfortunately it allows no feasible emulation
of QIITs.

[`ADS.agda`](ADS.agda) contains the algebra-displayed algerba-section
model of the theory of signatures.

[`AM.agda`](AM.agda) contains the algebra-homomorphism model of the
syntax. Homomorphisms are discussed in section 5 of the paper
"Constructing QIIts", but no other formalization here depends on them.

[`InitialAlg`](InitialAlg) contains the -ᶜ initial algebra model. It is
split into several files, in order to make incremental type checking
faster. The postulated eliminators are contained in
[`InitialAlg/Eliminators.agda`](InitialAlg/Eliminators.agda).

[`Elimination`](Elimination) contains the -ᴱ model, providing algebra
sections from the initial algebra to arbitrary displayed algebras. We
don't need to postulate eliminators for this model, since there are no
other models in the project which need to refer to them.

The `Elimination` and `InitialAlg` models both omit components which
are made trivial by UIP. They are also both incomplete in the case of
Pi, as there the confluence of "transport hell" and fragile REWRITE
behavior leads to technical difficulties.

[`CwF-Induction-Initiality.agda`](CwF-Induction-Initiality.agda)
contains a proof that induction is equivalent to initiality in any CwF
with constant families and extensional equality. This is discussed
in section 7.3 of the paper.

The [`CwFUElPi-Of-Categories`](CwFUElPi-Of-Categories) folder contains
a partial formalization of chapter 7.4 of the paper. The full
formalization would be a CwF-K-Eq model of the full syntax of
signatures. Here, we only construct a CwF+U+El+Pi of categories. This
is significantly smaller than the full model, since a category has
seven components, while a CwF-K-Eq has several times more. It appears
that we cannot go much beyond this formalization using Agda, as
Agda tends to run out of memory and typecheck forever when we try to
consider additional parts of the model.

[`NatInitialInd.agda`](NatInitialInd.agda) contains formalization of
the CwF-of-natural-number-algebra examples from section 7.4 of the
paper.
