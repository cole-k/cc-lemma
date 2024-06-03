# The `.ceg` language

CCLemma takes as input a `.ceg` file that contains datatype definitions,
function defitions, and properties that may hold for them.

For parsing convenience, the data is all represented as s-expressions. The
language's syntax is otherwise rather similar to that of Haskell.

The base `.ceg` file is a list of definitions, i.e.

```
(
def1
def2
...
defn
)
```

## Definitions

### Datatype declaration

A datatype is declared using the `data` keyword, whose syntax looks like:

```
(data TYPE_NAME [(TYPE_VARS)] (CONSTRUCTORS...))
```

The argument following `data` is the name. Type names must start with
an uppercase character.

After the name is either a list of type variables (which all must start with
lowercase letters) and a list of constructors (which all must start with
uppercase letters) or just the list of constructors.

The following, for example, declares the datatype of linked `List`s. Although
it is not immediately clear that this is so because we have yet to see the types
of its constructors `Nil` and `Cons`.

```
(data List (a) (Nil Cons))
```

If the type has no type variables, then the type vars argument may be omitted,
like with `Nat`.

```
(data Nat (Z S))
```

We require that you give a type declaration for each constructor.

### Type declaration

The type of a constructor is declared using `::`:

```
(:: FN_NAME FN_TYPE)
```

The names of constructors are capitalized while the names of functions start
lowercase.

We can now specify the types of the constructors of `List`s.

```
(data List (a) (Nil Cons))
(:: Nil  (List a))
(:: Cons (-> (a (List a)) (List a)))
```

Similarly, functions can have their types specified

```
(:: id (-> (a) a))
```

#### Types

There are three basic kinds of types.


Base types, which are written as-is (i.e. not in a list), e.g.

```
Nat
Bool
```

Fully-applied type constructors, which are written as lists, e.g.

```
(List a)
(Pair Nat Bool)
```

Arrow types, e.g. the type of `Cons`

```
(-> (a (List a)) (List a))
```

Note that the first argument of an arrow is a _list_ of types. The second
argument is a type.

So the below is not a valid way to write the type of the identity function

```
(-> a a)
```

but this is

```
(-> (a) a)
```

### Function/axiom definitions

Functions may be defined using the `let` keyword.

```
(let FN_NAME (ARGS) OUTPUT)
```

That is, the argument after the name is a list of arguments and the final
argument is what the function evaluates to on those arguments.

`ARGS` _must_ be a list even if the function only takes a single argument.

i.e. this is not valid

```
(let id ?x ?x)
```

but this is

```
(let id (?x) ?x)
```

Both `ARGS` and `OUTPUT` are patterns. For functions, the arguments may only be
patterns containing constructors.

Function definitions are always evaluated against patterns they match against;
they are _not_ tried in order.

An example function evaluation is

```
(id Z)
```

which matches the only function definition of `id` at `?x: Z` and evaluates to

```
Z
```

Axioms are like functions but defined with `axiom` instead of `let`. They
may contain functions as well as constructors in their arguments.

#### Patterns

A pattern is an s-expression built of constructors, functions, and pattern
variables.

A pattern variable begins with `?`, e.g. `?x` or `?var1`.

Intuitively, patterns match terms in the language, binding their variables to
those terms.

For example, the pattern

```
(Cons (foo ?x) ?y)
```

matches

```
(Cons (foo Z) Nil)
```

and its variables are bound to `?x: Z, ?y: Nil`.

It doesn't, however, match

```
(Cons Z Nil)
```

because only `?y` matches something.

### Properties

Properties are the main definition used to interact with CCLemma. It will
attempt to prove any property specified in a `.ceg` file.

#### Unconditional properties

An unconditional property is a property which doesn't have a condition. They are
defined as follows, with `===`

```
(=== PROPERTY_NAME (VARS) (VAR_TYPES)
  LHS
  RHS
  (AUX_REWRITES))
```

`VARS` is a list of variables used by the property. It must be in a list. Note
that these do not begin with `?`.

`VAR_TYPES` is a list of the types of the variables, in order of their
definition. It must also be in a list.

`LHS` and `RHS` are the left- and right-hand sides defined over the `VARS` that
are to be proven (un)equal.

`AUX_REWRITES` is an optional list of auxiliary rewrites that are assumed true.
These are useful for debugging. There are three types of `AUX_REWRITES`:

* `(=> LHS_PAT RHS_PAT)` which takes an LHS and RHS _pattern_ (not term) and
  assumes it as a rewrite from the LHS to the RHS.
* `(<=> LHS_PAT RHS_PAT)` is the same as the above but is bidirectional.
* `(=?> LHS_PAT RHS_PAT)` Looks to see if there are two e-classes which both
  match LHS and RHS, are not already equal, yet have the same _characteristic
  vector_ (an analysis our tool uses to vet whether e-classes could be unified).

This is an example, taken from `isaplanner.ceg`.

```
(=== goal_01 (n xs) (Nat (List a))
  (append (take n xs) (drop n xs))
  xs)
```
  
#### Conditional properties

Conditional properties are the same as unconditional properties except they have
a condition (aka premise). They are defined with `==>`.

```
(==> PROPERTY_NAME (VARS) (VAR_TYPES)
  LHS_COND
  RHS_COND
  LHS
  RHS
  (AUX_REWRITES))
```

Its only addition is a condition on the property. The condition states that if
`LHS_COND` = `RHS_COND`, then the property `LHS` = `RHS` holds.

The following is a property from IsaPlanner conditioned upon `n = x`.

```
(==> goal_05 (xs n x) ((List Nat) Nat Nat)
  n
  x
  (add (S Z) (count n xs))
  (count n (Cons x xs)))
```

## Builtins
We include a special reserved function `$` to allow for partial application in
higher-order functions.

`map`, for example, needs to be defined using `$` otherwise it cannot evaluate
properly.

```
(:: map (-> ((-> (a) b) (List a)) (List b)))
(let map (?f Nil          ) Nil                          )
(let map (?f (Cons ?x ?xs)) (Cons ($ ?f ?x) (map ?f ?xs)))
```

## Assumptions
We require that the following definitions are always provided (i.e. they aren't
baked into the prover but it expects them to be defined as such)

```
(data Bool (True False))
(:: True Bool)
(:: False Bool)

(:: ite (-> (Bool a a) a))
(let ite (True ?x ?y ) ?x)
(let ite (False ?x ?y) ?y)
```

If you change (or in some cases forget to provide) them, CCLemma may panic or
behave strangely.
