EVM Prime
=========

In `EVMPRIME` mode, certain opcodes can be used which compile down to standard EVM but provide better-behaved high-level language constructs.

```{.k .uiuck .rvk}
requires "evm.k"

module EVM-PRIME
    imports EVM
```

```{.k .rvk}
    imports K-REFLECTION
```

The extra sort `PrimeOp` are op-codes which only exist in EVM-PRIME, so must be compiled to EVM.

```{.k .uiuck .rvk}
    syntax OpCode ::= PrimeOp
 // -------------------------

    syntax Bool ::= isCompiled ( OpCodes ) [function]
 // -------------------------------------------------
    rule isCompiled ( .OpCodes ) => true
    rule isCompiled ( OP ; OPS ) => (notBool isPrimeOp(OP)) andBool isCompiled(OPS)
```

-   `TypedAddr` stores the address and its corresponding type.
-   `CompileCtx` stores the information for compiling EVM-PRIME.
    -   `Map` stores the variables to typed addresses mapping.
    -   `Int` stores the next available memory location.

```{.k .uiuck .rvk}
    syntax TypedAddr ::= taddr ( ABIType , Int )
    syntax CompileCtx ::= cctx ( Map , Int )
```

-   `#resolvePrimeOp` and `#resolvePrimeOps` operate in the monad from `(ENV, OpCode) -> OpCodes`.

```{.k .uiuck .rvk}
    syntax OpCodes ::= #resolvePrimeOp  ( CompileCtx , OpCode  ) [function]
                     | #resolvePrimeOps ( CompileCtx , OpCodes ) [function]
 // ------------------------------------------------------------------------------
    rule #resolvePrimeOp( CTX , OP ) => OP ; .OpCodes requires notBool isPrimeOp(OP)

    rule #resolvePrimeOps( _ , .OpCodes ) => .OpCodes
    rule #resolvePrimeOps( CTX , OP ; OPS ) => #resolvePrimeOp(CTX , OP) ++OpCodes #resolvePrimeOps(CTX , OPS)

    syntax OpCodes ::= OpCodes "++OpCodes" OpCodes [function]
 // ---------------------------------------------------------
    rule .OpCodes    ++OpCodes OPS  => OPS
    rule (OP ; OPS1) ++OpCodes OPS2 => OP ; (OPS1 ++OpCodes OPS2)
```

-   `#compile` will desugar `PrimeOp`s with `#resolvePrimeOps` and then resolve the jump destinations with `#resolveJumps`.

```{.k .uiuck .rvk}
    syntax OpCodes ::= #compilePrimeOps ( OpCodes ) [function]
 // --------------------------------------------------
    rule #compilePrimeOps(OPS) => #resolvePrimeOps(cctx(.Map , 0), OPS)
```

### Example

This is psuedo-code for the running example we have throughout this document.

```
s = 0 ;
n = 10 ;
while ( n > 0 ) {
    s = s + n ;
    n = n - 1 ;
}
sstore(0, s) ;
```

Structured Jumps
----------------

Because jump destinations are not well-defined until the entire program has been represented as bytecode, desugaring the `jump*` opcodes *must* be done *last*.

-   `jumpdest` allows marking a jump destination with a string (instead up relying on the program counter).
-   `jump` and `jumpi` allow supplying the string-labeled jump destination for jumping (instead of `PUSH`ing the destination).

```{.k .uiuck .rvk}
    syntax OpCode ::= JumpPrimeOp
    syntax JumpPrimeOp ::= jumpdest ( String ) | jump ( String ) | jumpi ( String )
 // -------------------------------------------------------------------------------
```

-   `#resolveJumps` will replace the labeled jump destinations/jumps with their corresponding EVM code.
-   `#calcJumpTable` is a helper for resolving the jump table.

```{.k .uiuck .rvk}
    syntax OpCodes ::= #resolveJumps ( OpCodes )             [function]
                     | #resolveJumps ( OpCodes , Int , Map ) [function, klabel(#resolveJumpsAux)]
 // ---------------------------------------------------------------------------------------------
    rule #resolveJumps( OPS ) => #resolveJumps( OPS , #maxJumpPushWidth(OPS), #calcJumpTable( OPS , 0 , #maxJumpPushWidth(OPS) , .Map ) )

    rule #resolveJumps( .OpCodes              , W , JT ) => .OpCodes
    rule #resolveJumps( OP              ; OPS , W , JT ) => OP       ; #resolveJumps(OPS, W, JT) requires notBool isJumpPrimeOp(OP)
    rule #resolveJumps( jumpdest(LABEL) ; OPS , W , JT ) => JUMPDEST ; #resolveJumps(OPS, W, JT)
    rule #resolveJumps( jump(LABEL)     ; OPS , W , LABEL |-> PCOUNT JT ) => PUSH(W, PCOUNT) ; JUMP  ; #resolveJumps(OPS, W, LABEL |-> PCOUNT JT)
    rule #resolveJumps( jumpi(LABEL)    ; OPS , W , LABEL |-> PCOUNT JT ) => PUSH(W, PCOUNT) ; JUMPI ; #resolveJumps(OPS, W, LABEL |-> PCOUNT JT)

    syntax Map ::= #calcJumpTable ( OpCodes , Int , Int , Map ) [function]
 // ----------------------------------------------------------------------
    rule #calcJumpTable( .OpCodes              , _      , MW , JT ) => JT
    rule #calcJumpTable( jumpdest(LABEL) ; OPS , PCOUNT , MW , JT ) => #calcJumpTable(OPS, PCOUNT +Int 1,        MW, JT [ LABEL <- PCOUNT ])
    rule #calcJumpTable( jump(LABEL)     ; OPS , PCOUNT , MW , JT ) => #calcJumpTable(PUSH(MW, 0) ; JUMP  ; OPS, PCOUNT, MW, JT)
    rule #calcJumpTable( jumpi(LABEL)    ; OPS , PCOUNT , MW , JT ) => #calcJumpTable(PUSH(MW, 0) ; JUMPI ; OPS, PCOUNT, MW, JT)
    rule #calcJumpTable( PUSH(W, _)      ; OPS , PCOUNT , MW , JT ) => #calcJumpTable(OPS, PCOUNT +Int W +Int 1, MW, JT)
    rule #calcJumpTable( _               ; OPS , PCOUNT , MW , JT ) => #calcJumpTable(OPS, PCOUNT +Int 1,        MW, JT) [owise]
```

-   `#maxJumpPushWidth` will calculate the maximum jump address that can be used in a chunk of EVM.
-   `#maxOpCodesWidth` will calculate the maximum width that an EVM `OpCodes` could have after resolving jump destinations.

```{.k .uiuck .rvk}
    syntax Int ::= #maxJumpPushWidth ( OpCodes ) [function]
                 | #maxOpCodesWidth  ( OpCodes ) [function]
 // -------------------------------------------------------
    rule #maxJumpPushWidth ( OPS ) => #sizeWordStack(#asByteStack(#maxOpCodesWidth(OPS)))

    rule #maxOpCodesWidth( .OpCodes )          => 0
    rule #maxOpCodesWidth( PUSH(W, _)  ; OPS ) => W +Int 1 +Int #maxOpCodesWidth(OPS)
    rule #maxOpCodesWidth( jumpdest(_) ; OPS ) => 1        +Int #maxOpCodesWidth(OPS)
    rule #maxOpCodesWidth( jump(_)     ; OPS ) => 34       +Int #maxOpCodesWidth(OPS)
    rule #maxOpCodesWidth( jumpi(_)    ; OPS ) => 34       +Int #maxOpCodesWidth(OPS)
    rule #maxOpCodesWidth( OP          ; OPS ) => 1        +Int #maxOpCodesWidth(OPS) [owise]
```

### Example

In this example, we check that using the structured jumps desugars to the correct original program.

```{.k .example}
load "exec" : { "code" : PUSH(1, 0)  ; PUSH(1, 0)  ; MSTORE
                       ; PUSH(1, 10) ; PUSH(1, 32) ; MSTORE
                       ; jumpdest("loop-begin")
                       ; PUSH(1, 0) ; PUSH(1, 32) ; MLOAD ; GT
                       ; ISZERO ; jumpi("end")
                       ; PUSH(1, 32) ; MLOAD ; PUSH(1, 0)  ; MLOAD ; ADD ; PUSH(1, 0)  ; MSTORE
                       ; PUSH(1, 1)          ; PUSH(1, 32) ; MLOAD ; SUB ; PUSH(1, 32) ; MSTORE
                       ; jump("loop-begin")
                       ; jumpdest("end")
                       ; PUSH(1, 0) ; MLOAD ; PUSH(1, 0) ; SSTORE
                       ; .OpCodes
              }

compile

check "program" : PUSH(1, 0)  ; PUSH(1, 0)  ; MSTORE
                ; PUSH(1, 10) ; PUSH(1, 32) ; MSTORE
                ; JUMPDEST
                ; PUSH(1, 0) ; PUSH(1, 32) ; MLOAD ; GT
                ; ISZERO ; PUSH(1, 43) ; JUMPI
                ; PUSH(1, 32) ; MLOAD ; PUSH(1, 0)  ; MLOAD ; ADD ; PUSH(1, 0)  ; MSTORE
                ; PUSH(1, 1)          ; PUSH(1, 32) ; MLOAD ; SUB ; PUSH(1, 32) ; MSTORE
                ; PUSH(1, 10) ; JUMP
                ; JUMPDEST
                ; PUSH(1, 0) ; MLOAD ; PUSH(1, 0) ; SSTORE
                ; .OpCodes

failure "DESUGAR EVMPRIME JUMPS"

clear
```

PUSH Simplification
-------------------

TODO (low): Add "typed" `push`. Eg, could say `push("hello")`, and it would do the sequence of word pushes necessary for that.
Not sure quite what this would get us, but perhaps good things long-term.

TODO : byteWidth could be calculated using byte2Int up/Int 8

-   `push` allows not specifying the width of the constant being pushed (it will be calculated for you).

```{.k .uiuck .rvk}
    syntax PrimeOp ::= push ( Int ) [function]
 // ------------------------------------------
    rule push(N) => PUSH(#sizeWordStack(#padToWidth(1, #asByteStack(N))), N) requires N <Int pow256

    syntax Int ::= #byteWidth ( Int ) [function]
 // --------------------------------------------
    rule #byteWidth( I:Int ) => #sizeWordStack(#padToWidth(1, #asByteStack(I)))
```

### Example

In this example, we use our simpler `push` notation for avoiding specifying the width of a `PUSH`.

```{.k .example}
load "exec" : { "code" : push(0)  ; push(0)  ; MSTORE
                       ; push(10) ; push(32) ; MSTORE
                       ; jumpdest("loop-begin")
                       ; push(0) ; push(32) ; MLOAD ; GT
                       ; ISZERO ; jumpi("end")
                       ; push(32) ; MLOAD ; push(0)  ; MLOAD ; ADD ; push(0)  ; MSTORE
                       ; push(1)          ; push(32) ; MLOAD ; SUB ; push(32) ; MSTORE
                       ; jump("loop-begin")
                       ; jumpdest("end")
                       ; push(0) ; MLOAD ; push(0) ; SSTORE
                       ; .OpCodes
              }

compile

check "program" : PUSH(1, 0)  ; PUSH(1, 0)  ; MSTORE
                ; PUSH(1, 10) ; PUSH(1, 32) ; MSTORE
                ; JUMPDEST
                ; PUSH(1, 0) ; PUSH(1, 32) ; MLOAD ; GT
                ; ISZERO ; PUSH(1, 43) ; JUMPI
                ; PUSH(1, 32) ; MLOAD ; PUSH(1, 0)  ; MLOAD ; ADD ; PUSH(1, 0)  ; MSTORE
                ; PUSH(1, 1)          ; PUSH(1, 32) ; MLOAD ; SUB ; PUSH(1, 32) ; MSTORE
                ; PUSH(1, 10) ; JUMP
                ; JUMPDEST
                ; PUSH(1, 0) ; MLOAD ; PUSH(1, 0) ; SSTORE
                ; .OpCodes

failure "DESUGAR EVMPRIME PUSH"

clear
```

ABI Types
---------

TODO (low): Add dynamically sized types.

For the type-system of EVM-PRIME, we use the types supplied in the [Ethereum Contract ABI](https://github.com/ethereum/wiki/wiki/Ethereum-Contract-ABI).
This means that well-typed EVM-PRIME programs generate ABI-compliant code.

-   `bool` is a variable of fixed size 1 byte, restricted to values 1 and 0.
-   `bytes(N)` is a variable of fixed size `N` bytes.
-   `address` is a `bytes(20)`.
-   `T[N]` is a `N` width array of type `T`.

```{.k .uiuck .rvk}
    syntax ABIType ::= "bool"
                     | bytes ( Int ) | "address" [function]
                     | ABIType "[" Int "]"
 // --------------------------------------
    rule address => bytes(20)
```

-   `ArithType` are types which may appear in arithmetic expressions.
-   Types ending in `word` are types where the integer expresses the size in bytes.
-   Types not ending in `word` are types where the integer expresses the size in bits.
-   They are immediately desugared into types ending in `word`.

TODO (high): Explain what each different word type here means and add appropriate desugarings.

```{.k .uiuck .rvk}
    syntax ABIType   ::= ArithType
    syntax ArithType ::= uintword ( Int )
                       |  intword ( Int )
                       | ufixed ( Int , Int )
                       |  fixed ( Int , Int )
                       | ufixedword ( Int , Int )
                       |  fixedword ( Int , Int )
 // ---------------------------------------------
```

-   `uint` and `int` desugar into `uintword` and `intword` if they have the correct bit-width.

```{.k .uiuck .rvk}
    syntax ArithType ::= uint ( Int ) [function]
                       |  int ( Int ) [function]
 // --------------------------------------------
    rule uint ( N ) => uintword ( N /Int 8 ) requires N %Int 8 ==Int 0
    rule  int ( N ) => intword  ( N /Int 8 ) requires N %Int 8 ==Int 0
```

-   `#type` is used for type-checking EVM-PRIME programs.

```{.k .uiuck .rvk}
    syntax ABIType ::= #type ( ExpOp , CompileCtx ) [function]
 // ----------------------------------------------------
    rule #type(V , cctx(V |-> taddr(T , _) ENV , _)) => T

    rule #type(I:Int, CTX) => intword(#byteWidth(I))
    rule #type(tt, CTX) => bool
    rule #type(ff, CTX) => bool
    rule #type(B1 | B2, CTX) => bool requires #type(B1, CTX) ==K bool andBool #type(B2, CTX) ==K bool
    rule #type(B1 & B2, CTX) => bool requires #type(B1, CTX) ==K bool andBool #type(B2, CTX) ==K bool

    rule #type(A1 == A2, CTX) => bool requires #type(A1, CTX) ==K #type(A2, CTX)
    rule #type(A1 =/= A2, CTX) => bool requires #type(A1, CTX) ==K #type(A2, CTX)
    rule #type(A1 < A2, CTX) => bool requires #type(A1, CTX) ==K #type(A2, CTX)
    rule #type(A1 <= A2, CTX) => bool requires #type(A1, CTX) ==K #type(A2, CTX)
    rule #type(A1 > A2, CTX) => bool requires #type(A1, CTX) ==K #type(A2, CTX)
    rule #type(A1 >= A2, CTX) => bool requires #type(A1, CTX) ==K #type(A2, CTX)
```

Variables: Declaration, Lookup, and Assignment
----------------------------------------------

-   A `Var` is an `Id` with an `ABIType` (used for declaring variables).
-   `Vars` are lists of `Id` (builtin to K), separated by `;`.

```{.k .uiuck .rvk}
    syntax Var  ::= "(" Id ":" ABIType ")"
    syntax Vars ::= List{Var, ";"}
 // ------------------------------
```

-   `#env` is used to calculate the correct memory locations to access for variables given the list of currently scoped variables.

TODO (high): Add width calculations for remaining types.

```{.k .uiuck .rvk}
    syntax Int ::= #width ( ABIType ) [function]
 // --------------------------------------------
    rule #width( uintword ( N ) ) => N
    rule #width( T [ N ] ) => #width(T) *Int N

    rule #width( intword ( N ) ) => N
    rule #width( ufixedword ( N , M ) ) => N
    rule #width( fixedword ( N , M ) ) => N

    rule #width( bool ) => 1 // bools have 1 byte
    rule #width( address ) => 20

    rule #width( bytes ( N ) ) => N
```

-   `scope (_) {_}` declares new variables in scope for the environment (note that new variables shadow existing ones).
-   `#updateScopeMap` updates the variables to typed addresses mapping for the current scope.

```{.k .uiuck .rvk}
    syntax PrimeOp ::= "scope" "(" Vars ")" "{" OpCodes "}"
 // -------------------------------------------------------
    rule #resolvePrimeOp( CTX , scope ( IDS2 ) { OPS } ) => #resolvePrimeOps(#updateScopeMap(CTX , IDS2) , OPS)

    syntax CompileCtx ::= #updateScopeMap ( CompileCtx, Vars ) [function]
 // ---------------------------------------------------------------------
    rule #updateScopeMap( CTX , .Vars ) => CTX
    rule #updateScopeMap( cctx(ENV , FREEADDR:Int) , ( V : T ) ; VS ) => #updateScopeMap(cctx(ENV [ V <- taddr(T , FREEADDR) ] , FREEADDR +Int #width(T)) , VS)
```

-   `mload` loads variables from the `localMem` onto the `wordStack` (using the environment to determine where they are).
-   `mstore` stores an element from the `wordStack` from the location specified in the `localMem`.

TODO (mid): `mload` and `mstore` now need to do different things based on the type of the variables.
Perhaps they should call the ABI decoding/encoding functions (respectively) so that when we store a bunch of types to memory we know it's correctly ABI packed.

```{.k .uiuck .rvk}
    syntax PrimeOp ::= mload ( Id ) | mstore ( Id )
 // -----------------------------------------------
    rule #resolvePrimeOp( cctx(V |-> taddr(_ , LOC) ENV , _ ) , mload(V) )  => push(LOC) ; MLOAD  ; .OpCodes
    rule #resolvePrimeOp( cctx(V |-> taddr(_ , LOC) ENV , _ ) , mstore(V) ) => push(LOC) ; MSTORE ; .OpCodes
```

-   Syntax `_:=_` is sugar for storing the result of an exprssion to the `localMem`.
TODO (mid): add type check.

```{.k .uiuck .rvk}
    syntax PrimeOp ::= Id ":=" ExpOp
 // --------------------------------
    rule #resolvePrimeOp( CTX , V := E ) => #resolvePrimeOps(CTX , E ; mstore(V) ; .OpCodes)
```

### Example

In this example, we use `scope` to declare some variables and use them with `mload` and `mstore`.

```{.k .example}
load "exec" : { "code" : scope((s : uintword(32)) ; (n : uintword(32)))
                            { push(0)  ; mstore(s)
                            ; push(10) ; mstore(n)
                            ; jumpdest("loop-begin")
                            ; push(0) ; mload(n) ; GT
                            ; ISZERO ; jumpi("end")
                            ; mload(n) ; mload(s) ; ADD ; mstore(s)
                            ; push(1)  ; mload(n) ; SUB ; mstore(n)
                            ; jump("loop-begin")
                            ; jumpdest("end")
                            ; mload(s) ; push(0) ; SSTORE
                            ; .OpCodes
                            }
                       ; .OpCodes
              }

compile

check "program" : PUSH(1, 0)  ; PUSH(1, 0)  ; MSTORE
                ; PUSH(1, 10) ; PUSH(1, 32) ; MSTORE
                ; JUMPDEST
                ; PUSH(1, 0) ; PUSH(1, 32) ; MLOAD ; GT
                ; ISZERO ; PUSH(1, 43) ; JUMPI
                ; PUSH(1, 32) ; MLOAD ; PUSH(1, 0)  ; MLOAD ; ADD ; PUSH(1, 0)  ; MSTORE
                ; PUSH(1, 1)          ; PUSH(1, 32) ; MLOAD ; SUB ; PUSH(1, 32) ; MSTORE
                ; PUSH(1, 10) ; JUMP
                ; JUMPDEST
                ; PUSH(1, 0) ; MLOAD ; PUSH(1, 0) ; SSTORE
                ; .OpCodes

failure "DESUGAR EVMPRIME MLOAD/MSTORE"

clear
```

Here is another example which uses nested scope and shadowing semantics.

```{.k .example}
load "exec" : { "code" : scope((s : uintword(32)) ; (n : uintword(32)))
                            { push(0)  ; mstore(s)
                            ; push(10) ; mstore(n)
                            ; mload(n) ; mload(s) ; ADD ; mstore(s)
                            ; scope((s : uintword(32)))
                                 { push(1)  ; mstore(s)
                                 ; mload(n) ; mload(s) ; ADD ; mstore(s)
                                 ; .OpCodes
                                 }
                            ; push(1)  ; mload(s) ; SUB ; mstore(s)
                            ; .OpCodes
                            }
                       ; .OpCodes
              }

compile

check "program" : PUSH(1, 0)  ; PUSH(1, 0)  ; MSTORE
                ; PUSH(1, 10) ; PUSH(1, 32) ; MSTORE
                ; PUSH(1, 32) ; MLOAD ; PUSH(1, 0)  ; MLOAD ; ADD ; PUSH(1, 0)  ; MSTORE
                ; PUSH(1, 1)  ; PUSH(1, 64)  ; MSTORE
                ; PUSH(1, 32) ; MLOAD ; PUSH(1, 64)  ; MLOAD ; ADD ; PUSH(1, 64)  ; MSTORE
                ; PUSH(1, 1)          ; PUSH(1, 0)   ; MLOAD ; SUB ; PUSH(1, 0)   ; MSTORE
                ; .OpCodes

failure "DESUGAR EVMPRIME NESTED SCOPE"

clear
```

Expressions
-----------

-   `Id` is subsorted into `PrimeOp` so and is interpereted as a variable lookup.
-   `Int` is subsorted into `PrimeOp` and means pushing a constant.
-   `tt`, `ff` are the constants for true and false in boolean expressions.

```{.k .uiuck .rvk}
    syntax PrimeOp ::= ExpOp
    syntax ExpOp   ::= Int | "tt" | "ff" | Id
 // ----------------------------------
    rule #resolvePrimeOp(CTX, V:Id)  => #resolvePrimeOp(CTX, mload(V))
    rule #resolvePrimeOp(CTX, C:Int) => push(C) ; .OpCodes
```

-   `_+_`, `_*_`, `_-_`, and `_/_` provide integer arithmetic expressions.

```{.k .uiuck .rvk}
    syntax ExpOp ::= ExpOp "*" ExpOp
                   | ExpOp "/" ExpOp
                   > ExpOp "+" ExpOp
                   | ExpOp "-" ExpOp
 // -----------------------------------
    rule #resolvePrimeOp( CTX , W0 + W1 ) => #resolvePrimeOps(CTX , W1 ; W0 ; ADD ; .OpCodes)
    rule #resolvePrimeOp( CTX , W0 - W1 ) => #resolvePrimeOps(CTX , W1 ; W0 ; SUB ; .OpCodes)
    rule #resolvePrimeOp( CTX , W0 * W1 ) => #resolvePrimeOps(CTX , W1 ; W0 ; MUL ; .OpCodes)
    rule #resolvePrimeOp( CTX , W0 / W1 ) => #resolvePrimeOps(CTX , W1 ; W0 ; DIV ; .OpCodes)
```

-   `tt`, `ff` are the constants for true and false in boolean expressions.
-   `!_` is negation, `_|_` is disjunction, and `_&_` is conjunction.

```{.k .uiuck .rvk}
    syntax ExpOp ::= "!" ExpOp
                   | ExpOp "|" ExpOp
                   | ExpOp "&" ExpOp
 // -----------------------------------
```

-   `_==_`, `_=/=_`, `_<_`, `_<=_`, `_>_`, and `_>=_` provide comparison operations over arithmetic expressions.

```{.k .uiuck .rvk}
    syntax ExpOp ::= ExpOp "=="  ExpOp
                   | ExpOp "=/=" ExpOp
                   | ExpOp "<"   ExpOp
                   | ExpOp "<="  ExpOp
                   | ExpOp ">"   ExpOp
                   | ExpOp ">="  ExpOp
 // -------------------------------------
    rule #resolvePrimeOp( CTX , W0 ==  W1 ) => #resolvePrimeOps(CTX , W1 ; W0 ; EQ           ; .OpCodes)
    rule #resolvePrimeOp( CTX , W0 =/= W1 ) => #resolvePrimeOps(CTX , W1 ; W0 ; EQ ; ISZERO  ; .OpCodes)
    rule #resolvePrimeOp( CTX , W0 <   W1 ) => #resolvePrimeOps(CTX , W1 ; W0 ; LT           ; .OpCodes)
    rule #resolvePrimeOp( CTX , W0 <=  W1 ) => #resolvePrimeOps(CTX , W1 ; W0 ; GT ; ISZERO  ; .OpCodes)
    rule #resolvePrimeOp( CTX , W0 >   W1 ) => #resolvePrimeOps(CTX , W1 ; W0 ; GT           ; .OpCodes)
    rule #resolvePrimeOp( CTX , W0 >=  W1 ) => #resolvePrimeOps(CTX , W1 ; W0 ; LT ; ISZERO  ; .OpCodes)
```

### Example

In this example, we use the above expression language and assignment (`_:=_`) to simplify many parts of the code.

```{.k .example}
load "exec" : { "code" : scope((s : uintword(32)) ; (n : uintword(32)))
                            { s := 0
                            ; n := 10
                            ; jumpdest("loop-begin")
                            ; n > 0
                            ; ISZERO ; jumpi("end")
                            ; s := s + n
                            ; n := n - 1
                            ; jump("loop-begin")
                            ; jumpdest("end")
                            ; mload(s) ; push(0) ; SSTORE
                            ; .OpCodes
                            }
                       ; .OpCodes
              }

compile

check "program" : PUSH(1, 0)  ; PUSH(1, 0)  ; MSTORE
                ; PUSH(1, 10) ; PUSH(1, 32) ; MSTORE
                ; JUMPDEST
                ; PUSH(1, 0) ; PUSH(1, 32) ; MLOAD ; GT
                ; ISZERO ; PUSH(1, 43) ; JUMPI
                ; PUSH(1, 32) ; MLOAD ; PUSH(1, 0)  ; MLOAD ; ADD ; PUSH(1, 0)  ; MSTORE
                ; PUSH(1, 1)          ; PUSH(1, 32) ; MLOAD ; SUB ; PUSH(1, 32) ; MSTORE
                ; PUSH(1, 10) ; JUMP
                ; JUMPDEST
                ; PUSH(1, 0) ; MLOAD ; PUSH(1, 0) ; SSTORE
                ; .OpCodes

failure "DESUGAR EVMPRIME EXPRESSIONS"

clear
```

Conditionals
------------

-   `if (_) {_}` allows for conditionally executing a piece of code.
-   `if (_) {_} else {_}` allows for a nicer looking branching structure than writing bare EVM.

```{.k .uiuck .rvk}
    syntax PrimeOp ::= "if" "(" ExpOp ")" "{" OpCodes "}"
 // -----------------------------------------------------
    rule #resolvePrimeOp( CTX , if ( COND ) { THEN } )
      =>             #resolvePrimeOp(CTX , COND)
         ++OpCodes ( ISZERO
                 ;   jumpi( #ifThenLabel(!LABEL:Int) +String "_end" )
                 ; ( #resolvePrimeOps(CTX , THEN)
         ++OpCodes ( jumpdest( #ifThenLabel(!LABEL) +String "_end" )
                 ;   .OpCodes
               )))

    syntax PrimeOp ::= "if" "(" ExpOp ")" "then" "{" OpCodes "}" "else" "{" OpCodes "}"
 // -----------------------------------------------------------------------------------
    rule #resolvePrimeOp( CTX , if ( COND ) then { THEN } else { ELSE } )
      =>             #resolvePrimeOp(CTX , COND)
         ++OpCodes ( jumpi(#ifThenElseLabel(!LABEL:Int) +String "_true")
                 ; ( #resolvePrimeOps(CTX , ELSE)
         ++OpCodes ( jump(#ifThenElseLabel(!LABEL) +String "_end")
                 ;   jumpdest(#ifThenElseLabel(!LABEL) +String "_true")
                 ; ( #resolvePrimeOps(CTX , THEN)
         ++OpCodes ( jumpdest(#ifThenElseLabel(!LABEL) +String "_end")
                 ;   .OpCodes
             )))))

    syntax String ::= #ifThenLabel     ( Int ) [function]
                    | #ifThenElseLabel ( Int ) [function]
 // -----------------------------------------------------
    rule #ifThenLabel( N )     => "if_then_-" +String Int2String(N)
    rule #ifThenElseLabel( N ) => "if_then_else_-" +String Int2String(N)
```

### Example

In this example, we use a conditional to help with jumping back to the loop head.

```{.k .example}
load "exec" : { "code" : scope((s : uintword(32)) ; (n : uintword(32)))
                            { s := 0
                            ; n := 10
                            ; jumpdest("loop-begin")
                            ; if ( n > 0 )
                                { s := s + n
                                ; n := n - 1
                                ; jump("loop-begin")
                                ; .OpCodes
                                }
                            ; mload(s) ; push(0) ; SSTORE
                            ; .OpCodes
                            }
                       ; .OpCodes
              }

compile

check "program" : PUSH(1, 0)  ; PUSH(1, 0)  ; MSTORE
                ; PUSH(1, 10) ; PUSH(1, 32) ; MSTORE
                ; JUMPDEST
                ; PUSH(1, 0) ; PUSH(1, 32) ; MLOAD ; GT
                ; ISZERO ; PUSH(1, 43) ; JUMPI
                ; PUSH(1, 32) ; MLOAD ; PUSH(1, 0)  ; MLOAD ; ADD ; PUSH(1, 0)  ; MSTORE
                ; PUSH(1, 1)          ; PUSH(1, 32) ; MLOAD ; SUB ; PUSH(1, 32) ; MSTORE
                ; PUSH(1, 10) ; JUMP
                ; JUMPDEST
                ; PUSH(1, 0) ; MLOAD ; PUSH(1, 0) ; SSTORE
                ; .OpCodes

failure "DESUGAR EVMPRIME IFTHEN"

clear
```

While Loops
-----------

-   `while (_) {_}` allows for simpler construction of loops.

```{.k .uiuck .rvk}
    syntax PrimeOp ::= "while" "(" ExpOp ")" "{" OpCodes "}"
 // --------------------------------------------------------
    rule #resolvePrimeOp( CTX , while ( COND ) { BODY } )
      =>   jumpdest( #whileLabel(!LABEL:Int) +String "_begin" )
         ; #resolvePrimeOp( CTX
                          , if ( COND ) {             BODY
                                          ++OpCodes ( jump( #whileLabel(!LABEL) +String "_begin" )
                                                    ; .OpCodes
                                                    )
                                        }
                          )

    syntax String ::= #whileLabel ( Int ) [function]
 // ------------------------------------------------
    rule #whileLabel( N ) => "while__-" +String Int2String(N)
endmodule
```

### Example

In this example, we use a while loop instead for the entire loop (becoming a highly readable program).

```{.k .example}
load "exec" : { "code" : scope((s : uintword(32)) ; (n : uintword(32)))
                            { s := 0
                            ; n := 10
                            ; while ( n > 0 )
                                { s := s + n
                                ; n := n - 1
                                ; .OpCodes
                                }
                            ; mload(s) ; push(0) ; SSTORE
                            ; .OpCodes
                            }
                       ; .OpCodes
              }

compile

check "program" : PUSH(1, 0)  ; PUSH(1, 0)  ; MSTORE
                ; PUSH(1, 10) ; PUSH(1, 32) ; MSTORE
                ; JUMPDEST
                ; PUSH(1, 0) ; PUSH(1, 32) ; MLOAD ; GT
                ; ISZERO ; PUSH(1, 43) ; JUMPI
                ; PUSH(1, 32) ; MLOAD ; PUSH(1, 0)  ; MLOAD ; ADD ; PUSH(1, 0)  ; MSTORE
                ; PUSH(1, 1)          ; PUSH(1, 32) ; MLOAD ; SUB ; PUSH(1, 32) ; MSTORE
                ; PUSH(1, 10) ; JUMP
                ; JUMPDEST
                ; PUSH(1, 0) ; MLOAD ; PUSH(1, 0) ; SSTORE
                ; .OpCodes

failure "DESUGAR EVMPRIME WHILE"

clear

success

.EthereumSimulation
```
