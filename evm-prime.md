EVM Prime
=========

In `EVMPRIME` mode, certain opcodes can be used which compile down to standard EVM but provide better-behaved high-level language constructs.

```{.k .uiuck .rvk}
requires "evm.k"

module EVM-PRIME
    imports EVM

    syntax OpCode ::= PrimeOp
 // -------------------------

    syntax Bool ::= isCompiled ( OpCodes ) [function]
 // -------------------------------------------------
    rule isCompiled ( .OpCodes ) => true
    rule isCompiled ( OP ; OPS ) => (notBool isPrimeOp(OP)) andBool isCompiled(OPS)
```

-   `Vars` are lists of `Id` (builtin to K), separated by `:`.
-   `#env` is used to calculate the correct memory locations to access for variables given the list of currently scoped variables.

```{.k .uiuck .rvk}
    syntax Vars ::= List{Id, ":"}
 // -----------------------------

    syntax Int ::= #env ( Vars , Id ) [function]
 // --------------------------------------------
    rule #env( (V : _)  , V ) => 0
    rule #env( (V : VS) , X ) => 32 +Int #env( VS , X ) requires X =/=K V
```

-   `#resolvePrimeOp` and `#resolvePrimeOps` operate in the monad from `(ENV, OpCode) -> OpCodes`.

```{.k .uiuck .rvk}
    syntax OpCodes ::= #resolvePrimeOp  ( Vars , OpCode  ) [function]
                     | #resolvePrimeOps ( Vars , OpCodes ) [function]
 // -----------------------------------------------------------------
    rule #resolvePrimeOp( IDS, OP ) => OP ; .OpCodes requires notBool isPrimeOp(OP)

    rule #resolvePrimeOps( _,   .OpCodes ) => .OpCodes
    rule #resolvePrimeOps( IDS, OP ; OPS ) => #resolvePrimeOp(IDS, OP) ++OpCodes #resolvePrimeOps(IDS, OPS)

    syntax OpCodes ::= OpCodes "++OpCodes" OpCodes [function]
 // ---------------------------------------------------------
    rule .OpCodes    ++OpCodes OPS  => OPS
    rule (OP ; OPS1) ++OpCodes OPS2 => OP ; (OPS1 ++OpCodes OPS2)
```

-   `#compile` will desugar `PrimeOp`s with `#resolvePrimeOps` and then resolve the jump destinations with `#resolveJumps`.

```{.k .uiuck .rvk}
    syntax OpCodes ::= #compile ( OpCodes ) [function]
 // --------------------------------------------------
    rule #compile(OPS) => #resolveJumps(#resolvePrimeOps(.Vars, OPS))
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

-   `push` allows not specifying the width of the constant being pushed (it will be calculated for you).

```{.k .uiuck .rvk}
    syntax PrimeOp ::= push ( Int ) [function]
 // ------------------------------------------
    rule push(N) => PUSH(#sizeWordStack(#padToWidth(1, #asByteStack(N))), N) requires N <Int pow256
endmodule
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
