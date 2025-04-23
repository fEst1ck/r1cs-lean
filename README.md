# README

We show how to verify in Lean a simple circuit `IsEqual` testing equality of two signals, see `example.circom`.

We define our R1CS format and its semantics in `R1CS/R1CS.lean`, then verify the example circuit in `R1CS/Example.lean`.

## Build

```bash
lake update
lake build
```