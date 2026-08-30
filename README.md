## amlc - applied meta lang compiler

a local compiler, verifier, debugger, and OCTB (octra exec package bytecode format) scanner, it's a pure compiler, it doesn't contain node code or other tools, representing a pure functional implementation of a virtual machine.

> this compiler version is a preview release and doesn't contain full documentation (we'll add it soon), but the core is already open for research and experimentation, examples with usage examples have been added for convenience.

## build amlc

```shell
opam switch create . 4.14.2
eval "$(opam env)"
opam install . --deps-only
sh scripts/build.sh
```
the bin is `_build/install/default/bin/amlc`.

## Use
for your convenience, we have prepared a series of in-depth examples of calls with available capabilities:
```shell
AMLC=_build/install/default/bin/amlc
mkdir -p runtime_data

$AMLC version
$AMLC feed examples/feed_result.aml examples/feed_result.val \
  --out runtime_data/feed-result.af1
$AMLC check examples/feed_result.aml \
  --feed runtime_data/feed-result.af1
$AMLC compile examples/feed_result.aml \
  --feed runtime_data/feed-result.af1 \
  --out runtime_data/feed-result.octb
$AMLC run examples/feed_result.aml \
  --feed runtime_data/feed-result.af1
$AMLC debug examples/feed_result.aml \
  --feed runtime_data/feed-result.af1 --expect i:42
$AMLC check examples/orbit.aml
$AMLC compile examples/shape.aml --out runtime_data/shape.octb
$AMLC test examples/forms.aml
$AMLC run examples/shape.aml
$AMLC debug examples/orbit.aml --expect i:9
$AMLC check examples/result.amlp
$AMLC compile examples/result.amlp --out runtime_data/result
$AMLC test examples/result.amlp
$AMLC run examples/result.amlp --root main
$AMLC run examples/project.amlp --root arithmetic
$AMLC debug examples/project.amlp --root forms --expect i:23
$AMLC run examples/project.amlp --root orbit
$AMLC debug examples/project.amlp --root shape --expect i:7
$AMLC run examples/project.amlp --root feed
$AMLC debug examples/project.amlp --root feed --expect i:42
$AMLC run runtime_data/result/project.cf1 --root main
$AMLC run runtime_data/result/main.octb
$AMLC debug examples/result.amlp --root main
$AMLC dump runtime_data/result/main.octb
$AMLC dump runtime_data/result/main.octb --format events
$AMLC dump runtime_data/result/main.octb --format dot
$AMLC check examples/contract.aml
$AMLC compile examples/contract.aml \
  --out runtime_data/contract.octb
$AMLC test examples/contract.aml
$AMLC dump runtime_data/contract.octb
$AMLC run examples/contract.aml \
  --method arithmetic --arg 4 --arg 7
$AMLC debug examples/storage.aml \
  --method write --arg beta
$AMLC check runtime_data/contract.octb
$AMLC test runtime_data/contract.octb
$AMLC run runtime_data/contract.octb \
  --method arithmetic --arg int:4 --arg int:7
$AMLC debug runtime_data/contract.octb \
  --method arithmetic --arg int:4 --arg int:7
```

## verify
```shell
sh scripts/prove.sh
```
> fyi: script `prove.sh` runs Coq proofs and checks 73 modules, requiring several conditions to be met (no axioms, no type intype, no unsafe co  fixpoints, no assumed positivity), also note that the proofs cover the formal model in `formal/`, not the OCaml in `lib/`.