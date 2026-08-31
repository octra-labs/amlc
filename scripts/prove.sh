set -eu

root=$(CDPATH= cd -- "$(dirname "$0")/.." && pwd)
work="$root/runtime_data/proof-$$"

trap 'rm -rf "$work"' EXIT
mkdir -p "$work"
cp "$root"/formal/*.v "$work"

version=$(coqc --print-version)
if [ "$version" != "9.0.0 4.14.2" ]; then
  printf 'amlc_proof = fail reason = tool_version actual = %s\n' "$version" >&2
  exit 1
fi

if grep -En '(^|[^[:alnum:]_])(Admitted|Axiom|Parameter|Conjecture|admit)([^[:alnum:]_]|$)' "$work"/*.v; then
  printf 'amlc_proof = fail reason = unchecked_claim\n' >&2
  exit 1
fi

(
  cd "$work"
  set -- Fp Lpn Iwork Uni Surf Fin Dec DecRel DecComp DecSound Fuel Lim Rule Proj Pack Bin Ser Pimg Low Fun Data Rift Rec Quant Weave Braid Loom Cmp Orbit Wake Idx Law Raw Norm Rnom Spec Poly Perm Fhe Hop Hfhe Graph Ent Param Crypt Hpar Sess Sbin Pbin Cert Scert Prof Text Lex Read Comp Src Seal Sha Root Host Ciph Turn Feed Rval Emit Trace Mach Smap Live Path Folio Dbg Dbin
  for unit in "$@"; do
    coqc -q "$unit.v"
  done
  coqc -q Iextract.v
  coqc -q Extract.v
  proof_ctx=$(coqchk -silent -o "$@" 2>&1)
  for claim in \
    '* Axioms: <none>' \
    '* Constants/Inductives relying on type-in-type: <none>' \
    '* Constants/Inductives relying on unsafe (co)fixpoints: <none>' \
    '* Inductives whose positivity is assumed: <none>'
  do
    if ! printf '%s\n' "$proof_ctx" | grep -Fqx "$claim"; then
      printf 'amlc_proof = fail reason = proof_context\n' >&2
      exit 1
    fi
  done
  sources=$(find . -type f -name '*.v' | wc -l | tr -d ' ')
  printf 'amlc_proof = pass sources = %s units = %s axioms = 0 type_in_type = 0 unsafe_fix = 0 positivity = 0\n' "$sources" "$#"
)