set -eu

root=$(CDPATH= cd -- "$(dirname "$0")/.." && pwd)

opam exec -- dune build --root "$root" @install

binary="$root/_build/install/default/bin/amlc"
if [ ! -x "$binary" ]; then
  printf 'amlc_build = fail reason = binary_absent\n' >&2
  exit 1
fi

printf 'amlc_build = pass binary = %s\n' "$binary"