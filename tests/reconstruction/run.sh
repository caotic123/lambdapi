#!/bin/bash
# Runs the examples of the reconstruction pipeline (why3 → CVC5 → Carcara →
# Lambdapi) and compares the outcome of every why3 call with expected.txt.
# See README.md.

usage() {
    cat <<-EOF
	Usage: tests/reconstruction/run.sh [-u|--update] [FILE.lp...]

	Checks each FILE (default: every .lp file of tests/reconstruction) with
	"lambdapi check --experimental-smt-proofs --debug=h", prints the outcome of
	each why3 call, and compares it with expected.txt.

	  -u, --update   write the outcomes to expected.txt instead of comparing.

	Environment (defaults in brackets):
	  LAMBDAPI     lambdapi binary [_build/install/default/bin/lambdapi]
	  CARCARA_DIR  checkout of NotBad4U/carcara, branch lambdapi-refactor
	               [\$HOME/Workspace/carcara-lambdapi]
	  CARCARA      carcara binary with "translate lambdapi"
	               [\$CARCARA_DIR/target/release/carcara]
	  ALETHE       Carcara's Lambdapi library [\$CARCARA_DIR/alethe-lp]
	  STDLIB       checkout of lambdapi-stdlib, mapped as Stdlib; empty if it is
	               installed in the library root [\$HOME/Workspace/lambdapi-stdlib]
	  OUT          logs and reports [\${TMPDIR:-/tmp}/lambdapi-reconstruction]

	Exit status: 0 if the outcomes are the expected ones, 1 otherwise.
	EOF
}

set -u

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(cd "$here/../.." && pwd)"

LAMBDAPI="${LAMBDAPI:-$repo/_build/install/default/bin/lambdapi}"
CARCARA_DIR="${CARCARA_DIR:-$HOME/Workspace/carcara-lambdapi}"
CARCARA="${CARCARA:-$CARCARA_DIR/target/release/carcara}"
ALETHE="${ALETHE:-$CARCARA_DIR/alethe-lp}"
STDLIB="${STDLIB-$HOME/Workspace/lambdapi-stdlib}"
OUT="${OUT:-${TMPDIR:-/tmp}/lambdapi-reconstruction}"

update=""
files=()
while [ $# -gt 0 ]; do
    case "$1" in
        -h | --help) usage; exit 0 ;;
        -u | --update) update=1 ;;
        -*) echo "invalid option: $1"; echo; usage; exit 2 ;;
        *)
            [ -f "$1" ] || { echo "error: no file $1" >&2; exit 2; }
            files+=("$(realpath --relative-to="$here" "$1")")
            ;;
    esac
    shift
done
if [ ${#files[@]} -eq 0 ]; then
    mapfile -t files < <(cd "$here" && find . -name '*.lp' | sed 's|^\./||' | sort)
fi

die() { echo "error: $*" >&2; exit 2; }

# Tools.
[ -x "$LAMBDAPI" ] || die "no lambdapi at $LAMBDAPI (run dune build, or set LAMBDAPI)"
lambdapi_bin="$(readlink -f "$LAMBDAPI")"
"$CARCARA" translate --help 2>/dev/null | grep -q lambdapi \
    || die "$CARCARA has no \"translate lambdapi\" (set CARCARA_DIR or CARCARA)"
[ -f "$ALETHE/lambdapi.pkg" ] || die "no Carcara library at $ALETHE (set ALETHE)"
maps=("--map-dir=alethe:$ALETHE")
if [ -n "$STDLIB" ]; then
    [ -f "$STDLIB/lambdapi.pkg" ] || die "no Stdlib at $STDLIB (set STDLIB)"
    maps+=("--map-dir=Stdlib:$STDLIB")
fi

mkdir -p "$OUT/logs" "$OUT/lib"

# Object files written by another lambdapi binary cannot be loaded ("is
# incompatible with current binary"): remove the ones older than the binary.
for d in "$ALETHE" ${STDLIB:+"$STDLIB"} "$repo/tests/OK"; do
    n=$(find "$d" -name '*.lpo' ! -newer "$lambdapi_bin" -print -delete | wc -l)
    [ "$n" -gt 0 ] && echo "removed $n stale .lpo files in $d"
done

# Compile the modules of Carcara's library that the examples use, each in its
# own process (see alethe-lp/README.md).
printf 'package_name = reconstruction_lib\nroot_path = reconstruction_lib\n' \
    > "$OUT/lib/lambdapi.pkg"
for m in core prop rare.prop quant; do
    echo "require alethe.$m;" > "$OUT/lib/$m.lp"
    "$LAMBDAPI" check -c -v 0 -w "${maps[@]}" "$OUT/lib/$m.lp" \
        > "$OUT/lib/$m.log" 2>&1 \
        || die "alethe.$m does not compile, see $OUT/lib/$m.log"
done

# [outcomes FILE LOG] prints one line per why3 call of FILE, read from the log
# LOG of its check: FILE, the symbol whose proof makes the call, and the
# outcome.
outcomes() {
    awk -v file="$1" '
    function line_of(s) {
        return match(s, /:[0-9]+:[0-9]/) ? substr(s, RSTART + 1, RLENGTH - 3) + 0 : 0
    }
    function after(s, prefix) {
        return index(s, prefix) ? substr(s, index(s, prefix) + length(prefix)) : s
    }
    function holes_of(s) {
        match(s, /with [0-9]+ holes/)
        return substr(s, RSTART + 5, RLENGTH - 11)
    }
    # The source: the why3 calls, and the last symbol declared before each.
    FNR == NR {
        s = $0; sub(/\/\/.*/, "", s)
        if (match(s, /symbol[ \t]+[^ \t(:]+/)) {
            sym = substr(s, RSTART, RLENGTH); sub(/symbol[ \t]+/, "", sym)
        }
        if (s ~ /(^|[^A-Za-z0-9_])why3([^A-Za-z0-9_]|$)/) {
            calls[++n] = FNR; name[FNR] = sym
        }
        next
    }
    # The log. Errors are printed in red.
    {
        red = ($0 ~ /^\033\[31m/)
        gsub(/\033\[[0-9;]*m/, "")
        L = line_of($0)
    }
    /^\[carc\] .* translated \(strict\) in / { mode[L] = "strict" }
    /^\[carc\] .* translated \(--admit-unsupported/ {
        r = after($0, "strict failed: "); sub(/\) in \/.*/, "", r)
        if (match(r, /rule `[^`]*`/)) r = substr(r, RSTART + 6, RLENGTH - 7)
        else gsub(/ /, "_", r)
        mode[L] = "admit=" r
    }
    /^\[carc\] .* reconstruction with [0-9]+ holes/ {
        kind = ($0 ~ /\(other builtins\)$/) ? "foreign" : "reconstructed"
        res[L] = kind " holes=" holes_of($0)
    }
    /Carcara: no translation/ {
        res[L] = "no-translation: " after($0, "): ")
    }
    /Carcara: the translation cannot be loaded: / {
        res[L] = "not-loaded: " after($0, "loaded: ")
    }
    red && /Uncaught exception:/ {
        crash = after($0, "Uncaught exception:"); sub(/^ +/, "", crash)
        if (crash ~ /:$/ && (getline nxt) > 0) {
            gsub(/\033\[[0-9;]*m/, "", nxt); sub(/^ +/, "", nxt)
            crash = crash " " nxt
        }
        next
    }
    red && L {
        msg = $0; sub(/^\[[^]]*\] */, "", msg)
        if (L in name) fatal[L] = msg; else other = msg
    }
    END {
        for (i = 1; i <= n; i++) {
            L = calls[i]
            if (L in res) {
                out = res[L]
                if (index(mode[L], "admit=") == 1) out = out " " mode[L]
            }
            else if (L in fatal) out = "error: " fatal[L]
            else if (crash != "" && !crash_used) { out = "crash: " crash; crash_used = 1 }
            else out = "not-reached"
            printf "%-22s %-14s %s\n", file, name[L], out
        }
        if (other != "") printf "%-22s %-14s %s\n", file, "-", "error: " other
        if (crash != "" && !crash_used) printf "%-22s %-14s %s\n", file, "-", "crash: " crash
    }' "$here/$1" "$2"
}

summary="$OUT/summary.txt"
: > "$summary"
logs=()
for f in "${files[@]}"; do
    log="$OUT/logs/${f//\//_}.log"
    logs+=("$log")
    printf '%s ' "$f"
    start=$(date +%s)
    (cd "$here" && "$LAMBDAPI" check -v 1 --debug=h --experimental-smt-proofs \
        --carcara "$CARCARA" "${maps[@]}" "$f") > "$log" 2>&1
    echo "(exit $?, $(( $(date +%s) - start ))s)"
    outcomes "$f" "$log" >> "$summary"
done

echo
cat "$summary"
echo
awk '
    { total++ }
    / reconstructed / { rec++ }
    / admit=/ { adm++ }
    / foreign / { frg++ }
    match($0, /holes=[0-9]+/) { holes += substr($0, RSTART + 6, RLENGTH - 6) }
    / (no-translation|not-loaded): / { fail++ }
    / error: / { err++ }
    / crash: / { crash++ }
    / not-reached$/ { nr++ }
    END {
        printf "%d why3 calls: %d reconstructed (%d with --admit-unsupported), ", \
            total, rec, adm
        printf "%d foreign, %d holes in all; ", frg, holes
        printf "%d not translated/loaded, %d errors, %d crashes, %d not reached\n", \
            fail, err, crash, nr
    }' "$summary"

# The Alethe rules of the translated proofs.
sed 's/\x1b\[[0-9;]*m//g' "${logs[@]}" | grep '^\[carc\] .* translated (' \
    | grep -oE '\) in /[^ ]+$' | sed 's|^) in ||' \
    | sort -u \
    | while read -r d; do
        grep -oE ':rule [^ )]+' "$d/proof.alethe" | sed 's/:rule //'
        grep -oE ':rule rare_rewrite :args \("?[^ ")]+' "$d/proof.alethe" \
            | sed 's/.*(//; s/"//g; s/^/rare_rewrite:/'
    done | grep -v '^rare_rewrite$' | sort | uniq -c | sort -rn > "$OUT/rules.txt"
echo "Alethe rules in the translated proofs (see $OUT/rules.txt):"
awk '{ printf "%s%s %s", (NR > 1 ? ", " : "  "), $2, $1 } END { print "" }' \
    "$OUT/rules.txt" | fold -s -w 78
echo "Logs: $OUT/logs"

# Comparison with the expected outcomes of the same files.
expected="$here/expected.txt"
selected() { awk 'NR == FNR { f[$0]; next } $1 in f' <(printf '%s\n' "${files[@]}") "$1"; }
if [ -n "$update" ]; then
    { [ -f "$expected" ] && awk 'NR == FNR { f[$0]; next } !($1 in f)' \
          <(printf '%s\n' "${files[@]}") "$expected"
      cat "$summary"; } | sort -s -k1,1 > "$expected.new"
    mv "$expected.new" "$expected"
    echo "Updated $expected."
elif [ ! -f "$expected" ]; then
    echo "No $expected: run with --update to create it."; exit 1
elif diff -u --label expected <(selected "$expected") --label actual \
        <(sort -s -k1,1 "$summary") > "$OUT/diff.txt"; then
    echo "Outcomes as expected."
else
    echo; echo "Outcomes differ from expected.txt:"; cat "$OUT/diff.txt"; exit 1
fi
