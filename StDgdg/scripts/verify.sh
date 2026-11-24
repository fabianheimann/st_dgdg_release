#!/usr/bin/env bash
# Verify the formalisation: build everything, reject proof holes and additional axioms.
#
#   lake exe cache get     # once, to download the compiled Mathlib
#   ./scripts/verify.sh
set -euo pipefail
cd "$(dirname -- "$0")/.."

echo "== building all modules"
lake build

echo "== checking for proof holes and declared axioms"
if grep -rnE '\bsorry\b|^\s*axiom\b|native_decide' StDgdg StDgdg.lean; then
  echo "FAILED: found sorry / axiom / native_decide" >&2
  exit 1
fi

echo "== checking the axioms of the main results and of the validation examples"
exports=(
  StDgdg.ExpWeight.inf_sup
  StDgdg.ExpWeight.inf_sup_product
  StDgdg.ExpWeight.unique_solvability
  StDgdg.Setting.CU_mc
  StDgdg.Setting.continuity
  StDgdg.ExpWeight.strang
  StDgdg.ErrorData.approx_D
  StDgdg.ErrorData.approx_C
  StDgdg.ErrorData.apriori_D
  StDgdg.ErrorData.apriori_C
  StDgdg.ErrorData.apriori_C_paper
  StDgdg.Ode.odeSetting
  StDgdg.Ode.odeExpWeight
  StDgdg.Ode.odeErrorData
  StDgdg.Ode.ode_apriori_D
  StDgdg.Ode.ode_apriori_C
  StDgdg.Cut1d.cutSetting
  StDgdg.Cut1d.cutExpWeight
  StDgdg.Cut1d.cut_inf_sup
  StDgdg.Move1d.moveSetting
  StDgdg.Move1d.moveExpWeight
  StDgdg.Move1d.move_inf_sup
)
probe="$(mktemp --suffix=.lean)"
trap 'rm -f "$probe"' EXIT
{
  echo "import StDgdg"
  for e in "${exports[@]}"; do echo "#print axioms $e"; done
} > "$probe"
out="$(lake env lean "$probe")"
echo "$out"
for e in "${exports[@]}"; do
  line="$(grep -F "'$e' " <<< "$out" || true)"
  if [[ -z "$line" ]]; then
    echo "FAILED: no axiom report for $e" >&2; exit 1
  fi
  axioms="$(sed -E 's/.*\[(.*)\].*/\1/' <<< "$line" | tr ',' '\n' | tr -d ' ')"
  for a in $axioms; do
    case "$a" in
      propext|Classical.choice|Quot.sound) ;;
      *) echo "FAILED: $e depends on the axiom $a" >&2; exit 1 ;;
    esac
  done
done
echo "VERIFIED: ${#exports[@]} results, no sorry, standard axioms only (propext, Classical.choice, Quot.sound)."
