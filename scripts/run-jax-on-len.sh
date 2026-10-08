#!/usr/bin/env bash
# Run from the isolated staging directory on len; shared runtime is read-only.
set -u
suite="${1:?suite required}"
case "$suite" in fft|shear|projection|tests|normalization|newton|newton-tests|notebook) ;; *) exit 2 ;; esac
task_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$task_root"
out="$task_root/results/20261008"
mkdir -p "$out"
runtime="/home/xangma/venvs/pycbc-torch213-cu130/bin/python"
export PYTHONPATH="$task_root/src"
export XLA_PYTHON_CLIENT_PREALLOCATE=false
export OMP_NUM_THREADS=4
echo "Host=$(hostname) cwd=$PWD suite=$suite wrapper_pid=$$ log=$out/$suite.log"
if [[ "$suite" == notebook ]]; then
  timeout --signal=TERM --kill-after=10s 180 "$runtime" -u scripts/check-paper-playground.py --device gpu --output "$out/notebook-gpu.json" > "$out/$suite.log" 2>&1 &
elif [[ "$suite" == normalization ]]; then
  timeout --signal=TERM --kill-after=10s 120 "$runtime" -u scripts/check-jax-fft-normalization.py --output "$out/normalization.json" > "$out/$suite.log" 2>&1 &
elif [[ "$suite" == newton-tests ]]; then
  timeout --signal=TERM --kill-after=10s 180 "$runtime" -u -m unittest discover -s tests -p 'test_jax_newton.py' -v > "$out/$suite.log" 2>&1 &
elif [[ "$suite" == tests ]]; then
  timeout --signal=TERM --kill-after=10s 600 "$runtime" -u -m unittest discover -s tests -p 'test_jax_*.py' -v > "$out/$suite.log" 2>&1 &
else
  timeout --signal=TERM --kill-after=10s 900 "$runtime" -u scripts/benchmark-jax.py --require-gpu --suite "$suite" --output "$out/$suite.json" > "$out/$suite.log" 2>&1 &
fi
task_pid=$!
echo "$task_pid" > "$out/$suite.timeout.pid"
echo "timeout_pid=$task_pid stop=ssh len kill -TERM $task_pid next_check=tail $out/$suite.log"
wait "$task_pid"
task_rc=$?
echo "$task_rc" > "$out/$suite.exit"
echo "suite=$suite exit=$task_rc"
exit "$task_rc"
