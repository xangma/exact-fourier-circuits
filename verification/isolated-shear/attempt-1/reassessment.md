The worker and an independent one-line RawKernel probe both failed at NVRTC
option admission, before numerical execution. The installed CuPy compiler
injects `-ftz=true`; adding `--ftz=false` duplicates that option. This is
unrelated to the shear algebra or its stability. Inspection of the installed
compiler identified `compile_using_nvrtc` as the interface that accepts the
explicit option unchanged. A direct NVRTC module probe with `--ftz=false`
preserved and doubled the FP32 subnormal `2^-140` exactly. The diagnostic now
uses that interface and retains its compiled object; the accuracy criterion,
inputs, arithmetic and requested options remain unchanged.
