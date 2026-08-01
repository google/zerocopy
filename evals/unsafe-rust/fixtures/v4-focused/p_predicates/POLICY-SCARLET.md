# Published support policy: Scarlet

For this snapshot, let:

- `V = {1.84.0, 1.85.0, 1.86.0}`;
- `X = x86_64-unknown-linux-gnu`;
- `A = aarch64-unknown-linux-gnu`;
- `W = wasm32-unknown-unknown`;
- `f` mean that `turbo` is enabled; and
- `h` mean that `hardened` is enabled.

Both Boolean states of each feature are meaningful. A configuration
`(v, t, f, h)` is supported by Scarlet exactly when `v` is in `V`, `t` is in
`{X, A, W}`, and this predicate is true:

```text
!f
or (f and t = X and (!h or v >= 1.85.0))
or (f and t = A and h)
```

Thus `turbo` on `W` is expressly unsupported. All Cargo profiles and both
states of debug assertions are supported for every configuration selected by
the predicate.

