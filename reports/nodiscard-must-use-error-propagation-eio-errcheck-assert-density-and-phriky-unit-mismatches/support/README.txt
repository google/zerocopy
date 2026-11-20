Probe sources for the unused-result findings.
  wur.c       C23 cases G1-G9 (gcc -std=c23 -c -o /dev/null wur.c)
  nd.cpp      C++20 cases P1-P8 (g++ -std=c++20 -c -o /dev/null nd.cpp)
  mu.rs       Rust cases R1-R18 (rustc --edition 2024 --crate-type bin --emit=metadata mu.rs [-W unused_results])
  godemo/     Go cases C1-C16 (errcheck ./... ; errcheck -blank -asserts ./... ; go vet ./...)
  outputs.txt Captured diagnostics and timings.
Building errcheck offline: clone kisielk/errcheck at 59d0c8437e9f9e666d6b5ab02e55a093eecf7736 and
golang/tools v0.51.0, golang/mod v0.41.0, golang/sync v0.23.0 side by side, then in errcheck/:
  go mod edit -replace golang.org/x/tools=../tools -replace golang.org/x/mod=../mod -replace golang.org/x/sync=../sync
  GOFLAGS=-mod=mod GOPROXY=off GOSUMDB=off go build -o errcheck-bin .
