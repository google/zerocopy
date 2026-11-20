Support material for the report in ../REPORT.md.

Contents
  toolchain.txt                 Go toolchain identity used for the probes
                                (`go version`, SHA-256 of the `compile` tool, GOOS/GOARCH).
  go_escape/probe.go            Escape-analysis probe functions E1..E10.
  go_escape/go.mod              Module file (module escprobe, go 1.27).
  go_escape/escape_m1.txt       Output of: go build -gcflags='-m' ./...
  go_escape/escape_m2_noinline.txt
                                Output of: go build -gcflags='-m=2 -l' ./...
                                filtered to lines that start with "# " or "./probe.go"
                                (standard-library diagnostics removed).
  go_live/live.go               Pointer-liveness probe functions L1..L4.
  go_live/go.mod                Module file (module liveprobe, go 1.27).
  go_live/live.txt              Output of: go build -gcflags='-live -l' ./...
  go_live/live_m.txt            Output of: go build -gcflags='-m -l' ./...

Reproduce (any Linux/amd64 host with the go1.27.3 toolchain on PATH):
  cd go_escape && go build -gcflags='-m' ./... 2>&1 | diff - escape_m1.txt
  cd go_live   && go build -gcflags='-live -l' ./... 2>&1 | diff - live.txt

The probes characterize the released go1.27.3 compiler only. They are not a
proof about any other Go revision; rerun them against the revision of interest.
