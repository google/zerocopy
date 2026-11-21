// Probe: can a Go object whose last use precedes the end of its function be
// reclaimed (and its cleanup/finalizer run) while the function is still running?
//
// A *File wraps a raw OS pipe write descriptor. A cleanup (runtime.AddCleanup)
// or finalizer (runtime.SetFinalizer) closes the descriptor when the *File
// becomes unreachable. Each "use" function copies p.fd into a local (the last
// mention of p), forces several GC cycles, then writes to the descriptor.
// If the cleanup ran early, the write fails with EBADF.
//
// Usage: go run early.go <cleanup|finalizer> <nofence|keepalive> <trials>
package main

import (
	"fmt"
	"os"
	"runtime"
	"strconv"
	"syscall"
	"time"
)

type File struct{ fd int }

func gcAndWait() {
	for i := 0; i < 3; i++ {
		runtime.GC()
		time.Sleep(20 * time.Millisecond) // let the cleanup/finalizer goroutine run
	}
}

func newFile(mech string) (*File, int) {
	var fds [2]int
	if err := syscall.Pipe(fds[:]); err != nil {
		panic(err)
	}
	p := &File{fd: fds[1]}
	switch mech {
	case "cleanup":
		runtime.AddCleanup(p, func(fd int) { syscall.Close(fd) }, fds[1])
	case "finalizer":
		runtime.SetFinalizer(p, func(f *File) { syscall.Close(f.fd) })
	default:
		panic("mechanism must be cleanup or finalizer")
	}
	return p, fds[0]
}

//go:noinline
func useNoFence(p *File) error {
	fd := p.fd // last mention of p
	gcAndWait()
	_, err := syscall.Write(fd, []byte("x"))
	return err
}

//go:noinline
func useKeepAlive(p *File) error {
	fd := p.fd
	gcAndWait()
	_, err := syscall.Write(fd, []byte("x"))
	runtime.KeepAlive(p) // p must stay reachable until here
	return err
}

func main() {
	if len(os.Args) != 4 {
		fmt.Fprintln(os.Stderr, "usage: early <cleanup|finalizer> <nofence|keepalive> <trials>")
		os.Exit(2)
	}
	mech, mode := os.Args[1], os.Args[2]
	trials, _ := strconv.Atoi(os.Args[3])
	early := 0
	notEarly := []int{}
	for t := 0; t < trials; t++ {
		p, rfd := newFile(mech)
		var err error
		if mode == "keepalive" {
			err = useKeepAlive(p)
		} else {
			err = useNoFence(p)
		}
		if err == syscall.EBADF {
			early++
		} else {
			notEarly = append(notEarly, t)
		}
		syscall.Close(rfd)
		gcAndWait() // let any pending cleanup close the write end before the next trial
	}
	fmt.Printf("go=%s mech=%s mode=%s trials=%d write_failed_EBADF=%d writes_ok_at_trials=%v\n",
		runtime.Version(), mech, mode, trials, early, notEarly)
}
