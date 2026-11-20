package demo

import (
	"bytes"
	"errors"
	"fmt"
	"io"
	"os"
)

func mayFail() error       { return nil }
func pair() (int, error)   { return 0, nil }
func callIt(fn func() error) { fn() } // C13: the wrapper itself drops the error

type thunk func() error

func Cases(w io.Writer, f *os.File) {
	mayFail()                              // C1 bare call
	_ = mayFail()                          // C2 explicit blank discard
	defer f.Close()                        // C3 deferred Close
	go mayFail()                           // C4 go statement
	fmt.Fprintf(w, "x")                    // C5 fmt.Fprintf to an arbitrary io.Writer
	fmt.Println("x")                       // C6 fmt.Println
	var b bytes.Buffer
	b.WriteString("x")                     // C7 bytes.Buffer write
	n, _ := pair()                         // C8 blank in tuple
	_ = n
	err := mayFail()                       // C9 assigned, then overwritten before any check
	err = mayFail()
	if err != nil {
		return
	}
	var cb thunk = mayFail
	cb()                                   // C10 call through a function value
	func() error { return mayFail() }()    // C11 immediately-invoked closure
	var i interface{} = 1
	s := i.(string)                        // C12 unchecked type assertion
	_ = s
	callIt(mayFail)                        // C13 error routed into a callback wrapper
	fmt.Sprintf("x")                       // C15 pure result discarded (not an error)
	errors.New("x")                        // C16 constructed error discarded
}
