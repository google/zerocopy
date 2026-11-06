// =======================================================================================
// This Sail RISC-V architecture model, comprising all files and
// directories except where otherwise noted is subject the BSD
// two-clause license in the LICENSE file.
//
// SPDX-License-Identifier: BSD-2-Clause
// =======================================================================================

// default register type
type regtype = xlenbits

// default zero register
let zero_reg : regtype = zeros()

// default register printer
function RegStr(r : regtype) -> string = bits_str(r)

// conversions

function regval_from_reg(r : regtype) -> xlenbits = r

function regval_into_reg(v : xlenbits) -> regtype = v
