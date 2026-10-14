module
import Kraken.AArch64.Semantics
set_option pp.explicit true in
#print Kraken.Layout.apply
set_option pp.explicit true in
#print Kraken.Executable.directivesFromStart
#eval (({start := 12, size := fun _ => 4} : Layout) []).startAddr
