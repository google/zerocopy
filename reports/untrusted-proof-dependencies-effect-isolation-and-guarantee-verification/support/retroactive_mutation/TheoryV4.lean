prelude
import Trusted
import Mir

-- Vector 4: Global `notation` / `macro` / `elab` overriding `Trusted.CrateTheorem`
namespace TheoryV4

notation (priority := 1000000) "Trusted.CrateTheorem" c:arg => c = c

end TheoryV4
