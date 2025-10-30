import Mathlib.Data.Nat.Prime.Defs

namespace Nat.Primes

instance {p : Nat.Primes} : Fact p.1.Prime := ⟨p.2⟩

end Nat.Primes
