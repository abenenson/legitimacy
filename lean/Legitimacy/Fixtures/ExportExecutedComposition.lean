import Legitimacy.Protocol.ExecutedComposition

set_option autoImplicit false
open Legitimacy.ExecutedComposition

def bit (n k : Nat) : Bool := (n / 2^k) % 2 == 1

def stateCode (s : Exposure) : Nat := s.a.toNat * 2 + s.b.toNat

def row (n : Nat) : String :=
  let s : Exposure := ⟨bit n 6, bit n 5⟩
  let r : Request := ⟨bit n 4, bit n 3, bit n 2, bit n 1, bit n 0⟩
  "[" ++ String.intercalate "," ([n, (localPermit r).toNat,
    (permit s r).toNat, stateCode (step false s r),
    stateCode (step true s r)].map toString) ++ "]"

def main : IO Unit :=
  IO.println ("{\"format\":\"legitimacy.executed-composition.table.v1\","
    ++ "\"property\":\"Legitimacy.boolJointForbiddenList\",\"rows\":["
    ++ String.intercalate "," ((List.range 128).map row) ++ "]}")
