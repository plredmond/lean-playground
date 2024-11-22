
-- Define objects with interfaces
class Intf (obj : Type) where
    send : obj -> packet -> obj
    recv : obj -> packet -> obj

#check Intf.send

-- Write specifications about interfaces
structure Intf.specS [Intf obj] where

class Intf.specC [Intf obj] where
    state : obj -> Set packet
    --init (o : obj) : _

#check Intf.specS
#check Intf.spec

-- Prove assume/guarantee relationships between these specifications
