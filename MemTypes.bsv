typedef Bit#(26) LineAddr;
typedef struct { Bit#(1) write; LineAddr addr; Bit#(512) data; } MainMemReq deriving (Eq, FShow, Bits, Bounded);
typedef Bit#(512) MainMemResp;
typedef Bit#(7) CacheIndex;
typedef Bit#(19) CacheTag;
typedef enum {Ready, StartHit, StartMiss, SendFillReq, WaitFillResp} ReqStatus deriving(Eq, Bits);
typedef struct{ LineAddr addr;
                MainMemResp data;} StBufType deriving(Eq, FShow, Bits); 

typedef Bit#(32) Word;
