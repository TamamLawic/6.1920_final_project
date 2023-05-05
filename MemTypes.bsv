typedef Bit#(32) WordAddr;
typedef Bit#(26) LineAddr;
typedef struct { Bit#(1) write; WordAddr addr; Word data; } CacheReq deriving (Eq, FShow, Bits, Bounded); 
typedef struct { Bit#(1) write; LineAddr addr; Bit#(512) data; } MainMemReq deriving (Eq, FShow, Bits, Bounded);
typedef Bit#(512) MainMemResp;
typedef Bit#(4) Offset;
typedef Bit#(7) CacheIndex;
typedef Bit#(19) CacheTag; // do yo thang 21, do yo thang
typedef enum {Ready, StartHit, StartMiss, SendFillReq, WaitFillResp} ReqStatus deriving(Eq, Bits);
typedef Bit#(32) Word;
