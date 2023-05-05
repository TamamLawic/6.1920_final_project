import BRAM::*;
import FIFOF :: *;
import FIFO::*;
import SpecialFIFOs::*;
import MemTypes::*;
import Vector::*;
import Ehr::*;

function Word getWord(Offset offset, MainMemResp line);
    Bit#(9) offsetExtended = zeroExtend(offset);
    return line[(32 * (offsetExtended + 1))-1 : 32 * offsetExtended];
endfunction

function MainMemResp putWord(Word word, Offset offset, MainMemResp line);
    MainMemResp mask = ~(zeroExtend((32'hffffffff)) << ({5'h00, offset} * 32));
    MainMemResp wordInLine =  zeroExtend(word) << ({5'h00, offset} * 32);
    return (line & mask) | wordInLine; //i love men
endfunction

function WordAddr makeAddr(CacheTag tag, CacheIndex index, Offset offset);
    return {tag, index, offset, 2'b00};
endfunction


interface Cache;
    method Action putFromProc(CacheReq e);
    method ActionValue#(Word) getToProc();
    method ActionValue#(MainMemReq) getToMem();
    method Action putFromMem(MainMemResp e);
endinterface

(* synthesize *)
module mkCache(Cache);
    // Debug print flag
    Bool debug = False;

    BRAM_Configure cfg = defaultValue;
    BRAM1Port#(Bit#(7), MainMemResp) dataBRAM <- mkBRAM1Server(cfg);
    Vector#(128, Reg#(CacheTag)) tags <- replicateM(mkReg(0));
    Vector#(128, Reg#(Bool)) valids <- replicateM(mkReg(False));
    Vector#(128, Reg#(Bool)) dirtys <- replicateM(mkReg(False));

    Reg#(ReqStatus) mshr <- mkReg(Ready);
    Reg#(CacheReq) missReq <- mkRegU;

    FIFO#(MainMemReq) toMemQ <- mkFIFO;
    FIFO#(MainMemResp) fromMemQ <- mkFIFO;
    FIFO#(Word) toProc <- mkFIFO;
    FIFO#(Word) hitQ <- mkFIFO;
    FIFOF#(CacheReq) stBuf <- mkFIFOF1;
    // make lockL1 with ehr to schedule putFromProc before processStoreBuffer
    Ehr#(2,Bool) lockL1 <- mkEhr(False);

    // address breakout functions
    function Offset offsetOf(WordAddr addr) = addr[5:2];
    function CacheIndex indexOf(WordAddr addr) = addr[12:6];
    function CacheTag tagOf(WordAddr addr) = addr[31:13];
    
    rule clearLockL1;
        lockL1[1] <= False;
    endrule
    rule processStoreBuf if (mshr == Ready && !lockL1[1]);
        let nextStore = stBuf.first();
        stBuf.deq();
        missReq <= nextStore;
        let idx = indexOf(nextStore.addr);

        if (tagOf(nextStore.addr) == tags[idx] && valids[idx]) begin 
            dirtys[idx] <= True;
            mshr <= StartHit;
        end else begin // miss
            mshr <= StartMiss;
        end
        // will request to read a the corresponding cache line in both cases
        dataBRAM.portA.request.put(BRAMRequest{write: False,
                                responseOnWrite: False,
                                address: idx,
                                datain: ?});
    endrule

    rule startHit if (mshr == StartHit);
        MainMemResp line <- dataBRAM.portA.response.get();
        let idx = indexOf(missReq.addr);
        let offset = offsetOf(missReq.addr);
        if (missReq.write == 1) begin // part of store buffer processing routine
            MainMemResp newLine = putWord(missReq.data, offset, line);
            dataBRAM.portA.request.put(BRAMRequest{write: True,
                                responseOnWrite: False,
                                address: idx,
                                datain: newLine});
            dirtys[idx] <= True; // redundant with processStoreBuf but didn't know which to keep
        end else begin // Read hits
            hitQ.enq(getWord(offset, line));
        end
        mshr <= Ready;
    endrule

    rule startMiss if (mshr == StartMiss); // request dataBRAM @ missReq idx before transitoning into here
        let residentLine <- dataBRAM.portA.response.get();
        let idx = indexOf(missReq.addr);
        if(valids[idx] && dirtys[idx]) begin // main mem writeback
            toMemQ.enq(MainMemReq {write: 1, addr: {tags[idx], idx}, data: residentLine});
        end 
        mshr <= SendFillReq;
    endrule

    rule sendFillReq if (mshr == SendFillReq);
        let idx = indexOf(missReq.addr);
        toMemQ.enq(MainMemReq {write: 0, addr: truncateLSB(missReq.addr), data: ?}); // truncateLSB(WordAddr) for LineAddr corresp to WordAddr.
        mshr <= WaitFillResp;
    endrule

    rule waitFillResp if (mshr == WaitFillResp);
        MainMemResp newLine = fromMemQ.first();
        let idx = indexOf(missReq.addr);
        let offset = offsetOf(missReq.addr);

        tags[idx] <= tagOf(missReq.addr);
        valids[idx] <= True;
        if (missReq.write == 1) begin // write (store)
            newLine = putWord(missReq.data, offset, newLine); // just change one word in the new line before storing.
            dirtys[idx] <= True;
        end else begin // load
            dirtys[idx] <= False;
            hitQ.enq(getWord(offset, newLine));      // send proc the requested word from newLine 
        end
        fromMemQ.deq();
        mshr <= Ready;
        dataBRAM.portA.request.put(BRAMRequest{  write: True,
                                                responseOnWrite: False,
                                                address: idx,
                                                datain: newLine});
    endrule

    method Action putFromProc(CacheReq e) if(mshr == Ready);
        if(debug)begin $display("REQUEST\nread:%d\naddr: %h\ndata:%h\n", e.write, e.addr, e.data); end
        lockL1[0] <= True;
        let idx = indexOf(e.addr);
        Bool stBufHit = False;
        CacheReq reqFromBuf = unpack(0);
        // save current request in case multi-cycle handling is needed
        missReq <= e;

        if (e.write == 0) begin // read

            if (stBuf.notEmpty()) begin
                reqFromBuf = stBuf.first();
                stBufHit = stBuf.first().addr == e.addr; 
            end

            if (stBufHit) begin         // stbuffer hit
                hitQ.enq(reqFromBuf.data);
                // instant return; mshr will stay ready.
            end else if(tagOf(e.addr) == tags[idx] && valids[idx]) begin // cache hit
                mshr <= StartHit;
                dataBRAM.portA.request.put(BRAMRequest{write: False,
                                responseOnWrite: False,
                                address: idx,
                                datain: ?});
            end else begin // miss 
                mshr <= StartMiss;
                dataBRAM.portA.request.put(BRAMRequest{write: False,
                            responseOnWrite: False,
                            address: idx,
                            datain: ?});
            end 
        end else begin // write
            // TODO: see if we can figure out how to write single words directly from our
            stBuf.enq(e); //enq in store buffer
        end  
        
    endmethod

    method ActionValue#(Word) getToProc();
        hitQ.deq();
        return hitQ.first();
    endmethod

    method ActionValue#(MainMemReq) getToMem();
        toMemQ.deq();
        return toMemQ.first();
    endmethod

    method Action putFromMem(MainMemResp e);
        fromMemQ.enq(e);
    endmethod

endmodule