import BRAM::*;
import FIFOF :: *;
import FIFO::*;
import SpecialFIFOs::*;
import MemTypes::*;
import Vector::*;
import Ehr::*;

interface Cache;
    method Action putFromProc(MainMemReq e);
    method ActionValue#(MainMemResp) getToProc();
    method ActionValue#(MainMemReq) getToMem();
    method Action putFromMem(MainMemResp e);
endinterface

module mkCache(Cache);
    // TODO Write a Cache
    // DEBUG PRINTS
    Bool debug = False;
    BRAM_Configure cfg = defaultValue;
    BRAM1Port#(Bit#(7), MainMemResp) dataBRAM <- mkBRAM1Server(cfg);
    Vector#(128, Reg#(CacheTag)) tags <- replicateM(mkReg(0));
    Vector#(128, Reg#(Bool)) valids <- replicateM(mkReg(False));
    Vector#(128, Reg#(Bool)) dirtys <- replicateM(mkReg(False));

    Reg#(ReqStatus) mshr <- mkReg(Ready);
    Reg#(MainMemReq) missReq <- mkRegU;

    FIFO#(MainMemReq) toMemQ <- mkFIFO;
    FIFO#(MainMemResp) fromMemQ <- mkFIFO;
    FIFO#(MainMemResp) toProc <- mkFIFO;
    FIFO#(MainMemResp) hitQ <- mkFIFO;
    FIFOF#(MainMemReq) stBuf <- mkFIFOF1;
        // make lockL1 with ehr to schedule putFromProc before processStoreBuffer
    Ehr#(2,Bool) lockL1 <- mkEhr(False);

    function CacheIndex indexOf(LineAddr addr) = truncate(addr);
    function CacheTag tagOf(LineAddr addr) = truncateLSB(addr);
    
    rule clearLockL1;
        lockL1[1] <= False;
    endrule
    rule processStoreBuf if (mshr == Ready && !lockL1[1]);
        let nextStore = stBuf.first();
        stBuf.deq();
        let idx = indexOf(nextStore.addr);
        if (tagOf(nextStore.addr) == tags[idx] && valids[idx]) begin // hit
            dirtys[idx] <= True;
            dataBRAM.portA.request.put(BRAMRequest{write: True,
                                responseOnWrite: False,
                                address: idx,
                                datain: nextStore.data});
        end else begin // miss
        missReq <= MainMemReq{write: 1, addr: nextStore.addr, data : nextStore.data};
        mshr <= StartMiss;
        dataBRAM.portA.request.put(BRAMRequest{write: False,
                                responseOnWrite: False,
                                address: idx,
                                datain: ?});
        end

    endrule

    rule startHit if (mshr == StartHit);
        let data <- dataBRAM.portA.response.get();
        hitQ.enq(data);
        mshr <= Ready;
    endrule

    rule startMiss if (mshr == StartMiss); // request dataBRAM @ missReq idx before transitoning into here
        let data <- dataBRAM.portA.response.get();
        let idx = indexOf(missReq.addr);
        if(valids[idx] && dirtys[idx]) begin
            toMemQ.enq(MainMemReq {write: 1, addr: {tags[idx], idx}, data: data});
        end 
        mshr <= SendFillReq;
    endrule

    rule sendFillReq if (mshr == SendFillReq);
        let idx = indexOf(missReq.addr);
        toMemQ.enq(MainMemReq {write: 0, addr: missReq.addr, data: ?});
        mshr <= WaitFillResp;
    endrule

    rule waitFillResp if (mshr == WaitFillResp);
        let newLine = fromMemQ.first();
        let idx = indexOf(missReq.addr);

        tags[idx] <= tagOf(missReq.addr);
        valids[idx] <= True;
        if (missReq.write == 1) begin // write (store)
            newLine = missReq.data; // I get that here we just overwrite, in other cases we would just change one word in the line before storing.
            dirtys[idx] <= True;
        end else begin // load
            dirtys[idx] <= False;
            hitQ.enq(newLine);      // here we would only take one word if we had many words per line
        end
        fromMemQ.deq();
        mshr <= Ready;
        dataBRAM.portA.request.put(BRAMRequest{  write: True,
                                                responseOnWrite: False,
                                                address: idx,
                                                datain: newLine});
    endrule

    method Action putFromProc(MainMemReq e) if(mshr == Ready);
        if(debug)begin $display("REQUEST\nread:%d\naddr: %h\ndata:%h\n", e.write, e.addr, e.data); end
        lockL1[0] <= True;
        let idx = indexOf(e.addr);
        Bool stBufHit = False;
        if (e.write == 0) begin // read

            if (stBuf.notEmpty()) begin
                stBufHit = stBuf.first().addr == e.addr;
            end

            if (stBufHit) begin  // stbuffer hit
                hitQ.enq(stBuf.first().data);
                // stay in ready state, ready for next req next cycle
            end else if(tagOf(e.addr) == tags[idx] && valids[idx]) begin // cache hit
                dataBRAM.portA.request.put(BRAMRequest{write: False,
                                responseOnWrite: False,
                                address: idx,
                                datain: ?});
                mshr <= StartHit;
            end else begin // miss 
                missReq <= e;
                mshr <= StartMiss;
                dataBRAM.portA.request.put(BRAMRequest{write: False,
                            responseOnWrite: False,
                            address: idx,
                            datain: ?});
            end 
        end else begin // write
            stBuf.enq(e); //enq in store buffer
        end  
        
    endmethod

    method ActionValue#(MainMemResp) getToProc();
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
