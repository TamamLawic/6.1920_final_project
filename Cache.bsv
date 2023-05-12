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

function MainMemResp putWord(Word word, ByteEn writeen, Offset offset, Line line);
    Word wordMask = 0;
    for(Integer i = 0; i < 32; i=i+1) begin
        wordMask[fromInteger(i)] = writeen[fromInteger(i)>>3];
    end
    Line wordInLine =  zeroExtend(word & wordMask) << ({5'h00, offset} * 32);
    Line mask = ~(zeroExtend((wordMask)) << ({5'h00, offset} * 32));
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
    BRAM1PortBE#(Bit#(7), MainMemResp, 64) dataBRAM <- mkBRAM1ServerBE(cfg);
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
            if(debug)begin $display("(stbuf) Write Miss"); end
            mshr <= StartMiss;
        end
        // will request to read a the corresponding cache line in both cases
        dataBRAM.portA.request.put(BRAMRequestBE{writeen: 0,
                                responseOnWrite: False,
                                address: idx,
                                datain: ?});
    endrule

    rule startHit if (mshr == StartHit);
        MainMemResp line <- dataBRAM.portA.response.get();
        let idx = indexOf(missReq.addr);
        let offset = offsetOf(missReq.addr);
        Bit#(6) beOffset = zeroExtend(offset) << 2; // shift because there's 4 bytes in a word
        LineWriteEn lineWriteEn = zeroExtend(missReq.writeen) << beOffset; 
        if (missReq.write == 1) begin // part of store buffer processing routine
            MainMemResp newLine = putWord(missReq.data, missReq.writeen, offset, line);
            if(debug)begin $display("Write hit"); 
                            $display("resident line: \n%h\nnew line: \n%h\n", line, newLine);end
            dataBRAM.portA.request.put(BRAMRequestBE{writeen: lineWriteEn,
                                responseOnWrite: False,
                                address: idx,
                                datain: newLine});
            dirtys[idx] <= True; // redundant with processStoreBuf but didn't know which to keep
        end else begin // Read hits
            let resp = getWord(offset, line);
            if(debug)begin $display("Read hit, respond: %h", resp); end
            hitQ.enq(resp);
        end
        mshr <= Ready;
    endrule

    rule startMiss if (mshr == StartMiss); // request dataBRAM @ missReq idx before transitoning into here
        let residentLine <- dataBRAM.portA.response.get();
        let idx = indexOf(missReq.addr);
        if(valids[idx] && dirtys[idx]) begin // main mem writeback
            if(debug)begin $display("old (tag=%h) line #%d written back\n", tags[idx], idx); end
            toMemQ.enq(MainMemReq {write: 1, addr: {tags[idx], idx}, data: residentLine});
        end 
        mshr <= SendFillReq;
    endrule

    rule sendFillReq if (mshr == SendFillReq);
        let idx = indexOf(missReq.addr);
        toMemQ.enq(MainMemReq {write: 0, addr: truncateLSB(missReq.addr), data: ?}); // truncateLSB(WordAddr) to find LineAddr corresp to WordAddr.
        if(debug)begin $display("line (tag=%h idx=%d) requested\n", tagOf(missReq.addr), indexOf(missReq.addr)); end
        mshr <= WaitFillResp;
    endrule

    rule waitFillResp if (mshr == WaitFillResp);
        if(debug)begin $display("new line recieved\n"); end
        MainMemResp newLine = fromMemQ.first();
        let idx = indexOf(missReq.addr);
        let offset = offsetOf(missReq.addr);
        Bit#(6) beOffset = zeroExtend(offset) << 2; // 4 bytes in a word
        LineWriteEn lineWriteEn = zeroExtend(missReq.writeen) << beOffset; 

        tags[idx] <= tagOf(missReq.addr);
        valids[idx] <= True;
        if (missReq.write == 1) begin // write (store)
            newLine = putWord(missReq.data, missReq.writeen, offset, newLine); // just change one word in the new line before storing.
            dirtys[idx] <= True;
            if(debug)begin $display("masked %h subbed in to line with offset %d (for store miss)\n", missReq.data, offset); end
        end else begin // read
            dirtys[idx] <= False;
            let resp = getWord(offset, newLine);
            if(debug)begin $display("read miss done, respond: %h", resp); end
            hitQ.enq(resp);      // send proc the requested word from newLine 
        end
        fromMemQ.deq();
        mshr <= Ready;
        if(debug)begin $display("new line dump: \n%h\n", newLine); end
        if(debug)begin $display("new line stored\n"); end
        dataBRAM.portA.request.put(BRAMRequestBE{  
                                                writeen: 64'hffffffffffffffff,
                                                responseOnWrite: False,
                                                address: idx,
                                                datain: newLine});
    endrule

    method Action putFromProc(CacheReq e) if(mshr == Ready);
        if(debug)begin $display("\nNEW REQUEST\nwrite:%b\naddr: %h\ndata:%h\n", e.writeen, e.addr, e.data); end
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
                if(debug)begin $display("Stbuf read hit\n"); end
                // instant return; mshr will stay ready.
            end else if(tagOf(e.addr) == tags[idx] && valids[idx]) begin // cache hit
                if(debug)begin $display("read hit, line: #%d \n", idx); end
                mshr <= StartHit;
                dataBRAM.portA.request.put(BRAMRequestBE{writeen: 0,
                                responseOnWrite: False,
                                address: idx,
                                datain: ?});
            end else begin // miss 
                if(debug)begin $display("Read Miss\n"); end
                mshr <= StartMiss;
                dataBRAM.portA.request.put(BRAMRequestBE{writeen: 0,
                            responseOnWrite: False,
                            address: idx,
                            datain: ?});
            end 
        end else begin // write
            // TODO: see if we can figure out how to write single words directly from our
            stBuf.enq(e); //enq in store buffer
            if(debug)begin $display("Stbuf enqueued\n"); end
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