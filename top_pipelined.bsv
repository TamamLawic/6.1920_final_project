import RVUtil::*;
import BRAM::*;
import pipelined::*;
import FIFO::*;
import MemTypes::*;
import Cache::*;
typedef Bit#(32) Word;

module mktop_pipelined(Empty);
    // Instantiate the dual ported memory
    BRAM_Configure cfg = defaultValue();
    cfg.loadFormat = tagged Hex "mem.vmh";
    BRAM2Port#(Bit#(512), Line) bram <- mkBRAM2Server(cfg);

    RVIfc rv_core <- mkpipelined;
    Reg#(Mem) ireq <- mkRegU;
    Reg#(Mem) dreq <- mkRegU;
    FIFO#(Mem) mmioreq <- mkFIFO;
    let debug = False;
    Reg#(Bit#(32)) cycle_count <- mkReg(0);
    Cache iCache <- mkCache();
    Cache dCache <- mkCache();

    rule tic;
	    cycle_count <= cycle_count + 1;
    endrule

    rule requestI;
        let req <- rv_core.getIReq;
        if (debug) $display("Get IReq", fshow(req));
        ireq <= req;
        Bit#(1) write = req.byte_en == 0? 0: 1;
        iCache.putFromProc(CacheReq{
            writeen: req.byte_en,
            write: write,
            addr: req.addr,
            data: req.data});
            // bram.portB.request.put(BRAMRequestBE{
            //         writeen: req.byte_en,
            //         responseOnWrite: True,
            //         address: truncate(req.addr >> 2),
            //         datain: req.data});
    endrule
    
    rule iCacheToMem;
            MainMemReq req = iCache.getToMem();
            bram.portB.request.put(BRAMRequest{
                    write: mem.write == 1,
                    responseOnWrite: False,
                    address: req.addr,
                    datain: req.data}); 
    endrule

    rule memToICache;
        MainMemResp memResp = bram.portB.response.get();
        iCache.putFromMem(memResp);
    endrule

    rule responseI;
        let x <- iCache.getToProc();
        let req = ireq;
        if (debug) $display("Get IResp ", fshow(req), fshow(x));
        req.data = x;
            rv_core.getIResp(req);
    endrule

    rule requestD;
        let req <- rv_core.getDReq;
        dreq <= req;
        if (debug) $display("Get DReq", fshow(req));
        Bit#(1) write = req.byte_en == 0? 0: 1;
        dCache.putFromProc(CacheReq{
            writeen: req.byte_en,
            write: write,
            addr: req.addr,
            data: req.data
        });
        // bram.portA.request.put(BRAMRequestBE{
        //   writeen: req.byte_en,
        //   responseOnWrite: True,
        //   address: truncate(req.addr >> 2),
        //   datain: req.data});
    endrule

    rule dCacheToMem;
            MainMemReq req = dcache.getToMem();
            bram.portA.request.put(BRAMRequest{
                    write: mem.write == 1,
                    responseOnWrite: False,
                    address: req.addr,
                    datain: req.data});  
    endrule

    rule memToDCache;
        MainMemResp memResp = bram.portA.response.get();
        dCache.putFromMem(memResp);
    endrule

    rule responseD;
        let x <- dCache.getToProc();
        let req = dreq;
        if (debug) $display("Get IResp ", fshow(req), fshow(x));
        req.data = x;
            rv_core.getDResp(req);
    endrule

  

    rule requestMMIO;
        let req <- rv_core.getMMIOReq;
        if (debug) $display("Get MMIOReq", fshow(req));
        if (req.byte_en == 'hf) begin
            if (req.addr == 'hf000_fff4) begin
                // Write integer to STDERR
                        $fwrite(stderr, "%0d", req.data);
                        $fflush(stderr);
            end
        end
        if (req.addr ==  'hf000_fff0) begin
                // Writing to STDERR
                $fwrite(stderr, "%c", req.data[7:0]);
                $fflush(stderr);
        end else
            if (req.addr == 'hf000_fff8) begin
            // Exiting Simulation
                if (req.data == 0) begin
                        $fdisplay(stderr, "  [0;32mPASS[0m");
                        $fdisplay(stderr, "Cycle count: ");
                        $fdisplay(stderr, cycle_count);
                end
                else
                    begin
                        $fdisplay(stderr, "  [0;31mFAIL[0m (%0d)", req.data);
                    end
                $fflush(stderr);
                $finish;
            end

        mmioreq.enq(req);
    endrule

    rule responseMMIO;
        let req = mmioreq.first();
        mmioreq.deq();
        if (debug) $display("Put MMIOResp", fshow(req));
        rv_core.getMMIOResp(req);
    endrule
    
endmodule
