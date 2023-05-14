import FIFO::*;
import FIFOF :: *;
import SpecialFIFOs::*;
import RegFile::*;
import BRAM::*;
import RVUtil::*;
import Vector::*;
import KonataHelper::*;
import Printf::*;
import Ehr::*;

typedef struct { Bit#(4) byte_en; Bit#(32) addr; Bit#(32) data; } Mem deriving (Eq, FShow, Bits);

interface RVIfc;
    method ActionValue#(Mem) getIReqRed();
    method Action getIRespRed(Mem a);
    method ActionValue#(Mem) getIReqBlue();
    method Action getIRespBlue(Mem a);
    method ActionValue#(Mem) getDReq();
    method Action getDResp(Mem a);
    method ActionValue#(Mem) getMMIOReq();
    method Action getMMIOResp(Mem a);
endinterface

typedef struct { Bool isUnsigned; Bit#(2) size; Bit#(2) offset; Bool mmio; } MemBusiness deriving (Eq, FShow, Bits);
typedef Bit#(32) TableResp;
typedef Bit#(7) BtbIndex;
typedef Bit#(25) BtbTag;
typedef Bit#(32) Addr;

interface AddrPred;
    method Addr nap(Addr pc);
    method Action update(Addr pc, Addr nextPC, Bool taken);
endinterface

module mkPredictor(AddrPred);
    // regs vectors brams
    Vector#(128, Ehr#(2, BtbTag)) tags <- replicateM(mkEhr(0));
    Vector#(128, Ehr#(2, Addr)) predPC <- replicateM(mkEhr(0));
    Vector#(128, Ehr#(2, Bool)) validArray <- replicateM(mkEhr(False));

    //functions for addressing
    function BtbIndex idxOf (Addr pc) = truncate (pc);
    function BtbTag tagOf (Addr pc) = truncateLSB (pc);

    method Addr nap(Addr current_pc);
        //start request
        let idx = idxOf(current_pc);
        let predictedAddr = current_pc + 4;
        let currentTag = tagOf(current_pc);
        
        if (validArray[idx][1] && tags[idx][1] == currentTag) begin
            predictedAddr = predPC[idx][1];
        end
        return predictedAddr;
    endmethod

    method Action update(Addr start_pc, Addr nextPC, Bool taken);
        //extract index and tag from pc;
        let idx = idxOf(start_pc);
        let tag = tagOf(start_pc);
        //if (branch taken) then update BTB with the new prediction; 
        if (taken) begin
            if (!validArray[idx][0]) begin
                validArray[idx][0] <= True;
            end
            predPC[idx][0] <= nextPC;
            tags[idx][0] <= tag;
        end
        //if the branch is not taken, and the entry is in the table, remove it
        else if(validArray[idx][0] && tags[idx][0] == tag) begin
            validArray[idx][0] <= False;
        end
        //mark the entry pc as branch taken;
        //else mark the entry pc as branch not taken
    endmethod
endmodule

typedef enum {
    Fetch, Decode, Execute, Writeback
} StateProc deriving (Eq, FShow, Bits);

function Bool isMMIO(Bit#(32) addr);
    Bool x = case (addr) 
        32'hf000fff0: True;
        32'hf000fff4: True;
        32'hf000fff8: True;
        default: False;
    endcase;
    return x;
endfunction

typedef struct { Bit#(32) pc;
                 Bit#(32) ppc;
                 Bit#(1) epoch; 
                 KonataId k_id; // <- This is a unique identifier per instructions, for logging purposes
             } F2D deriving (Eq, FShow, Bits);

typedef struct { 
    DecodedInst dinst;
    Bit#(32) pc;
    Bit#(32) ppc;
    Bit#(1) epoch;
    Bit#(32) rv1; 
    Bit#(32) rv2; 
    KonataId k_id; // <- This is a unique identifier per instructions, for logging purposes
    } D2E deriving (Eq, FShow, Bits);

typedef struct { 
    MemBusiness mem_business;
    Bit#(32) data;
    DecodedInst dinst;
    KonataId k_id; // <- This is a unique identifier per instructions, for logging purposes
} E2W deriving (Eq, FShow, Bits);

(* synthesize *)
module mkpipelined(RVIfc);

    function Bit#(32) predictPPC(Bit#(32) pc);
        return pc + 4;
    endfunction

    // Interface with memory and devices
    FIFOF#(Mem) toImemRed <- mkBypassFIFOF;
    FIFO#(Mem) fromImemRed <- mkBypassFIFO;
    FIFOF#(Mem) toImemBlue <- mkBypassFIFOF;
    FIFO#(Mem) fromImemBlue <- mkBypassFIFO;
    FIFO#(Mem) toDmem <- mkBypassFIFO;
    FIFO#(Mem) fromDmem <- mkBypassFIFO;
    FIFO#(Mem) toMMIO <- mkBypassFIFO;
    FIFO#(Mem) fromMMIO <- mkBypassFIFO;

    //start at the top of the code
    Vector#(32,  Ehr#(3, Bit#(32))) rf_r <- replicateM(mkEhr(0));
    Vector#(32,  Ehr#(3, Bit#(32))) rf_b <- replicateM(mkEhr(0));

    // Make queues for between each state
    FIFOF#(F2D) f2d_r <- mkFIFOF1();
    FIFOF#(D2E) d2e_r <- mkFIFOF1();
    FIFOF#(E2W) e2w_r <- mkFIFOF1();
    FIFOF#(F2D) f2d_b <- mkFIFOF1();
    FIFOF#(D2E) d2e_b <- mkFIFOF1();
    FIFOF#(E2W) e2w_b <- mkFIFOF1();

    Ehr#(2, Bit#(1)) epoch_r <- mkEhr(0);
    Ehr#(2, Bit#(32)) pc_r <- mkEhr(32'h0000000);
    Ehr#(2, Bit#(1)) epoch_b <- mkEhr(0);
    Ehr#(2, Bit#(32)) pc_b <- mkEhr(32'h0000000);

    //make the scoreboard
    Vector#(32, Ehr#(3, Bit#(2))) scoreboard_r <- replicateM(mkEhr(0));
    Vector#(32, Ehr#(3, Bit#(2))) scoreboard_b <- replicateM(mkEhr(0));

    //make structure for storing BTB table
    AddrPred btb <- mkPredictor;

    //adding support for SMT
    FIFOF#(Bool) colorCacheRed <- mkFIFOF1;
    Reg#(Bool) colorPriority <- mkReg(True);
    Reg#(Bool) colorPriorityWrite <- mkReg(True);
    FIFOF#(Bool) colorMRed <- mkFIFOF1;
    Reg#(Bool) instRed <- mkReg(True);

    // Code to support Konata visualization
    String dumpFile = "pipelined.log" ;
    let lfh <- mkReg(InvalidFile);
    Reg#(KonataId) fresh_id <- mkReg(0);
    Reg#(KonataId) commit_id <- mkReg(0);

    FIFO#(KonataId) retired <- mkFIFO;
    FIFO#(KonataId) squashed <- mkFIFO;

    Bool debug = False;
    Reg#(Bool) starting <- mkReg(True);
    rule do_tic_logging;
        if (starting) begin
            let f <- $fopen(dumpFile, "w") ;
            lfh <= f;
            $fwrite(f, "Kanata\t0004\nC=\t1\n");
            starting <= False;
        end
        konataTic(lfh);
    endrule

    rule fetch if (!starting);
        //check instruction priority
        //make sure there is room in the fifo your giving it to, and you still have instructions
        if (f2d_r.notFull) begin
            if(debug) $display("Fetch %x", pc_r[1]);
            Bit#(32) pc_fetched = pc_r[1];
            // You should put the pc that you fetch in pc_fetched
            // Below is the code to support Konata's visualization
            let iid <- fetch1Konata(lfh, fresh_id, 0);
            // CHANGE THIS LINE TO USE BTB!!
            pc_r[1] <= btb.nap(pc_r[1]);
            labelKonataLeft(lfh, iid, $format("PC %x",pc_r[1]));
            // TODO implement fetch
            let req = Mem {byte_en : 0,
                addr : pc_r[1],
                data : 0};
            toImemRed.enq(req);
            f2d_r.enq(F2D{pc : pc_r[1], ppc : btb.nap(pc_r[1]), epoch: epoch_r[1], k_id: iid});
            //make color fifo to make sure we know which we are starting
            colorCacheRed.enq(True);
        end
        else if (f2d_b.notFull) begin
            if(debug) $display("Fetch %x", pc_b[1]);
            Bit#(32) pc_fetched = pc_b[1];
            // You should put the pc that you fetch in pc_fetched
            // Below is the code to support Konata's visualization
            let iid <- fetch1Konata(lfh, fresh_id, 0);
            // CHANGE THIS LINE TO USE BTB!!
            pc_b[1] <= btb.nap(pc_b[1]);
            labelKonataLeft(lfh, iid, $format("PC %x",pc_b[1]));
            // TODO implement fetch
            let req = Mem {byte_en : 0,
                addr : pc_b[1],
                data : 0};
            toImemRed.enq(req);
            f2d_b.enq(F2D{pc : pc_b[1], ppc : btb.nap(pc_b[1]), epoch: epoch_b[1], k_id: iid});
            //set color instruction sent in fifo
            colorCacheRed.enq(False);
        end
    endrule

    rule decode if (!starting);
        // get the color of the instruction, if there is one
        if (colorCacheRed.notEmpty()) begin
            let colorRed = colorCacheRed.first();
            colorCacheRed.deq();
            if (debug) $display("[Decode] color red : ", fshow(colorRed));
            //if the color is red, put in red fifo
            if (colorRed) begin
                let from_fetch = f2d_r.first();
                let resp = fromImemRed.first();
                let instr = resp.data;
                let decodedInst = decodeInst(instr);
                decodeKonata(lfh, from_fetch.k_id);
                labelKonataLeft(lfh,from_fetch.k_id, $format("Instr bits: %x",decodedInst.inst));
                if (debug) $display("[Decode] ", fshow(decodedInst));
                let rs1_idx = getInstFields(instr).rs1;
                let rs2_idx = getInstFields(instr).rs2;
                let rs1 = (rs1_idx ==0 ? 0 : rf_r[rs1_idx][1]);
                let rs2 = (rs2_idx == 0 ? 0 : rf_r[rs2_idx][1]);
                let fields = getInstFields(decodedInst.inst);
                let rd_idx = fields.rd;
                labelKonataLeft(lfh,from_fetch.k_id, $format(" Potential r1: %x, Potential r2: %x" , rs1, rs2));
                // if the register is being used, wait
                if (scoreboard_r[rs1_idx][2] == 0 && scoreboard_r[rs2_idx][2] == 0 && scoreboard_r[rd_idx][2] == 0) begin
                    //mark any changed registers to in use
                    if (decodedInst.valid_rd) begin
                        if (rd_idx != 0) begin 
                            scoreboard_r[rd_idx][2] <= scoreboard_r[rd_idx][2] + 1;
                            if (debug) $display("[Decode scoreboard : ] ", rd_idx, fshow(scoreboard_r[rd_idx][2]));
                        end
                        if(debug) $display("Use Register %x", rd_idx);
                    end
                    d2e_r.enq(D2E{dinst: decodedInst, pc: from_fetch.pc, ppc: from_fetch.ppc, epoch: from_fetch.epoch, rv1: rs1, rv2: rs2, k_id: from_fetch.k_id});
                    f2d_r.deq();
                    fromImemRed.deq();
                end
            end
            else begin
                let from_fetch = f2d_b.first();
                let resp = fromImemBlue.first();
                let instr = resp.data;
                let decodedInst = decodeInst(instr);
                decodeKonata(lfh, from_fetch.k_id);
                labelKonataLeft(lfh,from_fetch.k_id, $format("Instr bits: %x",decodedInst.inst));
                if (debug) $display("[Decode] ", fshow(decodedInst));
                let rs1_idx = getInstFields(instr).rs1;
                let rs2_idx = getInstFields(instr).rs2;
                let rs1 = (rs1_idx ==0 ? 0 : rf_r[rs1_idx][1]);
                let rs2 = (rs2_idx == 0 ? 0 : rf_r[rs2_idx][1]);
                let fields = getInstFields(decodedInst.inst);
                let rd_idx = fields.rd;
                labelKonataLeft(lfh,from_fetch.k_id, $format(" Potential r1: %x, Potential r2: %x" , rs1, rs2));
                // if the register is being used, wait
                if (scoreboard_b[rs1_idx][2] == 0 && scoreboard_b[rs2_idx][2] == 0 && scoreboard_b[rd_idx][2] == 0) begin
                    //mark any changed registers to in use
                    if (decodedInst.valid_rd) begin
                        if (rd_idx != 0) begin 
                            scoreboard_b[rd_idx][2] <= scoreboard_b[rd_idx][2] + 1;
                            if (debug) $display("[Decode scoreboard : ] ", rd_idx, fshow(scoreboard_b[rd_idx][2]));
                        end
                        if(debug) $display("Use Register %x", rd_idx);
                    end
                    d2e_b.enq(D2E{dinst: decodedInst, pc: from_fetch.pc, ppc: from_fetch.ppc, epoch: from_fetch.epoch, rv1: rs1, rv2: rs2, k_id: from_fetch.k_id});
                    f2d_b.deq();
                    fromImemRed.deq();
                end
            end

        end
        //state <= Execute;
        // To add a decode event in Konata you will likely do something like:
        //  let from_fetch = f2d.first();
        //  decodeKonata(lfh, from_fetch.k_id);
        //  labelKonataLeft(lfh,from_fetch.k_id, $format("Any information you would like to put in the left pane in Konata, attached to the current instruction"));
    endrule

    rule execute if (!starting);
        // Similarly, to register an execute event for an instruction:
        //  executeKonata(lfh, k_id);
        // where k_id is the unique konata identifier that has been passed around that came from the fetch stage


        // Execute is also the place where we advise you to kill mispredicted instructions
        // (instead of Decode + Execute like in the class)
        // When you kill (or squash) an instruction, you should register an event for Konata:

        // squashed.enq(current_inst.k_id);

        // This will allow Konata to display those instructions in grey

        // Support for SMT
        
        //let from_fetch = d2e_r.first();

        //if red has priority, see if red has entry first
        if (colorPriority) begin 
            //check red fifo
            if (d2e_r.notEmpty) begin
                let from_fetch = d2e_r.first();
                d2e_r.deq();
                if (debug) $display("[Execute] ", fshow(from_fetch.dinst));
                let current_id = from_fetch.k_id;
                executeKonata(lfh, current_id);
                if (from_fetch.epoch == epoch_r[0])  begin
                    let imm = getImmediate(from_fetch.dinst);
                    Bool mmio = False;
                    let data = execALU32(from_fetch.dinst.inst, from_fetch.rv1, from_fetch.rv2, imm, from_fetch.pc);
                    let isUnsigned = 0;
                    let funct3 = getInstFields(from_fetch.dinst.inst).funct3;
                    let size = funct3[1:0];
                    let addr = from_fetch.rv1 + imm;
                    Bit#(2) offset = addr[1:0];
                    if (isMemoryInst(from_fetch.dinst)) begin
                        // Technical details for load byte/halfword/word
                        let shift_amount = {offset, 3'b0};
                        let byte_en = 0;
                        case (size) matches
                        2'b00: byte_en = 4'b0001 << offset;
                        2'b01: byte_en = 4'b0011 << offset;
                        2'b10: byte_en = 4'b1111 << offset;
                        endcase
                        data = from_fetch.rv2 << shift_amount;
                        addr = {addr[31:2], 2'b0};
                        isUnsigned = funct3[2];
                        let type_mem = (from_fetch.dinst.inst[5] == 1) ? byte_en : 0;
                        let req = Mem {byte_en : type_mem,
                                addr : addr,
                                data : data};
                        if (isMMIO(addr)) begin 
                            if (debug) $display("[Execute] MMIO", fshow(req));
                            toMMIO.enq(req);
                            labelKonataLeft(lfh,current_id, $format(" MMIO ", fshow(req)));
                            mmio = True;
                            //store color
                            colorMRed.enq(True);
                        end else begin 
                            labelKonataLeft(lfh,current_id, $format(" MEM ", fshow(req)));
                            toDmem.enq(req);
                            // store the color of the indtruction
                            colorMRed.enq(True);
                        end
                    end
                    else if (isControlInst(from_fetch.dinst)) begin
                            labelKonataLeft(lfh,current_id, $format(" Ctrl instr "));
                            data = from_fetch.pc + 4;
                    end else begin 
                        labelKonataLeft(lfh,current_id, $format(" Standard instr "));
                    end
                    let controlResult = execControl32(from_fetch.dinst.inst, from_fetch.rv1, from_fetch.rv2, imm, from_fetch.pc);
                    let nextPc = controlResult.nextPC;

                    //if the predicted next PC is not the actual PC, update epoch etc.
                    if(nextPc != from_fetch.ppc) begin
                        pc_r[0] <= nextPc;
                        epoch_r[0] <= ~epoch_r[0]; 
                        //for btb training
                        btb.update(from_fetch.pc, nextPc, controlResult.taken);
                        if(debug) $display("Redirect %x", nextPc);
                    end
        
                    let mem_business = MemBusiness { isUnsigned : unpack(isUnsigned), size : size, offset : offset, mmio: mmio};
                    e2w_r.enq(E2W{mem_business : mem_business, data : data, dinst : from_fetch.dinst, k_id : current_id});
                    labelKonataLeft(lfh,current_id, $format(" ALU output: %x" , data));
                end
                else begin
                    squashed.enq(from_fetch.k_id);
                    let fields = getInstFields(from_fetch.dinst.inst);
                    let rd_idx = fields.rd;
                    if (from_fetch.dinst.valid_rd && rd_idx != 0 ) begin
                        scoreboard_r[rd_idx][1] <= scoreboard_r[rd_idx][1] - 1;
                    end
                    if(debug) $display("Free Execute Register %x", rd_idx);
                    if (debug) $display("[Execute scoreboard : ] ", rd_idx, fshow(scoreboard_r[rd_idx][1]));
                end
            end
            //if red empty, try blue
            else if (d2e_b.notEmpty) begin
                let from_fetch = d2e_b.first();
                d2e_b.deq();
                if (debug) $display("[Execute] ", fshow(from_fetch.dinst));
                let current_id = from_fetch.k_id;
                executeKonata(lfh, current_id);
                    if (from_fetch.epoch == epoch_b[0])  begin
                        let imm = getImmediate(from_fetch.dinst);
                        Bool mmio = False;
                        let data = execALU32(from_fetch.dinst.inst, from_fetch.rv1, from_fetch.rv2, imm, from_fetch.pc);
                        let isUnsigned = 0;
                        let funct3 = getInstFields(from_fetch.dinst.inst).funct3;
                        let size = funct3[1:0];
                        let addr = from_fetch.rv1 + imm;
                        Bit#(2) offset = addr[1:0];
                        if (isMemoryInst(from_fetch.dinst)) begin
                            // Technical details for load byte/halfword/word
                            let shift_amount = {offset, 3'b0};
                            let byte_en = 0;
                            case (size) matches
                            2'b00: byte_en = 4'b0001 << offset;
                            2'b01: byte_en = 4'b0011 << offset;
                            2'b10: byte_en = 4'b1111 << offset;
                            endcase
                            data = from_fetch.rv2 << shift_amount;
                            addr = {addr[31:2], 2'b0};
                            isUnsigned = funct3[2];
                            let type_mem = (from_fetch.dinst.inst[5] == 1) ? byte_en : 0;
                            let req = Mem {byte_en : type_mem,
                                    addr : addr,
                                    data : data};
                            if (isMMIO(addr)) begin 
                                if (debug) $display("[Execute] MMIO", fshow(req));
                                toMMIO.enq(req);
                                labelKonataLeft(lfh,current_id, $format(" MMIO ", fshow(req)));
                                mmio = True;
                                //store color
                                colorMRed.enq(False);
                            end else begin 
                                labelKonataLeft(lfh,current_id, $format(" MEM ", fshow(req)));
                                toDmem.enq(req);
                                //store color
                                colorMRed.enq(False);
                            end
                        end
                        else if (isControlInst(from_fetch.dinst)) begin
                                labelKonataLeft(lfh,current_id, $format(" Ctrl instr "));
                                data = from_fetch.pc + 4;
                        end else begin 
                            labelKonataLeft(lfh,current_id, $format(" Standard instr "));
                        end
                        let controlResult = execControl32(from_fetch.dinst.inst, from_fetch.rv1, from_fetch.rv2, imm, from_fetch.pc);
                        let nextPc = controlResult.nextPC;

                        //if the predicted next PC is not the actual PC, update epoch etc.
                        if(nextPc != from_fetch.ppc) begin
                            pc_b[0] <= nextPc;
                            epoch_b[0] <= ~epoch_b[0]; 
                            //for btb training
                            btb.update(from_fetch.pc, nextPc, controlResult.taken);
                            if(debug) $display("Redirect %x", nextPc);
                        end
            
                        let mem_business = MemBusiness { isUnsigned : unpack(isUnsigned), size : size, offset : offset, mmio: mmio};
                        e2w_b.enq(E2W{mem_business : mem_business, data : data, dinst : from_fetch.dinst, k_id : current_id});
                        labelKonataLeft(lfh,current_id, $format(" ALU output: %x" , data));
                    end
                    else begin
                        squashed.enq(from_fetch.k_id);
                        let fields = getInstFields(from_fetch.dinst.inst);
                        let rd_idx = fields.rd;
                        if (from_fetch.dinst.valid_rd && rd_idx != 0 ) begin
                            scoreboard_b[rd_idx][1] <= scoreboard_b[rd_idx][1] - 1;
                        end
                        if(debug) $display("Free Execute Register %x", rd_idx);
                        if (debug) $display("[Execute scoreboard : ] ", rd_idx, fshow(scoreboard_b[rd_idx][1]));
                    end
            end
        end
        //if blue has priority, see if blue has entry first
        else begin
            //check blue fifo
            if (d2e_b.notEmpty) begin
                let from_fetch = d2e_b.first();
                d2e_b.deq();
                if (debug) $display("[Execute] ", fshow(from_fetch.dinst));
                let current_id = from_fetch.k_id;
                executeKonata(lfh, current_id);
                if (from_fetch.epoch == epoch_b[0])  begin
                    let imm = getImmediate(from_fetch.dinst);
                    Bool mmio = False;
                    let data = execALU32(from_fetch.dinst.inst, from_fetch.rv1, from_fetch.rv2, imm, from_fetch.pc);
                    let isUnsigned = 0;
                    let funct3 = getInstFields(from_fetch.dinst.inst).funct3;
                    let size = funct3[1:0];
                    let addr = from_fetch.rv1 + imm;
                    Bit#(2) offset = addr[1:0];
                    if (isMemoryInst(from_fetch.dinst)) begin
                        // Technical details for load byte/halfword/word
                        let shift_amount = {offset, 3'b0};
                        let byte_en = 0;
                        case (size) matches
                        2'b00: byte_en = 4'b0001 << offset;
                        2'b01: byte_en = 4'b0011 << offset;
                        2'b10: byte_en = 4'b1111 << offset;
                        endcase
                        data = from_fetch.rv2 << shift_amount;
                        addr = {addr[31:2], 2'b0};
                        isUnsigned = funct3[2];
                        let type_mem = (from_fetch.dinst.inst[5] == 1) ? byte_en : 0;
                        let req = Mem {byte_en : type_mem,
                                addr : addr,
                                data : data};
                        if (isMMIO(addr)) begin 
                            if (debug) $display("[Execute] MMIO", fshow(req));
                            toMMIO.enq(req);
                            labelKonataLeft(lfh,current_id, $format(" MMIO ", fshow(req)));
                            mmio = True;
                            //store color
                            colorMRed.enq(False);
                        end else begin 
                            labelKonataLeft(lfh,current_id, $format(" MEM ", fshow(req)));
                            toDmem.enq(req);
                            //store color
                            colorMRed.enq(False);
                        end
                    end
                    else if (isControlInst(from_fetch.dinst)) begin
                            labelKonataLeft(lfh,current_id, $format(" Ctrl instr "));
                            data = from_fetch.pc + 4;
                    end else begin 
                        labelKonataLeft(lfh,current_id, $format(" Standard instr "));
                    end
                    let controlResult = execControl32(from_fetch.dinst.inst, from_fetch.rv1, from_fetch.rv2, imm, from_fetch.pc);
                    let nextPc = controlResult.nextPC;

                    //if the predicted next PC is not the actual PC, update epoch etc.
                    if(nextPc != from_fetch.ppc) begin
                        pc_b[0] <= nextPc;
                        epoch_b[0] <= ~epoch_b[0]; 
                        //for btb training
                        btb.update(from_fetch.pc, nextPc, controlResult.taken);
                        if(debug) $display("Redirect %x", nextPc);
                    end
        
                    let mem_business = MemBusiness { isUnsigned : unpack(isUnsigned), size : size, offset : offset, mmio: mmio};
                    e2w_b.enq(E2W{mem_business : mem_business, data : data, dinst : from_fetch.dinst, k_id : current_id});
                    labelKonataLeft(lfh,current_id, $format(" ALU output: %x" , data));
                end
                else begin
                    squashed.enq(from_fetch.k_id);
                    let fields = getInstFields(from_fetch.dinst.inst);
                    let rd_idx = fields.rd;
                    if (from_fetch.dinst.valid_rd && rd_idx != 0 ) begin
                        scoreboard_b[rd_idx][1] <= scoreboard_b[rd_idx][1] - 1;
                    end
                    if(debug) $display("Free Execute Register %x", rd_idx);
                    if (debug) $display("[Execute scoreboard : ] ", rd_idx, fshow(scoreboard_b[rd_idx][1]));
                end
            end
            //if blue empty, try red
            else if (d2e_r.notEmpty) begin
                let from_fetch = d2e_r.first();
                d2e_r.deq();
                if (debug) $display("[Execute] ", fshow(from_fetch.dinst));
                let current_id = from_fetch.k_id;
                executeKonata(lfh, current_id);
                if (from_fetch.epoch == epoch_r[0])  begin
                    let imm = getImmediate(from_fetch.dinst);
                    Bool mmio = False;
                    let data = execALU32(from_fetch.dinst.inst, from_fetch.rv1, from_fetch.rv2, imm, from_fetch.pc);
                    let isUnsigned = 0;
                    let funct3 = getInstFields(from_fetch.dinst.inst).funct3;
                    let size = funct3[1:0];
                    let addr = from_fetch.rv1 + imm;
                    Bit#(2) offset = addr[1:0];
                    if (isMemoryInst(from_fetch.dinst)) begin
                        // Technical details for load byte/halfword/word
                        let shift_amount = {offset, 3'b0};
                        let byte_en = 0;
                        case (size) matches
                        2'b00: byte_en = 4'b0001 << offset;
                        2'b01: byte_en = 4'b0011 << offset;
                        2'b10: byte_en = 4'b1111 << offset;
                        endcase
                        data = from_fetch.rv2 << shift_amount;
                        addr = {addr[31:2], 2'b0};
                        isUnsigned = funct3[2];
                        let type_mem = (from_fetch.dinst.inst[5] == 1) ? byte_en : 0;
                        let req = Mem {byte_en : type_mem,
                                addr : addr,
                                data : data};
                        if (isMMIO(addr)) begin 
                            if (debug) $display("[Execute] MMIO", fshow(req));
                            toMMIO.enq(req);
                            labelKonataLeft(lfh,current_id, $format(" MMIO ", fshow(req)));
                            mmio = True;
                            //store color
                            colorMRed.enq(True);
                        end else begin 
                            labelKonataLeft(lfh,current_id, $format(" MEM ", fshow(req)));
                            toDmem.enq(req);
                            //store color
                            colorMRed.enq(True);
                        end
                    end
                    else if (isControlInst(from_fetch.dinst)) begin
                            labelKonataLeft(lfh,current_id, $format(" Ctrl instr "));
                            data = from_fetch.pc + 4;
                    end else begin 
                        labelKonataLeft(lfh,current_id, $format(" Standard instr "));
                    end
                    let controlResult = execControl32(from_fetch.dinst.inst, from_fetch.rv1, from_fetch.rv2, imm, from_fetch.pc);
                    let nextPc = controlResult.nextPC;

                    //if the predicted next PC is not the actual PC, update epoch etc.
                    if(nextPc != from_fetch.ppc) begin
                        pc_r[0] <= nextPc;
                        epoch_r[0] <= ~epoch_r[0]; 
                        //for btb training
                        btb.update(from_fetch.pc, nextPc, controlResult.taken);
                        if(debug) $display("Redirect %x", nextPc);
                    end
        
                    let mem_business = MemBusiness { isUnsigned : unpack(isUnsigned), size : size, offset : offset, mmio: mmio};
                    e2w_r.enq(E2W{mem_business : mem_business, data : data, dinst : from_fetch.dinst, k_id : current_id});
                    labelKonataLeft(lfh,current_id, $format(" ALU output: %x" , data));
                end
                else begin
                    squashed.enq(from_fetch.k_id);
                    let fields = getInstFields(from_fetch.dinst.inst);
                    let rd_idx = fields.rd;
                    if (from_fetch.dinst.valid_rd && rd_idx != 0 ) begin
                        scoreboard_r[rd_idx][1] <= scoreboard_r[rd_idx][1] - 1;
                    end
                    if(debug) $display("Free Execute Register %x", rd_idx);
                    if (debug) $display("[Execute scoreboard : ] ", rd_idx, fshow(scoreboard_r[rd_idx][1]));
                end
            end
        end
        //d2e_r.deq();
        //colorPriority <= !colorPriority;
    endrule

    rule writeback if (!starting);
        //if there is something in the red fifo
        if (colorMRed.notEmpty) begin
            let color = colorMRed.first();
            colorPriorityWrite <= color;
        end
        else begin
            colorPriorityWrite <= !colorPriorityWrite;
        end
        //if red is priority, write to red
        if (e2w_r.notEmpty) begin
            let from_fetched = e2w_r.first();
            let current_id = from_fetched.k_id;
            writebackKonata(lfh,current_id);
            retired.enq(current_id);
            let data = from_fetched.data;
            let dInst = from_fetched.dinst;
            let fields = getInstFields(dInst.inst);
            if (isMemoryInst(dInst)) begin // (* // write_val *) 
                let resp = ?;
                if (from_fetched.mem_business.mmio) begin 
                    resp = fromMMIO.first();
    		        fromMMIO.deq();
                    colorMRed.deq();
    		    end else if(dInst.inst[5] == 0) begin // only deq for reads
                    resp = fromDmem.first();
                    fromDmem.deq();
                    colorMRed.deq();
                end
                let mem_data = resp.data;
                mem_data = mem_data >> {from_fetched.mem_business.offset ,3'b0};
                case ({pack(from_fetched.mem_business.isUnsigned), from_fetched.mem_business.size}) matches
                3'b000 : data = signExtend(mem_data[7:0]);
                3'b001 : data = signExtend(mem_data[15:0]);
                3'b100 : data = zeroExtend(mem_data[7:0]);
                3'b101 : data = zeroExtend(mem_data[15:0]);
                3'b010 : data = mem_data;
                endcase
            end
            if(debug) $display("[Writeback]", fshow(dInst));
            if (!dInst.legal) begin
                if (debug) $display("[Writeback] Illegal Inst, Drop and fault: ", fshow(dInst));
                $finish(1); // Fault
            end
            let rd_idx = fields.rd;
            if (dInst.valid_rd) begin
                if (rd_idx != 0) begin 
                    rf_r[rd_idx][0] <= data;
                    scoreboard_r[rd_idx][0] <= scoreboard_r[rd_idx][0] - 1; 
                    if (debug) $display("[Writeback scoreboard : ] ", rd_idx, fshow(scoreboard_r[rd_idx][0]));
                end
            end
            if(debug) $display("Free Writeback Register %x", rd_idx);
            e2w_r.deq();
            
        end
        else if (e2w_b.notEmpty) begin
            let from_fetched = e2w_b.first();
            let current_id = from_fetched.k_id;
            writebackKonata(lfh,current_id);
            retired.enq(current_id);
            let data = from_fetched.data;
            let dInst = from_fetched.dinst;
            let fields = getInstFields(dInst.inst);
            if (isMemoryInst(dInst)) begin // (* // write_val *)
                let resp = ?;
                if (from_fetched.mem_business.mmio) begin 
                    resp = fromMMIO.first();
                    fromMMIO.deq();
                    colorMRed.deq();
                end else if(dInst.inst[5] == 0) begin
                    resp = fromDmem.first();
                    fromDmem.deq();
                    colorMRed.deq();
                end
                let mem_data = resp.data;
                mem_data = mem_data >> {from_fetched.mem_business.offset ,3'b0};
                case ({pack(from_fetched.mem_business.isUnsigned), from_fetched.mem_business.size}) matches
                3'b000 : data = signExtend(mem_data[7:0]);
                3'b001 : data = signExtend(mem_data[15:0]);
                3'b100 : data = zeroExtend(mem_data[7:0]);
                3'b101 : data = zeroExtend(mem_data[15:0]);
                3'b010 : data = mem_data;
                endcase
            end
            if(debug) $display("[Writeback]", fshow(dInst));
            if (!dInst.legal) begin
                if (debug) $display("[Writeback] Illegal Inst, Drop and fault: ", fshow(dInst));
                $finish(1); // Fault
            end
            let rd_idx = fields.rd;
            if (dInst.valid_rd) begin
                if (rd_idx != 0) begin 
                    rf_b[rd_idx][0] <= data;
                    scoreboard_b[rd_idx][0] <= scoreboard_b[rd_idx][0] - 1; 
                    if (debug) $display("[Writeback scoreboard : ] ", rd_idx, fshow(scoreboard_b[rd_idx][0]));
                end
            end
            if(debug) $display("Free Writeback Register %x", rd_idx);
            e2w_b.deq();
        end


    endrule


    // ADMINISTRATION:

    rule administrative_konata_commit;
            retired.deq();
            let f = retired.first();
            commitKonata(lfh, f, commit_id);
    endrule

    rule administrative_konata_flush;
            squashed.deq();
            let f = squashed.first();
            squashKonata(lfh, f);
    endrule

    method ActionValue#(Mem) getIReqBlue();
        toImemBlue.deq();
        return toImemBlue.first();
    endmethod
    method Action getIRespBlue(Mem a);
        fromImemBlue.enq(a);
    endmethod
    //add additional channel for instructions
    method ActionValue#(Mem) getIReqRed();
        toImemRed.deq();
        return toImemRed.first();
    endmethod
    method Action getIRespRed(Mem a);
        fromImemRed.enq(a);
    endmethod
    method ActionValue#(Mem) getDReq();
        toDmem.deq();
        return toDmem.first();
    endmethod
    method Action getDResp(Mem a);
        fromDmem.enq(a);
    endmethod
    method ActionValue#(Mem) getMMIOReq();
        toMMIO.deq();
        return toMMIO.first();
    endmethod
    method Action getMMIOResp(Mem a);
        fromMMIO.enq(a);
    endmethod
endmodule