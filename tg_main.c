
/*--------------------------------------------------------------------*/
/*--- Taintgrind: The Taint Analysis Valgrind tool.               tg_main.c ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of Taintgrind, the Taint Analysis Valgrind tool,
   which traces the propagation of tainted inputs in the program.

   Copyright (C) 2002-2011 Prof James Moriarty
      professormoriartyj@gmail.com

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA
   02111-1307, USA.

   The GNU General Public License is contained in the file COPYING.
*/

#include "pub_tool_basics.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_options.h"
#include "pub_tool_machine.h"     // VG_(fnptr_to_fnentry)

static Bool clo_trace_mem    = True;


/*------------------------------------------------------------*/
/*--- Stuff for --trace-mem                                ---*/
/*------------------------------------------------------------*/

#define MAX_DSIZE    512

typedef
   IRExpr 
   IRAtom;

typedef 
   enum { Event_Ir, Event_Dr, Event_Dw, Event_Dm }
   EventKind;

typedef
   struct {
      EventKind  ekind;
      IRAtom*    addr;
      Int        size;
   }
   Event;

/* Up to this many unnotified events are allowed.  Must be at least two,
   so that reads and writes to the same address can be merged into a modify.
   Beyond that, larger numbers just potentially induce more spilling due to
   extending live ranges of address temporaries. */
#define N_EVENTS 4

/* Maintain an ordered list of memory events which are outstanding, in
   the sense that no IR has yet been generated to do the relevant
   helper calls.  The SB is scanned top to bottom and memory events
   are added to the end of the list, merging with the most recent
   notified event where possible (Dw immediately following Dr and
   having the same size and EA can be merged).

   This merging is done so that for architectures which have
   load-op-store instructions (x86, amd64), the instr is treated as if
   it makes just one memory reference (a modify), rather than two (a
   read followed by a write at the same address).

   At various points the list will need to be flushed, that is, IR
   generated from it.  That must happen before any possible exit from
   the block (the end, or an IRStmt_Exit).  Flushing also takes place
   when there is no space to add a new event.

   If we require the simulation statistics to be up to date with
   respect to possible memory exceptions, then the list would have to
   be flushed before each memory reference.  That's a pain so we don't
   bother.

   Flushing the list consists of walking it start to end and emitting
   instrumentation IR for each event, in the order in which they
   appear. */

static Event events[N_EVENTS];
static Int   events_used = 0;


static VG_REGPARM(2) void trace_instr(Addr addr, SizeT size)
{
   VG_(printf)("I  %08lx,%lu\n", addr, size);
}

static VG_REGPARM(2) void trace_load(Addr addr, SizeT size)
{
   VG_(printf)(" L %08lx,%lu\n", addr, size);
}

static VG_REGPARM(2) void trace_store(Addr addr, SizeT size)
{
   VG_(printf)(" S %08lx,%lu\n", addr, size);
}

static VG_REGPARM(2) void trace_modify(Addr addr, SizeT size)
{
   VG_(printf)(" M %08lx,%lu\n", addr, size);
}


static void flushEvents(IRSB* sb)
{
   Int        i;
   Char*      helperName;
   void*      helperAddr;
   IRExpr**   argv;
   IRDirty*   di;
   Event*     ev;

   for (i = 0; i < events_used; i++) {

      ev = &events[i];
      
      // Decide on helper fn to call and args to pass it.
      switch (ev->ekind) {
         case Event_Ir: helperName = "trace_instr";
                        helperAddr =  trace_instr;  break;

         case Event_Dr: helperName = "trace_load";
                        helperAddr =  trace_load;   break;

         case Event_Dw: helperName = "trace_store";
                        helperAddr =  trace_store;  break;

         case Event_Dm: helperName = "trace_modify";
                        helperAddr =  trace_modify; break;
         default:
            tl_assert(0);
      }

      // Add the helper.
      argv = mkIRExprVec_2( ev->addr, mkIRExpr_HWord( ev->size ) );
      di   = unsafeIRDirty_0_N( /*regparms*/2, 
                                helperName, VG_(fnptr_to_fnentry)( helperAddr ),
                                argv );
      addStmtToIRSB( sb, IRStmt_Dirty(di) );
   }

   events_used = 0;
}

// WARNING:  If you aren't interested in instruction reads, you can omit the
// code that adds calls to trace_instr() in flushEvents().  However, you
// must still call this function, addEvent_Ir() -- it is necessary to add
// the Ir events to the events list so that merging of paired load/store
// events into modify events works correctly.
static void addEvent_Ir ( IRSB* sb, IRAtom* iaddr, UInt isize )
{
    Event* evt;
    tl_assert(clo_trace_mem);
    tl_assert( (VG_MIN_INSTR_SZB <= isize && isize <= VG_MAX_INSTR_SZB)
            || VG_CLREQ_SZB == isize );
    if (events_used == N_EVENTS)
      flushEvents(sb);
    tl_assert(events_used >= 0 && events_used < N_EVENTS);
    evt = &events[events_used];
    evt->ekind = Event_Ir;
    evt->addr  = iaddr;
    evt->size  = isize;
    events_used++;
}
static
void addEvent_Dr ( IRSB* sb, IRAtom* daddr, Int dsize )
{
    Event* evt;
    tl_assert(clo_trace_mem);
    tl_assert(isIRAtom(daddr));
    tl_assert(dsize >= 1 && dsize <= MAX_DSIZE);
    if (events_used == N_EVENTS)
      flushEvents(sb);
    tl_assert(events_used >= 0 && events_used < N_EVENTS);
    evt = &events[events_used];
    evt->ekind = Event_Dr;
    evt->addr  = daddr;
    evt->size  = dsize;
    events_used++;
}
static
void addEvent_Dw ( IRSB* sb, IRAtom* daddr, Int dsize )
{
    Event* lastEvt;
    Event* evt;
    tl_assert(clo_trace_mem);
    tl_assert(isIRAtom(daddr));
    tl_assert(dsize >= 1 && dsize <= MAX_DSIZE);

    // Is it possible to merge this write with the preceding read?
    lastEvt = &events[events_used-1];
    if (events_used > 0
    && lastEvt->ekind == Event_Dr
    && lastEvt->size  == dsize
    && eqIRAtom(lastEvt->addr, daddr))
    {
      lastEvt->ekind = Event_Dm;
      return;
    }

    // No.  Add as normal.
    if (events_used == N_EVENTS)
      flushEvents(sb);
    tl_assert(events_used >= 0 && events_used < N_EVENTS);
    evt = &events[events_used];
    evt->ekind = Event_Dw;
    evt->size  = dsize;
    evt->addr  = daddr;
    events_used++;
}

/*------------------------------------------------------------*/
/*--- Basic tool functions                                 ---*/
/*------------------------------------------------------------*/

static void tg_post_clo_init(void)
{
}

static
IRSB* tg_instrument ( VgCallbackClosure* closure,
                      IRSB* sbIn,
                      VexGuestLayout* layout, 
                      VexGuestExtents* vge,
                      IRType gWordTy, IRType hWordTy )
{
    IRDirty*   di;
    Int        i;
    IRSB*      sbOut;
    Char       fnname[100];
    IRType     type;
    IRTypeEnv* tyenv = sbIn->tyenv;
    if (gWordTy != hWordTy) {
        /* We don't currently support this case. */
        VG_(tool_panic)("host/guest word size mismatch");
    }

    /* Set up SB */
    sbOut = deepCopyIRSBExceptStmts(sbIn);

    // Copy verbatim any IR preamble preceding the first IMark
    i = 0;
    while (i < sbIn->stmts_used && sbIn->stmts[i]->tag != Ist_IMark) {
        addStmtToIRSB( sbOut, sbIn->stmts[i] );
        i++;
    }
    
    for (/*use current i*/; i < sbIn->stmts_used; i++) {
        IRStmt* st = sbIn->stmts[i];
        if (!st || st->tag == Ist_NoOp) continue;

        switch (st->tag) {
           case Ist_NoOp:
           case Ist_AbiHint:
           case Ist_Put:
           case Ist_PutI:
           case Ist_MBE:
              addStmtToIRSB( sbOut, st );
              break;

           case Ist_IMark:
              if (clo_trace_mem) {
                 // WARNING: do not remove this function call, even if you
                 // aren't interested in instruction reads.  See the comment
                 // above the function itself for more detail.
                 addEvent_Ir( sbOut, mkIRExpr_HWord( (HWord)st->Ist.IMark.addr ),
                              st->Ist.IMark.len );
              }
              addStmtToIRSB( sbOut, st );
              break;

           case Ist_WrTmp:
              // Add a call to trace_load() if --trace-mem=yes.
              if (clo_trace_mem) {
                 IRExpr* data = st->Ist.WrTmp.data;
                 if (data->tag == Iex_Load) {
                    addEvent_Dr( sbOut, data->Iex.Load.addr,
                                 sizeofIRType(data->Iex.Load.ty) );
                 }
              }
              addStmtToIRSB( sbOut, st );
              break;

           case Ist_Store:
              if (clo_trace_mem) {
                 IRExpr* data  = st->Ist.Store.data;
                 addEvent_Dw( sbOut, st->Ist.Store.addr,
                              sizeofIRType(typeOfIRExpr(tyenv, data)) );
              }
              addStmtToIRSB( sbOut, st );
              break;

           case Ist_Dirty: {
              if (clo_trace_mem) {
                 Int      dsize;
                 IRDirty* d = st->Ist.Dirty.details;
                 if (d->mFx != Ifx_None) {
                    // This dirty helper accesses memory.  Collect the details.
                    tl_assert(d->mAddr != NULL);
                    tl_assert(d->mSize != 0);
                    dsize = d->mSize;
                    if (d->mFx == Ifx_Read || d->mFx == Ifx_Modify)
                       addEvent_Dr( sbOut, d->mAddr, dsize );
                    if (d->mFx == Ifx_Write || d->mFx == Ifx_Modify)
                       addEvent_Dw( sbOut, d->mAddr, dsize );
                 } else {
                    tl_assert(d->mAddr == NULL);
                    tl_assert(d->mSize == 0);
                 }
              }
              addStmtToIRSB( sbOut, st );
              break;
           }

           case Ist_CAS: {
              /* We treat it as a read and a write of the location.  I
                 think that is the same behaviour as it was before IRCAS
                 was introduced, since prior to that point, the Vex
                 front ends would translate a lock-prefixed instruction
                 into a (normal) read followed by a (normal) write. */
              Int    dataSize;
              IRType dataTy;
              IRCAS* cas = st->Ist.CAS.details;
              tl_assert(cas->addr != NULL);
              tl_assert(cas->dataLo != NULL);
              dataTy   = typeOfIRExpr(tyenv, cas->dataLo);
              dataSize = sizeofIRType(dataTy);
              if (clo_trace_mem) {
                 addEvent_Dr( sbOut, cas->addr, dataSize );
                 addEvent_Dw( sbOut, cas->addr, dataSize );
              }
              addStmtToIRSB( sbOut, st );
              break;
           }

           case Ist_LLSC: {
              IRType dataTy;
              if (st->Ist.LLSC.storedata == NULL) {
                 /* LL */
                 dataTy = typeOfIRTemp(tyenv, st->Ist.LLSC.result);
                 if (clo_trace_mem)
                    addEvent_Dr( sbOut, st->Ist.LLSC.addr,
                                        sizeofIRType(dataTy) );
              } else {
                 /* SC */
                 dataTy = typeOfIRExpr(tyenv, st->Ist.LLSC.storedata);
                 if (clo_trace_mem)
                    addEvent_Dw( sbOut, st->Ist.LLSC.addr,
                                        sizeofIRType(dataTy) );
              }
              addStmtToIRSB( sbOut, st );
              break;
           }

           case Ist_Exit:
              if (clo_trace_mem) {
                 flushEvents(sbOut);
              }

              addStmtToIRSB( sbOut, st );      // Original statement
              break;

           default:
              tl_assert(0);
        }
    }
    if (clo_trace_mem) {
        /* At the end of the sbIn.  Flush outstandings. */
        flushEvents(sbOut);
    }
    return sbOut;
}

static void tg_fini(Int exitcode)
{
}

static void tg_pre_clo_init(void)
{
   VG_(details_name)            ("Taintgrind");
   VG_(details_version)         ("0.1");
   VG_(details_description)     ("CS510 Valgrind tool");
   VG_(details_copyright_author)(
      "Copyright (C) 2002-2011, and GNU GPL'd, by Prof James Moriarty.");
   VG_(details_bug_reports_to)  (VG_BUGS_TO);

   VG_(details_avg_translation_sizeB) ( 275 );

   VG_(basic_tool_funcs)        (tg_post_clo_init,
                                 tg_instrument,
                                 tg_fini);

   /* No needs, no core events to track */
}

VG_DETERMINE_INTERFACE_VERSION(tg_pre_clo_init)

/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/
