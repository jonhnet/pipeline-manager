module Types {
  type Page = nat
  datatype Request = Request(page: Page, seqnum: nat)
}

module CBF {
  import opened Types

  datatype Label =
    | IncrementLabel(page: Page)
    | DecrementLabel(page: Page)

  datatype Variables = Variables(
    counts: imap<Page, int>
  )
  {
    predicate WF() {
      forall page :: page in counts
    }

    // weird extra "peek-only" state interface
    predicate IsLocked(page: Page)
      requires WF()
    {
      counts[page] > 0
    }
  }

  predicate Init(v: Variables)
  {
    && v.WF()
    && (forall page :: v.counts[page] == 0)
  }

  predicate Increment(v: Variables, v': Variables, page: Page)
  {
    && v.WF()
    && v' == v.(counts := v.counts[page := v.counts[page] + 1])
  }

  predicate Decrement(v: Variables, v': Variables, page: Page)
  {
    && v.WF()
    && v' == v.(counts := v.counts[page := v.counts[page] - 1])
  }

  predicate Next(v: Variables, v': Variables, lbl: Label)
  {
    match lbl
      case IncrementLabel(page) => Increment(v, v', page)
      case DecrementLabel(page) => Decrement(v, v', page)
  }

}

module System {
  import opened Types
  import CBF

  type Cache = set<Request>
  type Fifo = seq<Request>

  datatype Variables = Variables(
    cache: Cache,
    fifo: Fifo,
    cacheFilter: CBF.Variables,
    fifoFilter: CBF.Variables)
  {
    predicate WF() {
      && cacheFilter.WF()
      && fifoFilter.WF()
    }
  }

  predicate Init(v: Variables)
  {
    && v.cache == {}
    && v.fifo == []
    && CBF.Init(v.cacheFilter)
    && CBF.Init(v.fifoFilter)
  }

  predicate AdmitNowEnabled(v: Variables, req: Request)
  {
    && v.WF()
    && !(v.cacheFilter.IsLocked(req.page) || v.fifoFilter.IsLocked(req.page))
  }
  predicate AdmitNow(v: Variables, v': Variables, req: Request)
  {
    && v.WF()
    && AdmitNowEnabled(v, req)
    && CBF.Next(v.cacheFilter, v'.cacheFilter, CBF.IncrementLabel(req.page))
    && v' == v.(
      cache := v.cache + {req},
      cacheFilter := v'.cacheFilter // not-UNCHANGED
      )
  }

  predicate AdmitFifo(v: Variables, v': Variables, req: Request)
  {
    && v.WF()
    && !AdmitNowEnabled(v, req)
    && CBF.Next(v.fifoFilter, v'.fifoFilter, CBF.IncrementLabel(req.page))
    && v' == v.(
      fifo := v.fifo + [req],
      fifoFilter := v'.fifoFilter // not-UNCHANGED
      )
  }

  predicate ReleaseFifo(v: Variables, v': Variables, req: Request)
  {
    && v.WF()
    && 0 < |v.fifo|
    && req == v.fifo[0]   // Request must be the first thing in line
    && !v.cacheFilter.IsLocked(req.page)
    && CBF.Next(v.cacheFilter, v'.cacheFilter, CBF.IncrementLabel(req.page))
    && CBF.Next(v.fifoFilter, v'.fifoFilter, CBF.DecrementLabel(req.page))
    && v' == v.(
      cache := v.cache + {req},
      fifo := v.fifo[1..],  // defifo the fifo
      cacheFilter := v'.cacheFilter, // not-UNCHANGED
      fifoFilter := v'.fifoFilter // not-UNCHANGED
      )
  }

  predicate Retire(v: Variables, v': Variables, req: Request)
  {
    && v.WF()
    && req in v.cache
    && CBF.Next(v.cacheFilter, v'.cacheFilter, CBF.DecrementLabel(req.page))
    && v' == v.(
      cache := v.cache - {req},
      cacheFilter := v'.cacheFilter // not-UNCHANGED
      )
  }

  datatype Step =
    | AdmitNowStep(req: Request)
    | AdmitFifoStep(req: Request)
    | ReleaseFifoStep(req: Request)
    | RetireStep(req: Request)

  predicate NextStep(v: Variables, v': Variables, step: Step)
  {
    match step
      case AdmitNowStep(req) => AdmitNow(v, v', req)
      case AdmitFifoStep(req) => AdmitFifo(v, v', req)
      case ReleaseFifoStep(req) => ReleaseFifo(v, v', req)
      case RetireStep(req) => Retire(v, v', req)
  }

  predicate Next(v: Variables, v': Variables)
  {
    exists step :: NextStep(v, v', step)
  }
}

module SystemProof {
  import opened Types
  import opened System

  // If a page is in the fifo, a matching request must enter the fifo
  predicate NoBypass(v: Variables, req: Request)
  {
    (exists idx :: 0 <= idx < |v.fifo| && v.fifo[idx].page == req.page)
      ==> !AdmitNowEnabled(v, req)
  }

  // If a page isn't in the cache, a matching request must not enter the fifo
  // Can't actually achieve this with a conservative (but not capricious) fifo
  predicate NoStalling(v: Variables, req: Request)
  {
    (forall activeReq | activeReq in v.cache :: activeReq.page != req.page)
      ==> AdmitNowEnabled(v, req)
  }

  // Theorem statement
  predicate Safety(v: Variables)
  {
    && (forall req :: NoBypass(v, req))
    && (forall req :: NoStalling(v, req))
  }

  // Proof machinery

  predicate NoBypassEquiv(v: Variables, req: Request)
  {
    (forall idx :: 0 <= idx < |v.fifo| && v.fifo[idx].page != req.page)
      || !AdmitNowEnabled(v, req)
  }

  predicate Inv(v: Variables)
  {
    && Safety(v)
  }

  // Theorem proof: Inductive conditions for []Safety
  lemma InitImpliesInv(v: Variables)
    requires Init(v)
    ensures Inv(v)
  {
  }

  lemma NextPreservesInv(v: Variables, v': Variables)
    requires Inv(v)
    requires Next(v, v')
    ensures Inv(v')
  {
  }

  lemma InvImpliesSafety(v: Variables)
    requires Inv(v)
    ensures Safety(v)
  {
  }
}
