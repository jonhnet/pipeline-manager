module Types {
  type Page = nat
  datatype Request = Request(page: Page, seqnum: nat)
}

module CBF {
  import opened Types

  datatype Label =
    | IncrementLabel(req: Page)
    | DecrementLabel(req: Page)

  datatype Variables = Variables()
  {
    // weird extra "peek-only" state interface
    predicate IsLocked(page: Page)
    {
      true // TODO
    }
  }


  predicate Increment(v: Variables, v': Variables, page: Page)
  {
    true // TODO
  }

  predicate Decrement(v: Variables, v': Variables, page: Page)
  {
    true // TODO
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

  type Fifo = seq<Request>
  type Cache = set<Request>

  datatype Variables = Variables(
    cache: Cache,
    fifo: Fifo,
    cacheFilter: CBF.Variables,
    fifoFilter: CBF.Variables)

  predicate AdmitNow(v: Variables, v': Variables, req: Request)
  {
    && !(v.cacheFilter.IsLocked(req.page) || v.fifoFilter.IsLocked(req.page))
    && CBF.Next(v.cacheFilter, v'.cacheFilter, CBF.IncrementLabel(req.page))
    && v' == v.(
      cache := v.cache + {req},
      cacheFilter := v'.cacheFilter // not-UNCHANGED
      )
  }

  predicate AdmitFifo(v: Variables, v': Variables, req: Request)
  {
    && (v.cacheFilter.IsLocked(req.page) || v.fifoFilter.IsLocked(req.page))
    && CBF.Next(v.fifoFilter, v'.fifoFilter, CBF.IncrementLabel(req.page))
    && v' == v.(
      fifo := v.fifo + [req],
      fifoFilter := v'.fifoFilter // not-UNCHANGED
      )
  }

  predicate ReleaseFifo(v: Variables, v': Variables, req: Request)
  {
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
  predicate NoBypass(v: Variables)
  {
  }

  // If a page isn't in the cache, a matching request must not enter the fifo
  // Can't actually achieve this with a conservative (but not capricious) fifo
  predicate NoStalling(v: Variables)
  {
  }
}
