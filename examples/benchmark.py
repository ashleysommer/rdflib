from random import random, randint, choice
from typing import List, Tuple, Any, Optional

from rdflib import Graph, URIRef, Literal

def make_short_string():
    # Random strings of length 19
    return ''.join(chr(randint(97, 122)) for _ in range(19))

def make_med_string():
    # Random strings of length 100
    return ''.join(chr(randint(97, 122)) for _ in range(100))

def make_short_uri():
    # Random uris of length 20  http://{8char}.ai/{1char}
    host = ''.join(chr(randint(97, 122)) for _ in range(8))
    path = chr(randint(97, 122))
    return f"http://{host}.ai/{path}"

def make_med_uri():
    # Random uris of length 50  http://{20char}.org/{18char}
    host = ''.join(chr(randint(97, 122)) for _ in range(20))
    path = ''.join(chr(randint(97, 122)) for _ in range(18))
    return f"http://{host}.org/{path}"

short_string_pool = [Literal(make_short_string()) for _ in range(10_000)]
med_string_pool = [Literal(make_med_string()) for _ in range(10_000)]
short_uri_pool = [URIRef(make_short_uri()) for _ in range(10_000)]
med_uri_pool = [URIRef(make_med_uri()) for _ in range(10_000)]


def make_record() -> List[Tuple]:
    triples = []
    subject = choice(med_uri_pool)
    # record is subject with 10 properties
    for _ in range(10):
        pred_pool = choice((short_uri_pool, med_uri_pool))
        pred = choice(pred_pool)
        obj_pool = choice((short_string_pool, med_string_pool, short_uri_pool, med_uri_pool))
        obj = choice(obj_pool)
        triples.append((subject, pred, obj))
    return triples

def load_graph(g: Graph) -> Graph:
    # load a graph with 100k records
    triples_to_lookup = []
    for i in range(100_000):
        r_triples = make_record()
        if i % 100 == 0:
            triples_to_lookup.append(choice(r_triples))
        for triple in r_triples:
            g.store.add(triple, g, quoted=False)
    return g, triples_to_lookup

def lookup(triples_to_lookup: List[Tuple], g: Graph) -> Any:
    rets = []
    for triple in triples_to_lookup:
        i = choice(range(3))
        if i == 0:
            rets.append(list(g.objects(triple[0], triple[1])))
        elif i == 1:
            rets.append(list(g.predicates(triple[0], triple[2])))
        else:
            rets.append(list(g.subjects(triple[1], triple[2])))
    return rets

def run_with_store(store: Optional[Any] = None) -> Any:
    import gc
    import time
    g = Graph(store=store if store is not None else "default")
    gc.collect()
    gc.disable()
    a = time.perf_counter()
    g, _triples_to_lookup = load_graph(g)
    b = time.perf_counter()
    print(f"Graph created in {(b - a) * 1000} milliseconds")
    c = time.perf_counter()
    lookup(_triples_to_lookup, g)
    d = time.perf_counter()
    print(f"Lookup done in {(d - c) * 1000} milliseconds")

if __name__ == "__main__":
    import sys
    #from rdflib.plugins.stores.memory import StringMemory
    from rdflib.plugins.stores.memory import RDFOxMemory
    run_with_store(RDFOxMemory())
    sys.exit(0)
