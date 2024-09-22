#
#
from __future__ import annotations

from dataclasses import dataclass
from typing import (
    TYPE_CHECKING,
    Any,
    Collection,
    Dict,
    Generator,
    Iterator,
    Mapping,
    Optional,
    Set,
    Tuple,
    Union,
    overload, List,
)

from rdflib.store import Store
from rdflib.util import _coalesce
from rdflib import term
from rdflib.term import Identifier, URIRef, BNode, Literal

if TYPE_CHECKING:
    from rdflib.graph import (
        Graph,
        _ContextType,
        _ObjectType,
        _PredicateType,
        _SubjectType,
        _TriplePatternType,
        _TripleType,
    )
    from rdflib.plugins.sparql.sparql import Query, Update
    from rdflib.query import Result

__all__ = ["SimpleMemory", "Memory"]

ANY: None = None


class SimpleMemory(Store):
    """\
    A fast naive in memory implementation of a triple store.

    This triple store uses nested dictionaries to store triples. Each
    triple is stored in two such indices as follows spo[s][p][o] = 1 and
    pos[p][o][s] = 1.

    Authors: Michel Pelletier, Daniel Krech, Stefan Niederhauser
    """

    def __init__(
        self,
        configuration: Optional[str] = None,
        identifier: Optional[Identifier] = None,
    ):
        super(SimpleMemory, self).__init__(configuration)
        self.identifier = identifier

        # indexed by [subject][predicate][object]
        self.__spo: Dict[_SubjectType, Dict[_PredicateType, Dict[_ObjectType, int]]] = (
            {}
        )

        # indexed by [predicate][object][subject]
        self.__pos: Dict[_PredicateType, Dict[_ObjectType, Dict[_SubjectType, int]]] = (
            {}
        )

        # indexed by [predicate][object][subject]
        self.__osp: Dict[_ObjectType, Dict[_SubjectType, Dict[_PredicateType, int]]] = (
            {}
        )

        self.__namespace: Dict[str, URIRef] = {}
        self.__prefix: Dict[URIRef, str] = {}

    def add(
        self,
        triple: _TripleType,
        context: _ContextType,
        quoted: bool = False,
    ) -> None:
        """\
        Add a triple to the store of triples.
        """
        # add dictionary entries for spo[s][p][p] = 1 and pos[p][o][s]
        # = 1, creating the nested dictionaries where they do not yet
        # exits.
        subject, predicate, object = triple
        spo = self.__spo
        try:
            po = spo[subject]
        except:  # noqa: E722
            po = spo[subject] = {}
        try:
            o = po[predicate]
        except:  # noqa: E722
            o = po[predicate] = {}
        o[object] = 1

        pos = self.__pos
        try:
            os = pos[predicate]
        except:  # noqa: E722
            os = pos[predicate] = {}
        try:
            s = os[object]
        except:  # noqa: E722
            s = os[object] = {}
        s[subject] = 1

        osp = self.__osp
        try:
            sp = osp[object]
        except:  # noqa: E722
            sp = osp[object] = {}
        try:
            p = sp[subject]
        except:  # noqa: E722
            p = sp[subject] = {}
        p[predicate] = 1

    def remove(
        self,
        triple_pattern: _TriplePatternType,
        context: Optional[_ContextType] = None,
    ) -> None:
        for (subject, predicate, object), c in list(self.triples(triple_pattern)):
            del self.__spo[subject][predicate][object]
            del self.__pos[predicate][object][subject]
            del self.__osp[object][subject][predicate]

    def triples(
        self,
        triple_pattern: _TriplePatternType,
        context: Optional[_ContextType] = None,
    ) -> Iterator[Tuple[_TripleType, Iterator[Optional[_ContextType]]]]:
        """A generator over all the triples matching"""
        subject, predicate, object = triple_pattern
        if subject != ANY:  # subject is given
            spo = self.__spo
            if subject in spo:
                subjectDictionary = spo[subject]  # noqa: N806
                if predicate != ANY:  # subject+predicate is given
                    if predicate in subjectDictionary:
                        if object != ANY:  # subject+predicate+object is given
                            if object in subjectDictionary[predicate]:
                                yield (subject, predicate, object), self.__contexts()
                            else:  # given object not found
                                pass
                        else:  # subject+predicate is given, object unbound
                            for o in subjectDictionary[predicate].keys():
                                yield (subject, predicate, o), self.__contexts()
                    else:  # given predicate not found
                        pass
                else:  # subject given, predicate unbound
                    for p in subjectDictionary.keys():
                        if object != ANY:  # object is given
                            if object in subjectDictionary[p]:
                                yield (subject, p, object), self.__contexts()
                            else:  # given object not found
                                pass
                        else:  # object unbound
                            for o in subjectDictionary[p].keys():
                                yield (subject, p, o), self.__contexts()
            else:  # given subject not found
                pass
        elif predicate != ANY:  # predicate is given, subject unbound
            pos = self.__pos
            if predicate in pos:
                predicateDictionary = pos[predicate]  # noqa: N806
                if object != ANY:  # predicate+object is given, subject unbound
                    if object in predicateDictionary:
                        for s in predicateDictionary[object].keys():
                            yield (s, predicate, object), self.__contexts()
                    else:  # given object not found
                        pass
                else:  # predicate is given, object+subject unbound
                    for o in predicateDictionary.keys():
                        for s in predicateDictionary[o].keys():
                            yield (s, predicate, o), self.__contexts()
        elif object != ANY:  # object is given, subject+predicate unbound
            osp = self.__osp
            if object in osp:
                objectDictionary = osp[object]  # noqa: N806
                for s in objectDictionary.keys():
                    for p in objectDictionary[s].keys():
                        yield (s, p, object), self.__contexts()
        else:  # subject+predicate+object unbound
            spo = self.__spo
            for s in spo.keys():
                subjectDictionary = spo[s]  # noqa: N806
                for p in subjectDictionary.keys():
                    for o in subjectDictionary[p].keys():
                        yield (s, p, o), self.__contexts()

    def __len__(self, context: Optional[_ContextType] = None) -> int:
        # @@ optimize
        i = 0
        for triple in self.triples((None, None, None)):
            i += 1
        return i

    def bind(self, prefix: str, namespace: URIRef, override: bool = True) -> None:
        # should be identical to `Memory.bind`
        bound_namespace = self.__namespace.get(prefix)
        bound_prefix = _coalesce(
            self.__prefix.get(namespace),
            # type error: error: Argument 1 to "get" of "Mapping" has incompatible type "Optional[URIRef]"; expected "URIRef"
            self.__prefix.get(bound_namespace),  # type: ignore[arg-type]
        )
        if override:
            if bound_prefix is not None:
                del self.__namespace[bound_prefix]
            if bound_namespace is not None:
                del self.__prefix[bound_namespace]
            self.__prefix[namespace] = prefix
            self.__namespace[prefix] = namespace
        else:
            # type error: Invalid index type "Optional[URIRef]" for "Dict[URIRef, str]"; expected type "URIRef"
            self.__prefix[_coalesce(bound_namespace, namespace)] = _coalesce(  # type: ignore[index]
                bound_prefix, default=prefix
            )
            # type error: Invalid index type "Optional[str]" for "Dict[str, URIRef]"; expected type "str"
            self.__namespace[_coalesce(bound_prefix, prefix)] = _coalesce(  # type: ignore[index]
                bound_namespace, default=namespace
            )

    def namespace(self, prefix: str) -> Optional[URIRef]:
        return self.__namespace.get(prefix, None)

    def prefix(self, namespace: URIRef) -> Optional[str]:
        return self.__prefix.get(namespace, None)

    def namespaces(self) -> Iterator[Tuple[str, URIRef]]:
        for prefix, namespace in self.__namespace.items():
            yield prefix, namespace

    def __contexts(self) -> Generator[_ContextType, None, None]:
        # TODO: best way to return empty generator
        # type error: Need type annotation for "c"
        return (c for c in [])  # type: ignore[var-annotated]

    # type error: Missing return statement
    def query(  # type: ignore[return]
        self,
        query: Union[Query, str],
        initNs: Mapping[str, Any],  # noqa: N803
        initBindings: Mapping[str, Identifier],  # noqa: N803
        queryGraph: str,  # noqa: N803
        **kwargs: Any,
    ) -> Result:
        super(SimpleMemory, self).query(
            query, initNs, initBindings, queryGraph, **kwargs
        )

    def update(
        self,
        update: Union[Update, str],
        initNs: Mapping[str, Any],  # noqa: N803
        initBindings: Mapping[str, Identifier],  # noqa: N803
        queryGraph: str,  # noqa: N803
        **kwargs: Any,
    ) -> None:
        super(SimpleMemory, self).update(
            update, initNs, initBindings, queryGraph, **kwargs
        )


class Memory(Store):
    """\
    An in memory implementation of a triple store.

    Same as SimpleMemory above, but is Context-aware, Graph-aware, and Formula-aware
    Authors: Ashley Sommer
    """

    context_aware = True
    formula_aware = True
    graph_aware = True

    def __init__(
        self,
        configuration: Optional[str] = None,
        identifier: Optional[Identifier] = None,
    ):
        super(Memory, self).__init__(configuration)
        self.identifier = identifier

        # indexed by [subject][predicate][object]
        self.__spo: Dict[_SubjectType, Dict[_PredicateType, Dict[_ObjectType, int]]] = (
            {}
        )

        # indexed by [predicate][object][subject]
        self.__pos: Dict[_PredicateType, Dict[_ObjectType, Dict[_SubjectType, int]]] = (
            {}
        )

        # indexed by [predicate][object][subject]
        self.__osp: Dict[_ObjectType, Dict[_SubjectType, Dict[_PredicateType, int]]] = (
            {}
        )

        self.__namespace: Dict[str, URIRef] = {}
        self.__prefix: Dict[URIRef, str] = {}
        self.__context_obj_map: Dict[str, Graph] = {}
        self.__tripleContexts: Dict[_TripleType, Dict[Optional[str], bool]] = {}
        self.__contextTriples: Dict[Optional[str], Set[_TripleType]] = {None: set()}
        # all contexts used in store (unencoded)
        self.__all_contexts: Set[Graph] = set()
        # default context information for triples
        self.__defaultContexts: Optional[Dict[Optional[str], bool]] = None

    def add(
        self,
        triple: _TripleType,
        context: _ContextType,
        quoted: bool = False,
    ) -> None:
        """\
        Add a triple to the store of triples.
        """
        # add dictionary entries for spo[s][p][p] = 1 and pos[p][o][s]
        # = 1, creating the nested dictionaries where they do not yet
        # exits.
        Store.add(self, triple, context, quoted=quoted)
        if context is not None:
            self.__all_contexts.add(context)
        subject, predicate, object_ = triple

        spo = self.__spo
        try:
            po = spo[subject]
        except LookupError:
            po = spo[subject] = {}
        try:
            o = po[predicate]
        except LookupError:
            o = po[predicate] = {}

        try:
            _ = o[object_]
            # This cannot be reached if (s, p, o) was not inserted before.
            triple_exists = True
        except KeyError:
            o[object_] = 1
            triple_exists = False
        self.__add_triple_context(triple, triple_exists, context, quoted)

        if triple_exists:
            # No need to insert twice this triple.
            return

        pos = self.__pos
        try:
            os = pos[predicate]
        except LookupError:
            os = pos[predicate] = {}
        try:
            s = os[object_]
        except LookupError:
            s = os[object_] = {}
        s[subject] = 1

        osp = self.__osp
        try:
            sp = osp[object_]
        except LookupError:
            sp = osp[object_] = {}
        try:
            p = sp[subject]
        except LookupError:
            p = sp[subject] = {}
        p[predicate] = 1

    def remove(
        self,
        triple_pattern: _TriplePatternType,
        context: Optional[_ContextType] = None,
    ) -> None:
        req_ctx = self.__ctx_to_str(context)
        for triple, c in self.triples(triple_pattern, context=context):
            subject, predicate, object_ = triple
            for ctx in self.__get_context_for_triple(triple):
                if context is not None and req_ctx != ctx:
                    continue
                self.__remove_triple_context(triple, ctx)
            ctxs = self.__get_context_for_triple(triple, skipQuoted=True)
            if None in ctxs and (context is None or len(ctxs) == 1):
                # remove from default graph too
                self.__remove_triple_context(triple, None)
            if len(self.__get_context_for_triple(triple)) == 0:
                del self.__spo[subject][predicate][object_]
                del self.__pos[predicate][object_][subject]
                del self.__osp[object_][subject][predicate]
                del self.__tripleContexts[triple]
        if (
            req_ctx is not None
            and req_ctx in self.__contextTriples
            and len(self.__contextTriples[req_ctx]) == 0
        ):
            # all triples are removed out of this context
            # and it's not the default context so delete it
            del self.__contextTriples[req_ctx]

        if (
            triple_pattern == (None, None, None)
            and context in self.__all_contexts
            and not self.graph_aware
        ):
            # remove the whole context
            self.__all_contexts.remove(context)

    def triples(
        self,
        triple_pattern: _TriplePatternType,
        context: Optional[_ContextType] = None,
    ) -> Generator[
        Tuple[_TripleType, Generator[Optional[_ContextType], None, None]],
        None,
        None,
    ]:
        """A generator over all the triples matching"""
        req_ctx = self.__ctx_to_str(context)
        subject, predicate, object_ = triple_pattern

        # all triples case (no triple parts given as pattern)
        if subject is None and predicate is None and object_ is None:
            # Just dump all known triples from the given graph
            if req_ctx not in self.__contextTriples:
                return
            for triple in self.__contextTriples[req_ctx].copy():
                yield triple, self.__contexts(triple)

        # optimize "triple in graph" case (all parts given)
        elif subject is not None and predicate is not None and object_ is not None:
            # type error: Incompatible types in assignment (expression has type "Tuple[Optional[IdentifiedNode], Optional[IdentifiedNode], Optional[Identifier]]", variable has type "Tuple[IdentifiedNode, IdentifiedNode, Identifier]")
            # NOTE on type error: at this point, all elements of triple_pattern
            # is not None, so it has the same type as triple
            triple = triple_pattern  # type: ignore[assignment]
            try:
                _ = self.__spo[subject][predicate][object_]
                if self.__triple_has_context(triple, req_ctx):
                    yield triple, self.__contexts(triple)
            except KeyError:
                return

        elif subject is not None:  # subject is given
            spo = self.__spo
            if subject in spo:
                subjectDictionary = spo[subject]  # noqa: N806
                if predicate is not None:  # subject+predicate is given
                    if predicate in subjectDictionary:
                        if object_ is not None:  # subject+predicate+object is given
                            if object_ in subjectDictionary[predicate]:
                                triple = (subject, predicate, object_)
                                if self.__triple_has_context(triple, req_ctx):
                                    yield triple, self.__contexts(triple)
                            else:  # given object not found
                                pass
                        else:  # subject+predicate is given, object unbound
                            for o in list(subjectDictionary[predicate].keys()):
                                triple = (subject, predicate, o)
                                if self.__triple_has_context(triple, req_ctx):
                                    yield triple, self.__contexts(triple)
                    else:  # given predicate not found
                        pass
                else:  # subject given, predicate unbound
                    for p in list(subjectDictionary.keys()):
                        if object_ is not None:  # object is given
                            if object_ in subjectDictionary[p]:
                                triple = (subject, p, object_)
                                if self.__triple_has_context(triple, req_ctx):
                                    yield triple, self.__contexts(triple)
                            else:  # given object not found
                                pass
                        else:  # object unbound
                            for o in list(subjectDictionary[p].keys()):
                                triple = (subject, p, o)
                                if self.__triple_has_context(triple, req_ctx):
                                    yield triple, self.__contexts(triple)
            else:  # given subject not found
                pass
        elif predicate is not None:  # predicate is given, subject unbound
            pos = self.__pos
            if predicate in pos:
                predicateDictionary = pos[predicate]  # noqa: N806
                if object_ is not None:  # predicate+object is given, subject unbound
                    if object_ in predicateDictionary:
                        for s in list(predicateDictionary[object_].keys()):
                            triple = (s, predicate, object_)
                            if self.__triple_has_context(triple, req_ctx):
                                yield triple, self.__contexts(triple)
                    else:  # given object not found
                        pass
                else:  # predicate is given, object+subject unbound
                    for o in list(predicateDictionary.keys()):
                        for s in list(predicateDictionary[o].keys()):
                            triple = (s, predicate, o)
                            if self.__triple_has_context(triple, req_ctx):
                                yield triple, self.__contexts(triple)
        elif object_ is not None:  # object is given, subject+predicate unbound
            osp = self.__osp
            if object_ in osp:
                objectDictionary = osp[object_]  # noqa: N806
                for s in list(objectDictionary.keys()):
                    for p in list(objectDictionary[s].keys()):
                        triple = (s, p, object_)
                        if self.__triple_has_context(triple, req_ctx):
                            yield triple, self.__contexts(triple)
        else:  # subject+predicate+object unbound
            # Shouldn't get here if all other cases above worked correctly.
            spo = self.__spo
            for s in list(spo.keys()):
                subjectDictionary = spo[s]  # noqa: N806
                for p in list(subjectDictionary.keys()):
                    for o in list(subjectDictionary[p].keys()):
                        triple = (s, p, o)
                        if self.__triple_has_context(triple, req_ctx):
                            yield triple, self.__contexts(triple)

    def bind(self, prefix: str, namespace: URIRef, override: bool = True) -> None:
        # should be identical to `SimpleMemory.bind`
        bound_namespace = self.__namespace.get(prefix)
        bound_prefix = _coalesce(
            self.__prefix.get(namespace),
            # type error: error: Argument 1 to "get" of "Mapping" has incompatible type "Optional[URIRef]"; expected "URIRef"
            self.__prefix.get(bound_namespace),  # type: ignore[arg-type]
        )
        if override:
            if bound_prefix is not None:
                del self.__namespace[bound_prefix]
            if bound_namespace is not None:
                del self.__prefix[bound_namespace]
            self.__prefix[namespace] = prefix
            self.__namespace[prefix] = namespace
        else:
            # type error: Invalid index type "Optional[URIRef]" for "Dict[URIRef, str]"; expected type "URIRef"
            self.__prefix[_coalesce(bound_namespace, namespace)] = _coalesce(  # type: ignore[index]
                bound_prefix, default=prefix
            )
            # type error: Invalid index type "Optional[str]" for "Dict[str, URIRef]"; expected type "str"
            # type error: Incompatible types in assignment (expression has type "Optional[URIRef]", target has type "URIRef")
            self.__namespace[_coalesce(bound_prefix, prefix)] = _coalesce(  # type: ignore[index]
                bound_namespace, default=namespace
            )

    def namespace(self, prefix: str) -> Optional[URIRef]:
        return self.__namespace.get(prefix, None)

    def prefix(self, namespace: URIRef) -> Optional[str]:
        return self.__prefix.get(namespace, None)

    def namespaces(self) -> Iterator[Tuple[str, URIRef]]:
        for prefix, namespace in self.__namespace.items():
            yield prefix, namespace

    def contexts(
        self, triple: Optional[_TripleType] = None
    ) -> Generator[_ContextType, None, None]:
        if triple is None or triple == (None, None, None):
            return (context for context in self.__all_contexts)

        subj, pred, obj = triple
        try:
            _ = self.__spo[subj][pred][obj]
            return self.__contexts(triple)
        except KeyError:
            return (_ for _ in [])

    def __len__(self, context: Optional[_ContextType] = None) -> int:
        ctx = self.__ctx_to_str(context)
        if ctx not in self.__contextTriples:
            return 0
        return len(self.__contextTriples[ctx])

    def add_graph(self, graph: Graph) -> None:
        if not self.graph_aware:
            Store.add_graph(self, graph)
        else:
            self.__all_contexts.add(graph)

    def remove_graph(self, graph: Graph) -> None:
        if not self.graph_aware:
            Store.remove_graph(self, graph)
        else:
            self.remove((None, None, None), graph)
            try:
                self.__all_contexts.remove(graph)
            except KeyError:
                pass  # we didn't know this graph, no problem

    # internal utility methods below
    def __add_triple_context(
        self,
        triple: _TripleType,
        triple_exists: bool,
        context: Optional[_ContextType],
        quoted: bool,
    ) -> None:
        """add the given context to the set of contexts for the triple"""
        ctx = self.__ctx_to_str(context)
        quoted = bool(quoted)
        if triple_exists:
            # we know the triple exists somewhere in the store
            try:
                triple_context = self.__tripleContexts[triple]
            except KeyError:
                # triple exists with default ctx info
                # start with a copy of the default ctx info
                # type error: Item "None" of "Optional[Dict[Optional[str], bool]]" has no attribute "copy"
                triple_context = self.__tripleContexts[triple] = (
                    self.__defaultContexts.copy()  # type: ignore[union-attr]
                )

            triple_context[ctx] = quoted

            if not quoted:
                triple_context[None] = quoted

        else:
            # the triple didn't exist before in the store
            if quoted:  # this context only
                triple_context = self.__tripleContexts[triple] = {ctx: quoted}
            else:  # default context as well
                triple_context = self.__tripleContexts[triple] = {
                    ctx: quoted,
                    None: quoted,
                }

        # if the triple is not quoted add it to the default context
        if not quoted:
            self.__contextTriples[None].add(triple)

        # always add the triple to given context, making sure it's initialized
        if ctx not in self.__contextTriples:
            self.__contextTriples[ctx] = set()
        self.__contextTriples[ctx].add(triple)

        # if this is the first ever triple in the store, set default ctx info
        if self.__defaultContexts is None:
            self.__defaultContexts = triple_context
        # if the context info is the same as default, no need to store it
        if triple_context == self.__defaultContexts:
            del self.__tripleContexts[triple]

    def __get_context_for_triple(
        self, triple: _TripleType, skipQuoted: bool = False  # noqa: N803
    ) -> Collection[Optional[str]]:
        """return a list of contexts (str) for the triple, skipping
        quoted contexts if skipQuoted==True"""

        ctxs = self.__tripleContexts.get(triple, self.__defaultContexts)

        if not skipQuoted:
            # type error: Item "None" of "Optional[Dict[Optional[str], bool]]" has no attribute "keys"
            return ctxs.keys()  # type: ignore[union-attr]

        # type error: Item "None" of "Optional[Dict[Optional[str], bool]]" has no attribute "items"
        return [ctx for ctx, quoted in ctxs.items() if not quoted]  # type: ignore[union-attr]

    def __triple_has_context(self, triple: _TripleType, ctx: Optional[str]) -> bool:
        """return True if the triple exists in the given context"""
        # type error: Unsupported right operand type for in ("Optional[Dict[Optional[str], bool]]")
        return ctx in self.__tripleContexts.get(triple, self.__defaultContexts)  # type: ignore[operator]

    def __remove_triple_context(self, triple: _TripleType, ctx):
        """remove the context from the triple"""
        # type error: Item "None" of "Optional[Dict[Optional[str], bool]]" has no attribute "copy"
        ctxs = self.__tripleContexts.get(triple, self.__defaultContexts).copy()  # type: ignore[union-attr]
        del ctxs[ctx]
        if ctxs == self.__defaultContexts:
            del self.__tripleContexts[triple]
        else:
            self.__tripleContexts[triple] = ctxs
        self.__contextTriples[ctx].remove(triple)

    @overload
    def __ctx_to_str(self, ctx: _ContextType) -> str: ...

    @overload
    def __ctx_to_str(self, ctx: None) -> None: ...

    def __ctx_to_str(self, ctx: Optional[_ContextType]) -> Optional[str]:
        if ctx is None:
            return None
        try:
            # ctx could be a graph. In that case, use its identifier
            ctx_str = "{}:{}".format(ctx.identifier.__class__.__name__, ctx.identifier)
            self.__context_obj_map[ctx_str] = ctx
            return ctx_str
        except AttributeError:
            # otherwise, ctx should be a URIRef or BNode or str
            # NOTE on type errors: This is actually never called with ctx value as str in all unit tests, so this seems like it should just not be here.
            # type error: Subclass of "Graph" and "str" cannot exist: would have incompatible method signatures
            if isinstance(ctx, str):  # type: ignore[unreachable]
                # type error: Statement is unreachable
                ctx_str = "{}:{}".format(ctx.__class__.__name__, ctx)  # type: ignore[unreachable]
                if ctx_str in self.__context_obj_map:
                    return ctx_str
                self.__context_obj_map[ctx_str] = ctx
                return ctx_str
            raise RuntimeError("Cannot use that type of object as a Graph context")

    def __contexts(self, triple: _TripleType) -> Generator[_ContextType, None, None]:
        """return a generator for all the non-quoted contexts
        (dereferenced) the encoded triple appears in"""
        # type error: Argument 2 to "get" of "Mapping" has incompatible type "str"; expected "Optional[Graph]"
        return (
            self.__context_obj_map.get(ctx_str, ctx_str)  # type: ignore[arg-type]
            for ctx_str in self.__get_context_for_triple(triple, skipQuoted=True)
            if ctx_str is not None
        )

    # type error: Missing return statement
    def query(  # type: ignore[return]
        self,
        query: Union[Query, str],
        initNs: Mapping[str, Any],  # noqa: N803
        initBindings: Mapping[str, Identifier],  # noqa: N803
        queryGraph: str,  # noqa: N803
        **kwargs,
    ) -> Result:
        super(Memory, self).query(query, initNs, initBindings, queryGraph, **kwargs)

    def update(
        self,
        update: Union[Update, Any],
        initNs: Mapping[str, Any],  # noqa: N803
        initBindings: Mapping[str, Identifier],  # noqa: N803
        queryGraph: str,  # noqa: N803
        **kwargs,
    ) -> None:
        super(Memory, self).update(update, initNs, initBindings, queryGraph, **kwargs)


class StringMemory(Store):
    """\
    An in memory implementation of a triple store.

    Same as SimpleMemory above, but is Context-aware, Graph-aware, and Formula-aware
    Authors: Ashley Sommer
    """

    context_aware = True
    formula_aware = True
    graph_aware = True

    def __init__(
        self,
        configuration: Optional[str] = None,
        identifier: Optional[Identifier] = None,
    ):
        super(StringMemory, self).__init__(configuration)
        self.identifier = identifier

        # indexed by [subject][predicate][object]
        self.__spo: Dict[str, Dict[str, Dict[str, int]]] = (
            {}
        )

        # indexed by [predicate][object][subject]
        self.__pos: Dict[str, Dict[str, Dict[str, int]]] = (
            {}
        )

        # indexed by [predicate][object][subject]
        self.__osp: Dict[str, Dict[str, Dict[str, int]]] = (
            {}
        )

        self.__namespace: Dict[str, URIRef] = {}
        self.__prefix: Dict[URIRef, str] = {}
        self.__context_obj_map: Dict[str, Graph] = {}
        self.__tripleContexts: Dict[Tuple[str, str, str], Dict[Optional[str], bool]] = {}
        self.__contextTriples: Dict[Optional[str], Set[Tuple[str, str, str]]] = {None: set()}
        # all contexts used in store (unencoded)
        self.__all_contexts: Set[Graph] = set()
        # default context information for triples
        self.__defaultContexts: Optional[Dict[Optional[str], bool]] = None

    @staticmethod
    def str_rep(s, p, o) -> Tuple[Optional[str], Optional[str], Optional[str]]:
        str_s: Optional[str]
        if s is None:
            str_s = None
        elif isinstance(s, term.Literal):
            lit = str(s)
            d = "" if s.datatype is None else str(s.datatype)
            l = "" if s.language is None else str(s.language)
            str_s = f"l|{lit}|{d}|{l}"
        elif isinstance(s, term.BNode):
            str_s = "_"+str(s)
        else:
            str_s = str(s)
        str_p: Optional[str]
        if p is None:
            str_p = None
        elif isinstance(p, term.Literal):
            lit = str(p)
            d = "" if p.datatype is None else str(p.datatype)
            l = "" if p.language is None else str(p.language)
            str_p = f"l|{lit}|{d}|{l}"
        elif isinstance(p, term.BNode):
            str_p = "_"+str(p)
        else:
            str_p = str(p)
        str_o: Optional[str]
        if o is None:
            str_o = None
        elif isinstance(o, term.Literal):
            lit = str(o)
            d = "" if o.datatype is None else str(o.datatype)
            l = "" if o.language is None else str(o.language)
            str_o = f"l|{lit}|{d}|{l}"
        elif isinstance(o, term.BNode):
            str_o = "_"+str(o)
        else:
            str_o = str(o)
        return str_s, str_p, str_o

    @staticmethod
    def from_str_rep(s: Optional[str], p: Optional[str], o: Optional[str]) -> Tuple[Optional[Any], Optional[Any], Optional[Any]]:
        if s is None:
            from_s = None
        elif s.startswith("l|"):
            lit, d, l = s[2:].split("|")
            from_s = Literal(lit, datatype=None if len(d) < 1 else URIRef(d), lang=None if len(l) < 1 else l)
        elif s.startswith("_"):
            from_s = BNode(s[1:])
        else:
            from_s = URIRef(s)

        if p is None:
            from_p = None
        elif p.startswith("l|"):
            lit, d, l = p[2:].split("|")
            from_p = Literal(lit, datatype=None if len(d) < 1 else URIRef(d), lang=None if len(l) < 1 else l)
        elif p.startswith("_"):
            from_p = BNode(p[1:])
        else:
            from_p = URIRef(p)

        if o is None:
            from_o = None
        elif o.startswith("l|"):
            lit, d, l = o[2:].split("|")
            from_o = Literal(lit, datatype=None if len(d) < 1 else URIRef(d), lang=None if len(l) < 1 else l)
        elif o.startswith("_"):
            from_o = BNode(o[1:])
        else:
            from_o = URIRef(o)
        return from_s, from_p, from_o

    def add(
        self,
        triple: _TripleType,
        context: _ContextType,
        quoted: bool = False,
    ) -> None:
        """\
        Add a triple to the store of triples.
        """
        # add dictionary entries for spo[s][p][p] = 1 and pos[p][o][s]
        # = 1, creating the nested dictionaries where they do not yet
        # exits.
        Store.add(self, triple, context, quoted=quoted)
        if context is not None:
            self.__all_contexts.add(context)
        subject, predicate, object_ = triple
        s_triple = self.str_rep(subject, predicate, object_)
        s_str, p_str, o_str = s_triple
        spo = self.__spo
        try:
            po = spo[s_str]
        except LookupError:
            po = spo[s_str] = {}
        try:
            o = po[p_str]
        except LookupError:
            o = po[p_str] = {}

        try:
            _ = o[o_str]
            # This cannot be reached if (s, p, o) was not inserted before.
            triple_exists = True
        except KeyError:
            o[o_str] = 1
            triple_exists = False
        self.__add_triple_context(s_triple, triple_exists, context, quoted)

        if triple_exists:
            # No need to insert twice this triple.
            return

        pos = self.__pos
        try:
            os = pos[p_str]
        except LookupError:
            os = pos[p_str] = {}
        try:
            s = os[o_str]
        except LookupError:
            s = os[o_str] = {}
        s[s_str] = 1

        osp = self.__osp
        try:
            sp = osp[o_str]
        except LookupError:
            sp = osp[o_str] = {}
        try:
            p = sp[s_str]
        except LookupError:
            p = sp[s_str] = {}
        p[p_str] = 1

    def remove(
        self,
        triple_pattern: _TriplePatternType,
        context: Optional[_ContextType] = None,
    ) -> None:
        req_ctx = self.__ctx_to_str(context)
        for triple, c in self.triples(triple_pattern, context=context):
            subject, predicate, object_ = triple
            str_triple = self.str_rep(subject, predicate, object_)
            str_s, str_p, str_o = str_triple
            for ctx in self.__get_context_for_triple(str_triple):
                if context is not None and req_ctx != ctx:
                    continue
                self.__remove_triple_context(str_triple, ctx)
            ctxs = self.__get_context_for_triple(str_triple, skipQuoted=True)
            if None in ctxs and (context is None or len(ctxs) == 1):
                # remove from default graph too
                self.__remove_triple_context(str_triple, None)

            if len(self.__get_context_for_triple(str_triple)) == 0:
                del self.__spo[str_s][str_p][str_o]
                del self.__pos[str_p][str_o][str_s]
                del self.__osp[str_o][str_s][str_p]
                del self.__tripleContexts[str_triple]
        if (
            req_ctx is not None
            and req_ctx in self.__contextTriples
            and len(self.__contextTriples[req_ctx]) == 0
        ):
            # all triples are removed out of this context
            # and it's not the default context so delete it
            del self.__contextTriples[req_ctx]

        if (
            triple_pattern == (None, None, None)
            and context in self.__all_contexts
            and not self.graph_aware
        ):
            # remove the whole context
            self.__all_contexts.remove(context)

    def triples(
        self,
        triple_pattern: _TriplePatternType,
        context: Optional[_ContextType] = None,
    ) -> Generator[
        Tuple[_TripleType, Generator[Optional[_ContextType], None, None]],
        None,
        None,
    ]:
        """A generator over all the triples matching"""
        req_ctx = self.__ctx_to_str(context)
        subject, predicate, object_ = triple_pattern
        if subject is None and predicate is None and object_ is None:
            # Just dump all known triples from the given graph
            if req_ctx not in self.__contextTriples:
                return
            for str_triple in self.__contextTriples[req_ctx].copy():
                triple = self.from_str_rep(str_triple[0], str_triple[1], str_triple[2])
                yield triple, self.__contexts(str_triple)
        else:
            str_triple_pattern = self.str_rep(subject, predicate, object_)
            for str_triple, _contexts in self.rep_triples(str_triple_pattern, req_ctx):
                yield self.from_str_rep(str_triple[0], str_triple[1], str_triple[2]), _contexts


    def rep_triples(
        self,
        str_triple_pattern: Tuple[Optional[str], Optional[str], Optional[str]],
        req_ctx: Optional[str] = None,
    ) -> Generator[
        Tuple[_TripleType, Generator[Optional[_ContextType], None, None]],
        None,
        None,
    ]:
        """A generator over all the triples matching"""
        subject, predicate, object_ = str_triple_pattern
        # all triples case (no triple parts given as pattern)
        if subject is None and predicate is None and object_ is None:
            # Just dump all known triples from the given graph
            if req_ctx not in self.__contextTriples:
                return
            for triple in self.__contextTriples[req_ctx].copy():
                yield triple, self.__contexts(triple)

        # optimize "triple in graph" case (all parts given)
        elif subject is not None and predicate is not None and object_ is not None:
            # type error: Incompatible types in assignment (expression has type "Tuple[Optional[IdentifiedNode], Optional[IdentifiedNode], Optional[Identifier]]", variable has type "Tuple[IdentifiedNode, IdentifiedNode, Identifier]")
            # NOTE on type error: at this point, all elements of triple_pattern
            # is not None, so it has the same type as triple
            triple = triple_pattern  # type: ignore[assignment]
            try:
                _ = self.__spo[subject][predicate][object_]
                if self.__triple_has_context(triple, req_ctx):
                    yield triple, self.__contexts(triple)
            except KeyError:
                return

        elif subject is not None:  # subject is given
            spo = self.__spo
            if subject in spo:
                subjectDictionary = spo[subject]  # noqa: N806
                if predicate is not None:  # subject+predicate is given
                    if predicate in subjectDictionary:
                        if object_ is not None:  # subject+predicate+object is given
                            if object_ in subjectDictionary[predicate]:
                                triple = (subject, predicate, object_)
                                if self.__triple_has_context(triple, req_ctx):
                                    yield triple, self.__contexts(triple)
                            else:  # given object not found
                                pass
                        else:  # subject+predicate is given, object unbound
                            for o in list(subjectDictionary[predicate].keys()):
                                triple = (subject, predicate, o)
                                if self.__triple_has_context(triple, req_ctx):
                                    yield triple, self.__contexts(triple)
                    else:  # given predicate not found
                        pass
                else:  # subject given, predicate unbound
                    for p in list(subjectDictionary.keys()):
                        if object_ is not None:  # object is given
                            if object_ in subjectDictionary[p]:
                                triple = (subject, p, object_)
                                if self.__triple_has_context(triple, req_ctx):
                                    yield triple, self.__contexts(triple)
                            else:  # given object not found
                                pass
                        else:  # object unbound
                            for o in list(subjectDictionary[p].keys()):
                                triple = (subject, p, o)
                                if self.__triple_has_context(triple, req_ctx):
                                    yield triple, self.__contexts(triple)
            else:  # given subject not found
                pass
        elif predicate is not None:  # predicate is given, subject unbound
            pos = self.__pos
            if predicate in pos:
                predicateDictionary = pos[predicate]  # noqa: N806
                if object_ is not None:  # predicate+object is given, subject unbound
                    if object_ in predicateDictionary:
                        for s in list(predicateDictionary[object_].keys()):
                            triple = (s, predicate, object_)
                            if self.__triple_has_context(triple, req_ctx):
                                yield triple, self.__contexts(triple)
                    else:  # given object not found
                        pass
                else:  # predicate is given, object+subject unbound
                    for o in list(predicateDictionary.keys()):
                        for s in list(predicateDictionary[o].keys()):
                            triple = (s, predicate, o)
                            if self.__triple_has_context(triple, req_ctx):
                                yield triple, self.__contexts(triple)
        elif object_ is not None:  # object is given, subject+predicate unbound
            osp = self.__osp
            if object_ in osp:
                objectDictionary = osp[object_]  # noqa: N806
                for s in list(objectDictionary.keys()):
                    for p in list(objectDictionary[s].keys()):
                        triple = (s, p, object_)
                        if self.__triple_has_context(triple, req_ctx):
                            yield triple, self.__contexts(triple)
        else:  # subject+predicate+object unbound
            # Shouldn't get here if all other cases above worked correctly.
            spo = self.__spo
            for s in list(spo.keys()):
                subjectDictionary = spo[s]  # noqa: N806
                for p in list(subjectDictionary.keys()):
                    for o in list(subjectDictionary[p].keys()):
                        triple = (s, p, o)
                        if self.__triple_has_context(triple, req_ctx):
                            yield triple, self.__contexts(triple)

    def bind(self, prefix: str, namespace: URIRef, override: bool = True) -> None:
        # should be identical to `SimpleMemory.bind`
        bound_namespace = self.__namespace.get(prefix)
        bound_prefix = _coalesce(
            self.__prefix.get(namespace),
            # type error: error: Argument 1 to "get" of "Mapping" has incompatible type "Optional[URIRef]"; expected "URIRef"
            self.__prefix.get(bound_namespace),  # type: ignore[arg-type]
        )
        if override:
            if bound_prefix is not None:
                del self.__namespace[bound_prefix]
            if bound_namespace is not None:
                del self.__prefix[bound_namespace]
            self.__prefix[namespace] = prefix
            self.__namespace[prefix] = namespace
        else:
            # type error: Invalid index type "Optional[URIRef]" for "Dict[URIRef, str]"; expected type "URIRef"
            self.__prefix[_coalesce(bound_namespace, namespace)] = _coalesce(  # type: ignore[index]
                bound_prefix, default=prefix
            )
            # type error: Invalid index type "Optional[str]" for "Dict[str, URIRef]"; expected type "str"
            # type error: Incompatible types in assignment (expression has type "Optional[URIRef]", target has type "URIRef")
            self.__namespace[_coalesce(bound_prefix, prefix)] = _coalesce(  # type: ignore[index]
                bound_namespace, default=namespace
            )

    def namespace(self, prefix: str) -> Optional[URIRef]:
        return self.__namespace.get(prefix, None)

    def prefix(self, namespace: URIRef) -> Optional[str]:
        return self.__prefix.get(namespace, None)

    def namespaces(self) -> Iterator[Tuple[str, URIRef]]:
        for prefix, namespace in self.__namespace.items():
            yield prefix, namespace

    def contexts(
        self, triple: Optional[_TripleType] = None
    ) -> Generator[_ContextType, None, None]:
        if triple is None or triple == (None, None, None):
            return (context for context in self.__all_contexts)

        subj, pred, obj = triple
        str_triple = self.str_rep(subj, pred, obj)
        str_s, str_p, str_o = str_triple
        try:
            _ = self.__spo[str_s][str_p][str_o]
            return self.__contexts(str_triple)
        except KeyError:
            return (_ for _ in [])

    def __len__(self, context: Optional[_ContextType] = None) -> int:
        ctx = self.__ctx_to_str(context)
        if ctx not in self.__contextTriples:
            return 0
        return len(self.__contextTriples[ctx])

    def add_graph(self, graph: Graph) -> None:
        if not self.graph_aware:
            Store.add_graph(self, graph)
        else:
            self.__all_contexts.add(graph)

    def remove_graph(self, graph: Graph) -> None:
        if not self.graph_aware:
            Store.remove_graph(self, graph)
        else:
            self.remove((None, None, None), graph)
            try:
                self.__all_contexts.remove(graph)
            except KeyError:
                pass  # we didn't know this graph, no problem

    # internal utility methods below
    def __add_triple_context(
        self,
        triple: Tuple[str, str, str],
        triple_exists: bool,
        context: Optional[_ContextType],
        quoted: bool,
    ) -> None:
        """add the given context to the set of contexts for the triple"""
        ctx = self.__ctx_to_str(context)
        quoted = bool(quoted)
        if triple_exists:
            # we know the triple exists somewhere in the store
            try:
                triple_context = self.__tripleContexts[triple]
            except KeyError:
                # triple exists with default ctx info
                # start with a copy of the default ctx info
                # type error: Item "None" of "Optional[Dict[Optional[str], bool]]" has no attribute "copy"
                triple_context = self.__tripleContexts[triple] = (
                    self.__defaultContexts.copy()  # type: ignore[union-attr]
                )

            triple_context[ctx] = quoted

            if not quoted:
                triple_context[None] = quoted

        else:
            # the triple didn't exist before in the store
            if quoted:  # this context only
                triple_context = self.__tripleContexts[triple] = {ctx: quoted}
            else:  # default context as well
                triple_context = self.__tripleContexts[triple] = {
                    ctx: quoted,
                    None: quoted,
                }

        # if the triple is not quoted add it to the default context
        if not quoted:
            self.__contextTriples[None].add(triple)

        # always add the triple to given context, making sure it's initialized
        if ctx not in self.__contextTriples:
            self.__contextTriples[ctx] = set()
        self.__contextTriples[ctx].add(triple)

        # if this is the first ever triple in the store, set default ctx info
        if self.__defaultContexts is None:
            self.__defaultContexts = triple_context
        # if the context info is the same as default, no need to store it
        if triple_context == self.__defaultContexts:
            del self.__tripleContexts[triple]

    def __get_context_for_triple(
        self, triple: Tuple[str, str, str], skipQuoted: bool = False  # noqa: N803
    ) -> Collection[Optional[str]]:
        """return a list of contexts (str) for the triple, skipping
        quoted contexts if skipQuoted==True"""

        ctxs = self.__tripleContexts.get(triple, self.__defaultContexts)

        if not skipQuoted:
            # type error: Item "None" of "Optional[Dict[Optional[str], bool]]" has no attribute "keys"
            return ctxs.keys()  # type: ignore[union-attr]

        # type error: Item "None" of "Optional[Dict[Optional[str], bool]]" has no attribute "items"
        return [ctx for ctx, quoted in ctxs.items() if not quoted]  # type: ignore[union-attr]

    def __triple_has_context(self, triple: Tuple[str, str, str], ctx: Optional[str]) -> bool:
        """return True if the triple exists in the given context"""
        # type error: Unsupported right operand type for in ("Optional[Dict[Optional[str], bool]]")
        return ctx in self.__tripleContexts.get(triple, self.__defaultContexts)  # type: ignore[operator]

    def __remove_triple_context(self, triple: Tuple[str, str, str], ctx):
        """remove the context from the triple"""
        # type error: Item "None" of "Optional[Dict[Optional[str], bool]]" has no attribute "copy"
        ctxs = self.__tripleContexts.get(triple, self.__defaultContexts).copy()  # type: ignore[union-attr]
        del ctxs[ctx]
        if ctxs == self.__defaultContexts:
            del self.__tripleContexts[triple]
        else:
            self.__tripleContexts[triple] = ctxs
        self.__contextTriples[ctx].remove(triple)

    @overload
    def __ctx_to_str(self, ctx: _ContextType) -> str: ...

    @overload
    def __ctx_to_str(self, ctx: None) -> None: ...

    def __ctx_to_str(self, ctx: Optional[_ContextType]) -> Optional[str]:
        if ctx is None:
            return None
        try:
            # ctx could be a graph. In that case, use its identifier
            ctx_str = "{}:{}".format(ctx.identifier.__class__.__name__, ctx.identifier)
            self.__context_obj_map[ctx_str] = ctx
            return ctx_str
        except AttributeError:
            # otherwise, ctx should be a URIRef or BNode or str
            # NOTE on type errors: This is actually never called with ctx value as str in all unit tests, so this seems like it should just not be here.
            # type error: Subclass of "Graph" and "str" cannot exist: would have incompatible method signatures
            if isinstance(ctx, str):  # type: ignore[unreachable]
                # type error: Statement is unreachable
                ctx_str = "{}:{}".format(ctx.__class__.__name__, ctx)  # type: ignore[unreachable]
                if ctx_str in self.__context_obj_map:
                    return ctx_str
                self.__context_obj_map[ctx_str] = ctx
                return ctx_str
            raise RuntimeError("Cannot use that type of object as a Graph context")

    def __contexts(self, triple: Tuple[str, str, str]) -> Generator[_ContextType, None, None]:
        """return a generator for all the non-quoted contexts
        (dereferenced) the encoded triple appears in"""
        # type error: Argument 2 to "get" of "Mapping" has incompatible type "str"; expected "Optional[Graph]"
        return (
            self.__context_obj_map.get(ctx_str, ctx_str)  # type: ignore[arg-type]
            for ctx_str in self.__get_context_for_triple(triple, skipQuoted=True)
            if ctx_str is not None
        )

    # type error: Missing return statement
    def query(  # type: ignore[return]
        self,
        query: Union[Query, str],
        initNs: Mapping[str, Any],  # noqa: N803
        initBindings: Mapping[str, Identifier],  # noqa: N803
        queryGraph: str,  # noqa: N803
        **kwargs,
    ) -> Result:
        super(StringMemory, self).query(query, initNs, initBindings, queryGraph, **kwargs)

    def update(
        self,
        update: Union[Update, Any],
        initNs: Mapping[str, Any],  # noqa: N803
        initBindings: Mapping[str, Identifier],  # noqa: N803
        queryGraph: str,  # noqa: N803
        **kwargs,
    ) -> None:
        super(StringMemory, self).update(update, initNs, initBindings, queryGraph, **kwargs)

@dataclass
class RDFOxQuadNode:
    quad: Tuple[_SubjectType, _PredicateType, _ObjectType, str]
    range_from: int
    range_to: int
    previous: Optional['RDFOxQuadNode']
    previous_s: Optional['RDFOxQuadNode']
    previous_p: Optional['RDFOxQuadNode']
    previous_o: Optional['RDFOxQuadNode']
    previous_c: Optional['RDFOxQuadNode']
    previous_po: Optional['RDFOxQuadNode']
    previous_sp: Optional['RDFOxQuadNode']

class RDFOxMemory(Store):
    """\
    A memory store based on RDFox and inspired by the new Memory quadstore
    in Oxigraph.

    Authors: Ashley Sommer
    """

    context_aware = True
    formula_aware = True
    graph_aware = True

    def __init__(
        self,
        configuration: Optional[str] = None,
        identifier: Optional[Identifier] = None,
    ):
        super(RDFOxMemory, self).__init__(configuration)
        self.identifier = identifier
        self.quad_set: Dict[Tuple[_SubjectType, _PredicateType, _ObjectType, str], RDFOxQuadNode] = {}
        self.last_inserted_quad: Optional[RDFOxQuadNode] = None
        self.last_quad_by_s: Dict[_SubjectType, Tuple[RDFOxQuadNode, int]] = {}
        self.last_quad_by_p: Dict[_PredicateType, Tuple[RDFOxQuadNode, int]] = {}
        self.last_quad_by_o: Dict[_ObjectType, Tuple[RDFOxQuadNode, int]] = {}
        self.last_quad_by_po: Dict[Tuple[_PredicateType, _ObjectType], Tuple[RDFOxQuadNode, int]] = {}
        self.last_quad_by_sp: Dict[Tuple[_SubjectType, _PredicateType], Tuple[RDFOxQuadNode, int]] = {}
        self.last_quad_by_c: Dict[str, Tuple[RDFOxQuadNode, int]] = {}
        self.transactions = 0

        self.__namespace: Dict[str, URIRef] = {}
        self.__prefix: Dict[URIRef, str] = {}
        self.__context_obj_map: Dict[str, Graph] = {}
        # all contexts used in store (unencoded)
        self.__all_contexts: Set[Graph] = set()


    def add(
        self,
        triple: _TripleType,
        context: _ContextType,
        quoted: bool = False,
    ) -> None:
        """\
        Add a triple to the store of triples.
        """
        # add dictionary entries for spo[s][p][p] = 1 and pos[p][o][s]
        # = 1, creating the nested dictionaries where they do not yet
        # exits.
        Store.add(self, triple, context, quoted=quoted)
        self.transactions = t = self.transactions + 1
        if context is not None:
            self.__all_contexts.add(context)
            req_ctx = self.__ctx_to_str(context)
        else:
            req_ctx = ""
        subject, predicate, object_ = triple
        quad = (subject, predicate, object_, req_ctx)
        try:
            existing_qnode = self.quad_set[quad]
            if existing_qnode.range_to > 0:
                # This was previously deleted.
                # TODO: Re-adding it will undelete it for all snapshots
                existing_qnode.range_to = 0
            return
        except LookupError:
            pass
        previous = self.last_inserted_quad
        previous_by_s, s_count = self.last_quad_by_s.get(subject, (None, 0))
        previous_by_p, p_count = self.last_quad_by_p.get(predicate, (None, 0))
        previous_by_o, o_count = self.last_quad_by_o.get(object_, (None, 0))
        previous_by_c, c_count = self.last_quad_by_c.get(req_ctx, (None, 0))
        previous_by_po, po_count = self.last_quad_by_po.get((predicate, object_), (None, 0))
        previous_by_sp, sp_count = self.last_quad_by_sp.get((subject, predicate), (None, 0))
        q = RDFOxQuadNode(quad, t, 0, previous, previous_by_s, previous_by_p, previous_by_o, previous_by_c, previous_by_po, previous_by_sp)
        self.quad_set[quad] = q
        self.last_inserted_quad = q
        self.last_quad_by_s[subject] = (q, s_count + 1)
        self.last_quad_by_p[predicate] = (q, p_count + 1)
        self.last_quad_by_o[object_] = (q, o_count + 1)
        self.last_quad_by_c[req_ctx] = (q, c_count + 1)
        self.last_quad_by_po[(predicate, object_)] = (q, po_count + 1)
        self.last_quad_by_sp[(subject, predicate)] = (q, sp_count + 1)

    def remove(
        self,
        triple_pattern: _TriplePatternType,
        context: Optional[_ContextType] = None,
    ) -> None:
        if context is not None:
            req_ctx = self.__ctx_to_str(context)
        else:
            req_ctx = ""
        self.transactions = t = self.transactions + 1
        for triple, c in self.triples(triple_pattern, context=context):
            subject, predicate, object_ = triple
            quad_node = self.quad_set.get((subject, predicate, object_, req_ctx), None)
            if quad_node:
                quad_node.range_to = t
        # TODO: Remove whole context if it is empty
        return

    def triples(
        self,
        triple_pattern: _TriplePatternType,
        context: Optional[_ContextType] = None,
    ) -> Generator[
        Tuple[_TripleType, Generator[Optional[_ContextType], None, None]],
        None,
        None,
    ]:
        """A generator over all the triples matching"""
        if context is not None:
            req_ctx = self.__ctx_to_str(context)
        else:
            req_ctx = ""
        t = self.transactions
        subject, predicate, object_ = triple_pattern
        qset_count = len(self.quad_set)
        if predicate is not None and object_ is not None:
            po_start, po_count = self.last_quad_by_po.get((predicate, object_), (None, 0))
        else:
            po_start = None
            po_count = qset_count
        if subject is not None and predicate is not None:
            sp_start, sp_count = self.last_quad_by_sp.get((subject, predicate), (None, 0))
        else:
            sp_start = None
            sp_count = qset_count
        if subject is not None:
            s_start, s_count = self.last_quad_by_s.get(subject, (None, 0))
        else:
            s_start = None
            s_count = qset_count
        if predicate is not None:
            p_start, p_count = self.last_quad_by_p.get(predicate, (None, 0))
        else:
            p_start = None
            p_count = qset_count
        if object_ is not None:
            o_start, o_count = self.last_quad_by_o.get(object_, (None, 0))
        else:
            o_start = None
            o_count = qset_count
        if context is not None:
            if len(self.__all_contexts) == 1 and context in self.__all_contexts:
                c_start = None
                c_count = 1
                ignore_context = True
            else:
                c_start, c_count = self.last_quad_by_c.get(req_ctx, (None, 0))
                ignore_context = False
        else:
            c_start = None
            c_count = qset_count
            ignore_context = False

        if po_start is not None and (
            po_count <= sp_count and
            po_count <= s_count and
            (ignore_context or po_count <= c_count)
        ):
            next_q = po_start
            while next_q is not None:
                # if next_q.range_from <= t and (
                #     next_q.range_to == 0 or
                #     next_q.range_to > t
                # ):
                quad = next_q.quad
                if (subject is None or quad[0] == subject) \
                    and (ignore_context or (context is None or quad[3] == req_ctx)):
                    yield (quad[0], quad[1], quad[2]), None
                next_q = next_q.previous_po
        elif sp_start is not None and (
            sp_count <= o_count and
            (ignore_context or sp_count <= c_count)
        ):
            next_q = sp_start
            while next_q is not None:
                # if next_q.range_from <= t and (
                #     next_q.range_to == 0 or
                #     next_q.range_to > t
                # ):
                quad = next_q.quad
                if (object_ is None or quad[2] == object_) \
                    and (ignore_context or (context is None or quad[3] == req_ctx)):
                    yield (quad[0], quad[1], quad[2]), None
                next_q = next_q.previous_sp
        elif s_start is not None and (
            s_count <= p_count and
            s_count <= o_count and
            (ignore_context or s_count <= c_count)
        ):
            #print(f"Looking up by subject {subject}", flush=True)
            next_q = s_start
            while next_q is not None:
                # if next_q.range_from <= t and (
                #   next_q.range_to == 0 or
                #   next_q.range_to > t
                # ):
                quad = next_q.quad
                if (predicate is None or quad[1] == predicate) \
                    and (object_ is None or quad[2] == object_) \
                    and (ignore_context or (context is None or quad[3] == req_ctx)):
                    yield (quad[0], quad[1], quad[2]), None
                next_q = next_q.previous_s

        elif p_start is not None and (
            p_count <= o_count and
            (ignore_context or p_count <= c_count)
        ):
            #print(f"Looking up by predicate {predicate}", flush=True)
            next_q = p_start
            while next_q is not None:
                # if next_q.range_from <= t and (
                #     next_q.range_to == 0 or
                #     next_q.range_to > t
                # ):
                quad = next_q.quad
                if (subject is None or quad[0] == subject) \
                    and (object_ is None or quad[2] == object_) \
                    and (ignore_context or (context is None or quad[3] == req_ctx)):
                    yield (quad[0], quad[1], quad[2]), None
                next_q = next_q.previous_p

        elif o_start is not None and (ignore_context or o_count <= c_count):
            #print(f"Looking up by object {object_}", flush=True)
            next_q = o_start
            while next_q is not None:
                # if next_q.range_from <= t and (
                #     next_q.range_to == 0 or
                #     next_q.range_to > t
                # ):
                quad = next_q.quad
                if (subject is None or quad[0] == subject) \
                    and (predicate is None or quad[1] == predicate) \
                    and (ignore_context or (context is None or quad[3] == req_ctx)):
                    yield (quad[0], quad[1], quad[2]), None
                next_q = next_q.previous_o

        elif c_start is not None:
            #print(f"Looking up by context {context}", flush=True)
            next_q = c_start
            while next_q is not None:
                # if next_q.range_from <= t and (
                #     next_q.range_to == 0 or
                #     next_q.range_to > t
                # ):
                quad = next_q.quad
                if (subject is None or quad[0] == subject) \
                    and (predicate is None or quad[1] == predicate) \
                    and (object_ is None or quad[2] == object_):
                    yield (quad[0], quad[1], quad[2]), None
                next_q = next_q.previous_c
        else:
            # all triples case (no triple parts given as pattern)
            for qnode in self.quad_set.values():
                # if qnode.range_from <= t and (
                #     qnode.range_to == 0 or
                #     qnode.range_to > t
                # ):
                quad = qnode.quad
                if (subject is None or quad[0] == subject) \
                    and (predicate is None or quad[1] == predicate) \
                    and (object_ is None or quad[2] == object_) \
                    and (ignore_context or (context is None or quad[3] == req_ctx)):
                    yield (quad[0], quad[1], quad[2]), None

    def bind(self, prefix: str, namespace: URIRef, override: bool = True) -> None:
        # should be identical to `SimpleMemory.bind`
        bound_namespace = self.__namespace.get(prefix)
        bound_prefix = _coalesce(
            self.__prefix.get(namespace),
            # type error: error: Argument 1 to "get" of "Mapping" has incompatible type "Optional[URIRef]"; expected "URIRef"
            self.__prefix.get(bound_namespace),  # type: ignore[arg-type]
        )
        if override:
            if bound_prefix is not None:
                del self.__namespace[bound_prefix]
            if bound_namespace is not None:
                del self.__prefix[bound_namespace]
            self.__prefix[namespace] = prefix
            self.__namespace[prefix] = namespace
        else:
            # type error: Invalid index type "Optional[URIRef]" for "Dict[URIRef, str]"; expected type "URIRef"
            self.__prefix[_coalesce(bound_namespace, namespace)] = _coalesce(  # type: ignore[index]
                bound_prefix, default=prefix
            )
            # type error: Invalid index type "Optional[str]" for "Dict[str, URIRef]"; expected type "str"
            # type error: Incompatible types in assignment (expression has type "Optional[URIRef]", target has type "URIRef")
            self.__namespace[_coalesce(bound_prefix, prefix)] = _coalesce(  # type: ignore[index]
                bound_namespace, default=namespace
            )

    def namespace(self, prefix: str) -> Optional[URIRef]:
        return self.__namespace.get(prefix, None)

    def prefix(self, namespace: URIRef) -> Optional[str]:
        return self.__prefix.get(namespace, None)

    def namespaces(self) -> Iterator[Tuple[str, URIRef]]:
        for prefix, namespace in self.__namespace.items():
            yield prefix, namespace

    def contexts(
        self, triple: Optional[_TripleType] = None
    ) -> Generator[_ContextType, None, None]:
        if triple is None or triple == (None, None, None):
            return (context for context in self.__all_contexts)

        subj, pred, obj = triple
        try:
            _ = self.__spo[subj][pred][obj]
            return self.__contexts(triple)
        except KeyError:
            return (_ for _ in [])

    def __len__(self, context: Optional[_ContextType] = None) -> int:
        if context is not None:
            req_ctx = self.__ctx_to_str(context)
            if req_ctx not in self.last_quad_by_c:
                return 0
            _, c_count = self.last_quad_by_c[req_ctx]
            return c_count
        else:
            return len(self.quad_set)

    def add_graph(self, graph: Graph) -> None:
        if not self.graph_aware:
            Store.add_graph(self, graph)
        else:
            self.__all_contexts.add(graph)

    def remove_graph(self, graph: Graph) -> None:
        if not self.graph_aware:
            Store.remove_graph(self, graph)
        else:
            self.remove((None, None, None), graph)
            try:
                self.__all_contexts.remove(graph)
            except KeyError:
                pass  # we didn't know this graph, no problem

    # internal utility methods below
    def __add_triple_context(
        self,
        triple: _TripleType,
        triple_exists: bool,
        context: Optional[_ContextType],
        quoted: bool,
    ) -> None:
        """add the given context to the set of contexts for the triple"""
        ctx = self.__ctx_to_str(context)
        quoted = bool(quoted)
        if triple_exists:
            # we know the triple exists somewhere in the store
            try:
                triple_context = self.__tripleContexts[triple]
            except KeyError:
                # triple exists with default ctx info
                # start with a copy of the default ctx info
                # type error: Item "None" of "Optional[Dict[Optional[str], bool]]" has no attribute "copy"
                triple_context = self.__tripleContexts[triple] = (
                    self.__defaultContexts.copy()  # type: ignore[union-attr]
                )

            triple_context[ctx] = quoted

            if not quoted:
                triple_context[None] = quoted

        else:
            # the triple didn't exist before in the store
            if quoted:  # this context only
                triple_context = self.__tripleContexts[triple] = {ctx: quoted}
            else:  # default context as well
                triple_context = self.__tripleContexts[triple] = {
                    ctx: quoted,
                    None: quoted,
                }

        # if the triple is not quoted add it to the default context
        if not quoted:
            self.__contextTriples[None].add(triple)

        # always add the triple to given context, making sure it's initialized
        if ctx not in self.__contextTriples:
            self.__contextTriples[ctx] = set()
        self.__contextTriples[ctx].add(triple)

        # if this is the first ever triple in the store, set default ctx info
        if self.__defaultContexts is None:
            self.__defaultContexts = triple_context
        # if the context info is the same as default, no need to store it
        if triple_context == self.__defaultContexts:
            del self.__tripleContexts[triple]

    def __get_context_for_triple(
        self, triple: _TripleType, skipQuoted: bool = False  # noqa: N803
    ) -> Collection[Optional[str]]:
        """return a list of contexts (str) for the triple, skipping
        quoted contexts if skipQuoted==True"""

        ctxs = self.__tripleContexts.get(triple, self.__defaultContexts)

        if not skipQuoted:
            # type error: Item "None" of "Optional[Dict[Optional[str], bool]]" has no attribute "keys"
            return ctxs.keys()  # type: ignore[union-attr]

        # type error: Item "None" of "Optional[Dict[Optional[str], bool]]" has no attribute "items"
        return [ctx for ctx, quoted in ctxs.items() if not quoted]  # type: ignore[union-attr]

    def __triple_has_context(self, triple: _TripleType, ctx: Optional[str]) -> bool:
        """return True if the triple exists in the given context"""
        # type error: Unsupported right operand type for in ("Optional[Dict[Optional[str], bool]]")
        return ctx in self.__tripleContexts.get(triple, self.__defaultContexts)  # type: ignore[operator]

    def __remove_triple_context(self, triple: _TripleType, ctx):
        """remove the context from the triple"""
        # type error: Item "None" of "Optional[Dict[Optional[str], bool]]" has no attribute "copy"
        ctxs = self.__tripleContexts.get(triple, self.__defaultContexts).copy()  # type: ignore[union-attr]
        del ctxs[ctx]
        if ctxs == self.__defaultContexts:
            del self.__tripleContexts[triple]
        else:
            self.__tripleContexts[triple] = ctxs
        self.__contextTriples[ctx].remove(triple)

    @overload
    def __ctx_to_str(self, ctx: _ContextType) -> str: ...

    @overload
    def __ctx_to_str(self, ctx: None) -> None: ...

    def __ctx_to_str(self, ctx: Optional[_ContextType]) -> Optional[str]:
        if ctx is None:
            return None
        try:
            # ctx could be a graph. In that case, use its identifier
            ctx_str = "{}:{}".format(ctx.identifier.__class__.__name__, ctx.identifier)
            self.__context_obj_map[ctx_str] = ctx
            return ctx_str
        except AttributeError:
            # otherwise, ctx should be a URIRef or BNode or str
            # NOTE on type errors: This is actually never called with ctx value as str in all unit tests, so this seems like it should just not be here.
            # type error: Subclass of "Graph" and "str" cannot exist: would have incompatible method signatures
            if isinstance(ctx, str):  # type: ignore[unreachable]
                # type error: Statement is unreachable
                ctx_str = "{}:{}".format(ctx.__class__.__name__, ctx)  # type: ignore[unreachable]
                if ctx_str in self.__context_obj_map:
                    return ctx_str
                self.__context_obj_map[ctx_str] = ctx
                return ctx_str
            raise RuntimeError("Cannot use that type of object as a Graph context")

    def __contexts(self, triple: _TripleType) -> Generator[_ContextType, None, None]:
        """return a generator for all the non-quoted contexts
        (dereferenced) the encoded triple appears in"""
        # type error: Argument 2 to "get" of "Mapping" has incompatible type "str"; expected "Optional[Graph]"
        return (
            self.__context_obj_map.get(ctx_str, ctx_str)  # type: ignore[arg-type]
            for ctx_str in self.__get_context_for_triple(triple, skipQuoted=True)
            if ctx_str is not None
        )

    # type error: Missing return statement
    def query(  # type: ignore[return]
        self,
        query: Union[Query, str],
        initNs: Mapping[str, Any],  # noqa: N803
        initBindings: Mapping[str, Identifier],  # noqa: N803
        queryGraph: str,  # noqa: N803
        **kwargs,
    ) -> Result:
        super(RDFOxMemory, self).query(query, initNs, initBindings, queryGraph, **kwargs)

    def update(
        self,
        update: Union[Update, Any],
        initNs: Mapping[str, Any],  # noqa: N803
        initBindings: Mapping[str, Identifier],  # noqa: N803
        queryGraph: str,  # noqa: N803
        **kwargs,
    ) -> None:
        super(RDFOxMemory, self).update(update, initNs, initBindings, queryGraph, **kwargs)
