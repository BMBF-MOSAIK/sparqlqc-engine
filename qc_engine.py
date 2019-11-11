import networkx as nx
import requests
from rdflib.plugins.sparql.algebra import translateQuery, pprintAlgebra, simplify
from rdflib.plugins.sparql.parser import parseQuery



def networkx_multidigraph_to_rdflib(nx_multigraph):
    from rdflib import Graph, Literal, BNode, Namespace, RDF, URIRef

    g = Graph()

    for nx_edge_data in nx_multigraph.edges.data():
        g.add( (nx_edge_data[0], nx_edge_data[2]['e'], nx_edge_data[1]) )

    return g


def draw_graph(g):
    import matplotlib.pyplot as plt
    import networkx as nx
    pos=nx.spring_layout(g)
    nx.draw(g, pos)
    nx.draw_networkx_labels(g, pos=pos)
    nx.draw_networkx_edge_labels(g, pos)
    plt.show()


def sparql_to_rgraph(query):
    """
    Transform SPARQL query into its R-graph representation.
    All BNodes are scoped within their BGPs and assigned a fresh and unique BNode label.
    All non-projection variables are assigned a fresh and unique BNode label on global scope.
    :param query: SPARQL algebra expression
    :return: rdflib.Graph
    """
    import networkx as nx
    import rdflib
    from rdflib import URIRef, BNode, Literal
    from rdflib.namespace import RDF

    def ground_projected_variables(r_graph):
        """
        Ground projected variables to avoid their removal during minimisation.
        :param r_graph:
        :return:
        """
        proj_vars = set(r_graph.objects(None, rdflib.term.URIRef("http://www.dfki.de/voc#var")))
        for proj_var in proj_vars:
            r_graph.skolemize(new_graph=r_graph, bnode=rdflib.term.BNode(proj_var))
            r_graph.remove((None, None, rdflib.term.BNode(proj_var)))
        return r_graph

    def sparql_iter(expr, ctx, ctx_graph):
        """
        Traverse SPARQL algebra expression and build rdflib.Graph
        :param expr: SPARQL algebra expression
        :param ctx: rdflib.Identifier as ctx node
        :return: rdflib.Graph for SPARQL query expression expr
        """

        # handles a triple pattern expression
        if isinstance(expr, tuple):
            # each triple pattern is a subgraph of its ctx node
            triple = BNode()
            ctx_graph.add((triple, RDF.type, URIRef("http://www.dfki.de/voc#TriplePattern")))
            ctx_graph.add((ctx, URIRef("http://www.dfki.de/voc#arg"), triple))

            if isinstance(expr[0], rdflib.term.URIRef):
                ctx_graph.add((triple, URIRef("http://www.dfki.de/voc#s"), URIRef(expr[0])))
            elif isinstance(expr[0], rdflib.term.Literal):
                ctx_graph.add((triple, URIRef("http://www.dfki.de/voc#s"), Literal(expr[0])))
            elif isinstance(expr[0], rdflib.term.BNode):
                # blank nodes are scoped to the basic graph pattern.
                ctx_graph.add((triple, URIRef("http://www.dfki.de/voc#s"), BNode(ctx.__str__() + "__" + expr[0])))
            elif isinstance(expr[0], rdflib.term.Variable):
                # Note that only variables projected out of the subquery will be visible
                if BNode(expr[0]) in set(ctx_graph.objects(None, URIRef("http://www.dfki.de/voc#var"))):
                    ctx_graph.add((triple, URIRef("http://www.dfki.de/voc#s"), BNode(expr[0])))
                else:
                    ctx_graph.add((triple, URIRef("http://www.dfki.de/voc#s"), BNode(ctx.__str__() + "__" + expr[0])))

            if isinstance(expr[1], rdflib.term.URIRef):
                ctx_graph.add((triple, URIRef("http://www.dfki.de/voc#p"), URIRef(expr[1])))
            elif isinstance(expr[1], rdflib.term.Literal):
                ctx_graph.add((triple, URIRef("http://www.dfki.de/voc#p"), Literal(expr[1])))
            elif isinstance(expr[1], rdflib.term.BNode):
                # blank nodes are scoped to the basic graph pattern.
                ctx_graph.add((triple, URIRef("http://www.dfki.de/voc#p"), BNode(ctx.__str__() + "__" + expr[1])))
            elif isinstance(expr[1], rdflib.term.Variable):
                # Note that only variables projected out of the subquery will be visible
                if BNode(expr[1]) in set(ctx_graph.objects(None, URIRef("http://www.dfki.de/voc#var"))):
                    ctx_graph.add((triple, URIRef("http://www.dfki.de/voc#p"), BNode(expr[1])))
                else:
                    ctx_graph.add((triple, URIRef("http://www.dfki.de/voc#p"), BNode(ctx.__str__() + "__" + expr[1])))

            if isinstance(expr[2], rdflib.term.URIRef):
                ctx_graph.add((triple, URIRef("http://www.dfki.de/voc#o"), URIRef(expr[2])))
            elif isinstance(expr[2], rdflib.term.Literal):
                ctx_graph.add((triple, URIRef("http://www.dfki.de/voc#o"), Literal(expr[2])))
            elif isinstance(expr[2], rdflib.term.BNode):
                # blank nodes are scoped to the basic graph pattern.
                ctx_graph.add((triple, URIRef("http://www.dfki.de/voc#o"), BNode(ctx.__str__() + "__" + expr[2])))
            elif isinstance(expr[2], rdflib.term.Variable):
                # Note that only variables projected out of the subquery will be visible
                if BNode(expr[2]) in set(ctx_graph.objects(None, URIRef("http://www.dfki.de/voc#var"))):
                    ctx_graph.add((triple, URIRef("http://www.dfki.de/voc#o"), BNode(expr[2])))
                else:
                    ctx_graph.add((triple, URIRef("http://www.dfki.de/voc#o"), BNode(ctx.__str__() + "__" + expr[2])))

            return ctx_graph

        # handles a Basic Graph Pattern as n-ary JOINs
        if expr.name == "BGP":
            # each BGP is a subgraph of its ctx node
            if (ctx, RDF.type, URIRef("http://www.dfki.de/voc#Join")) in ctx_graph:
                # if ctx node is a JOIN, we add all triple patterns as arguments
                for arg in set(expr['triples']):
                    ctx_graph = ctx_graph + sparql_iter(arg, ctx, ctx_graph)
            else:
                # if ctx node is NOT a JOIN, we turn the BGP into a JOIN node
                join = BNode()
                ctx_graph.add((join, RDF.type, URIRef("http://www.dfki.de/voc#Join")))
                ctx_graph.add((ctx, URIRef("http://www.dfki.de/voc#arg"), join))
                for arg in set(expr['triples']):
                    ctx_graph = ctx_graph + sparql_iter(arg, join, ctx_graph)

            return ctx_graph

        # handles a JOIN node
        if expr.name == "Join":
            # make nested JOINs n-ary operators
            if (ctx, RDF.type, URIRef("http://www.dfki.de/voc#Join")) in ctx_graph:
                ctx_graph = ctx_graph + sparql_iter(expr['p1'], ctx, ctx_graph)
                ctx_graph = ctx_graph + sparql_iter(expr['p2'], ctx, ctx_graph)
            else:
                join = BNode()
                ctx_graph.add((join, RDF.type, URIRef("http://www.dfki.de/voc#Join")))
                ctx_graph.add((ctx, URIRef("http://www.dfki.de/voc#arg"), join))
                ctx_graph = ctx_graph + sparql_iter(expr['p1'], join, ctx_graph)
                ctx_graph = ctx_graph + sparql_iter(expr['p2'], join, ctx_graph)

            return ctx_graph

        # handles a UNION node
        if expr.name == "Union":
            # make nested UNIONs n-ary operators
            if (ctx, RDF.type, URIRef("http://www.dfki.de/voc#Union")) in ctx_graph:
                ctx_graph = ctx_graph + sparql_iter(expr['p1'], ctx, ctx_graph)
                ctx_graph = ctx_graph + sparql_iter(expr['p2'], ctx, ctx_graph)
            else:
                union = BNode()
                ctx_graph.add((union, RDF.type, URIRef("http://www.dfki.de/voc#Union")))
                ctx_graph.add((ctx, URIRef("http://www.dfki.de/voc#arg"), union))
                ctx_graph = ctx_graph + sparql_iter(expr['p1'], union, ctx_graph)
                ctx_graph = ctx_graph + sparql_iter(expr['p2'], union, ctx_graph)

            return ctx_graph

        # handles a PROJECT node
        if expr.name == "Project":
            # since we assume UNION normal form, we always add a UNION below the SELECT node
            union = BNode()
            ctx_graph.add((union, RDF.type, URIRef("http://www.dfki.de/voc#Union")))
            ctx_graph.add((ctx, URIRef("http://www.dfki.de/voc#arg"), union))
            ctx_graph = ctx_graph + sparql_iter(expr['p'], union, ctx_graph)

            return ctx_graph

    # handles a SELECT node and transform the query into a R-graph
    if query.algebra.name == "SelectQuery":
        # every SELECT node is a query graph
        from rdflib.namespace import Namespace, NamespaceManager
        dfkiNs = Namespace("http://www.dfki.de/voc#")
        namespace_manager = NamespaceManager(rdflib.Graph())
        namespace_manager.bind("dfki", dfkiNs, override=False)

        r_graph = rdflib.Graph()
        r_graph.namespace_manager = namespace_manager
        select = BNode()  # a GUID is generated
        r_graph.add((select, RDF.type, URIRef("http://www.dfki.de/voc#Select")))
        for proj_var in set(query.algebra.PV):
            r_graph.add((select, URIRef("http://www.dfki.de/voc#var"), BNode(proj_var)))
        r_graph = r_graph + sparql_iter(query.algebra['p'], select, r_graph)

        return ground_projected_variables(r_graph)
    else:
        pass


class BNodeMatcher(nx.isomorphism.GraphMatcher):

    def __init__(self, G1, G2):
        import networkx.algorithms.isomorphism as iso
        em = iso.categorical_multiedge_match('e', None)
        super(BNodeMatcher, self).__init__(G1, G2, edge_match=em)

    def semantic_feasibility(self, G1_node, G2_node):
        import rdflib

        if isinstance(G1_node, rdflib.term.URIRef) and isinstance(G2_node, rdflib.term.URIRef) and not G1_node.eq(G2_node):
            return False
        if isinstance(G1_node, rdflib.term.Literal) and isinstance(G2_node, rdflib.term.Literal) and not G1_node.eq(G2_node):
            return False

        return super(BNodeMatcher, self).semantic_feasibility(G1_node, G2_node)


def minimize_rgraph(r_graph):

    def extract_conjunctive_queries(r_graph):
        import networkx as nx
        import rdflib
        from rdflib import URIRef, BNode, Literal
        from rdflib.namespace import RDF
        from rdflib.extras.external_graph_libs import rdflib_to_networkx_multidigraph

        join_nodes = r_graph.subjects(RDF.type, URIRef("http://www.dfki.de/voc#Join"))

#        nx_r_graph = rdflib_to_networkx_multidigraph(r_graph, edge_attrs=lambda s, p, o: {'e': r_graph.qname(p)})
        nx_r_graph = rdflib_to_networkx_multidigraph(r_graph, edge_attrs=lambda s, p, o: {'e': p})
#        draw_graph(nx_r_graph)

        nx_conjunctive_query_patterns = list()

        for join_node in join_nodes:
            nx_conjunctive_query_patterns.append(nx.subgraph(nx_r_graph, list(nx.dfs_preorder_nodes(nx_r_graph, join_node))).copy())

        return nx_conjunctive_query_patterns

    def compute_core_endomorphism(nx_graph):

        def compute_BNode_mappings(perm):
            import rdflib

            # transform node mapping into orbit representation
            cycles = []
            for source in list(perm.keys()):
                target = perm.pop(source, None)
                if target is None:
                    continue
                cycle = [source]
                while source != target:
                    cycle.append(target)
                    target = perm.pop(target)
                cycles.append(cycle)

            # compute the BNode mapping (with constant IL map)
            endomorphism = dict()
            for cycle in cycles:

                # if we have an identity, there is not much to do
                if len(cycle) == 1:
                    endomorphism[cycle[0]] = cycle[0]
                else:
                    r_nodes_in_cycle = [r_node for r_node in cycle if not isinstance(r_node, rdflib.term.BNode)]

                    # we need to choose a representative node
                    # NOTE: r_node is our target in the mapping!
                    if len(r_nodes_in_cycle) == 0:
                        r_node = cycle[0]
                    else:
                        r_node = r_nodes_in_cycle[0]

                    cycle.remove(r_node)
                    for node in cycle:
                        endomorphism[node] = r_node

            return endomorphism

        # note that we are operating on UNDIRECTED graphs here
        import networkx as nx
        assert(isinstance(nx_graph, nx.MultiGraph))

        # prepare blankNode isomorphism matcher
        iso_matcher = BNodeMatcher(nx_graph, nx_graph)

        # compute all possible homomorphisms
        endomorphisms = [compute_BNode_mappings(endomorphism) for endomorphism in list(iso_matcher.isomorphisms_iter())]

        # select a core endomorphism
        import rdflib
        co_domains = [sum(1 for target in set(endomorphism.values()) if isinstance(target, rdflib.term.BNode)) for endomorphism in endomorphisms]
        core_endomorphism = endomorphisms[co_domains.index(min(co_domains))]

        # return None iff core_endomorphism is an identity map
        is_identity = True
        for key, value in core_endomorphism.items():
            is_identity = is_identity & (key == value)

        if is_identity:
            return None
        else:
            return core_endomorphism

    def remove_intra_cq_redundancy(nx_cq_graph):
        import networkx as nx

        while True:
            # must transform into UNDIRECTED graphs for computation of endomorphisms!
            core_endomorphism = compute_core_endomorphism(nx_cq_graph.to_undirected())

            if core_endomorphism is None:
                return nx_cq_graph
            else:
                from networkx import relabel
                relabel.relabel_nodes(nx_cq_graph, core_endomorphism, copy=False)

    # extract all conjunctive query patterns from R-Graph
    nx_conjunctive_query_patterns = extract_conjunctive_queries(r_graph)

    # remove intra-cq redundancy
    min_nx_conjunctive_query_patterns = list()
    for nx_cq in nx_conjunctive_query_patterns:
        min_nx_conjunctive_query_patterns.append(remove_intra_cq_redundancy(nx_cq))

    # remove inter-cq redundancy from min_nx_conjunctive_query_patterns
    # condition 1: remove Q_1 iff ∃ Q_j: select_v(Q_i) ≡ select_v(Q_j)
    import itertools

    for Q_i, Q_j in itertools.combinations(min_nx_conjunctive_query_patterns, 2):
        if BNodeMatcher(Q_i.to_undirected(), Q_j.to_undirected()).is_isomorphic():
            min_nx_conjunctive_query_patterns.remove(Q_i)

    # condition 2: remove Q_1 iff ∃ Q_j: select_v(Q_i) ≢ select_v(Q_j) and select_v(Q_i) ⊏ select_v(Q_j)
    # TODO: Check if this is valid!
    for Q_i, Q_j in itertools.combinations(min_nx_conjunctive_query_patterns, 2):
        if BNodeMatcher(Q_j.to_undirected(), Q_i.to_undirected()).subgraph_is_isomorphic():
            min_nx_conjunctive_query_patterns.remove(Q_i)

    # returns r_graph in UCQ form
    return min_nx_conjunctive_query_patterns


def check_query_containment(G_1, G_2):
    """
    A ⊑ B iff for every CQ(B) we find an isomorphism to a subgraph of a CQ(A)
    :param A:
    :param B:
    :return:
    """
    # transform queries into their R-Graphs and extract the minimal conjunctive query patterns from both queries
    cqs_a = minimize_rgraph(G_1)
    cqs_b = minimize_rgraph(G_2)

    # check if for every CQ(B) we find an isomorphism to a subgraph of a CQ(A)
    for B in cqs_b:
        contained = False
        for A in cqs_a:
            # prepare blankNode isomorphism matcher
            iso_matcher = BNodeMatcher(A.to_undirected(), B.to_undirected())
            contained = contained or iso_matcher.subgraph_is_isomorphic()
            if contained:
                print("Containment witness: ")
                import pprint
                pp = pprint.PrettyPrinter(indent=4)
                pp.pprint(iso_matcher.mapping)
                break
        if not contained:
            return False
        return True


# load queries from Web and parse into (minimized) algebra expressions
#q_1 = "https://github.com/BMBF-MOSAIK/sparqlqc-benchmark/raw/master/noprojection/Q8a"
q_1 = "https://github.com/BMBF-MOSAIK/sparqlqc-benchmark/raw/master/family.rq"
q1 = translateQuery(parseQuery(requests.get(q_1).text))
q1_graph = sparql_to_rgraph(q1)
q1_ucq = minimize_rgraph(q1_graph)


#q_2 = "https://github.com/BMBF-MOSAIK/sparqlqc-benchmark/raw/master/noprojection/Q8b"
q_2 = "https://github.com/BMBF-MOSAIK/sparqlqc-benchmark/raw/master/family.rq"
q2 = translateQuery(parseQuery(requests.get(q_2).text))
q2_graph = sparql_to_rgraph(q2)
q2_ucq = minimize_rgraph(q2_graph)



print(check_query_containment(q1_graph, q2_graph))
print(check_query_containment(q2_graph, q1_graph))
