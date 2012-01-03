import networkx as nx
import os, struct
import utils
import time
import cPickle
import math
import getopt
import pdb
import sys

# edge "e" is (u, v) tuple. "path" is list of nodes.
#
# note that the edge is undirectioned. so returns true if either u--v
# or v--u is in the path.
def isEdgeInPath(e, path):
    # find u
    try:
        idx = path.index(e[0])
        # is v either side of u?
        v = e[1]
        if idx == 0:
            # u is at beginning of path
            return path[1] == v
        elif idx == (len(path) - 1):
            # u is at end of path
            return path[-2] == v
        else:
            # u is in middle of path
            return (path[idx-1] == v) or (path[idx+1] == v)
        pass
    except ValueError:
        pass
    return False


filename = '../../../../graphs/rocketfuel/1239/latencies.intra'
g, _ = utils.textToG(filename, useInt=True, ignoreWeights=False)


allNodes = tuple(g.nodes())
numNodes = len(allNodes)

allLinks = g.edges()

for l0 in allLinks:
    for s in allNodes:
        for d in allNodes:
            if s == d:
                continue

            ppath = nx.dijkstra_path(g, s, d)
            if isEdgeInPath(l0, ppath):
                ppathlen = nx.dijkstra_path_length(g, s, d)
                (fn1, fn2) = l0
                savedEdgeAttr = g[fn1][fn2].copy()
                g.remove_edge(fn1, fn2)

                newppath = None
                try:
                    newppath = nx.dijkstra_path(g, s, d)
                    pass
                except:
                    pass
                if newppath:
                    newppathlen = nx.dijkstra_path_length(g, s, d)
                    if (float(newppathlen) / float(ppathlen)) > 2.5:
                        print s, d, l0
                        print ppath, ppathlen
                        print newppathlen, newppathlen
                        pass
                    pass
                g.add_edge(fn1, fn2, attr_dict=savedEdgeAttr)
                pass
            pass
        pass
    pass
